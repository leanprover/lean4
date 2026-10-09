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
uint8_t l_Lean_instOrdOLeanLevel_ord(uint8_t, uint8_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Compiler_LCNF_resumeCompilation(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_output;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_serve;
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_String_instHashableRaw_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
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
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_st_mk_ref(lean_object*);
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
extern lean_object* l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedFileMap_default;
extern lean_object* l_Lean_Options_empty;
extern lean_object* l_Lean_NameSet_empty;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_declMapExt;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_name(lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_setDeclPublic(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_impureSigExt;
extern lean_object* l_Lean_Compiler_CSimp_ext;
extern lean_object* l_Lean_Meta_instanceExtension;
extern lean_object* l_Lean_classExtension;
extern lean_object* l_Lean_Meta_Match_Extension_extension;
lean_object* l_Lean_Environment_getModuleIdx_x3f(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedImportState_default;
lean_object* l_Lean_importModulesCore(lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
lean_object* l_Lean_finalizeImport(lean_object*, lean_object*, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t);
lean_object* l_Lean_withImporting___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
lean_object* l_Lean_Environment_setMainModule(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_main___elam__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_main___elam__0___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_main___elam__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_main___elam__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_main___elam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_main___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00main_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00main_spec__5___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_main___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_main___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_main___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_main___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "internal exception "};
static const lean_object* l_main___lam__2___closed__0 = (const lean_object*)&l_main___lam__2___closed__0_value;
static const lean_string_object l_main___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l_main___lam__2___closed__1 = (const lean_object*)&l_main___lam__2___closed__1_value;
static const lean_string_object l_main___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " (unknown)"};
static const lean_object* l_main___lam__2___closed__2 = (const lean_object*)&l_main___lam__2___closed__2_value;
LEAN_EXPORT lean_object* l_main___lam__2(lean_object*, lean_object*, uint16_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_main___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_main___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_main___lam__3___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___lam__0(lean_object*, lean_object*, lean_object*);
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
v_isModule_124_ = lean_ctor_get_uint8(v___x_123_, sizeof(void*)*8 + 4);
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
LEAN_EXPORT lean_object* l_main___elam__0___redArg___lam__0(lean_object* v___x_289_, lean_object* v_x_290_){
_start:
{
lean_inc_ref(v___x_289_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg___lam__0___boxed(lean_object* v___x_291_, lean_object* v_x_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_main___elam__0___redArg___lam__0(v___x_291_, v_x_292_);
lean_dec_ref(v_x_292_);
lean_dec_ref(v___x_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg(lean_object* v___x_294_, uint8_t v___x_295_, lean_object* v_inst_296_, lean_object* v_ext_297_, lean_object* v_env_298_){
_start:
{
lean_object* v_toEnvExtension_300_; lean_object* v_addImportedFn_301_; lean_object* v_asyncMode_302_; uint8_t v_logWrites_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v_importedEntries_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_342_; 
v_toEnvExtension_300_ = lean_ctor_get(v_ext_297_, 0);
lean_inc_ref(v_toEnvExtension_300_);
v_addImportedFn_301_ = lean_ctor_get(v_ext_297_, 2);
lean_inc_ref(v_addImportedFn_301_);
lean_dec_ref(v_ext_297_);
v_asyncMode_302_ = lean_ctor_get(v_toEnvExtension_300_, 2);
v_logWrites_303_ = lean_ctor_get_uint8(v_toEnvExtension_300_, sizeof(void*)*6);
v___x_304_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v_inst_296_);
lean_inc_ref(v_env_298_);
v___x_305_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_304_, v_toEnvExtension_300_, v_env_298_, v_asyncMode_302_, v___x_294_, v___x_295_);
lean_dec_ref(v___x_304_);
v_importedEntries_306_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_342_ == 0)
{
lean_object* v_unused_343_; 
v_unused_343_ = lean_ctor_get(v___x_305_, 1);
lean_dec(v_unused_343_);
v___x_308_ = v___x_305_;
v_isShared_309_ = v_isSharedCheck_342_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_importedEntries_306_);
lean_dec(v___x_305_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_342_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_310_ = l_Lean_Options_empty;
lean_inc_ref(v_env_298_);
v___x_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_311_, 0, v_env_298_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
lean_inc_ref(v_importedEntries_306_);
v___x_312_ = lean_apply_3(v_addImportedFn_301_, v_importedEntries_306_, v___x_311_, lean_box(0));
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_333_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_333_ == 0)
{
v___x_315_ = v___x_312_;
v_isShared_316_ = v_isSharedCheck_333_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_312_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_333_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v_a_313_);
v___x_318_ = v___x_308_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_importedEntries_306_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_a_313_);
v___x_318_ = v_reuseFailAlloc_332_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_object* v___f_319_; lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v___f_319_ = lean_alloc_closure((void*)(l_main___elam__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_319_, 0, v___x_318_);
v___x_320_ = lean_box(0);
v___x_321_ = lean_box(0);
v___x_322_ = 1;
if (v_logWrites_303_ == 0)
{
lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_323_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_300_, v_env_298_, v___f_319_, v___x_320_, v___x_321_, v___x_322_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v___x_323_);
v___x_325_ = v___x_315_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_330_; 
lean_inc_ref(v_toEnvExtension_300_);
v___x_327_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite___redArg(v_toEnvExtension_300_, v_env_298_);
lean_dec_ref(v_env_298_);
v___x_328_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_300_, v___x_327_, v___f_319_, v___x_320_, v___x_321_, v___x_322_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v___x_328_);
v___x_330_ = v___x_315_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
lean_del_object(v___x_308_);
lean_dec_ref(v_importedEntries_306_);
lean_dec_ref(v_toEnvExtension_300_);
lean_dec_ref(v_env_298_);
v_a_334_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_312_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_312_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg___boxed(lean_object* v___x_344_, lean_object* v___x_345_, lean_object* v_inst_346_, lean_object* v_ext_347_, lean_object* v_env_348_, lean_object* v___y_349_){
_start:
{
uint8_t v___x_36899__boxed_350_; lean_object* v_res_351_; 
v___x_36899__boxed_350_ = lean_unbox(v___x_345_);
v_res_351_ = l_main___elam__0___redArg(v___x_344_, v___x_36899__boxed_350_, v_inst_346_, v_ext_347_, v_env_348_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0(lean_object* v___x_352_, uint8_t v___x_353_, lean_object* v_00_u03b1_354_, lean_object* v_00_u03b2_355_, lean_object* v_00_u03c3_356_, lean_object* v_inst_357_, lean_object* v_ext_358_, lean_object* v_env_359_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_main___elam__0___redArg(v___x_352_, v___x_353_, v_inst_357_, v_ext_358_, v_env_359_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___boxed(lean_object* v___x_362_, lean_object* v___x_363_, lean_object* v_00_u03b1_364_, lean_object* v_00_u03b2_365_, lean_object* v_00_u03c3_366_, lean_object* v_inst_367_, lean_object* v_ext_368_, lean_object* v_env_369_, lean_object* v___y_370_){
_start:
{
uint8_t v___x_36989__boxed_371_; lean_object* v_res_372_; 
v___x_36989__boxed_371_ = lean_unbox(v___x_363_);
v_res_372_ = l_main___elam__0(v___x_362_, v___x_36989__boxed_371_, v_00_u03b1_364_, v_00_u03b2_365_, v_00_u03c3_366_, v_inst_367_, v_ext_368_, v_env_369_);
return v_res_372_;
}
}
static lean_object* _init_l_panic___at___00main_spec__5___closed__0(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = l_instInhabitedError;
v___x_374_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_374_, 0, lean_box(0));
lean_closure_set(v___x_374_, 1, lean_box(0));
lean_closure_set(v___x_374_, 2, v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5(lean_object* v_msg_375_){
_start:
{
lean_object* v___x_377_; lean_object* v___x_20025__overap_378_; lean_object* v___x_379_; 
v___x_377_ = lean_obj_once(&l_panic___at___00main_spec__5___closed__0, &l_panic___at___00main_spec__5___closed__0_once, _init_l_panic___at___00main_spec__5___closed__0);
v___x_20025__overap_378_ = lean_panic_fn_borrowed(v___x_377_, v_msg_375_);
v___x_379_ = lean_apply_1(v___x_20025__overap_378_, lean_box(0));
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5___boxed(lean_object* v_msg_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_panic___at___00main_spec__5(v_msg_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8(lean_object* v_opts_383_, lean_object* v_opt_384_){
_start:
{
lean_object* v_name_385_; lean_object* v_defValue_386_; lean_object* v_map_387_; lean_object* v___x_388_; 
v_name_385_ = lean_ctor_get(v_opt_384_, 0);
v_defValue_386_ = lean_ctor_get(v_opt_384_, 1);
v_map_387_ = lean_ctor_get(v_opts_383_, 0);
v___x_388_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_387_, v_name_385_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_inc(v_defValue_386_);
return v_defValue_386_;
}
else
{
lean_object* v_val_389_; 
v_val_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_val_389_);
lean_dec_ref_known(v___x_388_, 1);
if (lean_obj_tag(v_val_389_) == 3)
{
lean_object* v_v_390_; 
v_v_390_ = lean_ctor_get(v_val_389_, 0);
lean_inc(v_v_390_);
lean_dec_ref_known(v_val_389_, 1);
return v_v_390_;
}
else
{
lean_dec(v_val_389_);
lean_inc(v_defValue_386_);
return v_defValue_386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8___boxed(lean_object* v_opts_391_, lean_object* v_opt_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_Option_get___at___00main_spec__8(v_opts_391_, v_opt_392_);
lean_dec_ref(v_opt_392_);
lean_dec_ref(v_opts_391_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_main___lam__0(lean_object* v_package_x3f_394_, lean_object* v_ps_395_){
_start:
{
lean_object* v_importedEntries_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
v_importedEntries_396_ = lean_ctor_get(v_ps_395_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v_ps_395_);
if (v_isSharedCheck_403_ == 0)
{
lean_object* v_unused_404_; 
v_unused_404_ = lean_ctor_get(v_ps_395_, 1);
lean_dec(v_unused_404_);
v___x_398_ = v_ps_395_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_importedEntries_396_);
lean_dec(v_ps_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 1, v_package_x3f_394_);
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_importedEntries_396_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_package_x3f_394_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(lean_object* v_a_405_, lean_object* v_x_406_){
_start:
{
if (lean_obj_tag(v_x_406_) == 0)
{
lean_dec(v_a_405_);
return v_x_406_;
}
else
{
lean_object* v_key_407_; lean_object* v_value_408_; lean_object* v_tail_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_442_; 
v_key_407_ = lean_ctor_get(v_x_406_, 0);
v_value_408_ = lean_ctor_get(v_x_406_, 1);
v_tail_409_ = lean_ctor_get(v_x_406_, 2);
v_isSharedCheck_442_ = !lean_is_exclusive(v_x_406_);
if (v_isSharedCheck_442_ == 0)
{
v___x_411_ = v_x_406_;
v_isShared_412_ = v_isSharedCheck_442_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_tail_409_);
lean_inc(v_value_408_);
lean_inc(v_key_407_);
lean_dec(v_x_406_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_442_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
uint8_t v___x_413_; 
v___x_413_ = lean_name_eq(v_key_407_, v_a_405_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_414_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v_a_405_, v_tail_409_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 2, v___x_414_);
v___x_416_ = v___x_411_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_key_407_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_value_408_);
lean_ctor_set(v_reuseFailAlloc_417_, 2, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
else
{
lean_object* v_toEffectiveImport_418_; lean_object* v_parts_419_; lean_object* v_irParts_420_; uint8_t v_needsIRTrans_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_441_; 
lean_dec(v_key_407_);
v_toEffectiveImport_418_ = lean_ctor_get(v_value_408_, 0);
v_parts_419_ = lean_ctor_get(v_value_408_, 1);
v_irParts_420_ = lean_ctor_get(v_value_408_, 2);
v_needsIRTrans_421_ = lean_ctor_get_uint8(v_value_408_, sizeof(void*)*3);
v_isSharedCheck_441_ = !lean_is_exclusive(v_value_408_);
if (v_isSharedCheck_441_ == 0)
{
v___x_423_ = v_value_408_;
v_isShared_424_ = v_isSharedCheck_441_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_irParts_420_);
lean_inc(v_parts_419_);
lean_inc(v_toEffectiveImport_418_);
lean_dec(v_value_408_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_441_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v_toImport_425_; uint8_t v_hasData_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_440_; 
v_toImport_425_ = lean_ctor_get(v_toEffectiveImport_418_, 0);
v_hasData_426_ = lean_ctor_get_uint8(v_toEffectiveImport_418_, sizeof(void*)*1 + 1);
v_isSharedCheck_440_ = !lean_is_exclusive(v_toEffectiveImport_418_);
if (v_isSharedCheck_440_ == 0)
{
v___x_428_ = v_toEffectiveImport_418_;
v_isShared_429_ = v_isSharedCheck_440_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_toImport_425_);
lean_dec(v_toEffectiveImport_418_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_440_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
uint8_t v___x_430_; lean_object* v___x_432_; 
v___x_430_ = 0;
if (v_isShared_429_ == 0)
{
v___x_432_ = v___x_428_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_toImport_425_);
lean_ctor_set_uint8(v_reuseFailAlloc_439_, sizeof(void*)*1 + 1, v_hasData_426_);
v___x_432_ = v_reuseFailAlloc_439_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_434_; 
lean_ctor_set_uint8(v___x_432_, sizeof(void*)*1, v___x_430_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_432_);
v___x_434_ = v___x_423_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_432_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_parts_419_);
lean_ctor_set(v_reuseFailAlloc_438_, 2, v_irParts_420_);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, sizeof(void*)*3, v_needsIRTrans_421_);
v___x_434_ = v_reuseFailAlloc_438_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_436_; 
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 1, v___x_434_);
lean_ctor_set(v___x_411_, 0, v_a_405_);
v___x_436_ = v___x_411_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_405_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_437_, 2, v_tail_409_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(lean_object* v_m_443_, lean_object* v_a_444_){
_start:
{
lean_object* v_size_445_; lean_object* v_buckets_446_; lean_object* v___x_447_; uint64_t v___y_449_; 
v_size_445_ = lean_ctor_get(v_m_443_, 0);
v_buckets_446_ = lean_ctor_get(v_m_443_, 1);
v___x_447_ = lean_array_get_size(v_buckets_446_);
if (lean_obj_tag(v_a_444_) == 0)
{
uint64_t v___x_476_; 
v___x_476_ = 1723ULL;
v___y_449_ = v___x_476_;
goto v___jp_448_;
}
else
{
uint64_t v_hash_477_; 
v_hash_477_ = lean_ctor_get_uint64(v_a_444_, sizeof(void*)*2);
v___y_449_ = v_hash_477_;
goto v___jp_448_;
}
v___jp_448_:
{
uint64_t v___x_450_; uint64_t v___x_451_; uint64_t v_fold_452_; uint64_t v___x_453_; uint64_t v___x_454_; uint64_t v___x_455_; size_t v___x_456_; size_t v___x_457_; size_t v___x_458_; size_t v___x_459_; size_t v___x_460_; lean_object* v_bucket_461_; uint8_t v___x_462_; 
v___x_450_ = 32ULL;
v___x_451_ = lean_uint64_shift_right(v___y_449_, v___x_450_);
v_fold_452_ = lean_uint64_xor(v___y_449_, v___x_451_);
v___x_453_ = 16ULL;
v___x_454_ = lean_uint64_shift_right(v_fold_452_, v___x_453_);
v___x_455_ = lean_uint64_xor(v_fold_452_, v___x_454_);
v___x_456_ = lean_uint64_to_usize(v___x_455_);
v___x_457_ = lean_usize_of_nat(v___x_447_);
v___x_458_ = ((size_t)1ULL);
v___x_459_ = lean_usize_sub(v___x_457_, v___x_458_);
v___x_460_ = lean_usize_land(v___x_456_, v___x_459_);
v_bucket_461_ = lean_array_uget_borrowed(v_buckets_446_, v___x_460_);
v___x_462_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_a_444_, v_bucket_461_);
if (v___x_462_ == 0)
{
lean_dec(v_a_444_);
return v_m_443_;
}
else
{
lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_473_; 
lean_inc(v_bucket_461_);
lean_inc_ref(v_buckets_446_);
lean_inc(v_size_445_);
v_isSharedCheck_473_ = !lean_is_exclusive(v_m_443_);
if (v_isSharedCheck_473_ == 0)
{
lean_object* v_unused_474_; lean_object* v_unused_475_; 
v_unused_474_ = lean_ctor_get(v_m_443_, 1);
lean_dec(v_unused_474_);
v_unused_475_ = lean_ctor_get(v_m_443_, 0);
lean_dec(v_unused_475_);
v___x_464_ = v_m_443_;
v_isShared_465_ = v_isSharedCheck_473_;
goto v_resetjp_463_;
}
else
{
lean_dec(v_m_443_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_473_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v_buckets_467_; lean_object* v_bucket_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_466_ = lean_box(0);
v_buckets_467_ = lean_array_uset(v_buckets_446_, v___x_460_, v___x_466_);
v_bucket_468_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v_a_444_, v_bucket_461_);
v___x_469_ = lean_array_uset(v_buckets_467_, v___x_460_, v_bucket_468_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 1, v___x_469_);
v___x_471_ = v___x_464_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_size_445_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v___x_469_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__1(lean_object* v___x_478_, lean_object* v___x_479_, uint8_t v___x_480_, lean_object* v_importArts_481_, uint8_t v___y_482_, uint8_t v___x_483_, lean_object* v_name_484_, lean_object* v___x_485_, uint8_t v___x_486_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_st_mk_ref(v___x_478_);
v___x_489_ = l_Lean_importModulesCore(v___x_479_, v___x_480_, v_importArts_481_, v___y_482_, v___x_483_, v___x_488_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v___x_490_; lean_object* v_moduleNameMap_491_; lean_object* v_moduleNames_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_502_; 
lean_dec_ref_known(v___x_489_, 1);
v___x_490_ = lean_st_ref_get(v___x_488_);
lean_dec(v___x_488_);
v_moduleNameMap_491_ = lean_ctor_get(v___x_490_, 0);
v_moduleNames_492_ = lean_ctor_get(v___x_490_, 1);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_502_ == 0)
{
v___x_494_ = v___x_490_;
v_isShared_495_ = v_isSharedCheck_502_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_moduleNames_492_);
lean_inc(v_moduleNameMap_491_);
lean_dec(v___x_490_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_502_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_496_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(v_moduleNameMap_491_, v_name_484_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v___x_496_);
v___x_498_ = v___x_494_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_496_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_moduleNames_492_);
v___x_498_ = v_reuseFailAlloc_501_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
uint32_t v___x_499_; lean_object* v___x_500_; 
v___x_499_ = 0;
v___x_500_ = l_Lean_finalizeImport(v___x_498_, v___x_479_, v___x_485_, v___x_499_, v___x_483_, v___x_486_, v___x_480_, v___x_483_, v___x_483_);
lean_dec_ref(v___x_498_);
return v___x_500_;
}
}
}
else
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
lean_dec(v___x_488_);
lean_dec_ref(v___x_485_);
lean_dec(v_name_484_);
lean_dec_ref(v___x_479_);
v_a_503_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_489_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_489_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__1___boxed(lean_object* v___x_511_, lean_object* v___x_512_, lean_object* v___x_513_, lean_object* v_importArts_514_, lean_object* v___y_515_, lean_object* v___x_516_, lean_object* v_name_517_, lean_object* v___x_518_, lean_object* v___x_519_, lean_object* v___y_520_){
_start:
{
uint8_t v___x_37157__boxed_521_; uint8_t v___y_37158__boxed_522_; uint8_t v___x_37159__boxed_523_; uint8_t v___x_37161__boxed_524_; lean_object* v_res_525_; 
v___x_37157__boxed_521_ = lean_unbox(v___x_513_);
v___y_37158__boxed_522_ = lean_unbox(v___y_515_);
v___x_37159__boxed_523_ = lean_unbox(v___x_516_);
v___x_37161__boxed_524_ = lean_unbox(v___x_519_);
v_res_525_ = l_main___lam__1(v___x_511_, v___x_512_, v___x_37157__boxed_521_, v_importArts_514_, v___y_37158__boxed_522_, v___x_37159__boxed_523_, v_name_517_, v___x_518_, v___x_37161__boxed_524_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_main___lam__2(lean_object* v___x_529_, lean_object* v___x_530_, uint16_t v___x_531_, lean_object* v_name_532_, lean_object* v_a_533_, uint8_t v___x_534_, lean_object* v___x_535_, lean_object* v_head_536_, lean_object* v___x_537_, lean_object* v___x_538_, lean_object* v___x_539_, lean_object* v___x_540_, lean_object* v___x_541_, lean_object* v___x_542_, lean_object* v___x_543_, lean_object* v___x_544_, uint8_t v___x_545_, uint8_t v___x_546_){
_start:
{
lean_object* v_a_549_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v_fileName_555_; lean_object* v_fileMap_556_; lean_object* v_currNamespace_557_; lean_object* v_openDecls_558_; lean_object* v_initHeartbeats_559_; lean_object* v_maxHeartbeats_560_; lean_object* v_quotContext_561_; lean_object* v_currMacroScope_562_; lean_object* v_cancelTk_x3f_563_; lean_object* v_inheritedTraceOptions_564_; lean_object* v_currRecDepth_565_; lean_object* v_ref_566_; uint8_t v_suppressElabErrors_567_; uint8_t v_isRecordingDeps_568_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___y_604_; uint8_t v___y_626_; uint8_t v___y_627_; lean_object* v_env_628_; uint8_t v___x_629_; uint8_t v___y_631_; uint16_t v___x_632_; uint16_t v___x_633_; uint16_t v___x_634_; uint8_t v___x_635_; 
v___x_552_ = lean_io_get_num_heartbeats();
v___x_553_ = lean_st_mk_ref(v___x_529_);
v___x_600_ = l_Lean_inheritedTraceOptions;
v___x_601_ = lean_st_ref_get(v___x_600_);
v___x_602_ = lean_st_ref_get(v___x_553_);
v_env_628_ = lean_ctor_get(v___x_602_, 0);
lean_inc_ref(v_env_628_);
lean_dec(v___x_602_);
v___x_629_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_628_);
lean_dec_ref(v_env_628_);
v___x_632_ = 512;
v___x_633_ = lean_uint16_land(v___x_531_, v___x_632_);
v___x_634_ = 0;
v___x_635_ = lean_uint16_dec_eq(v___x_633_, v___x_634_);
if (v___x_635_ == 0)
{
v___y_631_ = v___x_534_;
goto v___jp_630_;
}
else
{
v___y_631_ = v___x_546_;
goto v___jp_630_;
}
v___jp_548_:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_mk_io_user_error(v_a_549_);
v___x_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
}
v___jp_554_:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_569_ = l_Lean_maxRecDepth;
v___x_570_ = l_Lean_Option_get___at___00main_spec__8(v___x_530_, v___x_569_);
v___x_571_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_571_, 0, v_fileName_555_);
lean_ctor_set(v___x_571_, 1, v_fileMap_556_);
lean_ctor_set(v___x_571_, 2, v___x_530_);
lean_ctor_set(v___x_571_, 3, v___x_570_);
lean_ctor_set(v___x_571_, 4, v_currNamespace_557_);
lean_ctor_set(v___x_571_, 5, v_openDecls_558_);
lean_ctor_set(v___x_571_, 6, v_initHeartbeats_559_);
lean_ctor_set(v___x_571_, 7, v_maxHeartbeats_560_);
lean_ctor_set(v___x_571_, 8, v_quotContext_561_);
lean_ctor_set(v___x_571_, 9, v_currMacroScope_562_);
lean_ctor_set(v___x_571_, 10, v_cancelTk_x3f_563_);
lean_ctor_set(v___x_571_, 11, v_inheritedTraceOptions_564_);
v___x_572_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v_currRecDepth_565_);
lean_ctor_set(v___x_572_, 2, v_ref_566_);
lean_ctor_set_uint16(v___x_572_, sizeof(void*)*3, v___x_531_);
lean_ctor_set_uint8(v___x_572_, sizeof(void*)*3 + 2, v_suppressElabErrors_567_);
lean_ctor_set_uint8(v___x_572_, sizeof(void*)*3 + 3, v_isRecordingDeps_568_);
v___x_573_ = l_Lean_Compiler_LCNF_emitC(v_name_532_, v___x_572_, v___x_553_);
lean_dec_ref_known(v___x_572_, 3);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_a_574_);
lean_dec_ref_known(v___x_573_, 1);
v___x_575_ = lean_st_ref_get(v___x_553_);
lean_dec(v___x_553_);
lean_dec(v___x_575_);
v___x_576_ = lean_string_to_utf8(v_a_574_);
lean_dec(v_a_574_);
v___x_577_ = lean_io_prim_handle_write(v_a_533_, v___x_576_);
lean_dec_ref(v___x_576_);
return v___x_577_;
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_599_; 
lean_dec(v___x_553_);
v_a_578_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_599_ == 0)
{
v___x_580_ = v___x_573_;
v_isShared_581_ = v_isSharedCheck_599_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_573_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_599_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
if (lean_obj_tag(v_a_578_) == 0)
{
lean_object* v_msg_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v_msg_582_ = lean_ctor_get(v_a_578_, 1);
lean_inc_ref(v_msg_582_);
lean_dec_ref_known(v_a_578_, 2);
v___x_583_ = l_Lean_MessageData_toString(v_msg_582_);
v___x_584_ = lean_mk_io_user_error(v___x_583_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v___x_584_);
v___x_586_ = v___x_580_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
else
{
lean_object* v_id_588_; lean_object* v___x_589_; 
lean_del_object(v___x_580_);
v_id_588_ = lean_ctor_get(v_a_578_, 0);
lean_inc(v_id_588_);
lean_dec_ref_known(v_a_578_, 2);
v___x_589_ = l_Lean_InternalExceptionId_getName(v_id_588_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
lean_dec(v_id_588_);
v_a_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_a_590_);
lean_dec_ref_known(v___x_589_, 1);
v___x_591_ = ((lean_object*)(l_main___lam__2___closed__0));
v___x_592_ = l_Lean_Name_toString(v_a_590_, v___x_534_);
v___x_593_ = lean_string_append(v___x_591_, v___x_592_);
lean_dec_ref(v___x_592_);
v_a_549_ = v___x_593_;
goto v___jp_548_;
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
lean_dec_ref_known(v___x_589_, 1);
v___x_594_ = ((lean_object*)(l_main___lam__2___closed__1));
v___x_595_ = l_Nat_reprFast(v_id_588_);
v___x_596_ = lean_string_append(v___x_594_, v___x_595_);
lean_dec_ref(v___x_595_);
v___x_597_ = ((lean_object*)(l_main___lam__2___closed__2));
v___x_598_ = lean_string_append(v___x_596_, v___x_597_);
v_a_549_ = v___x_598_;
goto v___jp_548_;
}
}
}
}
}
v___jp_603_:
{
lean_object* v___x_605_; lean_object* v_env_606_; lean_object* v_nextMacroScope_607_; lean_object* v_ngen_608_; lean_object* v_auxDeclNGen_609_; lean_object* v_traceState_610_; lean_object* v_recordedDeps_611_; lean_object* v_messages_612_; lean_object* v_infoState_613_; lean_object* v_snapshotTasks_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_623_; 
v___x_605_ = lean_st_ref_take(v___x_553_);
v_env_606_ = lean_ctor_get(v___x_605_, 0);
v_nextMacroScope_607_ = lean_ctor_get(v___x_605_, 1);
v_ngen_608_ = lean_ctor_get(v___x_605_, 2);
v_auxDeclNGen_609_ = lean_ctor_get(v___x_605_, 3);
v_traceState_610_ = lean_ctor_get(v___x_605_, 4);
v_recordedDeps_611_ = lean_ctor_get(v___x_605_, 6);
v_messages_612_ = lean_ctor_get(v___x_605_, 7);
v_infoState_613_ = lean_ctor_get(v___x_605_, 8);
v_snapshotTasks_614_ = lean_ctor_get(v___x_605_, 9);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_623_ == 0)
{
lean_object* v_unused_624_; 
v_unused_624_ = lean_ctor_get(v___x_605_, 5);
lean_dec(v_unused_624_);
v___x_616_ = v___x_605_;
v_isShared_617_ = v_isSharedCheck_623_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_snapshotTasks_614_);
lean_inc(v_infoState_613_);
lean_inc(v_messages_612_);
lean_inc(v_recordedDeps_611_);
lean_inc(v_traceState_610_);
lean_inc(v_auxDeclNGen_609_);
lean_inc(v_ngen_608_);
lean_inc(v_nextMacroScope_607_);
lean_inc(v_env_606_);
lean_dec(v___x_605_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_623_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_618_ = l_Lean_Kernel_enableDiag(v_env_606_, v___y_604_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 5, v___x_535_);
lean_ctor_set(v___x_616_, 0, v___x_618_);
v___x_620_ = v___x_616_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_618_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_nextMacroScope_607_);
lean_ctor_set(v_reuseFailAlloc_622_, 2, v_ngen_608_);
lean_ctor_set(v_reuseFailAlloc_622_, 3, v_auxDeclNGen_609_);
lean_ctor_set(v_reuseFailAlloc_622_, 4, v_traceState_610_);
lean_ctor_set(v_reuseFailAlloc_622_, 5, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_622_, 6, v_recordedDeps_611_);
lean_ctor_set(v_reuseFailAlloc_622_, 7, v_messages_612_);
lean_ctor_set(v_reuseFailAlloc_622_, 8, v_infoState_613_);
lean_ctor_set(v_reuseFailAlloc_622_, 9, v_snapshotTasks_614_);
v___x_620_ = v_reuseFailAlloc_622_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_621_; 
v___x_621_ = lean_st_ref_put(v___x_553_, v___x_620_);
lean_inc(v___x_538_);
v_fileName_555_ = v_head_536_;
v_fileMap_556_ = v___x_537_;
v_currNamespace_557_ = v___x_538_;
v_openDecls_558_ = v___x_539_;
v_initHeartbeats_559_ = v___x_552_;
v_maxHeartbeats_560_ = v___x_540_;
v_quotContext_561_ = v___x_538_;
v_currMacroScope_562_ = v___x_541_;
v_cancelTk_x3f_563_ = v___x_542_;
v_inheritedTraceOptions_564_ = v___x_601_;
v_currRecDepth_565_ = v___x_543_;
v_ref_566_ = v___x_544_;
v_suppressElabErrors_567_ = v___x_545_;
v_isRecordingDeps_568_ = v___x_545_;
goto v___jp_554_;
}
}
}
v___jp_625_:
{
if (v___y_627_ == 0)
{
v___y_604_ = v___y_626_;
goto v___jp_603_;
}
else
{
lean_dec_ref(v___x_535_);
lean_inc(v___x_538_);
v_fileName_555_ = v_head_536_;
v_fileMap_556_ = v___x_537_;
v_currNamespace_557_ = v___x_538_;
v_openDecls_558_ = v___x_539_;
v_initHeartbeats_559_ = v___x_552_;
v_maxHeartbeats_560_ = v___x_540_;
v_quotContext_561_ = v___x_538_;
v_currMacroScope_562_ = v___x_541_;
v_cancelTk_x3f_563_ = v___x_542_;
v_inheritedTraceOptions_564_ = v___x_601_;
v_currRecDepth_565_ = v___x_543_;
v_ref_566_ = v___x_544_;
v_suppressElabErrors_567_ = v___x_545_;
v_isRecordingDeps_568_ = v___x_545_;
goto v___jp_554_;
}
}
v___jp_630_:
{
if (v___y_631_ == 0)
{
if (v___x_629_ == 0)
{
v___y_626_ = v___y_631_;
v___y_627_ = v___x_534_;
goto v___jp_625_;
}
else
{
v___y_604_ = v___y_631_;
goto v___jp_603_;
}
}
else
{
v___y_626_ = v___y_631_;
v___y_627_ = v___x_629_;
goto v___jp_625_;
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__2___boxed(lean_object** _args){
lean_object* v___x_636_ = _args[0];
lean_object* v___x_637_ = _args[1];
lean_object* v___x_638_ = _args[2];
lean_object* v_name_639_ = _args[3];
lean_object* v_a_640_ = _args[4];
lean_object* v___x_641_ = _args[5];
lean_object* v___x_642_ = _args[6];
lean_object* v_head_643_ = _args[7];
lean_object* v___x_644_ = _args[8];
lean_object* v___x_645_ = _args[9];
lean_object* v___x_646_ = _args[10];
lean_object* v___x_647_ = _args[11];
lean_object* v___x_648_ = _args[12];
lean_object* v___x_649_ = _args[13];
lean_object* v___x_650_ = _args[14];
lean_object* v___x_651_ = _args[15];
lean_object* v___x_652_ = _args[16];
lean_object* v___x_653_ = _args[17];
lean_object* v___y_654_ = _args[18];
_start:
{
uint16_t v___x_37230__boxed_655_; uint8_t v___x_37232__boxed_656_; uint8_t v___x_37243__boxed_657_; uint8_t v___x_37244__boxed_658_; lean_object* v_res_659_; 
v___x_37230__boxed_655_ = lean_unbox(v___x_638_);
v___x_37232__boxed_656_ = lean_unbox(v___x_641_);
v___x_37243__boxed_657_ = lean_unbox(v___x_652_);
v___x_37244__boxed_658_ = lean_unbox(v___x_653_);
v_res_659_ = l_main___lam__2(v___x_636_, v___x_637_, v___x_37230__boxed_655_, v_name_639_, v_a_640_, v___x_37232__boxed_656_, v___x_642_, v_head_643_, v___x_644_, v___x_645_, v___x_646_, v___x_647_, v___x_648_, v___x_649_, v___x_650_, v___x_651_, v___x_37243__boxed_657_, v___x_37244__boxed_658_);
lean_dec(v_a_640_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_main___lam__3(lean_object* v___x_660_, lean_object* v_x_661_){
_start:
{
lean_inc_ref(v___x_660_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_main___lam__3___boxed(lean_object* v___x_662_, lean_object* v_x_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_main___lam__3(v___x_662_, v_x_663_);
lean_dec_ref(v_x_663_);
lean_dec_ref(v___x_662_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(lean_object* v_x2_665_, lean_object* v_as_666_, size_t v_i_667_, size_t v_stop_668_, lean_object* v_b_669_){
_start:
{
uint8_t v___x_670_; 
v___x_670_ = lean_usize_dec_eq(v_i_667_, v_stop_668_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; lean_object* v___x_672_; size_t v___x_673_; size_t v___x_674_; 
v___x_671_ = lean_array_uget_borrowed(v_as_666_, v_i_667_);
lean_inc_ref(v_x2_665_);
lean_inc(v___x_671_);
v___x_672_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_671_, v_x2_665_, v_b_669_);
v___x_673_ = ((size_t)1ULL);
v___x_674_ = lean_usize_add(v_i_667_, v___x_673_);
v_i_667_ = v___x_674_;
v_b_669_ = v___x_672_;
goto _start;
}
else
{
lean_dec_ref(v_x2_665_);
return v_b_669_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(lean_object* v_x2_676_, lean_object* v_as_677_, lean_object* v_i_678_, lean_object* v_stop_679_, lean_object* v_b_680_){
_start:
{
size_t v_i_boxed_681_; size_t v_stop_boxed_682_; lean_object* v_res_683_; 
v_i_boxed_681_ = lean_unbox_usize(v_i_678_);
lean_dec(v_i_678_);
v_stop_boxed_682_ = lean_unbox_usize(v_stop_679_);
lean_dec(v_stop_679_);
v_res_683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v_x2_676_, v_as_677_, v_i_boxed_681_, v_stop_boxed_682_, v_b_680_);
lean_dec_ref(v_as_677_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(lean_object* v_as_684_, size_t v_i_685_, size_t v_stop_686_, lean_object* v_b_687_){
_start:
{
lean_object* v___y_689_; uint8_t v___x_693_; 
v___x_693_ = lean_usize_dec_eq(v_i_685_, v_stop_686_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v_declNames_695_; lean_object* v___x_696_; lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_694_ = lean_array_uget_borrowed(v_as_684_, v_i_685_);
v_declNames_695_ = lean_ctor_get(v___x_694_, 0);
v___x_696_ = lean_unsigned_to_nat(0u);
v___x_697_ = lean_array_get_size(v_declNames_695_);
v___x_698_ = lean_nat_dec_lt(v___x_696_, v___x_697_);
if (v___x_698_ == 0)
{
v___y_689_ = v_b_687_;
goto v___jp_688_;
}
else
{
uint8_t v___x_699_; 
v___x_699_ = lean_nat_dec_le(v___x_697_, v___x_697_);
if (v___x_699_ == 0)
{
if (v___x_698_ == 0)
{
v___y_689_ = v_b_687_;
goto v___jp_688_;
}
else
{
size_t v___x_700_; size_t v___x_701_; lean_object* v___x_702_; 
v___x_700_ = ((size_t)0ULL);
v___x_701_ = lean_usize_of_nat(v___x_697_);
lean_inc(v___x_694_);
v___x_702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_694_, v_declNames_695_, v___x_700_, v___x_701_, v_b_687_);
v___y_689_ = v___x_702_;
goto v___jp_688_;
}
}
else
{
size_t v___x_703_; size_t v___x_704_; lean_object* v___x_705_; 
v___x_703_ = ((size_t)0ULL);
v___x_704_ = lean_usize_of_nat(v___x_697_);
lean_inc(v___x_694_);
v___x_705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_694_, v_declNames_695_, v___x_703_, v___x_704_, v_b_687_);
v___y_689_ = v___x_705_;
goto v___jp_688_;
}
}
}
else
{
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14___boxed(lean_object* v_as_706_, lean_object* v_i_707_, lean_object* v_stop_708_, lean_object* v_b_709_){
_start:
{
size_t v_i_boxed_710_; size_t v_stop_boxed_711_; lean_object* v_res_712_; 
v_i_boxed_710_ = lean_unbox_usize(v_i_707_);
lean_dec(v_i_707_);
v_stop_boxed_711_ = lean_unbox_usize(v_stop_708_);
lean_dec(v_stop_708_);
v_res_712_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v_as_706_, v_i_boxed_710_, v_stop_boxed_711_, v_b_709_);
lean_dec_ref(v_as_706_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(lean_object* v_s_713_){
_start:
{
lean_object* v___x_715_; lean_object* v_putStr_716_; lean_object* v___x_717_; 
v___x_715_ = lean_get_stderr();
v_putStr_716_ = lean_ctor_get(v___x_715_, 4);
lean_inc_ref(v_putStr_716_);
lean_dec_ref(v___x_715_);
v___x_717_ = lean_apply_2(v_putStr_716_, v_s_713_, lean_box(0));
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8___boxed(lean_object* v_s_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v_s_718_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6(lean_object* v_s_721_){
_start:
{
uint32_t v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_723_ = 10;
v___x_724_ = lean_string_push(v_s_721_, v___x_723_);
v___x_725_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v___x_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6___boxed(lean_object* v_s_726_, lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_IO_eprintln___at___00main_spec__6(v_s_726_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(lean_object* v_o_732_, lean_object* v_k_733_, lean_object* v_v_734_){
_start:
{
lean_object* v_map_735_; uint8_t v_hasTrace_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_750_; 
v_map_735_ = lean_ctor_get(v_o_732_, 0);
v_hasTrace_736_ = lean_ctor_get_uint8(v_o_732_, sizeof(void*)*1);
v_isSharedCheck_750_ = !lean_is_exclusive(v_o_732_);
if (v_isSharedCheck_750_ == 0)
{
v___x_738_ = v_o_732_;
v_isShared_739_ = v_isSharedCheck_750_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_map_735_);
lean_dec(v_o_732_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_750_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_740_, 0, v_v_734_);
lean_inc(v_k_733_);
v___x_741_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_733_, v___x_740_, v_map_735_);
if (v_hasTrace_736_ == 0)
{
lean_object* v___x_742_; uint8_t v___x_743_; lean_object* v___x_745_; 
v___x_742_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_743_ = l_Lean_Name_isPrefixOf(v___x_742_, v_k_733_);
lean_dec(v_k_733_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_741_);
v___x_745_ = v___x_738_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_741_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
lean_ctor_set_uint8(v___x_745_, sizeof(void*)*1, v___x_743_);
return v___x_745_;
}
}
else
{
lean_object* v___x_748_; 
lean_dec(v_k_733_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_741_);
v___x_748_ = v___x_738_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_741_);
lean_ctor_set_uint8(v_reuseFailAlloc_749_, sizeof(void*)*1, v_hasTrace_736_);
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
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00main_spec__3(lean_object* v_opts_751_, lean_object* v_opt_752_, lean_object* v_val_753_){
_start:
{
lean_object* v_name_754_; lean_object* v___x_755_; 
v_name_754_ = lean_ctor_get(v_opt_752_, 0);
lean_inc(v_name_754_);
lean_dec_ref(v_opt_752_);
v___x_755_ = l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(v_opts_751_, v_name_754_, v_val_753_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object* v_as_756_, size_t v_i_757_, size_t v_stop_758_, lean_object* v_b_759_){
_start:
{
uint8_t v___x_760_; 
v___x_760_ = lean_usize_dec_eq(v_i_757_, v_stop_758_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; lean_object* v_name_762_; lean_object* v___x_763_; size_t v___x_764_; size_t v___x_765_; 
v___x_761_ = lean_array_uget_borrowed(v_as_756_, v_i_757_);
v_name_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_name_762_);
v___x_763_ = l_Lean_Compiler_LCNF_setDeclPublic(v_b_759_, v_name_762_);
v___x_764_ = ((size_t)1ULL);
v___x_765_ = lean_usize_add(v_i_757_, v___x_764_);
v_i_757_ = v___x_765_;
v_b_759_ = v___x_763_;
goto _start;
}
else
{
return v_b_759_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object* v_as_767_, lean_object* v_i_768_, lean_object* v_stop_769_, lean_object* v_b_770_){
_start:
{
size_t v_i_boxed_771_; size_t v_stop_boxed_772_; lean_object* v_res_773_; 
v_i_boxed_771_ = lean_unbox_usize(v_i_768_);
lean_dec(v_i_768_);
v_stop_boxed_772_ = lean_unbox_usize(v_stop_769_);
lean_dec(v_stop_769_);
v_res_773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v_as_767_, v_i_boxed_771_, v_stop_boxed_772_, v_b_770_);
lean_dec_ref(v_as_767_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg(lean_object* v_as_x27_775_, lean_object* v_b_776_){
_start:
{
if (lean_obj_tag(v_as_x27_775_) == 0)
{
lean_object* v___x_778_; 
v___x_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_778_, 0, v_b_776_);
return v___x_778_;
}
else
{
lean_object* v_head_779_; lean_object* v_tail_780_; lean_object* v_fst_781_; lean_object* v_snd_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_807_; 
v_head_779_ = lean_ctor_get(v_as_x27_775_, 0);
v_tail_780_ = lean_ctor_get(v_as_x27_775_, 1);
v_fst_781_ = lean_ctor_get(v_b_776_, 0);
v_snd_782_ = lean_ctor_get(v_b_776_, 1);
v_isSharedCheck_807_ = !lean_is_exclusive(v_b_776_);
if (v_isSharedCheck_807_ == 0)
{
v___x_784_ = v_b_776_;
v_isShared_785_ = v_isSharedCheck_807_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_snd_782_);
lean_inc(v_fst_781_);
lean_dec(v_b_776_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_807_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_786_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0));
v___x_787_ = lean_string_dec_eq(v_head_779_, v___x_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; 
lean_inc(v_head_779_);
v___x_788_ = l___private_LeanIR_0__setConfigOption(v_snd_782_, v_head_779_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_791_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v___x_788_, 1);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v_a_789_);
v___x_791_ = v___x_784_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_fst_781_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_a_789_);
v___x_791_ = v_reuseFailAlloc_793_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
v_as_x27_775_ = v_tail_780_;
v_b_776_ = v___x_791_;
goto _start;
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_del_object(v___x_784_);
lean_dec(v_fst_781_);
v_a_794_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_788_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_788_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
else
{
lean_object* v___x_802_; lean_object* v___x_804_; 
lean_dec(v_fst_781_);
v___x_802_ = lean_box(v___x_787_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_802_);
v___x_804_ = v___x_784_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_802_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_snd_782_);
v___x_804_ = v_reuseFailAlloc_806_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
v_as_x27_775_ = v_tail_780_;
v_b_776_ = v___x_804_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(lean_object* v_as_x27_808_, lean_object* v_b_809_, lean_object* v___y_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_808_, v_b_809_);
lean_dec(v_as_x27_808_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object* v_a_812_, lean_object* v_as_813_, size_t v_i_814_, size_t v_stop_815_, lean_object* v_b_816_){
_start:
{
lean_object* v___y_818_; uint8_t v___x_822_; 
v___x_822_ = lean_usize_dec_eq(v_i_814_, v_stop_815_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; lean_object* v_name_824_; uint8_t v___x_825_; 
v___x_823_ = lean_array_uget_borrowed(v_as_813_, v_i_814_);
v_name_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_name_824_);
lean_inc_ref(v_a_812_);
v___x_825_ = l_Lean_isExtern(v_a_812_, v_name_824_);
if (v___x_825_ == 0)
{
v___y_818_ = v_b_816_;
goto v___jp_817_;
}
else
{
lean_object* v___x_826_; 
lean_inc(v___x_823_);
v___x_826_ = lean_array_push(v_b_816_, v___x_823_);
v___y_818_ = v___x_826_;
goto v___jp_817_;
}
}
else
{
lean_dec_ref(v_a_812_);
return v_b_816_;
}
v___jp_817_:
{
size_t v___x_819_; size_t v___x_820_; 
v___x_819_ = ((size_t)1ULL);
v___x_820_ = lean_usize_add(v_i_814_, v___x_819_);
v_i_814_ = v___x_820_;
v_b_816_ = v___y_818_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object* v_a_827_, lean_object* v_as_828_, lean_object* v_i_829_, lean_object* v_stop_830_, lean_object* v_b_831_){
_start:
{
size_t v_i_boxed_832_; size_t v_stop_boxed_833_; lean_object* v_res_834_; 
v_i_boxed_832_ = lean_unbox_usize(v_i_829_);
lean_dec(v_i_829_);
v_stop_boxed_833_ = lean_unbox_usize(v_stop_830_);
lean_dec(v_stop_830_);
v_res_834_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_827_, v_as_828_, v_i_boxed_832_, v_stop_boxed_833_, v_b_831_);
lean_dec_ref(v_as_828_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___lam__0(lean_object* v___x_835_, lean_object* v___x_836_, lean_object* v_s_837_){
_start:
{
lean_object* v_addEntryFn_838_; lean_object* v_importedEntries_839_; lean_object* v_state_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_848_; 
v_addEntryFn_838_ = lean_ctor_get(v___x_835_, 3);
lean_inc(v_addEntryFn_838_);
lean_dec_ref(v___x_835_);
v_importedEntries_839_ = lean_ctor_get(v_s_837_, 0);
v_state_840_ = lean_ctor_get(v_s_837_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v_s_837_);
if (v_isSharedCheck_848_ == 0)
{
v___x_842_ = v_s_837_;
v_isShared_843_ = v_isSharedCheck_848_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_state_840_);
lean_inc(v_importedEntries_839_);
lean_dec(v_s_837_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_848_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v_state_844_; lean_object* v___x_846_; 
v_state_844_ = lean_apply_2(v_addEntryFn_838_, v_state_840_, v___x_836_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 1, v_state_844_);
v___x_846_ = v___x_842_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_importedEntries_839_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_state_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object* v_as_849_, size_t v_i_850_, size_t v_stop_851_, lean_object* v_b_852_){
_start:
{
lean_object* v___y_854_; uint8_t v___x_858_; 
v___x_858_ = lean_usize_dec_eq(v_i_850_, v_stop_851_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; lean_object* v_toEnvExtension_860_; lean_object* v_asyncMode_861_; uint8_t v_logWrites_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___f_865_; uint8_t v___x_866_; 
v___x_859_ = l_Lean_Compiler_LCNF_impureSigExt;
v_toEnvExtension_860_ = lean_ctor_get(v___x_859_, 0);
v_asyncMode_861_ = lean_ctor_get(v_toEnvExtension_860_, 2);
v_logWrites_862_ = lean_ctor_get_uint8(v_toEnvExtension_860_, sizeof(void*)*6);
v___x_863_ = lean_box(0);
v___x_864_ = lean_array_uget_borrowed(v_as_849_, v_i_850_);
lean_inc(v___x_864_);
v___f_865_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___lam__0), 3, 2);
lean_closure_set(v___f_865_, 0, v___x_859_);
lean_closure_set(v___f_865_, 1, v___x_864_);
v___x_866_ = 1;
if (v_logWrites_862_ == 0)
{
lean_object* v___x_867_; 
lean_inc_ref(v_toEnvExtension_860_);
v___x_867_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_860_, v_b_852_, v___f_865_, v_asyncMode_861_, v___x_863_, v___x_866_);
v___y_854_ = v___x_867_;
goto v___jp_853_;
}
else
{
lean_object* v___x_868_; lean_object* v___x_869_; 
lean_inc_ref_n(v_toEnvExtension_860_, 2);
v___x_868_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite___redArg(v_toEnvExtension_860_, v_b_852_);
lean_dec_ref(v_b_852_);
v___x_869_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_860_, v___x_868_, v___f_865_, v_asyncMode_861_, v___x_863_, v___x_866_);
v___y_854_ = v___x_869_;
goto v___jp_853_;
}
}
else
{
return v_b_852_;
}
v___jp_853_:
{
size_t v___x_855_; size_t v___x_856_; 
v___x_855_ = ((size_t)1ULL);
v___x_856_ = lean_usize_add(v_i_850_, v___x_855_);
v_i_850_ = v___x_856_;
v_b_852_ = v___y_854_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object* v_as_870_, lean_object* v_i_871_, lean_object* v_stop_872_, lean_object* v_b_873_){
_start:
{
size_t v_i_boxed_874_; size_t v_stop_boxed_875_; lean_object* v_res_876_; 
v_i_boxed_874_ = lean_unbox_usize(v_i_871_);
lean_dec(v_i_871_);
v_stop_boxed_875_ = lean_unbox_usize(v_stop_872_);
lean_dec(v_stop_872_);
v_res_876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v_as_870_, v_i_boxed_874_, v_stop_boxed_875_, v_b_873_);
lean_dec_ref(v_as_870_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object* v___y_878_, lean_object* v_as_879_, size_t v_i_880_, size_t v_stop_881_, lean_object* v_b_882_){
_start:
{
lean_object* v___y_884_; uint8_t v___x_888_; 
v___x_888_ = lean_usize_dec_eq(v_i_880_, v_stop_881_);
if (v___x_888_ == 0)
{
lean_object* v_fst_889_; lean_object* v_snd_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___y_894_; 
v_fst_889_ = lean_ctor_get(v_b_882_, 0);
v_snd_890_ = lean_ctor_get(v_b_882_, 1);
v___x_891_ = lean_array_uget_borrowed(v_as_879_, v_i_880_);
v___x_892_ = l_Lean_IR_Decl_name(v___x_891_);
if (lean_obj_tag(v___x_892_) == 1)
{
lean_object* v_pre_907_; lean_object* v_str_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v_pre_907_ = lean_ctor_get(v___x_892_, 0);
v_str_908_ = lean_ctor_get(v___x_892_, 1);
v___x_909_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___closed__0));
v___x_910_ = lean_string_dec_eq(v_str_908_, v___x_909_);
if (v___x_910_ == 0)
{
lean_inc_ref(v___x_892_);
v___y_894_ = v___x_892_;
goto v___jp_893_;
}
else
{
lean_inc(v_pre_907_);
v___y_894_ = v_pre_907_;
goto v___jp_893_;
}
}
else
{
lean_inc(v___x_892_);
v___y_894_ = v___x_892_;
goto v___jp_893_;
}
v___jp_893_:
{
uint8_t v___x_895_; 
lean_inc_ref(v___y_878_);
v___x_895_ = l_Lean_isExtern(v___y_878_, v___y_894_);
if (v___x_895_ == 0)
{
lean_dec(v___x_892_);
v___y_884_ = v_b_882_;
goto v___jp_883_;
}
else
{
lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_904_; 
lean_inc(v_snd_890_);
lean_inc(v_fst_889_);
v_isSharedCheck_904_ = !lean_is_exclusive(v_b_882_);
if (v_isSharedCheck_904_ == 0)
{
lean_object* v_unused_905_; lean_object* v_unused_906_; 
v_unused_905_ = lean_ctor_get(v_b_882_, 1);
lean_dec(v_unused_905_);
v_unused_906_ = lean_ctor_get(v_b_882_, 0);
lean_dec(v_unused_906_);
v___x_897_ = v_b_882_;
v_isShared_898_ = v_isSharedCheck_904_;
goto v_resetjp_896_;
}
else
{
lean_dec(v_b_882_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_904_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_902_; 
lean_inc_n(v___x_891_, 2);
v___x_899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_891_);
lean_ctor_set(v___x_899_, 1, v_fst_889_);
v___x_900_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_890_, v___x_892_, v___x_891_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 1, v___x_900_);
lean_ctor_set(v___x_897_, 0, v___x_899_);
v___x_902_ = v___x_897_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v___x_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
v___y_884_ = v___x_902_;
goto v___jp_883_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_878_);
return v_b_882_;
}
v___jp_883_:
{
size_t v___x_885_; size_t v___x_886_; 
v___x_885_ = ((size_t)1ULL);
v___x_886_ = lean_usize_add(v_i_880_, v___x_885_);
v_i_880_ = v___x_886_;
v_b_882_ = v___y_884_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object* v___y_911_, lean_object* v_as_912_, lean_object* v_i_913_, lean_object* v_stop_914_, lean_object* v_b_915_){
_start:
{
size_t v_i_boxed_916_; size_t v_stop_boxed_917_; lean_object* v_res_918_; 
v_i_boxed_916_ = lean_unbox_usize(v_i_913_);
lean_dec(v_i_913_);
v_stop_boxed_917_ = lean_unbox_usize(v_stop_914_);
lean_dec(v_stop_914_);
v_res_918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_911_, v_as_912_, v_i_boxed_916_, v_stop_boxed_917_, v_b_915_);
lean_dec_ref(v_as_912_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27(lean_object* v_as_922_, size_t v_sz_923_, size_t v_i_924_, lean_object* v_b_925_){
_start:
{
uint8_t v___x_927_; 
v___x_927_ = lean_usize_dec_lt(v_i_924_, v_sz_923_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; 
v___x_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_928_, 0, v_b_925_);
return v___x_928_;
}
else
{
uint8_t v___x_929_; lean_object* v_a_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
lean_dec_ref(v_b_925_);
v___x_929_ = 0;
v_a_930_ = lean_array_uget_borrowed(v_as_922_, v_i_924_);
lean_inc(v_a_930_);
v___x_931_ = l_Lean_Message_toString(v_a_930_, v___x_929_);
v___x_932_ = l_IO_eprintln___at___00main_spec__6(v___x_931_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v___x_933_; size_t v___x_934_; size_t v___x_935_; 
lean_dec_ref_known(v___x_932_, 1);
v___x_933_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_934_ = ((size_t)1ULL);
v___x_935_ = lean_usize_add(v_i_924_, v___x_934_);
v_i_924_ = v___x_935_;
v_b_925_ = v___x_933_;
goto _start;
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
v_a_937_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_932_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_932_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___boxed(lean_object* v_as_945_, lean_object* v_sz_946_, lean_object* v_i_947_, lean_object* v_b_948_, lean_object* v___y_949_){
_start:
{
size_t v_sz_boxed_950_; size_t v_i_boxed_951_; lean_object* v_res_952_; 
v_sz_boxed_950_ = lean_unbox_usize(v_sz_946_);
lean_dec(v_sz_946_);
v_i_boxed_951_ = lean_unbox_usize(v_i_947_);
lean_dec(v_i_947_);
v_res_952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27(v_as_945_, v_sz_boxed_950_, v_i_boxed_951_, v_b_948_);
lean_dec_ref(v_as_945_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(lean_object* v_as_953_, size_t v_sz_954_, size_t v_i_955_, lean_object* v_b_956_){
_start:
{
uint8_t v___x_958_; 
v___x_958_ = lean_usize_dec_lt(v_i_955_, v_sz_954_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; 
v___x_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_959_, 0, v_b_956_);
return v___x_959_;
}
else
{
uint8_t v___x_960_; lean_object* v_a_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
lean_dec_ref(v_b_956_);
v___x_960_ = 0;
v_a_961_ = lean_array_uget_borrowed(v_as_953_, v_i_955_);
lean_inc(v_a_961_);
v___x_962_ = l_Lean_Message_toString(v_a_961_, v___x_960_);
v___x_963_ = l_IO_eprintln___at___00main_spec__6(v___x_962_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v___x_964_; size_t v___x_965_; size_t v___x_966_; lean_object* v___x_967_; 
lean_dec_ref_known(v___x_963_, 1);
v___x_964_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_965_ = ((size_t)1ULL);
v___x_966_ = lean_usize_add(v_i_955_, v___x_965_);
v___x_967_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27(v_as_953_, v_sz_954_, v___x_966_, v___x_964_);
return v___x_967_;
}
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
v_a_968_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_963_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_963_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13___boxed(lean_object* v_as_976_, lean_object* v_sz_977_, lean_object* v_i_978_, lean_object* v_b_979_, lean_object* v___y_980_){
_start:
{
size_t v_sz_boxed_981_; size_t v_i_boxed_982_; lean_object* v_res_983_; 
v_sz_boxed_981_ = lean_unbox_usize(v_sz_977_);
lean_dec(v_sz_977_);
v_i_boxed_982_ = lean_unbox_usize(v_i_978_);
lean_dec(v_i_978_);
v_res_983_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_as_976_, v_sz_boxed_981_, v_i_boxed_982_, v_b_979_);
lean_dec_ref(v_as_976_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(lean_object* v_init_984_, lean_object* v_n_985_, lean_object* v_b_986_){
_start:
{
if (lean_obj_tag(v_n_985_) == 0)
{
lean_object* v_cs_988_; lean_object* v___x_989_; lean_object* v___x_990_; size_t v_sz_991_; size_t v___x_992_; lean_object* v___x_993_; 
v_cs_988_ = lean_ctor_get(v_n_985_, 0);
v___x_989_ = lean_box(0);
v___x_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
lean_ctor_set(v___x_990_, 1, v_b_986_);
v_sz_991_ = lean_array_size(v_cs_988_);
v___x_992_ = ((size_t)0ULL);
v___x_993_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12(v_init_984_, v_cs_988_, v_sz_991_, v___x_992_, v___x_990_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1008_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_996_ = v___x_993_;
v_isShared_997_ = v_isSharedCheck_1008_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_993_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1008_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v_fst_998_; 
v_fst_998_ = lean_ctor_get(v_a_994_, 0);
if (lean_obj_tag(v_fst_998_) == 0)
{
lean_object* v_snd_999_; lean_object* v___x_1000_; lean_object* v___x_1002_; 
v_snd_999_ = lean_ctor_get(v_a_994_, 1);
lean_inc(v_snd_999_);
lean_dec(v_a_994_);
v___x_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1000_, 0, v_snd_999_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_1000_);
v___x_1002_ = v___x_996_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
else
{
lean_object* v_val_1004_; lean_object* v___x_1006_; 
lean_inc_ref(v_fst_998_);
lean_dec(v_a_994_);
v_val_1004_ = lean_ctor_get(v_fst_998_, 0);
lean_inc(v_val_1004_);
lean_dec_ref_known(v_fst_998_, 1);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v_val_1004_);
v___x_1006_ = v___x_996_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_val_1004_);
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
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
v_a_1009_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_993_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_993_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
else
{
lean_object* v_vs_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; size_t v_sz_1020_; size_t v___x_1021_; lean_object* v___x_1022_; 
v_vs_1017_ = lean_ctor_get(v_n_985_, 0);
v___x_1018_ = lean_box(0);
v___x_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
lean_ctor_set(v___x_1019_, 1, v_b_986_);
v_sz_1020_ = lean_array_size(v_vs_1017_);
v___x_1021_ = ((size_t)0ULL);
v___x_1022_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_vs_1017_, v_sz_1020_, v___x_1021_, v___x_1019_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1037_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1037_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1037_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v_fst_1027_; 
v_fst_1027_ = lean_ctor_get(v_a_1023_, 0);
if (lean_obj_tag(v_fst_1027_) == 0)
{
lean_object* v_snd_1028_; lean_object* v___x_1029_; lean_object* v___x_1031_; 
v_snd_1028_ = lean_ctor_get(v_a_1023_, 1);
lean_inc(v_snd_1028_);
lean_dec(v_a_1023_);
v___x_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1029_, 0, v_snd_1028_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1029_);
v___x_1031_ = v___x_1025_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
else
{
lean_object* v_val_1033_; lean_object* v___x_1035_; 
lean_inc_ref(v_fst_1027_);
lean_dec(v_a_1023_);
v_val_1033_ = lean_ctor_get(v_fst_1027_, 0);
lean_inc(v_val_1033_);
lean_dec_ref_known(v_fst_1027_, 1);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v_val_1033_);
v___x_1035_ = v___x_1025_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_val_1033_);
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
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
v_a_1038_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1022_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1022_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12(lean_object* v_init_1046_, lean_object* v_as_1047_, size_t v_sz_1048_, size_t v_i_1049_, lean_object* v_b_1050_){
_start:
{
uint8_t v___x_1052_; 
v___x_1052_ = lean_usize_dec_lt(v_i_1049_, v_sz_1048_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; 
v___x_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1053_, 0, v_b_1050_);
return v___x_1053_;
}
else
{
lean_object* v_snd_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1088_; 
v_snd_1054_ = lean_ctor_get(v_b_1050_, 1);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_b_1050_);
if (v_isSharedCheck_1088_ == 0)
{
lean_object* v_unused_1089_; 
v_unused_1089_ = lean_ctor_get(v_b_1050_, 0);
lean_dec(v_unused_1089_);
v___x_1056_ = v_b_1050_;
v_isShared_1057_ = v_isSharedCheck_1088_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_snd_1054_);
lean_dec(v_b_1050_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1088_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1058_; lean_object* v_a_1059_; lean_object* v___x_1060_; 
v___x_1058_ = lean_box(0);
v_a_1059_ = lean_array_uget_borrowed(v_as_1047_, v_i_1049_);
lean_inc(v_snd_1054_);
v___x_1060_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_1046_, v_a_1059_, v_snd_1054_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1079_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1063_ = v___x_1060_;
v_isShared_1064_ = v_isSharedCheck_1079_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1060_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1079_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
if (lean_obj_tag(v_a_1061_) == 0)
{
lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1065_, 0, v_a_1061_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v___x_1065_);
v___x_1067_ = v___x_1056_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1065_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v_snd_1054_);
v___x_1067_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1069_; 
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v___x_1067_);
v___x_1069_ = v___x_1063_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; 
lean_del_object(v___x_1063_);
lean_dec(v_snd_1054_);
v_a_1072_ = lean_ctor_get(v_a_1061_, 0);
lean_inc(v_a_1072_);
lean_dec_ref_known(v_a_1061_, 1);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 1, v_a_1072_);
lean_ctor_set(v___x_1056_, 0, v___x_1058_);
v___x_1074_ = v___x_1056_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1058_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_a_1072_);
v___x_1074_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
size_t v___x_1075_; size_t v___x_1076_; 
v___x_1075_ = ((size_t)1ULL);
v___x_1076_ = lean_usize_add(v_i_1049_, v___x_1075_);
v_i_1049_ = v___x_1076_;
v_b_1050_ = v___x_1074_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_del_object(v___x_1056_);
lean_dec(v_snd_1054_);
v_a_1080_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1060_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1060_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12___boxed(lean_object* v_init_1090_, lean_object* v_as_1091_, lean_object* v_sz_1092_, lean_object* v_i_1093_, lean_object* v_b_1094_, lean_object* v___y_1095_){
_start:
{
size_t v_sz_boxed_1096_; size_t v_i_boxed_1097_; lean_object* v_res_1098_; 
v_sz_boxed_1096_ = lean_unbox_usize(v_sz_1092_);
lean_dec(v_sz_1092_);
v_i_boxed_1097_ = lean_unbox_usize(v_i_1093_);
lean_dec(v_i_1093_);
v_res_1098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12(v_init_1090_, v_as_1091_, v_sz_boxed_1096_, v_i_boxed_1097_, v_b_1094_);
lean_dec_ref(v_as_1091_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10___boxed(lean_object* v_init_1099_, lean_object* v_n_1100_, lean_object* v_b_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_1099_, v_n_1100_, v_b_1101_);
lean_dec_ref(v_n_1100_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15(lean_object* v_as_1107_, size_t v_sz_1108_, size_t v_i_1109_, lean_object* v_b_1110_){
_start:
{
uint8_t v___x_1112_; 
v___x_1112_ = lean_usize_dec_lt(v_i_1109_, v_sz_1108_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1113_, 0, v_b_1110_);
return v___x_1113_;
}
else
{
uint8_t v___x_1114_; lean_object* v_a_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
lean_dec_ref(v_b_1110_);
v___x_1114_ = 0;
v_a_1115_ = lean_array_uget_borrowed(v_as_1107_, v_i_1109_);
lean_inc(v_a_1115_);
v___x_1116_ = l_Lean_Message_toString(v_a_1115_, v___x_1114_);
v___x_1117_ = l_IO_eprintln___at___00main_spec__6(v___x_1116_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v___x_1118_; size_t v___x_1119_; size_t v___x_1120_; 
lean_dec_ref_known(v___x_1117_, 1);
v___x_1118_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_1119_ = ((size_t)1ULL);
v___x_1120_ = lean_usize_add(v_i_1109_, v___x_1119_);
v_i_1109_ = v___x_1120_;
v_b_1110_ = v___x_1118_;
goto _start;
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
v_a_1122_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1117_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1117_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___boxed(lean_object* v_as_1130_, lean_object* v_sz_1131_, lean_object* v_i_1132_, lean_object* v_b_1133_, lean_object* v___y_1134_){
_start:
{
size_t v_sz_boxed_1135_; size_t v_i_boxed_1136_; lean_object* v_res_1137_; 
v_sz_boxed_1135_ = lean_unbox_usize(v_sz_1131_);
lean_dec(v_sz_1131_);
v_i_boxed_1136_ = lean_unbox_usize(v_i_1132_);
lean_dec(v_i_1132_);
v_res_1137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15(v_as_1130_, v_sz_boxed_1135_, v_i_boxed_1136_, v_b_1133_);
lean_dec_ref(v_as_1130_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(lean_object* v_as_1138_, size_t v_sz_1139_, size_t v_i_1140_, lean_object* v_b_1141_){
_start:
{
uint8_t v___x_1143_; 
v___x_1143_ = lean_usize_dec_lt(v_i_1140_, v_sz_1139_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; 
v___x_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1144_, 0, v_b_1141_);
return v___x_1144_;
}
else
{
uint8_t v___x_1145_; lean_object* v_a_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
lean_dec_ref(v_b_1141_);
v___x_1145_ = 0;
v_a_1146_ = lean_array_uget_borrowed(v_as_1138_, v_i_1140_);
lean_inc(v_a_1146_);
v___x_1147_ = l_Lean_Message_toString(v_a_1146_, v___x_1145_);
v___x_1148_ = l_IO_eprintln___at___00main_spec__6(v___x_1147_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v___x_1149_; size_t v___x_1150_; size_t v___x_1151_; lean_object* v___x_1152_; 
lean_dec_ref_known(v___x_1148_, 1);
v___x_1149_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_1150_ = ((size_t)1ULL);
v___x_1151_ = lean_usize_add(v_i_1140_, v___x_1150_);
v___x_1152_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15(v_as_1138_, v_sz_1139_, v___x_1151_, v___x_1149_);
return v___x_1152_;
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
v_a_1153_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1148_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1148_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11___boxed(lean_object* v_as_1161_, lean_object* v_sz_1162_, lean_object* v_i_1163_, lean_object* v_b_1164_, lean_object* v___y_1165_){
_start:
{
size_t v_sz_boxed_1166_; size_t v_i_boxed_1167_; lean_object* v_res_1168_; 
v_sz_boxed_1166_ = lean_unbox_usize(v_sz_1162_);
lean_dec(v_sz_1162_);
v_i_boxed_1167_ = lean_unbox_usize(v_i_1163_);
lean_dec(v_i_1163_);
v_res_1168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_as_1161_, v_sz_boxed_1166_, v_i_boxed_1167_, v_b_1164_);
lean_dec_ref(v_as_1161_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7(lean_object* v_t_1169_, lean_object* v_init_1170_){
_start:
{
lean_object* v_root_1172_; lean_object* v_tail_1173_; lean_object* v___x_1174_; 
v_root_1172_ = lean_ctor_get(v_t_1169_, 0);
v_tail_1173_ = lean_ctor_get(v_t_1169_, 1);
v___x_1174_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_1170_, v_root_1172_, v_init_1170_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1211_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1177_ = v___x_1174_;
v_isShared_1178_ = v_isSharedCheck_1211_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1174_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1211_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
if (lean_obj_tag(v_a_1175_) == 0)
{
lean_object* v_a_1179_; lean_object* v___x_1181_; 
v_a_1179_ = lean_ctor_get(v_a_1175_, 0);
lean_inc(v_a_1179_);
lean_dec_ref_known(v_a_1175_, 1);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v_a_1179_);
v___x_1181_ = v___x_1177_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1179_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; size_t v_sz_1186_; size_t v___x_1187_; lean_object* v___x_1188_; 
lean_del_object(v___x_1177_);
v_a_1183_ = lean_ctor_get(v_a_1175_, 0);
lean_inc(v_a_1183_);
lean_dec_ref_known(v_a_1175_, 1);
v___x_1184_ = lean_box(0);
v___x_1185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
lean_ctor_set(v___x_1185_, 1, v_a_1183_);
v_sz_1186_ = lean_array_size(v_tail_1173_);
v___x_1187_ = ((size_t)0ULL);
v___x_1188_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_tail_1173_, v_sz_1186_, v___x_1187_, v___x_1185_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1202_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1191_ = v___x_1188_;
v_isShared_1192_ = v_isSharedCheck_1202_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1188_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1202_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v_fst_1193_; 
v_fst_1193_ = lean_ctor_get(v_a_1189_, 0);
if (lean_obj_tag(v_fst_1193_) == 0)
{
lean_object* v_snd_1194_; lean_object* v___x_1196_; 
v_snd_1194_ = lean_ctor_get(v_a_1189_, 1);
lean_inc(v_snd_1194_);
lean_dec(v_a_1189_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v_snd_1194_);
v___x_1196_ = v___x_1191_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_snd_1194_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
else
{
lean_object* v_val_1198_; lean_object* v___x_1200_; 
lean_inc_ref(v_fst_1193_);
lean_dec(v_a_1189_);
v_val_1198_ = lean_ctor_get(v_fst_1193_, 0);
lean_inc(v_val_1198_);
lean_dec_ref_known(v_fst_1193_, 1);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v_val_1198_);
v___x_1200_ = v___x_1191_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_val_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
v_a_1203_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1188_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1188_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
v_a_1212_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1174_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1174_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7___boxed(lean_object* v_t_1220_, lean_object* v_init_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_t_1220_, v_init_1221_);
lean_dec_ref(v_t_1220_);
return v_res_1223_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0(uint8_t v_suppressElabErrors_1231_, uint8_t v___y_1232_, lean_object* v_x_1233_){
_start:
{
if (lean_obj_tag(v_x_1233_) == 1)
{
lean_object* v_pre_1234_; 
v_pre_1234_ = lean_ctor_get(v_x_1233_, 0);
switch(lean_obj_tag(v_pre_1234_))
{
case 1:
{
lean_object* v_pre_1235_; 
v_pre_1235_ = lean_ctor_get(v_pre_1234_, 0);
switch(lean_obj_tag(v_pre_1235_))
{
case 0:
{
lean_object* v_str_1236_; lean_object* v_str_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
v_str_1236_ = lean_ctor_get(v_x_1233_, 1);
v_str_1237_ = lean_ctor_get(v_pre_1234_, 1);
v___x_1238_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__0));
v___x_1239_ = lean_string_dec_eq(v_str_1237_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; uint8_t v___x_1241_; 
v___x_1240_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__1));
v___x_1241_ = lean_string_dec_eq(v_str_1237_, v___x_1240_);
if (v___x_1241_ == 0)
{
return v___x_1241_;
}
else
{
lean_object* v___x_1242_; uint8_t v___x_1243_; 
v___x_1242_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__2));
v___x_1243_ = lean_string_dec_eq(v_str_1236_, v___x_1242_);
if (v___x_1243_ == 0)
{
return v___x_1243_;
}
else
{
return v_suppressElabErrors_1231_;
}
}
}
else
{
lean_object* v___x_1244_; uint8_t v___x_1245_; 
v___x_1244_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__3));
v___x_1245_ = lean_string_dec_eq(v_str_1236_, v___x_1244_);
if (v___x_1245_ == 0)
{
return v___x_1245_;
}
else
{
return v_suppressElabErrors_1231_;
}
}
}
case 1:
{
lean_object* v_pre_1246_; 
v_pre_1246_ = lean_ctor_get(v_pre_1235_, 0);
if (lean_obj_tag(v_pre_1246_) == 0)
{
lean_object* v_str_1247_; lean_object* v_str_1248_; lean_object* v_str_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v_str_1247_ = lean_ctor_get(v_x_1233_, 1);
v_str_1248_ = lean_ctor_get(v_pre_1234_, 1);
v_str_1249_ = lean_ctor_get(v_pre_1235_, 1);
v___x_1250_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__4));
v___x_1251_ = lean_string_dec_eq(v_str_1249_, v___x_1250_);
if (v___x_1251_ == 0)
{
return v___x_1251_;
}
else
{
lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1252_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__5));
v___x_1253_ = lean_string_dec_eq(v_str_1248_, v___x_1252_);
if (v___x_1253_ == 0)
{
return v___x_1253_;
}
else
{
lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1254_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__6));
v___x_1255_ = lean_string_dec_eq(v_str_1247_, v___x_1254_);
if (v___x_1255_ == 0)
{
return v___x_1255_;
}
else
{
return v_suppressElabErrors_1231_;
}
}
}
}
else
{
return v___y_1232_;
}
}
default: 
{
return v___y_1232_;
}
}
}
case 0:
{
lean_object* v_str_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v_str_1256_ = lean_ctor_get(v_x_1233_, 1);
v___x_1257_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_1258_ = lean_string_dec_eq(v_str_1256_, v___x_1257_);
if (v___x_1258_ == 0)
{
return v___x_1258_;
}
else
{
return v_suppressElabErrors_1231_;
}
}
default: 
{
return v___y_1232_;
}
}
}
else
{
return v___y_1232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___boxed(lean_object* v_suppressElabErrors_1259_, lean_object* v___y_1260_, lean_object* v_x_1261_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1262_; uint8_t v___y_38196__boxed_1263_; uint8_t v_res_1264_; lean_object* v_r_1265_; 
v_suppressElabErrors_boxed_1262_ = lean_unbox(v_suppressElabErrors_1259_);
v___y_38196__boxed_1263_ = lean_unbox(v___y_1260_);
v_res_1264_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0(v_suppressElabErrors_boxed_1262_, v___y_38196__boxed_1263_, v_x_1261_);
lean_dec(v_x_1261_);
v_r_1265_ = lean_box(v_res_1264_);
return v_r_1265_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(lean_object* v_opts_1266_, lean_object* v_opt_1267_){
_start:
{
lean_object* v_name_1268_; lean_object* v_defValue_1269_; lean_object* v_map_1270_; lean_object* v___x_1271_; 
v_name_1268_ = lean_ctor_get(v_opt_1267_, 0);
v_defValue_1269_ = lean_ctor_get(v_opt_1267_, 1);
v_map_1270_ = lean_ctor_get(v_opts_1266_, 0);
v___x_1271_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1270_, v_name_1268_);
if (lean_obj_tag(v___x_1271_) == 0)
{
uint8_t v___x_1272_; 
v___x_1272_ = lean_unbox(v_defValue_1269_);
return v___x_1272_;
}
else
{
lean_object* v_val_1273_; 
v_val_1273_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_val_1273_);
lean_dec_ref_known(v___x_1271_, 1);
if (lean_obj_tag(v_val_1273_) == 1)
{
uint8_t v_v_1274_; 
v_v_1274_ = lean_ctor_get_uint8(v_val_1273_, 0);
lean_dec_ref_known(v_val_1273_, 0);
return v_v_1274_;
}
else
{
uint8_t v___x_1275_; 
lean_dec(v_val_1273_);
v___x_1275_ = lean_unbox(v_defValue_1269_);
return v___x_1275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___boxed(lean_object* v_opts_1276_, lean_object* v_opt_1277_){
_start:
{
uint8_t v_res_1278_; lean_object* v_r_1279_; 
v_res_1278_ = l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(v_opts_1276_, v_opt_1277_);
lean_dec_ref(v_opt_1277_);
lean_dec_ref(v_opts_1276_);
v_r_1279_ = lean_box(v_res_1278_);
return v_r_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44(lean_object* v_ref_1281_, lean_object* v_msgData_1282_, uint8_t v_severity_1283_, uint8_t v_isSilent_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
uint8_t v___y_1289_; uint8_t v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v_toCold_1296_; lean_object* v___y_1297_; lean_object* v___y_1326_; lean_object* v___y_1327_; uint8_t v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; uint8_t v___y_1331_; uint8_t v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1353_; lean_object* v___y_1354_; uint8_t v___y_1355_; lean_object* v___y_1356_; uint8_t v___y_1357_; uint8_t v___y_1358_; lean_object* v___y_1359_; uint8_t v___y_1363_; uint8_t v___y_1364_; uint8_t v___y_1365_; uint8_t v___x_1376_; uint8_t v___y_1378_; uint8_t v___y_1379_; uint8_t v___y_1380_; uint8_t v___y_1382_; uint8_t v___x_1390_; 
v___x_1376_ = 2;
v___x_1390_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1283_, v___x_1376_);
if (v___x_1390_ == 0)
{
v___y_1382_ = v___x_1390_;
goto v___jp_1381_;
}
else
{
uint8_t v___x_1391_; 
lean_inc_ref(v_msgData_1282_);
v___x_1391_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1282_);
v___y_1382_ = v___x_1391_;
goto v___jp_1381_;
}
v___jp_1288_:
{
lean_object* v_currNamespace_1298_; lean_object* v_openDecls_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v_env_1304_; lean_object* v_nextMacroScope_1305_; lean_object* v_ngen_1306_; lean_object* v_auxDeclNGen_1307_; lean_object* v_traceState_1308_; lean_object* v_cache_1309_; lean_object* v_recordedDeps_1310_; lean_object* v_messages_1311_; lean_object* v_infoState_1312_; lean_object* v_snapshotTasks_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1324_; 
v_currNamespace_1298_ = lean_ctor_get(v_toCold_1296_, 4);
v_openDecls_1299_ = lean_ctor_get(v_toCold_1296_, 5);
lean_inc(v_openDecls_1299_);
lean_inc(v_currNamespace_1298_);
v___x_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1300_, 0, v_currNamespace_1298_);
lean_ctor_set(v___x_1300_, 1, v_openDecls_1299_);
v___x_1301_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
lean_ctor_set(v___x_1301_, 1, v___y_1293_);
lean_inc_ref(v___y_1291_);
lean_inc_ref(v___y_1295_);
v___x_1302_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1302_, 0, v___y_1295_);
lean_ctor_set(v___x_1302_, 1, v___y_1294_);
lean_ctor_set(v___x_1302_, 2, v___y_1292_);
lean_ctor_set(v___x_1302_, 3, v___y_1291_);
lean_ctor_set(v___x_1302_, 4, v___x_1301_);
lean_ctor_set_uint8(v___x_1302_, sizeof(void*)*5, v___y_1289_);
lean_ctor_set_uint8(v___x_1302_, sizeof(void*)*5 + 1, v___y_1290_);
lean_ctor_set_uint8(v___x_1302_, sizeof(void*)*5 + 2, v_isSilent_1284_);
v___x_1303_ = lean_st_ref_take(v___y_1297_);
v_env_1304_ = lean_ctor_get(v___x_1303_, 0);
v_nextMacroScope_1305_ = lean_ctor_get(v___x_1303_, 1);
v_ngen_1306_ = lean_ctor_get(v___x_1303_, 2);
v_auxDeclNGen_1307_ = lean_ctor_get(v___x_1303_, 3);
v_traceState_1308_ = lean_ctor_get(v___x_1303_, 4);
v_cache_1309_ = lean_ctor_get(v___x_1303_, 5);
v_recordedDeps_1310_ = lean_ctor_get(v___x_1303_, 6);
v_messages_1311_ = lean_ctor_get(v___x_1303_, 7);
v_infoState_1312_ = lean_ctor_get(v___x_1303_, 8);
v_snapshotTasks_1313_ = lean_ctor_get(v___x_1303_, 9);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1315_ = v___x_1303_;
v_isShared_1316_ = v_isSharedCheck_1324_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_snapshotTasks_1313_);
lean_inc(v_infoState_1312_);
lean_inc(v_messages_1311_);
lean_inc(v_recordedDeps_1310_);
lean_inc(v_cache_1309_);
lean_inc(v_traceState_1308_);
lean_inc(v_auxDeclNGen_1307_);
lean_inc(v_ngen_1306_);
lean_inc(v_nextMacroScope_1305_);
lean_inc(v_env_1304_);
lean_dec(v___x_1303_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1324_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1320_; 
v___x_1317_ = lean_box(0);
v___x_1318_ = l_Lean_MessageLog_add(v___x_1302_, v_messages_1311_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 7, v___x_1318_);
v___x_1320_ = v___x_1315_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_env_1304_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_nextMacroScope_1305_);
lean_ctor_set(v_reuseFailAlloc_1323_, 2, v_ngen_1306_);
lean_ctor_set(v_reuseFailAlloc_1323_, 3, v_auxDeclNGen_1307_);
lean_ctor_set(v_reuseFailAlloc_1323_, 4, v_traceState_1308_);
lean_ctor_set(v_reuseFailAlloc_1323_, 5, v_cache_1309_);
lean_ctor_set(v_reuseFailAlloc_1323_, 6, v_recordedDeps_1310_);
lean_ctor_set(v_reuseFailAlloc_1323_, 7, v___x_1318_);
lean_ctor_set(v_reuseFailAlloc_1323_, 8, v_infoState_1312_);
lean_ctor_set(v_reuseFailAlloc_1323_, 9, v_snapshotTasks_1313_);
v___x_1320_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = lean_st_ref_put(v___y_1297_, v___x_1320_);
v___x_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1317_);
return v___x_1322_;
}
}
}
v___jp_1325_:
{
lean_object* v_fileName_1334_; lean_object* v_fileMap_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1351_; 
v_fileName_1334_ = lean_ctor_get(v___y_1330_, 0);
v_fileMap_1335_ = lean_ctor_get(v___y_1330_, 1);
v___x_1336_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1282_);
v___x_1337_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v___x_1336_, v___y_1285_, v___y_1286_);
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1340_ = v___x_1337_;
v_isShared_1341_ = v_isSharedCheck_1351_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1337_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1351_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
lean_inc_ref_n(v_fileMap_1335_, 2);
v___x_1342_ = l_Lean_FileMap_toPosition(v_fileMap_1335_, v___y_1329_);
lean_dec(v___y_1329_);
v___x_1343_ = l_Lean_FileMap_toPosition(v_fileMap_1335_, v___y_1333_);
lean_dec(v___y_1333_);
v___x_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
v___x_1345_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___closed__0));
if (v___y_1332_ == 0)
{
lean_del_object(v___x_1340_);
lean_dec_ref(v___y_1327_);
v___y_1289_ = v___y_1328_;
v___y_1290_ = v___y_1331_;
v___y_1291_ = v___x_1345_;
v___y_1292_ = v___x_1344_;
v___y_1293_ = v_a_1338_;
v___y_1294_ = v___x_1342_;
v___y_1295_ = v_fileName_1334_;
v_toCold_1296_ = v___y_1326_;
v___y_1297_ = v___y_1286_;
goto v___jp_1288_;
}
else
{
uint8_t v___x_1346_; 
lean_inc(v_a_1338_);
v___x_1346_ = l_Lean_MessageData_hasTag(v___y_1327_, v_a_1338_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; lean_object* v___x_1349_; 
lean_dec_ref_known(v___x_1344_, 1);
lean_dec_ref(v___x_1342_);
lean_dec(v_a_1338_);
v___x_1347_ = lean_box(0);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v___x_1347_);
v___x_1349_ = v___x_1340_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
else
{
lean_del_object(v___x_1340_);
v___y_1289_ = v___y_1328_;
v___y_1290_ = v___y_1331_;
v___y_1291_ = v___x_1345_;
v___y_1292_ = v___x_1344_;
v___y_1293_ = v_a_1338_;
v___y_1294_ = v___x_1342_;
v___y_1295_ = v_fileName_1334_;
v_toCold_1296_ = v___y_1326_;
v___y_1297_ = v___y_1286_;
goto v___jp_1288_;
}
}
}
}
v___jp_1352_:
{
lean_object* v___x_1360_; 
v___x_1360_ = l_Lean_Syntax_getTailPos_x3f(v___y_1356_, v___y_1357_);
lean_dec(v___y_1356_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_inc(v___y_1359_);
v___y_1326_ = v___y_1353_;
v___y_1327_ = v___y_1354_;
v___y_1328_ = v___y_1357_;
v___y_1329_ = v___y_1359_;
v___y_1330_ = v___y_1353_;
v___y_1331_ = v___y_1358_;
v___y_1332_ = v___y_1355_;
v___y_1333_ = v___y_1359_;
goto v___jp_1325_;
}
else
{
lean_object* v_val_1361_; 
v_val_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_val_1361_);
lean_dec_ref_known(v___x_1360_, 1);
v___y_1326_ = v___y_1353_;
v___y_1327_ = v___y_1354_;
v___y_1328_ = v___y_1357_;
v___y_1329_ = v___y_1359_;
v___y_1330_ = v___y_1353_;
v___y_1331_ = v___y_1358_;
v___y_1332_ = v___y_1355_;
v___y_1333_ = v_val_1361_;
goto v___jp_1325_;
}
}
v___jp_1362_:
{
lean_object* v_toCold_1366_; lean_object* v_ref_1367_; uint8_t v_suppressElabErrors_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___f_1371_; lean_object* v_ref_1372_; lean_object* v___x_1373_; 
v_toCold_1366_ = lean_ctor_get(v___y_1285_, 0);
v_ref_1367_ = lean_ctor_get(v___y_1285_, 2);
v_suppressElabErrors_1368_ = lean_ctor_get_uint8(v___y_1285_, sizeof(void*)*3 + 2);
v___x_1369_ = lean_box(v_suppressElabErrors_1368_);
v___x_1370_ = lean_box(v___y_1363_);
v___f_1371_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1371_, 0, v___x_1369_);
lean_closure_set(v___f_1371_, 1, v___x_1370_);
v_ref_1372_ = l_Lean_replaceRef(v_ref_1281_, v_ref_1367_);
v___x_1373_ = l_Lean_Syntax_getPos_x3f(v_ref_1372_, v___y_1364_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_unsigned_to_nat(0u);
v___y_1353_ = v_toCold_1366_;
v___y_1354_ = v___f_1371_;
v___y_1355_ = v_suppressElabErrors_1368_;
v___y_1356_ = v_ref_1372_;
v___y_1357_ = v___y_1364_;
v___y_1358_ = v___y_1365_;
v___y_1359_ = v___x_1374_;
goto v___jp_1352_;
}
else
{
lean_object* v_val_1375_; 
v_val_1375_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_val_1375_);
lean_dec_ref_known(v___x_1373_, 1);
v___y_1353_ = v_toCold_1366_;
v___y_1354_ = v___f_1371_;
v___y_1355_ = v_suppressElabErrors_1368_;
v___y_1356_ = v_ref_1372_;
v___y_1357_ = v___y_1364_;
v___y_1358_ = v___y_1365_;
v___y_1359_ = v_val_1375_;
goto v___jp_1352_;
}
}
v___jp_1377_:
{
if (v___y_1380_ == 0)
{
v___y_1363_ = v___y_1378_;
v___y_1364_ = v___y_1379_;
v___y_1365_ = v_severity_1283_;
goto v___jp_1362_;
}
else
{
v___y_1363_ = v___y_1378_;
v___y_1364_ = v___y_1379_;
v___y_1365_ = v___x_1376_;
goto v___jp_1362_;
}
}
v___jp_1381_:
{
if (v___y_1382_ == 0)
{
uint8_t v___x_1383_; uint8_t v___x_1384_; 
v___x_1383_ = 1;
v___x_1384_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1283_, v___x_1383_);
if (v___x_1384_ == 0)
{
v___y_1378_ = v___y_1382_;
v___y_1379_ = v___y_1382_;
v___y_1380_ = v___x_1384_;
goto v___jp_1377_;
}
else
{
lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v___x_1385_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1285_);
v___x_1386_ = l_Lean_warningAsError;
v___x_1387_ = l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(v___x_1385_, v___x_1386_);
lean_dec_ref(v___x_1385_);
v___y_1378_ = v___y_1382_;
v___y_1379_ = v___y_1382_;
v___y_1380_ = v___x_1387_;
goto v___jp_1377_;
}
}
else
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_dec_ref(v_msgData_1282_);
v___x_1388_ = lean_box(0);
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___boxed(lean_object* v_ref_1392_, lean_object* v_msgData_1393_, lean_object* v_severity_1394_, lean_object* v_isSilent_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
uint8_t v_severity_boxed_1399_; uint8_t v_isSilent_boxed_1400_; lean_object* v_res_1401_; 
v_severity_boxed_1399_ = lean_unbox(v_severity_1394_);
v_isSilent_boxed_1400_ = lean_unbox(v_isSilent_1395_);
v_res_1401_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44(v_ref_1392_, v_msgData_1393_, v_severity_boxed_1399_, v_isSilent_boxed_1400_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v_ref_1392_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30(lean_object* v_msgData_1402_, uint8_t v_severity_1403_, uint8_t v_isSilent_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_ref_1408_; lean_object* v___x_1409_; 
v_ref_1408_ = lean_ctor_get(v___y_1405_, 2);
v___x_1409_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44(v_ref_1408_, v_msgData_1402_, v_severity_1403_, v_isSilent_1404_, v___y_1405_, v___y_1406_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30___boxed(lean_object* v_msgData_1410_, lean_object* v_severity_1411_, lean_object* v_isSilent_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
uint8_t v_severity_boxed_1416_; uint8_t v_isSilent_boxed_1417_; lean_object* v_res_1418_; 
v_severity_boxed_1416_ = lean_unbox(v_severity_1411_);
v_isSilent_boxed_1417_ = lean_unbox(v_isSilent_1412_);
v_res_1418_ = l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30(v_msgData_1410_, v_severity_boxed_1416_, v_isSilent_boxed_1417_, v___y_1413_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13(lean_object* v_msgData_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
uint8_t v___x_1423_; uint8_t v___x_1424_; lean_object* v___x_1425_; 
v___x_1423_ = 2;
v___x_1424_ = 0;
v___x_1425_ = l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30(v_msgData_1419_, v___x_1423_, v___x_1424_, v___y_1420_, v___y_1421_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13___boxed(lean_object* v_msgData_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Lean_logError___at___00main_spec__13(v_msgData_1426_, v___y_1427_, v___y_1428_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(lean_object* v_opts_1431_, lean_object* v_opt_1432_){
_start:
{
lean_object* v_name_1433_; lean_object* v_map_1434_; lean_object* v___x_1435_; 
v_name_1433_ = lean_ctor_get(v_opt_1432_, 0);
v_map_1434_ = lean_ctor_get(v_opts_1431_, 0);
v___x_1435_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1434_, v_name_1433_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_box(0);
return v___x_1436_;
}
else
{
lean_object* v_val_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1446_; 
v_val_1437_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1439_ = v___x_1435_;
v_isShared_1440_ = v_isSharedCheck_1446_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_val_1437_);
lean_dec(v___x_1435_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1446_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
if (lean_obj_tag(v_val_1437_) == 0)
{
lean_object* v_v_1441_; lean_object* v___x_1443_; 
v_v_1441_ = lean_ctor_get(v_val_1437_, 0);
lean_inc_ref(v_v_1441_);
lean_dec_ref_known(v_val_1437_, 1);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v_v_1441_);
v___x_1443_ = v___x_1439_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_v_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
else
{
lean_object* v___x_1445_; 
lean_del_object(v___x_1439_);
lean_dec(v_val_1437_);
v___x_1445_ = lean_box(0);
return v___x_1445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___boxed(lean_object* v_opts_1447_, lean_object* v_opt_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(v_opts_1447_, v_opt_1448_);
lean_dec_ref(v_opt_1448_);
lean_dec_ref(v_opts_1447_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22(lean_object* v_x_1450_, lean_object* v_x_1451_){
_start:
{
if (lean_obj_tag(v_x_1451_) == 0)
{
return v_x_1450_;
}
else
{
lean_object* v_key_1452_; lean_object* v_value_1453_; lean_object* v_tail_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v_key_1452_ = lean_ctor_get(v_x_1451_, 0);
v_value_1453_ = lean_ctor_get(v_x_1451_, 1);
v_tail_1454_ = lean_ctor_get(v_x_1451_, 2);
lean_inc(v_value_1453_);
lean_inc(v_key_1452_);
v___x_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1455_, 0, v_key_1452_);
lean_ctor_set(v___x_1455_, 1, v_value_1453_);
v___x_1456_ = lean_array_push(v_x_1450_, v___x_1455_);
v_x_1450_ = v___x_1456_;
v_x_1451_ = v_tail_1454_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22___boxed(lean_object* v_x_1458_, lean_object* v_x_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22(v_x_1458_, v_x_1459_);
lean_dec(v_x_1459_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23(lean_object* v_as_1461_, size_t v_i_1462_, size_t v_stop_1463_, lean_object* v_b_1464_){
_start:
{
uint8_t v___x_1465_; 
v___x_1465_ = lean_usize_dec_eq(v_i_1462_, v_stop_1463_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1467_; size_t v___x_1468_; size_t v___x_1469_; 
v___x_1466_ = lean_array_uget_borrowed(v_as_1461_, v_i_1462_);
v___x_1467_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22(v_b_1464_, v___x_1466_);
v___x_1468_ = ((size_t)1ULL);
v___x_1469_ = lean_usize_add(v_i_1462_, v___x_1468_);
v_i_1462_ = v___x_1469_;
v_b_1464_ = v___x_1467_;
goto _start;
}
else
{
return v_b_1464_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23___boxed(lean_object* v_as_1471_, lean_object* v_i_1472_, lean_object* v_stop_1473_, lean_object* v_b_1474_){
_start:
{
size_t v_i_boxed_1475_; size_t v_stop_boxed_1476_; lean_object* v_res_1477_; 
v_i_boxed_1475_ = lean_unbox_usize(v_i_1472_);
lean_dec(v_i_1472_);
v_stop_boxed_1476_ = lean_unbox_usize(v_stop_1473_);
lean_dec(v_stop_1473_);
v_res_1477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23(v_as_1471_, v_i_boxed_1475_, v_stop_boxed_1476_, v_b_1474_);
lean_dec_ref(v_as_1471_);
return v_res_1477_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(lean_object* v_x_1478_, lean_object* v_x_1479_){
_start:
{
lean_object* v_fst_1480_; lean_object* v_fst_1481_; lean_object* v_fst_1482_; lean_object* v_fst_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; uint8_t v___x_1486_; 
v_fst_1480_ = lean_ctor_get(v_x_1478_, 0);
v_fst_1481_ = lean_ctor_get(v_x_1479_, 0);
v_fst_1482_ = lean_ctor_get(v_fst_1480_, 0);
v_fst_1483_ = lean_ctor_get(v_fst_1481_, 0);
v___x_1484_ = lean_unsigned_to_nat(1u);
v___x_1485_ = lean_nat_add(v_fst_1482_, v___x_1484_);
v___x_1486_ = lean_nat_dec_le(v___x_1485_, v_fst_1483_);
lean_dec(v___x_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0___boxed(lean_object* v_x_1487_, lean_object* v_x_1488_){
_start:
{
uint8_t v_res_1489_; lean_object* v_r_1490_; 
v_res_1489_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v_x_1487_, v_x_1488_);
lean_dec_ref(v_x_1488_);
lean_dec_ref(v_x_1487_);
v_r_1490_ = lean_box(v_res_1489_);
return v_r_1490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(lean_object* v_hi_1491_, lean_object* v_pivot_1492_, lean_object* v_as_1493_, lean_object* v_i_1494_, lean_object* v_k_1495_){
_start:
{
uint8_t v___x_1496_; 
v___x_1496_ = lean_nat_dec_lt(v_k_1495_, v_hi_1491_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
lean_dec(v_k_1495_);
v___x_1497_ = lean_array_fswap(v_as_1493_, v_i_1494_, v_hi_1491_);
v___x_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1498_, 0, v_i_1494_);
lean_ctor_set(v___x_1498_, 1, v___x_1497_);
return v___x_1498_;
}
else
{
lean_object* v___x_1499_; lean_object* v_fst_1500_; lean_object* v_fst_1501_; lean_object* v_fst_1502_; lean_object* v_fst_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; uint8_t v___x_1506_; 
v___x_1499_ = lean_array_fget_borrowed(v_as_1493_, v_k_1495_);
v_fst_1500_ = lean_ctor_get(v___x_1499_, 0);
v_fst_1501_ = lean_ctor_get(v_pivot_1492_, 0);
v_fst_1502_ = lean_ctor_get(v_fst_1500_, 0);
v_fst_1503_ = lean_ctor_get(v_fst_1501_, 0);
v___x_1504_ = lean_unsigned_to_nat(1u);
v___x_1505_ = lean_nat_add(v_fst_1502_, v___x_1504_);
v___x_1506_ = lean_nat_dec_le(v___x_1505_, v_fst_1503_);
lean_dec(v___x_1505_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; 
v___x_1507_ = lean_nat_add(v_k_1495_, v___x_1504_);
lean_dec(v_k_1495_);
v_k_1495_ = v___x_1507_;
goto _start;
}
else
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1509_ = lean_array_fswap(v_as_1493_, v_i_1494_, v_k_1495_);
v___x_1510_ = lean_nat_add(v_i_1494_, v___x_1504_);
lean_dec(v_i_1494_);
v___x_1511_ = lean_nat_add(v_k_1495_, v___x_1504_);
lean_dec(v_k_1495_);
v_as_1493_ = v___x_1509_;
v_i_1494_ = v___x_1510_;
v_k_1495_ = v___x_1511_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg___boxed(lean_object* v_hi_1513_, lean_object* v_pivot_1514_, lean_object* v_as_1515_, lean_object* v_i_1516_, lean_object* v_k_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(v_hi_1513_, v_pivot_1514_, v_as_1515_, v_i_1516_, v_k_1517_);
lean_dec_ref(v_pivot_1514_);
lean_dec(v_hi_1513_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(lean_object* v_n_1519_, lean_object* v_as_1520_, lean_object* v_lo_1521_, lean_object* v_hi_1522_){
_start:
{
lean_object* v___y_1524_; uint8_t v___x_1534_; 
v___x_1534_ = lean_nat_dec_lt(v_lo_1521_, v_hi_1522_);
if (v___x_1534_ == 0)
{
lean_dec(v_lo_1521_);
return v_as_1520_;
}
else
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v_mid_1537_; lean_object* v___y_1539_; lean_object* v___y_1545_; lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; 
v___x_1535_ = lean_nat_add(v_lo_1521_, v_hi_1522_);
v___x_1536_ = lean_unsigned_to_nat(1u);
v_mid_1537_ = lean_nat_shiftr(v___x_1535_, v___x_1536_);
lean_dec(v___x_1535_);
v___x_1550_ = lean_array_fget_borrowed(v_as_1520_, v_mid_1537_);
v___x_1551_ = lean_array_fget_borrowed(v_as_1520_, v_lo_1521_);
v___x_1552_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v___x_1550_, v___x_1551_);
if (v___x_1552_ == 0)
{
v___y_1545_ = v_as_1520_;
goto v___jp_1544_;
}
else
{
lean_object* v___x_1553_; 
v___x_1553_ = lean_array_fswap(v_as_1520_, v_lo_1521_, v_mid_1537_);
v___y_1545_ = v___x_1553_;
goto v___jp_1544_;
}
v___jp_1538_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; uint8_t v___x_1542_; 
v___x_1540_ = lean_array_fget_borrowed(v___y_1539_, v_mid_1537_);
v___x_1541_ = lean_array_fget_borrowed(v___y_1539_, v_hi_1522_);
v___x_1542_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v___x_1540_, v___x_1541_);
if (v___x_1542_ == 0)
{
lean_dec(v_mid_1537_);
v___y_1524_ = v___y_1539_;
goto v___jp_1523_;
}
else
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_array_fswap(v___y_1539_, v_mid_1537_, v_hi_1522_);
lean_dec(v_mid_1537_);
v___y_1524_ = v___x_1543_;
goto v___jp_1523_;
}
}
v___jp_1544_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v___x_1546_ = lean_array_fget_borrowed(v___y_1545_, v_hi_1522_);
v___x_1547_ = lean_array_fget_borrowed(v___y_1545_, v_lo_1521_);
v___x_1548_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v___x_1546_, v___x_1547_);
if (v___x_1548_ == 0)
{
v___y_1539_ = v___y_1545_;
goto v___jp_1538_;
}
else
{
lean_object* v___x_1549_; 
v___x_1549_ = lean_array_fswap(v___y_1545_, v_lo_1521_, v_hi_1522_);
v___y_1539_ = v___x_1549_;
goto v___jp_1538_;
}
}
}
v___jp_1523_:
{
lean_object* v_pivot_1525_; lean_object* v___x_1526_; lean_object* v_fst_1527_; lean_object* v_snd_1528_; uint8_t v___x_1529_; 
v_pivot_1525_ = lean_array_fget(v___y_1524_, v_hi_1522_);
lean_inc_n(v_lo_1521_, 2);
v___x_1526_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(v_hi_1522_, v_pivot_1525_, v___y_1524_, v_lo_1521_, v_lo_1521_);
lean_dec(v_pivot_1525_);
v_fst_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_fst_1527_);
v_snd_1528_ = lean_ctor_get(v___x_1526_, 1);
lean_inc(v_snd_1528_);
lean_dec_ref(v___x_1526_);
v___x_1529_ = lean_nat_dec_le(v_hi_1522_, v_fst_1527_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1530_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v_n_1519_, v_snd_1528_, v_lo_1521_, v_fst_1527_);
v___x_1531_ = lean_unsigned_to_nat(1u);
v___x_1532_ = lean_nat_add(v_fst_1527_, v___x_1531_);
lean_dec(v_fst_1527_);
v_as_1520_ = v___x_1530_;
v_lo_1521_ = v___x_1532_;
goto _start;
}
else
{
lean_dec(v_fst_1527_);
lean_dec(v_lo_1521_);
return v_snd_1528_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___boxed(lean_object* v_n_1554_, lean_object* v_as_1555_, lean_object* v_lo_1556_, lean_object* v_hi_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v_n_1554_, v_as_1555_, v_lo_1556_, v_hi_1557_);
lean_dec(v_hi_1557_);
lean_dec(v_n_1554_);
return v_res_1558_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0(uint8_t v_suppressElabErrors_1559_, uint8_t v___x_1560_, lean_object* v___x_1561_, lean_object* v_x_1562_){
_start:
{
if (lean_obj_tag(v_x_1562_) == 1)
{
lean_object* v_pre_1563_; 
v_pre_1563_ = lean_ctor_get(v_x_1562_, 0);
switch(lean_obj_tag(v_pre_1563_))
{
case 1:
{
lean_object* v_pre_1564_; 
v_pre_1564_ = lean_ctor_get(v_pre_1563_, 0);
switch(lean_obj_tag(v_pre_1564_))
{
case 0:
{
lean_object* v_str_1565_; lean_object* v_str_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; 
v_str_1565_ = lean_ctor_get(v_x_1562_, 1);
v_str_1566_ = lean_ctor_get(v_pre_1563_, 1);
v___x_1567_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__0));
v___x_1568_ = lean_string_dec_eq(v_str_1566_, v___x_1567_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; uint8_t v___x_1570_; 
v___x_1569_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__1));
v___x_1570_ = lean_string_dec_eq(v_str_1566_, v___x_1569_);
if (v___x_1570_ == 0)
{
return v___x_1570_;
}
else
{
lean_object* v___x_1571_; uint8_t v___x_1572_; 
v___x_1571_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__2));
v___x_1572_ = lean_string_dec_eq(v_str_1565_, v___x_1571_);
if (v___x_1572_ == 0)
{
return v___x_1572_;
}
else
{
return v_suppressElabErrors_1559_;
}
}
}
else
{
lean_object* v___x_1573_; uint8_t v___x_1574_; 
v___x_1573_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__3));
v___x_1574_ = lean_string_dec_eq(v_str_1565_, v___x_1573_);
if (v___x_1574_ == 0)
{
return v___x_1574_;
}
else
{
return v_suppressElabErrors_1559_;
}
}
}
case 1:
{
lean_object* v_pre_1575_; 
v_pre_1575_ = lean_ctor_get(v_pre_1564_, 0);
if (lean_obj_tag(v_pre_1575_) == 0)
{
lean_object* v_str_1576_; lean_object* v_str_1577_; lean_object* v_str_1578_; lean_object* v___x_1579_; uint8_t v___x_1580_; 
v_str_1576_ = lean_ctor_get(v_x_1562_, 1);
v_str_1577_ = lean_ctor_get(v_pre_1563_, 1);
v_str_1578_ = lean_ctor_get(v_pre_1564_, 1);
v___x_1579_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__4));
v___x_1580_ = lean_string_dec_eq(v_str_1578_, v___x_1579_);
if (v___x_1580_ == 0)
{
return v___x_1580_;
}
else
{
lean_object* v___x_1581_; uint8_t v___x_1582_; 
v___x_1581_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__5));
v___x_1582_ = lean_string_dec_eq(v_str_1577_, v___x_1581_);
if (v___x_1582_ == 0)
{
return v___x_1582_;
}
else
{
lean_object* v___x_1583_; uint8_t v___x_1584_; 
v___x_1583_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__6));
v___x_1584_ = lean_string_dec_eq(v_str_1576_, v___x_1583_);
if (v___x_1584_ == 0)
{
return v___x_1584_;
}
else
{
return v_suppressElabErrors_1559_;
}
}
}
}
else
{
return v___x_1560_;
}
}
default: 
{
return v___x_1560_;
}
}
}
case 0:
{
lean_object* v_str_1585_; uint8_t v___x_1586_; 
v_str_1585_ = lean_ctor_get(v_x_1562_, 1);
v___x_1586_ = lean_string_dec_eq(v_str_1585_, v___x_1561_);
if (v___x_1586_ == 0)
{
return v___x_1586_;
}
else
{
return v_suppressElabErrors_1559_;
}
}
default: 
{
return v___x_1560_;
}
}
}
else
{
return v___x_1560_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0___boxed(lean_object* v_suppressElabErrors_1587_, lean_object* v___x_1588_, lean_object* v___x_1589_, lean_object* v_x_1590_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1591_; uint8_t v___x_38660__boxed_1592_; uint8_t v_res_1593_; lean_object* v_r_1594_; 
v_suppressElabErrors_boxed_1591_ = lean_unbox(v_suppressElabErrors_1587_);
v___x_38660__boxed_1592_ = lean_unbox(v___x_1588_);
v_res_1593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0(v_suppressElabErrors_boxed_1591_, v___x_38660__boxed_1592_, v___x_1589_, v_x_1590_);
lean_dec(v_x_1590_);
lean_dec_ref(v___x_1589_);
v_r_1594_ = lean_box(v_res_1593_);
return v_r_1594_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0(void){
_start:
{
lean_object* v___x_1595_; double v___x_1596_; 
v___x_1595_ = lean_unsigned_to_nat(0u);
v___x_1596_ = lean_float_of_nat(v___x_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(uint8_t v___x_1597_, lean_object* v_as_1598_, size_t v_sz_1599_, size_t v_i_1600_, lean_object* v_b_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v_a_1606_; uint8_t v___x_1610_; 
v___x_1610_ = lean_usize_dec_lt(v_i_1600_, v_sz_1599_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; 
v___x_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1611_, 0, v_b_1601_);
return v___x_1611_;
}
else
{
lean_object* v_a_1612_; lean_object* v_fst_1613_; lean_object* v_snd_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1693_; 
v_a_1612_ = lean_array_uget(v_as_1598_, v_i_1600_);
v_fst_1613_ = lean_ctor_get(v_a_1612_, 0);
v_snd_1614_ = lean_ctor_get(v_a_1612_, 1);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_a_1612_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1616_ = v_a_1612_;
v_isShared_1617_ = v_isSharedCheck_1693_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_snd_1614_);
lean_inc(v_fst_1613_);
lean_dec(v_a_1612_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1693_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v_fst_1618_; lean_object* v_snd_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1692_; 
v_fst_1618_ = lean_ctor_get(v_fst_1613_, 0);
v_snd_1619_ = lean_ctor_get(v_fst_1613_, 1);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_fst_1613_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1621_ = v_fst_1613_;
v_isShared_1622_ = v_isSharedCheck_1692_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_snd_1619_);
lean_inc(v_fst_1618_);
lean_dec(v_fst_1613_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1692_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; double v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v_toCold_1628_; uint8_t v_suppressElabErrors_1629_; lean_object* v_fileName_1630_; lean_object* v_fileMap_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1638_; 
v___x_1623_ = lean_box(0);
v___x_1624_ = lean_box(0);
v___x_1625_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0);
v___x_1626_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___closed__0));
v___x_1627_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1627_, 0, v___x_1623_);
lean_ctor_set(v___x_1627_, 1, v___x_1624_);
lean_ctor_set(v___x_1627_, 2, v___x_1626_);
lean_ctor_set_float(v___x_1627_, sizeof(void*)*3, v___x_1625_);
lean_ctor_set_float(v___x_1627_, sizeof(void*)*3 + 8, v___x_1625_);
lean_ctor_set_uint8(v___x_1627_, sizeof(void*)*3 + 16, v___x_1610_);
v_toCold_1628_ = lean_ctor_get(v___y_1602_, 0);
v_suppressElabErrors_1629_ = lean_ctor_get_uint8(v___y_1602_, sizeof(void*)*3 + 2);
v_fileName_1630_ = lean_ctor_get(v_toCold_1628_, 0);
v_fileMap_1631_ = lean_ctor_get(v_toCold_1628_, 1);
v___x_1632_ = lean_box(0);
v___x_1633_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_1634_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_1635_ = l_Lean_MessageData_nil;
v___x_1636_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1627_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
lean_ctor_set(v___x_1636_, 2, v_snd_1614_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set_tag(v___x_1621_, 8);
lean_ctor_set(v___x_1621_, 1, v___x_1636_);
lean_ctor_set(v___x_1621_, 0, v___x_1634_);
v___x_1638_ = v___x_1621_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1634_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v___x_1636_);
v___x_1638_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
uint8_t v___x_1639_; lean_object* v___x_1640_; lean_object* v___y_1642_; lean_object* v___y_1643_; 
v___x_1639_ = 0;
lean_inc_ref(v_fileMap_1631_);
lean_inc_ref(v_fileName_1630_);
v___x_1640_ = l_Lean_Elab_mkMessageCore(v_fileName_1630_, v_fileMap_1631_, v___x_1638_, v___x_1639_, v_fst_1618_, v_snd_1619_);
lean_dec(v_snd_1619_);
lean_dec(v_fst_1618_);
if (v_suppressElabErrors_1629_ == 0)
{
v___y_1642_ = v___y_1602_;
v___y_1643_ = v___y_1603_;
goto v___jp_1641_;
}
else
{
lean_object* v_data_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___f_1689_; uint8_t v___x_1690_; 
v_data_1686_ = lean_ctor_get(v___x_1640_, 4);
v___x_1687_ = lean_box(v_suppressElabErrors_1629_);
v___x_1688_ = lean_box(v___x_1597_);
v___f_1689_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1689_, 0, v___x_1687_);
lean_closure_set(v___f_1689_, 1, v___x_1688_);
lean_closure_set(v___f_1689_, 2, v___x_1633_);
lean_inc(v_data_1686_);
v___x_1690_ = l_Lean_MessageData_hasTag(v___f_1689_, v_data_1686_);
if (v___x_1690_ == 0)
{
lean_dec_ref(v___x_1640_);
lean_del_object(v___x_1616_);
v_a_1606_ = v___x_1632_;
goto v___jp_1605_;
}
else
{
v___y_1642_ = v___y_1602_;
v___y_1643_ = v___y_1603_;
goto v___jp_1641_;
}
}
v___jp_1641_:
{
lean_object* v_toCold_1644_; lean_object* v_fileName_1645_; lean_object* v_pos_1646_; lean_object* v_endPos_1647_; uint8_t v_keepFullRange_1648_; uint8_t v_severity_1649_; uint8_t v_isSilent_1650_; lean_object* v_caption_1651_; lean_object* v_data_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1685_; 
v_toCold_1644_ = lean_ctor_get(v___y_1642_, 0);
v_fileName_1645_ = lean_ctor_get(v___x_1640_, 0);
v_pos_1646_ = lean_ctor_get(v___x_1640_, 1);
v_endPos_1647_ = lean_ctor_get(v___x_1640_, 2);
v_keepFullRange_1648_ = lean_ctor_get_uint8(v___x_1640_, sizeof(void*)*5);
v_severity_1649_ = lean_ctor_get_uint8(v___x_1640_, sizeof(void*)*5 + 1);
v_isSilent_1650_ = lean_ctor_get_uint8(v___x_1640_, sizeof(void*)*5 + 2);
v_caption_1651_ = lean_ctor_get(v___x_1640_, 3);
v_data_1652_ = lean_ctor_get(v___x_1640_, 4);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1654_ = v___x_1640_;
v_isShared_1655_ = v_isSharedCheck_1685_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_data_1652_);
lean_inc(v_caption_1651_);
lean_inc(v_endPos_1647_);
lean_inc(v_pos_1646_);
lean_inc(v_fileName_1645_);
lean_dec(v___x_1640_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1685_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v_currNamespace_1656_; lean_object* v_openDecls_1657_; lean_object* v___x_1659_; 
v_currNamespace_1656_ = lean_ctor_get(v_toCold_1644_, 4);
v_openDecls_1657_ = lean_ctor_get(v_toCold_1644_, 5);
lean_inc(v_openDecls_1657_);
lean_inc(v_currNamespace_1656_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 1, v_openDecls_1657_);
lean_ctor_set(v___x_1616_, 0, v_currNamespace_1656_);
v___x_1659_ = v___x_1616_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_currNamespace_1656_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_openDecls_1657_);
v___x_1659_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
lean_object* v___x_1660_; lean_object* v___x_1662_; 
v___x_1660_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1659_);
lean_ctor_set(v___x_1660_, 1, v_data_1652_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 4, v___x_1660_);
v___x_1662_ = v___x_1654_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_fileName_1645_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_pos_1646_);
lean_ctor_set(v_reuseFailAlloc_1683_, 2, v_endPos_1647_);
lean_ctor_set(v_reuseFailAlloc_1683_, 3, v_caption_1651_);
lean_ctor_set(v_reuseFailAlloc_1683_, 4, v___x_1660_);
lean_ctor_set_uint8(v_reuseFailAlloc_1683_, sizeof(void*)*5, v_keepFullRange_1648_);
lean_ctor_set_uint8(v_reuseFailAlloc_1683_, sizeof(void*)*5 + 1, v_severity_1649_);
lean_ctor_set_uint8(v_reuseFailAlloc_1683_, sizeof(void*)*5 + 2, v_isSilent_1650_);
v___x_1662_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1663_; lean_object* v_env_1664_; lean_object* v_nextMacroScope_1665_; lean_object* v_ngen_1666_; lean_object* v_auxDeclNGen_1667_; lean_object* v_traceState_1668_; lean_object* v_cache_1669_; lean_object* v_recordedDeps_1670_; lean_object* v_messages_1671_; lean_object* v_infoState_1672_; lean_object* v_snapshotTasks_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1682_; 
v___x_1663_ = lean_st_ref_take(v___y_1643_);
v_env_1664_ = lean_ctor_get(v___x_1663_, 0);
v_nextMacroScope_1665_ = lean_ctor_get(v___x_1663_, 1);
v_ngen_1666_ = lean_ctor_get(v___x_1663_, 2);
v_auxDeclNGen_1667_ = lean_ctor_get(v___x_1663_, 3);
v_traceState_1668_ = lean_ctor_get(v___x_1663_, 4);
v_cache_1669_ = lean_ctor_get(v___x_1663_, 5);
v_recordedDeps_1670_ = lean_ctor_get(v___x_1663_, 6);
v_messages_1671_ = lean_ctor_get(v___x_1663_, 7);
v_infoState_1672_ = lean_ctor_get(v___x_1663_, 8);
v_snapshotTasks_1673_ = lean_ctor_get(v___x_1663_, 9);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1675_ = v___x_1663_;
v_isShared_1676_ = v_isSharedCheck_1682_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_snapshotTasks_1673_);
lean_inc(v_infoState_1672_);
lean_inc(v_messages_1671_);
lean_inc(v_recordedDeps_1670_);
lean_inc(v_cache_1669_);
lean_inc(v_traceState_1668_);
lean_inc(v_auxDeclNGen_1667_);
lean_inc(v_ngen_1666_);
lean_inc(v_nextMacroScope_1665_);
lean_inc(v_env_1664_);
lean_dec(v___x_1663_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1682_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1677_; lean_object* v___x_1679_; 
v___x_1677_ = l_Lean_MessageLog_add(v___x_1662_, v_messages_1671_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 7, v___x_1677_);
v___x_1679_ = v___x_1675_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_env_1664_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v_nextMacroScope_1665_);
lean_ctor_set(v_reuseFailAlloc_1681_, 2, v_ngen_1666_);
lean_ctor_set(v_reuseFailAlloc_1681_, 3, v_auxDeclNGen_1667_);
lean_ctor_set(v_reuseFailAlloc_1681_, 4, v_traceState_1668_);
lean_ctor_set(v_reuseFailAlloc_1681_, 5, v_cache_1669_);
lean_ctor_set(v_reuseFailAlloc_1681_, 6, v_recordedDeps_1670_);
lean_ctor_set(v_reuseFailAlloc_1681_, 7, v___x_1677_);
lean_ctor_set(v_reuseFailAlloc_1681_, 8, v_infoState_1672_);
lean_ctor_set(v_reuseFailAlloc_1681_, 9, v_snapshotTasks_1673_);
v___x_1679_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
lean_object* v___x_1680_; 
v___x_1680_ = lean_st_ref_put(v___y_1643_, v___x_1679_);
v_a_1606_ = v___x_1632_;
goto v___jp_1605_;
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
v___jp_1605_:
{
size_t v___x_1607_; size_t v___x_1608_; 
v___x_1607_ = ((size_t)1ULL);
v___x_1608_ = lean_usize_add(v_i_1600_, v___x_1607_);
v_i_1600_ = v___x_1608_;
v_b_1601_ = v_a_1606_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___boxed(lean_object* v___x_1694_, lean_object* v_as_1695_, lean_object* v_sz_1696_, lean_object* v_i_1697_, lean_object* v_b_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
uint8_t v___x_38725__boxed_1702_; size_t v_sz_boxed_1703_; size_t v_i_boxed_1704_; lean_object* v_res_1705_; 
v___x_38725__boxed_1702_ = lean_unbox(v___x_1694_);
v_sz_boxed_1703_ = lean_unbox_usize(v_sz_1696_);
lean_dec(v_sz_1696_);
v_i_boxed_1704_ = lean_unbox_usize(v_i_1697_);
lean_dec(v_i_1697_);
v_res_1705_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(v___x_38725__boxed_1702_, v_as_1695_, v_sz_boxed_1703_, v_i_boxed_1704_, v_b_1698_, v___y_1699_, v___y_1700_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec_ref(v_as_1695_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(lean_object* v_a_1706_, lean_object* v_fallback_1707_, lean_object* v_x_1708_){
_start:
{
if (lean_obj_tag(v_x_1708_) == 0)
{
lean_inc(v_fallback_1707_);
return v_fallback_1707_;
}
else
{
lean_object* v_key_1709_; lean_object* v_value_1710_; lean_object* v_tail_1711_; lean_object* v_fst_1712_; lean_object* v_snd_1713_; lean_object* v_fst_1714_; lean_object* v_snd_1715_; uint8_t v_decide_1716_; 
v_key_1709_ = lean_ctor_get(v_x_1708_, 0);
v_value_1710_ = lean_ctor_get(v_x_1708_, 1);
v_tail_1711_ = lean_ctor_get(v_x_1708_, 2);
v_fst_1712_ = lean_ctor_get(v_key_1709_, 0);
v_snd_1713_ = lean_ctor_get(v_key_1709_, 1);
v_fst_1714_ = lean_ctor_get(v_a_1706_, 0);
v_snd_1715_ = lean_ctor_get(v_a_1706_, 1);
v_decide_1716_ = lean_nat_dec_eq(v_fst_1712_, v_fst_1714_);
if (v_decide_1716_ == 0)
{
v_x_1708_ = v_tail_1711_;
goto _start;
}
else
{
uint8_t v_decide_1718_; 
v_decide_1718_ = lean_nat_dec_eq(v_snd_1713_, v_snd_1715_);
if (v_decide_1718_ == 0)
{
v_x_1708_ = v_tail_1711_;
goto _start;
}
else
{
lean_inc(v_value_1710_);
return v_value_1710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg___boxed(lean_object* v_a_1720_, lean_object* v_fallback_1721_, lean_object* v_x_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(v_a_1720_, v_fallback_1721_, v_x_1722_);
lean_dec(v_x_1722_);
lean_dec(v_fallback_1721_);
lean_dec_ref(v_a_1720_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(lean_object* v_m_1724_, lean_object* v_a_1725_, lean_object* v_fallback_1726_){
_start:
{
lean_object* v_buckets_1727_; lean_object* v_fst_1728_; lean_object* v_snd_1729_; lean_object* v___x_1730_; uint64_t v___x_1731_; uint64_t v___x_1732_; uint64_t v___x_1733_; uint64_t v___x_1734_; uint64_t v___x_1735_; uint64_t v_fold_1736_; uint64_t v___x_1737_; uint64_t v___x_1738_; uint64_t v___x_1739_; size_t v___x_1740_; size_t v___x_1741_; size_t v___x_1742_; size_t v___x_1743_; size_t v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v_buckets_1727_ = lean_ctor_get(v_m_1724_, 1);
v_fst_1728_ = lean_ctor_get(v_a_1725_, 0);
v_snd_1729_ = lean_ctor_get(v_a_1725_, 1);
v___x_1730_ = lean_array_get_size(v_buckets_1727_);
v___x_1731_ = l_String_instHashableRaw_hash(v_fst_1728_);
v___x_1732_ = l_String_instHashableRaw_hash(v_snd_1729_);
v___x_1733_ = lean_uint64_mix_hash(v___x_1731_, v___x_1732_);
v___x_1734_ = 32ULL;
v___x_1735_ = lean_uint64_shift_right(v___x_1733_, v___x_1734_);
v_fold_1736_ = lean_uint64_xor(v___x_1733_, v___x_1735_);
v___x_1737_ = 16ULL;
v___x_1738_ = lean_uint64_shift_right(v_fold_1736_, v___x_1737_);
v___x_1739_ = lean_uint64_xor(v_fold_1736_, v___x_1738_);
v___x_1740_ = lean_uint64_to_usize(v___x_1739_);
v___x_1741_ = lean_usize_of_nat(v___x_1730_);
v___x_1742_ = ((size_t)1ULL);
v___x_1743_ = lean_usize_sub(v___x_1741_, v___x_1742_);
v___x_1744_ = lean_usize_land(v___x_1740_, v___x_1743_);
v___x_1745_ = lean_array_uget_borrowed(v_buckets_1727_, v___x_1744_);
v___x_1746_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(v_a_1725_, v_fallback_1726_, v___x_1745_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg___boxed(lean_object* v_m_1747_, lean_object* v_a_1748_, lean_object* v_fallback_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_m_1747_, v_a_1748_, v_fallback_1749_);
lean_dec(v_fallback_1749_);
lean_dec_ref(v_a_1748_);
lean_dec_ref(v_m_1747_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44___redArg(lean_object* v_x_1751_, lean_object* v_x_1752_){
_start:
{
if (lean_obj_tag(v_x_1752_) == 0)
{
return v_x_1751_;
}
else
{
lean_object* v_key_1753_; lean_object* v_value_1754_; lean_object* v_tail_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1782_; 
v_key_1753_ = lean_ctor_get(v_x_1752_, 0);
v_value_1754_ = lean_ctor_get(v_x_1752_, 1);
v_tail_1755_ = lean_ctor_get(v_x_1752_, 2);
v_isSharedCheck_1782_ = !lean_is_exclusive(v_x_1752_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1757_ = v_x_1752_;
v_isShared_1758_ = v_isSharedCheck_1782_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_tail_1755_);
lean_inc(v_value_1754_);
lean_inc(v_key_1753_);
lean_dec(v_x_1752_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1782_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v_fst_1759_; lean_object* v_snd_1760_; lean_object* v___x_1761_; uint64_t v___x_1762_; uint64_t v___x_1763_; uint64_t v___x_1764_; uint64_t v___x_1765_; uint64_t v___x_1766_; uint64_t v_fold_1767_; uint64_t v___x_1768_; uint64_t v___x_1769_; uint64_t v___x_1770_; size_t v___x_1771_; size_t v___x_1772_; size_t v___x_1773_; size_t v___x_1774_; size_t v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1778_; 
v_fst_1759_ = lean_ctor_get(v_key_1753_, 0);
v_snd_1760_ = lean_ctor_get(v_key_1753_, 1);
v___x_1761_ = lean_array_get_size(v_x_1751_);
v___x_1762_ = l_String_instHashableRaw_hash(v_fst_1759_);
v___x_1763_ = l_String_instHashableRaw_hash(v_snd_1760_);
v___x_1764_ = lean_uint64_mix_hash(v___x_1762_, v___x_1763_);
v___x_1765_ = 32ULL;
v___x_1766_ = lean_uint64_shift_right(v___x_1764_, v___x_1765_);
v_fold_1767_ = lean_uint64_xor(v___x_1764_, v___x_1766_);
v___x_1768_ = 16ULL;
v___x_1769_ = lean_uint64_shift_right(v_fold_1767_, v___x_1768_);
v___x_1770_ = lean_uint64_xor(v_fold_1767_, v___x_1769_);
v___x_1771_ = lean_uint64_to_usize(v___x_1770_);
v___x_1772_ = lean_usize_of_nat(v___x_1761_);
v___x_1773_ = ((size_t)1ULL);
v___x_1774_ = lean_usize_sub(v___x_1772_, v___x_1773_);
v___x_1775_ = lean_usize_land(v___x_1771_, v___x_1774_);
v___x_1776_ = lean_array_uget_borrowed(v_x_1751_, v___x_1775_);
lean_inc(v___x_1776_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 2, v___x_1776_);
v___x_1778_ = v___x_1757_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_key_1753_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_value_1754_);
lean_ctor_set(v_reuseFailAlloc_1781_, 2, v___x_1776_);
v___x_1778_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
lean_object* v___x_1779_; 
v___x_1779_ = lean_array_uset(v_x_1751_, v___x_1775_, v___x_1778_);
v_x_1751_ = v___x_1779_;
v_x_1752_ = v_tail_1755_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35___redArg(lean_object* v_i_1783_, lean_object* v_source_1784_, lean_object* v_target_1785_){
_start:
{
lean_object* v___x_1786_; uint8_t v___x_1787_; 
v___x_1786_ = lean_array_get_size(v_source_1784_);
v___x_1787_ = lean_nat_dec_lt(v_i_1783_, v___x_1786_);
if (v___x_1787_ == 0)
{
lean_dec_ref(v_source_1784_);
lean_dec(v_i_1783_);
return v_target_1785_;
}
else
{
lean_object* v_es_1788_; lean_object* v___x_1789_; lean_object* v_source_1790_; lean_object* v_target_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v_es_1788_ = lean_array_fget(v_source_1784_, v_i_1783_);
v___x_1789_ = lean_box(0);
v_source_1790_ = lean_array_fset(v_source_1784_, v_i_1783_, v___x_1789_);
v_target_1791_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44___redArg(v_target_1785_, v_es_1788_);
v___x_1792_ = lean_unsigned_to_nat(1u);
v___x_1793_ = lean_nat_add(v_i_1783_, v___x_1792_);
lean_dec(v_i_1783_);
v_i_1783_ = v___x_1793_;
v_source_1784_ = v_source_1790_;
v_target_1785_ = v_target_1791_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24___redArg(lean_object* v_data_1795_){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v_nbuckets_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1796_ = lean_array_get_size(v_data_1795_);
v___x_1797_ = lean_unsigned_to_nat(2u);
v_nbuckets_1798_ = lean_nat_mul(v___x_1796_, v___x_1797_);
v___x_1799_ = lean_unsigned_to_nat(0u);
v___x_1800_ = lean_box(0);
v___x_1801_ = lean_mk_array(v_nbuckets_1798_, v___x_1800_);
v___x_1802_ = lean_array_propagate_mark(v_data_1795_, v___x_1801_);
v___x_1803_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35___redArg(v___x_1799_, v_data_1795_, v___x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(lean_object* v_a_1804_, lean_object* v_b_1805_, lean_object* v_x_1806_){
_start:
{
if (lean_obj_tag(v_x_1806_) == 0)
{
lean_dec(v_b_1805_);
lean_dec_ref(v_a_1804_);
return v_x_1806_;
}
else
{
lean_object* v_key_1807_; lean_object* v_value_1808_; lean_object* v_tail_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1825_; 
v_key_1807_ = lean_ctor_get(v_x_1806_, 0);
v_value_1808_ = lean_ctor_get(v_x_1806_, 1);
v_tail_1809_ = lean_ctor_get(v_x_1806_, 2);
v_isSharedCheck_1825_ = !lean_is_exclusive(v_x_1806_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1811_ = v_x_1806_;
v_isShared_1812_ = v_isSharedCheck_1825_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_tail_1809_);
lean_inc(v_value_1808_);
lean_inc(v_key_1807_);
lean_dec(v_x_1806_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1825_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v_fst_1818_; lean_object* v_snd_1819_; lean_object* v_fst_1820_; lean_object* v_snd_1821_; uint8_t v_decide_1822_; 
v_fst_1818_ = lean_ctor_get(v_key_1807_, 0);
v_snd_1819_ = lean_ctor_get(v_key_1807_, 1);
v_fst_1820_ = lean_ctor_get(v_a_1804_, 0);
v_snd_1821_ = lean_ctor_get(v_a_1804_, 1);
v_decide_1822_ = lean_nat_dec_eq(v_fst_1818_, v_fst_1820_);
if (v_decide_1822_ == 0)
{
goto v___jp_1813_;
}
else
{
uint8_t v_decide_1823_; 
v_decide_1823_ = lean_nat_dec_eq(v_snd_1819_, v_snd_1821_);
if (v_decide_1823_ == 0)
{
goto v___jp_1813_;
}
else
{
lean_object* v___x_1824_; 
lean_del_object(v___x_1811_);
lean_dec(v_value_1808_);
lean_dec(v_key_1807_);
v___x_1824_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1824_, 0, v_a_1804_);
lean_ctor_set(v___x_1824_, 1, v_b_1805_);
lean_ctor_set(v___x_1824_, 2, v_tail_1809_);
return v___x_1824_;
}
}
v___jp_1813_:
{
lean_object* v___x_1814_; lean_object* v___x_1816_; 
v___x_1814_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(v_a_1804_, v_b_1805_, v_tail_1809_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 2, v___x_1814_);
v___x_1816_ = v___x_1811_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_key_1807_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_value_1808_);
lean_ctor_set(v_reuseFailAlloc_1817_, 2, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(lean_object* v_a_1826_, lean_object* v_x_1827_){
_start:
{
if (lean_obj_tag(v_x_1827_) == 0)
{
uint8_t v___x_1828_; 
v___x_1828_ = 0;
return v___x_1828_;
}
else
{
lean_object* v_key_1829_; lean_object* v_tail_1830_; lean_object* v_fst_1831_; lean_object* v_snd_1832_; lean_object* v_fst_1833_; lean_object* v_snd_1834_; uint8_t v_decide_1835_; 
v_key_1829_ = lean_ctor_get(v_x_1827_, 0);
v_tail_1830_ = lean_ctor_get(v_x_1827_, 2);
v_fst_1831_ = lean_ctor_get(v_key_1829_, 0);
v_snd_1832_ = lean_ctor_get(v_key_1829_, 1);
v_fst_1833_ = lean_ctor_get(v_a_1826_, 0);
v_snd_1834_ = lean_ctor_get(v_a_1826_, 1);
v_decide_1835_ = lean_nat_dec_eq(v_fst_1831_, v_fst_1833_);
if (v_decide_1835_ == 0)
{
v_x_1827_ = v_tail_1830_;
goto _start;
}
else
{
uint8_t v_decide_1837_; 
v_decide_1837_ = lean_nat_dec_eq(v_snd_1832_, v_snd_1834_);
if (v_decide_1837_ == 0)
{
v_x_1827_ = v_tail_1830_;
goto _start;
}
else
{
return v_decide_1837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg___boxed(lean_object* v_a_1839_, lean_object* v_x_1840_){
_start:
{
uint8_t v_res_1841_; lean_object* v_r_1842_; 
v_res_1841_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(v_a_1839_, v_x_1840_);
lean_dec(v_x_1840_);
lean_dec_ref(v_a_1839_);
v_r_1842_ = lean_box(v_res_1841_);
return v_r_1842_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(lean_object* v_m_1843_, lean_object* v_a_1844_, lean_object* v_b_1845_){
_start:
{
lean_object* v_size_1846_; lean_object* v_buckets_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1894_; 
v_size_1846_ = lean_ctor_get(v_m_1843_, 0);
v_buckets_1847_ = lean_ctor_get(v_m_1843_, 1);
v_isSharedCheck_1894_ = !lean_is_exclusive(v_m_1843_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1849_ = v_m_1843_;
v_isShared_1850_ = v_isSharedCheck_1894_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_buckets_1847_);
lean_inc(v_size_1846_);
lean_dec(v_m_1843_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1894_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v_fst_1851_; lean_object* v_snd_1852_; lean_object* v___x_1853_; uint64_t v___x_1854_; uint64_t v___x_1855_; uint64_t v___x_1856_; uint64_t v___x_1857_; uint64_t v___x_1858_; uint64_t v_fold_1859_; uint64_t v___x_1860_; uint64_t v___x_1861_; uint64_t v___x_1862_; size_t v___x_1863_; size_t v___x_1864_; size_t v___x_1865_; size_t v___x_1866_; size_t v___x_1867_; lean_object* v_bkt_1868_; uint8_t v___x_1869_; 
v_fst_1851_ = lean_ctor_get(v_a_1844_, 0);
v_snd_1852_ = lean_ctor_get(v_a_1844_, 1);
v___x_1853_ = lean_array_get_size(v_buckets_1847_);
v___x_1854_ = l_String_instHashableRaw_hash(v_fst_1851_);
v___x_1855_ = l_String_instHashableRaw_hash(v_snd_1852_);
v___x_1856_ = lean_uint64_mix_hash(v___x_1854_, v___x_1855_);
v___x_1857_ = 32ULL;
v___x_1858_ = lean_uint64_shift_right(v___x_1856_, v___x_1857_);
v_fold_1859_ = lean_uint64_xor(v___x_1856_, v___x_1858_);
v___x_1860_ = 16ULL;
v___x_1861_ = lean_uint64_shift_right(v_fold_1859_, v___x_1860_);
v___x_1862_ = lean_uint64_xor(v_fold_1859_, v___x_1861_);
v___x_1863_ = lean_uint64_to_usize(v___x_1862_);
v___x_1864_ = lean_usize_of_nat(v___x_1853_);
v___x_1865_ = ((size_t)1ULL);
v___x_1866_ = lean_usize_sub(v___x_1864_, v___x_1865_);
v___x_1867_ = lean_usize_land(v___x_1863_, v___x_1866_);
v_bkt_1868_ = lean_array_uget_borrowed(v_buckets_1847_, v___x_1867_);
v___x_1869_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(v_a_1844_, v_bkt_1868_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; lean_object* v_size_x27_1871_; lean_object* v___x_1872_; lean_object* v_buckets_x27_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; uint8_t v___x_1879_; 
v___x_1870_ = lean_unsigned_to_nat(1u);
v_size_x27_1871_ = lean_nat_add(v_size_1846_, v___x_1870_);
lean_dec(v_size_1846_);
lean_inc(v_bkt_1868_);
v___x_1872_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1872_, 0, v_a_1844_);
lean_ctor_set(v___x_1872_, 1, v_b_1845_);
lean_ctor_set(v___x_1872_, 2, v_bkt_1868_);
v_buckets_x27_1873_ = lean_array_uset(v_buckets_1847_, v___x_1867_, v___x_1872_);
v___x_1874_ = lean_unsigned_to_nat(4u);
v___x_1875_ = lean_nat_mul(v_size_x27_1871_, v___x_1874_);
v___x_1876_ = lean_unsigned_to_nat(3u);
v___x_1877_ = lean_nat_div(v___x_1875_, v___x_1876_);
lean_dec(v___x_1875_);
v___x_1878_ = lean_array_get_size(v_buckets_x27_1873_);
v___x_1879_ = lean_nat_dec_le(v___x_1877_, v___x_1878_);
lean_dec(v___x_1877_);
if (v___x_1879_ == 0)
{
lean_object* v_val_1880_; lean_object* v___x_1882_; 
v_val_1880_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24___redArg(v_buckets_x27_1873_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 1, v_val_1880_);
lean_ctor_set(v___x_1849_, 0, v_size_x27_1871_);
v___x_1882_ = v___x_1849_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_size_x27_1871_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v_val_1880_);
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
lean_object* v___x_1885_; 
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 1, v_buckets_x27_1873_);
lean_ctor_set(v___x_1849_, 0, v_size_x27_1871_);
v___x_1885_ = v___x_1849_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_size_x27_1871_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v_buckets_x27_1873_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
else
{
lean_object* v___x_1887_; lean_object* v_buckets_x27_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1892_; 
lean_inc(v_bkt_1868_);
v___x_1887_ = lean_box(0);
v_buckets_x27_1888_ = lean_array_uset(v_buckets_1847_, v___x_1867_, v___x_1887_);
v___x_1889_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(v_a_1844_, v_b_1845_, v_bkt_1868_);
v___x_1890_ = lean_array_uset(v_buckets_x27_1888_, v___x_1867_, v___x_1889_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 1, v___x_1890_);
v___x_1892_ = v___x_1849_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_size_1846_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v___x_1890_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(uint8_t v___x_1897_, lean_object* v_as_1898_, size_t v_sz_1899_, size_t v_i_1900_, lean_object* v_b_1901_, lean_object* v___y_1902_){
_start:
{
uint8_t v___x_1904_; 
v___x_1904_ = lean_usize_dec_lt(v_i_1900_, v_sz_1899_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; 
v___x_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1905_, 0, v_b_1901_);
return v___x_1905_;
}
else
{
lean_object* v_snd_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1943_; 
v_snd_1906_ = lean_ctor_get(v_b_1901_, 1);
v_isSharedCheck_1943_ = !lean_is_exclusive(v_b_1901_);
if (v_isSharedCheck_1943_ == 0)
{
lean_object* v_unused_1944_; 
v_unused_1944_ = lean_ctor_get(v_b_1901_, 0);
lean_dec(v_unused_1944_);
v___x_1908_ = v_b_1901_;
v_isShared_1909_ = v_isSharedCheck_1943_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_snd_1906_);
lean_dec(v_b_1901_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1943_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v_ref_1910_; lean_object* v_a_1911_; lean_object* v_ref_1912_; lean_object* v_msg_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1942_; 
v_ref_1910_ = lean_ctor_get(v___y_1902_, 2);
v_a_1911_ = lean_array_uget(v_as_1898_, v_i_1900_);
v_ref_1912_ = lean_ctor_get(v_a_1911_, 0);
v_msg_1913_ = lean_ctor_get(v_a_1911_, 1);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_a_1911_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1915_ = v_a_1911_;
v_isShared_1916_ = v_isSharedCheck_1942_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_msg_1913_);
lean_inc(v_ref_1912_);
lean_dec(v_a_1911_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1942_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1917_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v_ref_1934_; lean_object* v___y_1936_; lean_object* v___x_1939_; 
v___x_1917_ = lean_box(0);
v_ref_1934_ = l_Lean_replaceRef(v_ref_1912_, v_ref_1910_);
lean_dec(v_ref_1912_);
v___x_1939_ = l_Lean_Syntax_getPos_x3f(v_ref_1934_, v___x_1897_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v___x_1940_; 
v___x_1940_ = lean_unsigned_to_nat(0u);
v___y_1936_ = v___x_1940_;
goto v___jp_1935_;
}
else
{
lean_object* v_val_1941_; 
v_val_1941_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_val_1941_);
lean_dec_ref_known(v___x_1939_, 1);
v___y_1936_ = v_val_1941_;
goto v___jp_1935_;
}
v___jp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 1, v___y_1920_);
lean_ctor_set(v___x_1908_, 0, v___y_1919_);
v___x_1922_ = v___x_1908_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v___y_1919_);
lean_ctor_set(v_reuseFailAlloc_1933_, 1, v___y_1920_);
v___x_1922_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v_pos2traces_1926_; lean_object* v___x_1928_; 
v___x_1923_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1924_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1906_, v___x_1922_, v___x_1923_);
v___x_1925_ = lean_array_push(v___x_1924_, v_msg_1913_);
v_pos2traces_1926_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_1906_, v___x_1922_, v___x_1925_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 1, v_pos2traces_1926_);
lean_ctor_set(v___x_1915_, 0, v___x_1917_);
v___x_1928_ = v___x_1915_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1917_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_pos2traces_1926_);
v___x_1928_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
size_t v___x_1929_; size_t v___x_1930_; 
v___x_1929_ = ((size_t)1ULL);
v___x_1930_ = lean_usize_add(v_i_1900_, v___x_1929_);
v_i_1900_ = v___x_1930_;
v_b_1901_ = v___x_1928_;
goto _start;
}
}
}
v___jp_1935_:
{
lean_object* v___x_1937_; 
v___x_1937_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1934_, v___x_1897_);
lean_dec(v_ref_1934_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_inc(v___y_1936_);
v___y_1919_ = v___y_1936_;
v___y_1920_ = v___y_1936_;
goto v___jp_1918_;
}
else
{
lean_object* v_val_1938_; 
v_val_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_val_1938_);
lean_dec_ref_known(v___x_1937_, 1);
v___y_1919_ = v___y_1936_;
v___y_1920_ = v_val_1938_;
goto v___jp_1918_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___boxed(lean_object* v___x_1945_, lean_object* v_as_1946_, lean_object* v_sz_1947_, lean_object* v_i_1948_, lean_object* v_b_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
uint8_t v___x_39171__boxed_1952_; size_t v_sz_boxed_1953_; size_t v_i_boxed_1954_; lean_object* v_res_1955_; 
v___x_39171__boxed_1952_ = lean_unbox(v___x_1945_);
v_sz_boxed_1953_ = lean_unbox_usize(v_sz_1947_);
lean_dec(v_sz_1947_);
v_i_boxed_1954_ = lean_unbox_usize(v_i_1948_);
lean_dec(v_i_1948_);
v_res_1955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(v___x_39171__boxed_1952_, v_as_1946_, v_sz_boxed_1953_, v_i_boxed_1954_, v_b_1949_, v___y_1950_);
lean_dec_ref(v___y_1950_);
lean_dec_ref(v_as_1946_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40(uint8_t v___x_1956_, lean_object* v_as_1957_, size_t v_sz_1958_, size_t v_i_1959_, lean_object* v_b_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
uint8_t v___x_1964_; 
v___x_1964_ = lean_usize_dec_lt(v_i_1959_, v_sz_1958_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1965_; 
v___x_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1965_, 0, v_b_1960_);
return v___x_1965_;
}
else
{
lean_object* v_snd_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_2003_; 
v_snd_1966_ = lean_ctor_get(v_b_1960_, 1);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_b_1960_);
if (v_isSharedCheck_2003_ == 0)
{
lean_object* v_unused_2004_; 
v_unused_2004_ = lean_ctor_get(v_b_1960_, 0);
lean_dec(v_unused_2004_);
v___x_1968_ = v_b_1960_;
v_isShared_1969_ = v_isSharedCheck_2003_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_snd_1966_);
lean_dec(v_b_1960_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_2003_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v_ref_1970_; lean_object* v_a_1971_; lean_object* v_ref_1972_; lean_object* v_msg_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_2002_; 
v_ref_1970_ = lean_ctor_get(v___y_1961_, 2);
v_a_1971_ = lean_array_uget(v_as_1957_, v_i_1959_);
v_ref_1972_ = lean_ctor_get(v_a_1971_, 0);
v_msg_1973_ = lean_ctor_get(v_a_1971_, 1);
v_isSharedCheck_2002_ = !lean_is_exclusive(v_a_1971_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1975_ = v_a_1971_;
v_isShared_1976_ = v_isSharedCheck_2002_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_msg_1973_);
lean_inc(v_ref_1972_);
lean_dec(v_a_1971_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_2002_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1977_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v_ref_1994_; lean_object* v___y_1996_; lean_object* v___x_1999_; 
v___x_1977_ = lean_box(0);
v_ref_1994_ = l_Lean_replaceRef(v_ref_1972_, v_ref_1970_);
lean_dec(v_ref_1972_);
v___x_1999_ = l_Lean_Syntax_getPos_x3f(v_ref_1994_, v___x_1956_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v___x_2000_; 
v___x_2000_ = lean_unsigned_to_nat(0u);
v___y_1996_ = v___x_2000_;
goto v___jp_1995_;
}
else
{
lean_object* v_val_2001_; 
v_val_2001_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_val_2001_);
lean_dec_ref_known(v___x_1999_, 1);
v___y_1996_ = v_val_2001_;
goto v___jp_1995_;
}
v___jp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 1, v___y_1980_);
lean_ctor_set(v___x_1968_, 0, v___y_1979_);
v___x_1982_ = v___x_1968_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___y_1979_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v___y_1980_);
v___x_1982_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v_pos2traces_1986_; lean_object* v___x_1988_; 
v___x_1983_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1984_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1966_, v___x_1982_, v___x_1983_);
v___x_1985_ = lean_array_push(v___x_1984_, v_msg_1973_);
v_pos2traces_1986_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_1966_, v___x_1982_, v___x_1985_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 1, v_pos2traces_1986_);
lean_ctor_set(v___x_1975_, 0, v___x_1977_);
v___x_1988_ = v___x_1975_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1977_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_pos2traces_1986_);
v___x_1988_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
size_t v___x_1989_; size_t v___x_1990_; lean_object* v___x_1991_; 
v___x_1989_ = ((size_t)1ULL);
v___x_1990_ = lean_usize_add(v_i_1959_, v___x_1989_);
v___x_1991_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(v___x_1956_, v_as_1957_, v_sz_1958_, v___x_1990_, v___x_1988_, v___y_1961_);
return v___x_1991_;
}
}
}
v___jp_1995_:
{
lean_object* v___x_1997_; 
v___x_1997_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1994_, v___x_1956_);
lean_dec(v_ref_1994_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_inc(v___y_1996_);
v___y_1979_ = v___y_1996_;
v___y_1980_ = v___y_1996_;
goto v___jp_1978_;
}
else
{
lean_object* v_val_1998_; 
v_val_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_val_1998_);
lean_dec_ref_known(v___x_1997_, 1);
v___y_1979_ = v___y_1996_;
v___y_1980_ = v_val_1998_;
goto v___jp_1978_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40___boxed(lean_object* v___x_2005_, lean_object* v_as_2006_, lean_object* v_sz_2007_, lean_object* v_i_2008_, lean_object* v_b_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
uint8_t v___x_39252__boxed_2013_; size_t v_sz_boxed_2014_; size_t v_i_boxed_2015_; lean_object* v_res_2016_; 
v___x_39252__boxed_2013_ = lean_unbox(v___x_2005_);
v_sz_boxed_2014_ = lean_unbox_usize(v_sz_2007_);
lean_dec(v_sz_2007_);
v_i_boxed_2015_ = lean_unbox_usize(v_i_2008_);
lean_dec(v_i_2008_);
v_res_2016_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40(v___x_39252__boxed_2013_, v_as_2006_, v_sz_boxed_2014_, v_i_boxed_2015_, v_b_2009_, v___y_2010_, v___y_2011_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec_ref(v_as_2006_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(lean_object* v_init_2017_, uint8_t v___x_2018_, lean_object* v_n_2019_, lean_object* v_b_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
if (lean_obj_tag(v_n_2019_) == 0)
{
lean_object* v_cs_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; size_t v_sz_2027_; size_t v___x_2028_; lean_object* v___x_2029_; 
v_cs_2024_ = lean_ctor_get(v_n_2019_, 0);
v___x_2025_ = lean_box(0);
v___x_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2025_);
lean_ctor_set(v___x_2026_, 1, v_b_2020_);
v_sz_2027_ = lean_array_size(v_cs_2024_);
v___x_2028_ = ((size_t)0ULL);
v___x_2029_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39(v_init_2017_, v___x_2018_, v_cs_2024_, v_sz_2027_, v___x_2028_, v___x_2026_, v___y_2021_, v___y_2022_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2044_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2032_ = v___x_2029_;
v_isShared_2033_ = v_isSharedCheck_2044_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2029_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2044_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v_fst_2034_; 
v_fst_2034_ = lean_ctor_get(v_a_2030_, 0);
if (lean_obj_tag(v_fst_2034_) == 0)
{
lean_object* v_snd_2035_; lean_object* v___x_2036_; lean_object* v___x_2038_; 
v_snd_2035_ = lean_ctor_get(v_a_2030_, 1);
lean_inc(v_snd_2035_);
lean_dec(v_a_2030_);
v___x_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2036_, 0, v_snd_2035_);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 0, v___x_2036_);
v___x_2038_ = v___x_2032_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
else
{
lean_object* v_val_2040_; lean_object* v___x_2042_; 
lean_inc_ref(v_fst_2034_);
lean_dec(v_a_2030_);
v_val_2040_ = lean_ctor_get(v_fst_2034_, 0);
lean_inc(v_val_2040_);
lean_dec_ref_known(v_fst_2034_, 1);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 0, v_val_2040_);
v___x_2042_ = v___x_2032_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_val_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
v_a_2045_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_2029_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2029_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
else
{
lean_object* v_vs_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; size_t v_sz_2056_; size_t v___x_2057_; lean_object* v___x_2058_; 
v_vs_2053_ = lean_ctor_get(v_n_2019_, 0);
v___x_2054_ = lean_box(0);
v___x_2055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
lean_ctor_set(v___x_2055_, 1, v_b_2020_);
v_sz_2056_ = lean_array_size(v_vs_2053_);
v___x_2057_ = ((size_t)0ULL);
v___x_2058_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40(v___x_2018_, v_vs_2053_, v_sz_2056_, v___x_2057_, v___x_2055_, v___y_2021_, v___y_2022_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2073_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2061_ = v___x_2058_;
v_isShared_2062_ = v_isSharedCheck_2073_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2058_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2073_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v_fst_2063_; 
v_fst_2063_ = lean_ctor_get(v_a_2059_, 0);
if (lean_obj_tag(v_fst_2063_) == 0)
{
lean_object* v_snd_2064_; lean_object* v___x_2065_; lean_object* v___x_2067_; 
v_snd_2064_ = lean_ctor_get(v_a_2059_, 1);
lean_inc(v_snd_2064_);
lean_dec(v_a_2059_);
v___x_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2065_, 0, v_snd_2064_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v___x_2065_);
v___x_2067_ = v___x_2061_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2065_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
else
{
lean_object* v_val_2069_; lean_object* v___x_2071_; 
lean_inc_ref(v_fst_2063_);
lean_dec(v_a_2059_);
v_val_2069_ = lean_ctor_get(v_fst_2063_, 0);
lean_inc(v_val_2069_);
lean_dec_ref_known(v_fst_2063_, 1);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v_val_2069_);
v___x_2071_ = v___x_2061_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_val_2069_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
v_a_2074_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2058_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2058_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39(lean_object* v_init_2082_, uint8_t v___x_2083_, lean_object* v_as_2084_, size_t v_sz_2085_, size_t v_i_2086_, lean_object* v_b_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
uint8_t v___x_2091_; 
v___x_2091_ = lean_usize_dec_lt(v_i_2086_, v_sz_2085_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; 
v___x_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2092_, 0, v_b_2087_);
return v___x_2092_;
}
else
{
lean_object* v_snd_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2127_; 
v_snd_2093_ = lean_ctor_get(v_b_2087_, 1);
v_isSharedCheck_2127_ = !lean_is_exclusive(v_b_2087_);
if (v_isSharedCheck_2127_ == 0)
{
lean_object* v_unused_2128_; 
v_unused_2128_ = lean_ctor_get(v_b_2087_, 0);
lean_dec(v_unused_2128_);
v___x_2095_ = v_b_2087_;
v_isShared_2096_ = v_isSharedCheck_2127_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_snd_2093_);
lean_dec(v_b_2087_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2127_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2097_; lean_object* v_a_2098_; lean_object* v___x_2099_; 
v___x_2097_ = lean_box(0);
v_a_2098_ = lean_array_uget_borrowed(v_as_2084_, v_i_2086_);
lean_inc(v_snd_2093_);
v___x_2099_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(v_init_2082_, v___x_2083_, v_a_2098_, v_snd_2093_, v___y_2088_, v___y_2089_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2118_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2102_ = v___x_2099_;
v_isShared_2103_ = v_isSharedCheck_2118_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2099_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2118_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
if (lean_obj_tag(v_a_2100_) == 0)
{
lean_object* v___x_2104_; lean_object* v___x_2106_; 
v___x_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2104_, 0, v_a_2100_);
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 0, v___x_2104_);
v___x_2106_ = v___x_2095_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2104_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_snd_2093_);
v___x_2106_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2108_; 
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2106_);
v___x_2108_ = v___x_2102_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; 
lean_del_object(v___x_2102_);
lean_dec(v_snd_2093_);
v_a_2111_ = lean_ctor_get(v_a_2100_, 0);
lean_inc(v_a_2111_);
lean_dec_ref_known(v_a_2100_, 1);
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 1, v_a_2111_);
lean_ctor_set(v___x_2095_, 0, v___x_2097_);
v___x_2113_ = v___x_2095_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2097_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_a_2111_);
v___x_2113_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
size_t v___x_2114_; size_t v___x_2115_; 
v___x_2114_ = ((size_t)1ULL);
v___x_2115_ = lean_usize_add(v_i_2086_, v___x_2114_);
v_i_2086_ = v___x_2115_;
v_b_2087_ = v___x_2113_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_del_object(v___x_2095_);
lean_dec(v_snd_2093_);
v_a_2119_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2099_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2099_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39___boxed(lean_object* v_init_2129_, lean_object* v___x_2130_, lean_object* v_as_2131_, lean_object* v_sz_2132_, lean_object* v_i_2133_, lean_object* v_b_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
uint8_t v___x_39333__boxed_2138_; size_t v_sz_boxed_2139_; size_t v_i_boxed_2140_; lean_object* v_res_2141_; 
v___x_39333__boxed_2138_ = lean_unbox(v___x_2130_);
v_sz_boxed_2139_ = lean_unbox_usize(v_sz_2132_);
lean_dec(v_sz_2132_);
v_i_boxed_2140_ = lean_unbox_usize(v_i_2133_);
lean_dec(v_i_2133_);
v_res_2141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39(v_init_2129_, v___x_39333__boxed_2138_, v_as_2131_, v_sz_boxed_2139_, v_i_boxed_2140_, v_b_2134_, v___y_2135_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec_ref(v_as_2131_);
lean_dec_ref(v_init_2129_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27___boxed(lean_object* v_init_2142_, lean_object* v___x_2143_, lean_object* v_n_2144_, lean_object* v_b_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
uint8_t v___x_39353__boxed_2149_; lean_object* v_res_2150_; 
v___x_39353__boxed_2149_ = lean_unbox(v___x_2143_);
v_res_2150_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(v_init_2142_, v___x_39353__boxed_2149_, v_n_2144_, v_b_2145_, v___y_2146_, v___y_2147_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec_ref(v_n_2144_);
lean_dec_ref(v_init_2142_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(uint8_t v___x_2151_, lean_object* v_as_2152_, size_t v_sz_2153_, size_t v_i_2154_, lean_object* v_b_2155_, lean_object* v___y_2156_){
_start:
{
uint8_t v___x_2158_; 
v___x_2158_ = lean_usize_dec_lt(v_i_2154_, v_sz_2153_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; 
v___x_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2159_, 0, v_b_2155_);
return v___x_2159_;
}
else
{
lean_object* v_snd_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2197_; 
v_snd_2160_ = lean_ctor_get(v_b_2155_, 1);
v_isSharedCheck_2197_ = !lean_is_exclusive(v_b_2155_);
if (v_isSharedCheck_2197_ == 0)
{
lean_object* v_unused_2198_; 
v_unused_2198_ = lean_ctor_get(v_b_2155_, 0);
lean_dec(v_unused_2198_);
v___x_2162_ = v_b_2155_;
v_isShared_2163_ = v_isSharedCheck_2197_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_snd_2160_);
lean_dec(v_b_2155_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2197_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v_ref_2164_; lean_object* v_a_2165_; lean_object* v_ref_2166_; lean_object* v_msg_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2196_; 
v_ref_2164_ = lean_ctor_get(v___y_2156_, 2);
v_a_2165_ = lean_array_uget(v_as_2152_, v_i_2154_);
v_ref_2166_ = lean_ctor_get(v_a_2165_, 0);
v_msg_2167_ = lean_ctor_get(v_a_2165_, 1);
v_isSharedCheck_2196_ = !lean_is_exclusive(v_a_2165_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2169_ = v_a_2165_;
v_isShared_2170_ = v_isSharedCheck_2196_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_msg_2167_);
lean_inc(v_ref_2166_);
lean_dec(v_a_2165_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2196_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2171_; lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v_ref_2188_; lean_object* v___y_2190_; lean_object* v___x_2193_; 
v___x_2171_ = lean_box(0);
v_ref_2188_ = l_Lean_replaceRef(v_ref_2166_, v_ref_2164_);
lean_dec(v_ref_2166_);
v___x_2193_ = l_Lean_Syntax_getPos_x3f(v_ref_2188_, v___x_2151_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v___x_2194_; 
v___x_2194_ = lean_unsigned_to_nat(0u);
v___y_2190_ = v___x_2194_;
goto v___jp_2189_;
}
else
{
lean_object* v_val_2195_; 
v_val_2195_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_val_2195_);
lean_dec_ref_known(v___x_2193_, 1);
v___y_2190_ = v_val_2195_;
goto v___jp_2189_;
}
v___jp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 1, v___y_2174_);
lean_ctor_set(v___x_2162_, 0, v___y_2173_);
v___x_2176_ = v___x_2162_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___y_2173_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v___y_2174_);
v___x_2176_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v_pos2traces_2180_; lean_object* v___x_2182_; 
v___x_2177_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_2178_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_2160_, v___x_2176_, v___x_2177_);
v___x_2179_ = lean_array_push(v___x_2178_, v_msg_2167_);
v_pos2traces_2180_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_2160_, v___x_2176_, v___x_2179_);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 1, v_pos2traces_2180_);
lean_ctor_set(v___x_2169_, 0, v___x_2171_);
v___x_2182_ = v___x_2169_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2171_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_pos2traces_2180_);
v___x_2182_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
size_t v___x_2183_; size_t v___x_2184_; 
v___x_2183_ = ((size_t)1ULL);
v___x_2184_ = lean_usize_add(v_i_2154_, v___x_2183_);
v_i_2154_ = v___x_2184_;
v_b_2155_ = v___x_2182_;
goto _start;
}
}
}
v___jp_2189_:
{
lean_object* v___x_2191_; 
v___x_2191_ = l_Lean_Syntax_getTailPos_x3f(v_ref_2188_, v___x_2151_);
lean_dec(v_ref_2188_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_inc(v___y_2190_);
v___y_2173_ = v___y_2190_;
v___y_2174_ = v___y_2190_;
goto v___jp_2172_;
}
else
{
lean_object* v_val_2192_; 
v_val_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_val_2192_);
lean_dec_ref_known(v___x_2191_, 1);
v___y_2173_ = v___y_2190_;
v___y_2174_ = v_val_2192_;
goto v___jp_2172_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg___boxed(lean_object* v___x_2199_, lean_object* v_as_2200_, lean_object* v_sz_2201_, lean_object* v_i_2202_, lean_object* v_b_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
uint8_t v___x_39536__boxed_2206_; size_t v_sz_boxed_2207_; size_t v_i_boxed_2208_; lean_object* v_res_2209_; 
v___x_39536__boxed_2206_ = lean_unbox(v___x_2199_);
v_sz_boxed_2207_ = lean_unbox_usize(v_sz_2201_);
lean_dec(v_sz_2201_);
v_i_boxed_2208_ = lean_unbox_usize(v_i_2202_);
lean_dec(v_i_2202_);
v_res_2209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(v___x_39536__boxed_2206_, v_as_2200_, v_sz_boxed_2207_, v_i_boxed_2208_, v_b_2203_, v___y_2204_);
lean_dec_ref(v___y_2204_);
lean_dec_ref(v_as_2200_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28(uint8_t v___x_2210_, lean_object* v_as_2211_, size_t v_sz_2212_, size_t v_i_2213_, lean_object* v_b_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
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
lean_object* v_snd_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2257_; 
v_snd_2220_ = lean_ctor_get(v_b_2214_, 1);
v_isSharedCheck_2257_ = !lean_is_exclusive(v_b_2214_);
if (v_isSharedCheck_2257_ == 0)
{
lean_object* v_unused_2258_; 
v_unused_2258_ = lean_ctor_get(v_b_2214_, 0);
lean_dec(v_unused_2258_);
v___x_2222_ = v_b_2214_;
v_isShared_2223_ = v_isSharedCheck_2257_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_snd_2220_);
lean_dec(v_b_2214_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2257_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v_ref_2224_; lean_object* v_a_2225_; lean_object* v_ref_2226_; lean_object* v_msg_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2256_; 
v_ref_2224_ = lean_ctor_get(v___y_2215_, 2);
v_a_2225_ = lean_array_uget(v_as_2211_, v_i_2213_);
v_ref_2226_ = lean_ctor_get(v_a_2225_, 0);
v_msg_2227_ = lean_ctor_get(v_a_2225_, 1);
v_isSharedCheck_2256_ = !lean_is_exclusive(v_a_2225_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2229_ = v_a_2225_;
v_isShared_2230_ = v_isSharedCheck_2256_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_msg_2227_);
lean_inc(v_ref_2226_);
lean_dec(v_a_2225_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2256_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2231_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v_ref_2248_; lean_object* v___y_2250_; lean_object* v___x_2253_; 
v___x_2231_ = lean_box(0);
v_ref_2248_ = l_Lean_replaceRef(v_ref_2226_, v_ref_2224_);
lean_dec(v_ref_2226_);
v___x_2253_ = l_Lean_Syntax_getPos_x3f(v_ref_2248_, v___x_2210_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v___x_2254_; 
v___x_2254_ = lean_unsigned_to_nat(0u);
v___y_2250_ = v___x_2254_;
goto v___jp_2249_;
}
else
{
lean_object* v_val_2255_; 
v_val_2255_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_val_2255_);
lean_dec_ref_known(v___x_2253_, 1);
v___y_2250_ = v_val_2255_;
goto v___jp_2249_;
}
v___jp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 1, v___y_2234_);
lean_ctor_set(v___x_2222_, 0, v___y_2233_);
v___x_2236_ = v___x_2222_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v___y_2233_);
lean_ctor_set(v_reuseFailAlloc_2247_, 1, v___y_2234_);
v___x_2236_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v_pos2traces_2240_; lean_object* v___x_2242_; 
v___x_2237_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_2238_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_2220_, v___x_2236_, v___x_2237_);
v___x_2239_ = lean_array_push(v___x_2238_, v_msg_2227_);
v_pos2traces_2240_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_2220_, v___x_2236_, v___x_2239_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 1, v_pos2traces_2240_);
lean_ctor_set(v___x_2229_, 0, v___x_2231_);
v___x_2242_ = v___x_2229_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2246_, 1, v_pos2traces_2240_);
v___x_2242_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
size_t v___x_2243_; size_t v___x_2244_; lean_object* v___x_2245_; 
v___x_2243_ = ((size_t)1ULL);
v___x_2244_ = lean_usize_add(v_i_2213_, v___x_2243_);
v___x_2245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(v___x_2210_, v_as_2211_, v_sz_2212_, v___x_2244_, v___x_2242_, v___y_2215_);
return v___x_2245_;
}
}
}
v___jp_2249_:
{
lean_object* v___x_2251_; 
v___x_2251_ = l_Lean_Syntax_getTailPos_x3f(v_ref_2248_, v___x_2210_);
lean_dec(v_ref_2248_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_inc(v___y_2250_);
v___y_2233_ = v___y_2250_;
v___y_2234_ = v___y_2250_;
goto v___jp_2232_;
}
else
{
lean_object* v_val_2252_; 
v_val_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_val_2252_);
lean_dec_ref_known(v___x_2251_, 1);
v___y_2233_ = v___y_2250_;
v___y_2234_ = v_val_2252_;
goto v___jp_2232_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28___boxed(lean_object* v___x_2259_, lean_object* v_as_2260_, lean_object* v_sz_2261_, lean_object* v_i_2262_, lean_object* v_b_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
uint8_t v___x_39616__boxed_2267_; size_t v_sz_boxed_2268_; size_t v_i_boxed_2269_; lean_object* v_res_2270_; 
v___x_39616__boxed_2267_ = lean_unbox(v___x_2259_);
v_sz_boxed_2268_ = lean_unbox_usize(v_sz_2261_);
lean_dec(v_sz_2261_);
v_i_boxed_2269_ = lean_unbox_usize(v_i_2262_);
lean_dec(v_i_2262_);
v_res_2270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28(v___x_39616__boxed_2267_, v_as_2260_, v_sz_boxed_2268_, v_i_boxed_2269_, v_b_2263_, v___y_2264_, v___y_2265_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v_as_2260_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(uint8_t v___x_2271_, lean_object* v_t_2272_, lean_object* v_init_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
lean_object* v_root_2277_; lean_object* v_tail_2278_; lean_object* v___x_2279_; 
v_root_2277_ = lean_ctor_get(v_t_2272_, 0);
v_tail_2278_ = lean_ctor_get(v_t_2272_, 1);
lean_inc_ref(v_init_2273_);
v___x_2279_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(v_init_2273_, v___x_2271_, v_root_2277_, v_init_2273_, v___y_2274_, v___y_2275_);
lean_dec_ref(v_init_2273_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2316_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2282_ = v___x_2279_;
v_isShared_2283_ = v_isSharedCheck_2316_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2279_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2316_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
if (lean_obj_tag(v_a_2280_) == 0)
{
lean_object* v_a_2284_; lean_object* v___x_2286_; 
v_a_2284_ = lean_ctor_get(v_a_2280_, 0);
lean_inc(v_a_2284_);
lean_dec_ref_known(v_a_2280_, 1);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 0, v_a_2284_);
v___x_2286_ = v___x_2282_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2284_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; size_t v_sz_2291_; size_t v___x_2292_; lean_object* v___x_2293_; 
lean_del_object(v___x_2282_);
v_a_2288_ = lean_ctor_get(v_a_2280_, 0);
lean_inc(v_a_2288_);
lean_dec_ref_known(v_a_2280_, 1);
v___x_2289_ = lean_box(0);
v___x_2290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
lean_ctor_set(v___x_2290_, 1, v_a_2288_);
v_sz_2291_ = lean_array_size(v_tail_2278_);
v___x_2292_ = ((size_t)0ULL);
v___x_2293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28(v___x_2271_, v_tail_2278_, v_sz_2291_, v___x_2292_, v___x_2290_, v___y_2274_, v___y_2275_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2307_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2296_ = v___x_2293_;
v_isShared_2297_ = v_isSharedCheck_2307_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2293_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2307_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v_fst_2298_; 
v_fst_2298_ = lean_ctor_get(v_a_2294_, 0);
if (lean_obj_tag(v_fst_2298_) == 0)
{
lean_object* v_snd_2299_; lean_object* v___x_2301_; 
v_snd_2299_ = lean_ctor_get(v_a_2294_, 1);
lean_inc(v_snd_2299_);
lean_dec(v_a_2294_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v_snd_2299_);
v___x_2301_ = v___x_2296_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_snd_2299_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
else
{
lean_object* v_val_2303_; lean_object* v___x_2305_; 
lean_inc_ref(v_fst_2298_);
lean_dec(v_a_2294_);
v_val_2303_ = lean_ctor_get(v_fst_2298_, 0);
lean_inc(v_val_2303_);
lean_dec_ref_known(v_fst_2298_, 1);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v_val_2303_);
v___x_2305_ = v___x_2296_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_val_2303_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
else
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
v_a_2308_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2293_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2293_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
}
}
else
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2324_; 
v_a_2317_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2319_ = v___x_2279_;
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2279_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2322_; 
if (v_isShared_2320_ == 0)
{
v___x_2322_ = v___x_2319_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_a_2317_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___boxed(lean_object* v___x_2325_, lean_object* v_t_2326_, lean_object* v_init_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
uint8_t v___x_39697__boxed_2331_; lean_object* v_res_2332_; 
v___x_39697__boxed_2331_ = lean_unbox(v___x_2325_);
v_res_2332_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(v___x_39697__boxed_2331_, v_t_2326_, v_init_2327_, v___y_2328_, v___y_2329_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec_ref(v_t_2326_);
return v_res_2332_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0(void){
_start:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2333_ = lean_unsigned_to_nat(32u);
v___x_2334_ = lean_mk_empty_array_with_capacity(v___x_2333_);
v___x_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
return v___x_2335_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1(void){
_start:
{
size_t v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2336_ = ((size_t)5ULL);
v___x_2337_ = lean_unsigned_to_nat(0u);
v___x_2338_ = lean_unsigned_to_nat(32u);
v___x_2339_ = lean_mk_empty_array_with_capacity(v___x_2338_);
v___x_2340_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0);
v___x_2341_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2341_, 0, v___x_2340_);
lean_ctor_set(v___x_2341_, 1, v___x_2339_);
lean_ctor_set(v___x_2341_, 2, v___x_2337_);
lean_ctor_set(v___x_2341_, 3, v___x_2337_);
lean_ctor_set_usize(v___x_2341_, 4, v___x_2336_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(lean_object* v___y_2342_){
_start:
{
lean_object* v___x_2344_; lean_object* v_traceState_2345_; lean_object* v_traces_2346_; lean_object* v___x_2347_; lean_object* v_traceState_2348_; lean_object* v_env_2349_; lean_object* v_nextMacroScope_2350_; lean_object* v_ngen_2351_; lean_object* v_auxDeclNGen_2352_; lean_object* v_cache_2353_; lean_object* v_recordedDeps_2354_; lean_object* v_messages_2355_; lean_object* v_infoState_2356_; lean_object* v_snapshotTasks_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2376_; 
v___x_2344_ = lean_st_ref_get(v___y_2342_);
v_traceState_2345_ = lean_ctor_get(v___x_2344_, 4);
lean_inc_ref(v_traceState_2345_);
lean_dec(v___x_2344_);
v_traces_2346_ = lean_ctor_get(v_traceState_2345_, 0);
lean_inc_ref(v_traces_2346_);
lean_dec_ref(v_traceState_2345_);
v___x_2347_ = lean_st_ref_take(v___y_2342_);
v_traceState_2348_ = lean_ctor_get(v___x_2347_, 4);
v_env_2349_ = lean_ctor_get(v___x_2347_, 0);
v_nextMacroScope_2350_ = lean_ctor_get(v___x_2347_, 1);
v_ngen_2351_ = lean_ctor_get(v___x_2347_, 2);
v_auxDeclNGen_2352_ = lean_ctor_get(v___x_2347_, 3);
v_cache_2353_ = lean_ctor_get(v___x_2347_, 5);
v_recordedDeps_2354_ = lean_ctor_get(v___x_2347_, 6);
v_messages_2355_ = lean_ctor_get(v___x_2347_, 7);
v_infoState_2356_ = lean_ctor_get(v___x_2347_, 8);
v_snapshotTasks_2357_ = lean_ctor_get(v___x_2347_, 9);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2359_ = v___x_2347_;
v_isShared_2360_ = v_isSharedCheck_2376_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_snapshotTasks_2357_);
lean_inc(v_infoState_2356_);
lean_inc(v_messages_2355_);
lean_inc(v_recordedDeps_2354_);
lean_inc(v_cache_2353_);
lean_inc(v_traceState_2348_);
lean_inc(v_auxDeclNGen_2352_);
lean_inc(v_ngen_2351_);
lean_inc(v_nextMacroScope_2350_);
lean_inc(v_env_2349_);
lean_dec(v___x_2347_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2376_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
uint64_t v_tid_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2374_; 
v_tid_2361_ = lean_ctor_get_uint64(v_traceState_2348_, sizeof(void*)*1);
v_isSharedCheck_2374_ = !lean_is_exclusive(v_traceState_2348_);
if (v_isSharedCheck_2374_ == 0)
{
lean_object* v_unused_2375_; 
v_unused_2375_ = lean_ctor_get(v_traceState_2348_, 0);
lean_dec(v_unused_2375_);
v___x_2363_ = v_traceState_2348_;
v_isShared_2364_ = v_isSharedCheck_2374_;
goto v_resetjp_2362_;
}
else
{
lean_dec(v_traceState_2348_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2374_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2365_; lean_object* v___x_2367_; 
v___x_2365_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 0, v___x_2365_);
v___x_2367_ = v___x_2363_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2365_);
lean_ctor_set_uint64(v_reuseFailAlloc_2373_, sizeof(void*)*1, v_tid_2361_);
v___x_2367_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
lean_object* v___x_2369_; 
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 4, v___x_2367_);
v___x_2369_ = v___x_2359_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_env_2349_);
lean_ctor_set(v_reuseFailAlloc_2372_, 1, v_nextMacroScope_2350_);
lean_ctor_set(v_reuseFailAlloc_2372_, 2, v_ngen_2351_);
lean_ctor_set(v_reuseFailAlloc_2372_, 3, v_auxDeclNGen_2352_);
lean_ctor_set(v_reuseFailAlloc_2372_, 4, v___x_2367_);
lean_ctor_set(v_reuseFailAlloc_2372_, 5, v_cache_2353_);
lean_ctor_set(v_reuseFailAlloc_2372_, 6, v_recordedDeps_2354_);
lean_ctor_set(v_reuseFailAlloc_2372_, 7, v_messages_2355_);
lean_ctor_set(v_reuseFailAlloc_2372_, 8, v_infoState_2356_);
lean_ctor_set(v_reuseFailAlloc_2372_, 9, v_snapshotTasks_2357_);
v___x_2369_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2370_ = lean_st_ref_put(v___y_2342_, v___x_2369_);
v___x_2371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2371_, 0, v_traces_2346_);
return v___x_2371_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___boxed(lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___y_2377_);
lean_dec(v___y_2377_);
return v_res_2379_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0(void){
_start:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2380_ = lean_box(0);
v___x_2381_ = lean_unsigned_to_nat(16u);
v___x_2382_ = lean_mk_array(v___x_2381_, v___x_2380_);
return v___x_2382_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1(void){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v_pos2traces_2385_; 
v___x_2383_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0, &l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0);
v___x_2384_ = lean_unsigned_to_nat(0u);
v_pos2traces_2385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_2385_, 0, v___x_2384_);
lean_ctor_set(v_pos2traces_2385_, 1, v___x_2383_);
return v_pos2traces_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9(lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v_toCold_2392_; lean_object* v_options_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v_toCold_2392_ = lean_ctor_get(v___y_2386_, 0);
v_options_2393_ = lean_ctor_get(v_toCold_2392_, 2);
v___x_2394_ = l_Lean_trace_profiler_output;
v___x_2395_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(v_options_2393_, v___x_2394_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v___x_2396_; uint8_t v___x_2397_; 
v___x_2396_ = l_Lean_trace_profiler_serve;
v___x_2397_ = l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(v_options_2393_, v___x_2396_);
if (v___x_2397_ == 0)
{
lean_object* v___x_2398_; lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2461_; 
v___x_2398_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___y_2387_);
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2401_ = v___x_2398_;
v_isShared_2402_ = v_isSharedCheck_2461_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2398_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2461_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
uint8_t v___x_2403_; 
v___x_2403_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_2399_);
if (v___x_2403_ == 0)
{
lean_object* v___x_2404_; lean_object* v_pos2traces_2405_; lean_object* v___x_2406_; 
lean_del_object(v___x_2401_);
v___x_2404_ = lean_unsigned_to_nat(0u);
v_pos2traces_2405_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1, &l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1);
v___x_2406_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(v___x_2403_, v_a_2399_, v_pos2traces_2405_, v___y_2386_, v___y_2387_);
lean_dec(v_a_2399_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; lean_object* v___y_2409_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2435_; lean_object* v_size_2441_; lean_object* v_buckets_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; uint8_t v___x_2445_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_a_2407_);
lean_dec_ref_known(v___x_2406_, 1);
v_size_2441_ = lean_ctor_get(v_a_2407_, 0);
lean_inc(v_size_2441_);
v_buckets_2442_ = lean_ctor_get(v_a_2407_, 1);
lean_inc_ref(v_buckets_2442_);
lean_dec(v_a_2407_);
v___x_2443_ = lean_mk_empty_array_with_capacity(v_size_2441_);
lean_dec(v_size_2441_);
v___x_2444_ = lean_array_get_size(v_buckets_2442_);
v___x_2445_ = lean_nat_dec_lt(v___x_2404_, v___x_2444_);
if (v___x_2445_ == 0)
{
lean_dec_ref(v_buckets_2442_);
v___y_2435_ = v___x_2443_;
goto v___jp_2434_;
}
else
{
size_t v___x_2446_; size_t v___x_2447_; lean_object* v___x_2448_; 
v___x_2446_ = ((size_t)0ULL);
v___x_2447_ = lean_usize_of_nat(v___x_2444_);
v___x_2448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23(v_buckets_2442_, v___x_2446_, v___x_2447_, v___x_2443_);
lean_dec_ref(v_buckets_2442_);
v___y_2435_ = v___x_2448_;
goto v___jp_2434_;
}
v___jp_2408_:
{
lean_object* v___x_2410_; size_t v_sz_2411_; size_t v___x_2412_; lean_object* v___x_2413_; 
v___x_2410_ = lean_box(0);
v_sz_2411_ = lean_array_size(v___y_2409_);
v___x_2412_ = ((size_t)0ULL);
v___x_2413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(v___x_2397_, v___y_2409_, v_sz_2411_, v___x_2412_, v___x_2410_, v___y_2386_, v___y_2387_);
lean_dec_ref(v___y_2409_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2420_; 
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2420_ == 0)
{
lean_object* v_unused_2421_; 
v_unused_2421_ = lean_ctor_get(v___x_2413_, 0);
lean_dec(v_unused_2421_);
v___x_2415_ = v___x_2413_;
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
else
{
lean_dec(v___x_2413_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 0, v___x_2410_);
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2410_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
else
{
return v___x_2413_;
}
}
v___jp_2422_:
{
lean_object* v___x_2427_; 
v___x_2427_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v___y_2423_, v___y_2425_, v___y_2424_, v___y_2426_);
lean_dec(v___y_2426_);
lean_dec(v___y_2423_);
v___y_2409_ = v___x_2427_;
goto v___jp_2408_;
}
v___jp_2428_:
{
uint8_t v___x_2433_; 
v___x_2433_ = lean_nat_dec_le(v___y_2432_, v___y_2431_);
if (v___x_2433_ == 0)
{
lean_dec(v___y_2431_);
lean_inc(v___y_2432_);
v___y_2423_ = v___y_2429_;
v___y_2424_ = v___y_2432_;
v___y_2425_ = v___y_2430_;
v___y_2426_ = v___y_2432_;
goto v___jp_2422_;
}
else
{
v___y_2423_ = v___y_2429_;
v___y_2424_ = v___y_2432_;
v___y_2425_ = v___y_2430_;
v___y_2426_ = v___y_2431_;
goto v___jp_2422_;
}
}
v___jp_2434_:
{
lean_object* v___x_2436_; uint8_t v___x_2437_; 
v___x_2436_ = lean_array_get_size(v___y_2435_);
v___x_2437_ = lean_nat_dec_eq(v___x_2436_, v___x_2404_);
if (v___x_2437_ == 0)
{
lean_object* v___x_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; 
v___x_2438_ = lean_unsigned_to_nat(1u);
v___x_2439_ = lean_nat_sub(v___x_2436_, v___x_2438_);
v___x_2440_ = lean_nat_dec_le(v___x_2404_, v___x_2439_);
if (v___x_2440_ == 0)
{
lean_inc(v___x_2439_);
v___y_2429_ = v___x_2436_;
v___y_2430_ = v___y_2435_;
v___y_2431_ = v___x_2439_;
v___y_2432_ = v___x_2439_;
goto v___jp_2428_;
}
else
{
v___y_2429_ = v___x_2436_;
v___y_2430_ = v___y_2435_;
v___y_2431_ = v___x_2439_;
v___y_2432_ = v___x_2404_;
goto v___jp_2428_;
}
}
else
{
v___y_2409_ = v___y_2435_;
goto v___jp_2408_;
}
}
}
else
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2456_; 
v_a_2449_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2451_ = v___x_2406_;
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2406_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
else
{
lean_object* v___x_2457_; lean_object* v___x_2459_; 
lean_dec(v_a_2399_);
v___x_2457_ = lean_box(0);
if (v_isShared_2402_ == 0)
{
lean_ctor_set(v___x_2401_, 0, v___x_2457_);
v___x_2459_ = v___x_2401_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2457_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
else
{
goto v___jp_2389_;
}
}
else
{
lean_dec_ref_known(v___x_2395_, 1);
goto v___jp_2389_;
}
v___jp_2389_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = lean_box(0);
v___x_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
return v___x_2391_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9___boxed(lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2462_, v___y_2463_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(lean_object* v_as_2466_, size_t v_sz_2467_, size_t v_i_2468_, lean_object* v_b_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
uint8_t v___x_2473_; 
v___x_2473_ = lean_usize_dec_lt(v_i_2468_, v_sz_2467_);
if (v___x_2473_ == 0)
{
lean_object* v___x_2474_; 
v___x_2474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2474_, 0, v_b_2469_);
return v___x_2474_;
}
else
{
lean_object* v___x_2475_; lean_object* v_a_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2475_ = lean_box(0);
v_a_2476_ = lean_array_uget_borrowed(v_as_2466_, v_i_2468_);
v___x_2477_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2470_);
lean_inc(v_a_2476_);
v___x_2478_ = l_Lean_Compiler_LCNF_resumeCompilation(v_a_2476_, v___x_2477_, v___y_2470_, v___y_2471_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v___x_2479_; 
lean_dec_ref_known(v___x_2478_, 1);
v___x_2479_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2470_, v___y_2471_);
if (lean_obj_tag(v___x_2479_) == 0)
{
size_t v___x_2480_; size_t v___x_2481_; 
lean_dec_ref_known(v___x_2479_, 1);
v___x_2480_ = ((size_t)1ULL);
v___x_2481_ = lean_usize_add(v_i_2468_, v___x_2480_);
v_i_2468_ = v___x_2481_;
v_b_2469_ = v___x_2475_;
goto _start;
}
else
{
return v___x_2479_;
}
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2484_; 
v_a_2483_ = lean_ctor_get(v___x_2478_, 0);
lean_inc(v_a_2483_);
lean_dec_ref_known(v___x_2478_, 1);
v___x_2484_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2470_, v___y_2471_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2491_ == 0)
{
lean_object* v_unused_2492_; 
v_unused_2492_ = lean_ctor_get(v___x_2484_, 0);
lean_dec(v_unused_2492_);
v___x_2486_ = v___x_2484_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_dec(v___x_2484_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
lean_ctor_set_tag(v___x_2486_, 1);
lean_ctor_set(v___x_2486_, 0, v_a_2483_);
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2483_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
else
{
lean_dec(v_a_2483_);
return v___x_2484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10___boxed(lean_object* v_as_2493_, lean_object* v_sz_2494_, lean_object* v_i_2495_, lean_object* v_b_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
size_t v_sz_boxed_2500_; size_t v_i_boxed_2501_; lean_object* v_res_2502_; 
v_sz_boxed_2500_ = lean_unbox_usize(v_sz_2494_);
lean_dec(v_sz_2494_);
v_i_boxed_2501_ = lean_unbox_usize(v_i_2495_);
lean_dec(v_i_2495_);
v_res_2502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(v_as_2493_, v_sz_boxed_2500_, v_i_boxed_2501_, v_b_2496_, v___y_2497_, v___y_2498_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec_ref(v_as_2493_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(lean_object* v_as_2503_, size_t v_sz_2504_, size_t v_i_2505_, lean_object* v_b_2506_, lean_object* v___y_2507_){
_start:
{
uint8_t v___x_2509_; 
v___x_2509_ = lean_usize_dec_lt(v_i_2505_, v_sz_2504_);
if (v___x_2509_ == 0)
{
lean_object* v___x_2510_; 
v___x_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2510_, 0, v_b_2506_);
return v___x_2510_;
}
else
{
uint8_t v___x_2511_; lean_object* v_a_2512_; lean_object* v___x_2513_; lean_object* v_ref_2514_; lean_object* v___x_2515_; 
lean_dec_ref(v_b_2506_);
v___x_2511_ = 0;
v_a_2512_ = lean_array_uget_borrowed(v_as_2503_, v_i_2505_);
lean_inc(v_a_2512_);
v___x_2513_ = l_Lean_Message_toString(v_a_2512_, v___x_2511_);
v_ref_2514_ = lean_ctor_get(v___y_2507_, 2);
v___x_2515_ = l_IO_eprintln___at___00main_spec__6(v___x_2513_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v___x_2516_; size_t v___x_2517_; size_t v___x_2518_; 
lean_dec_ref_known(v___x_2515_, 1);
v___x_2516_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_2517_ = ((size_t)1ULL);
v___x_2518_ = lean_usize_add(v_i_2505_, v___x_2517_);
v_i_2505_ = v___x_2518_;
v_b_2506_ = v___x_2516_;
goto _start;
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2531_; 
v_a_2520_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2522_ = v___x_2515_;
v_isShared_2523_ = v_isSharedCheck_2531_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2515_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2531_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2529_; 
v___x_2524_ = lean_io_error_to_string(v_a_2520_);
v___x_2525_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2524_);
v___x_2526_ = l_Lean_MessageData_ofFormat(v___x_2525_);
lean_inc(v_ref_2514_);
v___x_2527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2527_, 0, v_ref_2514_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
if (v_isShared_2523_ == 0)
{
lean_ctor_set(v___x_2522_, 0, v___x_2527_);
v___x_2529_ = v___x_2522_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2527_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg___boxed(lean_object* v_as_2532_, lean_object* v_sz_2533_, lean_object* v_i_2534_, lean_object* v_b_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
size_t v_sz_boxed_2538_; size_t v_i_boxed_2539_; lean_object* v_res_2540_; 
v_sz_boxed_2538_ = lean_unbox_usize(v_sz_2533_);
lean_dec(v_sz_2533_);
v_i_boxed_2539_ = lean_unbox_usize(v_i_2534_);
lean_dec(v_i_2534_);
v_res_2540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(v_as_2532_, v_sz_boxed_2538_, v_i_boxed_2539_, v_b_2535_, v___y_2536_);
lean_dec_ref(v___y_2536_);
lean_dec_ref(v_as_2532_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38(lean_object* v_as_2541_, size_t v_sz_2542_, size_t v_i_2543_, lean_object* v_b_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_){
_start:
{
uint8_t v___x_2548_; 
v___x_2548_ = lean_usize_dec_lt(v_i_2543_, v_sz_2542_);
if (v___x_2548_ == 0)
{
lean_object* v___x_2549_; 
v___x_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2549_, 0, v_b_2544_);
return v___x_2549_;
}
else
{
uint8_t v___x_2550_; lean_object* v_a_2551_; lean_object* v___x_2552_; lean_object* v_ref_2553_; lean_object* v___x_2554_; 
lean_dec_ref(v_b_2544_);
v___x_2550_ = 0;
v_a_2551_ = lean_array_uget_borrowed(v_as_2541_, v_i_2543_);
lean_inc(v_a_2551_);
v___x_2552_ = l_Lean_Message_toString(v_a_2551_, v___x_2550_);
v_ref_2553_ = lean_ctor_get(v___y_2545_, 2);
v___x_2554_ = l_IO_eprintln___at___00main_spec__6(v___x_2552_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v___x_2555_; size_t v___x_2556_; size_t v___x_2557_; lean_object* v___x_2558_; 
lean_dec_ref_known(v___x_2554_, 1);
v___x_2555_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_2556_ = ((size_t)1ULL);
v___x_2557_ = lean_usize_add(v_i_2543_, v___x_2556_);
v___x_2558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(v_as_2541_, v_sz_2542_, v___x_2557_, v___x_2555_, v___y_2545_);
return v___x_2558_;
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2570_; 
v_a_2559_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2561_ = v___x_2554_;
v_isShared_2562_ = v_isSharedCheck_2570_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2554_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2570_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2568_; 
v___x_2563_ = lean_io_error_to_string(v_a_2559_);
v___x_2564_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2563_);
v___x_2565_ = l_Lean_MessageData_ofFormat(v___x_2564_);
lean_inc(v_ref_2553_);
v___x_2566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2566_, 0, v_ref_2553_);
lean_ctor_set(v___x_2566_, 1, v___x_2565_);
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v___x_2566_);
v___x_2568_ = v___x_2561_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2566_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38___boxed(lean_object* v_as_2571_, lean_object* v_sz_2572_, lean_object* v_i_2573_, lean_object* v_b_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
size_t v_sz_boxed_2578_; size_t v_i_boxed_2579_; lean_object* v_res_2580_; 
v_sz_boxed_2578_ = lean_unbox_usize(v_sz_2572_);
lean_dec(v_sz_2572_);
v_i_boxed_2579_ = lean_unbox_usize(v_i_2573_);
lean_dec(v_i_2573_);
v_res_2580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38(v_as_2571_, v_sz_boxed_2578_, v_i_boxed_2579_, v_b_2574_, v___y_2575_, v___y_2576_);
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec_ref(v_as_2571_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(lean_object* v_init_2581_, lean_object* v_n_2582_, lean_object* v_b_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
if (lean_obj_tag(v_n_2582_) == 0)
{
lean_object* v_cs_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; size_t v_sz_2590_; size_t v___x_2591_; lean_object* v___x_2592_; 
v_cs_2587_ = lean_ctor_get(v_n_2582_, 0);
v___x_2588_ = lean_box(0);
v___x_2589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2588_);
lean_ctor_set(v___x_2589_, 1, v_b_2583_);
v_sz_2590_ = lean_array_size(v_cs_2587_);
v___x_2591_ = ((size_t)0ULL);
v___x_2592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37(v_init_2581_, v_cs_2587_, v_sz_2590_, v___x_2591_, v___x_2589_, v___y_2584_, v___y_2585_);
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
v_vs_2616_ = lean_ctor_get(v_n_2582_, 0);
v___x_2617_ = lean_box(0);
v___x_2618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2617_);
lean_ctor_set(v___x_2618_, 1, v_b_2583_);
v_sz_2619_ = lean_array_size(v_vs_2616_);
v___x_2620_ = ((size_t)0ULL);
v___x_2621_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38(v_vs_2616_, v_sz_2619_, v___x_2620_, v___x_2618_, v___y_2584_, v___y_2585_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37(lean_object* v_init_2645_, lean_object* v_as_2646_, size_t v_sz_2647_, size_t v_i_2648_, lean_object* v_b_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
uint8_t v___x_2653_; 
v___x_2653_ = lean_usize_dec_lt(v_i_2648_, v_sz_2647_);
if (v___x_2653_ == 0)
{
lean_object* v___x_2654_; 
v___x_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2654_, 0, v_b_2649_);
return v___x_2654_;
}
else
{
lean_object* v_snd_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2689_; 
v_snd_2655_ = lean_ctor_get(v_b_2649_, 1);
v_isSharedCheck_2689_ = !lean_is_exclusive(v_b_2649_);
if (v_isSharedCheck_2689_ == 0)
{
lean_object* v_unused_2690_; 
v_unused_2690_ = lean_ctor_get(v_b_2649_, 0);
lean_dec(v_unused_2690_);
v___x_2657_ = v_b_2649_;
v_isShared_2658_ = v_isSharedCheck_2689_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_snd_2655_);
lean_dec(v_b_2649_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2689_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2659_; lean_object* v_a_2660_; lean_object* v___x_2661_; 
v___x_2659_ = lean_box(0);
v_a_2660_ = lean_array_uget_borrowed(v_as_2646_, v_i_2648_);
lean_inc(v_snd_2655_);
v___x_2661_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(v_init_2645_, v_a_2660_, v_snd_2655_, v___y_2650_, v___y_2651_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2680_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2664_ = v___x_2661_;
v_isShared_2665_ = v_isSharedCheck_2680_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2661_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2680_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
if (lean_obj_tag(v_a_2662_) == 0)
{
lean_object* v___x_2666_; lean_object* v___x_2668_; 
v___x_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2666_, 0, v_a_2662_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 0, v___x_2666_);
v___x_2668_ = v___x_2657_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2666_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v_snd_2655_);
v___x_2668_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
lean_object* v___x_2670_; 
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 0, v___x_2668_);
v___x_2670_ = v___x_2664_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2668_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
else
{
lean_object* v_a_2673_; lean_object* v___x_2675_; 
lean_del_object(v___x_2664_);
lean_dec(v_snd_2655_);
v_a_2673_ = lean_ctor_get(v_a_2662_, 0);
lean_inc(v_a_2673_);
lean_dec_ref_known(v_a_2662_, 1);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 1, v_a_2673_);
lean_ctor_set(v___x_2657_, 0, v___x_2659_);
v___x_2675_ = v___x_2657_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2659_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v_a_2673_);
v___x_2675_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
size_t v___x_2676_; size_t v___x_2677_; 
v___x_2676_ = ((size_t)1ULL);
v___x_2677_ = lean_usize_add(v_i_2648_, v___x_2676_);
v_i_2648_ = v___x_2677_;
v_b_2649_ = v___x_2675_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2688_; 
lean_del_object(v___x_2657_);
lean_dec(v_snd_2655_);
v_a_2681_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2683_ = v___x_2661_;
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2661_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2686_; 
if (v_isShared_2684_ == 0)
{
v___x_2686_ = v___x_2683_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_a_2681_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37___boxed(lean_object* v_init_2691_, lean_object* v_as_2692_, lean_object* v_sz_2693_, lean_object* v_i_2694_, lean_object* v_b_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
size_t v_sz_boxed_2699_; size_t v_i_boxed_2700_; lean_object* v_res_2701_; 
v_sz_boxed_2699_ = lean_unbox_usize(v_sz_2693_);
lean_dec(v_sz_2693_);
v_i_boxed_2700_ = lean_unbox_usize(v_i_2694_);
lean_dec(v_i_2694_);
v_res_2701_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37(v_init_2691_, v_as_2692_, v_sz_boxed_2699_, v_i_boxed_2700_, v_b_2695_, v___y_2696_, v___y_2697_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec_ref(v_as_2692_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26___boxed(lean_object* v_init_2702_, lean_object* v_n_2703_, lean_object* v_b_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(v_init_2702_, v_n_2703_, v_b_2704_, v___y_2705_, v___y_2706_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec_ref(v_n_2703_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(lean_object* v_as_2709_, size_t v_sz_2710_, size_t v_i_2711_, lean_object* v_b_2712_, lean_object* v___y_2713_){
_start:
{
uint8_t v___x_2715_; 
v___x_2715_ = lean_usize_dec_lt(v_i_2711_, v_sz_2710_);
if (v___x_2715_ == 0)
{
lean_object* v___x_2716_; 
v___x_2716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2716_, 0, v_b_2712_);
return v___x_2716_;
}
else
{
uint8_t v___x_2717_; lean_object* v_a_2718_; lean_object* v___x_2719_; lean_object* v_ref_2720_; lean_object* v___x_2721_; 
lean_dec_ref(v_b_2712_);
v___x_2717_ = 0;
v_a_2718_ = lean_array_uget_borrowed(v_as_2709_, v_i_2711_);
lean_inc(v_a_2718_);
v___x_2719_ = l_Lean_Message_toString(v_a_2718_, v___x_2717_);
v_ref_2720_ = lean_ctor_get(v___y_2713_, 2);
v___x_2721_ = l_IO_eprintln___at___00main_spec__6(v___x_2719_);
if (lean_obj_tag(v___x_2721_) == 0)
{
lean_object* v___x_2722_; size_t v___x_2723_; size_t v___x_2724_; 
lean_dec_ref_known(v___x_2721_, 1);
v___x_2722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_2723_ = ((size_t)1ULL);
v___x_2724_ = lean_usize_add(v_i_2711_, v___x_2723_);
v_i_2711_ = v___x_2724_;
v_b_2712_ = v___x_2722_;
goto _start;
}
else
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2737_; 
v_a_2726_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2728_ = v___x_2721_;
v_isShared_2729_ = v_isSharedCheck_2737_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2721_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2737_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2735_; 
v___x_2730_ = lean_io_error_to_string(v_a_2726_);
v___x_2731_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2730_);
v___x_2732_ = l_Lean_MessageData_ofFormat(v___x_2731_);
lean_inc(v_ref_2720_);
v___x_2733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2733_, 0, v_ref_2720_);
lean_ctor_set(v___x_2733_, 1, v___x_2732_);
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 0, v___x_2733_);
v___x_2735_ = v___x_2728_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2733_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg___boxed(lean_object* v_as_2738_, lean_object* v_sz_2739_, lean_object* v_i_2740_, lean_object* v_b_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_){
_start:
{
size_t v_sz_boxed_2744_; size_t v_i_boxed_2745_; lean_object* v_res_2746_; 
v_sz_boxed_2744_ = lean_unbox_usize(v_sz_2739_);
lean_dec(v_sz_2739_);
v_i_boxed_2745_ = lean_unbox_usize(v_i_2740_);
lean_dec(v_i_2740_);
v_res_2746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(v_as_2738_, v_sz_boxed_2744_, v_i_boxed_2745_, v_b_2741_, v___y_2742_);
lean_dec_ref(v___y_2742_);
lean_dec_ref(v_as_2738_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27(lean_object* v_as_2747_, size_t v_sz_2748_, size_t v_i_2749_, lean_object* v_b_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
uint8_t v___x_2754_; 
v___x_2754_ = lean_usize_dec_lt(v_i_2749_, v_sz_2748_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2755_; 
v___x_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2755_, 0, v_b_2750_);
return v___x_2755_;
}
else
{
uint8_t v___x_2756_; lean_object* v_a_2757_; lean_object* v___x_2758_; lean_object* v_ref_2759_; lean_object* v___x_2760_; 
lean_dec_ref(v_b_2750_);
v___x_2756_ = 0;
v_a_2757_ = lean_array_uget_borrowed(v_as_2747_, v_i_2749_);
lean_inc(v_a_2757_);
v___x_2758_ = l_Lean_Message_toString(v_a_2757_, v___x_2756_);
v_ref_2759_ = lean_ctor_get(v___y_2751_, 2);
v___x_2760_ = l_IO_eprintln___at___00main_spec__6(v___x_2758_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v___x_2761_; size_t v___x_2762_; size_t v___x_2763_; lean_object* v___x_2764_; 
lean_dec_ref_known(v___x_2760_, 1);
v___x_2761_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_2762_ = ((size_t)1ULL);
v___x_2763_ = lean_usize_add(v_i_2749_, v___x_2762_);
v___x_2764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(v_as_2747_, v_sz_2748_, v___x_2763_, v___x_2761_, v___y_2751_);
return v___x_2764_;
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2776_; 
v_a_2765_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2767_ = v___x_2760_;
v_isShared_2768_ = v_isSharedCheck_2776_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2760_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2776_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; 
v___x_2769_ = lean_io_error_to_string(v_a_2765_);
v___x_2770_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2769_);
v___x_2771_ = l_Lean_MessageData_ofFormat(v___x_2770_);
lean_inc(v_ref_2759_);
v___x_2772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2772_, 0, v_ref_2759_);
lean_ctor_set(v___x_2772_, 1, v___x_2771_);
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 0, v___x_2772_);
v___x_2774_ = v___x_2767_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27___boxed(lean_object* v_as_2777_, lean_object* v_sz_2778_, lean_object* v_i_2779_, lean_object* v_b_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
size_t v_sz_boxed_2784_; size_t v_i_boxed_2785_; lean_object* v_res_2786_; 
v_sz_boxed_2784_ = lean_unbox_usize(v_sz_2778_);
lean_dec(v_sz_2778_);
v_i_boxed_2785_ = lean_unbox_usize(v_i_2779_);
lean_dec(v_i_2779_);
v_res_2786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27(v_as_2777_, v_sz_boxed_2784_, v_i_boxed_2785_, v_b_2780_, v___y_2781_, v___y_2782_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec_ref(v_as_2777_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__11(lean_object* v_t_2787_, lean_object* v_init_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v_root_2792_; lean_object* v_tail_2793_; lean_object* v___x_2794_; 
v_root_2792_ = lean_ctor_get(v_t_2787_, 0);
v_tail_2793_ = lean_ctor_get(v_t_2787_, 1);
v___x_2794_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(v_init_2788_, v_root_2792_, v_init_2788_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2831_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2797_ = v___x_2794_;
v_isShared_2798_ = v_isSharedCheck_2831_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2794_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2831_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
if (lean_obj_tag(v_a_2795_) == 0)
{
lean_object* v_a_2799_; lean_object* v___x_2801_; 
v_a_2799_ = lean_ctor_get(v_a_2795_, 0);
lean_inc(v_a_2799_);
lean_dec_ref_known(v_a_2795_, 1);
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 0, v_a_2799_);
v___x_2801_ = v___x_2797_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2799_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
else
{
lean_object* v_a_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; size_t v_sz_2806_; size_t v___x_2807_; lean_object* v___x_2808_; 
lean_del_object(v___x_2797_);
v_a_2803_ = lean_ctor_get(v_a_2795_, 0);
lean_inc(v_a_2803_);
lean_dec_ref_known(v_a_2795_, 1);
v___x_2804_ = lean_box(0);
v___x_2805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
lean_ctor_set(v___x_2805_, 1, v_a_2803_);
v_sz_2806_ = lean_array_size(v_tail_2793_);
v___x_2807_ = ((size_t)0ULL);
v___x_2808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27(v_tail_2793_, v_sz_2806_, v___x_2807_, v___x_2805_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2822_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2811_ = v___x_2808_;
v_isShared_2812_ = v_isSharedCheck_2822_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2808_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2822_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v_fst_2813_; 
v_fst_2813_ = lean_ctor_get(v_a_2809_, 0);
if (lean_obj_tag(v_fst_2813_) == 0)
{
lean_object* v_snd_2814_; lean_object* v___x_2816_; 
v_snd_2814_ = lean_ctor_get(v_a_2809_, 1);
lean_inc(v_snd_2814_);
lean_dec(v_a_2809_);
if (v_isShared_2812_ == 0)
{
lean_ctor_set(v___x_2811_, 0, v_snd_2814_);
v___x_2816_ = v___x_2811_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_snd_2814_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
else
{
lean_object* v_val_2818_; lean_object* v___x_2820_; 
lean_inc_ref(v_fst_2813_);
lean_dec(v_a_2809_);
v_val_2818_ = lean_ctor_get(v_fst_2813_, 0);
lean_inc(v_val_2818_);
lean_dec_ref_known(v_fst_2813_, 1);
if (v_isShared_2812_ == 0)
{
lean_ctor_set(v___x_2811_, 0, v_val_2818_);
v___x_2820_ = v___x_2811_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_val_2818_);
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
else
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
v_a_2823_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2808_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2808_);
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
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
v_a_2832_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2794_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2794_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__11___boxed(lean_object* v_t_2840_, lean_object* v_init_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l_Lean_PersistentArray_forIn___at___00main_spec__11(v_t_2840_, v_init_2841_, v___y_2842_, v___y_2843_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec_ref(v_t_2840_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(lean_object* v_as_2846_, size_t v_sz_2847_, size_t v_i_2848_, lean_object* v_b_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
uint8_t v___x_2853_; 
v___x_2853_ = lean_usize_dec_lt(v_i_2848_, v_sz_2847_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2854_; 
v___x_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2854_, 0, v_b_2849_);
return v___x_2854_;
}
else
{
lean_object* v_a_2855_; lean_object* v_declNames_2856_; lean_object* v___x_2857_; size_t v_sz_2858_; size_t v___x_2859_; lean_object* v___x_2860_; 
v_a_2855_ = lean_array_uget_borrowed(v_as_2846_, v_i_2848_);
v_declNames_2856_ = lean_ctor_get(v_a_2855_, 0);
v___x_2857_ = lean_box(0);
v_sz_2858_ = lean_array_size(v_declNames_2856_);
v___x_2859_ = ((size_t)0ULL);
v___x_2860_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(v_declNames_2856_, v_sz_2858_, v___x_2859_, v___x_2857_, v___y_2850_, v___y_2851_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v___x_2861_; 
lean_dec_ref_known(v___x_2860_, 1);
v___x_2861_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v___y_2851_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; lean_object* v_unreported_2863_; lean_object* v___x_2864_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref_known(v___x_2861_, 1);
v_unreported_2863_ = lean_ctor_get(v_a_2862_, 1);
lean_inc_ref(v_unreported_2863_);
lean_dec(v_a_2862_);
v___x_2864_ = l_Lean_PersistentArray_forIn___at___00main_spec__11(v_unreported_2863_, v___x_2857_, v___y_2850_, v___y_2851_);
lean_dec_ref(v_unreported_2863_);
if (lean_obj_tag(v___x_2864_) == 0)
{
size_t v___x_2865_; size_t v___x_2866_; 
lean_dec_ref_known(v___x_2864_, 1);
v___x_2865_ = ((size_t)1ULL);
v___x_2866_ = lean_usize_add(v_i_2848_, v___x_2865_);
v_i_2848_ = v___x_2866_;
v_b_2849_ = v___x_2857_;
goto _start;
}
else
{
return v___x_2864_;
}
}
else
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2875_; 
v_a_2868_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2870_ = v___x_2861_;
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2861_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2873_; 
if (v_isShared_2871_ == 0)
{
v___x_2873_ = v___x_2870_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_a_2868_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
else
{
return v___x_2860_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___boxed(lean_object* v_as_2876_, lean_object* v_sz_2877_, lean_object* v_i_2878_, lean_object* v_b_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
size_t v_sz_boxed_2883_; size_t v_i_boxed_2884_; lean_object* v_res_2885_; 
v_sz_boxed_2883_ = lean_unbox_usize(v_sz_2877_);
lean_dec(v_sz_2877_);
v_i_boxed_2884_ = lean_unbox_usize(v_i_2878_);
lean_dec(v_i_2878_);
v_res_2885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(v_as_2876_, v_sz_boxed_2883_, v_i_boxed_2884_, v_b_2879_, v___y_2880_, v___y_2881_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec_ref(v_as_2876_);
return v_res_2885_;
}
}
static lean_object* _init_l_main___closed__1(void){
_start:
{
lean_object* v___x_2887_; 
v___x_2887_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg();
return v___x_2887_;
}
}
static lean_object* _init_l_main___closed__2(void){
_start:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2888_ = l_Lean_instInhabitedClassState_default;
v___x_2889_ = lean_box(0);
v___x_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2889_);
lean_ctor_set(v___x_2890_, 1, v___x_2888_);
return v___x_2890_;
}
}
static lean_object* _init_l_main___closed__3(void){
_start:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2891_ = l_Lean_Meta_Match_Extension_instInhabitedState;
v___x_2892_ = lean_box(0);
v___x_2893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2892_);
lean_ctor_set(v___x_2893_, 1, v___x_2891_);
return v___x_2893_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_2894_; 
v___x_2894_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_2894_;
}
}
static lean_object* _init_l_main___closed__5(void){
_start:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2895_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2896_ = lean_box(0);
v___x_2897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2896_);
lean_ctor_set(v___x_2897_, 1, v___x_2895_);
return v___x_2897_;
}
}
static lean_object* _init_l_main___closed__6(void){
_start:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_2899_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2898_);
return v___x_2899_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = l_Array_instInhabited___redArg();
return v___x_2900_;
}
}
static lean_object* _init_l_main___closed__17(void){
_start:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2913_ = ((lean_object*)(l_main___closed__16));
v___x_2914_ = lean_unsigned_to_nat(27u);
v___x_2915_ = lean_unsigned_to_nat(151u);
v___x_2916_ = ((lean_object*)(l_main___closed__15));
v___x_2917_ = ((lean_object*)(l_main___closed__14));
v___x_2918_ = l_mkPanicMessageWithDecl(v___x_2917_, v___x_2916_, v___x_2915_, v___x_2914_, v___x_2913_);
return v___x_2918_;
}
}
static lean_object* _init_l_main___closed__19(void){
_start:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2920_ = ((lean_object*)(l_main___closed__16));
v___x_2921_ = lean_unsigned_to_nat(51u);
v___x_2922_ = lean_unsigned_to_nat(124u);
v___x_2923_ = ((lean_object*)(l_main___closed__15));
v___x_2924_ = ((lean_object*)(l_main___closed__14));
v___x_2925_ = l_mkPanicMessageWithDecl(v___x_2924_, v___x_2923_, v___x_2922_, v___x_2921_, v___x_2920_);
return v___x_2925_;
}
}
static lean_object* _init_l_main___closed__20(void){
_start:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2926_ = lean_unsigned_to_nat(1u);
v___x_2927_ = l_Lean_firstFrontendMacroScope;
v___x_2928_ = lean_nat_add(v___x_2927_, v___x_2926_);
return v___x_2928_;
}
}
static lean_object* _init_l_main___closed__24(void){
_start:
{
lean_object* v___x_2935_; uint64_t v___x_2936_; lean_object* v___x_2937_; 
v___x_2935_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
v___x_2936_ = 0ULL;
v___x_2937_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2937_, 0, v___x_2935_);
lean_ctor_set_uint64(v___x_2937_, sizeof(void*)*1, v___x_2936_);
return v___x_2937_;
}
}
static lean_object* _init_l_main___closed__25(void){
_start:
{
lean_object* v___x_2938_; 
v___x_2938_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2938_;
}
}
static lean_object* _init_l_main___closed__26(void){
_start:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2939_ = lean_obj_once(&l_main___closed__25, &l_main___closed__25_once, _init_l_main___closed__25);
v___x_2940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2939_);
return v___x_2940_;
}
}
static lean_object* _init_l_main___closed__27(void){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2941_ = lean_obj_once(&l_main___closed__26, &l_main___closed__26_once, _init_l_main___closed__26);
v___x_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
lean_ctor_set(v___x_2942_, 1, v___x_2941_);
return v___x_2942_;
}
}
static lean_object* _init_l_main___closed__29(void){
_start:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2945_ = lean_unsigned_to_nat(0u);
v___x_2946_ = l_Lean_Options_empty;
v___x_2947_ = ((lean_object*)(l_main___closed__28));
v___x_2948_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2947_);
lean_ctor_set(v___x_2948_, 1, v___x_2946_);
lean_ctor_set(v___x_2948_, 2, v___x_2947_);
lean_ctor_set(v___x_2948_, 3, v___x_2945_);
lean_ctor_set(v___x_2948_, 4, v___x_2945_);
lean_ctor_set(v___x_2948_, 5, v___x_2945_);
return v___x_2948_;
}
}
static lean_object* _init_l_main___closed__30(void){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2949_ = l_Lean_NameSet_empty;
v___x_2950_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
v___x_2951_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
lean_ctor_set(v___x_2951_, 1, v___x_2950_);
lean_ctor_set(v___x_2951_, 2, v___x_2949_);
return v___x_2951_;
}
}
static lean_object* _init_l_main___closed__31(void){
_start:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; uint8_t v___x_2954_; lean_object* v___x_2955_; 
v___x_2952_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
v___x_2953_ = lean_obj_once(&l_main___closed__26, &l_main___closed__26_once, _init_l_main___closed__26);
v___x_2954_ = 1;
v___x_2955_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2955_, 0, v___x_2953_);
lean_ctor_set(v___x_2955_, 1, v___x_2953_);
lean_ctor_set(v___x_2955_, 2, v___x_2952_);
lean_ctor_set_uint8(v___x_2955_, sizeof(void*)*3, v___x_2954_);
return v___x_2955_;
}
}
static uint8_t _init_l_main___closed__35(void){
_start:
{
uint8_t v___x_2960_; uint8_t v___x_2961_; uint8_t v___x_2962_; 
v___x_2960_ = 2;
v___x_2961_ = 0;
v___x_2962_ = l_Lean_instOrdOLeanLevel_ord(v___x_2961_, v___x_2960_);
return v___x_2962_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_2963_; lean_object* v___x_2964_; 
v___x_2963_ = 0;
v___x_2964_ = lean_box_uint32(v___x_2963_);
return v___x_2964_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_2965_; lean_object* v___x_2966_; 
v___x_2965_ = 1;
v___x_2966_ = lean_box_uint32(v___x_2965_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_2967_){
_start:
{
if (lean_obj_tag(v_args_2967_) == 1)
{
lean_object* v_tail_2992_; 
v_tail_2992_ = lean_ctor_get(v_args_2967_, 1);
lean_inc(v_tail_2992_);
if (lean_obj_tag(v_tail_2992_) == 1)
{
lean_object* v_tail_2993_; 
v_tail_2993_ = lean_ctor_get(v_tail_2992_, 1);
lean_inc(v_tail_2993_);
if (lean_obj_tag(v_tail_2993_) == 1)
{
lean_object* v_head_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3752_; 
v_head_2994_ = lean_ctor_get(v_args_2967_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v_args_2967_);
if (v_isSharedCheck_3752_ == 0)
{
lean_object* v_unused_3753_; 
v_unused_3753_ = lean_ctor_get(v_args_2967_, 1);
lean_dec(v_unused_3753_);
v___x_2996_ = v_args_2967_;
v_isShared_2997_ = v_isSharedCheck_3752_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_head_2994_);
lean_dec(v_args_2967_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3752_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v_head_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3750_; 
v_head_2998_ = lean_ctor_get(v_tail_2992_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v_tail_2992_);
if (v_isSharedCheck_3750_ == 0)
{
lean_object* v_unused_3751_; 
v_unused_3751_ = lean_ctor_get(v_tail_2992_, 1);
lean_dec(v_unused_3751_);
v___x_3000_ = v_tail_2992_;
v_isShared_3001_ = v_isSharedCheck_3750_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_head_2998_);
lean_dec(v_tail_2992_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3750_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v_head_3002_; lean_object* v_tail_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3749_; 
v_head_3002_ = lean_ctor_get(v_tail_2993_, 0);
v_tail_3003_ = lean_ctor_get(v_tail_2993_, 1);
v_isSharedCheck_3749_ = !lean_is_exclusive(v_tail_2993_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3005_ = v_tail_2993_;
v_isShared_3006_ = v_isSharedCheck_3749_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_tail_3003_);
lean_inc(v_head_3002_);
lean_dec(v_tail_2993_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3749_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3007_ = lean_obj_once(&l_main___closed__1, &l_main___closed__1_once, _init_l_main___closed__1);
v___x_3008_ = lean_box(0);
v___x_3009_ = lean_obj_once(&l_main___closed__2, &l_main___closed__2_once, _init_l_main___closed__2);
v___x_3010_ = lean_obj_once(&l_main___closed__3, &l_main___closed__3_once, _init_l_main___closed__3);
v___x_3011_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_3012_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_3013_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_3014_ = lean_box(1);
v___x_3015_ = ((lean_object*)(l_main___closed__8));
v___x_3016_ = l_Lean_ModuleSetup_load(v_head_2994_);
lean_dec(v_head_2994_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v_name_3018_; lean_object* v_package_x3f_3019_; lean_object* v_importArts_3020_; lean_object* v_options_3021_; lean_object* v___f_3022_; uint8_t v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3027_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref_known(v___x_3016_, 1);
v_name_3018_ = lean_ctor_get(v_a_3017_, 0);
lean_inc(v_name_3018_);
v_package_x3f_3019_ = lean_ctor_get(v_a_3017_, 1);
lean_inc(v_package_x3f_3019_);
v_importArts_3020_ = lean_ctor_get(v_a_3017_, 3);
lean_inc(v_importArts_3020_);
v_options_3021_ = lean_ctor_get(v_a_3017_, 6);
lean_inc(v_options_3021_);
lean_dec(v_a_3017_);
v___f_3022_ = lean_alloc_closure((void*)(l_main___lam__0), 2, 1);
lean_closure_set(v___f_3022_, 0, v_package_x3f_3019_);
v___x_3023_ = 0;
v___x_3024_ = l_Lean_LeanOptions_toOptions(v_options_3021_);
v___x_3025_ = lean_box(v___x_3023_);
if (v_isShared_3006_ == 0)
{
lean_ctor_set_tag(v___x_3005_, 0);
lean_ctor_set(v___x_3005_, 1, v___x_3024_);
lean_ctor_set(v___x_3005_, 0, v___x_3025_);
v___x_3027_ = v___x_3005_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v___x_3025_);
lean_ctor_set(v_reuseFailAlloc_3740_, 1, v___x_3024_);
v___x_3027_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
lean_object* v___x_3028_; 
v___x_3028_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_tail_3003_, v___x_3027_);
lean_dec(v_tail_3003_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v_a_3029_; lean_object* v_fst_3030_; lean_object* v_snd_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3731_; 
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_a_3029_);
lean_dec_ref_known(v___x_3028_, 1);
v_fst_3030_ = lean_ctor_get(v_a_3029_, 0);
v_snd_3031_ = lean_ctor_get(v_a_3029_, 1);
v_isSharedCheck_3731_ = !lean_is_exclusive(v_a_3029_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3033_ = v_a_3029_;
v_isShared_3034_ = v_isSharedCheck_3731_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_snd_3031_);
lean_inc(v_fst_3030_);
lean_dec(v_a_3029_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3731_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3035_; uint8_t v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; uint8_t v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; uint8_t v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v_nextMacroScope_3219_; lean_object* v_ngen_3220_; lean_object* v_auxDeclNGen_3221_; lean_object* v_traceState_3222_; lean_object* v_recordedDeps_3223_; lean_object* v_messages_3224_; lean_object* v_infoState_3225_; lean_object* v_snapshotTasks_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; uint8_t v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; uint16_t v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; uint8_t v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; uint16_t v___y_3353_; uint8_t v___y_3354_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; uint8_t v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; uint16_t v___y_3400_; uint8_t v___y_3401_; uint8_t v___y_3402_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; uint8_t v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; uint16_t v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; uint8_t v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; uint8_t v___y_3427_; lean_object* v___y_3428_; uint8_t v___y_3429_; lean_object* v___x_3430_; 
v___x_3035_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_3036_ = 1;
v___x_3037_ = l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(v_snd_3031_, v___x_3035_, v___x_3036_);
v___x_3038_ = l_Lean_maxHeartbeats;
v___x_3039_ = lean_unsigned_to_nat(0u);
v___x_3040_ = l_Lean_Option_set___at___00main_spec__3(v___x_3037_, v___x_3038_, v___x_3039_);
v___x_3430_ = lean_init_search_path();
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; uint8_t v___x_3436_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; uint8_t v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3619_; lean_object* v___y_3620_; uint8_t v___y_3695_; uint8_t v___x_3722_; 
lean_dec_ref_known(v___x_3430_, 1);
v___x_3431_ = ((lean_object*)(l_main___closed__18));
lean_inc(v_name_3018_);
v___x_3432_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3432_, 0, v_name_3018_);
lean_ctor_set_uint8(v___x_3432_, sizeof(void*)*1, v___x_3036_);
lean_ctor_set_uint8(v___x_3432_, sizeof(void*)*1 + 1, v___x_3036_);
lean_ctor_set_uint8(v___x_3432_, sizeof(void*)*1 + 2, v___x_3023_);
v___x_3433_ = lean_unsigned_to_nat(1u);
v___x_3434_ = lean_mk_empty_array_with_capacity(v___x_3433_);
v___x_3435_ = lean_array_push(v___x_3434_, v___x_3432_);
v___x_3436_ = 0;
v___x_3722_ = lean_uint8_once(&l_main___closed__35, &l_main___closed__35_once, _init_l_main___closed__35);
if (v___x_3722_ == 0)
{
v___y_3695_ = v___x_3036_;
goto v___jp_3694_;
}
else
{
v___y_3695_ = v___x_3023_;
goto v___jp_3694_;
}
v___jp_3437_:
{
lean_object* v___x_3442_; lean_object* v_moduleData_3443_; lean_object* v___x_3444_; uint8_t v___x_3445_; 
v___x_3442_ = l_Lean_Environment_header(v___y_3441_);
v_moduleData_3443_ = lean_ctor_get(v___x_3442_, 7);
lean_inc_ref(v_moduleData_3443_);
lean_dec_ref(v___x_3442_);
v___x_3444_ = lean_array_get_size(v_moduleData_3443_);
v___x_3445_ = lean_nat_dec_lt(v___y_3440_, v___x_3444_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3446_; lean_object* v___x_3447_; 
lean_dec_ref(v_moduleData_3443_);
lean_dec_ref(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec_ref(v___x_3040_);
lean_del_object(v___x_3033_);
lean_dec(v_fst_3030_);
lean_dec(v_name_3018_);
lean_dec(v_head_3002_);
lean_del_object(v___x_3000_);
lean_dec(v_head_2998_);
v___x_3446_ = lean_obj_once(&l_main___closed__19, &l_main___closed__19_once, _init_l_main___closed__19);
v___x_3447_ = l_panic___at___00main_spec__5(v___x_3446_);
return v___x_3447_;
}
else
{
lean_object* v_base_3448_; lean_object* v_private_3449_; lean_object* v_header_3450_; lean_object* v_serverBaseExts_3451_; lean_object* v_checked_3452_; lean_object* v_asyncConstsMap_3453_; lean_object* v_asyncCtx_x3f_3454_; lean_object* v_importRealizationCtx_x3f_3455_; lean_object* v_localRealizationCtxMap_3456_; lean_object* v_allRealizations_3457_; uint8_t v_isExporting_3458_; uint8_t v_isRecordingDeps_3459_; lean_object* v_synthCacheRaw_x3f_3460_; lean_object* v_declChangeLog_3461_; lean_object* v_recordingConstGen_3462_; lean_object* v_constAddedGens_3463_; lean_object* v_constGen_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3547_; 
v_base_3448_ = lean_ctor_get(v___y_3441_, 0);
lean_inc_ref(v_base_3448_);
v_private_3449_ = lean_ctor_get(v_base_3448_, 0);
lean_inc(v_private_3449_);
v_header_3450_ = lean_ctor_get(v_private_3449_, 7);
lean_inc_ref(v_header_3450_);
v_serverBaseExts_3451_ = lean_ctor_get(v___y_3441_, 1);
v_checked_3452_ = lean_ctor_get(v___y_3441_, 2);
v_asyncConstsMap_3453_ = lean_ctor_get(v___y_3441_, 3);
v_asyncCtx_x3f_3454_ = lean_ctor_get(v___y_3441_, 4);
v_importRealizationCtx_x3f_3455_ = lean_ctor_get(v___y_3441_, 5);
v_localRealizationCtxMap_3456_ = lean_ctor_get(v___y_3441_, 6);
v_allRealizations_3457_ = lean_ctor_get(v___y_3441_, 7);
v_isExporting_3458_ = lean_ctor_get_uint8(v___y_3441_, sizeof(void*)*13);
v_isRecordingDeps_3459_ = lean_ctor_get_uint8(v___y_3441_, sizeof(void*)*13 + 1);
v_synthCacheRaw_x3f_3460_ = lean_ctor_get(v___y_3441_, 8);
v_declChangeLog_3461_ = lean_ctor_get(v___y_3441_, 9);
v_recordingConstGen_3462_ = lean_ctor_get(v___y_3441_, 10);
v_constAddedGens_3463_ = lean_ctor_get(v___y_3441_, 11);
v_constGen_3464_ = lean_ctor_get(v___y_3441_, 12);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___y_3441_);
if (v_isSharedCheck_3547_ == 0)
{
lean_object* v_unused_3548_; 
v_unused_3548_ = lean_ctor_get(v___y_3441_, 0);
lean_dec(v_unused_3548_);
v___x_3466_ = v___y_3441_;
v_isShared_3467_ = v_isSharedCheck_3547_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_constGen_3464_);
lean_inc(v_constAddedGens_3463_);
lean_inc(v_recordingConstGen_3462_);
lean_inc(v_declChangeLog_3461_);
lean_inc(v_synthCacheRaw_x3f_3460_);
lean_inc(v_allRealizations_3457_);
lean_inc(v_localRealizationCtxMap_3456_);
lean_inc(v_importRealizationCtx_x3f_3455_);
lean_inc(v_asyncCtx_x3f_3454_);
lean_inc(v_asyncConstsMap_3453_);
lean_inc(v_checked_3452_);
lean_inc(v_serverBaseExts_3451_);
lean_dec(v___y_3441_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3547_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v_public_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3545_; 
v_public_3468_ = lean_ctor_get(v_base_3448_, 1);
v_isSharedCheck_3545_ = !lean_is_exclusive(v_base_3448_);
if (v_isSharedCheck_3545_ == 0)
{
lean_object* v_unused_3546_; 
v_unused_3546_ = lean_ctor_get(v_base_3448_, 0);
lean_dec(v_unused_3546_);
v___x_3470_ = v_base_3448_;
v_isShared_3471_ = v_isSharedCheck_3545_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_public_3468_);
lean_dec(v_base_3448_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3545_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v_constants_3472_; uint8_t v_quotInit_3473_; lean_object* v_diagnostics_3474_; lean_object* v_const2ModIdx_3475_; lean_object* v_extensions_3476_; lean_object* v_irBaseExts_3477_; lean_object* v_extGens_3478_; lean_object* v_trackedGen_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3543_; 
v_constants_3472_ = lean_ctor_get(v_private_3449_, 0);
v_quotInit_3473_ = lean_ctor_get_uint8(v_private_3449_, sizeof(void*)*8);
v_diagnostics_3474_ = lean_ctor_get(v_private_3449_, 1);
v_const2ModIdx_3475_ = lean_ctor_get(v_private_3449_, 2);
v_extensions_3476_ = lean_ctor_get(v_private_3449_, 3);
v_irBaseExts_3477_ = lean_ctor_get(v_private_3449_, 4);
v_extGens_3478_ = lean_ctor_get(v_private_3449_, 5);
v_trackedGen_3479_ = lean_ctor_get(v_private_3449_, 6);
v_isSharedCheck_3543_ = !lean_is_exclusive(v_private_3449_);
if (v_isSharedCheck_3543_ == 0)
{
lean_object* v_unused_3544_; 
v_unused_3544_ = lean_ctor_get(v_private_3449_, 7);
lean_dec(v_unused_3544_);
v___x_3481_ = v_private_3449_;
v_isShared_3482_ = v_isSharedCheck_3543_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_trackedGen_3479_);
lean_inc(v_extGens_3478_);
lean_inc(v_irBaseExts_3477_);
lean_inc(v_extensions_3476_);
lean_inc(v_const2ModIdx_3475_);
lean_inc(v_diagnostics_3474_);
lean_inc(v_constants_3472_);
lean_dec(v_private_3449_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3543_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
uint32_t v_trustLevel_3483_; lean_object* v_mainModule_3484_; uint8_t v_isModule_3485_; lean_object* v_regions_3486_; lean_object* v_modules_3487_; lean_object* v_moduleNames_3488_; lean_object* v_moduleName2Idx_3489_; lean_object* v_importAllModules_3490_; lean_object* v_moduleData_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3541_; 
v_trustLevel_3483_ = lean_ctor_get_uint32(v_header_3450_, sizeof(void*)*8);
v_mainModule_3484_ = lean_ctor_get(v_header_3450_, 0);
v_isModule_3485_ = lean_ctor_get_uint8(v_header_3450_, sizeof(void*)*8 + 4);
v_regions_3486_ = lean_ctor_get(v_header_3450_, 2);
v_modules_3487_ = lean_ctor_get(v_header_3450_, 3);
v_moduleNames_3488_ = lean_ctor_get(v_header_3450_, 4);
v_moduleName2Idx_3489_ = lean_ctor_get(v_header_3450_, 5);
v_importAllModules_3490_ = lean_ctor_get(v_header_3450_, 6);
v_moduleData_3491_ = lean_ctor_get(v_header_3450_, 7);
v_isSharedCheck_3541_ = !lean_is_exclusive(v_header_3450_);
if (v_isSharedCheck_3541_ == 0)
{
lean_object* v_unused_3542_; 
v_unused_3542_ = lean_ctor_get(v_header_3450_, 1);
lean_dec(v_unused_3542_);
v___x_3493_ = v_header_3450_;
v_isShared_3494_ = v_isSharedCheck_3541_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_moduleData_3491_);
lean_inc(v_importAllModules_3490_);
lean_inc(v_moduleName2Idx_3489_);
lean_inc(v_moduleNames_3488_);
lean_inc(v_modules_3487_);
lean_inc(v_regions_3486_);
lean_inc(v_mainModule_3484_);
lean_dec(v_header_3450_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3541_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3495_; lean_object* v_imports_3496_; lean_object* v___x_3498_; 
v___x_3495_ = lean_array_fget(v_moduleData_3443_, v___y_3440_);
lean_dec_ref(v_moduleData_3443_);
v_imports_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc_ref(v_imports_3496_);
lean_dec(v___x_3495_);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 1, v_imports_3496_);
v___x_3498_ = v___x_3493_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 8, 5);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_mainModule_3484_);
lean_ctor_set(v_reuseFailAlloc_3540_, 1, v_imports_3496_);
lean_ctor_set(v_reuseFailAlloc_3540_, 2, v_regions_3486_);
lean_ctor_set(v_reuseFailAlloc_3540_, 3, v_modules_3487_);
lean_ctor_set(v_reuseFailAlloc_3540_, 4, v_moduleNames_3488_);
lean_ctor_set(v_reuseFailAlloc_3540_, 5, v_moduleName2Idx_3489_);
lean_ctor_set(v_reuseFailAlloc_3540_, 6, v_importAllModules_3490_);
lean_ctor_set(v_reuseFailAlloc_3540_, 7, v_moduleData_3491_);
lean_ctor_set_uint32(v_reuseFailAlloc_3540_, sizeof(void*)*8, v_trustLevel_3483_);
lean_ctor_set_uint8(v_reuseFailAlloc_3540_, sizeof(void*)*8 + 4, v_isModule_3485_);
v___x_3498_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
lean_object* v___x_3500_; 
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 7, v___x_3498_);
v___x_3500_ = v___x_3481_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_constants_3472_);
lean_ctor_set(v_reuseFailAlloc_3539_, 1, v_diagnostics_3474_);
lean_ctor_set(v_reuseFailAlloc_3539_, 2, v_const2ModIdx_3475_);
lean_ctor_set(v_reuseFailAlloc_3539_, 3, v_extensions_3476_);
lean_ctor_set(v_reuseFailAlloc_3539_, 4, v_irBaseExts_3477_);
lean_ctor_set(v_reuseFailAlloc_3539_, 5, v_extGens_3478_);
lean_ctor_set(v_reuseFailAlloc_3539_, 6, v_trackedGen_3479_);
lean_ctor_set(v_reuseFailAlloc_3539_, 7, v___x_3498_);
lean_ctor_set_uint8(v_reuseFailAlloc_3539_, sizeof(void*)*8, v_quotInit_3473_);
v___x_3500_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
lean_object* v___x_3502_; 
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 0, v___x_3500_);
v___x_3502_ = v___x_3470_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3500_);
lean_ctor_set(v_reuseFailAlloc_3538_, 1, v_public_3468_);
v___x_3502_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
lean_object* v___x_3504_; 
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 0, v___x_3502_);
v___x_3504_ = v___x_3466_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3502_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v_serverBaseExts_3451_);
lean_ctor_set(v_reuseFailAlloc_3537_, 2, v_checked_3452_);
lean_ctor_set(v_reuseFailAlloc_3537_, 3, v_asyncConstsMap_3453_);
lean_ctor_set(v_reuseFailAlloc_3537_, 4, v_asyncCtx_x3f_3454_);
lean_ctor_set(v_reuseFailAlloc_3537_, 5, v_importRealizationCtx_x3f_3455_);
lean_ctor_set(v_reuseFailAlloc_3537_, 6, v_localRealizationCtxMap_3456_);
lean_ctor_set(v_reuseFailAlloc_3537_, 7, v_allRealizations_3457_);
lean_ctor_set(v_reuseFailAlloc_3537_, 8, v_synthCacheRaw_x3f_3460_);
lean_ctor_set(v_reuseFailAlloc_3537_, 9, v_declChangeLog_3461_);
lean_ctor_set(v_reuseFailAlloc_3537_, 10, v_recordingConstGen_3462_);
lean_ctor_set(v_reuseFailAlloc_3537_, 11, v_constAddedGens_3463_);
lean_ctor_set(v_reuseFailAlloc_3537_, 12, v_constGen_3464_);
lean_ctor_set_uint8(v_reuseFailAlloc_3537_, sizeof(void*)*13, v_isExporting_3458_);
lean_ctor_set_uint8(v_reuseFailAlloc_3537_, sizeof(void*)*13 + 1, v_isRecordingDeps_3459_);
v___x_3504_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; uint16_t v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v_env_3531_; uint8_t v___x_3532_; uint16_t v___x_3533_; uint16_t v___x_3534_; uint16_t v___x_3535_; uint8_t v___x_3536_; 
v___x_3505_ = l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
v___x_3506_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3015_, v___x_3505_, v___x_3504_, v___y_3440_, v___x_3436_);
lean_dec(v___y_3440_);
v___x_3507_ = l_Lean_instInhabitedFileMap_default;
v___x_3508_ = lean_unsigned_to_nat(1000u);
v___x_3509_ = l_Lean_Core_getMaxHeartbeats(v___x_3040_);
v___x_3510_ = l_Lean_firstFrontendMacroScope;
v___x_3511_ = lean_box(0);
v___x_3512_ = lean_box(0);
v___x_3513_ = l_Lean_OptionFlags_ofOptions(v___x_3040_);
v___x_3514_ = lean_obj_once(&l_main___closed__20, &l_main___closed__20_once, _init_l_main___closed__20);
v___x_3515_ = ((lean_object*)(l_main___closed__23));
lean_inc_n(v___y_3439_, 3);
v___x_3516_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3516_, 0, v___y_3439_);
lean_ctor_set(v___x_3516_, 1, v___x_3433_);
lean_ctor_set(v___x_3516_, 2, v___x_3008_);
v___x_3517_ = lean_obj_once(&l_main___closed__24, &l_main___closed__24_once, _init_l_main___closed__24);
v___x_3518_ = lean_obj_once(&l_main___closed__27, &l_main___closed__27_once, _init_l_main___closed__27);
v___x_3519_ = ((lean_object*)(l_main___closed__28));
v___x_3520_ = l_Lean_Options_empty;
v___x_3521_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_3522_ = lean_obj_once(&l_main___closed__30, &l_main___closed__30_once, _init_l_main___closed__30);
v___x_3523_ = lean_obj_once(&l_main___closed__31, &l_main___closed__31_once, _init_l_main___closed__31);
lean_inc_ref(v___x_3516_);
v___x_3524_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3504_);
lean_ctor_set(v___x_3524_, 1, v___x_3514_);
lean_ctor_set(v___x_3524_, 2, v___x_3515_);
lean_ctor_set(v___x_3524_, 3, v___x_3516_);
lean_ctor_set(v___x_3524_, 4, v___x_3517_);
lean_ctor_set(v___x_3524_, 5, v___x_3518_);
lean_ctor_set(v___x_3524_, 6, v___x_3521_);
lean_ctor_set(v___x_3524_, 7, v___x_3522_);
lean_ctor_set(v___x_3524_, 8, v___x_3523_);
lean_ctor_set(v___x_3524_, 9, v___x_3519_);
v___x_3525_ = lean_st_mk_ref(v___x_3524_);
v___x_3526_ = l_Lean_inheritedTraceOptions;
v___x_3527_ = lean_st_ref_get(v___x_3526_);
lean_inc_ref(v___x_3040_);
lean_inc(v_head_2998_);
v___x_3528_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3528_, 0, v_head_2998_);
lean_ctor_set(v___x_3528_, 1, v___x_3507_);
lean_ctor_set(v___x_3528_, 2, v___x_3040_);
lean_ctor_set(v___x_3528_, 3, v___x_3508_);
lean_ctor_set(v___x_3528_, 4, v___y_3439_);
lean_ctor_set(v___x_3528_, 5, v___x_3008_);
lean_ctor_set(v___x_3528_, 6, v___x_3039_);
lean_ctor_set(v___x_3528_, 7, v___x_3509_);
lean_ctor_set(v___x_3528_, 8, v___y_3439_);
lean_ctor_set(v___x_3528_, 9, v___x_3510_);
lean_ctor_set(v___x_3528_, 10, v___x_3511_);
lean_ctor_set(v___x_3528_, 11, v___x_3527_);
v___x_3529_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3529_, 0, v___x_3528_);
lean_ctor_set(v___x_3529_, 1, v___x_3039_);
lean_ctor_set(v___x_3529_, 2, v___x_3512_);
lean_ctor_set_uint16(v___x_3529_, sizeof(void*)*3, v___x_3513_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 2, v___x_3023_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 3, v___x_3023_);
v___x_3530_ = lean_st_ref_get(v___x_3525_);
v_env_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc_ref(v_env_3531_);
lean_dec(v___x_3530_);
v___x_3532_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3531_);
lean_dec_ref(v_env_3531_);
v___x_3533_ = 512;
v___x_3534_ = lean_uint16_land(v___x_3513_, v___x_3533_);
v___x_3535_ = 0;
v___x_3536_ = lean_uint16_dec_eq(v___x_3534_, v___x_3535_);
if (v___x_3536_ == 0)
{
if (v___x_3445_ == 0)
{
v___y_3404_ = v___x_3518_;
v___y_3405_ = v___x_3008_;
v___y_3406_ = v___x_3507_;
v___y_3407_ = v___x_3517_;
v___y_3408_ = v___x_3515_;
v___y_3409_ = v___x_3516_;
v___y_3410_ = v___x_3445_;
v___y_3411_ = v___x_3506_;
v___y_3412_ = v___x_3505_;
v___y_3413_ = v___x_3511_;
v___y_3414_ = v___x_3520_;
v___y_3415_ = v___x_3514_;
v___y_3416_ = v___x_3512_;
v___y_3417_ = v___y_3438_;
v___y_3418_ = v___x_3510_;
v___y_3419_ = v___x_3513_;
v___y_3420_ = v___x_3529_;
v___y_3421_ = v___x_3525_;
v___y_3422_ = v___x_3523_;
v___y_3423_ = v___x_3519_;
v___y_3424_ = v___x_3445_;
v___y_3425_ = v___x_3522_;
v___y_3426_ = v___x_3521_;
v___y_3427_ = v___x_3532_;
v___y_3428_ = v___y_3439_;
v___y_3429_ = v___x_3445_;
goto v___jp_3403_;
}
else
{
v___y_3376_ = v___x_3518_;
v___y_3377_ = v___x_3008_;
v___y_3378_ = v___x_3511_;
v___y_3379_ = v___x_3507_;
v___y_3380_ = v___x_3520_;
v___y_3381_ = v___x_3512_;
v___y_3382_ = v___x_3510_;
v___y_3383_ = v___y_3438_;
v___y_3384_ = v___x_3445_;
v___y_3385_ = v___x_3529_;
v___y_3386_ = v___x_3518_;
v___y_3387_ = v___x_3525_;
v___y_3388_ = v___x_3523_;
v___y_3389_ = v___x_3517_;
v___y_3390_ = v___x_3515_;
v___y_3391_ = v___x_3516_;
v___y_3392_ = v___x_3519_;
v___y_3393_ = v___x_3506_;
v___y_3394_ = v___x_3522_;
v___y_3395_ = v___x_3521_;
v___y_3396_ = v___x_3505_;
v___y_3397_ = v___x_3520_;
v___y_3398_ = v___x_3514_;
v___y_3399_ = v___y_3439_;
v___y_3400_ = v___x_3513_;
v___y_3401_ = v___x_3445_;
v___y_3402_ = v___x_3532_;
goto v___jp_3375_;
}
}
else
{
v___y_3404_ = v___x_3518_;
v___y_3405_ = v___x_3008_;
v___y_3406_ = v___x_3507_;
v___y_3407_ = v___x_3517_;
v___y_3408_ = v___x_3515_;
v___y_3409_ = v___x_3516_;
v___y_3410_ = v___x_3445_;
v___y_3411_ = v___x_3506_;
v___y_3412_ = v___x_3505_;
v___y_3413_ = v___x_3511_;
v___y_3414_ = v___x_3520_;
v___y_3415_ = v___x_3514_;
v___y_3416_ = v___x_3512_;
v___y_3417_ = v___y_3438_;
v___y_3418_ = v___x_3510_;
v___y_3419_ = v___x_3513_;
v___y_3420_ = v___x_3529_;
v___y_3421_ = v___x_3525_;
v___y_3422_ = v___x_3523_;
v___y_3423_ = v___x_3519_;
v___y_3424_ = v___x_3445_;
v___y_3425_ = v___x_3522_;
v___y_3426_ = v___x_3521_;
v___y_3427_ = v___x_3532_;
v___y_3428_ = v___y_3439_;
v___y_3429_ = v___x_3023_;
goto v___jp_3403_;
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
v___jp_3549_:
{
lean_object* v___x_3559_; 
if (v_isShared_2997_ == 0)
{
lean_ctor_set_tag(v___x_2996_, 0);
lean_ctor_set(v___x_2996_, 1, v___y_3557_);
lean_ctor_set(v___x_2996_, 0, v___y_3551_);
v___x_3559_ = v___x_2996_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___y_3551_);
lean_ctor_set(v_reuseFailAlloc_3565_, 1, v___y_3557_);
v___x_3559_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
lean_object* v___f_3560_; lean_object* v___x_3561_; 
v___f_3560_ = lean_alloc_closure((void*)(l_main___lam__3___boxed), 2, 1);
lean_closure_set(v___f_3560_, 0, v___x_3559_);
v___x_3561_ = lean_box(0);
if (v___y_3553_ == 0)
{
lean_object* v___x_3562_; 
lean_inc(v___y_3555_);
lean_inc_ref(v___y_3552_);
v___x_3562_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v___y_3552_, v___y_3554_, v___f_3560_, v___x_3561_, v___y_3555_, v___x_3036_);
v___y_3438_ = v___y_3550_;
v___y_3439_ = v___y_3555_;
v___y_3440_ = v___y_3556_;
v___y_3441_ = v___x_3562_;
goto v___jp_3437_;
}
else
{
lean_object* v___x_3563_; lean_object* v___x_3564_; 
lean_inc_ref_n(v___y_3552_, 2);
v___x_3563_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite___redArg(v___y_3552_, v___y_3554_);
lean_dec_ref(v___y_3554_);
lean_inc(v___y_3555_);
v___x_3564_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v___y_3552_, v___x_3563_, v___f_3560_, v___x_3561_, v___y_3555_, v___x_3036_);
v___y_3438_ = v___y_3550_;
v___y_3439_ = v___y_3555_;
v___y_3440_ = v___y_3556_;
v___y_3441_ = v___x_3564_;
goto v___jp_3437_;
}
}
}
v___jp_3566_:
{
lean_object* v___x_3571_; lean_object* v_toEnvExtension_3572_; lean_object* v_asyncMode_3573_; uint8_t v_logWrites_3574_; lean_object* v___x_3575_; lean_object* v_importedEntries_3576_; lean_object* v_state_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; uint8_t v___x_3580_; 
v___x_3571_ = l_Lean_IR_declMapExt;
v_toEnvExtension_3572_ = lean_ctor_get(v___x_3571_, 0);
v_asyncMode_3573_ = lean_ctor_get(v_toEnvExtension_3572_, 2);
v_logWrites_3574_ = lean_ctor_get_uint8(v_toEnvExtension_3572_, sizeof(void*)*6);
lean_inc(v___y_3568_);
lean_inc_ref(v___y_3570_);
v___x_3575_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3012_, v_toEnvExtension_3572_, v___y_3570_, v_asyncMode_3573_, v___y_3568_, v___x_3023_);
v_importedEntries_3576_ = lean_ctor_get(v___x_3575_, 0);
lean_inc_ref(v_importedEntries_3576_);
v_state_3577_ = lean_ctor_get(v___x_3575_, 1);
lean_inc(v_state_3577_);
lean_dec(v___x_3575_);
v___x_3578_ = lean_array_get_borrowed(v___x_3013_, v_importedEntries_3576_, v___y_3569_);
v___x_3579_ = lean_array_get_size(v___x_3578_);
v___x_3580_ = lean_nat_dec_lt(v___x_3039_, v___x_3579_);
if (v___x_3580_ == 0)
{
v___y_3550_ = v___y_3567_;
v___y_3551_ = v_importedEntries_3576_;
v___y_3552_ = v_toEnvExtension_3572_;
v___y_3553_ = v_logWrites_3574_;
v___y_3554_ = v___y_3570_;
v___y_3555_ = v___y_3568_;
v___y_3556_ = v___y_3569_;
v___y_3557_ = v_state_3577_;
goto v___jp_3549_;
}
else
{
uint8_t v___x_3581_; 
v___x_3581_ = lean_nat_dec_le(v___x_3579_, v___x_3579_);
if (v___x_3581_ == 0)
{
if (v___x_3580_ == 0)
{
v___y_3550_ = v___y_3567_;
v___y_3551_ = v_importedEntries_3576_;
v___y_3552_ = v_toEnvExtension_3572_;
v___y_3553_ = v_logWrites_3574_;
v___y_3554_ = v___y_3570_;
v___y_3555_ = v___y_3568_;
v___y_3556_ = v___y_3569_;
v___y_3557_ = v_state_3577_;
goto v___jp_3549_;
}
else
{
size_t v___x_3582_; size_t v___x_3583_; lean_object* v___x_3584_; 
v___x_3582_ = ((size_t)0ULL);
v___x_3583_ = lean_usize_of_nat(v___x_3579_);
lean_inc_ref(v___y_3570_);
v___x_3584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3570_, v___x_3578_, v___x_3582_, v___x_3583_, v_state_3577_);
v___y_3550_ = v___y_3567_;
v___y_3551_ = v_importedEntries_3576_;
v___y_3552_ = v_toEnvExtension_3572_;
v___y_3553_ = v_logWrites_3574_;
v___y_3554_ = v___y_3570_;
v___y_3555_ = v___y_3568_;
v___y_3556_ = v___y_3569_;
v___y_3557_ = v___x_3584_;
goto v___jp_3549_;
}
}
else
{
size_t v___x_3585_; size_t v___x_3586_; lean_object* v___x_3587_; 
v___x_3585_ = ((size_t)0ULL);
v___x_3586_ = lean_usize_of_nat(v___x_3579_);
lean_inc_ref(v___y_3570_);
v___x_3587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3570_, v___x_3578_, v___x_3585_, v___x_3586_, v_state_3577_);
v___y_3550_ = v___y_3567_;
v___y_3551_ = v_importedEntries_3576_;
v___y_3552_ = v_toEnvExtension_3572_;
v___y_3553_ = v_logWrites_3574_;
v___y_3554_ = v___y_3570_;
v___y_3555_ = v___y_3568_;
v___y_3556_ = v___y_3569_;
v___y_3557_ = v___x_3587_;
goto v___jp_3549_;
}
}
}
v___jp_3588_:
{
uint8_t v___x_3595_; 
v___x_3595_ = lean_nat_dec_lt(v___x_3039_, v___y_3590_);
if (v___x_3595_ == 0)
{
lean_dec_ref(v___y_3591_);
lean_dec(v___y_3590_);
v___y_3567_ = v___y_3589_;
v___y_3568_ = v___y_3592_;
v___y_3569_ = v___y_3593_;
v___y_3570_ = v___y_3594_;
goto v___jp_3566_;
}
else
{
uint8_t v___x_3596_; 
v___x_3596_ = lean_nat_dec_le(v___y_3590_, v___y_3590_);
if (v___x_3596_ == 0)
{
if (v___x_3595_ == 0)
{
lean_dec_ref(v___y_3591_);
lean_dec(v___y_3590_);
v___y_3567_ = v___y_3589_;
v___y_3568_ = v___y_3592_;
v___y_3569_ = v___y_3593_;
v___y_3570_ = v___y_3594_;
goto v___jp_3566_;
}
else
{
size_t v___x_3597_; size_t v___x_3598_; lean_object* v___x_3599_; 
v___x_3597_ = ((size_t)0ULL);
v___x_3598_ = lean_usize_of_nat(v___y_3590_);
lean_dec(v___y_3590_);
v___x_3599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3591_, v___x_3597_, v___x_3598_, v___y_3594_);
lean_dec_ref(v___y_3591_);
v___y_3567_ = v___y_3589_;
v___y_3568_ = v___y_3592_;
v___y_3569_ = v___y_3593_;
v___y_3570_ = v___x_3599_;
goto v___jp_3566_;
}
}
else
{
size_t v___x_3600_; size_t v___x_3601_; lean_object* v___x_3602_; 
v___x_3600_ = ((size_t)0ULL);
v___x_3601_ = lean_usize_of_nat(v___y_3590_);
lean_dec(v___y_3590_);
v___x_3602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3591_, v___x_3600_, v___x_3601_, v___y_3594_);
lean_dec_ref(v___y_3591_);
v___y_3567_ = v___y_3589_;
v___y_3568_ = v___y_3592_;
v___y_3569_ = v___y_3593_;
v___y_3570_ = v___x_3602_;
goto v___jp_3566_;
}
}
}
v___jp_3603_:
{
lean_object* v___x_3609_; uint8_t v___x_3610_; 
v___x_3609_ = lean_array_get_size(v___y_3608_);
v___x_3610_ = lean_nat_dec_lt(v___x_3039_, v___x_3609_);
if (v___x_3610_ == 0)
{
v___y_3589_ = v___y_3604_;
v___y_3590_ = v___x_3609_;
v___y_3591_ = v___y_3608_;
v___y_3592_ = v___y_3606_;
v___y_3593_ = v___y_3607_;
v___y_3594_ = v___y_3605_;
goto v___jp_3588_;
}
else
{
uint8_t v___x_3611_; 
v___x_3611_ = lean_nat_dec_le(v___x_3609_, v___x_3609_);
if (v___x_3611_ == 0)
{
if (v___x_3610_ == 0)
{
v___y_3589_ = v___y_3604_;
v___y_3590_ = v___x_3609_;
v___y_3591_ = v___y_3608_;
v___y_3592_ = v___y_3606_;
v___y_3593_ = v___y_3607_;
v___y_3594_ = v___y_3605_;
goto v___jp_3588_;
}
else
{
size_t v___x_3612_; size_t v___x_3613_; lean_object* v___x_3614_; 
v___x_3612_ = ((size_t)0ULL);
v___x_3613_ = lean_usize_of_nat(v___x_3609_);
v___x_3614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3608_, v___x_3612_, v___x_3613_, v___y_3605_);
v___y_3589_ = v___y_3604_;
v___y_3590_ = v___x_3609_;
v___y_3591_ = v___y_3608_;
v___y_3592_ = v___y_3606_;
v___y_3593_ = v___y_3607_;
v___y_3594_ = v___x_3614_;
goto v___jp_3588_;
}
}
else
{
size_t v___x_3615_; size_t v___x_3616_; lean_object* v___x_3617_; 
v___x_3615_ = ((size_t)0ULL);
v___x_3616_ = lean_usize_of_nat(v___x_3609_);
v___x_3617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3608_, v___x_3615_, v___x_3616_, v___y_3605_);
v___y_3589_ = v___y_3604_;
v___y_3590_ = v___x_3609_;
v___y_3591_ = v___y_3608_;
v___y_3592_ = v___y_3606_;
v___y_3593_ = v___y_3607_;
v___y_3594_ = v___x_3617_;
goto v___jp_3588_;
}
}
}
v___jp_3618_:
{
lean_object* v___x_3621_; lean_object* v_ext_3622_; lean_object* v___x_3623_; 
v___x_3621_ = l_Lean_Compiler_CSimp_ext;
v_ext_3622_ = lean_ctor_get(v___x_3621_, 1);
lean_inc_ref(v_ext_3622_);
lean_inc(v___y_3619_);
v___x_3623_ = l_main___elam__0___redArg(v___y_3619_, v___x_3023_, v___x_3007_, v_ext_3622_, v___y_3620_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v_a_3624_; lean_object* v___x_3625_; lean_object* v_ext_3626_; lean_object* v___x_3627_; 
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
lean_inc(v_a_3624_);
lean_dec_ref_known(v___x_3623_, 1);
v___x_3625_ = l_Lean_Meta_instanceExtension;
v_ext_3626_ = lean_ctor_get(v___x_3625_, 1);
lean_inc_ref(v_ext_3626_);
lean_inc(v___y_3619_);
v___x_3627_ = l_main___elam__0___redArg(v___y_3619_, v___x_3023_, v___x_3007_, v_ext_3626_, v_a_3624_);
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_object* v_a_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; 
v_a_3628_ = lean_ctor_get(v___x_3627_, 0);
lean_inc(v_a_3628_);
lean_dec_ref_known(v___x_3627_, 1);
v___x_3629_ = l_Lean_classExtension;
lean_inc(v___y_3619_);
v___x_3630_ = l_main___elam__0___redArg(v___y_3619_, v___x_3023_, v___x_3009_, v___x_3629_, v_a_3628_);
if (lean_obj_tag(v___x_3630_) == 0)
{
lean_object* v_a_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v_a_3631_ = lean_ctor_get(v___x_3630_, 0);
lean_inc(v_a_3631_);
lean_dec_ref_known(v___x_3630_, 1);
v___x_3632_ = l_Lean_Meta_Match_Extension_extension;
lean_inc(v___y_3619_);
v___x_3633_ = l_main___elam__0___redArg(v___y_3619_, v___x_3023_, v___x_3010_, v___x_3632_, v_a_3631_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_a_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3661_; 
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3636_ = v___x_3633_;
v_isShared_3637_ = v_isSharedCheck_3661_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_a_3634_);
lean_dec(v___x_3633_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3661_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3638_; 
v___x_3638_ = l_Lean_Environment_getModuleIdx_x3f(v_a_3634_, v_name_3018_);
if (lean_obj_tag(v___x_3638_) == 1)
{
lean_object* v_val_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; uint8_t v___x_3644_; 
lean_del_object(v___x_3636_);
v_val_3639_ = lean_ctor_get(v___x_3638_, 0);
lean_inc(v_val_3639_);
lean_dec_ref_known(v___x_3638_, 1);
v___x_3640_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_3641_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3011_, v___x_3640_, v_a_3634_, v_val_3639_, v___x_3436_);
v___x_3642_ = lean_array_get_size(v___x_3641_);
v___x_3643_ = ((lean_object*)(l_main___closed__32));
v___x_3644_ = lean_nat_dec_lt(v___x_3039_, v___x_3642_);
if (v___x_3644_ == 0)
{
lean_dec_ref(v___x_3641_);
lean_inc(v___y_3619_);
v___y_3604_ = v___y_3619_;
v___y_3605_ = v_a_3634_;
v___y_3606_ = v___y_3619_;
v___y_3607_ = v_val_3639_;
v___y_3608_ = v___x_3643_;
goto v___jp_3603_;
}
else
{
uint8_t v___x_3645_; 
v___x_3645_ = lean_nat_dec_le(v___x_3642_, v___x_3642_);
if (v___x_3645_ == 0)
{
if (v___x_3644_ == 0)
{
lean_dec_ref(v___x_3641_);
lean_inc(v___y_3619_);
v___y_3604_ = v___y_3619_;
v___y_3605_ = v_a_3634_;
v___y_3606_ = v___y_3619_;
v___y_3607_ = v_val_3639_;
v___y_3608_ = v___x_3643_;
goto v___jp_3603_;
}
else
{
size_t v___x_3646_; size_t v___x_3647_; lean_object* v___x_3648_; 
v___x_3646_ = ((size_t)0ULL);
v___x_3647_ = lean_usize_of_nat(v___x_3642_);
lean_inc(v_a_3634_);
v___x_3648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_3634_, v___x_3641_, v___x_3646_, v___x_3647_, v___x_3643_);
lean_dec_ref(v___x_3641_);
lean_inc(v___y_3619_);
v___y_3604_ = v___y_3619_;
v___y_3605_ = v_a_3634_;
v___y_3606_ = v___y_3619_;
v___y_3607_ = v_val_3639_;
v___y_3608_ = v___x_3648_;
goto v___jp_3603_;
}
}
else
{
size_t v___x_3649_; size_t v___x_3650_; lean_object* v___x_3651_; 
v___x_3649_ = ((size_t)0ULL);
v___x_3650_ = lean_usize_of_nat(v___x_3642_);
lean_inc(v_a_3634_);
v___x_3651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_3634_, v___x_3641_, v___x_3649_, v___x_3650_, v___x_3643_);
lean_dec_ref(v___x_3641_);
lean_inc(v___y_3619_);
v___y_3604_ = v___y_3619_;
v___y_3605_ = v_a_3634_;
v___y_3606_ = v___y_3619_;
v___y_3607_ = v_val_3639_;
v___y_3608_ = v___x_3651_;
goto v___jp_3603_;
}
}
}
else
{
lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3659_; 
lean_dec(v___x_3638_);
lean_dec(v_a_3634_);
lean_dec(v___y_3619_);
lean_dec_ref(v___x_3040_);
lean_del_object(v___x_3033_);
lean_dec(v_fst_3030_);
lean_dec(v_head_3002_);
lean_del_object(v___x_3000_);
lean_dec(v_head_2998_);
lean_del_object(v___x_2996_);
v___x_3652_ = ((lean_object*)(l_main___closed__33));
v___x_3653_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3018_, v___x_3036_);
v___x_3654_ = lean_string_append(v___x_3652_, v___x_3653_);
lean_dec_ref(v___x_3653_);
v___x_3655_ = ((lean_object*)(l_main___closed__34));
v___x_3656_ = lean_string_append(v___x_3654_, v___x_3655_);
v___x_3657_ = lean_mk_io_user_error(v___x_3656_);
if (v_isShared_3637_ == 0)
{
lean_ctor_set_tag(v___x_3636_, 1);
lean_ctor_set(v___x_3636_, 0, v___x_3657_);
v___x_3659_ = v___x_3636_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3657_);
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
else
{
lean_object* v_a_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3669_; 
lean_dec(v___y_3619_);
lean_dec_ref(v___x_3040_);
lean_del_object(v___x_3033_);
lean_dec(v_fst_3030_);
lean_dec(v_name_3018_);
lean_dec(v_head_3002_);
lean_del_object(v___x_3000_);
lean_dec(v_head_2998_);
lean_del_object(v___x_2996_);
v_a_3662_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3664_ = v___x_3633_;
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_a_3662_);
lean_dec(v___x_3633_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3667_; 
if (v_isShared_3665_ == 0)
{
v___x_3667_ = v___x_3664_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_a_3662_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
return v___x_3667_;
}
}
}
}
else
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3677_; 
lean_dec(v___y_3619_);
lean_dec_ref(v___x_3040_);
lean_del_object(v___x_3033_);
lean_dec(v_fst_3030_);
lean_dec(v_name_3018_);
lean_dec(v_head_3002_);
lean_del_object(v___x_3000_);
lean_dec(v_head_2998_);
lean_del_object(v___x_2996_);
v_a_3670_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3672_ = v___x_3630_;
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3630_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3675_; 
if (v_isShared_3673_ == 0)
{
v___x_3675_ = v___x_3672_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_a_3670_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
}
else
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3685_; 
lean_dec(v___y_3619_);
lean_dec_ref(v___x_3040_);
lean_del_object(v___x_3033_);
lean_dec(v_fst_3030_);
lean_dec(v_name_3018_);
lean_dec(v_head_3002_);
lean_del_object(v___x_3000_);
lean_dec(v_head_2998_);
lean_del_object(v___x_2996_);
v_a_3678_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3680_ = v___x_3627_;
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3627_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3683_; 
if (v_isShared_3681_ == 0)
{
v___x_3683_ = v___x_3680_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
else
{
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3693_; 
lean_dec(v___y_3619_);
lean_dec_ref(v___x_3040_);
lean_del_object(v___x_3033_);
lean_dec(v_fst_3030_);
lean_dec(v_name_3018_);
lean_dec(v_head_3002_);
lean_del_object(v___x_3000_);
lean_dec(v_head_2998_);
lean_del_object(v___x_2996_);
v_a_3686_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3688_ = v___x_3623_;
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3623_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3691_; 
if (v_isShared_3689_ == 0)
{
v___x_3691_ = v___x_3688_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
v___jp_3694_:
{
lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___f_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; 
v___x_3696_ = l_Lean_instInhabitedImportState_default;
v___x_3697_ = lean_box(v___x_3436_);
v___x_3698_ = lean_box(v___y_3695_);
v___x_3699_ = lean_box(v___x_3036_);
v___x_3700_ = lean_box(v___x_3023_);
lean_inc_ref(v___x_3040_);
lean_inc(v_name_3018_);
v___f_3701_ = lean_alloc_closure((void*)(l_main___lam__1___boxed), 10, 9);
lean_closure_set(v___f_3701_, 0, v___x_3696_);
lean_closure_set(v___f_3701_, 1, v___x_3435_);
lean_closure_set(v___f_3701_, 2, v___x_3697_);
lean_closure_set(v___f_3701_, 3, v_importArts_3020_);
lean_closure_set(v___f_3701_, 4, v___x_3698_);
lean_closure_set(v___f_3701_, 5, v___x_3699_);
lean_closure_set(v___f_3701_, 6, v_name_3018_);
lean_closure_set(v___f_3701_, 7, v___x_3040_);
lean_closure_set(v___f_3701_, 8, v___x_3700_);
v___x_3702_ = lean_alloc_closure((void*)(l_Lean_withImporting___boxed), 3, 2);
lean_closure_set(v___x_3702_, 0, lean_box(0));
lean_closure_set(v___x_3702_, 1, v___f_3701_);
v___x_3703_ = lean_box(0);
v___x_3704_ = l_Lean_profileitIOUnsafe___redArg(v___x_3431_, v___x_3040_, v___x_3702_, v___x_3703_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v_a_3705_; lean_object* v___x_3706_; lean_object* v_toEnvExtension_3707_; lean_object* v_asyncMode_3708_; uint8_t v_logWrites_3709_; lean_object* v___x_3710_; 
v_a_3705_ = lean_ctor_get(v___x_3704_, 0);
lean_inc(v_a_3705_);
lean_dec_ref_known(v___x_3704_, 1);
v___x_3706_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_3707_ = lean_ctor_get(v___x_3706_, 0);
v_asyncMode_3708_ = lean_ctor_get(v_toEnvExtension_3707_, 2);
v_logWrites_3709_ = lean_ctor_get_uint8(v_toEnvExtension_3707_, sizeof(void*)*6);
lean_inc(v_name_3018_);
v___x_3710_ = l_Lean_Environment_setMainModule(v_a_3705_, v_name_3018_);
if (v_logWrites_3709_ == 0)
{
lean_object* v___x_3711_; 
lean_inc_ref(v_toEnvExtension_3707_);
v___x_3711_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_3707_, v___x_3710_, v___f_3022_, v_asyncMode_3708_, v___x_3703_, v___x_3036_);
v___y_3619_ = v___x_3703_;
v___y_3620_ = v___x_3711_;
goto v___jp_3618_;
}
else
{
lean_object* v___x_3712_; lean_object* v___x_3713_; 
lean_inc_ref_n(v_toEnvExtension_3707_, 2);
v___x_3712_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite___redArg(v_toEnvExtension_3707_, v___x_3710_);
lean_dec_ref(v___x_3710_);
v___x_3713_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_3707_, v___x_3712_, v___f_3022_, v_asyncMode_3708_, v___x_3703_, v___x_3036_);
v___y_3619_ = v___x_3703_;
v___y_3620_ = v___x_3713_;
goto v___jp_3618_;
}
}
else
{
lean_object* v_a_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3721_; 
lean_dec_ref(v___x_3040_);
lean_del_object(v___x_3033_);
lean_dec(v_fst_3030_);
lean_dec_ref(v___f_3022_);
lean_dec(v_name_3018_);
lean_dec(v_head_3002_);
lean_del_object(v___x_3000_);
lean_dec(v_head_2998_);
lean_del_object(v___x_2996_);
v_a_3714_ = lean_ctor_get(v___x_3704_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v___x_3704_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3716_ = v___x_3704_;
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_a_3714_);
lean_dec(v___x_3704_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v___x_3719_; 
if (v_isShared_3717_ == 0)
{
v___x_3719_ = v___x_3716_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v_a_3714_);
v___x_3719_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
return v___x_3719_;
}
}
}
}
}
else
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3730_; 
lean_dec_ref(v___x_3040_);
lean_del_object(v___x_3033_);
lean_dec(v_fst_3030_);
lean_dec_ref(v___f_3022_);
lean_dec(v_importArts_3020_);
lean_dec(v_name_3018_);
lean_dec(v_head_3002_);
lean_del_object(v___x_3000_);
lean_dec(v_head_2998_);
lean_del_object(v___x_2996_);
v_a_3723_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3725_ = v___x_3430_;
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3430_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3728_; 
if (v_isShared_3726_ == 0)
{
v___x_3728_ = v___x_3725_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_a_3723_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
v___jp_3041_:
{
lean_object* v___x_3063_; lean_object* v_messages_3064_; lean_object* v_env_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3190_; 
v___x_3063_ = lean_st_ref_get(v___y_3056_);
lean_dec(v___y_3056_);
v_messages_3064_ = lean_ctor_get(v___x_3063_, 7);
v_env_3065_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3190_ == 0)
{
lean_object* v_unused_3191_; lean_object* v_unused_3192_; lean_object* v_unused_3193_; lean_object* v_unused_3194_; lean_object* v_unused_3195_; lean_object* v_unused_3196_; lean_object* v_unused_3197_; lean_object* v_unused_3198_; 
v_unused_3191_ = lean_ctor_get(v___x_3063_, 9);
lean_dec(v_unused_3191_);
v_unused_3192_ = lean_ctor_get(v___x_3063_, 8);
lean_dec(v_unused_3192_);
v_unused_3193_ = lean_ctor_get(v___x_3063_, 6);
lean_dec(v_unused_3193_);
v_unused_3194_ = lean_ctor_get(v___x_3063_, 5);
lean_dec(v_unused_3194_);
v_unused_3195_ = lean_ctor_get(v___x_3063_, 4);
lean_dec(v_unused_3195_);
v_unused_3196_ = lean_ctor_get(v___x_3063_, 3);
lean_dec(v_unused_3196_);
v_unused_3197_ = lean_ctor_get(v___x_3063_, 2);
lean_dec(v_unused_3197_);
v_unused_3198_ = lean_ctor_get(v___x_3063_, 1);
lean_dec(v_unused_3198_);
v___x_3067_ = v___x_3063_;
v_isShared_3068_ = v_isSharedCheck_3190_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_messages_3064_);
lean_inc(v_env_3065_);
lean_dec(v___x_3063_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3190_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v_unreported_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v_unreported_3069_ = lean_ctor_get(v_messages_3064_, 1);
v___x_3070_ = lean_box(0);
v___x_3071_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_unreported_3069_, v___x_3070_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3180_; 
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3180_ == 0)
{
lean_object* v_unused_3181_; 
v_unused_3181_ = lean_ctor_get(v___x_3071_, 0);
lean_dec(v_unused_3181_);
v___x_3073_ = v___x_3071_;
v_isShared_3074_ = v_isSharedCheck_3180_;
goto v_resetjp_3072_;
}
else
{
lean_dec(v___x_3071_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3180_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
uint8_t v___x_3075_; 
v___x_3075_ = l_Lean_MessageLog_hasErrors(v_messages_3064_);
lean_dec_ref(v_messages_3064_);
if (v___x_3075_ == 0)
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
lean_del_object(v___x_3073_);
v___x_3076_ = ((lean_object*)(l_main___closed__9));
lean_inc(v_head_2998_);
v___x_3077_ = l_System_FilePath_addExtension(v_head_2998_, v___x_3076_);
lean_inc_ref(v_env_3065_);
v___x_3078_ = l___private_LeanIR_0__mkIRSigData(v_env_3065_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_object* v_a_3079_; lean_object* v___x_3080_; 
v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
lean_inc(v_a_3079_);
lean_dec_ref_known(v___x_3078_, 1);
lean_inc_ref(v_env_3065_);
v___x_3080_ = l___private_LeanIR_0__mkIRData(v_env_3065_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3086_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_a_3081_);
lean_dec_ref_known(v___x_3080_, 1);
v___x_3082_ = l_Lean_Environment_mainModule(v_env_3065_);
v___x_3083_ = ((lean_object*)(l_main___closed__11));
v___x_3084_ = l_Lean_Name_append(v___x_3082_, v___x_3083_);
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 1, v_a_3079_);
lean_ctor_set(v___x_3033_, 0, v___x_3077_);
v___x_3086_ = v___x_3033_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v___x_3077_);
lean_ctor_set(v_reuseFailAlloc_3159_, 1, v_a_3079_);
v___x_3086_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
lean_object* v___x_3088_; 
lean_inc(v_head_2998_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set_tag(v___x_3000_, 0);
lean_ctor_set(v___x_3000_, 1, v_a_3081_);
v___x_3088_ = v___x_3000_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_head_2998_);
lean_ctor_set(v_reuseFailAlloc_3158_, 1, v_a_3081_);
v___x_3088_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3089_ = lean_unsigned_to_nat(2u);
v___x_3090_ = lean_mk_empty_array_with_capacity(v___x_3089_);
v___x_3091_ = lean_array_push(v___x_3090_, v___x_3086_);
v___x_3092_ = lean_array_push(v___x_3091_, v___x_3088_);
v___x_3093_ = l_Lean_saveModuleDataParts(v___x_3084_, v___x_3092_);
lean_dec_ref(v___x_3092_);
lean_dec(v___x_3084_);
if (lean_obj_tag(v___x_3093_) == 0)
{
uint8_t v___x_3094_; lean_object* v___x_3095_; 
lean_dec_ref_known(v___x_3093_, 1);
v___x_3094_ = 1;
v___x_3095_ = lean_io_prim_handle_mk(v_head_3002_, v___x_3094_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v_a_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; uint16_t v___x_3099_; lean_object* v___x_3101_; 
lean_dec(v_head_3002_);
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
lean_inc(v_a_3096_);
lean_dec_ref_known(v___x_3095_, 1);
v___x_3097_ = ((lean_object*)(l_main___closed__12));
v___x_3098_ = l_Lean_Core_getMaxHeartbeats(v___y_3054_);
v___x_3099_ = l_Lean_OptionFlags_ofOptions(v___y_3054_);
lean_inc_ref(v___y_3061_);
lean_inc_ref(v___y_3058_);
lean_inc_ref(v___y_3051_);
lean_inc_ref(v___y_3053_);
lean_inc_ref(v___y_3052_);
lean_inc_ref(v___y_3059_);
lean_inc_ref(v___y_3060_);
lean_inc(v___y_3055_);
lean_inc_ref(v_env_3065_);
if (v_isShared_3068_ == 0)
{
lean_ctor_set(v___x_3067_, 9, v___y_3061_);
lean_ctor_set(v___x_3067_, 8, v___y_3058_);
lean_ctor_set(v___x_3067_, 7, v___y_3051_);
lean_ctor_set(v___x_3067_, 6, v___y_3053_);
lean_ctor_set(v___x_3067_, 5, v___y_3052_);
lean_ctor_set(v___x_3067_, 4, v___y_3059_);
lean_ctor_set(v___x_3067_, 3, v___y_3062_);
lean_ctor_set(v___x_3067_, 2, v___y_3060_);
lean_ctor_set(v___x_3067_, 1, v___y_3055_);
v___x_3101_ = v___x_3067_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_env_3065_);
lean_ctor_set(v_reuseFailAlloc_3127_, 1, v___y_3055_);
lean_ctor_set(v_reuseFailAlloc_3127_, 2, v___y_3060_);
lean_ctor_set(v_reuseFailAlloc_3127_, 3, v___y_3062_);
lean_ctor_set(v_reuseFailAlloc_3127_, 4, v___y_3059_);
lean_ctor_set(v_reuseFailAlloc_3127_, 5, v___y_3052_);
lean_ctor_set(v_reuseFailAlloc_3127_, 6, v___y_3053_);
lean_ctor_set(v_reuseFailAlloc_3127_, 7, v___y_3051_);
lean_ctor_set(v_reuseFailAlloc_3127_, 8, v___y_3058_);
lean_ctor_set(v_reuseFailAlloc_3127_, 9, v___y_3061_);
v___x_3101_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___f_3106_; lean_object* v___x_3107_; 
v___x_3102_ = lean_box(v___x_3099_);
v___x_3103_ = lean_box(v___y_3050_);
v___x_3104_ = lean_box(v___x_3023_);
v___x_3105_ = lean_box(v___x_3075_);
lean_inc(v___y_3047_);
lean_inc(v___y_3044_);
lean_inc(v___y_3048_);
lean_inc(v___y_3043_);
lean_inc_ref(v___y_3045_);
lean_inc_ref(v___y_3042_);
lean_inc_ref(v___y_3046_);
v___f_3106_ = lean_alloc_closure((void*)(l_main___lam__2___boxed), 19, 18);
lean_closure_set(v___f_3106_, 0, v___x_3101_);
lean_closure_set(v___f_3106_, 1, v___y_3046_);
lean_closure_set(v___f_3106_, 2, v___x_3102_);
lean_closure_set(v___f_3106_, 3, v_name_3018_);
lean_closure_set(v___f_3106_, 4, v_a_3096_);
lean_closure_set(v___f_3106_, 5, v___x_3103_);
lean_closure_set(v___f_3106_, 6, v___y_3042_);
lean_closure_set(v___f_3106_, 7, v_head_2998_);
lean_closure_set(v___f_3106_, 8, v___y_3045_);
lean_closure_set(v___f_3106_, 9, v___y_3049_);
lean_closure_set(v___f_3106_, 10, v___y_3043_);
lean_closure_set(v___f_3106_, 11, v___x_3098_);
lean_closure_set(v___f_3106_, 12, v___y_3048_);
lean_closure_set(v___f_3106_, 13, v___y_3044_);
lean_closure_set(v___f_3106_, 14, v___x_3039_);
lean_closure_set(v___f_3106_, 15, v___y_3047_);
lean_closure_set(v___f_3106_, 16, v___x_3104_);
lean_closure_set(v___f_3106_, 17, v___x_3105_);
v___x_3107_ = l_Lean_profileitIOUnsafe___redArg(v___x_3097_, v___x_3040_, v___f_3106_, v___y_3057_);
lean_dec_ref(v___x_3040_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v___x_3108_; uint8_t v___x_3109_; 
lean_dec_ref_known(v___x_3107_, 1);
v___x_3108_ = lean_display_cumulative_profiling_times();
v___x_3109_ = lean_unbox(v_fst_3030_);
lean_dec(v_fst_3030_);
if (v___x_3109_ == 0)
{
lean_dec_ref(v_env_3065_);
goto v___jp_2969_;
}
else
{
lean_object* v___x_3110_; 
v___x_3110_ = l_Lean_Environment_displayStats(v_env_3065_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_dec_ref_known(v___x_3110_, 1);
goto v___jp_2969_;
}
else
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3118_; 
v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3113_ = v___x_3110_;
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3110_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3116_; 
if (v_isShared_3114_ == 0)
{
v___x_3116_ = v___x_3113_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_a_3111_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
}
}
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec_ref(v_env_3065_);
lean_dec(v_fst_3030_);
v_a_3119_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3107_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3107_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
}
else
{
lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
lean_dec_ref_known(v___x_3095_, 1);
lean_del_object(v___x_3067_);
lean_dec_ref(v_env_3065_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3057_);
lean_dec(v___y_3049_);
lean_dec_ref(v___x_3040_);
lean_dec(v_fst_3030_);
lean_dec(v_name_3018_);
lean_dec(v_head_2998_);
v___x_3128_ = ((lean_object*)(l_main___closed__13));
v___x_3129_ = lean_string_append(v___x_3128_, v_head_3002_);
lean_dec(v_head_3002_);
v___x_3130_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__1));
v___x_3131_ = lean_string_append(v___x_3129_, v___x_3130_);
v___x_3132_ = l_IO_eprintln___at___00main_spec__6(v___x_3131_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3140_; 
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3140_ == 0)
{
lean_object* v_unused_3141_; 
v_unused_3141_ = lean_ctor_get(v___x_3132_, 0);
lean_dec(v_unused_3141_);
v___x_3134_ = v___x_3132_;
v_isShared_3135_ = v_isSharedCheck_3140_;
goto v_resetjp_3133_;
}
else
{
lean_dec(v___x_3132_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3140_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3136_; lean_object* v___x_3138_; 
v___x_3136_ = l_main___boxed__const__2;
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 0, v___x_3136_);
v___x_3138_ = v___x_3134_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v___x_3136_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
else
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
v_a_3142_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3132_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3132_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3147_; 
if (v_isShared_3145_ == 0)
{
v___x_3147_ = v___x_3144_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_a_3142_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_del_object(v___x_3067_);
lean_dec_ref(v_env_3065_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3057_);
lean_dec(v___y_3049_);
lean_dec_ref(v___x_3040_);
lean_dec(v_fst_3030_);
lean_dec(v_name_3018_);
lean_dec(v_head_3002_);
lean_dec(v_head_2998_);
v_a_3150_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3093_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3093_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
}
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_dec(v_a_3079_);
lean_dec_ref(v___x_3077_);
lean_del_object(v___x_3067_);
lean_dec_ref(v_env_3065_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3057_);
lean_dec(v___y_3049_);
lean_dec_ref(v___x_3040_);
lean_del_object(v___x_3033_);
lean_dec(v_fst_3030_);
lean_dec(v_name_3018_);
lean_dec(v_head_3002_);
lean_del_object(v___x_3000_);
lean_dec(v_head_2998_);
v_a_3160_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3080_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3080_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
else
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
lean_dec_ref(v___x_3077_);
lean_del_object(v___x_3067_);
lean_dec_ref(v_env_3065_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3057_);
lean_dec(v___y_3049_);
lean_dec_ref(v___x_3040_);
lean_del_object(v___x_3033_);
lean_dec(v_fst_3030_);
lean_dec(v_name_3018_);
lean_dec(v_head_3002_);
lean_del_object(v___x_3000_);
lean_dec(v_head_2998_);
v_a_3168_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3078_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3078_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_3168_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
else
{
lean_object* v___x_3176_; lean_object* v___x_3178_; 
lean_del_object(v___x_3067_);
lean_dec_ref(v_env_3065_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3057_);
lean_dec(v___y_3049_);
lean_dec_ref(v___x_3040_);
lean_del_object(v___x_3033_);
lean_dec(v_fst_3030_);
lean_dec(v_name_3018_);
lean_dec(v_head_3002_);
lean_del_object(v___x_3000_);
lean_dec(v_head_2998_);
v___x_3176_ = l_main___boxed__const__2;
if (v_isShared_3074_ == 0)
{
lean_ctor_set(v___x_3073_, 0, v___x_3176_);
v___x_3178_ = v___x_3073_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v___x_3176_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
else
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
lean_del_object(v___x_3067_);
lean_dec_ref(v_env_3065_);
lean_dec_ref(v_messages_3064_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3057_);
lean_dec(v___y_3049_);
lean_dec_ref(v___x_3040_);
lean_del_object(v___x_3033_);
lean_dec(v_fst_3030_);
lean_dec(v_name_3018_);
lean_dec(v_head_3002_);
lean_del_object(v___x_3000_);
lean_dec(v_head_2998_);
v_a_3182_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3184_ = v___x_3071_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3071_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
}
v___jp_3199_:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; size_t v_sz_3236_; size_t v___x_3237_; lean_object* v___x_3238_; 
lean_inc_ref(v___y_3209_);
v___x_3233_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3233_, 0, v___y_3232_);
lean_ctor_set(v___x_3233_, 1, v_nextMacroScope_3219_);
lean_ctor_set(v___x_3233_, 2, v_ngen_3220_);
lean_ctor_set(v___x_3233_, 3, v_auxDeclNGen_3221_);
lean_ctor_set(v___x_3233_, 4, v_traceState_3222_);
lean_ctor_set(v___x_3233_, 5, v___y_3209_);
lean_ctor_set(v___x_3233_, 6, v_recordedDeps_3223_);
lean_ctor_set(v___x_3233_, 7, v_messages_3224_);
lean_ctor_set(v___x_3233_, 8, v_infoState_3225_);
lean_ctor_set(v___x_3233_, 9, v_snapshotTasks_3226_);
v___x_3234_ = lean_st_ref_put(v___y_3231_, v___x_3233_);
v___x_3235_ = lean_box(0);
v_sz_3236_ = lean_array_size(v___y_3217_);
v___x_3237_ = ((size_t)0ULL);
v___x_3238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(v___y_3217_, v_sz_3236_, v___x_3237_, v___x_3235_, v___y_3214_, v___y_3231_);
lean_dec_ref(v___y_3217_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_dec_ref_known(v___x_3238_, 1);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3214_);
v___y_3042_ = v___y_3200_;
v___y_3043_ = v___y_3201_;
v___y_3044_ = v___y_3202_;
v___y_3045_ = v___y_3204_;
v___y_3046_ = v___y_3203_;
v___y_3047_ = v___y_3205_;
v___y_3048_ = v___y_3207_;
v___y_3049_ = v___y_3206_;
v___y_3050_ = v___y_3208_;
v___y_3051_ = v___y_3218_;
v___y_3052_ = v___y_3209_;
v___y_3053_ = v___y_3227_;
v___y_3054_ = v___y_3228_;
v___y_3055_ = v___y_3229_;
v___y_3056_ = v___y_3210_;
v___y_3057_ = v___y_3230_;
v___y_3058_ = v___y_3211_;
v___y_3059_ = v___y_3212_;
v___y_3060_ = v___y_3213_;
v___y_3061_ = v___y_3216_;
v___y_3062_ = v___y_3215_;
goto v___jp_3041_;
}
else
{
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_dec_ref_known(v___x_3238_, 1);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3214_);
v___y_3042_ = v___y_3200_;
v___y_3043_ = v___y_3201_;
v___y_3044_ = v___y_3202_;
v___y_3045_ = v___y_3204_;
v___y_3046_ = v___y_3203_;
v___y_3047_ = v___y_3205_;
v___y_3048_ = v___y_3207_;
v___y_3049_ = v___y_3206_;
v___y_3050_ = v___y_3208_;
v___y_3051_ = v___y_3218_;
v___y_3052_ = v___y_3209_;
v___y_3053_ = v___y_3227_;
v___y_3054_ = v___y_3228_;
v___y_3055_ = v___y_3229_;
v___y_3056_ = v___y_3210_;
v___y_3057_ = v___y_3230_;
v___y_3058_ = v___y_3211_;
v___y_3059_ = v___y_3212_;
v___y_3060_ = v___y_3213_;
v___y_3061_ = v___y_3216_;
v___y_3062_ = v___y_3215_;
goto v___jp_3041_;
}
else
{
lean_object* v_a_3239_; uint8_t v___x_3240_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
lean_inc(v_a_3239_);
lean_dec_ref_known(v___x_3238_, 1);
v___x_3240_ = l_Lean_Exception_isInterrupt(v_a_3239_);
if (v___x_3240_ == 0)
{
lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3241_ = l_Lean_Exception_toMessageData(v_a_3239_);
v___x_3242_ = l_Lean_logError___at___00main_spec__13(v___x_3241_, v___y_3214_, v___y_3231_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3214_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_dec_ref_known(v___x_3242_, 1);
v___y_3042_ = v___y_3200_;
v___y_3043_ = v___y_3201_;
v___y_3044_ = v___y_3202_;
v___y_3045_ = v___y_3204_;
v___y_3046_ = v___y_3203_;
v___y_3047_ = v___y_3205_;
v___y_3048_ = v___y_3207_;
v___y_3049_ = v___y_3206_;
v___y_3050_ = v___y_3208_;
v___y_3051_ = v___y_3218_;
v___y_3052_ = v___y_3209_;
v___y_3053_ = v___y_3227_;
v___y_3054_ = v___y_3228_;
v___y_3055_ = v___y_3229_;
v___y_3056_ = v___y_3210_;
v___y_3057_ = v___y_3230_;
v___y_3058_ = v___y_3211_;
v___y_3059_ = v___y_3212_;
v___y_3060_ = v___y_3213_;
v___y_3061_ = v___y_3216_;
v___y_3062_ = v___y_3215_;
goto v___jp_3041_;
}
else
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
lean_dec_ref_known(v___x_3242_, 1);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3215_);
lean_dec(v___y_3210_);
lean_dec(v___y_3206_);
lean_dec_ref(v___x_3040_);
lean_del_object(v___x_3033_);
lean_dec(v_fst_3030_);
lean_dec(v_name_3018_);
lean_dec(v_head_3002_);
lean_del_object(v___x_3000_);
lean_dec(v_head_2998_);
v___x_3243_ = lean_obj_once(&l_main___closed__17, &l_main___closed__17_once, _init_l_main___closed__17);
v___x_3244_ = l_panic___at___00main_spec__5(v___x_3243_);
return v___x_3244_;
}
}
else
{
lean_dec(v_a_3239_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3214_);
v___y_3042_ = v___y_3200_;
v___y_3043_ = v___y_3201_;
v___y_3044_ = v___y_3202_;
v___y_3045_ = v___y_3204_;
v___y_3046_ = v___y_3203_;
v___y_3047_ = v___y_3205_;
v___y_3048_ = v___y_3207_;
v___y_3049_ = v___y_3206_;
v___y_3050_ = v___y_3208_;
v___y_3051_ = v___y_3218_;
v___y_3052_ = v___y_3209_;
v___y_3053_ = v___y_3227_;
v___y_3054_ = v___y_3228_;
v___y_3055_ = v___y_3229_;
v___y_3056_ = v___y_3210_;
v___y_3057_ = v___y_3230_;
v___y_3058_ = v___y_3211_;
v___y_3059_ = v___y_3212_;
v___y_3060_ = v___y_3213_;
v___y_3061_ = v___y_3216_;
v___y_3062_ = v___y_3215_;
goto v___jp_3041_;
}
}
}
}
v___jp_3245_:
{
lean_object* v_toCold_3272_; lean_object* v_currRecDepth_3273_; lean_object* v_ref_3274_; uint8_t v_suppressElabErrors_3275_; uint8_t v_isRecordingDeps_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3327_; 
v_toCold_3272_ = lean_ctor_get(v___y_3270_, 0);
v_currRecDepth_3273_ = lean_ctor_get(v___y_3270_, 1);
v_ref_3274_ = lean_ctor_get(v___y_3270_, 2);
v_suppressElabErrors_3275_ = lean_ctor_get_uint8(v___y_3270_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3276_ = lean_ctor_get_uint8(v___y_3270_, sizeof(void*)*3 + 3);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___y_3270_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3278_ = v___y_3270_;
v_isShared_3279_ = v_isSharedCheck_3327_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_ref_3274_);
lean_inc(v_currRecDepth_3273_);
lean_inc(v_toCold_3272_);
lean_dec(v___y_3270_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3327_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v_fileName_3280_; lean_object* v_fileMap_3281_; lean_object* v_currNamespace_3282_; lean_object* v_openDecls_3283_; lean_object* v_initHeartbeats_3284_; lean_object* v_maxHeartbeats_3285_; lean_object* v_quotContext_3286_; lean_object* v_currMacroScope_3287_; lean_object* v_cancelTk_x3f_3288_; lean_object* v_inheritedTraceOptions_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3324_; 
v_fileName_3280_ = lean_ctor_get(v_toCold_3272_, 0);
v_fileMap_3281_ = lean_ctor_get(v_toCold_3272_, 1);
v_currNamespace_3282_ = lean_ctor_get(v_toCold_3272_, 4);
v_openDecls_3283_ = lean_ctor_get(v_toCold_3272_, 5);
v_initHeartbeats_3284_ = lean_ctor_get(v_toCold_3272_, 6);
v_maxHeartbeats_3285_ = lean_ctor_get(v_toCold_3272_, 7);
v_quotContext_3286_ = lean_ctor_get(v_toCold_3272_, 8);
v_currMacroScope_3287_ = lean_ctor_get(v_toCold_3272_, 9);
v_cancelTk_x3f_3288_ = lean_ctor_get(v_toCold_3272_, 10);
v_inheritedTraceOptions_3289_ = lean_ctor_get(v_toCold_3272_, 11);
v_isSharedCheck_3324_ = !lean_is_exclusive(v_toCold_3272_);
if (v_isSharedCheck_3324_ == 0)
{
lean_object* v_unused_3325_; lean_object* v_unused_3326_; 
v_unused_3325_ = lean_ctor_get(v_toCold_3272_, 3);
lean_dec(v_unused_3325_);
v_unused_3326_ = lean_ctor_get(v_toCold_3272_, 2);
lean_dec(v_unused_3326_);
v___x_3291_ = v_toCold_3272_;
v_isShared_3292_ = v_isSharedCheck_3324_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_inheritedTraceOptions_3289_);
lean_inc(v_cancelTk_x3f_3288_);
lean_inc(v_currMacroScope_3287_);
lean_inc(v_quotContext_3286_);
lean_inc(v_maxHeartbeats_3285_);
lean_inc(v_initHeartbeats_3284_);
lean_inc(v_openDecls_3283_);
lean_inc(v_currNamespace_3282_);
lean_inc(v_fileMap_3281_);
lean_inc(v_fileName_3280_);
lean_dec(v_toCold_3272_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3324_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3296_; 
v___x_3293_ = l_Lean_maxRecDepth;
v___x_3294_ = l_Lean_Option_get___at___00main_spec__8(v___x_3040_, v___x_3293_);
lean_inc_ref(v___x_3040_);
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 3, v___x_3294_);
lean_ctor_set(v___x_3291_, 2, v___x_3040_);
v___x_3296_ = v___x_3291_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_fileName_3280_);
lean_ctor_set(v_reuseFailAlloc_3323_, 1, v_fileMap_3281_);
lean_ctor_set(v_reuseFailAlloc_3323_, 2, v___x_3040_);
lean_ctor_set(v_reuseFailAlloc_3323_, 3, v___x_3294_);
lean_ctor_set(v_reuseFailAlloc_3323_, 4, v_currNamespace_3282_);
lean_ctor_set(v_reuseFailAlloc_3323_, 5, v_openDecls_3283_);
lean_ctor_set(v_reuseFailAlloc_3323_, 6, v_initHeartbeats_3284_);
lean_ctor_set(v_reuseFailAlloc_3323_, 7, v_maxHeartbeats_3285_);
lean_ctor_set(v_reuseFailAlloc_3323_, 8, v_quotContext_3286_);
lean_ctor_set(v_reuseFailAlloc_3323_, 9, v_currMacroScope_3287_);
lean_ctor_set(v_reuseFailAlloc_3323_, 10, v_cancelTk_x3f_3288_);
lean_ctor_set(v_reuseFailAlloc_3323_, 11, v_inheritedTraceOptions_3289_);
v___x_3296_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
lean_object* v___x_3298_; 
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 0, v___x_3296_);
v___x_3298_ = v___x_3278_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3296_);
lean_ctor_set(v_reuseFailAlloc_3322_, 1, v_currRecDepth_3273_);
lean_ctor_set(v_reuseFailAlloc_3322_, 2, v_ref_3274_);
lean_ctor_set_uint8(v_reuseFailAlloc_3322_, sizeof(void*)*3 + 2, v_suppressElabErrors_3275_);
lean_ctor_set_uint8(v_reuseFailAlloc_3322_, sizeof(void*)*3 + 3, v_isRecordingDeps_3276_);
v___x_3298_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
lean_object* v___x_3299_; lean_object* v_env_3300_; lean_object* v_nextMacroScope_3301_; lean_object* v_ngen_3302_; lean_object* v_auxDeclNGen_3303_; lean_object* v_traceState_3304_; lean_object* v_recordedDeps_3305_; lean_object* v_messages_3306_; lean_object* v_infoState_3307_; lean_object* v_snapshotTasks_3308_; lean_object* v___x_3309_; uint8_t v___x_3310_; 
lean_ctor_set_uint16(v___x_3298_, sizeof(void*)*3, v___y_3269_);
v___x_3299_ = lean_st_ref_take(v___y_3271_);
v_env_3300_ = lean_ctor_get(v___x_3299_, 0);
lean_inc_ref(v_env_3300_);
v_nextMacroScope_3301_ = lean_ctor_get(v___x_3299_, 1);
lean_inc(v_nextMacroScope_3301_);
v_ngen_3302_ = lean_ctor_get(v___x_3299_, 2);
lean_inc_ref(v_ngen_3302_);
v_auxDeclNGen_3303_ = lean_ctor_get(v___x_3299_, 3);
lean_inc_ref(v_auxDeclNGen_3303_);
v_traceState_3304_ = lean_ctor_get(v___x_3299_, 4);
lean_inc_ref(v_traceState_3304_);
v_recordedDeps_3305_ = lean_ctor_get(v___x_3299_, 6);
lean_inc_ref(v_recordedDeps_3305_);
v_messages_3306_ = lean_ctor_get(v___x_3299_, 7);
lean_inc_ref(v_messages_3306_);
v_infoState_3307_ = lean_ctor_get(v___x_3299_, 8);
lean_inc_ref(v_infoState_3307_);
v_snapshotTasks_3308_ = lean_ctor_get(v___x_3299_, 9);
lean_inc_ref(v_snapshotTasks_3308_);
lean_dec(v___x_3299_);
v___x_3309_ = lean_array_get_size(v___y_3262_);
v___x_3310_ = lean_nat_dec_lt(v___x_3039_, v___x_3309_);
if (v___x_3310_ == 0)
{
lean_object* v___x_3311_; 
lean_inc_ref(v___y_3265_);
v___x_3311_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3265_, v_env_3300_, v___x_3014_);
v___y_3200_ = v___y_3246_;
v___y_3201_ = v___y_3247_;
v___y_3202_ = v___y_3248_;
v___y_3203_ = v___y_3250_;
v___y_3204_ = v___y_3249_;
v___y_3205_ = v___y_3251_;
v___y_3206_ = v___y_3253_;
v___y_3207_ = v___y_3252_;
v___y_3208_ = v___y_3254_;
v___y_3209_ = v___y_3255_;
v___y_3210_ = v___y_3256_;
v___y_3211_ = v___y_3257_;
v___y_3212_ = v___y_3258_;
v___y_3213_ = v___y_3259_;
v___y_3214_ = v___x_3298_;
v___y_3215_ = v___y_3260_;
v___y_3216_ = v___y_3261_;
v___y_3217_ = v___y_3262_;
v___y_3218_ = v___y_3263_;
v_nextMacroScope_3219_ = v_nextMacroScope_3301_;
v_ngen_3220_ = v_ngen_3302_;
v_auxDeclNGen_3221_ = v_auxDeclNGen_3303_;
v_traceState_3222_ = v_traceState_3304_;
v_recordedDeps_3223_ = v_recordedDeps_3305_;
v_messages_3224_ = v_messages_3306_;
v_infoState_3225_ = v_infoState_3307_;
v_snapshotTasks_3226_ = v_snapshotTasks_3308_;
v___y_3227_ = v___y_3264_;
v___y_3228_ = v___y_3266_;
v___y_3229_ = v___y_3267_;
v___y_3230_ = v___y_3268_;
v___y_3231_ = v___y_3271_;
v___y_3232_ = v___x_3311_;
goto v___jp_3199_;
}
else
{
uint8_t v___x_3312_; 
v___x_3312_ = lean_nat_dec_le(v___x_3309_, v___x_3309_);
if (v___x_3312_ == 0)
{
if (v___x_3310_ == 0)
{
lean_object* v___x_3313_; 
lean_inc_ref(v___y_3265_);
v___x_3313_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3265_, v_env_3300_, v___x_3014_);
v___y_3200_ = v___y_3246_;
v___y_3201_ = v___y_3247_;
v___y_3202_ = v___y_3248_;
v___y_3203_ = v___y_3250_;
v___y_3204_ = v___y_3249_;
v___y_3205_ = v___y_3251_;
v___y_3206_ = v___y_3253_;
v___y_3207_ = v___y_3252_;
v___y_3208_ = v___y_3254_;
v___y_3209_ = v___y_3255_;
v___y_3210_ = v___y_3256_;
v___y_3211_ = v___y_3257_;
v___y_3212_ = v___y_3258_;
v___y_3213_ = v___y_3259_;
v___y_3214_ = v___x_3298_;
v___y_3215_ = v___y_3260_;
v___y_3216_ = v___y_3261_;
v___y_3217_ = v___y_3262_;
v___y_3218_ = v___y_3263_;
v_nextMacroScope_3219_ = v_nextMacroScope_3301_;
v_ngen_3220_ = v_ngen_3302_;
v_auxDeclNGen_3221_ = v_auxDeclNGen_3303_;
v_traceState_3222_ = v_traceState_3304_;
v_recordedDeps_3223_ = v_recordedDeps_3305_;
v_messages_3224_ = v_messages_3306_;
v_infoState_3225_ = v_infoState_3307_;
v_snapshotTasks_3226_ = v_snapshotTasks_3308_;
v___y_3227_ = v___y_3264_;
v___y_3228_ = v___y_3266_;
v___y_3229_ = v___y_3267_;
v___y_3230_ = v___y_3268_;
v___y_3231_ = v___y_3271_;
v___y_3232_ = v___x_3313_;
goto v___jp_3199_;
}
else
{
size_t v___x_3314_; size_t v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3314_ = ((size_t)0ULL);
v___x_3315_ = lean_usize_of_nat(v___x_3309_);
v___x_3316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v___y_3262_, v___x_3314_, v___x_3315_, v___x_3014_);
lean_inc_ref(v___y_3265_);
v___x_3317_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3265_, v_env_3300_, v___x_3316_);
v___y_3200_ = v___y_3246_;
v___y_3201_ = v___y_3247_;
v___y_3202_ = v___y_3248_;
v___y_3203_ = v___y_3250_;
v___y_3204_ = v___y_3249_;
v___y_3205_ = v___y_3251_;
v___y_3206_ = v___y_3253_;
v___y_3207_ = v___y_3252_;
v___y_3208_ = v___y_3254_;
v___y_3209_ = v___y_3255_;
v___y_3210_ = v___y_3256_;
v___y_3211_ = v___y_3257_;
v___y_3212_ = v___y_3258_;
v___y_3213_ = v___y_3259_;
v___y_3214_ = v___x_3298_;
v___y_3215_ = v___y_3260_;
v___y_3216_ = v___y_3261_;
v___y_3217_ = v___y_3262_;
v___y_3218_ = v___y_3263_;
v_nextMacroScope_3219_ = v_nextMacroScope_3301_;
v_ngen_3220_ = v_ngen_3302_;
v_auxDeclNGen_3221_ = v_auxDeclNGen_3303_;
v_traceState_3222_ = v_traceState_3304_;
v_recordedDeps_3223_ = v_recordedDeps_3305_;
v_messages_3224_ = v_messages_3306_;
v_infoState_3225_ = v_infoState_3307_;
v_snapshotTasks_3226_ = v_snapshotTasks_3308_;
v___y_3227_ = v___y_3264_;
v___y_3228_ = v___y_3266_;
v___y_3229_ = v___y_3267_;
v___y_3230_ = v___y_3268_;
v___y_3231_ = v___y_3271_;
v___y_3232_ = v___x_3317_;
goto v___jp_3199_;
}
}
else
{
size_t v___x_3318_; size_t v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___x_3318_ = ((size_t)0ULL);
v___x_3319_ = lean_usize_of_nat(v___x_3309_);
v___x_3320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v___y_3262_, v___x_3318_, v___x_3319_, v___x_3014_);
lean_inc_ref(v___y_3265_);
v___x_3321_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3265_, v_env_3300_, v___x_3320_);
v___y_3200_ = v___y_3246_;
v___y_3201_ = v___y_3247_;
v___y_3202_ = v___y_3248_;
v___y_3203_ = v___y_3250_;
v___y_3204_ = v___y_3249_;
v___y_3205_ = v___y_3251_;
v___y_3206_ = v___y_3253_;
v___y_3207_ = v___y_3252_;
v___y_3208_ = v___y_3254_;
v___y_3209_ = v___y_3255_;
v___y_3210_ = v___y_3256_;
v___y_3211_ = v___y_3257_;
v___y_3212_ = v___y_3258_;
v___y_3213_ = v___y_3259_;
v___y_3214_ = v___x_3298_;
v___y_3215_ = v___y_3260_;
v___y_3216_ = v___y_3261_;
v___y_3217_ = v___y_3262_;
v___y_3218_ = v___y_3263_;
v_nextMacroScope_3219_ = v_nextMacroScope_3301_;
v_ngen_3220_ = v_ngen_3302_;
v_auxDeclNGen_3221_ = v_auxDeclNGen_3303_;
v_traceState_3222_ = v_traceState_3304_;
v_recordedDeps_3223_ = v_recordedDeps_3305_;
v_messages_3224_ = v_messages_3306_;
v_infoState_3225_ = v_infoState_3307_;
v_snapshotTasks_3226_ = v_snapshotTasks_3308_;
v___y_3227_ = v___y_3264_;
v___y_3228_ = v___y_3266_;
v___y_3229_ = v___y_3267_;
v___y_3230_ = v___y_3268_;
v___y_3231_ = v___y_3271_;
v___y_3232_ = v___x_3321_;
goto v___jp_3199_;
}
}
}
}
}
}
}
v___jp_3328_:
{
lean_object* v___x_3355_; lean_object* v_env_3356_; lean_object* v_nextMacroScope_3357_; lean_object* v_ngen_3358_; lean_object* v_auxDeclNGen_3359_; lean_object* v_traceState_3360_; lean_object* v_recordedDeps_3361_; lean_object* v_messages_3362_; lean_object* v_infoState_3363_; lean_object* v_snapshotTasks_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3373_; 
v___x_3355_ = lean_st_ref_take(v___y_3340_);
v_env_3356_ = lean_ctor_get(v___x_3355_, 0);
v_nextMacroScope_3357_ = lean_ctor_get(v___x_3355_, 1);
v_ngen_3358_ = lean_ctor_get(v___x_3355_, 2);
v_auxDeclNGen_3359_ = lean_ctor_get(v___x_3355_, 3);
v_traceState_3360_ = lean_ctor_get(v___x_3355_, 4);
v_recordedDeps_3361_ = lean_ctor_get(v___x_3355_, 6);
v_messages_3362_ = lean_ctor_get(v___x_3355_, 7);
v_infoState_3363_ = lean_ctor_get(v___x_3355_, 8);
v_snapshotTasks_3364_ = lean_ctor_get(v___x_3355_, 9);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3373_ == 0)
{
lean_object* v_unused_3374_; 
v_unused_3374_ = lean_ctor_get(v___x_3355_, 5);
lean_dec(v_unused_3374_);
v___x_3366_ = v___x_3355_;
v_isShared_3367_ = v_isSharedCheck_3373_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_snapshotTasks_3364_);
lean_inc(v_infoState_3363_);
lean_inc(v_messages_3362_);
lean_inc(v_recordedDeps_3361_);
lean_inc(v_traceState_3360_);
lean_inc(v_auxDeclNGen_3359_);
lean_inc(v_ngen_3358_);
lean_inc(v_nextMacroScope_3357_);
lean_inc(v_env_3356_);
lean_dec(v___x_3355_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3373_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3368_; lean_object* v___x_3370_; 
v___x_3368_ = l_Lean_Kernel_enableDiag(v_env_3356_, v___y_3354_);
lean_inc_ref(v___y_3339_);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 5, v___y_3339_);
lean_ctor_set(v___x_3366_, 0, v___x_3368_);
v___x_3370_ = v___x_3366_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3368_);
lean_ctor_set(v_reuseFailAlloc_3372_, 1, v_nextMacroScope_3357_);
lean_ctor_set(v_reuseFailAlloc_3372_, 2, v_ngen_3358_);
lean_ctor_set(v_reuseFailAlloc_3372_, 3, v_auxDeclNGen_3359_);
lean_ctor_set(v_reuseFailAlloc_3372_, 4, v_traceState_3360_);
lean_ctor_set(v_reuseFailAlloc_3372_, 5, v___y_3339_);
lean_ctor_set(v_reuseFailAlloc_3372_, 6, v_recordedDeps_3361_);
lean_ctor_set(v_reuseFailAlloc_3372_, 7, v_messages_3362_);
lean_ctor_set(v_reuseFailAlloc_3372_, 8, v_infoState_3363_);
lean_ctor_set(v_reuseFailAlloc_3372_, 9, v_snapshotTasks_3364_);
v___x_3370_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
lean_object* v___x_3371_; 
v___x_3371_ = lean_st_ref_put(v___y_3340_, v___x_3370_);
lean_inc(v___y_3340_);
v___y_3246_ = v___y_3329_;
v___y_3247_ = v___y_3330_;
v___y_3248_ = v___y_3331_;
v___y_3249_ = v___y_3333_;
v___y_3250_ = v___y_3332_;
v___y_3251_ = v___y_3334_;
v___y_3252_ = v___y_3336_;
v___y_3253_ = v___y_3335_;
v___y_3254_ = v___y_3337_;
v___y_3255_ = v___y_3339_;
v___y_3256_ = v___y_3340_;
v___y_3257_ = v___y_3341_;
v___y_3258_ = v___y_3342_;
v___y_3259_ = v___y_3343_;
v___y_3260_ = v___y_3344_;
v___y_3261_ = v___y_3345_;
v___y_3262_ = v___y_3346_;
v___y_3263_ = v___y_3347_;
v___y_3264_ = v___y_3348_;
v___y_3265_ = v___y_3349_;
v___y_3266_ = v___y_3350_;
v___y_3267_ = v___y_3351_;
v___y_3268_ = v___y_3352_;
v___y_3269_ = v___y_3353_;
v___y_3270_ = v___y_3338_;
v___y_3271_ = v___y_3340_;
goto v___jp_3245_;
}
}
}
v___jp_3375_:
{
if (v___y_3402_ == 0)
{
v___y_3329_ = v___y_3376_;
v___y_3330_ = v___y_3377_;
v___y_3331_ = v___y_3378_;
v___y_3332_ = v___y_3380_;
v___y_3333_ = v___y_3379_;
v___y_3334_ = v___y_3381_;
v___y_3335_ = v___y_3383_;
v___y_3336_ = v___y_3382_;
v___y_3337_ = v___y_3384_;
v___y_3338_ = v___y_3385_;
v___y_3339_ = v___y_3386_;
v___y_3340_ = v___y_3387_;
v___y_3341_ = v___y_3388_;
v___y_3342_ = v___y_3389_;
v___y_3343_ = v___y_3390_;
v___y_3344_ = v___y_3391_;
v___y_3345_ = v___y_3392_;
v___y_3346_ = v___y_3393_;
v___y_3347_ = v___y_3394_;
v___y_3348_ = v___y_3395_;
v___y_3349_ = v___y_3396_;
v___y_3350_ = v___y_3397_;
v___y_3351_ = v___y_3398_;
v___y_3352_ = v___y_3399_;
v___y_3353_ = v___y_3400_;
v___y_3354_ = v___y_3401_;
goto v___jp_3328_;
}
else
{
lean_inc(v___y_3387_);
v___y_3246_ = v___y_3376_;
v___y_3247_ = v___y_3377_;
v___y_3248_ = v___y_3378_;
v___y_3249_ = v___y_3379_;
v___y_3250_ = v___y_3380_;
v___y_3251_ = v___y_3381_;
v___y_3252_ = v___y_3382_;
v___y_3253_ = v___y_3383_;
v___y_3254_ = v___y_3384_;
v___y_3255_ = v___y_3386_;
v___y_3256_ = v___y_3387_;
v___y_3257_ = v___y_3388_;
v___y_3258_ = v___y_3389_;
v___y_3259_ = v___y_3390_;
v___y_3260_ = v___y_3391_;
v___y_3261_ = v___y_3392_;
v___y_3262_ = v___y_3393_;
v___y_3263_ = v___y_3394_;
v___y_3264_ = v___y_3395_;
v___y_3265_ = v___y_3396_;
v___y_3266_ = v___y_3397_;
v___y_3267_ = v___y_3398_;
v___y_3268_ = v___y_3399_;
v___y_3269_ = v___y_3400_;
v___y_3270_ = v___y_3385_;
v___y_3271_ = v___y_3387_;
goto v___jp_3245_;
}
}
v___jp_3403_:
{
if (v___y_3427_ == 0)
{
v___y_3376_ = v___y_3404_;
v___y_3377_ = v___y_3405_;
v___y_3378_ = v___y_3413_;
v___y_3379_ = v___y_3406_;
v___y_3380_ = v___y_3414_;
v___y_3381_ = v___y_3416_;
v___y_3382_ = v___y_3418_;
v___y_3383_ = v___y_3417_;
v___y_3384_ = v___y_3410_;
v___y_3385_ = v___y_3420_;
v___y_3386_ = v___y_3404_;
v___y_3387_ = v___y_3421_;
v___y_3388_ = v___y_3422_;
v___y_3389_ = v___y_3407_;
v___y_3390_ = v___y_3408_;
v___y_3391_ = v___y_3409_;
v___y_3392_ = v___y_3423_;
v___y_3393_ = v___y_3411_;
v___y_3394_ = v___y_3425_;
v___y_3395_ = v___y_3426_;
v___y_3396_ = v___y_3412_;
v___y_3397_ = v___y_3414_;
v___y_3398_ = v___y_3415_;
v___y_3399_ = v___y_3428_;
v___y_3400_ = v___y_3419_;
v___y_3401_ = v___y_3429_;
v___y_3402_ = v___y_3424_;
goto v___jp_3375_;
}
else
{
v___y_3329_ = v___y_3404_;
v___y_3330_ = v___y_3405_;
v___y_3331_ = v___y_3413_;
v___y_3332_ = v___y_3414_;
v___y_3333_ = v___y_3406_;
v___y_3334_ = v___y_3416_;
v___y_3335_ = v___y_3417_;
v___y_3336_ = v___y_3418_;
v___y_3337_ = v___y_3410_;
v___y_3338_ = v___y_3420_;
v___y_3339_ = v___y_3404_;
v___y_3340_ = v___y_3421_;
v___y_3341_ = v___y_3422_;
v___y_3342_ = v___y_3407_;
v___y_3343_ = v___y_3408_;
v___y_3344_ = v___y_3409_;
v___y_3345_ = v___y_3423_;
v___y_3346_ = v___y_3411_;
v___y_3347_ = v___y_3425_;
v___y_3348_ = v___y_3426_;
v___y_3349_ = v___y_3412_;
v___y_3350_ = v___y_3414_;
v___y_3351_ = v___y_3415_;
v___y_3352_ = v___y_3428_;
v___y_3353_ = v___y_3419_;
v___y_3354_ = v___y_3429_;
goto v___jp_3328_;
}
}
}
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
lean_dec_ref(v___f_3022_);
lean_dec(v_importArts_3020_);
lean_dec(v_name_3018_);
lean_dec(v_head_3002_);
lean_del_object(v___x_3000_);
lean_dec(v_head_2998_);
lean_del_object(v___x_2996_);
v_a_3732_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3028_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3028_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
}
else
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
lean_del_object(v___x_3005_);
lean_dec(v_tail_3003_);
lean_dec(v_head_3002_);
lean_del_object(v___x_3000_);
lean_dec(v_head_2998_);
lean_del_object(v___x_2996_);
v_a_3741_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3743_ = v___x_3016_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3016_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3741_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
}
}
}
else
{
lean_dec(v_tail_2993_);
lean_dec_ref_known(v_tail_2992_, 2);
lean_dec_ref_known(v_args_2967_, 2);
goto v___jp_2972_;
}
}
else
{
lean_dec_ref_known(v_args_2967_, 2);
lean_dec(v_tail_2992_);
goto v___jp_2972_;
}
}
else
{
lean_dec(v_args_2967_);
goto v___jp_2972_;
}
v___jp_2969_:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2970_ = l_main___boxed__const__1;
v___x_2971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2970_);
return v___x_2971_;
}
v___jp_2972_:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2973_ = ((lean_object*)(l_main___closed__0));
v___x_2974_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_2973_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2982_; 
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_2982_ == 0)
{
lean_object* v_unused_2983_; 
v_unused_2983_ = lean_ctor_get(v___x_2974_, 0);
lean_dec(v_unused_2983_);
v___x_2976_ = v___x_2974_;
v_isShared_2977_ = v_isSharedCheck_2982_;
goto v_resetjp_2975_;
}
else
{
lean_dec(v___x_2974_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2982_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2978_; lean_object* v___x_2980_; 
v___x_2978_ = l_main___boxed__const__2;
if (v_isShared_2977_ == 0)
{
lean_ctor_set(v___x_2976_, 0, v___x_2978_);
v___x_2980_ = v___x_2976_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2978_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
else
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
v_a_2984_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2974_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2974_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
if (v_isShared_2987_ == 0)
{
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_a_2984_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_3754_, lean_object* v_a_3755_){
_start:
{
lean_object* v_res_3756_; 
v_res_3756_ = _lean_main(v_args_3754_);
return v_res_3756_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object* v_as_3757_, lean_object* v_as_x27_3758_, lean_object* v_b_3759_, lean_object* v_a_3760_){
_start:
{
lean_object* v___x_3762_; 
v___x_3762_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_3758_, v_b_3759_);
return v___x_3762_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object* v_as_3763_, lean_object* v_as_x27_3764_, lean_object* v_b_3765_, lean_object* v_a_3766_, lean_object* v___y_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l_List_forIn_x27_loop___at___00main_spec__1(v_as_3763_, v_as_x27_3764_, v_b_3765_, v_a_3766_);
lean_dec(v_as_x27_3764_);
lean_dec(v_as_3763_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16(lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v___x_3772_; 
v___x_3772_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___y_3770_);
return v___x_3772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___boxed(lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
lean_object* v_res_3776_; 
v_res_3776_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16(v___y_3773_, v___y_3774_);
lean_dec(v___y_3774_);
lean_dec_ref(v___y_3773_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17(lean_object* v_00_u03b2_3777_, lean_object* v_m_3778_, lean_object* v_a_3779_, lean_object* v_fallback_3780_){
_start:
{
lean_object* v___x_3781_; 
v___x_3781_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_m_3778_, v_a_3779_, v_fallback_3780_);
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___boxed(lean_object* v_00_u03b2_3782_, lean_object* v_m_3783_, lean_object* v_a_3784_, lean_object* v_fallback_3785_){
_start:
{
lean_object* v_res_3786_; 
v_res_3786_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17(v_00_u03b2_3782_, v_m_3783_, v_a_3784_, v_fallback_3785_);
lean_dec(v_fallback_3785_);
lean_dec_ref(v_a_3784_);
lean_dec_ref(v_m_3783_);
return v_res_3786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18(lean_object* v_00_u03b2_3787_, lean_object* v_m_3788_, lean_object* v_a_3789_, lean_object* v_b_3790_){
_start:
{
lean_object* v___x_3791_; 
v___x_3791_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_m_3788_, v_a_3789_, v_b_3790_);
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21(lean_object* v_n_3792_, lean_object* v_as_3793_, lean_object* v_lo_3794_, lean_object* v_hi_3795_, lean_object* v_w_3796_, lean_object* v_hlo_3797_, lean_object* v_hhi_3798_){
_start:
{
lean_object* v___x_3799_; 
v___x_3799_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v_n_3792_, v_as_3793_, v_lo_3794_, v_hi_3795_);
return v___x_3799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___boxed(lean_object* v_n_3800_, lean_object* v_as_3801_, lean_object* v_lo_3802_, lean_object* v_hi_3803_, lean_object* v_w_3804_, lean_object* v_hlo_3805_, lean_object* v_hhi_3806_){
_start:
{
lean_object* v_res_3807_; 
v_res_3807_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21(v_n_3800_, v_as_3801_, v_lo_3802_, v_hi_3803_, v_w_3804_, v_hlo_3805_, v_hhi_3806_);
lean_dec(v_hi_3803_);
lean_dec(v_n_3800_);
return v_res_3807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21(lean_object* v_00_u03b2_3808_, lean_object* v_a_3809_, lean_object* v_fallback_3810_, lean_object* v_x_3811_){
_start:
{
lean_object* v___x_3812_; 
v___x_3812_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(v_a_3809_, v_fallback_3810_, v_x_3811_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3813_, lean_object* v_a_3814_, lean_object* v_fallback_3815_, lean_object* v_x_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21(v_00_u03b2_3813_, v_a_3814_, v_fallback_3815_, v_x_3816_);
lean_dec(v_x_3816_);
lean_dec(v_fallback_3815_);
lean_dec_ref(v_a_3814_);
return v_res_3817_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23(lean_object* v_00_u03b2_3818_, lean_object* v_a_3819_, lean_object* v_x_3820_){
_start:
{
uint8_t v___x_3821_; 
v___x_3821_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(v_a_3819_, v_x_3820_);
return v___x_3821_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___boxed(lean_object* v_00_u03b2_3822_, lean_object* v_a_3823_, lean_object* v_x_3824_){
_start:
{
uint8_t v_res_3825_; lean_object* v_r_3826_; 
v_res_3825_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23(v_00_u03b2_3822_, v_a_3823_, v_x_3824_);
lean_dec(v_x_3824_);
lean_dec_ref(v_a_3823_);
v_r_3826_ = lean_box(v_res_3825_);
return v_r_3826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24(lean_object* v_00_u03b2_3827_, lean_object* v_data_3828_){
_start:
{
lean_object* v___x_3829_; 
v___x_3829_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24___redArg(v_data_3828_);
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25(lean_object* v_00_u03b2_3830_, lean_object* v_a_3831_, lean_object* v_b_3832_, lean_object* v_x_3833_){
_start:
{
lean_object* v___x_3834_; 
v___x_3834_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(v_a_3831_, v_b_3832_, v_x_3833_);
return v___x_3834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31(lean_object* v_n_3835_, lean_object* v_lo_3836_, lean_object* v_hi_3837_, lean_object* v_hhi_3838_, lean_object* v_pivot_3839_, lean_object* v_as_3840_, lean_object* v_i_3841_, lean_object* v_k_3842_, lean_object* v_ilo_3843_, lean_object* v_ik_3844_, lean_object* v_w_3845_){
_start:
{
lean_object* v___x_3846_; 
v___x_3846_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(v_hi_3837_, v_pivot_3839_, v_as_3840_, v_i_3841_, v_k_3842_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___boxed(lean_object* v_n_3847_, lean_object* v_lo_3848_, lean_object* v_hi_3849_, lean_object* v_hhi_3850_, lean_object* v_pivot_3851_, lean_object* v_as_3852_, lean_object* v_i_3853_, lean_object* v_k_3854_, lean_object* v_ilo_3855_, lean_object* v_ik_3856_, lean_object* v_w_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31(v_n_3847_, v_lo_3848_, v_hi_3849_, v_hhi_3850_, v_pivot_3851_, v_as_3852_, v_i_3853_, v_k_3854_, v_ilo_3855_, v_ik_3856_, v_w_3857_);
lean_dec_ref(v_pivot_3851_);
lean_dec(v_hi_3849_);
lean_dec(v_lo_3848_);
lean_dec(v_n_3847_);
return v_res_3858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40(lean_object* v_as_3859_, size_t v_sz_3860_, size_t v_i_3861_, lean_object* v_b_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_){
_start:
{
lean_object* v___x_3866_; 
v___x_3866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(v_as_3859_, v_sz_3860_, v_i_3861_, v_b_3862_, v___y_3863_);
return v___x_3866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___boxed(lean_object* v_as_3867_, lean_object* v_sz_3868_, lean_object* v_i_3869_, lean_object* v_b_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
size_t v_sz_boxed_3874_; size_t v_i_boxed_3875_; lean_object* v_res_3876_; 
v_sz_boxed_3874_ = lean_unbox_usize(v_sz_3868_);
lean_dec(v_sz_3868_);
v_i_boxed_3875_ = lean_unbox_usize(v_i_3869_);
lean_dec(v_i_3869_);
v_res_3876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40(v_as_3867_, v_sz_boxed_3874_, v_i_boxed_3875_, v_b_3870_, v___y_3871_, v___y_3872_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec_ref(v_as_3867_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35(lean_object* v_00_u03b2_3877_, lean_object* v_i_3878_, lean_object* v_source_3879_, lean_object* v_target_3880_){
_start:
{
lean_object* v___x_3881_; 
v___x_3881_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35___redArg(v_i_3878_, v_source_3879_, v_target_3880_);
return v___x_3881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42(uint8_t v___x_3882_, lean_object* v_as_3883_, size_t v_sz_3884_, size_t v_i_3885_, lean_object* v_b_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_){
_start:
{
lean_object* v___x_3890_; 
v___x_3890_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(v___x_3882_, v_as_3883_, v_sz_3884_, v_i_3885_, v_b_3886_, v___y_3887_);
return v___x_3890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___boxed(lean_object* v___x_3891_, lean_object* v_as_3892_, lean_object* v_sz_3893_, lean_object* v_i_3894_, lean_object* v_b_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
uint8_t v___x_42430__boxed_3899_; size_t v_sz_boxed_3900_; size_t v_i_boxed_3901_; lean_object* v_res_3902_; 
v___x_42430__boxed_3899_ = lean_unbox(v___x_3891_);
v_sz_boxed_3900_ = lean_unbox_usize(v_sz_3893_);
lean_dec(v_sz_3893_);
v_i_boxed_3901_ = lean_unbox_usize(v_i_3894_);
lean_dec(v_i_3894_);
v_res_3902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42(v___x_42430__boxed_3899_, v_as_3892_, v_sz_boxed_3900_, v_i_boxed_3901_, v_b_3895_, v___y_3896_, v___y_3897_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec_ref(v_as_3892_);
return v_res_3902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51(lean_object* v_as_3903_, size_t v_sz_3904_, size_t v_i_3905_, lean_object* v_b_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_){
_start:
{
lean_object* v___x_3910_; 
v___x_3910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(v_as_3903_, v_sz_3904_, v_i_3905_, v_b_3906_, v___y_3907_);
return v___x_3910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___boxed(lean_object* v_as_3911_, lean_object* v_sz_3912_, lean_object* v_i_3913_, lean_object* v_b_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_){
_start:
{
size_t v_sz_boxed_3918_; size_t v_i_boxed_3919_; lean_object* v_res_3920_; 
v_sz_boxed_3918_ = lean_unbox_usize(v_sz_3912_);
lean_dec(v_sz_3912_);
v_i_boxed_3919_ = lean_unbox_usize(v_i_3913_);
lean_dec(v_i_3913_);
v_res_3920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51(v_as_3911_, v_sz_boxed_3918_, v_i_boxed_3919_, v_b_3914_, v___y_3915_, v___y_3916_);
lean_dec(v___y_3916_);
lean_dec_ref(v___y_3915_);
lean_dec_ref(v_as_3911_);
return v_res_3920_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44(lean_object* v_00_u03b2_3921_, lean_object* v_x_3922_, lean_object* v_x_3923_){
_start:
{
lean_object* v___x_3924_; 
v___x_3924_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44___redArg(v_x_3922_, v_x_3923_);
return v___x_3924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49(uint8_t v___x_3925_, lean_object* v_as_3926_, size_t v_sz_3927_, size_t v_i_3928_, lean_object* v_b_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_){
_start:
{
lean_object* v___x_3933_; 
v___x_3933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(v___x_3925_, v_as_3926_, v_sz_3927_, v_i_3928_, v_b_3929_, v___y_3930_);
return v___x_3933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___boxed(lean_object* v___x_3934_, lean_object* v_as_3935_, lean_object* v_sz_3936_, lean_object* v_i_3937_, lean_object* v_b_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_){
_start:
{
uint8_t v___x_42461__boxed_3942_; size_t v_sz_boxed_3943_; size_t v_i_boxed_3944_; lean_object* v_res_3945_; 
v___x_42461__boxed_3942_ = lean_unbox(v___x_3934_);
v_sz_boxed_3943_ = lean_unbox_usize(v_sz_3936_);
lean_dec(v_sz_3936_);
v_i_boxed_3944_ = lean_unbox_usize(v_i_3937_);
lean_dec(v_i_3937_);
v_res_3945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49(v___x_42461__boxed_3942_, v_as_3935_, v_sz_boxed_3943_, v_i_boxed_3944_, v_b_3938_, v___y_3939_, v___y_3940_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec_ref(v_as_3935_);
return v_res_3945_;
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
