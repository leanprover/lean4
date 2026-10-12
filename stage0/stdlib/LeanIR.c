// Lean compiler output
// Module: LeanIR
// Imports: public import Init public meta import Init import Lean.CoreM import Lean.Util.ForEachExpr import all Lean.Util.Path import all Lean.Environment import Lean.Compiler.Options import Lean.Compiler.Bytecode.Basic import Lean.Compiler.ModPkgExt import all Lean.Compiler.CSimpAttr import Lean.Compiler.LCNF.EmitC import Lean.Language.Lean import Lean.Compiler.LCNF.PhaseExt import Lean.Compiler.LCNF.Main import Lean.Meta.ExprDefEq import Lean.Meta.LevelDefEq import Lean.Meta.Match.MatchEqs import Lean.Elab.PreDefinition.Structural.Eqns import Lean.Parser
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
lean_object* lean_bytecode_export_entries(lean_object*);
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
extern lean_object* l_Lean_Compiler_Bytecode_declMapExt;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
lean_object* lean_bytecode_mk_initial_cache(lean_object*);
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
lean_object* l___private_LeanIR_0__mkIRSigData(lean_object* v_env_1_){
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
LEAN_EXPORT void l___private_LeanIR_0__mkIRSigData_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1_ = stack[0].m_obj;
lean_object* v_res_29_;
v_res_29_ = l___private_LeanIR_0__mkIRSigData(v_env_1_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__mkIRSigData___boxed(lean_object* v_env_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l___private_LeanIR_0__mkIRSigData(v_env_30_);
return v_res_32_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1(lean_object* v_a_33_, lean_object* v_as_34_, size_t v_i_35_, size_t v_stop_36_){
_start:
{
uint8_t v___x_37_; 
v___x_37_ = lean_usize_dec_eq(v_i_35_, v_stop_36_);
if (v___x_37_ == 0)
{
lean_object* v___x_38_; uint8_t v___x_39_; 
v___x_38_ = lean_array_uget_borrowed(v_as_34_, v_i_35_);
v___x_39_ = lean_name_eq(v_a_33_, v___x_38_);
if (v___x_39_ == 0)
{
size_t v___x_40_; size_t v___x_41_; 
v___x_40_ = ((size_t)1ULL);
v___x_41_ = lean_usize_add(v_i_35_, v___x_40_);
v_i_35_ = v___x_41_;
goto _start;
}
else
{
return v___x_39_;
}
}
else
{
uint8_t v___x_43_; 
v___x_43_ = 0;
return v___x_43_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_33_ = stack[0].m_obj;
lean_object* v_as_34_ = stack[1].m_obj;
size_t v_i_35_ = stack[2].m_num;
size_t v_stop_36_ = stack[3].m_num;
uint8_t v_res_44_;
v_res_44_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1(v_a_33_, v_as_34_, v_i_35_, v_stop_36_);
stack->m_num = v_res_44_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1___boxed(lean_object* v_a_45_, lean_object* v_as_46_, lean_object* v_i_47_, lean_object* v_stop_48_){
_start:
{
size_t v_i_boxed_49_; size_t v_stop_boxed_50_; uint8_t v_res_51_; lean_object* v_r_52_; 
v_i_boxed_49_ = lean_unbox_usize(v_i_47_);
lean_dec(v_i_47_);
v_stop_boxed_50_ = lean_unbox_usize(v_stop_48_);
lean_dec(v_stop_48_);
v_res_51_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1(v_a_45_, v_as_46_, v_i_boxed_49_, v_stop_boxed_50_);
lean_dec_ref(v_as_46_);
lean_dec(v_a_45_);
v_r_52_ = lean_box(v_res_51_);
return v_r_52_;
}
}
uint8_t l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1(lean_object* v_as_53_, lean_object* v_a_54_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_55_ = lean_unsigned_to_nat(0u);
v___x_56_ = lean_array_get_size(v_as_53_);
v___x_57_ = lean_nat_dec_lt(v___x_55_, v___x_56_);
if (v___x_57_ == 0)
{
return v___x_57_;
}
else
{
if (v___x_57_ == 0)
{
return v___x_57_;
}
else
{
size_t v___x_58_; size_t v___x_59_; uint8_t v___x_60_; 
v___x_58_ = ((size_t)0ULL);
v___x_59_ = lean_usize_of_nat(v___x_56_);
v___x_60_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1(v_a_54_, v_as_53_, v___x_58_, v___x_59_);
return v___x_60_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_53_ = stack[0].m_obj;
lean_object* v_a_54_ = stack[1].m_obj;
uint8_t v_res_61_;
v_res_61_ = l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1(v_as_53_, v_a_54_);
stack->m_num = v_res_61_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1___boxed(lean_object* v_as_62_, lean_object* v_a_63_){
_start:
{
uint8_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1(v_as_62_, v_a_63_);
lean_dec(v_a_63_);
lean_dec_ref(v_as_62_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(lean_object* v_irExtNames_66_, lean_object* v_as_67_, size_t v_i_68_, size_t v_stop_69_, lean_object* v_b_70_){
_start:
{
lean_object* v___y_72_; uint8_t v___x_76_; 
v___x_76_ = lean_usize_dec_eq(v_i_68_, v_stop_69_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v_fst_78_; uint8_t v___x_79_; 
v___x_77_ = lean_array_uget_borrowed(v_as_67_, v_i_68_);
v_fst_78_ = lean_ctor_get(v___x_77_, 0);
v___x_79_ = l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1(v_irExtNames_66_, v_fst_78_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; 
lean_inc(v___x_77_);
v___x_80_ = lean_array_push(v_b_70_, v___x_77_);
v___y_72_ = v___x_80_;
goto v___jp_71_;
}
else
{
v___y_72_ = v_b_70_;
goto v___jp_71_;
}
}
else
{
return v_b_70_;
}
v___jp_71_:
{
size_t v___x_73_; size_t v___x_74_; 
v___x_73_ = ((size_t)1ULL);
v___x_74_ = lean_usize_add(v_i_68_, v___x_73_);
v_i_68_ = v___x_74_;
v_b_70_ = v___y_72_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_irExtNames_66_ = stack[0].m_obj;
lean_object* v_as_67_ = stack[1].m_obj;
size_t v_i_68_ = stack[2].m_num;
size_t v_stop_69_ = stack[3].m_num;
lean_object* v_b_70_ = stack[4].m_obj;
lean_object* v_res_81_;
v_res_81_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(v_irExtNames_66_, v_as_67_, v_i_68_, v_stop_69_, v_b_70_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2___boxed(lean_object* v_irExtNames_82_, lean_object* v_as_83_, lean_object* v_i_84_, lean_object* v_stop_85_, lean_object* v_b_86_){
_start:
{
size_t v_i_boxed_87_; size_t v_stop_boxed_88_; lean_object* v_res_89_; 
v_i_boxed_87_ = lean_unbox_usize(v_i_84_);
lean_dec(v_i_84_);
v_stop_boxed_88_ = lean_unbox_usize(v_stop_85_);
lean_dec(v_stop_85_);
v_res_89_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(v_irExtNames_82_, v_as_83_, v_i_boxed_87_, v_stop_boxed_88_, v_b_86_);
lean_dec_ref(v_as_83_);
lean_dec_ref(v_irExtNames_82_);
return v_res_89_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0(size_t v_sz_90_, size_t v_i_91_, lean_object* v_bs_92_){
_start:
{
uint8_t v___x_93_; 
v___x_93_ = lean_usize_dec_lt(v_i_91_, v_sz_90_);
if (v___x_93_ == 0)
{
return v_bs_92_;
}
else
{
lean_object* v_v_94_; lean_object* v_fst_95_; lean_object* v___x_96_; lean_object* v_bs_x27_97_; size_t v___x_98_; size_t v___x_99_; lean_object* v___x_100_; 
v_v_94_ = lean_array_uget_borrowed(v_bs_92_, v_i_91_);
v_fst_95_ = lean_ctor_get(v_v_94_, 0);
lean_inc(v_fst_95_);
v___x_96_ = lean_unsigned_to_nat(0u);
v_bs_x27_97_ = lean_array_uset(v_bs_92_, v_i_91_, v___x_96_);
v___x_98_ = ((size_t)1ULL);
v___x_99_ = lean_usize_add(v_i_91_, v___x_98_);
v___x_100_ = lean_array_uset(v_bs_x27_97_, v_i_91_, v_fst_95_);
v_i_91_ = v___x_99_;
v_bs_92_ = v___x_100_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_90_ = stack[0].m_num;
size_t v_i_91_ = stack[1].m_num;
lean_object* v_bs_92_ = stack[2].m_obj;
lean_object* v_res_102_;
v_res_102_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0(v_sz_90_, v_i_91_, v_bs_92_);
stack->m_obj
 = v_res_102_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0___boxed(lean_object* v_sz_103_, lean_object* v_i_104_, lean_object* v_bs_105_){
_start:
{
size_t v_sz_boxed_106_; size_t v_i_boxed_107_; lean_object* v_res_108_; 
v_sz_boxed_106_ = lean_unbox_usize(v_sz_103_);
lean_dec(v_sz_103_);
v_i_boxed_107_ = lean_unbox_usize(v_i_104_);
lean_dec(v_i_104_);
v_res_108_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0(v_sz_boxed_106_, v_i_boxed_107_, v_bs_105_);
return v_res_108_;
}
}
lean_object* l___private_LeanIR_0__mkIRData(lean_object* v_env_113_){
_start:
{
lean_object* v_irEntries_115_; size_t v_sz_116_; size_t v___x_117_; lean_object* v_irExtNames_118_; uint8_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
lean_inc_ref_n(v_env_113_, 2);
v_irEntries_115_ = lean_bytecode_export_entries(v_env_113_);
v_sz_116_ = lean_array_size(v_irEntries_115_);
v___x_117_ = ((size_t)0ULL);
lean_inc_ref(v_irEntries_115_);
v_irExtNames_118_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0(v_sz_116_, v___x_117_, v_irEntries_115_);
v___x_119_ = 2;
v___x_120_ = lean_box(0);
v___x_121_ = l_Lean_mkModuleData(v_env_113_, v___x_119_, v___x_120_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_149_; 
v_a_122_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_149_ == 0)
{
v___x_124_ = v___x_121_;
v_isShared_125_ = v_isSharedCheck_149_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_121_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_149_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___y_127_; lean_object* v_entries_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v_entries_139_ = lean_ctor_get(v_a_122_, 4);
lean_inc_ref(v_entries_139_);
lean_dec(v_a_122_);
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = lean_array_get_size(v_entries_139_);
v___x_142_ = ((lean_object*)(l___private_LeanIR_0__mkIRData___closed__1));
v___x_143_ = lean_nat_dec_lt(v___x_140_, v___x_141_);
if (v___x_143_ == 0)
{
lean_dec_ref(v_entries_139_);
lean_dec_ref(v_irExtNames_118_);
v___y_127_ = v___x_142_;
goto v___jp_126_;
}
else
{
uint8_t v___x_144_; 
v___x_144_ = lean_nat_dec_le(v___x_141_, v___x_141_);
if (v___x_144_ == 0)
{
if (v___x_143_ == 0)
{
lean_dec_ref(v_entries_139_);
lean_dec_ref(v_irExtNames_118_);
v___y_127_ = v___x_142_;
goto v___jp_126_;
}
else
{
size_t v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lean_usize_of_nat(v___x_141_);
v___x_146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(v_irExtNames_118_, v_entries_139_, v___x_117_, v___x_145_, v___x_142_);
lean_dec_ref(v_entries_139_);
lean_dec_ref(v_irExtNames_118_);
v___y_127_ = v___x_146_;
goto v___jp_126_;
}
}
else
{
size_t v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_usize_of_nat(v___x_141_);
v___x_148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(v_irExtNames_118_, v_entries_139_, v___x_117_, v___x_147_, v___x_142_);
lean_dec_ref(v_entries_139_);
lean_dec_ref(v_irExtNames_118_);
v___y_127_ = v___x_148_;
goto v___jp_126_;
}
}
v___jp_126_:
{
lean_object* v___x_128_; uint8_t v_isModule_129_; lean_object* v_imports_130_; lean_object* v___x_131_; uint8_t v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_128_ = l_Lean_Environment_header(v_env_113_);
v_isModule_129_ = lean_ctor_get_uint8(v___x_128_, sizeof(void*)*8 + 4);
v_imports_130_ = lean_ctor_get(v___x_128_, 1);
lean_inc_ref(v_imports_130_);
lean_dec_ref(v___x_128_);
v___x_131_ = ((lean_object*)(l___private_LeanIR_0__mkIRData___closed__0));
v___x_132_ = 1;
v___x_133_ = lean_get_ir_extra_const_names(v_env_113_, v___x_119_, v___x_132_);
v___x_134_ = l_Array_append___redArg(v_irEntries_115_, v___y_127_);
lean_dec_ref(v___y_127_);
v___x_135_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_135_, 0, v_imports_130_);
lean_ctor_set(v___x_135_, 1, v___x_131_);
lean_ctor_set(v___x_135_, 2, v___x_131_);
lean_ctor_set(v___x_135_, 3, v___x_133_);
lean_ctor_set(v___x_135_, 4, v___x_134_);
lean_ctor_set_uint8(v___x_135_, sizeof(void*)*5, v_isModule_129_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v___x_135_);
v___x_137_ = v___x_124_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
else
{
lean_dec_ref(v_irExtNames_118_);
lean_dec_ref(v_irEntries_115_);
lean_dec_ref(v_env_113_);
return v___x_121_;
}
}
}
LEAN_EXPORT void l___private_LeanIR_0__mkIRData_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_113_ = stack[0].m_obj;
lean_object* v_res_150_;
v_res_150_ = l___private_LeanIR_0__mkIRData(v_env_113_);
stack->m_obj
 = v_res_150_;
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__mkIRData___boxed(lean_object* v_env_151_, lean_object* v_a_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l___private_LeanIR_0__mkIRData(v_env_151_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(lean_object* v_s_155_){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_156_ = lean_string_utf8_byte_size(v_s_155_);
v___x_157_ = lean_unsigned_to_nat(2u);
v___x_158_ = lean_nat_dec_le(v___x_157_, v___x_156_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; 
lean_dec_ref(v_s_155_);
v___x_159_ = lean_box(0);
return v___x_159_;
}
else
{
lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_160_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__0));
v___x_161_ = lean_unsigned_to_nat(0u);
v___x_162_ = lean_string_memcmp(v_s_155_, v___x_160_, v___x_161_, v___x_161_, v___x_157_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; 
lean_dec_ref(v_s_155_);
v___x_163_ = lean_box(0);
return v___x_163_;
}
else
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
lean_inc_ref(v_s_155_);
v___x_164_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_164_, 0, v_s_155_);
lean_ctor_set(v___x_164_, 1, v___x_161_);
lean_ctor_set(v___x_164_, 2, v___x_156_);
v___x_165_ = l_String_Slice_pos_x21(v___x_164_, v___x_157_);
lean_dec_ref_known(v___x_164_, 3);
v___x_166_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_166_, 0, v_s_155_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
lean_ctor_set(v___x_166_, 2, v___x_156_);
v___x_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
return v___x_167_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0(lean_object* v_s_168_, lean_object* v_pat_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(v_s_168_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___boxed(lean_object* v_s_171_, lean_object* v_pat_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0(v_s_171_, v_pat_172_);
lean_dec_ref(v_pat_172_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(lean_object* v_val_174_, lean_object* v_a_175_, lean_object* v_b_176_){
_start:
{
lean_object* v_str_177_; lean_object* v_startInclusive_178_; lean_object* v_endExclusive_179_; lean_object* v___x_180_; uint8_t v_decide_181_; 
v_str_177_ = lean_ctor_get(v_val_174_, 0);
v_startInclusive_178_ = lean_ctor_get(v_val_174_, 1);
v_endExclusive_179_ = lean_ctor_get(v_val_174_, 2);
v___x_180_ = lean_nat_sub(v_endExclusive_179_, v_startInclusive_178_);
v_decide_181_ = lean_nat_dec_eq(v_a_175_, v___x_180_);
lean_dec(v___x_180_);
if (v_decide_181_ == 0)
{
lean_object* v___x_182_; uint32_t v___x_183_; uint32_t v___x_184_; uint8_t v___x_185_; 
v___x_182_ = lean_nat_add(v_startInclusive_178_, v_a_175_);
v___x_183_ = lean_string_utf8_get_fast(v_str_177_, v___x_182_);
v___x_184_ = 61;
v___x_185_ = lean_uint32_dec_eq(v___x_183_, v___x_184_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
lean_dec(v_a_175_);
v___x_186_ = lean_box(0);
v___x_187_ = lean_string_utf8_next_fast(v_str_177_, v___x_182_);
lean_dec(v___x_182_);
v___x_188_ = lean_nat_sub(v___x_187_, v_startInclusive_178_);
v_a_175_ = v___x_188_;
v_b_176_ = v___x_186_;
goto _start;
}
else
{
lean_object* v___x_190_; 
lean_dec(v___x_182_);
v___x_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_190_, 0, v_a_175_);
return v___x_190_;
}
}
else
{
lean_dec(v_a_175_);
lean_inc(v_b_176_);
return v_b_176_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg___boxed(lean_object* v_val_191_, lean_object* v_a_192_, lean_object* v_b_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(v_val_191_, v_a_192_, v_b_193_);
lean_dec(v_b_193_);
lean_dec_ref(v_val_191_);
return v_res_194_;
}
}
lean_object* l___private_LeanIR_0__setConfigOption(lean_object* v_opts_202_, lean_object* v_arg_203_){
_start:
{
lean_object* v___x_205_; 
lean_inc_ref(v_arg_203_);
v___x_205_ = l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(v_arg_203_);
if (lean_obj_tag(v___x_205_) == 1)
{
lean_object* v_val_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_270_; 
lean_dec_ref(v_arg_203_);
v_val_206_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_270_ == 0)
{
v___x_208_ = v___x_205_;
v_isShared_209_ = v_isSharedCheck_270_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_val_206_);
lean_dec(v___x_205_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_270_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___y_211_; lean_object* v_searcher_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v_searcher_263_ = lean_unsigned_to_nat(0u);
v___x_264_ = lean_box(0);
v___x_265_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(v_val_206_, v_searcher_263_, v___x_264_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_startInclusive_266_; lean_object* v_endExclusive_267_; lean_object* v___x_268_; 
v_startInclusive_266_ = lean_ctor_get(v_val_206_, 1);
v_endExclusive_267_ = lean_ctor_get(v_val_206_, 2);
v___x_268_ = lean_nat_sub(v_endExclusive_267_, v_startInclusive_266_);
v___y_211_ = v___x_268_;
goto v___jp_210_;
}
else
{
lean_object* v_val_269_; 
v_val_269_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_val_269_);
lean_dec_ref_known(v___x_265_, 1);
v___y_211_ = v_val_269_;
goto v___jp_210_;
}
v___jp_210_:
{
lean_object* v_str_212_; lean_object* v_startInclusive_213_; lean_object* v_endExclusive_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_262_; 
v_str_212_ = lean_ctor_get(v_val_206_, 0);
v_startInclusive_213_ = lean_ctor_get(v_val_206_, 1);
v_endExclusive_214_ = lean_ctor_get(v_val_206_, 2);
v_isSharedCheck_262_ = !lean_is_exclusive(v_val_206_);
if (v_isSharedCheck_262_ == 0)
{
v___x_216_ = v_val_206_;
v_isShared_217_ = v_isSharedCheck_262_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_endExclusive_214_);
lean_inc(v_startInclusive_213_);
lean_inc(v_str_212_);
lean_dec(v_val_206_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_262_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_218_; uint8_t v_decide_219_; 
v___x_218_ = lean_nat_sub(v_endExclusive_214_, v_startInclusive_213_);
v_decide_219_ = lean_nat_dec_eq(v___y_211_, v___x_218_);
lean_dec(v___x_218_);
if (v_decide_219_ == 0)
{
lean_object* v___x_220_; lean_object* v___x_222_; 
v___x_220_ = lean_nat_add(v_startInclusive_213_, v___y_211_);
lean_dec(v___y_211_);
lean_inc(v___x_220_);
lean_inc(v_startInclusive_213_);
lean_inc_ref(v_str_212_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 2, v___x_220_);
v___x_222_ = v___x_216_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_str_212_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_startInclusive_213_);
lean_ctor_set(v_reuseFailAlloc_257_, 2, v___x_220_);
v___x_222_ = v_reuseFailAlloc_257_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
lean_object* v_name_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v_val_227_; lean_object* v___x_228_; 
v_name_223_ = l_String_Slice_toName(v___x_222_);
lean_dec_ref(v___x_222_);
v___x_224_ = lean_string_utf8_next_fast(v_str_212_, v___x_220_);
lean_dec(v___x_220_);
v___x_225_ = lean_nat_sub(v___x_224_, v_startInclusive_213_);
v___x_226_ = lean_nat_add(v_startInclusive_213_, v___x_225_);
lean_dec(v___x_225_);
lean_dec(v_startInclusive_213_);
v_val_227_ = lean_string_utf8_extract_fast(v_str_212_, v___x_226_, v_endExclusive_214_);
lean_dec(v_endExclusive_214_);
lean_dec(v___x_226_);
lean_dec_ref(v_str_212_);
v___x_228_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_248_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_248_ == 0)
{
v___x_231_ = v___x_228_;
v_isShared_232_ = v_isSharedCheck_248_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_228_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_248_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; 
v___x_233_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_229_, v_name_223_);
lean_dec(v_a_229_);
if (lean_obj_tag(v___x_233_) == 1)
{
lean_object* v_val_234_; lean_object* v___x_235_; 
lean_del_object(v___x_231_);
lean_del_object(v___x_208_);
v_val_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_val_234_);
lean_dec_ref_known(v___x_233_, 1);
v___x_235_ = l_Lean_Language_Lean_setOption(v_opts_202_, v_val_234_, v_name_223_, v_val_227_);
return v___x_235_;
}
else
{
lean_object* v___x_236_; uint8_t v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_243_; 
lean_dec(v___x_233_);
lean_dec_ref(v_val_227_);
lean_dec_ref(v_opts_202_);
v___x_236_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__0));
v___x_237_ = 1;
v___x_238_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_223_, v___x_237_);
v___x_239_ = lean_string_append(v___x_236_, v___x_238_);
lean_dec_ref(v___x_238_);
v___x_240_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__1));
v___x_241_ = lean_string_append(v___x_239_, v___x_240_);
if (v_isShared_209_ == 0)
{
lean_ctor_set_tag(v___x_208_, 18);
lean_ctor_set(v___x_208_, 0, v___x_241_);
v___x_243_ = v___x_208_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_241_);
v___x_243_ = v_reuseFailAlloc_247_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_245_; 
if (v_isShared_232_ == 0)
{
lean_ctor_set_tag(v___x_231_, 1);
lean_ctor_set(v___x_231_, 0, v___x_243_);
v___x_245_ = v___x_231_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_243_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
}
else
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_256_; 
lean_dec_ref(v_val_227_);
lean_dec(v_name_223_);
lean_del_object(v___x_208_);
lean_dec_ref(v_opts_202_);
v_a_249_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_256_ == 0)
{
v___x_251_ = v___x_228_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_228_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_254_; 
if (v_isShared_252_ == 0)
{
v___x_254_ = v___x_251_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_a_249_);
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
else
{
lean_object* v___x_258_; lean_object* v___x_260_; 
lean_del_object(v___x_216_);
lean_dec(v_endExclusive_214_);
lean_dec(v_startInclusive_213_);
lean_dec_ref(v_str_212_);
lean_dec(v___y_211_);
lean_dec_ref(v_opts_202_);
v___x_258_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__3));
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v___x_258_);
v___x_260_ = v___x_208_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
}
}
else
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
lean_dec(v___x_205_);
lean_dec_ref(v_opts_202_);
v___x_271_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__4));
v___x_272_ = lean_string_append(v___x_271_, v_arg_203_);
lean_dec_ref(v_arg_203_);
v___x_273_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__5));
v___x_274_ = lean_string_append(v___x_272_, v___x_273_);
v___x_275_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
v___x_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
return v___x_276_;
}
}
}
LEAN_EXPORT void l___private_LeanIR_0__setConfigOption_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_202_ = stack[0].m_obj;
lean_object* v_arg_203_ = stack[1].m_obj;
lean_object* v_res_277_;
v_res_277_ = l___private_LeanIR_0__setConfigOption(v_opts_202_, v_arg_203_);
stack->m_obj
 = v_res_277_;
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption___boxed(lean_object* v_opts_278_, lean_object* v_arg_279_, lean_object* v_a_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l___private_LeanIR_0__setConfigOption(v_opts_278_, v_arg_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1(lean_object* v_val_282_, lean_object* v_inst_283_, lean_object* v_R_284_, lean_object* v_a_285_, lean_object* v_b_286_, lean_object* v_c_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(v_val_282_, v_a_285_, v_b_286_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___boxed(lean_object* v_val_289_, lean_object* v_inst_290_, lean_object* v_R_291_, lean_object* v_a_292_, lean_object* v_b_293_, lean_object* v_c_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1(v_val_289_, v_inst_290_, v_R_291_, v_a_292_, v_b_293_, v_c_294_);
lean_dec(v_b_293_);
lean_dec_ref(v_val_289_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg___lam__0(lean_object* v___x_296_, lean_object* v_x_297_){
_start:
{
lean_inc_ref(v___x_296_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg___lam__0___boxed(lean_object* v___x_298_, lean_object* v_x_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_main___elam__0___redArg___lam__0(v___x_298_, v_x_299_);
lean_dec_ref(v_x_299_);
lean_dec_ref(v___x_298_);
return v_res_300_;
}
}
lean_object* l_main___elam__0___redArg(lean_object* v___x_301_, uint8_t v___x_302_, lean_object* v_inst_303_, lean_object* v_ext_304_, lean_object* v_env_305_){
_start:
{
lean_object* v_toEnvExtension_307_; lean_object* v_addImportedFn_308_; lean_object* v_asyncMode_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v_importedEntries_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_343_; 
v_toEnvExtension_307_ = lean_ctor_get(v_ext_304_, 0);
lean_inc_ref(v_toEnvExtension_307_);
v_addImportedFn_308_ = lean_ctor_get(v_ext_304_, 2);
lean_inc_ref(v_addImportedFn_308_);
lean_dec_ref(v_ext_304_);
v_asyncMode_309_ = lean_ctor_get(v_toEnvExtension_307_, 2);
v___x_310_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v_inst_303_);
lean_inc_ref(v_env_305_);
v___x_311_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_310_, v_toEnvExtension_307_, v_env_305_, v_asyncMode_309_, v___x_301_, v___x_302_);
lean_dec_ref(v___x_310_);
v_importedEntries_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_343_ == 0)
{
lean_object* v_unused_344_; 
v_unused_344_ = lean_ctor_get(v___x_311_, 1);
lean_dec(v_unused_344_);
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_343_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_importedEntries_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_343_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_316_ = l_Lean_Options_empty;
lean_inc_ref(v_env_305_);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v_env_305_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
lean_inc_ref(v_importedEntries_312_);
v___x_318_ = lean_apply_3(v_addImportedFn_308_, v_importedEntries_312_, v___x_317_, lean_box(0));
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_334_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_334_ == 0)
{
v___x_321_ = v___x_318_;
v_isShared_322_ = v_isSharedCheck_334_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_318_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_334_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 1, v_a_319_);
v___x_324_ = v___x_314_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_importedEntries_312_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_a_319_);
v___x_324_ = v_reuseFailAlloc_333_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___f_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
v___f_325_ = lean_alloc_closure((void*)(l_main___elam__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_325_, 0, v___x_324_);
v___x_326_ = lean_box(0);
v___x_327_ = lean_box(0);
v___x_328_ = 1;
v___x_329_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_307_, v_env_305_, v___f_325_, v___x_326_, v___x_327_, v___x_328_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_329_);
v___x_331_ = v___x_321_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
else
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
lean_del_object(v___x_314_);
lean_dec_ref(v_importedEntries_312_);
lean_dec_ref(v_toEnvExtension_307_);
lean_dec_ref(v_env_305_);
v_a_335_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_342_ == 0)
{
v___x_337_ = v___x_318_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_318_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_335_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
}
}
LEAN_EXPORT void l_main___elam__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_301_ = stack[0].m_obj;
uint8_t v___x_302_ = stack[1].m_num;
lean_object* v_inst_303_ = stack[2].m_obj;
lean_object* v_ext_304_ = stack[3].m_obj;
lean_object* v_env_305_ = stack[4].m_obj;
lean_object* v_res_345_;
v_res_345_ = l_main___elam__0___redArg(v___x_301_, v___x_302_, v_inst_303_, v_ext_304_, v_env_305_);
stack->m_obj
 = v_res_345_;
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg___boxed(lean_object* v___x_346_, lean_object* v___x_347_, lean_object* v_inst_348_, lean_object* v_ext_349_, lean_object* v_env_350_, lean_object* v___y_351_){
_start:
{
uint8_t v___x_37003__boxed_352_; lean_object* v_res_353_; 
v___x_37003__boxed_352_ = lean_unbox(v___x_347_);
v_res_353_ = l_main___elam__0___redArg(v___x_346_, v___x_37003__boxed_352_, v_inst_348_, v_ext_349_, v_env_350_);
return v_res_353_;
}
}
lean_object* l_main___elam__0(lean_object* v___x_354_, uint8_t v___x_355_, lean_object* v_00_u03b1_356_, lean_object* v_00_u03b2_357_, lean_object* v_00_u03c3_358_, lean_object* v_inst_359_, lean_object* v_ext_360_, lean_object* v_env_361_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_main___elam__0___redArg(v___x_354_, v___x_355_, v_inst_359_, v_ext_360_, v_env_361_);
return v___x_363_;
}
}
LEAN_EXPORT void l_main___elam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_354_ = stack[0].m_obj;
uint8_t v___x_355_ = stack[1].m_num;
lean_object* v_inst_359_ = stack[5].m_obj;
lean_object* v_ext_360_ = stack[6].m_obj;
lean_object* v_env_361_ = stack[7].m_obj;
lean_object* v_res_364_;
v_res_364_ = l_main___elam__0(v___x_354_, v___x_355_, lean_box(0), lean_box(0), lean_box(0), v_inst_359_, v_ext_360_, v_env_361_);
stack->m_obj
 = v_res_364_;
}
LEAN_EXPORT lean_object* l_main___elam__0___boxed(lean_object* v___x_365_, lean_object* v___x_366_, lean_object* v_00_u03b1_367_, lean_object* v_00_u03b2_368_, lean_object* v_00_u03c3_369_, lean_object* v_inst_370_, lean_object* v_ext_371_, lean_object* v_env_372_, lean_object* v___y_373_){
_start:
{
uint8_t v___x_37125__boxed_374_; lean_object* v_res_375_; 
v___x_37125__boxed_374_ = lean_unbox(v___x_366_);
v_res_375_ = l_main___elam__0(v___x_365_, v___x_37125__boxed_374_, v_00_u03b1_367_, v_00_u03b2_368_, v_00_u03c3_369_, v_inst_370_, v_ext_371_, v_env_372_);
return v_res_375_;
}
}
static lean_object* _init_l_panic___at___00main_spec__5___closed__0(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = l_instInhabitedError;
v___x_377_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_377_, 0, lean_box(0));
lean_closure_set(v___x_377_, 1, lean_box(0));
lean_closure_set(v___x_377_, 2, v___x_376_);
return v___x_377_;
}
}
lean_object* l_panic___at___00main_spec__5(lean_object* v_msg_378_){
_start:
{
lean_object* v___x_380_; lean_object* v___x_20109__overap_381_; lean_object* v___x_382_; 
v___x_380_ = lean_obj_once(&l_panic___at___00main_spec__5___closed__0, &l_panic___at___00main_spec__5___closed__0_once, _init_l_panic___at___00main_spec__5___closed__0);
v___x_20109__overap_381_ = lean_panic_fn_borrowed(v___x_380_, v_msg_378_);
v___x_382_ = lean_apply_1(v___x_20109__overap_381_, lean_box(0));
return v___x_382_;
}
}
LEAN_EXPORT void l_panic___at___00main_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_378_ = stack[0].m_obj;
lean_object* v_res_383_;
v_res_383_ = l_panic___at___00main_spec__5(v_msg_378_);
stack->m_obj
 = v_res_383_;
}
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5___boxed(lean_object* v_msg_384_, lean_object* v___y_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_panic___at___00main_spec__5(v_msg_384_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8(lean_object* v_opts_387_, lean_object* v_opt_388_){
_start:
{
lean_object* v_name_389_; lean_object* v_defValue_390_; lean_object* v_map_391_; lean_object* v___x_392_; 
v_name_389_ = lean_ctor_get(v_opt_388_, 0);
v_defValue_390_ = lean_ctor_get(v_opt_388_, 1);
v_map_391_ = lean_ctor_get(v_opts_387_, 0);
v___x_392_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_391_, v_name_389_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_inc(v_defValue_390_);
return v_defValue_390_;
}
else
{
lean_object* v_val_393_; 
v_val_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_val_393_);
lean_dec_ref_known(v___x_392_, 1);
if (lean_obj_tag(v_val_393_) == 3)
{
lean_object* v_v_394_; 
v_v_394_ = lean_ctor_get(v_val_393_, 0);
lean_inc(v_v_394_);
lean_dec_ref_known(v_val_393_, 1);
return v_v_394_;
}
else
{
lean_dec(v_val_393_);
lean_inc(v_defValue_390_);
return v_defValue_390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8___boxed(lean_object* v_opts_395_, lean_object* v_opt_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Option_get___at___00main_spec__8(v_opts_395_, v_opt_396_);
lean_dec_ref(v_opt_396_);
lean_dec_ref(v_opts_395_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_main___lam__0(lean_object* v_package_x3f_398_, lean_object* v_ps_399_){
_start:
{
lean_object* v_importedEntries_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
v_importedEntries_400_ = lean_ctor_get(v_ps_399_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v_ps_399_);
if (v_isSharedCheck_407_ == 0)
{
lean_object* v_unused_408_; 
v_unused_408_ = lean_ctor_get(v_ps_399_, 1);
lean_dec(v_unused_408_);
v___x_402_ = v_ps_399_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_importedEntries_400_);
lean_dec(v_ps_399_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 1, v_package_x3f_398_);
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_importedEntries_400_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_package_x3f_398_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(lean_object* v_a_409_, lean_object* v_x_410_){
_start:
{
if (lean_obj_tag(v_x_410_) == 0)
{
lean_dec(v_a_409_);
return v_x_410_;
}
else
{
lean_object* v_key_411_; lean_object* v_value_412_; lean_object* v_tail_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_446_; 
v_key_411_ = lean_ctor_get(v_x_410_, 0);
v_value_412_ = lean_ctor_get(v_x_410_, 1);
v_tail_413_ = lean_ctor_get(v_x_410_, 2);
v_isSharedCheck_446_ = !lean_is_exclusive(v_x_410_);
if (v_isSharedCheck_446_ == 0)
{
v___x_415_ = v_x_410_;
v_isShared_416_ = v_isSharedCheck_446_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_tail_413_);
lean_inc(v_value_412_);
lean_inc(v_key_411_);
lean_dec(v_x_410_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_446_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
uint8_t v___x_417_; 
v___x_417_ = lean_name_eq(v_key_411_, v_a_409_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_418_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v_a_409_, v_tail_413_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 2, v___x_418_);
v___x_420_ = v___x_415_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_key_411_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_value_412_);
lean_ctor_set(v_reuseFailAlloc_421_, 2, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
else
{
lean_object* v_toEffectiveImport_422_; lean_object* v_parts_423_; lean_object* v_irParts_424_; uint8_t v_needsIRTrans_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_445_; 
lean_dec(v_key_411_);
v_toEffectiveImport_422_ = lean_ctor_get(v_value_412_, 0);
v_parts_423_ = lean_ctor_get(v_value_412_, 1);
v_irParts_424_ = lean_ctor_get(v_value_412_, 2);
v_needsIRTrans_425_ = lean_ctor_get_uint8(v_value_412_, sizeof(void*)*3);
v_isSharedCheck_445_ = !lean_is_exclusive(v_value_412_);
if (v_isSharedCheck_445_ == 0)
{
v___x_427_ = v_value_412_;
v_isShared_428_ = v_isSharedCheck_445_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_irParts_424_);
lean_inc(v_parts_423_);
lean_inc(v_toEffectiveImport_422_);
lean_dec(v_value_412_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_445_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v_toImport_429_; uint8_t v_hasData_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_444_; 
v_toImport_429_ = lean_ctor_get(v_toEffectiveImport_422_, 0);
v_hasData_430_ = lean_ctor_get_uint8(v_toEffectiveImport_422_, sizeof(void*)*1 + 1);
v_isSharedCheck_444_ = !lean_is_exclusive(v_toEffectiveImport_422_);
if (v_isSharedCheck_444_ == 0)
{
v___x_432_ = v_toEffectiveImport_422_;
v_isShared_433_ = v_isSharedCheck_444_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_toImport_429_);
lean_dec(v_toEffectiveImport_422_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_444_;
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
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_toImport_429_);
lean_ctor_set_uint8(v_reuseFailAlloc_443_, sizeof(void*)*1 + 1, v_hasData_430_);
v___x_436_ = v_reuseFailAlloc_443_;
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
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_parts_423_);
lean_ctor_set(v_reuseFailAlloc_442_, 2, v_irParts_424_);
lean_ctor_set_uint8(v_reuseFailAlloc_442_, sizeof(void*)*3, v_needsIRTrans_425_);
v___x_438_ = v_reuseFailAlloc_442_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_440_; 
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 1, v___x_438_);
lean_ctor_set(v___x_415_, 0, v_a_409_);
v___x_440_ = v___x_415_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_409_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_441_, 2, v_tail_413_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(lean_object* v_m_447_, lean_object* v_a_448_){
_start:
{
lean_object* v_size_449_; lean_object* v_buckets_450_; lean_object* v___x_451_; uint64_t v___y_453_; 
v_size_449_ = lean_ctor_get(v_m_447_, 0);
v_buckets_450_ = lean_ctor_get(v_m_447_, 1);
v___x_451_ = lean_array_get_size(v_buckets_450_);
if (lean_obj_tag(v_a_448_) == 0)
{
uint64_t v___x_480_; 
v___x_480_ = 1723ULL;
v___y_453_ = v___x_480_;
goto v___jp_452_;
}
else
{
uint64_t v_hash_481_; 
v_hash_481_ = lean_ctor_get_uint64(v_a_448_, sizeof(void*)*2);
v___y_453_ = v_hash_481_;
goto v___jp_452_;
}
v___jp_452_:
{
uint64_t v___x_454_; uint64_t v___x_455_; uint64_t v_fold_456_; uint64_t v___x_457_; uint64_t v___x_458_; uint64_t v___x_459_; size_t v___x_460_; size_t v___x_461_; size_t v___x_462_; size_t v___x_463_; size_t v___x_464_; lean_object* v_bucket_465_; uint8_t v___x_466_; 
v___x_454_ = 32ULL;
v___x_455_ = lean_uint64_shift_right(v___y_453_, v___x_454_);
v_fold_456_ = lean_uint64_xor(v___y_453_, v___x_455_);
v___x_457_ = 16ULL;
v___x_458_ = lean_uint64_shift_right(v_fold_456_, v___x_457_);
v___x_459_ = lean_uint64_xor(v_fold_456_, v___x_458_);
v___x_460_ = lean_uint64_to_usize(v___x_459_);
v___x_461_ = lean_usize_of_nat(v___x_451_);
v___x_462_ = ((size_t)1ULL);
v___x_463_ = lean_usize_sub(v___x_461_, v___x_462_);
v___x_464_ = lean_usize_land(v___x_460_, v___x_463_);
v_bucket_465_ = lean_array_uget_borrowed(v_buckets_450_, v___x_464_);
v___x_466_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_a_448_, v_bucket_465_);
if (v___x_466_ == 0)
{
lean_dec(v_a_448_);
return v_m_447_;
}
else
{
lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_477_; 
lean_inc(v_bucket_465_);
lean_inc_ref(v_buckets_450_);
lean_inc(v_size_449_);
v_isSharedCheck_477_ = !lean_is_exclusive(v_m_447_);
if (v_isSharedCheck_477_ == 0)
{
lean_object* v_unused_478_; lean_object* v_unused_479_; 
v_unused_478_ = lean_ctor_get(v_m_447_, 1);
lean_dec(v_unused_478_);
v_unused_479_ = lean_ctor_get(v_m_447_, 0);
lean_dec(v_unused_479_);
v___x_468_ = v_m_447_;
v_isShared_469_ = v_isSharedCheck_477_;
goto v_resetjp_467_;
}
else
{
lean_dec(v_m_447_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_477_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v_buckets_471_; lean_object* v_bucket_472_; lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_470_ = lean_box(0);
v_buckets_471_ = lean_array_uset(v_buckets_450_, v___x_464_, v___x_470_);
v_bucket_472_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v_a_448_, v_bucket_465_);
v___x_473_ = lean_array_uset(v_buckets_471_, v___x_464_, v_bucket_472_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 1, v___x_473_);
v___x_475_ = v___x_468_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_size_449_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v___x_473_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
}
lean_object* l_main___lam__1(lean_object* v___x_482_, lean_object* v___x_483_, uint8_t v___x_484_, lean_object* v_importArts_485_, uint8_t v___y_486_, uint8_t v___x_487_, lean_object* v_name_488_, lean_object* v___x_489_, uint8_t v___x_490_){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_st_mk_ref(v___x_482_);
v___x_493_ = l_Lean_importModulesCore(v___x_483_, v___x_484_, v_importArts_485_, v___y_486_, v___x_487_, v___x_492_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v___x_494_; lean_object* v_moduleNameMap_495_; lean_object* v_moduleNames_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_506_; 
lean_dec_ref_known(v___x_493_, 1);
v___x_494_ = lean_st_ref_get(v___x_492_);
lean_dec(v___x_492_);
v_moduleNameMap_495_ = lean_ctor_get(v___x_494_, 0);
v_moduleNames_496_ = lean_ctor_get(v___x_494_, 1);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_506_ == 0)
{
v___x_498_ = v___x_494_;
v_isShared_499_ = v_isSharedCheck_506_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_moduleNames_496_);
lean_inc(v_moduleNameMap_495_);
lean_dec(v___x_494_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_506_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_500_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(v_moduleNameMap_495_, v_name_488_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_500_);
v___x_502_ = v___x_498_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_500_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_moduleNames_496_);
v___x_502_ = v_reuseFailAlloc_505_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
uint32_t v___x_503_; lean_object* v___x_504_; 
v___x_503_ = 0;
v___x_504_ = l_Lean_finalizeImport(v___x_502_, v___x_483_, v___x_489_, v___x_503_, v___x_487_, v___x_490_, v___x_484_, v___x_487_, v___x_487_);
lean_dec_ref(v___x_502_);
return v___x_504_;
}
}
}
else
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
lean_dec(v___x_492_);
lean_dec_ref(v___x_489_);
lean_dec(v_name_488_);
lean_dec_ref(v___x_483_);
v_a_507_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___x_493_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_493_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_507_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
}
LEAN_EXPORT void l_main___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_482_ = stack[0].m_obj;
lean_object* v___x_483_ = stack[1].m_obj;
uint8_t v___x_484_ = stack[2].m_num;
lean_object* v_importArts_485_ = stack[3].m_obj;
uint8_t v___y_486_ = stack[4].m_num;
uint8_t v___x_487_ = stack[5].m_num;
lean_object* v_name_488_ = stack[6].m_obj;
lean_object* v___x_489_ = stack[7].m_obj;
uint8_t v___x_490_ = stack[8].m_num;
lean_object* v_res_515_;
v_res_515_ = l_main___lam__1(v___x_482_, v___x_483_, v___x_484_, v_importArts_485_, v___y_486_, v___x_487_, v_name_488_, v___x_489_, v___x_490_);
stack->m_obj
 = v_res_515_;
}
LEAN_EXPORT lean_object* l_main___lam__1___boxed(lean_object* v___x_516_, lean_object* v___x_517_, lean_object* v___x_518_, lean_object* v_importArts_519_, lean_object* v___y_520_, lean_object* v___x_521_, lean_object* v_name_522_, lean_object* v___x_523_, lean_object* v___x_524_, lean_object* v___y_525_){
_start:
{
uint8_t v___x_37378__boxed_526_; uint8_t v___y_37379__boxed_527_; uint8_t v___x_37380__boxed_528_; uint8_t v___x_37382__boxed_529_; lean_object* v_res_530_; 
v___x_37378__boxed_526_ = lean_unbox(v___x_518_);
v___y_37379__boxed_527_ = lean_unbox(v___y_520_);
v___x_37380__boxed_528_ = lean_unbox(v___x_521_);
v___x_37382__boxed_529_ = lean_unbox(v___x_524_);
v_res_530_ = l_main___lam__1(v___x_516_, v___x_517_, v___x_37378__boxed_526_, v_importArts_519_, v___y_37379__boxed_527_, v___x_37380__boxed_528_, v_name_522_, v___x_523_, v___x_37382__boxed_529_);
return v_res_530_;
}
}
lean_object* l_main___lam__2(lean_object* v___x_534_, lean_object* v___x_535_, uint16_t v___x_536_, lean_object* v_name_537_, lean_object* v_a_538_, uint8_t v___x_539_, lean_object* v___x_540_, lean_object* v_head_541_, lean_object* v___x_542_, lean_object* v___x_543_, lean_object* v___x_544_, lean_object* v___x_545_, lean_object* v___x_546_, lean_object* v___x_547_, lean_object* v___x_548_, lean_object* v___x_549_, uint8_t v___x_550_, uint8_t v___x_551_){
_start:
{
lean_object* v_a_554_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v_fileName_560_; lean_object* v_fileMap_561_; lean_object* v_currNamespace_562_; lean_object* v_openDecls_563_; lean_object* v_initHeartbeats_564_; lean_object* v_maxHeartbeats_565_; lean_object* v_quotContext_566_; lean_object* v_currMacroScope_567_; lean_object* v_cancelTk_x3f_568_; lean_object* v_inheritedTraceOptions_569_; lean_object* v_currRecDepth_570_; lean_object* v_ref_571_; uint8_t v_suppressElabErrors_572_; uint8_t v_isRecordingDeps_573_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___y_609_; uint8_t v___y_631_; uint8_t v___y_632_; lean_object* v_env_633_; uint8_t v___x_634_; uint8_t v___y_636_; uint16_t v___x_637_; uint16_t v___x_638_; uint16_t v___x_639_; uint8_t v___x_640_; 
v___x_557_ = lean_io_get_num_heartbeats();
v___x_558_ = lean_st_mk_ref(v___x_534_);
v___x_605_ = l_Lean_inheritedTraceOptions;
v___x_606_ = lean_st_ref_get(v___x_605_);
v___x_607_ = lean_st_ref_get(v___x_558_);
v_env_633_ = lean_ctor_get(v___x_607_, 0);
lean_inc_ref(v_env_633_);
lean_dec(v___x_607_);
v___x_634_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_633_);
lean_dec_ref(v_env_633_);
v___x_637_ = 512;
v___x_638_ = lean_uint16_land(v___x_536_, v___x_637_);
v___x_639_ = 0;
v___x_640_ = lean_uint16_dec_eq(v___x_638_, v___x_639_);
if (v___x_640_ == 0)
{
v___y_636_ = v___x_539_;
goto v___jp_635_;
}
else
{
v___y_636_ = v___x_551_;
goto v___jp_635_;
}
v___jp_553_:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_mk_io_user_error(v_a_554_);
v___x_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
v___jp_559_:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_574_ = l_Lean_maxRecDepth;
v___x_575_ = l_Lean_Option_get___at___00main_spec__8(v___x_535_, v___x_574_);
v___x_576_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_576_, 0, v_fileName_560_);
lean_ctor_set(v___x_576_, 1, v_fileMap_561_);
lean_ctor_set(v___x_576_, 2, v___x_535_);
lean_ctor_set(v___x_576_, 3, v___x_575_);
lean_ctor_set(v___x_576_, 4, v_currNamespace_562_);
lean_ctor_set(v___x_576_, 5, v_openDecls_563_);
lean_ctor_set(v___x_576_, 6, v_initHeartbeats_564_);
lean_ctor_set(v___x_576_, 7, v_maxHeartbeats_565_);
lean_ctor_set(v___x_576_, 8, v_quotContext_566_);
lean_ctor_set(v___x_576_, 9, v_currMacroScope_567_);
lean_ctor_set(v___x_576_, 10, v_cancelTk_x3f_568_);
lean_ctor_set(v___x_576_, 11, v_inheritedTraceOptions_569_);
v___x_577_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v_currRecDepth_570_);
lean_ctor_set(v___x_577_, 2, v_ref_571_);
lean_ctor_set_uint16(v___x_577_, sizeof(void*)*3, v___x_536_);
lean_ctor_set_uint8(v___x_577_, sizeof(void*)*3 + 2, v_suppressElabErrors_572_);
lean_ctor_set_uint8(v___x_577_, sizeof(void*)*3 + 3, v_isRecordingDeps_573_);
v___x_578_ = l_Lean_Compiler_LCNF_emitC(v_name_537_, v___x_577_, v___x_558_);
lean_dec_ref_known(v___x_577_, 3);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref_known(v___x_578_, 1);
v___x_580_ = lean_st_ref_get(v___x_558_);
lean_dec(v___x_558_);
lean_dec(v___x_580_);
v___x_581_ = lean_string_to_utf8(v_a_579_);
lean_dec(v_a_579_);
v___x_582_ = lean_io_prim_handle_write(v_a_538_, v___x_581_);
lean_dec_ref(v___x_581_);
return v___x_582_;
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_604_; 
lean_dec(v___x_558_);
v_a_583_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_604_ == 0)
{
v___x_585_ = v___x_578_;
v_isShared_586_ = v_isSharedCheck_604_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_578_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_604_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
if (lean_obj_tag(v_a_583_) == 0)
{
lean_object* v_msg_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_591_; 
v_msg_587_ = lean_ctor_get(v_a_583_, 1);
lean_inc_ref(v_msg_587_);
lean_dec_ref_known(v_a_583_, 2);
v___x_588_ = l_Lean_MessageData_toString(v_msg_587_);
v___x_589_ = lean_mk_io_user_error(v___x_588_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_589_);
v___x_591_ = v___x_585_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_589_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
else
{
lean_object* v_id_593_; lean_object* v___x_594_; 
lean_del_object(v___x_585_);
v_id_593_ = lean_ctor_get(v_a_583_, 0);
lean_inc(v_id_593_);
lean_dec_ref_known(v_a_583_, 2);
v___x_594_ = l_Lean_InternalExceptionId_getName(v_id_593_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
lean_dec(v_id_593_);
v_a_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_a_595_);
lean_dec_ref_known(v___x_594_, 1);
v___x_596_ = ((lean_object*)(l_main___lam__2___closed__0));
v___x_597_ = l_Lean_Name_toString(v_a_595_, v___x_539_);
v___x_598_ = lean_string_append(v___x_596_, v___x_597_);
lean_dec_ref(v___x_597_);
v_a_554_ = v___x_598_;
goto v___jp_553_;
}
else
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
lean_dec_ref_known(v___x_594_, 1);
v___x_599_ = ((lean_object*)(l_main___lam__2___closed__1));
v___x_600_ = l_Nat_reprFast(v_id_593_);
v___x_601_ = lean_string_append(v___x_599_, v___x_600_);
lean_dec_ref(v___x_600_);
v___x_602_ = ((lean_object*)(l_main___lam__2___closed__2));
v___x_603_ = lean_string_append(v___x_601_, v___x_602_);
v_a_554_ = v___x_603_;
goto v___jp_553_;
}
}
}
}
}
v___jp_608_:
{
lean_object* v___x_610_; lean_object* v_env_611_; lean_object* v_nextMacroScope_612_; lean_object* v_ngen_613_; lean_object* v_auxDeclNGen_614_; lean_object* v_traceState_615_; lean_object* v_recordedDeps_616_; lean_object* v_messages_617_; lean_object* v_infoState_618_; lean_object* v_snapshotTasks_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_628_; 
v___x_610_ = lean_st_ref_take(v___x_558_);
v_env_611_ = lean_ctor_get(v___x_610_, 0);
v_nextMacroScope_612_ = lean_ctor_get(v___x_610_, 1);
v_ngen_613_ = lean_ctor_get(v___x_610_, 2);
v_auxDeclNGen_614_ = lean_ctor_get(v___x_610_, 3);
v_traceState_615_ = lean_ctor_get(v___x_610_, 4);
v_recordedDeps_616_ = lean_ctor_get(v___x_610_, 6);
v_messages_617_ = lean_ctor_get(v___x_610_, 7);
v_infoState_618_ = lean_ctor_get(v___x_610_, 8);
v_snapshotTasks_619_ = lean_ctor_get(v___x_610_, 9);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_628_ == 0)
{
lean_object* v_unused_629_; 
v_unused_629_ = lean_ctor_get(v___x_610_, 5);
lean_dec(v_unused_629_);
v___x_621_ = v___x_610_;
v_isShared_622_ = v_isSharedCheck_628_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_snapshotTasks_619_);
lean_inc(v_infoState_618_);
lean_inc(v_messages_617_);
lean_inc(v_recordedDeps_616_);
lean_inc(v_traceState_615_);
lean_inc(v_auxDeclNGen_614_);
lean_inc(v_ngen_613_);
lean_inc(v_nextMacroScope_612_);
lean_inc(v_env_611_);
lean_dec(v___x_610_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_628_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_623_ = l_Lean_Kernel_enableDiag(v_env_611_, v___y_609_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 5, v___x_540_);
lean_ctor_set(v___x_621_, 0, v___x_623_);
v___x_625_ = v___x_621_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_nextMacroScope_612_);
lean_ctor_set(v_reuseFailAlloc_627_, 2, v_ngen_613_);
lean_ctor_set(v_reuseFailAlloc_627_, 3, v_auxDeclNGen_614_);
lean_ctor_set(v_reuseFailAlloc_627_, 4, v_traceState_615_);
lean_ctor_set(v_reuseFailAlloc_627_, 5, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_627_, 6, v_recordedDeps_616_);
lean_ctor_set(v_reuseFailAlloc_627_, 7, v_messages_617_);
lean_ctor_set(v_reuseFailAlloc_627_, 8, v_infoState_618_);
lean_ctor_set(v_reuseFailAlloc_627_, 9, v_snapshotTasks_619_);
v___x_625_ = v_reuseFailAlloc_627_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_626_; 
v___x_626_ = lean_st_ref_put(v___x_558_, v___x_625_);
lean_inc(v___x_543_);
v_fileName_560_ = v_head_541_;
v_fileMap_561_ = v___x_542_;
v_currNamespace_562_ = v___x_543_;
v_openDecls_563_ = v___x_544_;
v_initHeartbeats_564_ = v___x_557_;
v_maxHeartbeats_565_ = v___x_545_;
v_quotContext_566_ = v___x_543_;
v_currMacroScope_567_ = v___x_546_;
v_cancelTk_x3f_568_ = v___x_547_;
v_inheritedTraceOptions_569_ = v___x_606_;
v_currRecDepth_570_ = v___x_548_;
v_ref_571_ = v___x_549_;
v_suppressElabErrors_572_ = v___x_550_;
v_isRecordingDeps_573_ = v___x_550_;
goto v___jp_559_;
}
}
}
v___jp_630_:
{
if (v___y_632_ == 0)
{
v___y_609_ = v___y_631_;
goto v___jp_608_;
}
else
{
lean_dec_ref(v___x_540_);
lean_inc(v___x_543_);
v_fileName_560_ = v_head_541_;
v_fileMap_561_ = v___x_542_;
v_currNamespace_562_ = v___x_543_;
v_openDecls_563_ = v___x_544_;
v_initHeartbeats_564_ = v___x_557_;
v_maxHeartbeats_565_ = v___x_545_;
v_quotContext_566_ = v___x_543_;
v_currMacroScope_567_ = v___x_546_;
v_cancelTk_x3f_568_ = v___x_547_;
v_inheritedTraceOptions_569_ = v___x_606_;
v_currRecDepth_570_ = v___x_548_;
v_ref_571_ = v___x_549_;
v_suppressElabErrors_572_ = v___x_550_;
v_isRecordingDeps_573_ = v___x_550_;
goto v___jp_559_;
}
}
v___jp_635_:
{
if (v___y_636_ == 0)
{
if (v___x_634_ == 0)
{
v___y_631_ = v___y_636_;
v___y_632_ = v___x_539_;
goto v___jp_630_;
}
else
{
v___y_609_ = v___y_636_;
goto v___jp_608_;
}
}
else
{
v___y_631_ = v___y_636_;
v___y_632_ = v___x_634_;
goto v___jp_630_;
}
}
}
}
LEAN_EXPORT void l_main___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_534_ = stack[0].m_obj;
lean_object* v___x_535_ = stack[1].m_obj;
uint16_t v___x_536_ = stack[2].m_num;
lean_object* v_name_537_ = stack[3].m_obj;
lean_object* v_a_538_ = stack[4].m_obj;
uint8_t v___x_539_ = stack[5].m_num;
lean_object* v___x_540_ = stack[6].m_obj;
lean_object* v_head_541_ = stack[7].m_obj;
lean_object* v___x_542_ = stack[8].m_obj;
lean_object* v___x_543_ = stack[9].m_obj;
lean_object* v___x_544_ = stack[10].m_obj;
lean_object* v___x_545_ = stack[11].m_obj;
lean_object* v___x_546_ = stack[12].m_obj;
lean_object* v___x_547_ = stack[13].m_obj;
lean_object* v___x_548_ = stack[14].m_obj;
lean_object* v___x_549_ = stack[15].m_obj;
uint8_t v___x_550_ = stack[16].m_num;
uint8_t v___x_551_ = stack[17].m_num;
lean_object* v_res_641_;
v_res_641_ = l_main___lam__2(v___x_534_, v___x_535_, v___x_536_, v_name_537_, v_a_538_, v___x_539_, v___x_540_, v_head_541_, v___x_542_, v___x_543_, v___x_544_, v___x_545_, v___x_546_, v___x_547_, v___x_548_, v___x_549_, v___x_550_, v___x_551_);
stack->m_obj
 = v_res_641_;
}
LEAN_EXPORT lean_object* l_main___lam__2___boxed(lean_object** _args){
lean_object* v___x_642_ = _args[0];
lean_object* v___x_643_ = _args[1];
lean_object* v___x_644_ = _args[2];
lean_object* v_name_645_ = _args[3];
lean_object* v_a_646_ = _args[4];
lean_object* v___x_647_ = _args[5];
lean_object* v___x_648_ = _args[6];
lean_object* v_head_649_ = _args[7];
lean_object* v___x_650_ = _args[8];
lean_object* v___x_651_ = _args[9];
lean_object* v___x_652_ = _args[10];
lean_object* v___x_653_ = _args[11];
lean_object* v___x_654_ = _args[12];
lean_object* v___x_655_ = _args[13];
lean_object* v___x_656_ = _args[14];
lean_object* v___x_657_ = _args[15];
lean_object* v___x_658_ = _args[16];
lean_object* v___x_659_ = _args[17];
lean_object* v___y_660_ = _args[18];
_start:
{
uint16_t v___x_37488__boxed_661_; uint8_t v___x_37490__boxed_662_; uint8_t v___x_37501__boxed_663_; uint8_t v___x_37502__boxed_664_; lean_object* v_res_665_; 
v___x_37488__boxed_661_ = lean_unbox(v___x_644_);
v___x_37490__boxed_662_ = lean_unbox(v___x_647_);
v___x_37501__boxed_663_ = lean_unbox(v___x_658_);
v___x_37502__boxed_664_ = lean_unbox(v___x_659_);
v_res_665_ = l_main___lam__2(v___x_642_, v___x_643_, v___x_37488__boxed_661_, v_name_645_, v_a_646_, v___x_37490__boxed_662_, v___x_648_, v_head_649_, v___x_650_, v___x_651_, v___x_652_, v___x_653_, v___x_654_, v___x_655_, v___x_656_, v___x_657_, v___x_37501__boxed_663_, v___x_37502__boxed_664_);
lean_dec(v_a_646_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_main___lam__3(lean_object* v___x_666_, lean_object* v_x_667_){
_start:
{
lean_inc_ref(v___x_666_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_main___lam__3___boxed(lean_object* v___x_668_, lean_object* v_x_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_main___lam__3(v___x_668_, v_x_669_);
lean_dec_ref(v_x_669_);
lean_dec_ref(v___x_668_);
return v_res_670_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(lean_object* v_x2_671_, lean_object* v_as_672_, size_t v_i_673_, size_t v_stop_674_, lean_object* v_b_675_){
_start:
{
uint8_t v___x_676_; 
v___x_676_ = lean_usize_dec_eq(v_i_673_, v_stop_674_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; lean_object* v___x_678_; size_t v___x_679_; size_t v___x_680_; 
v___x_677_ = lean_array_uget_borrowed(v_as_672_, v_i_673_);
lean_inc_ref(v_x2_671_);
lean_inc(v___x_677_);
v___x_678_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_677_, v_x2_671_, v_b_675_);
v___x_679_ = ((size_t)1ULL);
v___x_680_ = lean_usize_add(v_i_673_, v___x_679_);
v_i_673_ = v___x_680_;
v_b_675_ = v___x_678_;
goto _start;
}
else
{
lean_dec_ref(v_x2_671_);
return v_b_675_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x2_671_ = stack[0].m_obj;
lean_object* v_as_672_ = stack[1].m_obj;
size_t v_i_673_ = stack[2].m_num;
size_t v_stop_674_ = stack[3].m_num;
lean_object* v_b_675_ = stack[4].m_obj;
lean_object* v_res_682_;
v_res_682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v_x2_671_, v_as_672_, v_i_673_, v_stop_674_, v_b_675_);
stack->m_obj
 = v_res_682_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(lean_object* v_x2_683_, lean_object* v_as_684_, lean_object* v_i_685_, lean_object* v_stop_686_, lean_object* v_b_687_){
_start:
{
size_t v_i_boxed_688_; size_t v_stop_boxed_689_; lean_object* v_res_690_; 
v_i_boxed_688_ = lean_unbox_usize(v_i_685_);
lean_dec(v_i_685_);
v_stop_boxed_689_ = lean_unbox_usize(v_stop_686_);
lean_dec(v_stop_686_);
v_res_690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v_x2_683_, v_as_684_, v_i_boxed_688_, v_stop_boxed_689_, v_b_687_);
lean_dec_ref(v_as_684_);
return v_res_690_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(lean_object* v_as_691_, size_t v_i_692_, size_t v_stop_693_, lean_object* v_b_694_){
_start:
{
lean_object* v___y_696_; uint8_t v___x_700_; 
v___x_700_ = lean_usize_dec_eq(v_i_692_, v_stop_693_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; lean_object* v_declNames_702_; lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v___x_701_ = lean_array_uget_borrowed(v_as_691_, v_i_692_);
v_declNames_702_ = lean_ctor_get(v___x_701_, 0);
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = lean_array_get_size(v_declNames_702_);
v___x_705_ = lean_nat_dec_lt(v___x_703_, v___x_704_);
if (v___x_705_ == 0)
{
v___y_696_ = v_b_694_;
goto v___jp_695_;
}
else
{
uint8_t v___x_706_; 
v___x_706_ = lean_nat_dec_le(v___x_704_, v___x_704_);
if (v___x_706_ == 0)
{
if (v___x_705_ == 0)
{
v___y_696_ = v_b_694_;
goto v___jp_695_;
}
else
{
size_t v___x_707_; size_t v___x_708_; lean_object* v___x_709_; 
v___x_707_ = ((size_t)0ULL);
v___x_708_ = lean_usize_of_nat(v___x_704_);
lean_inc(v___x_701_);
v___x_709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_701_, v_declNames_702_, v___x_707_, v___x_708_, v_b_694_);
v___y_696_ = v___x_709_;
goto v___jp_695_;
}
}
else
{
size_t v___x_710_; size_t v___x_711_; lean_object* v___x_712_; 
v___x_710_ = ((size_t)0ULL);
v___x_711_ = lean_usize_of_nat(v___x_704_);
lean_inc(v___x_701_);
v___x_712_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_701_, v_declNames_702_, v___x_710_, v___x_711_, v_b_694_);
v___y_696_ = v___x_712_;
goto v___jp_695_;
}
}
}
else
{
return v_b_694_;
}
v___jp_695_:
{
size_t v___x_697_; size_t v___x_698_; 
v___x_697_ = ((size_t)1ULL);
v___x_698_ = lean_usize_add(v_i_692_, v___x_697_);
v_i_692_ = v___x_698_;
v_b_694_ = v___y_696_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_691_ = stack[0].m_obj;
size_t v_i_692_ = stack[1].m_num;
size_t v_stop_693_ = stack[2].m_num;
lean_object* v_b_694_ = stack[3].m_obj;
lean_object* v_res_713_;
v_res_713_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v_as_691_, v_i_692_, v_stop_693_, v_b_694_);
stack->m_obj
 = v_res_713_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14___boxed(lean_object* v_as_714_, lean_object* v_i_715_, lean_object* v_stop_716_, lean_object* v_b_717_){
_start:
{
size_t v_i_boxed_718_; size_t v_stop_boxed_719_; lean_object* v_res_720_; 
v_i_boxed_718_ = lean_unbox_usize(v_i_715_);
lean_dec(v_i_715_);
v_stop_boxed_719_ = lean_unbox_usize(v_stop_716_);
lean_dec(v_stop_716_);
v_res_720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v_as_714_, v_i_boxed_718_, v_stop_boxed_719_, v_b_717_);
lean_dec_ref(v_as_714_);
return v_res_720_;
}
}
lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(lean_object* v_s_721_){
_start:
{
lean_object* v___x_723_; lean_object* v_putStr_724_; lean_object* v___x_725_; 
v___x_723_ = lean_get_stderr();
v_putStr_724_ = lean_ctor_get(v___x_723_, 4);
lean_inc_ref(v_putStr_724_);
lean_dec_ref(v___x_723_);
v___x_725_ = lean_apply_2(v_putStr_724_, v_s_721_, lean_box(0));
return v___x_725_;
}
}
LEAN_EXPORT void l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_721_ = stack[0].m_obj;
lean_object* v_res_726_;
v_res_726_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v_s_721_);
stack->m_obj
 = v_res_726_;
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8___boxed(lean_object* v_s_727_, lean_object* v_a_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v_s_727_);
return v_res_729_;
}
}
lean_object* l_IO_eprintln___at___00main_spec__6(lean_object* v_s_730_){
_start:
{
uint32_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_732_ = 10;
v___x_733_ = lean_string_push(v_s_730_, v___x_732_);
v___x_734_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT void l_IO_eprintln___at___00main_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_730_ = stack[0].m_obj;
lean_object* v_res_735_;
v_res_735_ = l_IO_eprintln___at___00main_spec__6(v_s_730_);
stack->m_obj
 = v_res_735_;
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6___boxed(lean_object* v_s_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_IO_eprintln___at___00main_spec__6(v_s_736_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(lean_object* v_o_742_, lean_object* v_k_743_, lean_object* v_v_744_){
_start:
{
lean_object* v_map_745_; uint8_t v_hasTrace_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_760_; 
v_map_745_ = lean_ctor_get(v_o_742_, 0);
v_hasTrace_746_ = lean_ctor_get_uint8(v_o_742_, sizeof(void*)*1);
v_isSharedCheck_760_ = !lean_is_exclusive(v_o_742_);
if (v_isSharedCheck_760_ == 0)
{
v___x_748_ = v_o_742_;
v_isShared_749_ = v_isSharedCheck_760_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_map_745_);
lean_dec(v_o_742_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_760_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_750_, 0, v_v_744_);
lean_inc(v_k_743_);
v___x_751_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_743_, v___x_750_, v_map_745_);
if (v_hasTrace_746_ == 0)
{
lean_object* v___x_752_; uint8_t v___x_753_; lean_object* v___x_755_; 
v___x_752_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_753_ = l_Lean_Name_isPrefixOf(v___x_752_, v_k_743_);
lean_dec(v_k_743_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v___x_751_);
v___x_755_ = v___x_748_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_751_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_ctor_set_uint8(v___x_755_, sizeof(void*)*1, v___x_753_);
return v___x_755_;
}
}
else
{
lean_object* v___x_758_; 
lean_dec(v_k_743_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v___x_751_);
v___x_758_ = v___x_748_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_751_);
lean_ctor_set_uint8(v_reuseFailAlloc_759_, sizeof(void*)*1, v_hasTrace_746_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00main_spec__3(lean_object* v_opts_761_, lean_object* v_opt_762_, lean_object* v_val_763_){
_start:
{
lean_object* v_name_764_; lean_object* v___x_765_; 
v_name_764_ = lean_ctor_get(v_opt_762_, 0);
lean_inc(v_name_764_);
lean_dec_ref(v_opt_762_);
v___x_765_ = l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(v_opts_761_, v_name_764_, v_val_763_);
return v___x_765_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object* v_as_766_, size_t v_i_767_, size_t v_stop_768_, lean_object* v_b_769_){
_start:
{
uint8_t v___x_770_; 
v___x_770_ = lean_usize_dec_eq(v_i_767_, v_stop_768_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; lean_object* v_name_772_; lean_object* v___x_773_; size_t v___x_774_; size_t v___x_775_; 
v___x_771_ = lean_array_uget_borrowed(v_as_766_, v_i_767_);
v_name_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_name_772_);
v___x_773_ = l_Lean_Compiler_LCNF_setDeclPublic(v_b_769_, v_name_772_);
v___x_774_ = ((size_t)1ULL);
v___x_775_ = lean_usize_add(v_i_767_, v___x_774_);
v_i_767_ = v___x_775_;
v_b_769_ = v___x_773_;
goto _start;
}
else
{
return v_b_769_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_766_ = stack[0].m_obj;
size_t v_i_767_ = stack[1].m_num;
size_t v_stop_768_ = stack[2].m_num;
lean_object* v_b_769_ = stack[3].m_obj;
lean_object* v_res_777_;
v_res_777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v_as_766_, v_i_767_, v_stop_768_, v_b_769_);
stack->m_obj
 = v_res_777_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object* v_as_778_, lean_object* v_i_779_, lean_object* v_stop_780_, lean_object* v_b_781_){
_start:
{
size_t v_i_boxed_782_; size_t v_stop_boxed_783_; lean_object* v_res_784_; 
v_i_boxed_782_ = lean_unbox_usize(v_i_779_);
lean_dec(v_i_779_);
v_stop_boxed_783_ = lean_unbox_usize(v_stop_780_);
lean_dec(v_stop_780_);
v_res_784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v_as_778_, v_i_boxed_782_, v_stop_boxed_783_, v_b_781_);
lean_dec_ref(v_as_778_);
return v_res_784_;
}
}
lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg(lean_object* v_as_x27_786_, lean_object* v_b_787_){
_start:
{
if (lean_obj_tag(v_as_x27_786_) == 0)
{
lean_object* v___x_789_; 
v___x_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_789_, 0, v_b_787_);
return v___x_789_;
}
else
{
lean_object* v_head_790_; lean_object* v_tail_791_; lean_object* v_fst_792_; lean_object* v_snd_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_818_; 
v_head_790_ = lean_ctor_get(v_as_x27_786_, 0);
v_tail_791_ = lean_ctor_get(v_as_x27_786_, 1);
v_fst_792_ = lean_ctor_get(v_b_787_, 0);
v_snd_793_ = lean_ctor_get(v_b_787_, 1);
v_isSharedCheck_818_ = !lean_is_exclusive(v_b_787_);
if (v_isSharedCheck_818_ == 0)
{
v___x_795_ = v_b_787_;
v_isShared_796_ = v_isSharedCheck_818_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_snd_793_);
lean_inc(v_fst_792_);
lean_dec(v_b_787_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_818_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; uint8_t v___x_798_; 
v___x_797_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0));
v___x_798_ = lean_string_dec_eq(v_head_790_, v___x_797_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; 
lean_inc(v_head_790_);
v___x_799_ = l___private_LeanIR_0__setConfigOption(v_snd_793_, v_head_790_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_802_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
lean_dec_ref_known(v___x_799_, 1);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v_a_800_);
v___x_802_ = v___x_795_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_fst_792_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_a_800_);
v___x_802_ = v_reuseFailAlloc_804_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
v_as_x27_786_ = v_tail_791_;
v_b_787_ = v___x_802_;
goto _start;
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_del_object(v___x_795_);
lean_dec(v_fst_792_);
v_a_805_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_799_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_799_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
else
{
lean_object* v___x_813_; lean_object* v___x_815_; 
lean_dec(v_fst_792_);
v___x_813_ = lean_box(v___x_798_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_813_);
v___x_815_ = v___x_795_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_snd_793_);
v___x_815_ = v_reuseFailAlloc_817_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
v_as_x27_786_ = v_tail_791_;
v_b_787_ = v___x_815_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00main_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_786_ = stack[0].m_obj;
lean_object* v_b_787_ = stack[1].m_obj;
lean_object* v_res_819_;
v_res_819_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_786_, v_b_787_);
stack->m_obj
 = v_res_819_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(lean_object* v_as_x27_820_, lean_object* v_b_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_820_, v_b_821_);
lean_dec(v_as_x27_820_);
return v_res_823_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object* v_a_824_, lean_object* v_as_825_, size_t v_i_826_, size_t v_stop_827_, lean_object* v_b_828_){
_start:
{
lean_object* v___y_830_; uint8_t v___x_834_; 
v___x_834_ = lean_usize_dec_eq(v_i_826_, v_stop_827_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; lean_object* v_name_836_; uint8_t v___x_837_; 
v___x_835_ = lean_array_uget_borrowed(v_as_825_, v_i_826_);
v_name_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_name_836_);
lean_inc_ref(v_a_824_);
v___x_837_ = l_Lean_isExtern(v_a_824_, v_name_836_);
if (v___x_837_ == 0)
{
v___y_830_ = v_b_828_;
goto v___jp_829_;
}
else
{
lean_object* v___x_838_; 
lean_inc(v___x_835_);
v___x_838_ = lean_array_push(v_b_828_, v___x_835_);
v___y_830_ = v___x_838_;
goto v___jp_829_;
}
}
else
{
lean_dec_ref(v_a_824_);
return v_b_828_;
}
v___jp_829_:
{
size_t v___x_831_; size_t v___x_832_; 
v___x_831_ = ((size_t)1ULL);
v___x_832_ = lean_usize_add(v_i_826_, v___x_831_);
v_i_826_ = v___x_832_;
v_b_828_ = v___y_830_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_824_ = stack[0].m_obj;
lean_object* v_as_825_ = stack[1].m_obj;
size_t v_i_826_ = stack[2].m_num;
size_t v_stop_827_ = stack[3].m_num;
lean_object* v_b_828_ = stack[4].m_obj;
lean_object* v_res_839_;
v_res_839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_824_, v_as_825_, v_i_826_, v_stop_827_, v_b_828_);
stack->m_obj
 = v_res_839_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object* v_a_840_, lean_object* v_as_841_, lean_object* v_i_842_, lean_object* v_stop_843_, lean_object* v_b_844_){
_start:
{
size_t v_i_boxed_845_; size_t v_stop_boxed_846_; lean_object* v_res_847_; 
v_i_boxed_845_ = lean_unbox_usize(v_i_842_);
lean_dec(v_i_842_);
v_stop_boxed_846_ = lean_unbox_usize(v_stop_843_);
lean_dec(v_stop_843_);
v_res_847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_840_, v_as_841_, v_i_boxed_845_, v_stop_boxed_846_, v_b_844_);
lean_dec_ref(v_as_841_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___lam__0(lean_object* v___x_848_, lean_object* v___x_849_, lean_object* v_s_850_){
_start:
{
lean_object* v_addEntryFn_851_; lean_object* v_importedEntries_852_; lean_object* v_state_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_861_; 
v_addEntryFn_851_ = lean_ctor_get(v___x_848_, 3);
lean_inc(v_addEntryFn_851_);
lean_dec_ref(v___x_848_);
v_importedEntries_852_ = lean_ctor_get(v_s_850_, 0);
v_state_853_ = lean_ctor_get(v_s_850_, 1);
v_isSharedCheck_861_ = !lean_is_exclusive(v_s_850_);
if (v_isSharedCheck_861_ == 0)
{
v___x_855_ = v_s_850_;
v_isShared_856_ = v_isSharedCheck_861_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_state_853_);
lean_inc(v_importedEntries_852_);
lean_dec(v_s_850_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_861_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v_state_857_; lean_object* v___x_859_; 
v_state_857_ = lean_apply_2(v_addEntryFn_851_, v_state_853_, v___x_849_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 1, v_state_857_);
v___x_859_ = v___x_855_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_importedEntries_852_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v_state_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object* v_as_862_, size_t v_i_863_, size_t v_stop_864_, lean_object* v_b_865_){
_start:
{
lean_object* v___y_867_; uint8_t v___x_871_; 
v___x_871_ = lean_usize_dec_eq(v_i_863_, v_stop_864_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; lean_object* v_toEnvExtension_873_; lean_object* v_asyncMode_874_; uint8_t v_logWrites_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___f_878_; uint8_t v___x_879_; 
v___x_872_ = l_Lean_Compiler_LCNF_impureSigExt;
v_toEnvExtension_873_ = lean_ctor_get(v___x_872_, 0);
v_asyncMode_874_ = lean_ctor_get(v_toEnvExtension_873_, 2);
v_logWrites_875_ = lean_ctor_get_uint8(v_toEnvExtension_873_, sizeof(void*)*6);
v___x_876_ = lean_box(0);
v___x_877_ = lean_array_uget_borrowed(v_as_862_, v_i_863_);
lean_inc(v___x_877_);
v___f_878_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___lam__0), 3, 2);
lean_closure_set(v___f_878_, 0, v___x_872_);
lean_closure_set(v___f_878_, 1, v___x_877_);
v___x_879_ = 1;
if (v_logWrites_875_ == 0)
{
lean_object* v___x_880_; 
lean_inc_ref(v_toEnvExtension_873_);
v___x_880_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_873_, v_b_865_, v___f_878_, v_asyncMode_874_, v___x_876_, v___x_879_);
v___y_867_ = v___x_880_;
goto v___jp_866_;
}
else
{
lean_object* v___x_881_; lean_object* v___x_882_; 
lean_inc_ref_n(v_toEnvExtension_873_, 2);
v___x_881_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite___redArg(v_toEnvExtension_873_, v_b_865_);
lean_dec_ref(v_b_865_);
v___x_882_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_873_, v___x_881_, v___f_878_, v_asyncMode_874_, v___x_876_, v___x_879_);
v___y_867_ = v___x_882_;
goto v___jp_866_;
}
}
else
{
return v_b_865_;
}
v___jp_866_:
{
size_t v___x_868_; size_t v___x_869_; 
v___x_868_ = ((size_t)1ULL);
v___x_869_ = lean_usize_add(v_i_863_, v___x_868_);
v_i_863_ = v___x_869_;
v_b_865_ = v___y_867_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_862_ = stack[0].m_obj;
size_t v_i_863_ = stack[1].m_num;
size_t v_stop_864_ = stack[2].m_num;
lean_object* v_b_865_ = stack[3].m_obj;
lean_object* v_res_883_;
v_res_883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v_as_862_, v_i_863_, v_stop_864_, v_b_865_);
stack->m_obj
 = v_res_883_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object* v_as_884_, lean_object* v_i_885_, lean_object* v_stop_886_, lean_object* v_b_887_){
_start:
{
size_t v_i_boxed_888_; size_t v_stop_boxed_889_; lean_object* v_res_890_; 
v_i_boxed_888_ = lean_unbox_usize(v_i_885_);
lean_dec(v_i_885_);
v_stop_boxed_889_ = lean_unbox_usize(v_stop_886_);
lean_dec(v_stop_886_);
v_res_890_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v_as_884_, v_i_boxed_888_, v_stop_boxed_889_, v_b_887_);
lean_dec_ref(v_as_884_);
return v_res_890_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object* v___y_892_, lean_object* v_as_893_, size_t v_i_894_, size_t v_stop_895_, lean_object* v_b_896_){
_start:
{
lean_object* v___y_898_; uint8_t v___x_902_; 
v___x_902_ = lean_usize_dec_eq(v_i_894_, v_stop_895_);
if (v___x_902_ == 0)
{
lean_object* v_fst_903_; lean_object* v_snd_904_; lean_object* v___x_905_; lean_object* v_name_906_; lean_object* v_code_907_; lean_object* v_stackReserved_908_; lean_object* v_stackSpace_909_; lean_object* v_symbols_910_; lean_object* v_arity_911_; lean_object* v_constants_912_; lean_object* v_sorryDep_x3f_913_; lean_object* v___y_915_; 
v_fst_903_ = lean_ctor_get(v_b_896_, 0);
v_snd_904_ = lean_ctor_get(v_b_896_, 1);
v___x_905_ = lean_array_uget_borrowed(v_as_893_, v_i_894_);
v_name_906_ = lean_ctor_get(v___x_905_, 0);
v_code_907_ = lean_ctor_get(v___x_905_, 1);
v_stackReserved_908_ = lean_ctor_get(v___x_905_, 2);
v_stackSpace_909_ = lean_ctor_get(v___x_905_, 3);
v_symbols_910_ = lean_ctor_get(v___x_905_, 4);
v_arity_911_ = lean_ctor_get(v___x_905_, 6);
v_constants_912_ = lean_ctor_get(v___x_905_, 7);
v_sorryDep_x3f_913_ = lean_ctor_get(v___x_905_, 8);
if (lean_obj_tag(v_name_906_) == 1)
{
lean_object* v_pre_930_; lean_object* v_str_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v_pre_930_ = lean_ctor_get(v_name_906_, 0);
v_str_931_ = lean_ctor_get(v_name_906_, 1);
v___x_932_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___closed__0));
v___x_933_ = lean_string_dec_eq(v_str_931_, v___x_932_);
if (v___x_933_ == 0)
{
lean_inc_ref(v_name_906_);
v___y_915_ = v_name_906_;
goto v___jp_914_;
}
else
{
lean_inc(v_pre_930_);
v___y_915_ = v_pre_930_;
goto v___jp_914_;
}
}
else
{
lean_inc(v_name_906_);
v___y_915_ = v_name_906_;
goto v___jp_914_;
}
v___jp_914_:
{
uint8_t v___x_916_; 
lean_inc_ref(v___y_892_);
v___x_916_ = l_Lean_isExtern(v___y_892_, v___y_915_);
if (v___x_916_ == 0)
{
v___y_898_ = v_b_896_;
goto v___jp_897_;
}
else
{
lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_927_; 
lean_inc(v_snd_904_);
lean_inc(v_fst_903_);
v_isSharedCheck_927_ = !lean_is_exclusive(v_b_896_);
if (v_isSharedCheck_927_ == 0)
{
lean_object* v_unused_928_; lean_object* v_unused_929_; 
v_unused_928_ = lean_ctor_get(v_b_896_, 1);
lean_dec(v_unused_928_);
v_unused_929_ = lean_ctor_get(v_b_896_, 0);
lean_dec(v_unused_929_);
v___x_918_ = v_b_896_;
v_isShared_919_ = v_isSharedCheck_927_;
goto v_resetjp_917_;
}
else
{
lean_dec(v_b_896_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_927_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_925_; 
lean_inc(v___x_905_);
v___x_920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_905_);
lean_ctor_set(v___x_920_, 1, v_fst_903_);
v___x_921_ = lean_bytecode_mk_initial_cache(v_symbols_910_);
lean_inc(v_sorryDep_x3f_913_);
lean_inc_ref(v_constants_912_);
lean_inc(v_arity_911_);
lean_inc_ref(v_symbols_910_);
lean_inc(v_stackSpace_909_);
lean_inc(v_stackReserved_908_);
lean_inc_ref(v_code_907_);
lean_inc_n(v_name_906_, 2);
v___x_922_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_922_, 0, v_name_906_);
lean_ctor_set(v___x_922_, 1, v_code_907_);
lean_ctor_set(v___x_922_, 2, v_stackReserved_908_);
lean_ctor_set(v___x_922_, 3, v_stackSpace_909_);
lean_ctor_set(v___x_922_, 4, v_symbols_910_);
lean_ctor_set(v___x_922_, 5, v___x_921_);
lean_ctor_set(v___x_922_, 6, v_arity_911_);
lean_ctor_set(v___x_922_, 7, v_constants_912_);
lean_ctor_set(v___x_922_, 8, v_sorryDep_x3f_913_);
v___x_923_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_904_, v_name_906_, v___x_922_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 1, v___x_923_);
lean_ctor_set(v___x_918_, 0, v___x_920_);
v___x_925_ = v___x_918_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_920_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
v___y_898_ = v___x_925_;
goto v___jp_897_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_892_);
return v_b_896_;
}
v___jp_897_:
{
size_t v___x_899_; size_t v___x_900_; 
v___x_899_ = ((size_t)1ULL);
v___x_900_ = lean_usize_add(v_i_894_, v___x_899_);
v_i_894_ = v___x_900_;
v_b_896_ = v___y_898_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_892_ = stack[0].m_obj;
lean_object* v_as_893_ = stack[1].m_obj;
size_t v_i_894_ = stack[2].m_num;
size_t v_stop_895_ = stack[3].m_num;
lean_object* v_b_896_ = stack[4].m_obj;
lean_object* v_res_934_;
v_res_934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_892_, v_as_893_, v_i_894_, v_stop_895_, v_b_896_);
stack->m_obj
 = v_res_934_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object* v___y_935_, lean_object* v_as_936_, lean_object* v_i_937_, lean_object* v_stop_938_, lean_object* v_b_939_){
_start:
{
size_t v_i_boxed_940_; size_t v_stop_boxed_941_; lean_object* v_res_942_; 
v_i_boxed_940_ = lean_unbox_usize(v_i_937_);
lean_dec(v_i_937_);
v_stop_boxed_941_ = lean_unbox_usize(v_stop_938_);
lean_dec(v_stop_938_);
v_res_942_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_935_, v_as_936_, v_i_boxed_940_, v_stop_boxed_941_, v_b_939_);
lean_dec_ref(v_as_936_);
return v_res_942_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27(lean_object* v_as_946_, size_t v_sz_947_, size_t v_i_948_, lean_object* v_b_949_){
_start:
{
uint8_t v___x_951_; 
v___x_951_ = lean_usize_dec_lt(v_i_948_, v_sz_947_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; 
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v_b_949_);
return v___x_952_;
}
else
{
uint8_t v___x_953_; lean_object* v_a_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
lean_dec_ref(v_b_949_);
v___x_953_ = 0;
v_a_954_ = lean_array_uget_borrowed(v_as_946_, v_i_948_);
lean_inc(v_a_954_);
v___x_955_ = l_Lean_Message_toString(v_a_954_, v___x_953_);
v___x_956_ = l_IO_eprintln___at___00main_spec__6(v___x_955_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v___x_957_; size_t v___x_958_; size_t v___x_959_; 
lean_dec_ref_known(v___x_956_, 1);
v___x_957_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_958_ = ((size_t)1ULL);
v___x_959_ = lean_usize_add(v_i_948_, v___x_958_);
v_i_948_ = v___x_959_;
v_b_949_ = v___x_957_;
goto _start;
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
v_a_961_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_956_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_956_);
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
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_946_ = stack[0].m_obj;
size_t v_sz_947_ = stack[1].m_num;
size_t v_i_948_ = stack[2].m_num;
lean_object* v_b_949_ = stack[3].m_obj;
lean_object* v_res_969_;
v_res_969_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27(v_as_946_, v_sz_947_, v_i_948_, v_b_949_);
stack->m_obj
 = v_res_969_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___boxed(lean_object* v_as_970_, lean_object* v_sz_971_, lean_object* v_i_972_, lean_object* v_b_973_, lean_object* v___y_974_){
_start:
{
size_t v_sz_boxed_975_; size_t v_i_boxed_976_; lean_object* v_res_977_; 
v_sz_boxed_975_ = lean_unbox_usize(v_sz_971_);
lean_dec(v_sz_971_);
v_i_boxed_976_ = lean_unbox_usize(v_i_972_);
lean_dec(v_i_972_);
v_res_977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27(v_as_970_, v_sz_boxed_975_, v_i_boxed_976_, v_b_973_);
lean_dec_ref(v_as_970_);
return v_res_977_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(lean_object* v_as_978_, size_t v_sz_979_, size_t v_i_980_, lean_object* v_b_981_){
_start:
{
uint8_t v___x_983_; 
v___x_983_ = lean_usize_dec_lt(v_i_980_, v_sz_979_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; 
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v_b_981_);
return v___x_984_;
}
else
{
uint8_t v___x_985_; lean_object* v_a_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
lean_dec_ref(v_b_981_);
v___x_985_ = 0;
v_a_986_ = lean_array_uget_borrowed(v_as_978_, v_i_980_);
lean_inc(v_a_986_);
v___x_987_ = l_Lean_Message_toString(v_a_986_, v___x_985_);
v___x_988_ = l_IO_eprintln___at___00main_spec__6(v___x_987_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v___x_989_; size_t v___x_990_; size_t v___x_991_; lean_object* v___x_992_; 
lean_dec_ref_known(v___x_988_, 1);
v___x_989_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_990_ = ((size_t)1ULL);
v___x_991_ = lean_usize_add(v_i_980_, v___x_990_);
v___x_992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27(v_as_978_, v_sz_979_, v___x_991_, v___x_989_);
return v___x_992_;
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
v_a_993_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_988_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_988_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
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
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_978_ = stack[0].m_obj;
size_t v_sz_979_ = stack[1].m_num;
size_t v_i_980_ = stack[2].m_num;
lean_object* v_b_981_ = stack[3].m_obj;
lean_object* v_res_1001_;
v_res_1001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_as_978_, v_sz_979_, v_i_980_, v_b_981_);
stack->m_obj
 = v_res_1001_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13___boxed(lean_object* v_as_1002_, lean_object* v_sz_1003_, lean_object* v_i_1004_, lean_object* v_b_1005_, lean_object* v___y_1006_){
_start:
{
size_t v_sz_boxed_1007_; size_t v_i_boxed_1008_; lean_object* v_res_1009_; 
v_sz_boxed_1007_ = lean_unbox_usize(v_sz_1003_);
lean_dec(v_sz_1003_);
v_i_boxed_1008_ = lean_unbox_usize(v_i_1004_);
lean_dec(v_i_1004_);
v_res_1009_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_as_1002_, v_sz_boxed_1007_, v_i_boxed_1008_, v_b_1005_);
lean_dec_ref(v_as_1002_);
return v_res_1009_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(lean_object* v_init_1010_, lean_object* v_n_1011_, lean_object* v_b_1012_){
_start:
{
if (lean_obj_tag(v_n_1011_) == 0)
{
lean_object* v_cs_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; size_t v_sz_1017_; size_t v___x_1018_; lean_object* v___x_1019_; 
v_cs_1014_ = lean_ctor_get(v_n_1011_, 0);
v___x_1015_ = lean_box(0);
v___x_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v_b_1012_);
v_sz_1017_ = lean_array_size(v_cs_1014_);
v___x_1018_ = ((size_t)0ULL);
v___x_1019_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12(v_init_1010_, v_cs_1014_, v_sz_1017_, v___x_1018_, v___x_1016_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1034_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1022_ = v___x_1019_;
v_isShared_1023_ = v_isSharedCheck_1034_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1019_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1034_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v_fst_1024_; 
v_fst_1024_ = lean_ctor_get(v_a_1020_, 0);
if (lean_obj_tag(v_fst_1024_) == 0)
{
lean_object* v_snd_1025_; lean_object* v___x_1026_; lean_object* v___x_1028_; 
v_snd_1025_ = lean_ctor_get(v_a_1020_, 1);
lean_inc(v_snd_1025_);
lean_dec(v_a_1020_);
v___x_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1026_, 0, v_snd_1025_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v___x_1026_);
v___x_1028_ = v___x_1022_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
else
{
lean_object* v_val_1030_; lean_object* v___x_1032_; 
lean_inc_ref(v_fst_1024_);
lean_dec(v_a_1020_);
v_val_1030_ = lean_ctor_get(v_fst_1024_, 0);
lean_inc(v_val_1030_);
lean_dec_ref_known(v_fst_1024_, 1);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v_val_1030_);
v___x_1032_ = v___x_1022_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_val_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
v_a_1035_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_1019_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1019_);
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
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
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
lean_object* v_vs_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; size_t v_sz_1046_; size_t v___x_1047_; lean_object* v___x_1048_; 
v_vs_1043_ = lean_ctor_get(v_n_1011_, 0);
v___x_1044_ = lean_box(0);
v___x_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
lean_ctor_set(v___x_1045_, 1, v_b_1012_);
v_sz_1046_ = lean_array_size(v_vs_1043_);
v___x_1047_ = ((size_t)0ULL);
v___x_1048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_vs_1043_, v_sz_1046_, v___x_1047_, v___x_1045_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1063_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1051_ = v___x_1048_;
v_isShared_1052_ = v_isSharedCheck_1063_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1048_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1063_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v_fst_1053_; 
v_fst_1053_ = lean_ctor_get(v_a_1049_, 0);
if (lean_obj_tag(v_fst_1053_) == 0)
{
lean_object* v_snd_1054_; lean_object* v___x_1055_; lean_object* v___x_1057_; 
v_snd_1054_ = lean_ctor_get(v_a_1049_, 1);
lean_inc(v_snd_1054_);
lean_dec(v_a_1049_);
v___x_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1055_, 0, v_snd_1054_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 0, v___x_1055_);
v___x_1057_ = v___x_1051_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
else
{
lean_object* v_val_1059_; lean_object* v___x_1061_; 
lean_inc_ref(v_fst_1053_);
lean_dec(v_a_1049_);
v_val_1059_ = lean_ctor_get(v_fst_1053_, 0);
lean_inc(v_val_1059_);
lean_dec_ref_known(v_fst_1053_, 1);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 0, v_val_1059_);
v___x_1061_ = v___x_1051_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_val_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
v_a_1064_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1048_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1048_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1010_ = stack[0].m_obj;
lean_object* v_n_1011_ = stack[1].m_obj;
lean_object* v_b_1012_ = stack[2].m_obj;
lean_object* v_res_1072_;
v_res_1072_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_1010_, v_n_1011_, v_b_1012_);
stack->m_obj
 = v_res_1072_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12(lean_object* v_init_1073_, lean_object* v_as_1074_, size_t v_sz_1075_, size_t v_i_1076_, lean_object* v_b_1077_){
_start:
{
uint8_t v___x_1079_; 
v___x_1079_ = lean_usize_dec_lt(v_i_1076_, v_sz_1075_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1080_, 0, v_b_1077_);
return v___x_1080_;
}
else
{
lean_object* v_snd_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1115_; 
v_snd_1081_ = lean_ctor_get(v_b_1077_, 1);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_b_1077_);
if (v_isSharedCheck_1115_ == 0)
{
lean_object* v_unused_1116_; 
v_unused_1116_ = lean_ctor_get(v_b_1077_, 0);
lean_dec(v_unused_1116_);
v___x_1083_ = v_b_1077_;
v_isShared_1084_ = v_isSharedCheck_1115_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_snd_1081_);
lean_dec(v_b_1077_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1115_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1085_; lean_object* v_a_1086_; lean_object* v___x_1087_; 
v___x_1085_ = lean_box(0);
v_a_1086_ = lean_array_uget_borrowed(v_as_1074_, v_i_1076_);
lean_inc(v_snd_1081_);
v___x_1087_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_1073_, v_a_1086_, v_snd_1081_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1106_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1090_ = v___x_1087_;
v_isShared_1091_ = v_isSharedCheck_1106_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1087_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1106_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
if (lean_obj_tag(v_a_1088_) == 0)
{
lean_object* v___x_1092_; lean_object* v___x_1094_; 
v___x_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1092_, 0, v_a_1088_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1092_);
v___x_1094_ = v___x_1083_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_snd_1081_);
v___x_1094_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1096_; 
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v___x_1094_);
v___x_1096_ = v___x_1090_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; 
lean_del_object(v___x_1090_);
lean_dec(v_snd_1081_);
v_a_1099_ = lean_ctor_get(v_a_1088_, 0);
lean_inc(v_a_1099_);
lean_dec_ref_known(v_a_1088_, 1);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 1, v_a_1099_);
lean_ctor_set(v___x_1083_, 0, v___x_1085_);
v___x_1101_ = v___x_1083_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_a_1099_);
v___x_1101_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
size_t v___x_1102_; size_t v___x_1103_; 
v___x_1102_ = ((size_t)1ULL);
v___x_1103_ = lean_usize_add(v_i_1076_, v___x_1102_);
v_i_1076_ = v___x_1103_;
v_b_1077_ = v___x_1101_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_del_object(v___x_1083_);
lean_dec(v_snd_1081_);
v_a_1107_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1087_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1087_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1073_ = stack[0].m_obj;
lean_object* v_as_1074_ = stack[1].m_obj;
size_t v_sz_1075_ = stack[2].m_num;
size_t v_i_1076_ = stack[3].m_num;
lean_object* v_b_1077_ = stack[4].m_obj;
lean_object* v_res_1117_;
v_res_1117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12(v_init_1073_, v_as_1074_, v_sz_1075_, v_i_1076_, v_b_1077_);
stack->m_obj
 = v_res_1117_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12___boxed(lean_object* v_init_1118_, lean_object* v_as_1119_, lean_object* v_sz_1120_, lean_object* v_i_1121_, lean_object* v_b_1122_, lean_object* v___y_1123_){
_start:
{
size_t v_sz_boxed_1124_; size_t v_i_boxed_1125_; lean_object* v_res_1126_; 
v_sz_boxed_1124_ = lean_unbox_usize(v_sz_1120_);
lean_dec(v_sz_1120_);
v_i_boxed_1125_ = lean_unbox_usize(v_i_1121_);
lean_dec(v_i_1121_);
v_res_1126_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12(v_init_1118_, v_as_1119_, v_sz_boxed_1124_, v_i_boxed_1125_, v_b_1122_);
lean_dec_ref(v_as_1119_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10___boxed(lean_object* v_init_1127_, lean_object* v_n_1128_, lean_object* v_b_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_1127_, v_n_1128_, v_b_1129_);
lean_dec_ref(v_n_1128_);
return v_res_1131_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15(lean_object* v_as_1135_, size_t v_sz_1136_, size_t v_i_1137_, lean_object* v_b_1138_){
_start:
{
uint8_t v___x_1140_; 
v___x_1140_ = lean_usize_dec_lt(v_i_1137_, v_sz_1136_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1141_, 0, v_b_1138_);
return v___x_1141_;
}
else
{
uint8_t v___x_1142_; lean_object* v_a_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_dec_ref(v_b_1138_);
v___x_1142_ = 0;
v_a_1143_ = lean_array_uget_borrowed(v_as_1135_, v_i_1137_);
lean_inc(v_a_1143_);
v___x_1144_ = l_Lean_Message_toString(v_a_1143_, v___x_1142_);
v___x_1145_ = l_IO_eprintln___at___00main_spec__6(v___x_1144_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v___x_1146_; size_t v___x_1147_; size_t v___x_1148_; 
lean_dec_ref_known(v___x_1145_, 1);
v___x_1146_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_1147_ = ((size_t)1ULL);
v___x_1148_ = lean_usize_add(v_i_1137_, v___x_1147_);
v_i_1137_ = v___x_1148_;
v_b_1138_ = v___x_1146_;
goto _start;
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
v_a_1150_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1145_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1145_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1135_ = stack[0].m_obj;
size_t v_sz_1136_ = stack[1].m_num;
size_t v_i_1137_ = stack[2].m_num;
lean_object* v_b_1138_ = stack[3].m_obj;
lean_object* v_res_1158_;
v_res_1158_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15(v_as_1135_, v_sz_1136_, v_i_1137_, v_b_1138_);
stack->m_obj
 = v_res_1158_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___boxed(lean_object* v_as_1159_, lean_object* v_sz_1160_, lean_object* v_i_1161_, lean_object* v_b_1162_, lean_object* v___y_1163_){
_start:
{
size_t v_sz_boxed_1164_; size_t v_i_boxed_1165_; lean_object* v_res_1166_; 
v_sz_boxed_1164_ = lean_unbox_usize(v_sz_1160_);
lean_dec(v_sz_1160_);
v_i_boxed_1165_ = lean_unbox_usize(v_i_1161_);
lean_dec(v_i_1161_);
v_res_1166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15(v_as_1159_, v_sz_boxed_1164_, v_i_boxed_1165_, v_b_1162_);
lean_dec_ref(v_as_1159_);
return v_res_1166_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(lean_object* v_as_1167_, size_t v_sz_1168_, size_t v_i_1169_, lean_object* v_b_1170_){
_start:
{
uint8_t v___x_1172_; 
v___x_1172_ = lean_usize_dec_lt(v_i_1169_, v_sz_1168_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; 
v___x_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1173_, 0, v_b_1170_);
return v___x_1173_;
}
else
{
uint8_t v___x_1174_; lean_object* v_a_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
lean_dec_ref(v_b_1170_);
v___x_1174_ = 0;
v_a_1175_ = lean_array_uget_borrowed(v_as_1167_, v_i_1169_);
lean_inc(v_a_1175_);
v___x_1176_ = l_Lean_Message_toString(v_a_1175_, v___x_1174_);
v___x_1177_ = l_IO_eprintln___at___00main_spec__6(v___x_1176_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v___x_1178_; size_t v___x_1179_; size_t v___x_1180_; lean_object* v___x_1181_; 
lean_dec_ref_known(v___x_1177_, 1);
v___x_1178_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_1179_ = ((size_t)1ULL);
v___x_1180_ = lean_usize_add(v_i_1169_, v___x_1179_);
v___x_1181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15(v_as_1167_, v_sz_1168_, v___x_1180_, v___x_1178_);
return v___x_1181_;
}
else
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
v_a_1182_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1177_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1177_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1167_ = stack[0].m_obj;
size_t v_sz_1168_ = stack[1].m_num;
size_t v_i_1169_ = stack[2].m_num;
lean_object* v_b_1170_ = stack[3].m_obj;
lean_object* v_res_1190_;
v_res_1190_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_as_1167_, v_sz_1168_, v_i_1169_, v_b_1170_);
stack->m_obj
 = v_res_1190_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11___boxed(lean_object* v_as_1191_, lean_object* v_sz_1192_, lean_object* v_i_1193_, lean_object* v_b_1194_, lean_object* v___y_1195_){
_start:
{
size_t v_sz_boxed_1196_; size_t v_i_boxed_1197_; lean_object* v_res_1198_; 
v_sz_boxed_1196_ = lean_unbox_usize(v_sz_1192_);
lean_dec(v_sz_1192_);
v_i_boxed_1197_ = lean_unbox_usize(v_i_1193_);
lean_dec(v_i_1193_);
v_res_1198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_as_1191_, v_sz_boxed_1196_, v_i_boxed_1197_, v_b_1194_);
lean_dec_ref(v_as_1191_);
return v_res_1198_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7(lean_object* v_t_1199_, lean_object* v_init_1200_){
_start:
{
lean_object* v_root_1202_; lean_object* v_tail_1203_; lean_object* v___x_1204_; 
v_root_1202_ = lean_ctor_get(v_t_1199_, 0);
v_tail_1203_ = lean_ctor_get(v_t_1199_, 1);
v___x_1204_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_1200_, v_root_1202_, v_init_1200_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1241_; 
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1207_ = v___x_1204_;
v_isShared_1208_ = v_isSharedCheck_1241_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1204_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1241_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
if (lean_obj_tag(v_a_1205_) == 0)
{
lean_object* v_a_1209_; lean_object* v___x_1211_; 
v_a_1209_ = lean_ctor_get(v_a_1205_, 0);
lean_inc(v_a_1209_);
lean_dec_ref_known(v_a_1205_, 1);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v_a_1209_);
v___x_1211_ = v___x_1207_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1209_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; size_t v_sz_1216_; size_t v___x_1217_; lean_object* v___x_1218_; 
lean_del_object(v___x_1207_);
v_a_1213_ = lean_ctor_get(v_a_1205_, 0);
lean_inc(v_a_1213_);
lean_dec_ref_known(v_a_1205_, 1);
v___x_1214_ = lean_box(0);
v___x_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
lean_ctor_set(v___x_1215_, 1, v_a_1213_);
v_sz_1216_ = lean_array_size(v_tail_1203_);
v___x_1217_ = ((size_t)0ULL);
v___x_1218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_tail_1203_, v_sz_1216_, v___x_1217_, v___x_1215_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1232_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1221_ = v___x_1218_;
v_isShared_1222_ = v_isSharedCheck_1232_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1232_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v_fst_1223_; 
v_fst_1223_ = lean_ctor_get(v_a_1219_, 0);
if (lean_obj_tag(v_fst_1223_) == 0)
{
lean_object* v_snd_1224_; lean_object* v___x_1226_; 
v_snd_1224_ = lean_ctor_get(v_a_1219_, 1);
lean_inc(v_snd_1224_);
lean_dec(v_a_1219_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v_snd_1224_);
v___x_1226_ = v___x_1221_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_snd_1224_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
else
{
lean_object* v_val_1228_; lean_object* v___x_1230_; 
lean_inc_ref(v_fst_1223_);
lean_dec(v_a_1219_);
v_val_1228_ = lean_ctor_get(v_fst_1223_, 0);
lean_inc(v_val_1228_);
lean_dec_ref_known(v_fst_1223_, 1);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v_val_1228_);
v___x_1230_ = v___x_1221_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_val_1228_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
v_a_1233_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1218_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1218_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
}
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
v_a_1242_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1204_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1204_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00main_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1199_ = stack[0].m_obj;
lean_object* v_init_1200_ = stack[1].m_obj;
lean_object* v_res_1250_;
v_res_1250_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_t_1199_, v_init_1200_);
stack->m_obj
 = v_res_1250_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7___boxed(lean_object* v_t_1251_, lean_object* v_init_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_t_1251_, v_init_1252_);
lean_dec_ref(v_t_1251_);
return v_res_1254_;
}
}
uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0(uint8_t v_suppressElabErrors_1262_, uint8_t v___y_1263_, lean_object* v_x_1264_){
_start:
{
if (lean_obj_tag(v_x_1264_) == 1)
{
lean_object* v_pre_1265_; 
v_pre_1265_ = lean_ctor_get(v_x_1264_, 0);
switch(lean_obj_tag(v_pre_1265_))
{
case 1:
{
lean_object* v_pre_1266_; 
v_pre_1266_ = lean_ctor_get(v_pre_1265_, 0);
switch(lean_obj_tag(v_pre_1266_))
{
case 0:
{
lean_object* v_str_1267_; lean_object* v_str_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v_str_1267_ = lean_ctor_get(v_x_1264_, 1);
v_str_1268_ = lean_ctor_get(v_pre_1265_, 1);
v___x_1269_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__0));
v___x_1270_ = lean_string_dec_eq(v_str_1268_, v___x_1269_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1271_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__1));
v___x_1272_ = lean_string_dec_eq(v_str_1268_, v___x_1271_);
if (v___x_1272_ == 0)
{
return v___x_1272_;
}
else
{
lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1273_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__2));
v___x_1274_ = lean_string_dec_eq(v_str_1267_, v___x_1273_);
if (v___x_1274_ == 0)
{
return v___x_1274_;
}
else
{
return v_suppressElabErrors_1262_;
}
}
}
else
{
lean_object* v___x_1275_; uint8_t v___x_1276_; 
v___x_1275_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__3));
v___x_1276_ = lean_string_dec_eq(v_str_1267_, v___x_1275_);
if (v___x_1276_ == 0)
{
return v___x_1276_;
}
else
{
return v_suppressElabErrors_1262_;
}
}
}
case 1:
{
lean_object* v_pre_1277_; 
v_pre_1277_ = lean_ctor_get(v_pre_1266_, 0);
if (lean_obj_tag(v_pre_1277_) == 0)
{
lean_object* v_str_1278_; lean_object* v_str_1279_; lean_object* v_str_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v_str_1278_ = lean_ctor_get(v_x_1264_, 1);
v_str_1279_ = lean_ctor_get(v_pre_1265_, 1);
v_str_1280_ = lean_ctor_get(v_pre_1266_, 1);
v___x_1281_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__4));
v___x_1282_ = lean_string_dec_eq(v_str_1280_, v___x_1281_);
if (v___x_1282_ == 0)
{
return v___x_1282_;
}
else
{
lean_object* v___x_1283_; uint8_t v___x_1284_; 
v___x_1283_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__5));
v___x_1284_ = lean_string_dec_eq(v_str_1279_, v___x_1283_);
if (v___x_1284_ == 0)
{
return v___x_1284_;
}
else
{
lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1285_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__6));
v___x_1286_ = lean_string_dec_eq(v_str_1278_, v___x_1285_);
if (v___x_1286_ == 0)
{
return v___x_1286_;
}
else
{
return v_suppressElabErrors_1262_;
}
}
}
}
else
{
return v___y_1263_;
}
}
default: 
{
return v___y_1263_;
}
}
}
case 0:
{
lean_object* v_str_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v_str_1287_ = lean_ctor_get(v_x_1264_, 1);
v___x_1288_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_1289_ = lean_string_dec_eq(v_str_1287_, v___x_1288_);
if (v___x_1289_ == 0)
{
return v___x_1289_;
}
else
{
return v_suppressElabErrors_1262_;
}
}
default: 
{
return v___y_1263_;
}
}
}
else
{
return v___y_1263_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_1262_ = stack[0].m_num;
uint8_t v___y_1263_ = stack[1].m_num;
lean_object* v_x_1264_ = stack[2].m_obj;
uint8_t v_res_1290_;
v_res_1290_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0(v_suppressElabErrors_1262_, v___y_1263_, v_x_1264_);
stack->m_num = v_res_1290_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___boxed(lean_object* v_suppressElabErrors_1291_, lean_object* v___y_1292_, lean_object* v_x_1293_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1294_; uint8_t v___y_38937__boxed_1295_; uint8_t v_res_1296_; lean_object* v_r_1297_; 
v_suppressElabErrors_boxed_1294_ = lean_unbox(v_suppressElabErrors_1291_);
v___y_38937__boxed_1295_ = lean_unbox(v___y_1292_);
v_res_1296_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0(v_suppressElabErrors_boxed_1294_, v___y_38937__boxed_1295_, v_x_1293_);
lean_dec(v_x_1293_);
v_r_1297_ = lean_box(v_res_1296_);
return v_r_1297_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(lean_object* v_opts_1298_, lean_object* v_opt_1299_){
_start:
{
lean_object* v_name_1300_; lean_object* v_defValue_1301_; lean_object* v_map_1302_; lean_object* v___x_1303_; 
v_name_1300_ = lean_ctor_get(v_opt_1299_, 0);
v_defValue_1301_ = lean_ctor_get(v_opt_1299_, 1);
v_map_1302_ = lean_ctor_get(v_opts_1298_, 0);
v___x_1303_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1302_, v_name_1300_);
if (lean_obj_tag(v___x_1303_) == 0)
{
uint8_t v___x_1304_; 
v___x_1304_ = lean_unbox(v_defValue_1301_);
return v___x_1304_;
}
else
{
lean_object* v_val_1305_; 
v_val_1305_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_val_1305_);
lean_dec_ref_known(v___x_1303_, 1);
if (lean_obj_tag(v_val_1305_) == 1)
{
uint8_t v_v_1306_; 
v_v_1306_ = lean_ctor_get_uint8(v_val_1305_, 0);
lean_dec_ref_known(v_val_1305_, 0);
return v_v_1306_;
}
else
{
uint8_t v___x_1307_; 
lean_dec(v_val_1305_);
v___x_1307_ = lean_unbox(v_defValue_1301_);
return v___x_1307_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1298_ = stack[0].m_obj;
lean_object* v_opt_1299_ = stack[1].m_obj;
uint8_t v_res_1308_;
v_res_1308_ = l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(v_opts_1298_, v_opt_1299_);
stack->m_num = v_res_1308_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___boxed(lean_object* v_opts_1309_, lean_object* v_opt_1310_){
_start:
{
uint8_t v_res_1311_; lean_object* v_r_1312_; 
v_res_1311_ = l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(v_opts_1309_, v_opt_1310_);
lean_dec_ref(v_opt_1310_);
lean_dec_ref(v_opts_1309_);
v_r_1312_ = lean_box(v_res_1311_);
return v_r_1312_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44(lean_object* v_ref_1314_, lean_object* v_msgData_1315_, uint8_t v_severity_1316_, uint8_t v_isSilent_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v___y_1322_; uint8_t v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; uint8_t v___y_1328_; lean_object* v_toCold_1329_; lean_object* v___y_1330_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; uint8_t v___y_1362_; lean_object* v___y_1363_; uint8_t v___y_1364_; uint8_t v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1386_; lean_object* v___y_1387_; uint8_t v___y_1388_; uint8_t v___y_1389_; lean_object* v___y_1390_; uint8_t v___y_1391_; lean_object* v___y_1392_; uint8_t v___y_1396_; uint8_t v___y_1397_; uint8_t v___y_1398_; uint8_t v___x_1409_; uint8_t v___y_1411_; uint8_t v___y_1412_; uint8_t v___y_1413_; uint8_t v___y_1415_; uint8_t v___x_1423_; 
v___x_1409_ = 2;
v___x_1423_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1316_, v___x_1409_);
if (v___x_1423_ == 0)
{
v___y_1415_ = v___x_1423_;
goto v___jp_1414_;
}
else
{
uint8_t v___x_1424_; 
lean_inc_ref(v_msgData_1315_);
v___x_1424_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1315_);
v___y_1415_ = v___x_1424_;
goto v___jp_1414_;
}
v___jp_1321_:
{
lean_object* v_currNamespace_1331_; lean_object* v_openDecls_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v_env_1337_; lean_object* v_nextMacroScope_1338_; lean_object* v_ngen_1339_; lean_object* v_auxDeclNGen_1340_; lean_object* v_traceState_1341_; lean_object* v_cache_1342_; lean_object* v_recordedDeps_1343_; lean_object* v_messages_1344_; lean_object* v_infoState_1345_; lean_object* v_snapshotTasks_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1357_; 
v_currNamespace_1331_ = lean_ctor_get(v_toCold_1329_, 4);
v_openDecls_1332_ = lean_ctor_get(v_toCold_1329_, 5);
lean_inc(v_openDecls_1332_);
lean_inc(v_currNamespace_1331_);
v___x_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1333_, 0, v_currNamespace_1331_);
lean_ctor_set(v___x_1333_, 1, v_openDecls_1332_);
v___x_1334_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
lean_ctor_set(v___x_1334_, 1, v___y_1324_);
lean_inc_ref(v___y_1327_);
lean_inc_ref(v___y_1326_);
v___x_1335_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1335_, 0, v___y_1326_);
lean_ctor_set(v___x_1335_, 1, v___y_1325_);
lean_ctor_set(v___x_1335_, 2, v___y_1322_);
lean_ctor_set(v___x_1335_, 3, v___y_1327_);
lean_ctor_set(v___x_1335_, 4, v___x_1334_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*5, v___y_1328_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*5 + 1, v___y_1323_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*5 + 2, v_isSilent_1317_);
v___x_1336_ = lean_st_ref_take(v___y_1330_);
v_env_1337_ = lean_ctor_get(v___x_1336_, 0);
v_nextMacroScope_1338_ = lean_ctor_get(v___x_1336_, 1);
v_ngen_1339_ = lean_ctor_get(v___x_1336_, 2);
v_auxDeclNGen_1340_ = lean_ctor_get(v___x_1336_, 3);
v_traceState_1341_ = lean_ctor_get(v___x_1336_, 4);
v_cache_1342_ = lean_ctor_get(v___x_1336_, 5);
v_recordedDeps_1343_ = lean_ctor_get(v___x_1336_, 6);
v_messages_1344_ = lean_ctor_get(v___x_1336_, 7);
v_infoState_1345_ = lean_ctor_get(v___x_1336_, 8);
v_snapshotTasks_1346_ = lean_ctor_get(v___x_1336_, 9);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1348_ = v___x_1336_;
v_isShared_1349_ = v_isSharedCheck_1357_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_snapshotTasks_1346_);
lean_inc(v_infoState_1345_);
lean_inc(v_messages_1344_);
lean_inc(v_recordedDeps_1343_);
lean_inc(v_cache_1342_);
lean_inc(v_traceState_1341_);
lean_inc(v_auxDeclNGen_1340_);
lean_inc(v_ngen_1339_);
lean_inc(v_nextMacroScope_1338_);
lean_inc(v_env_1337_);
lean_dec(v___x_1336_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1357_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1350_ = lean_box(0);
v___x_1351_ = l_Lean_MessageLog_add(v___x_1335_, v_messages_1344_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 7, v___x_1351_);
v___x_1353_ = v___x_1348_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_env_1337_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_nextMacroScope_1338_);
lean_ctor_set(v_reuseFailAlloc_1356_, 2, v_ngen_1339_);
lean_ctor_set(v_reuseFailAlloc_1356_, 3, v_auxDeclNGen_1340_);
lean_ctor_set(v_reuseFailAlloc_1356_, 4, v_traceState_1341_);
lean_ctor_set(v_reuseFailAlloc_1356_, 5, v_cache_1342_);
lean_ctor_set(v_reuseFailAlloc_1356_, 6, v_recordedDeps_1343_);
lean_ctor_set(v_reuseFailAlloc_1356_, 7, v___x_1351_);
lean_ctor_set(v_reuseFailAlloc_1356_, 8, v_infoState_1345_);
lean_ctor_set(v_reuseFailAlloc_1356_, 9, v_snapshotTasks_1346_);
v___x_1353_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = lean_st_ref_put(v___y_1330_, v___x_1353_);
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1350_);
return v___x_1355_;
}
}
}
v___jp_1358_:
{
lean_object* v_fileName_1367_; lean_object* v_fileMap_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1384_; 
v_fileName_1367_ = lean_ctor_get(v___y_1361_, 0);
v_fileMap_1368_ = lean_ctor_get(v___y_1361_, 1);
v___x_1369_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1315_);
v___x_1370_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v___x_1369_, v___y_1318_, v___y_1319_);
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1373_ = v___x_1370_;
v_isShared_1374_ = v_isSharedCheck_1384_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1370_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1384_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
lean_inc_ref_n(v_fileMap_1368_, 2);
v___x_1375_ = l_Lean_FileMap_toPosition(v_fileMap_1368_, v___y_1363_);
lean_dec(v___y_1363_);
v___x_1376_ = l_Lean_FileMap_toPosition(v_fileMap_1368_, v___y_1366_);
lean_dec(v___y_1366_);
v___x_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1376_);
v___x_1378_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___closed__0));
if (v___y_1364_ == 0)
{
lean_del_object(v___x_1373_);
lean_dec_ref(v___y_1360_);
v___y_1322_ = v___x_1377_;
v___y_1323_ = v___y_1362_;
v___y_1324_ = v_a_1371_;
v___y_1325_ = v___x_1375_;
v___y_1326_ = v_fileName_1367_;
v___y_1327_ = v___x_1378_;
v___y_1328_ = v___y_1365_;
v_toCold_1329_ = v___y_1359_;
v___y_1330_ = v___y_1319_;
goto v___jp_1321_;
}
else
{
uint8_t v___x_1379_; 
lean_inc(v_a_1371_);
v___x_1379_ = l_Lean_MessageData_hasTag(v___y_1360_, v_a_1371_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; lean_object* v___x_1382_; 
lean_dec_ref_known(v___x_1377_, 1);
lean_dec_ref(v___x_1375_);
lean_dec(v_a_1371_);
v___x_1380_ = lean_box(0);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v___x_1380_);
v___x_1382_ = v___x_1373_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1380_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
else
{
lean_del_object(v___x_1373_);
v___y_1322_ = v___x_1377_;
v___y_1323_ = v___y_1362_;
v___y_1324_ = v_a_1371_;
v___y_1325_ = v___x_1375_;
v___y_1326_ = v_fileName_1367_;
v___y_1327_ = v___x_1378_;
v___y_1328_ = v___y_1365_;
v_toCold_1329_ = v___y_1359_;
v___y_1330_ = v___y_1319_;
goto v___jp_1321_;
}
}
}
}
v___jp_1385_:
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Lean_Syntax_getTailPos_x3f(v___y_1390_, v___y_1391_);
lean_dec(v___y_1390_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_inc(v___y_1392_);
v___y_1359_ = v___y_1386_;
v___y_1360_ = v___y_1387_;
v___y_1361_ = v___y_1386_;
v___y_1362_ = v___y_1389_;
v___y_1363_ = v___y_1392_;
v___y_1364_ = v___y_1388_;
v___y_1365_ = v___y_1391_;
v___y_1366_ = v___y_1392_;
goto v___jp_1358_;
}
else
{
lean_object* v_val_1394_; 
v_val_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_val_1394_);
lean_dec_ref_known(v___x_1393_, 1);
v___y_1359_ = v___y_1386_;
v___y_1360_ = v___y_1387_;
v___y_1361_ = v___y_1386_;
v___y_1362_ = v___y_1389_;
v___y_1363_ = v___y_1392_;
v___y_1364_ = v___y_1388_;
v___y_1365_ = v___y_1391_;
v___y_1366_ = v_val_1394_;
goto v___jp_1358_;
}
}
v___jp_1395_:
{
lean_object* v_toCold_1399_; lean_object* v_ref_1400_; uint8_t v_suppressElabErrors_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___f_1404_; lean_object* v_ref_1405_; lean_object* v___x_1406_; 
v_toCold_1399_ = lean_ctor_get(v___y_1318_, 0);
v_ref_1400_ = lean_ctor_get(v___y_1318_, 2);
v_suppressElabErrors_1401_ = lean_ctor_get_uint8(v___y_1318_, sizeof(void*)*3 + 2);
v___x_1402_ = lean_box(v_suppressElabErrors_1401_);
v___x_1403_ = lean_box(v___y_1396_);
v___f_1404_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1404_, 0, v___x_1402_);
lean_closure_set(v___f_1404_, 1, v___x_1403_);
v_ref_1405_ = l_Lean_replaceRef(v_ref_1314_, v_ref_1400_);
v___x_1406_ = l_Lean_Syntax_getPos_x3f(v_ref_1405_, v___y_1397_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v___x_1407_; 
v___x_1407_ = lean_unsigned_to_nat(0u);
v___y_1386_ = v_toCold_1399_;
v___y_1387_ = v___f_1404_;
v___y_1388_ = v_suppressElabErrors_1401_;
v___y_1389_ = v___y_1398_;
v___y_1390_ = v_ref_1405_;
v___y_1391_ = v___y_1397_;
v___y_1392_ = v___x_1407_;
goto v___jp_1385_;
}
else
{
lean_object* v_val_1408_; 
v_val_1408_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_val_1408_);
lean_dec_ref_known(v___x_1406_, 1);
v___y_1386_ = v_toCold_1399_;
v___y_1387_ = v___f_1404_;
v___y_1388_ = v_suppressElabErrors_1401_;
v___y_1389_ = v___y_1398_;
v___y_1390_ = v_ref_1405_;
v___y_1391_ = v___y_1397_;
v___y_1392_ = v_val_1408_;
goto v___jp_1385_;
}
}
v___jp_1410_:
{
if (v___y_1413_ == 0)
{
v___y_1396_ = v___y_1411_;
v___y_1397_ = v___y_1412_;
v___y_1398_ = v_severity_1316_;
goto v___jp_1395_;
}
else
{
v___y_1396_ = v___y_1411_;
v___y_1397_ = v___y_1412_;
v___y_1398_ = v___x_1409_;
goto v___jp_1395_;
}
}
v___jp_1414_:
{
if (v___y_1415_ == 0)
{
uint8_t v___x_1416_; uint8_t v___x_1417_; 
v___x_1416_ = 1;
v___x_1417_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1316_, v___x_1416_);
if (v___x_1417_ == 0)
{
v___y_1411_ = v___y_1415_;
v___y_1412_ = v___y_1415_;
v___y_1413_ = v___x_1417_;
goto v___jp_1410_;
}
else
{
lean_object* v___x_1418_; lean_object* v___x_1419_; uint8_t v___x_1420_; 
v___x_1418_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1318_);
v___x_1419_ = l_Lean_warningAsError;
v___x_1420_ = l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(v___x_1418_, v___x_1419_);
lean_dec_ref(v___x_1418_);
v___y_1411_ = v___y_1415_;
v___y_1412_ = v___y_1415_;
v___y_1413_ = v___x_1420_;
goto v___jp_1410_;
}
}
else
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
lean_dec_ref(v_msgData_1315_);
v___x_1421_ = lean_box(0);
v___x_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
return v___x_1422_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1314_ = stack[0].m_obj;
lean_object* v_msgData_1315_ = stack[1].m_obj;
uint8_t v_severity_1316_ = stack[2].m_num;
uint8_t v_isSilent_1317_ = stack[3].m_num;
lean_object* v___y_1318_ = stack[4].m_obj;
lean_object* v___y_1319_ = stack[5].m_obj;
lean_object* v_res_1425_;
v_res_1425_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44(v_ref_1314_, v_msgData_1315_, v_severity_1316_, v_isSilent_1317_, v___y_1318_, v___y_1319_);
stack->m_obj
 = v_res_1425_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___boxed(lean_object* v_ref_1426_, lean_object* v_msgData_1427_, lean_object* v_severity_1428_, lean_object* v_isSilent_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
uint8_t v_severity_boxed_1433_; uint8_t v_isSilent_boxed_1434_; lean_object* v_res_1435_; 
v_severity_boxed_1433_ = lean_unbox(v_severity_1428_);
v_isSilent_boxed_1434_ = lean_unbox(v_isSilent_1429_);
v_res_1435_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44(v_ref_1426_, v_msgData_1427_, v_severity_boxed_1433_, v_isSilent_boxed_1434_, v___y_1430_, v___y_1431_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v_ref_1426_);
return v_res_1435_;
}
}
lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30(lean_object* v_msgData_1436_, uint8_t v_severity_1437_, uint8_t v_isSilent_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v_ref_1442_; lean_object* v___x_1443_; 
v_ref_1442_ = lean_ctor_get(v___y_1439_, 2);
v___x_1443_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44(v_ref_1442_, v_msgData_1436_, v_severity_1437_, v_isSilent_1438_, v___y_1439_, v___y_1440_);
return v___x_1443_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1436_ = stack[0].m_obj;
uint8_t v_severity_1437_ = stack[1].m_num;
uint8_t v_isSilent_1438_ = stack[2].m_num;
lean_object* v___y_1439_ = stack[3].m_obj;
lean_object* v___y_1440_ = stack[4].m_obj;
lean_object* v_res_1444_;
v_res_1444_ = l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30(v_msgData_1436_, v_severity_1437_, v_isSilent_1438_, v___y_1439_, v___y_1440_);
stack->m_obj
 = v_res_1444_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30___boxed(lean_object* v_msgData_1445_, lean_object* v_severity_1446_, lean_object* v_isSilent_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
uint8_t v_severity_boxed_1451_; uint8_t v_isSilent_boxed_1452_; lean_object* v_res_1453_; 
v_severity_boxed_1451_ = lean_unbox(v_severity_1446_);
v_isSilent_boxed_1452_ = lean_unbox(v_isSilent_1447_);
v_res_1453_ = l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30(v_msgData_1445_, v_severity_boxed_1451_, v_isSilent_boxed_1452_, v___y_1448_, v___y_1449_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
return v_res_1453_;
}
}
lean_object* l_Lean_logError___at___00main_spec__13(lean_object* v_msgData_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
uint8_t v___x_1458_; uint8_t v___x_1459_; lean_object* v___x_1460_; 
v___x_1458_ = 2;
v___x_1459_ = 0;
v___x_1460_ = l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30(v_msgData_1454_, v___x_1458_, v___x_1459_, v___y_1455_, v___y_1456_);
return v___x_1460_;
}
}
LEAN_EXPORT void l_Lean_logError___at___00main_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1454_ = stack[0].m_obj;
lean_object* v___y_1455_ = stack[1].m_obj;
lean_object* v___y_1456_ = stack[2].m_obj;
lean_object* v_res_1461_;
v_res_1461_ = l_Lean_logError___at___00main_spec__13(v_msgData_1454_, v___y_1455_, v___y_1456_);
stack->m_obj
 = v_res_1461_;
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13___boxed(lean_object* v_msgData_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_logError___at___00main_spec__13(v_msgData_1462_, v___y_1463_, v___y_1464_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(lean_object* v_opts_1467_, lean_object* v_opt_1468_){
_start:
{
lean_object* v_name_1469_; lean_object* v_map_1470_; lean_object* v___x_1471_; 
v_name_1469_ = lean_ctor_get(v_opt_1468_, 0);
v_map_1470_ = lean_ctor_get(v_opts_1467_, 0);
v___x_1471_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1470_, v_name_1469_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v___x_1472_; 
v___x_1472_ = lean_box(0);
return v___x_1472_;
}
else
{
lean_object* v_val_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1482_; 
v_val_1473_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1475_ = v___x_1471_;
v_isShared_1476_ = v_isSharedCheck_1482_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_val_1473_);
lean_dec(v___x_1471_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1482_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
if (lean_obj_tag(v_val_1473_) == 0)
{
lean_object* v_v_1477_; lean_object* v___x_1479_; 
v_v_1477_ = lean_ctor_get(v_val_1473_, 0);
lean_inc_ref(v_v_1477_);
lean_dec_ref_known(v_val_1473_, 1);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 0, v_v_1477_);
v___x_1479_ = v___x_1475_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_v_1477_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
else
{
lean_object* v___x_1481_; 
lean_del_object(v___x_1475_);
lean_dec(v_val_1473_);
v___x_1481_ = lean_box(0);
return v___x_1481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___boxed(lean_object* v_opts_1483_, lean_object* v_opt_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(v_opts_1483_, v_opt_1484_);
lean_dec_ref(v_opt_1484_);
lean_dec_ref(v_opts_1483_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22(lean_object* v_x_1486_, lean_object* v_x_1487_){
_start:
{
if (lean_obj_tag(v_x_1487_) == 0)
{
return v_x_1486_;
}
else
{
lean_object* v_key_1488_; lean_object* v_value_1489_; lean_object* v_tail_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v_key_1488_ = lean_ctor_get(v_x_1487_, 0);
v_value_1489_ = lean_ctor_get(v_x_1487_, 1);
v_tail_1490_ = lean_ctor_get(v_x_1487_, 2);
lean_inc(v_value_1489_);
lean_inc(v_key_1488_);
v___x_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1491_, 0, v_key_1488_);
lean_ctor_set(v___x_1491_, 1, v_value_1489_);
v___x_1492_ = lean_array_push(v_x_1486_, v___x_1491_);
v_x_1486_ = v___x_1492_;
v_x_1487_ = v_tail_1490_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22___boxed(lean_object* v_x_1494_, lean_object* v_x_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22(v_x_1494_, v_x_1495_);
lean_dec(v_x_1495_);
return v_res_1496_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23(lean_object* v_as_1497_, size_t v_i_1498_, size_t v_stop_1499_, lean_object* v_b_1500_){
_start:
{
uint8_t v___x_1501_; 
v___x_1501_ = lean_usize_dec_eq(v_i_1498_, v_stop_1499_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; lean_object* v___x_1503_; size_t v___x_1504_; size_t v___x_1505_; 
v___x_1502_ = lean_array_uget_borrowed(v_as_1497_, v_i_1498_);
v___x_1503_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22(v_b_1500_, v___x_1502_);
v___x_1504_ = ((size_t)1ULL);
v___x_1505_ = lean_usize_add(v_i_1498_, v___x_1504_);
v_i_1498_ = v___x_1505_;
v_b_1500_ = v___x_1503_;
goto _start;
}
else
{
return v_b_1500_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1497_ = stack[0].m_obj;
size_t v_i_1498_ = stack[1].m_num;
size_t v_stop_1499_ = stack[2].m_num;
lean_object* v_b_1500_ = stack[3].m_obj;
lean_object* v_res_1507_;
v_res_1507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23(v_as_1497_, v_i_1498_, v_stop_1499_, v_b_1500_);
stack->m_obj
 = v_res_1507_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23___boxed(lean_object* v_as_1508_, lean_object* v_i_1509_, lean_object* v_stop_1510_, lean_object* v_b_1511_){
_start:
{
size_t v_i_boxed_1512_; size_t v_stop_boxed_1513_; lean_object* v_res_1514_; 
v_i_boxed_1512_ = lean_unbox_usize(v_i_1509_);
lean_dec(v_i_1509_);
v_stop_boxed_1513_ = lean_unbox_usize(v_stop_1510_);
lean_dec(v_stop_1510_);
v_res_1514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23(v_as_1508_, v_i_boxed_1512_, v_stop_boxed_1513_, v_b_1511_);
lean_dec_ref(v_as_1508_);
return v_res_1514_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(lean_object* v_x_1515_, lean_object* v_x_1516_){
_start:
{
lean_object* v_fst_1517_; lean_object* v_fst_1518_; lean_object* v_fst_1519_; lean_object* v_fst_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v_fst_1517_ = lean_ctor_get(v_x_1515_, 0);
v_fst_1518_ = lean_ctor_get(v_x_1516_, 0);
v_fst_1519_ = lean_ctor_get(v_fst_1517_, 0);
v_fst_1520_ = lean_ctor_get(v_fst_1518_, 0);
v___x_1521_ = lean_unsigned_to_nat(1u);
v___x_1522_ = lean_nat_add(v_fst_1519_, v___x_1521_);
v___x_1523_ = lean_nat_dec_le(v___x_1522_, v_fst_1520_);
lean_dec(v___x_1522_);
return v___x_1523_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1515_ = stack[0].m_obj;
lean_object* v_x_1516_ = stack[1].m_obj;
uint8_t v_res_1524_;
v_res_1524_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v_x_1515_, v_x_1516_);
stack->m_num = v_res_1524_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0___boxed(lean_object* v_x_1525_, lean_object* v_x_1526_){
_start:
{
uint8_t v_res_1527_; lean_object* v_r_1528_; 
v_res_1527_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v_x_1525_, v_x_1526_);
lean_dec_ref(v_x_1526_);
lean_dec_ref(v_x_1525_);
v_r_1528_ = lean_box(v_res_1527_);
return v_r_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(lean_object* v_hi_1529_, lean_object* v_pivot_1530_, lean_object* v_as_1531_, lean_object* v_i_1532_, lean_object* v_k_1533_){
_start:
{
uint8_t v___x_1534_; 
v___x_1534_ = lean_nat_dec_lt(v_k_1533_, v_hi_1529_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
lean_dec(v_k_1533_);
v___x_1535_ = lean_array_fswap(v_as_1531_, v_i_1532_, v_hi_1529_);
v___x_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1536_, 0, v_i_1532_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
return v___x_1536_;
}
else
{
lean_object* v___x_1537_; lean_object* v_fst_1538_; lean_object* v_fst_1539_; lean_object* v_fst_1540_; lean_object* v_fst_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; 
v___x_1537_ = lean_array_fget_borrowed(v_as_1531_, v_k_1533_);
v_fst_1538_ = lean_ctor_get(v___x_1537_, 0);
v_fst_1539_ = lean_ctor_get(v_pivot_1530_, 0);
v_fst_1540_ = lean_ctor_get(v_fst_1538_, 0);
v_fst_1541_ = lean_ctor_get(v_fst_1539_, 0);
v___x_1542_ = lean_unsigned_to_nat(1u);
v___x_1543_ = lean_nat_add(v_fst_1540_, v___x_1542_);
v___x_1544_ = lean_nat_dec_le(v___x_1543_, v_fst_1541_);
lean_dec(v___x_1543_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; 
v___x_1545_ = lean_nat_add(v_k_1533_, v___x_1542_);
lean_dec(v_k_1533_);
v_k_1533_ = v___x_1545_;
goto _start;
}
else
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1547_ = lean_array_fswap(v_as_1531_, v_i_1532_, v_k_1533_);
v___x_1548_ = lean_nat_add(v_i_1532_, v___x_1542_);
lean_dec(v_i_1532_);
v___x_1549_ = lean_nat_add(v_k_1533_, v___x_1542_);
lean_dec(v_k_1533_);
v_as_1531_ = v___x_1547_;
v_i_1532_ = v___x_1548_;
v_k_1533_ = v___x_1549_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg___boxed(lean_object* v_hi_1551_, lean_object* v_pivot_1552_, lean_object* v_as_1553_, lean_object* v_i_1554_, lean_object* v_k_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(v_hi_1551_, v_pivot_1552_, v_as_1553_, v_i_1554_, v_k_1555_);
lean_dec_ref(v_pivot_1552_);
lean_dec(v_hi_1551_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(lean_object* v_n_1557_, lean_object* v_as_1558_, lean_object* v_lo_1559_, lean_object* v_hi_1560_){
_start:
{
lean_object* v___y_1562_; uint8_t v___x_1572_; 
v___x_1572_ = lean_nat_dec_lt(v_lo_1559_, v_hi_1560_);
if (v___x_1572_ == 0)
{
lean_dec(v_lo_1559_);
return v_as_1558_;
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v_mid_1575_; lean_object* v___y_1577_; lean_object* v___y_1583_; lean_object* v___x_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; 
v___x_1573_ = lean_nat_add(v_lo_1559_, v_hi_1560_);
v___x_1574_ = lean_unsigned_to_nat(1u);
v_mid_1575_ = lean_nat_shiftr(v___x_1573_, v___x_1574_);
lean_dec(v___x_1573_);
v___x_1588_ = lean_array_fget_borrowed(v_as_1558_, v_mid_1575_);
v___x_1589_ = lean_array_fget_borrowed(v_as_1558_, v_lo_1559_);
v___x_1590_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v___x_1588_, v___x_1589_);
if (v___x_1590_ == 0)
{
v___y_1583_ = v_as_1558_;
goto v___jp_1582_;
}
else
{
lean_object* v___x_1591_; 
v___x_1591_ = lean_array_fswap(v_as_1558_, v_lo_1559_, v_mid_1575_);
v___y_1583_ = v___x_1591_;
goto v___jp_1582_;
}
v___jp_1576_:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; uint8_t v___x_1580_; 
v___x_1578_ = lean_array_fget_borrowed(v___y_1577_, v_mid_1575_);
v___x_1579_ = lean_array_fget_borrowed(v___y_1577_, v_hi_1560_);
v___x_1580_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v___x_1578_, v___x_1579_);
if (v___x_1580_ == 0)
{
lean_dec(v_mid_1575_);
v___y_1562_ = v___y_1577_;
goto v___jp_1561_;
}
else
{
lean_object* v___x_1581_; 
v___x_1581_ = lean_array_fswap(v___y_1577_, v_mid_1575_, v_hi_1560_);
lean_dec(v_mid_1575_);
v___y_1562_ = v___x_1581_;
goto v___jp_1561_;
}
}
v___jp_1582_:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; uint8_t v___x_1586_; 
v___x_1584_ = lean_array_fget_borrowed(v___y_1583_, v_hi_1560_);
v___x_1585_ = lean_array_fget_borrowed(v___y_1583_, v_lo_1559_);
v___x_1586_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v___x_1584_, v___x_1585_);
if (v___x_1586_ == 0)
{
v___y_1577_ = v___y_1583_;
goto v___jp_1576_;
}
else
{
lean_object* v___x_1587_; 
v___x_1587_ = lean_array_fswap(v___y_1583_, v_lo_1559_, v_hi_1560_);
v___y_1577_ = v___x_1587_;
goto v___jp_1576_;
}
}
}
v___jp_1561_:
{
lean_object* v_pivot_1563_; lean_object* v___x_1564_; lean_object* v_fst_1565_; lean_object* v_snd_1566_; uint8_t v___x_1567_; 
v_pivot_1563_ = lean_array_fget(v___y_1562_, v_hi_1560_);
lean_inc_n(v_lo_1559_, 2);
v___x_1564_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(v_hi_1560_, v_pivot_1563_, v___y_1562_, v_lo_1559_, v_lo_1559_);
lean_dec(v_pivot_1563_);
v_fst_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_fst_1565_);
v_snd_1566_ = lean_ctor_get(v___x_1564_, 1);
lean_inc(v_snd_1566_);
lean_dec_ref(v___x_1564_);
v___x_1567_ = lean_nat_dec_le(v_hi_1560_, v_fst_1565_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1568_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v_n_1557_, v_snd_1566_, v_lo_1559_, v_fst_1565_);
v___x_1569_ = lean_unsigned_to_nat(1u);
v___x_1570_ = lean_nat_add(v_fst_1565_, v___x_1569_);
lean_dec(v_fst_1565_);
v_as_1558_ = v___x_1568_;
v_lo_1559_ = v___x_1570_;
goto _start;
}
else
{
lean_dec(v_fst_1565_);
lean_dec(v_lo_1559_);
return v_snd_1566_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___boxed(lean_object* v_n_1592_, lean_object* v_as_1593_, lean_object* v_lo_1594_, lean_object* v_hi_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v_n_1592_, v_as_1593_, v_lo_1594_, v_hi_1595_);
lean_dec(v_hi_1595_);
lean_dec(v_n_1592_);
return v_res_1596_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0(uint8_t v_suppressElabErrors_1597_, uint8_t v___x_1598_, lean_object* v___x_1599_, lean_object* v_x_1600_){
_start:
{
if (lean_obj_tag(v_x_1600_) == 1)
{
lean_object* v_pre_1601_; 
v_pre_1601_ = lean_ctor_get(v_x_1600_, 0);
switch(lean_obj_tag(v_pre_1601_))
{
case 1:
{
lean_object* v_pre_1602_; 
v_pre_1602_ = lean_ctor_get(v_pre_1601_, 0);
switch(lean_obj_tag(v_pre_1602_))
{
case 0:
{
lean_object* v_str_1603_; lean_object* v_str_1604_; lean_object* v___x_1605_; uint8_t v___x_1606_; 
v_str_1603_ = lean_ctor_get(v_x_1600_, 1);
v_str_1604_ = lean_ctor_get(v_pre_1601_, 1);
v___x_1605_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__0));
v___x_1606_ = lean_string_dec_eq(v_str_1604_, v___x_1605_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; uint8_t v___x_1608_; 
v___x_1607_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__1));
v___x_1608_ = lean_string_dec_eq(v_str_1604_, v___x_1607_);
if (v___x_1608_ == 0)
{
return v___x_1608_;
}
else
{
lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1609_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__2));
v___x_1610_ = lean_string_dec_eq(v_str_1603_, v___x_1609_);
if (v___x_1610_ == 0)
{
return v___x_1610_;
}
else
{
return v_suppressElabErrors_1597_;
}
}
}
else
{
lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1611_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__3));
v___x_1612_ = lean_string_dec_eq(v_str_1603_, v___x_1611_);
if (v___x_1612_ == 0)
{
return v___x_1612_;
}
else
{
return v_suppressElabErrors_1597_;
}
}
}
case 1:
{
lean_object* v_pre_1613_; 
v_pre_1613_ = lean_ctor_get(v_pre_1602_, 0);
if (lean_obj_tag(v_pre_1613_) == 0)
{
lean_object* v_str_1614_; lean_object* v_str_1615_; lean_object* v_str_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; 
v_str_1614_ = lean_ctor_get(v_x_1600_, 1);
v_str_1615_ = lean_ctor_get(v_pre_1601_, 1);
v_str_1616_ = lean_ctor_get(v_pre_1602_, 1);
v___x_1617_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__4));
v___x_1618_ = lean_string_dec_eq(v_str_1616_, v___x_1617_);
if (v___x_1618_ == 0)
{
return v___x_1618_;
}
else
{
lean_object* v___x_1619_; uint8_t v___x_1620_; 
v___x_1619_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__5));
v___x_1620_ = lean_string_dec_eq(v_str_1615_, v___x_1619_);
if (v___x_1620_ == 0)
{
return v___x_1620_;
}
else
{
lean_object* v___x_1621_; uint8_t v___x_1622_; 
v___x_1621_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__6));
v___x_1622_ = lean_string_dec_eq(v_str_1614_, v___x_1621_);
if (v___x_1622_ == 0)
{
return v___x_1622_;
}
else
{
return v_suppressElabErrors_1597_;
}
}
}
}
else
{
return v___x_1598_;
}
}
default: 
{
return v___x_1598_;
}
}
}
case 0:
{
lean_object* v_str_1623_; uint8_t v___x_1624_; 
v_str_1623_ = lean_ctor_get(v_x_1600_, 1);
v___x_1624_ = lean_string_dec_eq(v_str_1623_, v___x_1599_);
if (v___x_1624_ == 0)
{
return v___x_1624_;
}
else
{
return v_suppressElabErrors_1597_;
}
}
default: 
{
return v___x_1598_;
}
}
}
else
{
return v___x_1598_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_1597_ = stack[0].m_num;
uint8_t v___x_1598_ = stack[1].m_num;
lean_object* v___x_1599_ = stack[2].m_obj;
lean_object* v_x_1600_ = stack[3].m_obj;
uint8_t v_res_1625_;
v_res_1625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0(v_suppressElabErrors_1597_, v___x_1598_, v___x_1599_, v_x_1600_);
stack->m_num = v_res_1625_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0___boxed(lean_object* v_suppressElabErrors_1626_, lean_object* v___x_1627_, lean_object* v___x_1628_, lean_object* v_x_1629_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1630_; uint8_t v___x_39635__boxed_1631_; uint8_t v_res_1632_; lean_object* v_r_1633_; 
v_suppressElabErrors_boxed_1630_ = lean_unbox(v_suppressElabErrors_1626_);
v___x_39635__boxed_1631_ = lean_unbox(v___x_1627_);
v_res_1632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0(v_suppressElabErrors_boxed_1630_, v___x_39635__boxed_1631_, v___x_1628_, v_x_1629_);
lean_dec(v_x_1629_);
lean_dec_ref(v___x_1628_);
v_r_1633_ = lean_box(v_res_1632_);
return v_r_1633_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0(void){
_start:
{
lean_object* v___x_1634_; double v___x_1635_; 
v___x_1634_ = lean_unsigned_to_nat(0u);
v___x_1635_ = lean_float_of_nat(v___x_1634_);
return v___x_1635_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(uint8_t v___x_1636_, lean_object* v_as_1637_, size_t v_sz_1638_, size_t v_i_1639_, lean_object* v_b_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v_a_1645_; uint8_t v___x_1649_; 
v___x_1649_ = lean_usize_dec_lt(v_i_1639_, v_sz_1638_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; 
v___x_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1650_, 0, v_b_1640_);
return v___x_1650_;
}
else
{
lean_object* v_a_1651_; lean_object* v_fst_1652_; lean_object* v_snd_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1732_; 
v_a_1651_ = lean_array_uget(v_as_1637_, v_i_1639_);
v_fst_1652_ = lean_ctor_get(v_a_1651_, 0);
v_snd_1653_ = lean_ctor_get(v_a_1651_, 1);
v_isSharedCheck_1732_ = !lean_is_exclusive(v_a_1651_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1655_ = v_a_1651_;
v_isShared_1656_ = v_isSharedCheck_1732_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_snd_1653_);
lean_inc(v_fst_1652_);
lean_dec(v_a_1651_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1732_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v_fst_1657_; lean_object* v_snd_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1731_; 
v_fst_1657_ = lean_ctor_get(v_fst_1652_, 0);
v_snd_1658_ = lean_ctor_get(v_fst_1652_, 1);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_fst_1652_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1660_ = v_fst_1652_;
v_isShared_1661_ = v_isSharedCheck_1731_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_snd_1658_);
lean_inc(v_fst_1657_);
lean_dec(v_fst_1652_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1731_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; double v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v_toCold_1667_; uint8_t v_suppressElabErrors_1668_; lean_object* v_fileName_1669_; lean_object* v_fileMap_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1677_; 
v___x_1662_ = lean_box(0);
v___x_1663_ = lean_box(0);
v___x_1664_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0);
v___x_1665_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___closed__0));
v___x_1666_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1666_, 0, v___x_1662_);
lean_ctor_set(v___x_1666_, 1, v___x_1663_);
lean_ctor_set(v___x_1666_, 2, v___x_1665_);
lean_ctor_set_float(v___x_1666_, sizeof(void*)*3, v___x_1664_);
lean_ctor_set_float(v___x_1666_, sizeof(void*)*3 + 8, v___x_1664_);
lean_ctor_set_uint8(v___x_1666_, sizeof(void*)*3 + 16, v___x_1649_);
v_toCold_1667_ = lean_ctor_get(v___y_1641_, 0);
v_suppressElabErrors_1668_ = lean_ctor_get_uint8(v___y_1641_, sizeof(void*)*3 + 2);
v_fileName_1669_ = lean_ctor_get(v_toCold_1667_, 0);
v_fileMap_1670_ = lean_ctor_get(v_toCold_1667_, 1);
v___x_1671_ = lean_box(0);
v___x_1672_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_1673_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_1674_ = l_Lean_MessageData_nil;
v___x_1675_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1666_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
lean_ctor_set(v___x_1675_, 2, v_snd_1653_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set_tag(v___x_1660_, 8);
lean_ctor_set(v___x_1660_, 1, v___x_1675_);
lean_ctor_set(v___x_1660_, 0, v___x_1673_);
v___x_1677_ = v___x_1660_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
uint8_t v___x_1678_; lean_object* v___x_1679_; lean_object* v___y_1681_; lean_object* v___y_1682_; 
v___x_1678_ = 0;
lean_inc_ref(v_fileMap_1670_);
lean_inc_ref(v_fileName_1669_);
v___x_1679_ = l_Lean_Elab_mkMessageCore(v_fileName_1669_, v_fileMap_1670_, v___x_1677_, v___x_1678_, v_fst_1657_, v_snd_1658_);
lean_dec(v_snd_1658_);
lean_dec(v_fst_1657_);
if (v_suppressElabErrors_1668_ == 0)
{
v___y_1681_ = v___y_1641_;
v___y_1682_ = v___y_1642_;
goto v___jp_1680_;
}
else
{
lean_object* v_data_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___f_1728_; uint8_t v___x_1729_; 
v_data_1725_ = lean_ctor_get(v___x_1679_, 4);
v___x_1726_ = lean_box(v_suppressElabErrors_1668_);
v___x_1727_ = lean_box(v___x_1636_);
v___f_1728_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1728_, 0, v___x_1726_);
lean_closure_set(v___f_1728_, 1, v___x_1727_);
lean_closure_set(v___f_1728_, 2, v___x_1672_);
lean_inc(v_data_1725_);
v___x_1729_ = l_Lean_MessageData_hasTag(v___f_1728_, v_data_1725_);
if (v___x_1729_ == 0)
{
lean_dec_ref(v___x_1679_);
lean_del_object(v___x_1655_);
v_a_1645_ = v___x_1671_;
goto v___jp_1644_;
}
else
{
v___y_1681_ = v___y_1641_;
v___y_1682_ = v___y_1642_;
goto v___jp_1680_;
}
}
v___jp_1680_:
{
lean_object* v_toCold_1683_; lean_object* v_fileName_1684_; lean_object* v_pos_1685_; lean_object* v_endPos_1686_; uint8_t v_keepFullRange_1687_; uint8_t v_severity_1688_; uint8_t v_isSilent_1689_; lean_object* v_caption_1690_; lean_object* v_data_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1724_; 
v_toCold_1683_ = lean_ctor_get(v___y_1681_, 0);
v_fileName_1684_ = lean_ctor_get(v___x_1679_, 0);
v_pos_1685_ = lean_ctor_get(v___x_1679_, 1);
v_endPos_1686_ = lean_ctor_get(v___x_1679_, 2);
v_keepFullRange_1687_ = lean_ctor_get_uint8(v___x_1679_, sizeof(void*)*5);
v_severity_1688_ = lean_ctor_get_uint8(v___x_1679_, sizeof(void*)*5 + 1);
v_isSilent_1689_ = lean_ctor_get_uint8(v___x_1679_, sizeof(void*)*5 + 2);
v_caption_1690_ = lean_ctor_get(v___x_1679_, 3);
v_data_1691_ = lean_ctor_get(v___x_1679_, 4);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1693_ = v___x_1679_;
v_isShared_1694_ = v_isSharedCheck_1724_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_data_1691_);
lean_inc(v_caption_1690_);
lean_inc(v_endPos_1686_);
lean_inc(v_pos_1685_);
lean_inc(v_fileName_1684_);
lean_dec(v___x_1679_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1724_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v_currNamespace_1695_; lean_object* v_openDecls_1696_; lean_object* v___x_1698_; 
v_currNamespace_1695_ = lean_ctor_get(v_toCold_1683_, 4);
v_openDecls_1696_ = lean_ctor_get(v_toCold_1683_, 5);
lean_inc(v_openDecls_1696_);
lean_inc(v_currNamespace_1695_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 1, v_openDecls_1696_);
lean_ctor_set(v___x_1655_, 0, v_currNamespace_1695_);
v___x_1698_ = v___x_1655_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_currNamespace_1695_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_openDecls_1696_);
v___x_1698_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
lean_object* v___x_1699_; lean_object* v___x_1701_; 
v___x_1699_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
lean_ctor_set(v___x_1699_, 1, v_data_1691_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 4, v___x_1699_);
v___x_1701_ = v___x_1693_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_fileName_1684_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_pos_1685_);
lean_ctor_set(v_reuseFailAlloc_1722_, 2, v_endPos_1686_);
lean_ctor_set(v_reuseFailAlloc_1722_, 3, v_caption_1690_);
lean_ctor_set(v_reuseFailAlloc_1722_, 4, v___x_1699_);
lean_ctor_set_uint8(v_reuseFailAlloc_1722_, sizeof(void*)*5, v_keepFullRange_1687_);
lean_ctor_set_uint8(v_reuseFailAlloc_1722_, sizeof(void*)*5 + 1, v_severity_1688_);
lean_ctor_set_uint8(v_reuseFailAlloc_1722_, sizeof(void*)*5 + 2, v_isSilent_1689_);
v___x_1701_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
lean_object* v___x_1702_; lean_object* v_env_1703_; lean_object* v_nextMacroScope_1704_; lean_object* v_ngen_1705_; lean_object* v_auxDeclNGen_1706_; lean_object* v_traceState_1707_; lean_object* v_cache_1708_; lean_object* v_recordedDeps_1709_; lean_object* v_messages_1710_; lean_object* v_infoState_1711_; lean_object* v_snapshotTasks_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1721_; 
v___x_1702_ = lean_st_ref_take(v___y_1682_);
v_env_1703_ = lean_ctor_get(v___x_1702_, 0);
v_nextMacroScope_1704_ = lean_ctor_get(v___x_1702_, 1);
v_ngen_1705_ = lean_ctor_get(v___x_1702_, 2);
v_auxDeclNGen_1706_ = lean_ctor_get(v___x_1702_, 3);
v_traceState_1707_ = lean_ctor_get(v___x_1702_, 4);
v_cache_1708_ = lean_ctor_get(v___x_1702_, 5);
v_recordedDeps_1709_ = lean_ctor_get(v___x_1702_, 6);
v_messages_1710_ = lean_ctor_get(v___x_1702_, 7);
v_infoState_1711_ = lean_ctor_get(v___x_1702_, 8);
v_snapshotTasks_1712_ = lean_ctor_get(v___x_1702_, 9);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1714_ = v___x_1702_;
v_isShared_1715_ = v_isSharedCheck_1721_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_snapshotTasks_1712_);
lean_inc(v_infoState_1711_);
lean_inc(v_messages_1710_);
lean_inc(v_recordedDeps_1709_);
lean_inc(v_cache_1708_);
lean_inc(v_traceState_1707_);
lean_inc(v_auxDeclNGen_1706_);
lean_inc(v_ngen_1705_);
lean_inc(v_nextMacroScope_1704_);
lean_inc(v_env_1703_);
lean_dec(v___x_1702_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1721_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1716_; lean_object* v___x_1718_; 
v___x_1716_ = l_Lean_MessageLog_add(v___x_1701_, v_messages_1710_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 7, v___x_1716_);
v___x_1718_ = v___x_1714_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_env_1703_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v_nextMacroScope_1704_);
lean_ctor_set(v_reuseFailAlloc_1720_, 2, v_ngen_1705_);
lean_ctor_set(v_reuseFailAlloc_1720_, 3, v_auxDeclNGen_1706_);
lean_ctor_set(v_reuseFailAlloc_1720_, 4, v_traceState_1707_);
lean_ctor_set(v_reuseFailAlloc_1720_, 5, v_cache_1708_);
lean_ctor_set(v_reuseFailAlloc_1720_, 6, v_recordedDeps_1709_);
lean_ctor_set(v_reuseFailAlloc_1720_, 7, v___x_1716_);
lean_ctor_set(v_reuseFailAlloc_1720_, 8, v_infoState_1711_);
lean_ctor_set(v_reuseFailAlloc_1720_, 9, v_snapshotTasks_1712_);
v___x_1718_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
lean_object* v___x_1719_; 
v___x_1719_ = lean_st_ref_put(v___y_1682_, v___x_1718_);
v_a_1645_ = v___x_1671_;
goto v___jp_1644_;
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
v___jp_1644_:
{
size_t v___x_1646_; size_t v___x_1647_; 
v___x_1646_ = ((size_t)1ULL);
v___x_1647_ = lean_usize_add(v_i_1639_, v___x_1646_);
v_i_1639_ = v___x_1647_;
v_b_1640_ = v_a_1645_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1636_ = stack[0].m_num;
lean_object* v_as_1637_ = stack[1].m_obj;
size_t v_sz_1638_ = stack[2].m_num;
size_t v_i_1639_ = stack[3].m_num;
lean_object* v_b_1640_ = stack[4].m_obj;
lean_object* v___y_1641_ = stack[5].m_obj;
lean_object* v___y_1642_ = stack[6].m_obj;
lean_object* v_res_1733_;
v_res_1733_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(v___x_1636_, v_as_1637_, v_sz_1638_, v_i_1639_, v_b_1640_, v___y_1641_, v___y_1642_);
stack->m_obj
 = v_res_1733_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___boxed(lean_object* v___x_1734_, lean_object* v_as_1735_, lean_object* v_sz_1736_, lean_object* v_i_1737_, lean_object* v_b_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
uint8_t v___x_39730__boxed_1742_; size_t v_sz_boxed_1743_; size_t v_i_boxed_1744_; lean_object* v_res_1745_; 
v___x_39730__boxed_1742_ = lean_unbox(v___x_1734_);
v_sz_boxed_1743_ = lean_unbox_usize(v_sz_1736_);
lean_dec(v_sz_1736_);
v_i_boxed_1744_ = lean_unbox_usize(v_i_1737_);
lean_dec(v_i_1737_);
v_res_1745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(v___x_39730__boxed_1742_, v_as_1735_, v_sz_boxed_1743_, v_i_boxed_1744_, v_b_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec_ref(v_as_1735_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(lean_object* v_a_1746_, lean_object* v_fallback_1747_, lean_object* v_x_1748_){
_start:
{
if (lean_obj_tag(v_x_1748_) == 0)
{
lean_inc(v_fallback_1747_);
return v_fallback_1747_;
}
else
{
lean_object* v_key_1749_; lean_object* v_value_1750_; lean_object* v_tail_1751_; lean_object* v_fst_1752_; lean_object* v_snd_1753_; lean_object* v_fst_1754_; lean_object* v_snd_1755_; uint8_t v_decide_1756_; 
v_key_1749_ = lean_ctor_get(v_x_1748_, 0);
v_value_1750_ = lean_ctor_get(v_x_1748_, 1);
v_tail_1751_ = lean_ctor_get(v_x_1748_, 2);
v_fst_1752_ = lean_ctor_get(v_key_1749_, 0);
v_snd_1753_ = lean_ctor_get(v_key_1749_, 1);
v_fst_1754_ = lean_ctor_get(v_a_1746_, 0);
v_snd_1755_ = lean_ctor_get(v_a_1746_, 1);
v_decide_1756_ = lean_nat_dec_eq(v_fst_1752_, v_fst_1754_);
if (v_decide_1756_ == 0)
{
v_x_1748_ = v_tail_1751_;
goto _start;
}
else
{
uint8_t v_decide_1758_; 
v_decide_1758_ = lean_nat_dec_eq(v_snd_1753_, v_snd_1755_);
if (v_decide_1758_ == 0)
{
v_x_1748_ = v_tail_1751_;
goto _start;
}
else
{
lean_inc(v_value_1750_);
return v_value_1750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg___boxed(lean_object* v_a_1760_, lean_object* v_fallback_1761_, lean_object* v_x_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(v_a_1760_, v_fallback_1761_, v_x_1762_);
lean_dec(v_x_1762_);
lean_dec(v_fallback_1761_);
lean_dec_ref(v_a_1760_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(lean_object* v_m_1764_, lean_object* v_a_1765_, lean_object* v_fallback_1766_){
_start:
{
lean_object* v_buckets_1767_; lean_object* v_fst_1768_; lean_object* v_snd_1769_; lean_object* v___x_1770_; uint64_t v___x_1771_; uint64_t v___x_1772_; uint64_t v___x_1773_; uint64_t v___x_1774_; uint64_t v___x_1775_; uint64_t v_fold_1776_; uint64_t v___x_1777_; uint64_t v___x_1778_; uint64_t v___x_1779_; size_t v___x_1780_; size_t v___x_1781_; size_t v___x_1782_; size_t v___x_1783_; size_t v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v_buckets_1767_ = lean_ctor_get(v_m_1764_, 1);
v_fst_1768_ = lean_ctor_get(v_a_1765_, 0);
v_snd_1769_ = lean_ctor_get(v_a_1765_, 1);
v___x_1770_ = lean_array_get_size(v_buckets_1767_);
v___x_1771_ = l_String_instHashableRaw_hash(v_fst_1768_);
v___x_1772_ = l_String_instHashableRaw_hash(v_snd_1769_);
v___x_1773_ = lean_uint64_mix_hash(v___x_1771_, v___x_1772_);
v___x_1774_ = 32ULL;
v___x_1775_ = lean_uint64_shift_right(v___x_1773_, v___x_1774_);
v_fold_1776_ = lean_uint64_xor(v___x_1773_, v___x_1775_);
v___x_1777_ = 16ULL;
v___x_1778_ = lean_uint64_shift_right(v_fold_1776_, v___x_1777_);
v___x_1779_ = lean_uint64_xor(v_fold_1776_, v___x_1778_);
v___x_1780_ = lean_uint64_to_usize(v___x_1779_);
v___x_1781_ = lean_usize_of_nat(v___x_1770_);
v___x_1782_ = ((size_t)1ULL);
v___x_1783_ = lean_usize_sub(v___x_1781_, v___x_1782_);
v___x_1784_ = lean_usize_land(v___x_1780_, v___x_1783_);
v___x_1785_ = lean_array_uget_borrowed(v_buckets_1767_, v___x_1784_);
v___x_1786_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(v_a_1765_, v_fallback_1766_, v___x_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg___boxed(lean_object* v_m_1787_, lean_object* v_a_1788_, lean_object* v_fallback_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_m_1787_, v_a_1788_, v_fallback_1789_);
lean_dec(v_fallback_1789_);
lean_dec_ref(v_a_1788_);
lean_dec_ref(v_m_1787_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44___redArg(lean_object* v_x_1791_, lean_object* v_x_1792_){
_start:
{
if (lean_obj_tag(v_x_1792_) == 0)
{
return v_x_1791_;
}
else
{
lean_object* v_key_1793_; lean_object* v_value_1794_; lean_object* v_tail_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1822_; 
v_key_1793_ = lean_ctor_get(v_x_1792_, 0);
v_value_1794_ = lean_ctor_get(v_x_1792_, 1);
v_tail_1795_ = lean_ctor_get(v_x_1792_, 2);
v_isSharedCheck_1822_ = !lean_is_exclusive(v_x_1792_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1797_ = v_x_1792_;
v_isShared_1798_ = v_isSharedCheck_1822_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_tail_1795_);
lean_inc(v_value_1794_);
lean_inc(v_key_1793_);
lean_dec(v_x_1792_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1822_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v_fst_1799_; lean_object* v_snd_1800_; lean_object* v___x_1801_; uint64_t v___x_1802_; uint64_t v___x_1803_; uint64_t v___x_1804_; uint64_t v___x_1805_; uint64_t v___x_1806_; uint64_t v_fold_1807_; uint64_t v___x_1808_; uint64_t v___x_1809_; uint64_t v___x_1810_; size_t v___x_1811_; size_t v___x_1812_; size_t v___x_1813_; size_t v___x_1814_; size_t v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1818_; 
v_fst_1799_ = lean_ctor_get(v_key_1793_, 0);
v_snd_1800_ = lean_ctor_get(v_key_1793_, 1);
v___x_1801_ = lean_array_get_size(v_x_1791_);
v___x_1802_ = l_String_instHashableRaw_hash(v_fst_1799_);
v___x_1803_ = l_String_instHashableRaw_hash(v_snd_1800_);
v___x_1804_ = lean_uint64_mix_hash(v___x_1802_, v___x_1803_);
v___x_1805_ = 32ULL;
v___x_1806_ = lean_uint64_shift_right(v___x_1804_, v___x_1805_);
v_fold_1807_ = lean_uint64_xor(v___x_1804_, v___x_1806_);
v___x_1808_ = 16ULL;
v___x_1809_ = lean_uint64_shift_right(v_fold_1807_, v___x_1808_);
v___x_1810_ = lean_uint64_xor(v_fold_1807_, v___x_1809_);
v___x_1811_ = lean_uint64_to_usize(v___x_1810_);
v___x_1812_ = lean_usize_of_nat(v___x_1801_);
v___x_1813_ = ((size_t)1ULL);
v___x_1814_ = lean_usize_sub(v___x_1812_, v___x_1813_);
v___x_1815_ = lean_usize_land(v___x_1811_, v___x_1814_);
v___x_1816_ = lean_array_uget_borrowed(v_x_1791_, v___x_1815_);
lean_inc(v___x_1816_);
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 2, v___x_1816_);
v___x_1818_ = v___x_1797_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_key_1793_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_value_1794_);
lean_ctor_set(v_reuseFailAlloc_1821_, 2, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1819_; 
v___x_1819_ = lean_array_uset(v_x_1791_, v___x_1815_, v___x_1818_);
v_x_1791_ = v___x_1819_;
v_x_1792_ = v_tail_1795_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35___redArg(lean_object* v_i_1823_, lean_object* v_source_1824_, lean_object* v_target_1825_){
_start:
{
lean_object* v___x_1826_; uint8_t v___x_1827_; 
v___x_1826_ = lean_array_get_size(v_source_1824_);
v___x_1827_ = lean_nat_dec_lt(v_i_1823_, v___x_1826_);
if (v___x_1827_ == 0)
{
lean_dec_ref(v_source_1824_);
lean_dec(v_i_1823_);
return v_target_1825_;
}
else
{
lean_object* v_es_1828_; lean_object* v___x_1829_; lean_object* v_source_1830_; lean_object* v_target_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v_es_1828_ = lean_array_fget(v_source_1824_, v_i_1823_);
v___x_1829_ = lean_box(0);
v_source_1830_ = lean_array_fset(v_source_1824_, v_i_1823_, v___x_1829_);
v_target_1831_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44___redArg(v_target_1825_, v_es_1828_);
v___x_1832_ = lean_unsigned_to_nat(1u);
v___x_1833_ = lean_nat_add(v_i_1823_, v___x_1832_);
lean_dec(v_i_1823_);
v_i_1823_ = v___x_1833_;
v_source_1824_ = v_source_1830_;
v_target_1825_ = v_target_1831_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24___redArg(lean_object* v_data_1835_){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v_nbuckets_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1836_ = lean_array_get_size(v_data_1835_);
v___x_1837_ = lean_unsigned_to_nat(2u);
v_nbuckets_1838_ = lean_nat_mul(v___x_1836_, v___x_1837_);
v___x_1839_ = lean_unsigned_to_nat(0u);
v___x_1840_ = lean_box(0);
v___x_1841_ = lean_mk_array(v_nbuckets_1838_, v___x_1840_);
v___x_1842_ = lean_array_propagate_mark(v_data_1835_, v___x_1841_);
v___x_1843_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35___redArg(v___x_1839_, v_data_1835_, v___x_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(lean_object* v_a_1844_, lean_object* v_b_1845_, lean_object* v_x_1846_){
_start:
{
if (lean_obj_tag(v_x_1846_) == 0)
{
lean_dec(v_b_1845_);
lean_dec_ref(v_a_1844_);
return v_x_1846_;
}
else
{
lean_object* v_key_1847_; lean_object* v_value_1848_; lean_object* v_tail_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1865_; 
v_key_1847_ = lean_ctor_get(v_x_1846_, 0);
v_value_1848_ = lean_ctor_get(v_x_1846_, 1);
v_tail_1849_ = lean_ctor_get(v_x_1846_, 2);
v_isSharedCheck_1865_ = !lean_is_exclusive(v_x_1846_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1851_ = v_x_1846_;
v_isShared_1852_ = v_isSharedCheck_1865_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_tail_1849_);
lean_inc(v_value_1848_);
lean_inc(v_key_1847_);
lean_dec(v_x_1846_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1865_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v_fst_1858_; lean_object* v_snd_1859_; lean_object* v_fst_1860_; lean_object* v_snd_1861_; uint8_t v_decide_1862_; 
v_fst_1858_ = lean_ctor_get(v_key_1847_, 0);
v_snd_1859_ = lean_ctor_get(v_key_1847_, 1);
v_fst_1860_ = lean_ctor_get(v_a_1844_, 0);
v_snd_1861_ = lean_ctor_get(v_a_1844_, 1);
v_decide_1862_ = lean_nat_dec_eq(v_fst_1858_, v_fst_1860_);
if (v_decide_1862_ == 0)
{
goto v___jp_1853_;
}
else
{
uint8_t v_decide_1863_; 
v_decide_1863_ = lean_nat_dec_eq(v_snd_1859_, v_snd_1861_);
if (v_decide_1863_ == 0)
{
goto v___jp_1853_;
}
else
{
lean_object* v___x_1864_; 
lean_del_object(v___x_1851_);
lean_dec(v_value_1848_);
lean_dec(v_key_1847_);
v___x_1864_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1864_, 0, v_a_1844_);
lean_ctor_set(v___x_1864_, 1, v_b_1845_);
lean_ctor_set(v___x_1864_, 2, v_tail_1849_);
return v___x_1864_;
}
}
v___jp_1853_:
{
lean_object* v___x_1854_; lean_object* v___x_1856_; 
v___x_1854_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(v_a_1844_, v_b_1845_, v_tail_1849_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 2, v___x_1854_);
v___x_1856_ = v___x_1851_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_key_1847_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_value_1848_);
lean_ctor_set(v_reuseFailAlloc_1857_, 2, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(lean_object* v_a_1866_, lean_object* v_x_1867_){
_start:
{
if (lean_obj_tag(v_x_1867_) == 0)
{
uint8_t v___x_1868_; 
v___x_1868_ = 0;
return v___x_1868_;
}
else
{
lean_object* v_key_1869_; lean_object* v_tail_1870_; lean_object* v_fst_1871_; lean_object* v_snd_1872_; lean_object* v_fst_1873_; lean_object* v_snd_1874_; uint8_t v_decide_1875_; 
v_key_1869_ = lean_ctor_get(v_x_1867_, 0);
v_tail_1870_ = lean_ctor_get(v_x_1867_, 2);
v_fst_1871_ = lean_ctor_get(v_key_1869_, 0);
v_snd_1872_ = lean_ctor_get(v_key_1869_, 1);
v_fst_1873_ = lean_ctor_get(v_a_1866_, 0);
v_snd_1874_ = lean_ctor_get(v_a_1866_, 1);
v_decide_1875_ = lean_nat_dec_eq(v_fst_1871_, v_fst_1873_);
if (v_decide_1875_ == 0)
{
v_x_1867_ = v_tail_1870_;
goto _start;
}
else
{
uint8_t v_decide_1877_; 
v_decide_1877_ = lean_nat_dec_eq(v_snd_1872_, v_snd_1874_);
if (v_decide_1877_ == 0)
{
v_x_1867_ = v_tail_1870_;
goto _start;
}
else
{
return v_decide_1877_;
}
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1866_ = stack[0].m_obj;
lean_object* v_x_1867_ = stack[1].m_obj;
uint8_t v_res_1879_;
v_res_1879_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(v_a_1866_, v_x_1867_);
stack->m_num = v_res_1879_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg___boxed(lean_object* v_a_1880_, lean_object* v_x_1881_){
_start:
{
uint8_t v_res_1882_; lean_object* v_r_1883_; 
v_res_1882_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(v_a_1880_, v_x_1881_);
lean_dec(v_x_1881_);
lean_dec_ref(v_a_1880_);
v_r_1883_ = lean_box(v_res_1882_);
return v_r_1883_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(lean_object* v_m_1884_, lean_object* v_a_1885_, lean_object* v_b_1886_){
_start:
{
lean_object* v_size_1887_; lean_object* v_buckets_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1935_; 
v_size_1887_ = lean_ctor_get(v_m_1884_, 0);
v_buckets_1888_ = lean_ctor_get(v_m_1884_, 1);
v_isSharedCheck_1935_ = !lean_is_exclusive(v_m_1884_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1890_ = v_m_1884_;
v_isShared_1891_ = v_isSharedCheck_1935_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_buckets_1888_);
lean_inc(v_size_1887_);
lean_dec(v_m_1884_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1935_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v_fst_1892_; lean_object* v_snd_1893_; lean_object* v___x_1894_; uint64_t v___x_1895_; uint64_t v___x_1896_; uint64_t v___x_1897_; uint64_t v___x_1898_; uint64_t v___x_1899_; uint64_t v_fold_1900_; uint64_t v___x_1901_; uint64_t v___x_1902_; uint64_t v___x_1903_; size_t v___x_1904_; size_t v___x_1905_; size_t v___x_1906_; size_t v___x_1907_; size_t v___x_1908_; lean_object* v_bkt_1909_; uint8_t v___x_1910_; 
v_fst_1892_ = lean_ctor_get(v_a_1885_, 0);
v_snd_1893_ = lean_ctor_get(v_a_1885_, 1);
v___x_1894_ = lean_array_get_size(v_buckets_1888_);
v___x_1895_ = l_String_instHashableRaw_hash(v_fst_1892_);
v___x_1896_ = l_String_instHashableRaw_hash(v_snd_1893_);
v___x_1897_ = lean_uint64_mix_hash(v___x_1895_, v___x_1896_);
v___x_1898_ = 32ULL;
v___x_1899_ = lean_uint64_shift_right(v___x_1897_, v___x_1898_);
v_fold_1900_ = lean_uint64_xor(v___x_1897_, v___x_1899_);
v___x_1901_ = 16ULL;
v___x_1902_ = lean_uint64_shift_right(v_fold_1900_, v___x_1901_);
v___x_1903_ = lean_uint64_xor(v_fold_1900_, v___x_1902_);
v___x_1904_ = lean_uint64_to_usize(v___x_1903_);
v___x_1905_ = lean_usize_of_nat(v___x_1894_);
v___x_1906_ = ((size_t)1ULL);
v___x_1907_ = lean_usize_sub(v___x_1905_, v___x_1906_);
v___x_1908_ = lean_usize_land(v___x_1904_, v___x_1907_);
v_bkt_1909_ = lean_array_uget_borrowed(v_buckets_1888_, v___x_1908_);
v___x_1910_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(v_a_1885_, v_bkt_1909_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1911_; lean_object* v_size_x27_1912_; lean_object* v___x_1913_; lean_object* v_buckets_x27_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; uint8_t v___x_1920_; 
v___x_1911_ = lean_unsigned_to_nat(1u);
v_size_x27_1912_ = lean_nat_add(v_size_1887_, v___x_1911_);
lean_dec(v_size_1887_);
lean_inc(v_bkt_1909_);
v___x_1913_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1913_, 0, v_a_1885_);
lean_ctor_set(v___x_1913_, 1, v_b_1886_);
lean_ctor_set(v___x_1913_, 2, v_bkt_1909_);
v_buckets_x27_1914_ = lean_array_uset(v_buckets_1888_, v___x_1908_, v___x_1913_);
v___x_1915_ = lean_unsigned_to_nat(4u);
v___x_1916_ = lean_nat_mul(v_size_x27_1912_, v___x_1915_);
v___x_1917_ = lean_unsigned_to_nat(3u);
v___x_1918_ = lean_nat_div(v___x_1916_, v___x_1917_);
lean_dec(v___x_1916_);
v___x_1919_ = lean_array_get_size(v_buckets_x27_1914_);
v___x_1920_ = lean_nat_dec_le(v___x_1918_, v___x_1919_);
lean_dec(v___x_1918_);
if (v___x_1920_ == 0)
{
lean_object* v_val_1921_; lean_object* v___x_1923_; 
v_val_1921_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24___redArg(v_buckets_x27_1914_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 1, v_val_1921_);
lean_ctor_set(v___x_1890_, 0, v_size_x27_1912_);
v___x_1923_ = v___x_1890_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_size_x27_1912_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_val_1921_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
else
{
lean_object* v___x_1926_; 
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 1, v_buckets_x27_1914_);
lean_ctor_set(v___x_1890_, 0, v_size_x27_1912_);
v___x_1926_ = v___x_1890_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_size_x27_1912_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_buckets_x27_1914_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
else
{
lean_object* v___x_1928_; lean_object* v_buckets_x27_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1933_; 
lean_inc(v_bkt_1909_);
v___x_1928_ = lean_box(0);
v_buckets_x27_1929_ = lean_array_uset(v_buckets_1888_, v___x_1908_, v___x_1928_);
v___x_1930_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(v_a_1885_, v_b_1886_, v_bkt_1909_);
v___x_1931_ = lean_array_uset(v_buckets_x27_1929_, v___x_1908_, v___x_1930_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 1, v___x_1931_);
v___x_1933_ = v___x_1890_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_size_1887_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v___x_1931_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(uint8_t v___x_1938_, lean_object* v_as_1939_, size_t v_sz_1940_, size_t v_i_1941_, lean_object* v_b_1942_, lean_object* v___y_1943_){
_start:
{
uint8_t v___x_1945_; 
v___x_1945_ = lean_usize_dec_lt(v_i_1941_, v_sz_1940_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; 
v___x_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1946_, 0, v_b_1942_);
return v___x_1946_;
}
else
{
lean_object* v_snd_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1984_; 
v_snd_1947_ = lean_ctor_get(v_b_1942_, 1);
v_isSharedCheck_1984_ = !lean_is_exclusive(v_b_1942_);
if (v_isSharedCheck_1984_ == 0)
{
lean_object* v_unused_1985_; 
v_unused_1985_ = lean_ctor_get(v_b_1942_, 0);
lean_dec(v_unused_1985_);
v___x_1949_ = v_b_1942_;
v_isShared_1950_ = v_isSharedCheck_1984_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_snd_1947_);
lean_dec(v_b_1942_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1984_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v_ref_1951_; lean_object* v_a_1952_; lean_object* v_ref_1953_; lean_object* v_msg_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1983_; 
v_ref_1951_ = lean_ctor_get(v___y_1943_, 2);
v_a_1952_ = lean_array_uget(v_as_1939_, v_i_1941_);
v_ref_1953_ = lean_ctor_get(v_a_1952_, 0);
v_msg_1954_ = lean_ctor_get(v_a_1952_, 1);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_a_1952_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1956_ = v_a_1952_;
v_isShared_1957_ = v_isSharedCheck_1983_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_msg_1954_);
lean_inc(v_ref_1953_);
lean_dec(v_a_1952_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1983_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1958_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v_ref_1975_; lean_object* v___y_1977_; lean_object* v___x_1980_; 
v___x_1958_ = lean_box(0);
v_ref_1975_ = l_Lean_replaceRef(v_ref_1953_, v_ref_1951_);
lean_dec(v_ref_1953_);
v___x_1980_ = l_Lean_Syntax_getPos_x3f(v_ref_1975_, v___x_1938_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v___x_1981_; 
v___x_1981_ = lean_unsigned_to_nat(0u);
v___y_1977_ = v___x_1981_;
goto v___jp_1976_;
}
else
{
lean_object* v_val_1982_; 
v_val_1982_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_val_1982_);
lean_dec_ref_known(v___x_1980_, 1);
v___y_1977_ = v_val_1982_;
goto v___jp_1976_;
}
v___jp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 1, v___y_1961_);
lean_ctor_set(v___x_1949_, 0, v___y_1960_);
v___x_1963_ = v___x_1949_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v___y_1960_);
lean_ctor_set(v_reuseFailAlloc_1974_, 1, v___y_1961_);
v___x_1963_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v_pos2traces_1967_; lean_object* v___x_1969_; 
v___x_1964_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1965_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1947_, v___x_1963_, v___x_1964_);
v___x_1966_ = lean_array_push(v___x_1965_, v_msg_1954_);
v_pos2traces_1967_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_1947_, v___x_1963_, v___x_1966_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 1, v_pos2traces_1967_);
lean_ctor_set(v___x_1956_, 0, v___x_1958_);
v___x_1969_ = v___x_1956_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1958_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_pos2traces_1967_);
v___x_1969_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
size_t v___x_1970_; size_t v___x_1971_; 
v___x_1970_ = ((size_t)1ULL);
v___x_1971_ = lean_usize_add(v_i_1941_, v___x_1970_);
v_i_1941_ = v___x_1971_;
v_b_1942_ = v___x_1969_;
goto _start;
}
}
}
v___jp_1976_:
{
lean_object* v___x_1978_; 
v___x_1978_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1975_, v___x_1938_);
lean_dec(v_ref_1975_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_inc(v___y_1977_);
v___y_1960_ = v___y_1977_;
v___y_1961_ = v___y_1977_;
goto v___jp_1959_;
}
else
{
lean_object* v_val_1979_; 
v_val_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_val_1979_);
lean_dec_ref_known(v___x_1978_, 1);
v___y_1960_ = v___y_1977_;
v___y_1961_ = v_val_1979_;
goto v___jp_1959_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1938_ = stack[0].m_num;
lean_object* v_as_1939_ = stack[1].m_obj;
size_t v_sz_1940_ = stack[2].m_num;
size_t v_i_1941_ = stack[3].m_num;
lean_object* v_b_1942_ = stack[4].m_obj;
lean_object* v___y_1943_ = stack[5].m_obj;
lean_object* v_res_1986_;
v_res_1986_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(v___x_1938_, v_as_1939_, v_sz_1940_, v_i_1941_, v_b_1942_, v___y_1943_);
stack->m_obj
 = v_res_1986_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___boxed(lean_object* v___x_1987_, lean_object* v_as_1988_, lean_object* v_sz_1989_, lean_object* v_i_1990_, lean_object* v_b_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
uint8_t v___x_40401__boxed_1994_; size_t v_sz_boxed_1995_; size_t v_i_boxed_1996_; lean_object* v_res_1997_; 
v___x_40401__boxed_1994_ = lean_unbox(v___x_1987_);
v_sz_boxed_1995_ = lean_unbox_usize(v_sz_1989_);
lean_dec(v_sz_1989_);
v_i_boxed_1996_ = lean_unbox_usize(v_i_1990_);
lean_dec(v_i_1990_);
v_res_1997_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(v___x_40401__boxed_1994_, v_as_1988_, v_sz_boxed_1995_, v_i_boxed_1996_, v_b_1991_, v___y_1992_);
lean_dec_ref(v___y_1992_);
lean_dec_ref(v_as_1988_);
return v_res_1997_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40(uint8_t v___x_1998_, lean_object* v_as_1999_, size_t v_sz_2000_, size_t v_i_2001_, lean_object* v_b_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
uint8_t v___x_2006_; 
v___x_2006_ = lean_usize_dec_lt(v_i_2001_, v_sz_2000_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; 
v___x_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2007_, 0, v_b_2002_);
return v___x_2007_;
}
else
{
lean_object* v_snd_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2045_; 
v_snd_2008_ = lean_ctor_get(v_b_2002_, 1);
v_isSharedCheck_2045_ = !lean_is_exclusive(v_b_2002_);
if (v_isSharedCheck_2045_ == 0)
{
lean_object* v_unused_2046_; 
v_unused_2046_ = lean_ctor_get(v_b_2002_, 0);
lean_dec(v_unused_2046_);
v___x_2010_ = v_b_2002_;
v_isShared_2011_ = v_isSharedCheck_2045_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_snd_2008_);
lean_dec(v_b_2002_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2045_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v_ref_2012_; lean_object* v_a_2013_; lean_object* v_ref_2014_; lean_object* v_msg_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2044_; 
v_ref_2012_ = lean_ctor_get(v___y_2003_, 2);
v_a_2013_ = lean_array_uget(v_as_1999_, v_i_2001_);
v_ref_2014_ = lean_ctor_get(v_a_2013_, 0);
v_msg_2015_ = lean_ctor_get(v_a_2013_, 1);
v_isSharedCheck_2044_ = !lean_is_exclusive(v_a_2013_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2017_ = v_a_2013_;
v_isShared_2018_ = v_isSharedCheck_2044_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_msg_2015_);
lean_inc(v_ref_2014_);
lean_dec(v_a_2013_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2044_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v_ref_2036_; lean_object* v___y_2038_; lean_object* v___x_2041_; 
v___x_2019_ = lean_box(0);
v_ref_2036_ = l_Lean_replaceRef(v_ref_2014_, v_ref_2012_);
lean_dec(v_ref_2014_);
v___x_2041_ = l_Lean_Syntax_getPos_x3f(v_ref_2036_, v___x_1998_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v___x_2042_; 
v___x_2042_ = lean_unsigned_to_nat(0u);
v___y_2038_ = v___x_2042_;
goto v___jp_2037_;
}
else
{
lean_object* v_val_2043_; 
v_val_2043_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_val_2043_);
lean_dec_ref_known(v___x_2041_, 1);
v___y_2038_ = v_val_2043_;
goto v___jp_2037_;
}
v___jp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 1, v___y_2022_);
lean_ctor_set(v___x_2010_, 0, v___y_2021_);
v___x_2024_ = v___x_2010_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___y_2021_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v___y_2022_);
v___x_2024_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v_pos2traces_2028_; lean_object* v___x_2030_; 
v___x_2025_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_2026_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_2008_, v___x_2024_, v___x_2025_);
v___x_2027_ = lean_array_push(v___x_2026_, v_msg_2015_);
v_pos2traces_2028_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_2008_, v___x_2024_, v___x_2027_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 1, v_pos2traces_2028_);
lean_ctor_set(v___x_2017_, 0, v___x_2019_);
v___x_2030_ = v___x_2017_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_pos2traces_2028_);
v___x_2030_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
size_t v___x_2031_; size_t v___x_2032_; lean_object* v___x_2033_; 
v___x_2031_ = ((size_t)1ULL);
v___x_2032_ = lean_usize_add(v_i_2001_, v___x_2031_);
v___x_2033_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(v___x_1998_, v_as_1999_, v_sz_2000_, v___x_2032_, v___x_2030_, v___y_2003_);
return v___x_2033_;
}
}
}
v___jp_2037_:
{
lean_object* v___x_2039_; 
v___x_2039_ = l_Lean_Syntax_getTailPos_x3f(v_ref_2036_, v___x_1998_);
lean_dec(v_ref_2036_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_inc(v___y_2038_);
v___y_2021_ = v___y_2038_;
v___y_2022_ = v___y_2038_;
goto v___jp_2020_;
}
else
{
lean_object* v_val_2040_; 
v_val_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_val_2040_);
lean_dec_ref_known(v___x_2039_, 1);
v___y_2021_ = v___y_2038_;
v___y_2022_ = v_val_2040_;
goto v___jp_2020_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1998_ = stack[0].m_num;
lean_object* v_as_1999_ = stack[1].m_obj;
size_t v_sz_2000_ = stack[2].m_num;
size_t v_i_2001_ = stack[3].m_num;
lean_object* v_b_2002_ = stack[4].m_obj;
lean_object* v___y_2003_ = stack[5].m_obj;
lean_object* v___y_2004_ = stack[6].m_obj;
lean_object* v_res_2047_;
v_res_2047_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40(v___x_1998_, v_as_1999_, v_sz_2000_, v_i_2001_, v_b_2002_, v___y_2003_, v___y_2004_);
stack->m_obj
 = v_res_2047_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40___boxed(lean_object* v___x_2048_, lean_object* v_as_2049_, lean_object* v_sz_2050_, lean_object* v_i_2051_, lean_object* v_b_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
uint8_t v___x_40524__boxed_2056_; size_t v_sz_boxed_2057_; size_t v_i_boxed_2058_; lean_object* v_res_2059_; 
v___x_40524__boxed_2056_ = lean_unbox(v___x_2048_);
v_sz_boxed_2057_ = lean_unbox_usize(v_sz_2050_);
lean_dec(v_sz_2050_);
v_i_boxed_2058_ = lean_unbox_usize(v_i_2051_);
lean_dec(v_i_2051_);
v_res_2059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40(v___x_40524__boxed_2056_, v_as_2049_, v_sz_boxed_2057_, v_i_boxed_2058_, v_b_2052_, v___y_2053_, v___y_2054_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec_ref(v_as_2049_);
return v_res_2059_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(lean_object* v_init_2060_, uint8_t v___x_2061_, lean_object* v_n_2062_, lean_object* v_b_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
if (lean_obj_tag(v_n_2062_) == 0)
{
lean_object* v_cs_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; size_t v_sz_2070_; size_t v___x_2071_; lean_object* v___x_2072_; 
v_cs_2067_ = lean_ctor_get(v_n_2062_, 0);
v___x_2068_ = lean_box(0);
v___x_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
lean_ctor_set(v___x_2069_, 1, v_b_2063_);
v_sz_2070_ = lean_array_size(v_cs_2067_);
v___x_2071_ = ((size_t)0ULL);
v___x_2072_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39(v_init_2060_, v___x_2061_, v_cs_2067_, v_sz_2070_, v___x_2071_, v___x_2069_, v___y_2064_, v___y_2065_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2087_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2075_ = v___x_2072_;
v_isShared_2076_ = v_isSharedCheck_2087_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2072_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2087_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v_fst_2077_; 
v_fst_2077_ = lean_ctor_get(v_a_2073_, 0);
if (lean_obj_tag(v_fst_2077_) == 0)
{
lean_object* v_snd_2078_; lean_object* v___x_2079_; lean_object* v___x_2081_; 
v_snd_2078_ = lean_ctor_get(v_a_2073_, 1);
lean_inc(v_snd_2078_);
lean_dec(v_a_2073_);
v___x_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2079_, 0, v_snd_2078_);
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 0, v___x_2079_);
v___x_2081_ = v___x_2075_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
else
{
lean_object* v_val_2083_; lean_object* v___x_2085_; 
lean_inc_ref(v_fst_2077_);
lean_dec(v_a_2073_);
v_val_2083_ = lean_ctor_get(v_fst_2077_, 0);
lean_inc(v_val_2083_);
lean_dec_ref_known(v_fst_2077_, 1);
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 0, v_val_2083_);
v___x_2085_ = v___x_2075_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_val_2083_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
v_a_2088_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2072_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2072_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
else
{
lean_object* v_vs_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; size_t v_sz_2099_; size_t v___x_2100_; lean_object* v___x_2101_; 
v_vs_2096_ = lean_ctor_get(v_n_2062_, 0);
v___x_2097_ = lean_box(0);
v___x_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
lean_ctor_set(v___x_2098_, 1, v_b_2063_);
v_sz_2099_ = lean_array_size(v_vs_2096_);
v___x_2100_ = ((size_t)0ULL);
v___x_2101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40(v___x_2061_, v_vs_2096_, v_sz_2099_, v___x_2100_, v___x_2098_, v___y_2064_, v___y_2065_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2116_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2104_ = v___x_2101_;
v_isShared_2105_ = v_isSharedCheck_2116_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2101_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2116_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v_fst_2106_; 
v_fst_2106_ = lean_ctor_get(v_a_2102_, 0);
if (lean_obj_tag(v_fst_2106_) == 0)
{
lean_object* v_snd_2107_; lean_object* v___x_2108_; lean_object* v___x_2110_; 
v_snd_2107_ = lean_ctor_get(v_a_2102_, 1);
lean_inc(v_snd_2107_);
lean_dec(v_a_2102_);
v___x_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2108_, 0, v_snd_2107_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 0, v___x_2108_);
v___x_2110_ = v___x_2104_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2108_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
else
{
lean_object* v_val_2112_; lean_object* v___x_2114_; 
lean_inc_ref(v_fst_2106_);
lean_dec(v_a_2102_);
v_val_2112_ = lean_ctor_get(v_fst_2106_, 0);
lean_inc(v_val_2112_);
lean_dec_ref_known(v_fst_2106_, 1);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 0, v_val_2112_);
v___x_2114_ = v___x_2104_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_val_2112_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
else
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
v_a_2117_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___x_2101_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2101_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_2060_ = stack[0].m_obj;
uint8_t v___x_2061_ = stack[1].m_num;
lean_object* v_n_2062_ = stack[2].m_obj;
lean_object* v_b_2063_ = stack[3].m_obj;
lean_object* v___y_2064_ = stack[4].m_obj;
lean_object* v___y_2065_ = stack[5].m_obj;
lean_object* v_res_2125_;
v_res_2125_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(v_init_2060_, v___x_2061_, v_n_2062_, v_b_2063_, v___y_2064_, v___y_2065_);
stack->m_obj
 = v_res_2125_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39(lean_object* v_init_2126_, uint8_t v___x_2127_, lean_object* v_as_2128_, size_t v_sz_2129_, size_t v_i_2130_, lean_object* v_b_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
uint8_t v___x_2135_; 
v___x_2135_ = lean_usize_dec_lt(v_i_2130_, v_sz_2129_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; 
v___x_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2136_, 0, v_b_2131_);
return v___x_2136_;
}
else
{
lean_object* v_snd_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2171_; 
v_snd_2137_ = lean_ctor_get(v_b_2131_, 1);
v_isSharedCheck_2171_ = !lean_is_exclusive(v_b_2131_);
if (v_isSharedCheck_2171_ == 0)
{
lean_object* v_unused_2172_; 
v_unused_2172_ = lean_ctor_get(v_b_2131_, 0);
lean_dec(v_unused_2172_);
v___x_2139_ = v_b_2131_;
v_isShared_2140_ = v_isSharedCheck_2171_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_snd_2137_);
lean_dec(v_b_2131_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2171_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2141_; lean_object* v_a_2142_; lean_object* v___x_2143_; 
v___x_2141_ = lean_box(0);
v_a_2142_ = lean_array_uget_borrowed(v_as_2128_, v_i_2130_);
lean_inc(v_snd_2137_);
v___x_2143_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(v_init_2126_, v___x_2127_, v_a_2142_, v_snd_2137_, v___y_2132_, v___y_2133_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2162_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2146_ = v___x_2143_;
v_isShared_2147_ = v_isSharedCheck_2162_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2143_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2162_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
if (lean_obj_tag(v_a_2144_) == 0)
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
v___x_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2148_, 0, v_a_2144_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v___x_2148_);
v___x_2150_ = v___x_2139_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_snd_2137_);
v___x_2150_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
lean_object* v___x_2152_; 
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v___x_2150_);
v___x_2152_ = v___x_2146_;
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
else
{
lean_object* v_a_2155_; lean_object* v___x_2157_; 
lean_del_object(v___x_2146_);
lean_dec(v_snd_2137_);
v_a_2155_ = lean_ctor_get(v_a_2144_, 0);
lean_inc(v_a_2155_);
lean_dec_ref_known(v_a_2144_, 1);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 1, v_a_2155_);
lean_ctor_set(v___x_2139_, 0, v___x_2141_);
v___x_2157_ = v___x_2139_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2141_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_a_2155_);
v___x_2157_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
size_t v___x_2158_; size_t v___x_2159_; 
v___x_2158_ = ((size_t)1ULL);
v___x_2159_ = lean_usize_add(v_i_2130_, v___x_2158_);
v_i_2130_ = v___x_2159_;
v_b_2131_ = v___x_2157_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
lean_del_object(v___x_2139_);
lean_dec(v_snd_2137_);
v_a_2163_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2165_ = v___x_2143_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2143_);
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
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_2126_ = stack[0].m_obj;
uint8_t v___x_2127_ = stack[1].m_num;
lean_object* v_as_2128_ = stack[2].m_obj;
size_t v_sz_2129_ = stack[3].m_num;
size_t v_i_2130_ = stack[4].m_num;
lean_object* v_b_2131_ = stack[5].m_obj;
lean_object* v___y_2132_ = stack[6].m_obj;
lean_object* v___y_2133_ = stack[7].m_obj;
lean_object* v_res_2173_;
v_res_2173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39(v_init_2126_, v___x_2127_, v_as_2128_, v_sz_2129_, v_i_2130_, v_b_2131_, v___y_2132_, v___y_2133_);
stack->m_obj
 = v_res_2173_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39___boxed(lean_object* v_init_2174_, lean_object* v___x_2175_, lean_object* v_as_2176_, lean_object* v_sz_2177_, lean_object* v_i_2178_, lean_object* v_b_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
uint8_t v___x_40647__boxed_2183_; size_t v_sz_boxed_2184_; size_t v_i_boxed_2185_; lean_object* v_res_2186_; 
v___x_40647__boxed_2183_ = lean_unbox(v___x_2175_);
v_sz_boxed_2184_ = lean_unbox_usize(v_sz_2177_);
lean_dec(v_sz_2177_);
v_i_boxed_2185_ = lean_unbox_usize(v_i_2178_);
lean_dec(v_i_2178_);
v_res_2186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39(v_init_2174_, v___x_40647__boxed_2183_, v_as_2176_, v_sz_boxed_2184_, v_i_boxed_2185_, v_b_2179_, v___y_2180_, v___y_2181_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec_ref(v_as_2176_);
lean_dec_ref(v_init_2174_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27___boxed(lean_object* v_init_2187_, lean_object* v___x_2188_, lean_object* v_n_2189_, lean_object* v_b_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
uint8_t v___x_40667__boxed_2194_; lean_object* v_res_2195_; 
v___x_40667__boxed_2194_ = lean_unbox(v___x_2188_);
v_res_2195_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(v_init_2187_, v___x_40667__boxed_2194_, v_n_2189_, v_b_2190_, v___y_2191_, v___y_2192_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec_ref(v_n_2189_);
lean_dec_ref(v_init_2187_);
return v_res_2195_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(uint8_t v___x_2196_, lean_object* v_as_2197_, size_t v_sz_2198_, size_t v_i_2199_, lean_object* v_b_2200_, lean_object* v___y_2201_){
_start:
{
uint8_t v___x_2203_; 
v___x_2203_ = lean_usize_dec_lt(v_i_2199_, v_sz_2198_);
if (v___x_2203_ == 0)
{
lean_object* v___x_2204_; 
v___x_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2204_, 0, v_b_2200_);
return v___x_2204_;
}
else
{
lean_object* v_snd_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2242_; 
v_snd_2205_ = lean_ctor_get(v_b_2200_, 1);
v_isSharedCheck_2242_ = !lean_is_exclusive(v_b_2200_);
if (v_isSharedCheck_2242_ == 0)
{
lean_object* v_unused_2243_; 
v_unused_2243_ = lean_ctor_get(v_b_2200_, 0);
lean_dec(v_unused_2243_);
v___x_2207_ = v_b_2200_;
v_isShared_2208_ = v_isSharedCheck_2242_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_snd_2205_);
lean_dec(v_b_2200_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2242_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v_ref_2209_; lean_object* v_a_2210_; lean_object* v_ref_2211_; lean_object* v_msg_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2241_; 
v_ref_2209_ = lean_ctor_get(v___y_2201_, 2);
v_a_2210_ = lean_array_uget(v_as_2197_, v_i_2199_);
v_ref_2211_ = lean_ctor_get(v_a_2210_, 0);
v_msg_2212_ = lean_ctor_get(v_a_2210_, 1);
v_isSharedCheck_2241_ = !lean_is_exclusive(v_a_2210_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2214_ = v_a_2210_;
v_isShared_2215_ = v_isSharedCheck_2241_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_msg_2212_);
lean_inc(v_ref_2211_);
lean_dec(v_a_2210_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2241_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2216_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v_ref_2233_; lean_object* v___y_2235_; lean_object* v___x_2238_; 
v___x_2216_ = lean_box(0);
v_ref_2233_ = l_Lean_replaceRef(v_ref_2211_, v_ref_2209_);
lean_dec(v_ref_2211_);
v___x_2238_ = l_Lean_Syntax_getPos_x3f(v_ref_2233_, v___x_2196_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v___x_2239_; 
v___x_2239_ = lean_unsigned_to_nat(0u);
v___y_2235_ = v___x_2239_;
goto v___jp_2234_;
}
else
{
lean_object* v_val_2240_; 
v_val_2240_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_val_2240_);
lean_dec_ref_known(v___x_2238_, 1);
v___y_2235_ = v_val_2240_;
goto v___jp_2234_;
}
v___jp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 1, v___y_2219_);
lean_ctor_set(v___x_2207_, 0, v___y_2218_);
v___x_2221_ = v___x_2207_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___y_2218_);
lean_ctor_set(v_reuseFailAlloc_2232_, 1, v___y_2219_);
v___x_2221_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v_pos2traces_2225_; lean_object* v___x_2227_; 
v___x_2222_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_2223_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_2205_, v___x_2221_, v___x_2222_);
v___x_2224_ = lean_array_push(v___x_2223_, v_msg_2212_);
v_pos2traces_2225_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_2205_, v___x_2221_, v___x_2224_);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 1, v_pos2traces_2225_);
lean_ctor_set(v___x_2214_, 0, v___x_2216_);
v___x_2227_ = v___x_2214_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v___x_2216_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_pos2traces_2225_);
v___x_2227_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
size_t v___x_2228_; size_t v___x_2229_; 
v___x_2228_ = ((size_t)1ULL);
v___x_2229_ = lean_usize_add(v_i_2199_, v___x_2228_);
v_i_2199_ = v___x_2229_;
v_b_2200_ = v___x_2227_;
goto _start;
}
}
}
v___jp_2234_:
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Lean_Syntax_getTailPos_x3f(v_ref_2233_, v___x_2196_);
lean_dec(v_ref_2233_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_inc(v___y_2235_);
v___y_2218_ = v___y_2235_;
v___y_2219_ = v___y_2235_;
goto v___jp_2217_;
}
else
{
lean_object* v_val_2237_; 
v_val_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_val_2237_);
lean_dec_ref_known(v___x_2236_, 1);
v___y_2218_ = v___y_2235_;
v___y_2219_ = v_val_2237_;
goto v___jp_2217_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2196_ = stack[0].m_num;
lean_object* v_as_2197_ = stack[1].m_obj;
size_t v_sz_2198_ = stack[2].m_num;
size_t v_i_2199_ = stack[3].m_num;
lean_object* v_b_2200_ = stack[4].m_obj;
lean_object* v___y_2201_ = stack[5].m_obj;
lean_object* v_res_2244_;
v_res_2244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(v___x_2196_, v_as_2197_, v_sz_2198_, v_i_2199_, v_b_2200_, v___y_2201_);
stack->m_obj
 = v_res_2244_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg___boxed(lean_object* v___x_2245_, lean_object* v_as_2246_, lean_object* v_sz_2247_, lean_object* v_i_2248_, lean_object* v_b_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
uint8_t v___x_40954__boxed_2252_; size_t v_sz_boxed_2253_; size_t v_i_boxed_2254_; lean_object* v_res_2255_; 
v___x_40954__boxed_2252_ = lean_unbox(v___x_2245_);
v_sz_boxed_2253_ = lean_unbox_usize(v_sz_2247_);
lean_dec(v_sz_2247_);
v_i_boxed_2254_ = lean_unbox_usize(v_i_2248_);
lean_dec(v_i_2248_);
v_res_2255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(v___x_40954__boxed_2252_, v_as_2246_, v_sz_boxed_2253_, v_i_boxed_2254_, v_b_2249_, v___y_2250_);
lean_dec_ref(v___y_2250_);
lean_dec_ref(v_as_2246_);
return v_res_2255_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28(uint8_t v___x_2256_, lean_object* v_as_2257_, size_t v_sz_2258_, size_t v_i_2259_, lean_object* v_b_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
uint8_t v___x_2264_; 
v___x_2264_ = lean_usize_dec_lt(v_i_2259_, v_sz_2258_);
if (v___x_2264_ == 0)
{
lean_object* v___x_2265_; 
v___x_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2265_, 0, v_b_2260_);
return v___x_2265_;
}
else
{
lean_object* v_snd_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2303_; 
v_snd_2266_ = lean_ctor_get(v_b_2260_, 1);
v_isSharedCheck_2303_ = !lean_is_exclusive(v_b_2260_);
if (v_isSharedCheck_2303_ == 0)
{
lean_object* v_unused_2304_; 
v_unused_2304_ = lean_ctor_get(v_b_2260_, 0);
lean_dec(v_unused_2304_);
v___x_2268_ = v_b_2260_;
v_isShared_2269_ = v_isSharedCheck_2303_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_snd_2266_);
lean_dec(v_b_2260_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2303_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v_ref_2270_; lean_object* v_a_2271_; lean_object* v_ref_2272_; lean_object* v_msg_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2302_; 
v_ref_2270_ = lean_ctor_get(v___y_2261_, 2);
v_a_2271_ = lean_array_uget(v_as_2257_, v_i_2259_);
v_ref_2272_ = lean_ctor_get(v_a_2271_, 0);
v_msg_2273_ = lean_ctor_get(v_a_2271_, 1);
v_isSharedCheck_2302_ = !lean_is_exclusive(v_a_2271_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2275_ = v_a_2271_;
v_isShared_2276_ = v_isSharedCheck_2302_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_msg_2273_);
lean_inc(v_ref_2272_);
lean_dec(v_a_2271_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2302_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2277_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v_ref_2294_; lean_object* v___y_2296_; lean_object* v___x_2299_; 
v___x_2277_ = lean_box(0);
v_ref_2294_ = l_Lean_replaceRef(v_ref_2272_, v_ref_2270_);
lean_dec(v_ref_2272_);
v___x_2299_ = l_Lean_Syntax_getPos_x3f(v_ref_2294_, v___x_2256_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v___x_2300_; 
v___x_2300_ = lean_unsigned_to_nat(0u);
v___y_2296_ = v___x_2300_;
goto v___jp_2295_;
}
else
{
lean_object* v_val_2301_; 
v_val_2301_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_val_2301_);
lean_dec_ref_known(v___x_2299_, 1);
v___y_2296_ = v_val_2301_;
goto v___jp_2295_;
}
v___jp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 1, v___y_2280_);
lean_ctor_set(v___x_2268_, 0, v___y_2279_);
v___x_2282_ = v___x_2268_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___y_2279_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v___y_2280_);
v___x_2282_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v_pos2traces_2286_; lean_object* v___x_2288_; 
v___x_2283_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_2284_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_2266_, v___x_2282_, v___x_2283_);
v___x_2285_ = lean_array_push(v___x_2284_, v_msg_2273_);
v_pos2traces_2286_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_2266_, v___x_2282_, v___x_2285_);
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 1, v_pos2traces_2286_);
lean_ctor_set(v___x_2275_, 0, v___x_2277_);
v___x_2288_ = v___x_2275_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2277_);
lean_ctor_set(v_reuseFailAlloc_2292_, 1, v_pos2traces_2286_);
v___x_2288_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
size_t v___x_2289_; size_t v___x_2290_; lean_object* v___x_2291_; 
v___x_2289_ = ((size_t)1ULL);
v___x_2290_ = lean_usize_add(v_i_2259_, v___x_2289_);
v___x_2291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(v___x_2256_, v_as_2257_, v_sz_2258_, v___x_2290_, v___x_2288_, v___y_2261_);
return v___x_2291_;
}
}
}
v___jp_2295_:
{
lean_object* v___x_2297_; 
v___x_2297_ = l_Lean_Syntax_getTailPos_x3f(v_ref_2294_, v___x_2256_);
lean_dec(v_ref_2294_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_inc(v___y_2296_);
v___y_2279_ = v___y_2296_;
v___y_2280_ = v___y_2296_;
goto v___jp_2278_;
}
else
{
lean_object* v_val_2298_; 
v_val_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_val_2298_);
lean_dec_ref_known(v___x_2297_, 1);
v___y_2279_ = v___y_2296_;
v___y_2280_ = v_val_2298_;
goto v___jp_2278_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2256_ = stack[0].m_num;
lean_object* v_as_2257_ = stack[1].m_obj;
size_t v_sz_2258_ = stack[2].m_num;
size_t v_i_2259_ = stack[3].m_num;
lean_object* v_b_2260_ = stack[4].m_obj;
lean_object* v___y_2261_ = stack[5].m_obj;
lean_object* v___y_2262_ = stack[6].m_obj;
lean_object* v_res_2305_;
v_res_2305_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28(v___x_2256_, v_as_2257_, v_sz_2258_, v_i_2259_, v_b_2260_, v___y_2261_, v___y_2262_);
stack->m_obj
 = v_res_2305_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28___boxed(lean_object* v___x_2306_, lean_object* v_as_2307_, lean_object* v_sz_2308_, lean_object* v_i_2309_, lean_object* v_b_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
uint8_t v___x_41074__boxed_2314_; size_t v_sz_boxed_2315_; size_t v_i_boxed_2316_; lean_object* v_res_2317_; 
v___x_41074__boxed_2314_ = lean_unbox(v___x_2306_);
v_sz_boxed_2315_ = lean_unbox_usize(v_sz_2308_);
lean_dec(v_sz_2308_);
v_i_boxed_2316_ = lean_unbox_usize(v_i_2309_);
lean_dec(v_i_2309_);
v_res_2317_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28(v___x_41074__boxed_2314_, v_as_2307_, v_sz_boxed_2315_, v_i_boxed_2316_, v_b_2310_, v___y_2311_, v___y_2312_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec_ref(v_as_2307_);
return v_res_2317_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(uint8_t v___x_2318_, lean_object* v_t_2319_, lean_object* v_init_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v_root_2324_; lean_object* v_tail_2325_; lean_object* v___x_2326_; 
v_root_2324_ = lean_ctor_get(v_t_2319_, 0);
v_tail_2325_ = lean_ctor_get(v_t_2319_, 1);
lean_inc_ref(v_init_2320_);
v___x_2326_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(v_init_2320_, v___x_2318_, v_root_2324_, v_init_2320_, v___y_2321_, v___y_2322_);
lean_dec_ref(v_init_2320_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2363_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2329_ = v___x_2326_;
v_isShared_2330_ = v_isSharedCheck_2363_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2326_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2363_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
if (lean_obj_tag(v_a_2327_) == 0)
{
lean_object* v_a_2331_; lean_object* v___x_2333_; 
v_a_2331_ = lean_ctor_get(v_a_2327_, 0);
lean_inc(v_a_2331_);
lean_dec_ref_known(v_a_2327_, 1);
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 0, v_a_2331_);
v___x_2333_ = v___x_2329_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2331_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; size_t v_sz_2338_; size_t v___x_2339_; lean_object* v___x_2340_; 
lean_del_object(v___x_2329_);
v_a_2335_ = lean_ctor_get(v_a_2327_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v_a_2327_, 1);
v___x_2336_ = lean_box(0);
v___x_2337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
lean_ctor_set(v___x_2337_, 1, v_a_2335_);
v_sz_2338_ = lean_array_size(v_tail_2325_);
v___x_2339_ = ((size_t)0ULL);
v___x_2340_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28(v___x_2318_, v_tail_2325_, v_sz_2338_, v___x_2339_, v___x_2337_, v___y_2321_, v___y_2322_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2354_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2343_ = v___x_2340_;
v_isShared_2344_ = v_isSharedCheck_2354_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2340_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2354_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v_fst_2345_; 
v_fst_2345_ = lean_ctor_get(v_a_2341_, 0);
if (lean_obj_tag(v_fst_2345_) == 0)
{
lean_object* v_snd_2346_; lean_object* v___x_2348_; 
v_snd_2346_ = lean_ctor_get(v_a_2341_, 1);
lean_inc(v_snd_2346_);
lean_dec(v_a_2341_);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 0, v_snd_2346_);
v___x_2348_ = v___x_2343_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_snd_2346_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
else
{
lean_object* v_val_2350_; lean_object* v___x_2352_; 
lean_inc_ref(v_fst_2345_);
lean_dec(v_a_2341_);
v_val_2350_ = lean_ctor_get(v_fst_2345_, 0);
lean_inc(v_val_2350_);
lean_dec_ref_known(v_fst_2345_, 1);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 0, v_val_2350_);
v___x_2352_ = v___x_2343_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_val_2350_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
v_a_2355_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2340_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2340_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
v_a_2364_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2326_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2326_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2318_ = stack[0].m_num;
lean_object* v_t_2319_ = stack[1].m_obj;
lean_object* v_init_2320_ = stack[2].m_obj;
lean_object* v___y_2321_ = stack[3].m_obj;
lean_object* v___y_2322_ = stack[4].m_obj;
lean_object* v_res_2372_;
v_res_2372_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(v___x_2318_, v_t_2319_, v_init_2320_, v___y_2321_, v___y_2322_);
stack->m_obj
 = v_res_2372_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___boxed(lean_object* v___x_2373_, lean_object* v_t_2374_, lean_object* v_init_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
uint8_t v___x_41197__boxed_2379_; lean_object* v_res_2380_; 
v___x_41197__boxed_2379_ = lean_unbox(v___x_2373_);
v_res_2380_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(v___x_41197__boxed_2379_, v_t_2374_, v_init_2375_, v___y_2376_, v___y_2377_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec_ref(v_t_2374_);
return v_res_2380_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0(void){
_start:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2381_ = lean_unsigned_to_nat(32u);
v___x_2382_ = lean_mk_empty_array_with_capacity(v___x_2381_);
v___x_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
return v___x_2383_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1(void){
_start:
{
size_t v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2384_ = ((size_t)5ULL);
v___x_2385_ = lean_unsigned_to_nat(0u);
v___x_2386_ = lean_unsigned_to_nat(32u);
v___x_2387_ = lean_mk_empty_array_with_capacity(v___x_2386_);
v___x_2388_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0);
v___x_2389_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
lean_ctor_set(v___x_2389_, 1, v___x_2387_);
lean_ctor_set(v___x_2389_, 2, v___x_2385_);
lean_ctor_set(v___x_2389_, 3, v___x_2385_);
lean_ctor_set_usize(v___x_2389_, 4, v___x_2384_);
return v___x_2389_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(lean_object* v___y_2390_){
_start:
{
lean_object* v___x_2392_; lean_object* v_traceState_2393_; lean_object* v_traces_2394_; lean_object* v___x_2395_; lean_object* v_traceState_2396_; lean_object* v_env_2397_; lean_object* v_nextMacroScope_2398_; lean_object* v_ngen_2399_; lean_object* v_auxDeclNGen_2400_; lean_object* v_cache_2401_; lean_object* v_recordedDeps_2402_; lean_object* v_messages_2403_; lean_object* v_infoState_2404_; lean_object* v_snapshotTasks_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2424_; 
v___x_2392_ = lean_st_ref_get(v___y_2390_);
v_traceState_2393_ = lean_ctor_get(v___x_2392_, 4);
lean_inc_ref(v_traceState_2393_);
lean_dec(v___x_2392_);
v_traces_2394_ = lean_ctor_get(v_traceState_2393_, 0);
lean_inc_ref(v_traces_2394_);
lean_dec_ref(v_traceState_2393_);
v___x_2395_ = lean_st_ref_take(v___y_2390_);
v_traceState_2396_ = lean_ctor_get(v___x_2395_, 4);
v_env_2397_ = lean_ctor_get(v___x_2395_, 0);
v_nextMacroScope_2398_ = lean_ctor_get(v___x_2395_, 1);
v_ngen_2399_ = lean_ctor_get(v___x_2395_, 2);
v_auxDeclNGen_2400_ = lean_ctor_get(v___x_2395_, 3);
v_cache_2401_ = lean_ctor_get(v___x_2395_, 5);
v_recordedDeps_2402_ = lean_ctor_get(v___x_2395_, 6);
v_messages_2403_ = lean_ctor_get(v___x_2395_, 7);
v_infoState_2404_ = lean_ctor_get(v___x_2395_, 8);
v_snapshotTasks_2405_ = lean_ctor_get(v___x_2395_, 9);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2407_ = v___x_2395_;
v_isShared_2408_ = v_isSharedCheck_2424_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_snapshotTasks_2405_);
lean_inc(v_infoState_2404_);
lean_inc(v_messages_2403_);
lean_inc(v_recordedDeps_2402_);
lean_inc(v_cache_2401_);
lean_inc(v_traceState_2396_);
lean_inc(v_auxDeclNGen_2400_);
lean_inc(v_ngen_2399_);
lean_inc(v_nextMacroScope_2398_);
lean_inc(v_env_2397_);
lean_dec(v___x_2395_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2424_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
uint64_t v_tid_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2422_; 
v_tid_2409_ = lean_ctor_get_uint64(v_traceState_2396_, sizeof(void*)*1);
v_isSharedCheck_2422_ = !lean_is_exclusive(v_traceState_2396_);
if (v_isSharedCheck_2422_ == 0)
{
lean_object* v_unused_2423_; 
v_unused_2423_ = lean_ctor_get(v_traceState_2396_, 0);
lean_dec(v_unused_2423_);
v___x_2411_ = v_traceState_2396_;
v_isShared_2412_ = v_isSharedCheck_2422_;
goto v_resetjp_2410_;
}
else
{
lean_dec(v_traceState_2396_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2422_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2413_; lean_object* v___x_2415_; 
v___x_2413_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 0, v___x_2413_);
v___x_2415_ = v___x_2411_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v___x_2413_);
lean_ctor_set_uint64(v_reuseFailAlloc_2421_, sizeof(void*)*1, v_tid_2409_);
v___x_2415_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
lean_object* v___x_2417_; 
if (v_isShared_2408_ == 0)
{
lean_ctor_set(v___x_2407_, 4, v___x_2415_);
v___x_2417_ = v___x_2407_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_env_2397_);
lean_ctor_set(v_reuseFailAlloc_2420_, 1, v_nextMacroScope_2398_);
lean_ctor_set(v_reuseFailAlloc_2420_, 2, v_ngen_2399_);
lean_ctor_set(v_reuseFailAlloc_2420_, 3, v_auxDeclNGen_2400_);
lean_ctor_set(v_reuseFailAlloc_2420_, 4, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2420_, 5, v_cache_2401_);
lean_ctor_set(v_reuseFailAlloc_2420_, 6, v_recordedDeps_2402_);
lean_ctor_set(v_reuseFailAlloc_2420_, 7, v_messages_2403_);
lean_ctor_set(v_reuseFailAlloc_2420_, 8, v_infoState_2404_);
lean_ctor_set(v_reuseFailAlloc_2420_, 9, v_snapshotTasks_2405_);
v___x_2417_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = lean_st_ref_put(v___y_2390_, v___x_2417_);
v___x_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2419_, 0, v_traces_2394_);
return v___x_2419_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2390_ = stack[0].m_obj;
lean_object* v_res_2425_;
v_res_2425_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___y_2390_);
stack->m_obj
 = v_res_2425_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___boxed(lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___y_2426_);
lean_dec(v___y_2426_);
return v_res_2428_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0(void){
_start:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2429_ = lean_box(0);
v___x_2430_ = lean_unsigned_to_nat(16u);
v___x_2431_ = lean_mk_array(v___x_2430_, v___x_2429_);
return v___x_2431_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1(void){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v_pos2traces_2434_; 
v___x_2432_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0, &l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0);
v___x_2433_ = lean_unsigned_to_nat(0u);
v_pos2traces_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_2434_, 0, v___x_2433_);
lean_ctor_set(v_pos2traces_2434_, 1, v___x_2432_);
return v_pos2traces_2434_;
}
}
lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9(lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
lean_object* v_toCold_2441_; lean_object* v_options_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v_toCold_2441_ = lean_ctor_get(v___y_2435_, 0);
v_options_2442_ = lean_ctor_get(v_toCold_2441_, 2);
v___x_2443_ = l_Lean_trace_profiler_output;
v___x_2444_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(v_options_2442_, v___x_2443_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v___x_2445_; uint8_t v___x_2446_; 
v___x_2445_ = l_Lean_trace_profiler_serve;
v___x_2446_ = l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(v_options_2442_, v___x_2445_);
if (v___x_2446_ == 0)
{
lean_object* v___x_2447_; lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2510_; 
v___x_2447_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___y_2436_);
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2450_ = v___x_2447_;
v_isShared_2451_ = v_isSharedCheck_2510_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2447_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2510_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
uint8_t v___x_2452_; 
v___x_2452_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_2448_);
if (v___x_2452_ == 0)
{
lean_object* v___x_2453_; lean_object* v_pos2traces_2454_; lean_object* v___x_2455_; 
lean_del_object(v___x_2450_);
v___x_2453_ = lean_unsigned_to_nat(0u);
v_pos2traces_2454_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1, &l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1);
v___x_2455_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(v___x_2452_, v_a_2448_, v_pos2traces_2454_, v___y_2435_, v___y_2436_);
lean_dec(v_a_2448_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v___y_2458_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2484_; lean_object* v_size_2490_; lean_object* v_buckets_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; uint8_t v___x_2494_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2456_);
lean_dec_ref_known(v___x_2455_, 1);
v_size_2490_ = lean_ctor_get(v_a_2456_, 0);
lean_inc(v_size_2490_);
v_buckets_2491_ = lean_ctor_get(v_a_2456_, 1);
lean_inc_ref(v_buckets_2491_);
lean_dec(v_a_2456_);
v___x_2492_ = lean_mk_empty_array_with_capacity(v_size_2490_);
lean_dec(v_size_2490_);
v___x_2493_ = lean_array_get_size(v_buckets_2491_);
v___x_2494_ = lean_nat_dec_lt(v___x_2453_, v___x_2493_);
if (v___x_2494_ == 0)
{
lean_dec_ref(v_buckets_2491_);
v___y_2484_ = v___x_2492_;
goto v___jp_2483_;
}
else
{
size_t v___x_2495_; size_t v___x_2496_; lean_object* v___x_2497_; 
v___x_2495_ = ((size_t)0ULL);
v___x_2496_ = lean_usize_of_nat(v___x_2493_);
v___x_2497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23(v_buckets_2491_, v___x_2495_, v___x_2496_, v___x_2492_);
lean_dec_ref(v_buckets_2491_);
v___y_2484_ = v___x_2497_;
goto v___jp_2483_;
}
v___jp_2457_:
{
lean_object* v___x_2459_; size_t v_sz_2460_; size_t v___x_2461_; lean_object* v___x_2462_; 
v___x_2459_ = lean_box(0);
v_sz_2460_ = lean_array_size(v___y_2458_);
v___x_2461_ = ((size_t)0ULL);
v___x_2462_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(v___x_2446_, v___y_2458_, v_sz_2460_, v___x_2461_, v___x_2459_, v___y_2435_, v___y_2436_);
lean_dec_ref(v___y_2458_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2469_ == 0)
{
lean_object* v_unused_2470_; 
v_unused_2470_ = lean_ctor_get(v___x_2462_, 0);
lean_dec(v_unused_2470_);
v___x_2464_ = v___x_2462_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_dec(v___x_2462_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v___x_2459_);
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v___x_2459_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
else
{
return v___x_2462_;
}
}
v___jp_2471_:
{
lean_object* v___x_2476_; 
v___x_2476_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v___y_2474_, v___y_2472_, v___y_2473_, v___y_2475_);
lean_dec(v___y_2475_);
lean_dec(v___y_2474_);
v___y_2458_ = v___x_2476_;
goto v___jp_2457_;
}
v___jp_2477_:
{
uint8_t v___x_2482_; 
v___x_2482_ = lean_nat_dec_le(v___y_2481_, v___y_2479_);
if (v___x_2482_ == 0)
{
lean_dec(v___y_2479_);
lean_inc(v___y_2481_);
v___y_2472_ = v___y_2478_;
v___y_2473_ = v___y_2481_;
v___y_2474_ = v___y_2480_;
v___y_2475_ = v___y_2481_;
goto v___jp_2471_;
}
else
{
v___y_2472_ = v___y_2478_;
v___y_2473_ = v___y_2481_;
v___y_2474_ = v___y_2480_;
v___y_2475_ = v___y_2479_;
goto v___jp_2471_;
}
}
v___jp_2483_:
{
lean_object* v___x_2485_; uint8_t v___x_2486_; 
v___x_2485_ = lean_array_get_size(v___y_2484_);
v___x_2486_ = lean_nat_dec_eq(v___x_2485_, v___x_2453_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; lean_object* v___x_2488_; uint8_t v___x_2489_; 
v___x_2487_ = lean_unsigned_to_nat(1u);
v___x_2488_ = lean_nat_sub(v___x_2485_, v___x_2487_);
v___x_2489_ = lean_nat_dec_le(v___x_2453_, v___x_2488_);
if (v___x_2489_ == 0)
{
lean_inc(v___x_2488_);
v___y_2478_ = v___y_2484_;
v___y_2479_ = v___x_2488_;
v___y_2480_ = v___x_2485_;
v___y_2481_ = v___x_2488_;
goto v___jp_2477_;
}
else
{
v___y_2478_ = v___y_2484_;
v___y_2479_ = v___x_2488_;
v___y_2480_ = v___x_2485_;
v___y_2481_ = v___x_2453_;
goto v___jp_2477_;
}
}
else
{
v___y_2458_ = v___y_2484_;
goto v___jp_2457_;
}
}
}
else
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
v_a_2498_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2500_ = v___x_2455_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2455_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
else
{
lean_object* v___x_2506_; lean_object* v___x_2508_; 
lean_dec(v_a_2448_);
v___x_2506_ = lean_box(0);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 0, v___x_2506_);
v___x_2508_ = v___x_2450_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2506_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
else
{
goto v___jp_2438_;
}
}
else
{
lean_dec_ref_known(v___x_2444_, 1);
goto v___jp_2438_;
}
v___jp_2438_:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2439_ = lean_box(0);
v___x_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
return v___x_2440_;
}
}
}
LEAN_EXPORT void l_Lean_addTraceAsMessages___at___00main_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2435_ = stack[0].m_obj;
lean_object* v___y_2436_ = stack[1].m_obj;
lean_object* v_res_2511_;
v_res_2511_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2435_, v___y_2436_);
stack->m_obj
 = v_res_2511_;
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9___boxed(lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2512_, v___y_2513_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
return v_res_2515_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(lean_object* v_as_2516_, size_t v_sz_2517_, size_t v_i_2518_, lean_object* v_b_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
uint8_t v___x_2523_; 
v___x_2523_ = lean_usize_dec_lt(v_i_2518_, v_sz_2517_);
if (v___x_2523_ == 0)
{
lean_object* v___x_2524_; 
v___x_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2524_, 0, v_b_2519_);
return v___x_2524_;
}
else
{
lean_object* v___x_2525_; lean_object* v_a_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2525_ = lean_box(0);
v_a_2526_ = lean_array_uget_borrowed(v_as_2516_, v_i_2518_);
v___x_2527_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2520_);
lean_inc(v_a_2526_);
v___x_2528_ = l_Lean_Compiler_LCNF_resumeCompilation(v_a_2526_, v___x_2527_, v___y_2520_, v___y_2521_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v___x_2529_; 
lean_dec_ref_known(v___x_2528_, 1);
v___x_2529_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2520_, v___y_2521_);
if (lean_obj_tag(v___x_2529_) == 0)
{
size_t v___x_2530_; size_t v___x_2531_; 
lean_dec_ref_known(v___x_2529_, 1);
v___x_2530_ = ((size_t)1ULL);
v___x_2531_ = lean_usize_add(v_i_2518_, v___x_2530_);
v_i_2518_ = v___x_2531_;
v_b_2519_ = v___x_2525_;
goto _start;
}
else
{
return v___x_2529_;
}
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2534_; 
v_a_2533_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2533_);
lean_dec_ref_known(v___x_2528_, 1);
v___x_2534_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2520_, v___y_2521_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2541_ == 0)
{
lean_object* v_unused_2542_; 
v_unused_2542_ = lean_ctor_get(v___x_2534_, 0);
lean_dec(v_unused_2542_);
v___x_2536_ = v___x_2534_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_dec(v___x_2534_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
lean_ctor_set_tag(v___x_2536_, 1);
lean_ctor_set(v___x_2536_, 0, v_a_2533_);
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2533_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
else
{
lean_dec(v_a_2533_);
return v___x_2534_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2516_ = stack[0].m_obj;
size_t v_sz_2517_ = stack[1].m_num;
size_t v_i_2518_ = stack[2].m_num;
lean_object* v_b_2519_ = stack[3].m_obj;
lean_object* v___y_2520_ = stack[4].m_obj;
lean_object* v___y_2521_ = stack[5].m_obj;
lean_object* v_res_2543_;
v_res_2543_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(v_as_2516_, v_sz_2517_, v_i_2518_, v_b_2519_, v___y_2520_, v___y_2521_);
stack->m_obj
 = v_res_2543_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10___boxed(lean_object* v_as_2544_, lean_object* v_sz_2545_, lean_object* v_i_2546_, lean_object* v_b_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
size_t v_sz_boxed_2551_; size_t v_i_boxed_2552_; lean_object* v_res_2553_; 
v_sz_boxed_2551_ = lean_unbox_usize(v_sz_2545_);
lean_dec(v_sz_2545_);
v_i_boxed_2552_ = lean_unbox_usize(v_i_2546_);
lean_dec(v_i_2546_);
v_res_2553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(v_as_2544_, v_sz_boxed_2551_, v_i_boxed_2552_, v_b_2547_, v___y_2548_, v___y_2549_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec_ref(v_as_2544_);
return v_res_2553_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(lean_object* v_as_2554_, size_t v_sz_2555_, size_t v_i_2556_, lean_object* v_b_2557_, lean_object* v___y_2558_){
_start:
{
uint8_t v___x_2560_; 
v___x_2560_ = lean_usize_dec_lt(v_i_2556_, v_sz_2555_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2561_; 
v___x_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2561_, 0, v_b_2557_);
return v___x_2561_;
}
else
{
uint8_t v___x_2562_; lean_object* v_a_2563_; lean_object* v___x_2564_; lean_object* v_ref_2565_; lean_object* v___x_2566_; 
lean_dec_ref(v_b_2557_);
v___x_2562_ = 0;
v_a_2563_ = lean_array_uget_borrowed(v_as_2554_, v_i_2556_);
lean_inc(v_a_2563_);
v___x_2564_ = l_Lean_Message_toString(v_a_2563_, v___x_2562_);
v_ref_2565_ = lean_ctor_get(v___y_2558_, 2);
v___x_2566_ = l_IO_eprintln___at___00main_spec__6(v___x_2564_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v___x_2567_; size_t v___x_2568_; size_t v___x_2569_; 
lean_dec_ref_known(v___x_2566_, 1);
v___x_2567_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_2568_ = ((size_t)1ULL);
v___x_2569_ = lean_usize_add(v_i_2556_, v___x_2568_);
v_i_2556_ = v___x_2569_;
v_b_2557_ = v___x_2567_;
goto _start;
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2582_; 
v_a_2571_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2573_ = v___x_2566_;
v_isShared_2574_ = v_isSharedCheck_2582_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2566_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2582_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2580_; 
v___x_2575_ = lean_io_error_to_string(v_a_2571_);
v___x_2576_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
v___x_2577_ = l_Lean_MessageData_ofFormat(v___x_2576_);
lean_inc(v_ref_2565_);
v___x_2578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2578_, 0, v_ref_2565_);
lean_ctor_set(v___x_2578_, 1, v___x_2577_);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 0, v___x_2578_);
v___x_2580_ = v___x_2573_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2578_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2554_ = stack[0].m_obj;
size_t v_sz_2555_ = stack[1].m_num;
size_t v_i_2556_ = stack[2].m_num;
lean_object* v_b_2557_ = stack[3].m_obj;
lean_object* v___y_2558_ = stack[4].m_obj;
lean_object* v_res_2583_;
v_res_2583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(v_as_2554_, v_sz_2555_, v_i_2556_, v_b_2557_, v___y_2558_);
stack->m_obj
 = v_res_2583_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg___boxed(lean_object* v_as_2584_, lean_object* v_sz_2585_, lean_object* v_i_2586_, lean_object* v_b_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
size_t v_sz_boxed_2590_; size_t v_i_boxed_2591_; lean_object* v_res_2592_; 
v_sz_boxed_2590_ = lean_unbox_usize(v_sz_2585_);
lean_dec(v_sz_2585_);
v_i_boxed_2591_ = lean_unbox_usize(v_i_2586_);
lean_dec(v_i_2586_);
v_res_2592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(v_as_2584_, v_sz_boxed_2590_, v_i_boxed_2591_, v_b_2587_, v___y_2588_);
lean_dec_ref(v___y_2588_);
lean_dec_ref(v_as_2584_);
return v_res_2592_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38(lean_object* v_as_2593_, size_t v_sz_2594_, size_t v_i_2595_, lean_object* v_b_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
uint8_t v___x_2600_; 
v___x_2600_ = lean_usize_dec_lt(v_i_2595_, v_sz_2594_);
if (v___x_2600_ == 0)
{
lean_object* v___x_2601_; 
v___x_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2601_, 0, v_b_2596_);
return v___x_2601_;
}
else
{
uint8_t v___x_2602_; lean_object* v_a_2603_; lean_object* v___x_2604_; lean_object* v_ref_2605_; lean_object* v___x_2606_; 
lean_dec_ref(v_b_2596_);
v___x_2602_ = 0;
v_a_2603_ = lean_array_uget_borrowed(v_as_2593_, v_i_2595_);
lean_inc(v_a_2603_);
v___x_2604_ = l_Lean_Message_toString(v_a_2603_, v___x_2602_);
v_ref_2605_ = lean_ctor_get(v___y_2597_, 2);
v___x_2606_ = l_IO_eprintln___at___00main_spec__6(v___x_2604_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v___x_2607_; size_t v___x_2608_; size_t v___x_2609_; lean_object* v___x_2610_; 
lean_dec_ref_known(v___x_2606_, 1);
v___x_2607_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_2608_ = ((size_t)1ULL);
v___x_2609_ = lean_usize_add(v_i_2595_, v___x_2608_);
v___x_2610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(v_as_2593_, v_sz_2594_, v___x_2609_, v___x_2607_, v___y_2597_);
return v___x_2610_;
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2622_; 
v_a_2611_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2613_ = v___x_2606_;
v_isShared_2614_ = v_isSharedCheck_2622_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2606_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2622_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2620_; 
v___x_2615_ = lean_io_error_to_string(v_a_2611_);
v___x_2616_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2615_);
v___x_2617_ = l_Lean_MessageData_ofFormat(v___x_2616_);
lean_inc(v_ref_2605_);
v___x_2618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2618_, 0, v_ref_2605_);
lean_ctor_set(v___x_2618_, 1, v___x_2617_);
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 0, v___x_2618_);
v___x_2620_ = v___x_2613_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2593_ = stack[0].m_obj;
size_t v_sz_2594_ = stack[1].m_num;
size_t v_i_2595_ = stack[2].m_num;
lean_object* v_b_2596_ = stack[3].m_obj;
lean_object* v___y_2597_ = stack[4].m_obj;
lean_object* v___y_2598_ = stack[5].m_obj;
lean_object* v_res_2623_;
v_res_2623_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38(v_as_2593_, v_sz_2594_, v_i_2595_, v_b_2596_, v___y_2597_, v___y_2598_);
stack->m_obj
 = v_res_2623_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38___boxed(lean_object* v_as_2624_, lean_object* v_sz_2625_, lean_object* v_i_2626_, lean_object* v_b_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
size_t v_sz_boxed_2631_; size_t v_i_boxed_2632_; lean_object* v_res_2633_; 
v_sz_boxed_2631_ = lean_unbox_usize(v_sz_2625_);
lean_dec(v_sz_2625_);
v_i_boxed_2632_ = lean_unbox_usize(v_i_2626_);
lean_dec(v_i_2626_);
v_res_2633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38(v_as_2624_, v_sz_boxed_2631_, v_i_boxed_2632_, v_b_2627_, v___y_2628_, v___y_2629_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec_ref(v_as_2624_);
return v_res_2633_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(lean_object* v_init_2634_, lean_object* v_n_2635_, lean_object* v_b_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
if (lean_obj_tag(v_n_2635_) == 0)
{
lean_object* v_cs_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; size_t v_sz_2643_; size_t v___x_2644_; lean_object* v___x_2645_; 
v_cs_2640_ = lean_ctor_get(v_n_2635_, 0);
v___x_2641_ = lean_box(0);
v___x_2642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2641_);
lean_ctor_set(v___x_2642_, 1, v_b_2636_);
v_sz_2643_ = lean_array_size(v_cs_2640_);
v___x_2644_ = ((size_t)0ULL);
v___x_2645_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37(v_init_2634_, v_cs_2640_, v_sz_2643_, v___x_2644_, v___x_2642_, v___y_2637_, v___y_2638_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2660_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2648_ = v___x_2645_;
v_isShared_2649_ = v_isSharedCheck_2660_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2645_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2660_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v_fst_2650_; 
v_fst_2650_ = lean_ctor_get(v_a_2646_, 0);
if (lean_obj_tag(v_fst_2650_) == 0)
{
lean_object* v_snd_2651_; lean_object* v___x_2652_; lean_object* v___x_2654_; 
v_snd_2651_ = lean_ctor_get(v_a_2646_, 1);
lean_inc(v_snd_2651_);
lean_dec(v_a_2646_);
v___x_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2652_, 0, v_snd_2651_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v___x_2652_);
v___x_2654_ = v___x_2648_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2652_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
else
{
lean_object* v_val_2656_; lean_object* v___x_2658_; 
lean_inc_ref(v_fst_2650_);
lean_dec(v_a_2646_);
v_val_2656_ = lean_ctor_get(v_fst_2650_, 0);
lean_inc(v_val_2656_);
lean_dec_ref_known(v_fst_2650_, 1);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v_val_2656_);
v___x_2658_ = v___x_2648_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_val_2656_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
v_a_2661_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2645_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2645_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
else
{
lean_object* v_vs_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; size_t v_sz_2672_; size_t v___x_2673_; lean_object* v___x_2674_; 
v_vs_2669_ = lean_ctor_get(v_n_2635_, 0);
v___x_2670_ = lean_box(0);
v___x_2671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2670_);
lean_ctor_set(v___x_2671_, 1, v_b_2636_);
v_sz_2672_ = lean_array_size(v_vs_2669_);
v___x_2673_ = ((size_t)0ULL);
v___x_2674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38(v_vs_2669_, v_sz_2672_, v___x_2673_, v___x_2671_, v___y_2637_, v___y_2638_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2689_; 
v_a_2675_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2677_ = v___x_2674_;
v_isShared_2678_ = v_isSharedCheck_2689_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2674_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2689_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v_fst_2679_; 
v_fst_2679_ = lean_ctor_get(v_a_2675_, 0);
if (lean_obj_tag(v_fst_2679_) == 0)
{
lean_object* v_snd_2680_; lean_object* v___x_2681_; lean_object* v___x_2683_; 
v_snd_2680_ = lean_ctor_get(v_a_2675_, 1);
lean_inc(v_snd_2680_);
lean_dec(v_a_2675_);
v___x_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2681_, 0, v_snd_2680_);
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 0, v___x_2681_);
v___x_2683_ = v___x_2677_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2681_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
else
{
lean_object* v_val_2685_; lean_object* v___x_2687_; 
lean_inc_ref(v_fst_2679_);
lean_dec(v_a_2675_);
v_val_2685_ = lean_ctor_get(v_fst_2679_, 0);
lean_inc(v_val_2685_);
lean_dec_ref_known(v_fst_2679_, 1);
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 0, v_val_2685_);
v___x_2687_ = v___x_2677_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_val_2685_);
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
else
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
v_a_2690_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2674_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2674_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2690_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_2634_ = stack[0].m_obj;
lean_object* v_n_2635_ = stack[1].m_obj;
lean_object* v_b_2636_ = stack[2].m_obj;
lean_object* v___y_2637_ = stack[3].m_obj;
lean_object* v___y_2638_ = stack[4].m_obj;
lean_object* v_res_2698_;
v_res_2698_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(v_init_2634_, v_n_2635_, v_b_2636_, v___y_2637_, v___y_2638_);
stack->m_obj
 = v_res_2698_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37(lean_object* v_init_2699_, lean_object* v_as_2700_, size_t v_sz_2701_, size_t v_i_2702_, lean_object* v_b_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
uint8_t v___x_2707_; 
v___x_2707_ = lean_usize_dec_lt(v_i_2702_, v_sz_2701_);
if (v___x_2707_ == 0)
{
lean_object* v___x_2708_; 
v___x_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2708_, 0, v_b_2703_);
return v___x_2708_;
}
else
{
lean_object* v_snd_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2743_; 
v_snd_2709_ = lean_ctor_get(v_b_2703_, 1);
v_isSharedCheck_2743_ = !lean_is_exclusive(v_b_2703_);
if (v_isSharedCheck_2743_ == 0)
{
lean_object* v_unused_2744_; 
v_unused_2744_ = lean_ctor_get(v_b_2703_, 0);
lean_dec(v_unused_2744_);
v___x_2711_ = v_b_2703_;
v_isShared_2712_ = v_isSharedCheck_2743_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_snd_2709_);
lean_dec(v_b_2703_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2743_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2713_; lean_object* v_a_2714_; lean_object* v___x_2715_; 
v___x_2713_ = lean_box(0);
v_a_2714_ = lean_array_uget_borrowed(v_as_2700_, v_i_2702_);
lean_inc(v_snd_2709_);
v___x_2715_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(v_init_2699_, v_a_2714_, v_snd_2709_, v___y_2704_, v___y_2705_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2734_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2718_ = v___x_2715_;
v_isShared_2719_ = v_isSharedCheck_2734_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2715_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2734_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
if (lean_obj_tag(v_a_2716_) == 0)
{
lean_object* v___x_2720_; lean_object* v___x_2722_; 
v___x_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2720_, 0, v_a_2716_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 0, v___x_2720_);
v___x_2722_ = v___x_2711_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2720_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v_snd_2709_);
v___x_2722_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
lean_object* v___x_2724_; 
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v___x_2722_);
v___x_2724_ = v___x_2718_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2727_; lean_object* v___x_2729_; 
lean_del_object(v___x_2718_);
lean_dec(v_snd_2709_);
v_a_2727_ = lean_ctor_get(v_a_2716_, 0);
lean_inc(v_a_2727_);
lean_dec_ref_known(v_a_2716_, 1);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 1, v_a_2727_);
lean_ctor_set(v___x_2711_, 0, v___x_2713_);
v___x_2729_ = v___x_2711_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v___x_2713_);
lean_ctor_set(v_reuseFailAlloc_2733_, 1, v_a_2727_);
v___x_2729_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
size_t v___x_2730_; size_t v___x_2731_; 
v___x_2730_ = ((size_t)1ULL);
v___x_2731_ = lean_usize_add(v_i_2702_, v___x_2730_);
v_i_2702_ = v___x_2731_;
v_b_2703_ = v___x_2729_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
lean_del_object(v___x_2711_);
lean_dec(v_snd_2709_);
v_a_2735_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v___x_2715_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2715_);
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
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_2699_ = stack[0].m_obj;
lean_object* v_as_2700_ = stack[1].m_obj;
size_t v_sz_2701_ = stack[2].m_num;
size_t v_i_2702_ = stack[3].m_num;
lean_object* v_b_2703_ = stack[4].m_obj;
lean_object* v___y_2704_ = stack[5].m_obj;
lean_object* v___y_2705_ = stack[6].m_obj;
lean_object* v_res_2745_;
v_res_2745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37(v_init_2699_, v_as_2700_, v_sz_2701_, v_i_2702_, v_b_2703_, v___y_2704_, v___y_2705_);
stack->m_obj
 = v_res_2745_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37___boxed(lean_object* v_init_2746_, lean_object* v_as_2747_, lean_object* v_sz_2748_, lean_object* v_i_2749_, lean_object* v_b_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
size_t v_sz_boxed_2754_; size_t v_i_boxed_2755_; lean_object* v_res_2756_; 
v_sz_boxed_2754_ = lean_unbox_usize(v_sz_2748_);
lean_dec(v_sz_2748_);
v_i_boxed_2755_ = lean_unbox_usize(v_i_2749_);
lean_dec(v_i_2749_);
v_res_2756_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37(v_init_2746_, v_as_2747_, v_sz_boxed_2754_, v_i_boxed_2755_, v_b_2750_, v___y_2751_, v___y_2752_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec_ref(v_as_2747_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26___boxed(lean_object* v_init_2757_, lean_object* v_n_2758_, lean_object* v_b_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(v_init_2757_, v_n_2758_, v_b_2759_, v___y_2760_, v___y_2761_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec_ref(v_n_2758_);
return v_res_2763_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(lean_object* v_as_2764_, size_t v_sz_2765_, size_t v_i_2766_, lean_object* v_b_2767_, lean_object* v___y_2768_){
_start:
{
uint8_t v___x_2770_; 
v___x_2770_ = lean_usize_dec_lt(v_i_2766_, v_sz_2765_);
if (v___x_2770_ == 0)
{
lean_object* v___x_2771_; 
v___x_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2771_, 0, v_b_2767_);
return v___x_2771_;
}
else
{
uint8_t v___x_2772_; lean_object* v_a_2773_; lean_object* v___x_2774_; lean_object* v_ref_2775_; lean_object* v___x_2776_; 
lean_dec_ref(v_b_2767_);
v___x_2772_ = 0;
v_a_2773_ = lean_array_uget_borrowed(v_as_2764_, v_i_2766_);
lean_inc(v_a_2773_);
v___x_2774_ = l_Lean_Message_toString(v_a_2773_, v___x_2772_);
v_ref_2775_ = lean_ctor_get(v___y_2768_, 2);
v___x_2776_ = l_IO_eprintln___at___00main_spec__6(v___x_2774_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v___x_2777_; size_t v___x_2778_; size_t v___x_2779_; 
lean_dec_ref_known(v___x_2776_, 1);
v___x_2777_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_2778_ = ((size_t)1ULL);
v___x_2779_ = lean_usize_add(v_i_2766_, v___x_2778_);
v_i_2766_ = v___x_2779_;
v_b_2767_ = v___x_2777_;
goto _start;
}
else
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2792_; 
v_a_2781_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2783_ = v___x_2776_;
v_isShared_2784_ = v_isSharedCheck_2792_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2776_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2792_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2790_; 
v___x_2785_ = lean_io_error_to_string(v_a_2781_);
v___x_2786_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
v___x_2787_ = l_Lean_MessageData_ofFormat(v___x_2786_);
lean_inc(v_ref_2775_);
v___x_2788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2788_, 0, v_ref_2775_);
lean_ctor_set(v___x_2788_, 1, v___x_2787_);
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 0, v___x_2788_);
v___x_2790_ = v___x_2783_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v___x_2788_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2764_ = stack[0].m_obj;
size_t v_sz_2765_ = stack[1].m_num;
size_t v_i_2766_ = stack[2].m_num;
lean_object* v_b_2767_ = stack[3].m_obj;
lean_object* v___y_2768_ = stack[4].m_obj;
lean_object* v_res_2793_;
v_res_2793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(v_as_2764_, v_sz_2765_, v_i_2766_, v_b_2767_, v___y_2768_);
stack->m_obj
 = v_res_2793_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg___boxed(lean_object* v_as_2794_, lean_object* v_sz_2795_, lean_object* v_i_2796_, lean_object* v_b_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
size_t v_sz_boxed_2800_; size_t v_i_boxed_2801_; lean_object* v_res_2802_; 
v_sz_boxed_2800_ = lean_unbox_usize(v_sz_2795_);
lean_dec(v_sz_2795_);
v_i_boxed_2801_ = lean_unbox_usize(v_i_2796_);
lean_dec(v_i_2796_);
v_res_2802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(v_as_2794_, v_sz_boxed_2800_, v_i_boxed_2801_, v_b_2797_, v___y_2798_);
lean_dec_ref(v___y_2798_);
lean_dec_ref(v_as_2794_);
return v_res_2802_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27(lean_object* v_as_2803_, size_t v_sz_2804_, size_t v_i_2805_, lean_object* v_b_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
uint8_t v___x_2810_; 
v___x_2810_ = lean_usize_dec_lt(v_i_2805_, v_sz_2804_);
if (v___x_2810_ == 0)
{
lean_object* v___x_2811_; 
v___x_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2811_, 0, v_b_2806_);
return v___x_2811_;
}
else
{
uint8_t v___x_2812_; lean_object* v_a_2813_; lean_object* v___x_2814_; lean_object* v_ref_2815_; lean_object* v___x_2816_; 
lean_dec_ref(v_b_2806_);
v___x_2812_ = 0;
v_a_2813_ = lean_array_uget_borrowed(v_as_2803_, v_i_2805_);
lean_inc(v_a_2813_);
v___x_2814_ = l_Lean_Message_toString(v_a_2813_, v___x_2812_);
v_ref_2815_ = lean_ctor_get(v___y_2807_, 2);
v___x_2816_ = l_IO_eprintln___at___00main_spec__6(v___x_2814_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v___x_2817_; size_t v___x_2818_; size_t v___x_2819_; lean_object* v___x_2820_; 
lean_dec_ref_known(v___x_2816_, 1);
v___x_2817_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_2818_ = ((size_t)1ULL);
v___x_2819_ = lean_usize_add(v_i_2805_, v___x_2818_);
v___x_2820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(v_as_2803_, v_sz_2804_, v___x_2819_, v___x_2817_, v___y_2807_);
return v___x_2820_;
}
else
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2832_; 
v_a_2821_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2823_ = v___x_2816_;
v_isShared_2824_ = v_isSharedCheck_2832_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2816_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2832_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2830_; 
v___x_2825_ = lean_io_error_to_string(v_a_2821_);
v___x_2826_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2825_);
v___x_2827_ = l_Lean_MessageData_ofFormat(v___x_2826_);
lean_inc(v_ref_2815_);
v___x_2828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2828_, 0, v_ref_2815_);
lean_ctor_set(v___x_2828_, 1, v___x_2827_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 0, v___x_2828_);
v___x_2830_ = v___x_2823_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2828_);
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
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2803_ = stack[0].m_obj;
size_t v_sz_2804_ = stack[1].m_num;
size_t v_i_2805_ = stack[2].m_num;
lean_object* v_b_2806_ = stack[3].m_obj;
lean_object* v___y_2807_ = stack[4].m_obj;
lean_object* v___y_2808_ = stack[5].m_obj;
lean_object* v_res_2833_;
v_res_2833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27(v_as_2803_, v_sz_2804_, v_i_2805_, v_b_2806_, v___y_2807_, v___y_2808_);
stack->m_obj
 = v_res_2833_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27___boxed(lean_object* v_as_2834_, lean_object* v_sz_2835_, lean_object* v_i_2836_, lean_object* v_b_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
size_t v_sz_boxed_2841_; size_t v_i_boxed_2842_; lean_object* v_res_2843_; 
v_sz_boxed_2841_ = lean_unbox_usize(v_sz_2835_);
lean_dec(v_sz_2835_);
v_i_boxed_2842_ = lean_unbox_usize(v_i_2836_);
lean_dec(v_i_2836_);
v_res_2843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27(v_as_2834_, v_sz_boxed_2841_, v_i_boxed_2842_, v_b_2837_, v___y_2838_, v___y_2839_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec_ref(v_as_2834_);
return v_res_2843_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__11(lean_object* v_t_2844_, lean_object* v_init_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v_root_2849_; lean_object* v_tail_2850_; lean_object* v___x_2851_; 
v_root_2849_ = lean_ctor_get(v_t_2844_, 0);
v_tail_2850_ = lean_ctor_get(v_t_2844_, 1);
v___x_2851_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(v_init_2845_, v_root_2849_, v_init_2845_, v___y_2846_, v___y_2847_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2888_; 
v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2854_ = v___x_2851_;
v_isShared_2855_ = v_isSharedCheck_2888_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2851_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2888_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
if (lean_obj_tag(v_a_2852_) == 0)
{
lean_object* v_a_2856_; lean_object* v___x_2858_; 
v_a_2856_ = lean_ctor_get(v_a_2852_, 0);
lean_inc(v_a_2856_);
lean_dec_ref_known(v_a_2852_, 1);
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 0, v_a_2856_);
v___x_2858_ = v___x_2854_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2856_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
else
{
lean_object* v_a_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; size_t v_sz_2863_; size_t v___x_2864_; lean_object* v___x_2865_; 
lean_del_object(v___x_2854_);
v_a_2860_ = lean_ctor_get(v_a_2852_, 0);
lean_inc(v_a_2860_);
lean_dec_ref_known(v_a_2852_, 1);
v___x_2861_ = lean_box(0);
v___x_2862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2861_);
lean_ctor_set(v___x_2862_, 1, v_a_2860_);
v_sz_2863_ = lean_array_size(v_tail_2850_);
v___x_2864_ = ((size_t)0ULL);
v___x_2865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27(v_tail_2850_, v_sz_2863_, v___x_2864_, v___x_2862_, v___y_2846_, v___y_2847_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2879_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2868_ = v___x_2865_;
v_isShared_2869_ = v_isSharedCheck_2879_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2865_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2879_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v_fst_2870_; 
v_fst_2870_ = lean_ctor_get(v_a_2866_, 0);
if (lean_obj_tag(v_fst_2870_) == 0)
{
lean_object* v_snd_2871_; lean_object* v___x_2873_; 
v_snd_2871_ = lean_ctor_get(v_a_2866_, 1);
lean_inc(v_snd_2871_);
lean_dec(v_a_2866_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 0, v_snd_2871_);
v___x_2873_ = v___x_2868_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_snd_2871_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
else
{
lean_object* v_val_2875_; lean_object* v___x_2877_; 
lean_inc_ref(v_fst_2870_);
lean_dec(v_a_2866_);
v_val_2875_ = lean_ctor_get(v_fst_2870_, 0);
lean_inc(v_val_2875_);
lean_dec_ref_known(v_fst_2870_, 1);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 0, v_val_2875_);
v___x_2877_ = v___x_2868_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_val_2875_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
else
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
v_a_2880_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2865_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2865_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2880_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
}
}
else
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
v_a_2889_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2851_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2851_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_a_2889_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00main_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2844_ = stack[0].m_obj;
lean_object* v_init_2845_ = stack[1].m_obj;
lean_object* v___y_2846_ = stack[2].m_obj;
lean_object* v___y_2847_ = stack[3].m_obj;
lean_object* v_res_2897_;
v_res_2897_ = l_Lean_PersistentArray_forIn___at___00main_spec__11(v_t_2844_, v_init_2845_, v___y_2846_, v___y_2847_);
stack->m_obj
 = v_res_2897_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__11___boxed(lean_object* v_t_2898_, lean_object* v_init_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l_Lean_PersistentArray_forIn___at___00main_spec__11(v_t_2898_, v_init_2899_, v___y_2900_, v___y_2901_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
lean_dec_ref(v_t_2898_);
return v_res_2903_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(lean_object* v_as_2904_, size_t v_sz_2905_, size_t v_i_2906_, lean_object* v_b_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
uint8_t v___x_2911_; 
v___x_2911_ = lean_usize_dec_lt(v_i_2906_, v_sz_2905_);
if (v___x_2911_ == 0)
{
lean_object* v___x_2912_; 
v___x_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2912_, 0, v_b_2907_);
return v___x_2912_;
}
else
{
lean_object* v_a_2913_; lean_object* v_declNames_2914_; lean_object* v___x_2915_; size_t v_sz_2916_; size_t v___x_2917_; lean_object* v___x_2918_; 
v_a_2913_ = lean_array_uget_borrowed(v_as_2904_, v_i_2906_);
v_declNames_2914_ = lean_ctor_get(v_a_2913_, 0);
v___x_2915_ = lean_box(0);
v_sz_2916_ = lean_array_size(v_declNames_2914_);
v___x_2917_ = ((size_t)0ULL);
v___x_2918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(v_declNames_2914_, v_sz_2916_, v___x_2917_, v___x_2915_, v___y_2908_, v___y_2909_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_object* v___x_2919_; 
lean_dec_ref_known(v___x_2918_, 1);
v___x_2919_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v___y_2909_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_a_2920_; lean_object* v_unreported_2921_; lean_object* v___x_2922_; 
v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
lean_inc(v_a_2920_);
lean_dec_ref_known(v___x_2919_, 1);
v_unreported_2921_ = lean_ctor_get(v_a_2920_, 1);
lean_inc_ref(v_unreported_2921_);
lean_dec(v_a_2920_);
v___x_2922_ = l_Lean_PersistentArray_forIn___at___00main_spec__11(v_unreported_2921_, v___x_2915_, v___y_2908_, v___y_2909_);
lean_dec_ref(v_unreported_2921_);
if (lean_obj_tag(v___x_2922_) == 0)
{
size_t v___x_2923_; size_t v___x_2924_; 
lean_dec_ref_known(v___x_2922_, 1);
v___x_2923_ = ((size_t)1ULL);
v___x_2924_ = lean_usize_add(v_i_2906_, v___x_2923_);
v_i_2906_ = v___x_2924_;
v_b_2907_ = v___x_2915_;
goto _start;
}
else
{
return v___x_2922_;
}
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
v_a_2926_ = lean_ctor_get(v___x_2919_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2919_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2919_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
else
{
return v___x_2918_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2904_ = stack[0].m_obj;
size_t v_sz_2905_ = stack[1].m_num;
size_t v_i_2906_ = stack[2].m_num;
lean_object* v_b_2907_ = stack[3].m_obj;
lean_object* v___y_2908_ = stack[4].m_obj;
lean_object* v___y_2909_ = stack[5].m_obj;
lean_object* v_res_2934_;
v_res_2934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(v_as_2904_, v_sz_2905_, v_i_2906_, v_b_2907_, v___y_2908_, v___y_2909_);
stack->m_obj
 = v_res_2934_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___boxed(lean_object* v_as_2935_, lean_object* v_sz_2936_, lean_object* v_i_2937_, lean_object* v_b_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
size_t v_sz_boxed_2942_; size_t v_i_boxed_2943_; lean_object* v_res_2944_; 
v_sz_boxed_2942_ = lean_unbox_usize(v_sz_2936_);
lean_dec(v_sz_2936_);
v_i_boxed_2943_ = lean_unbox_usize(v_i_2937_);
lean_dec(v_i_2937_);
v_res_2944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(v_as_2935_, v_sz_boxed_2942_, v_i_boxed_2943_, v_b_2938_, v___y_2939_, v___y_2940_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec_ref(v_as_2935_);
return v_res_2944_;
}
}
static lean_object* _init_l_main___closed__1(void){
_start:
{
lean_object* v___x_2946_; 
v___x_2946_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg();
return v___x_2946_;
}
}
static lean_object* _init_l_main___closed__2(void){
_start:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2947_ = l_Lean_instInhabitedClassState_default;
v___x_2948_ = lean_box(0);
v___x_2949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
lean_ctor_set(v___x_2949_, 1, v___x_2947_);
return v___x_2949_;
}
}
static lean_object* _init_l_main___closed__3(void){
_start:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2950_ = l_Lean_Meta_Match_Extension_instInhabitedState;
v___x_2951_ = lean_box(0);
v___x_2952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2951_);
lean_ctor_set(v___x_2952_, 1, v___x_2950_);
return v___x_2952_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_2953_; 
v___x_2953_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_2953_;
}
}
static lean_object* _init_l_main___closed__5(void){
_start:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2954_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2955_ = lean_box(0);
v___x_2956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2955_);
lean_ctor_set(v___x_2956_, 1, v___x_2954_);
return v___x_2956_;
}
}
static lean_object* _init_l_main___closed__6(void){
_start:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2957_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_2958_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2957_);
return v___x_2958_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = l_Array_instInhabited___redArg();
return v___x_2959_;
}
}
static lean_object* _init_l_main___closed__17(void){
_start:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2972_ = ((lean_object*)(l_main___closed__16));
v___x_2973_ = lean_unsigned_to_nat(27u);
v___x_2974_ = lean_unsigned_to_nat(163u);
v___x_2975_ = ((lean_object*)(l_main___closed__15));
v___x_2976_ = ((lean_object*)(l_main___closed__14));
v___x_2977_ = l_mkPanicMessageWithDecl(v___x_2976_, v___x_2975_, v___x_2974_, v___x_2973_, v___x_2972_);
return v___x_2977_;
}
}
static lean_object* _init_l_main___closed__19(void){
_start:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2979_ = ((lean_object*)(l_main___closed__16));
v___x_2980_ = lean_unsigned_to_nat(51u);
v___x_2981_ = lean_unsigned_to_nat(136u);
v___x_2982_ = ((lean_object*)(l_main___closed__15));
v___x_2983_ = ((lean_object*)(l_main___closed__14));
v___x_2984_ = l_mkPanicMessageWithDecl(v___x_2983_, v___x_2982_, v___x_2981_, v___x_2980_, v___x_2979_);
return v___x_2984_;
}
}
static lean_object* _init_l_main___closed__20(void){
_start:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2985_ = lean_unsigned_to_nat(1u);
v___x_2986_ = l_Lean_firstFrontendMacroScope;
v___x_2987_ = lean_nat_add(v___x_2986_, v___x_2985_);
return v___x_2987_;
}
}
static lean_object* _init_l_main___closed__24(void){
_start:
{
lean_object* v___x_2994_; uint64_t v___x_2995_; lean_object* v___x_2996_; 
v___x_2994_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
v___x_2995_ = 0ULL;
v___x_2996_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2996_, 0, v___x_2994_);
lean_ctor_set_uint64(v___x_2996_, sizeof(void*)*1, v___x_2995_);
return v___x_2996_;
}
}
static lean_object* _init_l_main___closed__25(void){
_start:
{
lean_object* v___x_2997_; 
v___x_2997_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2997_;
}
}
static lean_object* _init_l_main___closed__26(void){
_start:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2998_ = lean_obj_once(&l_main___closed__25, &l_main___closed__25_once, _init_l_main___closed__25);
v___x_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2998_);
return v___x_2999_;
}
}
static lean_object* _init_l_main___closed__27(void){
_start:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_3000_ = lean_obj_once(&l_main___closed__26, &l_main___closed__26_once, _init_l_main___closed__26);
v___x_3001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
lean_ctor_set(v___x_3001_, 1, v___x_3000_);
return v___x_3001_;
}
}
static lean_object* _init_l_main___closed__29(void){
_start:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3004_ = lean_unsigned_to_nat(0u);
v___x_3005_ = l_Lean_Options_empty;
v___x_3006_ = ((lean_object*)(l_main___closed__28));
v___x_3007_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3006_);
lean_ctor_set(v___x_3007_, 1, v___x_3005_);
lean_ctor_set(v___x_3007_, 2, v___x_3006_);
lean_ctor_set(v___x_3007_, 3, v___x_3004_);
lean_ctor_set(v___x_3007_, 4, v___x_3004_);
lean_ctor_set(v___x_3007_, 5, v___x_3004_);
return v___x_3007_;
}
}
static lean_object* _init_l_main___closed__30(void){
_start:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3008_ = l_Lean_NameSet_empty;
v___x_3009_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
v___x_3010_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
lean_ctor_set(v___x_3010_, 1, v___x_3009_);
lean_ctor_set(v___x_3010_, 2, v___x_3008_);
return v___x_3010_;
}
}
static lean_object* _init_l_main___closed__31(void){
_start:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; uint8_t v___x_3013_; lean_object* v___x_3014_; 
v___x_3011_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
v___x_3012_ = lean_obj_once(&l_main___closed__26, &l_main___closed__26_once, _init_l_main___closed__26);
v___x_3013_ = 1;
v___x_3014_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3014_, 0, v___x_3012_);
lean_ctor_set(v___x_3014_, 1, v___x_3012_);
lean_ctor_set(v___x_3014_, 2, v___x_3011_);
lean_ctor_set_uint8(v___x_3014_, sizeof(void*)*3, v___x_3013_);
return v___x_3014_;
}
}
static uint8_t _init_l_main___closed__35(void){
_start:
{
uint8_t v___x_3019_; uint8_t v___x_3020_; uint8_t v___x_3021_; 
v___x_3019_ = 2;
v___x_3020_ = 0;
v___x_3021_ = l_Lean_instOrdOLeanLevel_ord(v___x_3020_, v___x_3019_);
return v___x_3021_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = 0;
v___x_3023_ = lean_box_uint32(v___x_3022_);
return v___x_3023_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_3024_; lean_object* v___x_3025_; 
v___x_3024_ = 1;
v___x_3025_ = lean_box_uint32(v___x_3024_);
return v___x_3025_;
}
}
lean_object* _lean_main(lean_object* v_args_3026_){
_start:
{
if (lean_obj_tag(v_args_3026_) == 1)
{
lean_object* v_tail_3051_; 
v_tail_3051_ = lean_ctor_get(v_args_3026_, 1);
lean_inc(v_tail_3051_);
if (lean_obj_tag(v_tail_3051_) == 1)
{
lean_object* v_tail_3052_; 
v_tail_3052_ = lean_ctor_get(v_tail_3051_, 1);
lean_inc(v_tail_3052_);
if (lean_obj_tag(v_tail_3052_) == 1)
{
lean_object* v_head_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3811_; 
v_head_3053_ = lean_ctor_get(v_args_3026_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v_args_3026_);
if (v_isSharedCheck_3811_ == 0)
{
lean_object* v_unused_3812_; 
v_unused_3812_ = lean_ctor_get(v_args_3026_, 1);
lean_dec(v_unused_3812_);
v___x_3055_ = v_args_3026_;
v_isShared_3056_ = v_isSharedCheck_3811_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_head_3053_);
lean_dec(v_args_3026_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3811_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v_head_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3809_; 
v_head_3057_ = lean_ctor_get(v_tail_3051_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v_tail_3051_);
if (v_isSharedCheck_3809_ == 0)
{
lean_object* v_unused_3810_; 
v_unused_3810_ = lean_ctor_get(v_tail_3051_, 1);
lean_dec(v_unused_3810_);
v___x_3059_ = v_tail_3051_;
v_isShared_3060_ = v_isSharedCheck_3809_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_head_3057_);
lean_dec(v_tail_3051_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3809_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v_head_3061_; lean_object* v_tail_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3808_; 
v_head_3061_ = lean_ctor_get(v_tail_3052_, 0);
v_tail_3062_ = lean_ctor_get(v_tail_3052_, 1);
v_isSharedCheck_3808_ = !lean_is_exclusive(v_tail_3052_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3064_ = v_tail_3052_;
v_isShared_3065_ = v_isSharedCheck_3808_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_tail_3062_);
lean_inc(v_head_3061_);
lean_dec(v_tail_3052_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3808_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3066_ = lean_obj_once(&l_main___closed__1, &l_main___closed__1_once, _init_l_main___closed__1);
v___x_3067_ = lean_box(0);
v___x_3068_ = lean_obj_once(&l_main___closed__2, &l_main___closed__2_once, _init_l_main___closed__2);
v___x_3069_ = lean_obj_once(&l_main___closed__3, &l_main___closed__3_once, _init_l_main___closed__3);
v___x_3070_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_3071_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_3072_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_3073_ = lean_box(1);
v___x_3074_ = ((lean_object*)(l_main___closed__8));
v___x_3075_ = l_Lean_ModuleSetup_load(v_head_3053_);
lean_dec(v_head_3053_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v_a_3076_; lean_object* v_name_3077_; lean_object* v_package_x3f_3078_; lean_object* v_importArts_3079_; lean_object* v_options_3080_; lean_object* v___f_3081_; uint8_t v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3086_; 
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
lean_inc(v_a_3076_);
lean_dec_ref_known(v___x_3075_, 1);
v_name_3077_ = lean_ctor_get(v_a_3076_, 0);
lean_inc(v_name_3077_);
v_package_x3f_3078_ = lean_ctor_get(v_a_3076_, 1);
lean_inc(v_package_x3f_3078_);
v_importArts_3079_ = lean_ctor_get(v_a_3076_, 3);
lean_inc(v_importArts_3079_);
v_options_3080_ = lean_ctor_get(v_a_3076_, 6);
lean_inc(v_options_3080_);
lean_dec(v_a_3076_);
v___f_3081_ = lean_alloc_closure((void*)(l_main___lam__0), 2, 1);
lean_closure_set(v___f_3081_, 0, v_package_x3f_3078_);
v___x_3082_ = 0;
v___x_3083_ = l_Lean_LeanOptions_toOptions(v_options_3080_);
v___x_3084_ = lean_box(v___x_3082_);
if (v_isShared_3065_ == 0)
{
lean_ctor_set_tag(v___x_3064_, 0);
lean_ctor_set(v___x_3064_, 1, v___x_3083_);
lean_ctor_set(v___x_3064_, 0, v___x_3084_);
v___x_3086_ = v___x_3064_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v___x_3084_);
lean_ctor_set(v_reuseFailAlloc_3799_, 1, v___x_3083_);
v___x_3086_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
lean_object* v___x_3087_; 
v___x_3087_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_tail_3062_, v___x_3086_);
lean_dec(v_tail_3062_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_object* v_a_3088_; lean_object* v_fst_3089_; lean_object* v_snd_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3790_; 
v_a_3088_ = lean_ctor_get(v___x_3087_, 0);
lean_inc(v_a_3088_);
lean_dec_ref_known(v___x_3087_, 1);
v_fst_3089_ = lean_ctor_get(v_a_3088_, 0);
v_snd_3090_ = lean_ctor_get(v_a_3088_, 1);
v_isSharedCheck_3790_ = !lean_is_exclusive(v_a_3088_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3092_ = v_a_3088_;
v_isShared_3093_ = v_isSharedCheck_3790_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_snd_3090_);
lean_inc(v_fst_3089_);
lean_dec(v_a_3088_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3790_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3094_; uint8_t v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; uint8_t v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; uint8_t v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v_nextMacroScope_3270_; lean_object* v_ngen_3271_; lean_object* v_auxDeclNGen_3272_; lean_object* v_traceState_3273_; lean_object* v_recordedDeps_3274_; lean_object* v_messages_3275_; lean_object* v_infoState_3276_; lean_object* v_snapshotTasks_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; uint8_t v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; uint16_t v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; uint8_t v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; uint8_t v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; uint16_t v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; uint8_t v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; uint8_t v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; uint16_t v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; uint8_t v___y_3461_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; uint8_t v___y_3473_; lean_object* v___y_3474_; uint16_t v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; uint8_t v___y_3484_; uint8_t v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; uint8_t v___y_3488_; lean_object* v___x_3489_; 
v___x_3094_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_3095_ = 1;
v___x_3096_ = l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(v_snd_3090_, v___x_3094_, v___x_3095_);
v___x_3097_ = l_Lean_maxHeartbeats;
v___x_3098_ = lean_unsigned_to_nat(0u);
v___x_3099_ = l_Lean_Option_set___at___00main_spec__3(v___x_3096_, v___x_3097_, v___x_3098_);
v___x_3489_ = lean_init_search_path();
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; uint8_t v___x_3495_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3609_; uint8_t v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; lean_object* v___y_3614_; lean_object* v___y_3615_; lean_object* v___y_3616_; lean_object* v___y_3626_; lean_object* v___y_3627_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3648_; lean_object* v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3663_; lean_object* v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3678_; lean_object* v___y_3679_; uint8_t v___y_3754_; uint8_t v___x_3781_; 
lean_dec_ref_known(v___x_3489_, 1);
v___x_3490_ = ((lean_object*)(l_main___closed__18));
lean_inc(v_name_3077_);
v___x_3491_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3491_, 0, v_name_3077_);
lean_ctor_set_uint8(v___x_3491_, sizeof(void*)*1, v___x_3095_);
lean_ctor_set_uint8(v___x_3491_, sizeof(void*)*1 + 1, v___x_3095_);
lean_ctor_set_uint8(v___x_3491_, sizeof(void*)*1 + 2, v___x_3082_);
v___x_3492_ = lean_unsigned_to_nat(1u);
v___x_3493_ = lean_mk_empty_array_with_capacity(v___x_3492_);
v___x_3494_ = lean_array_push(v___x_3493_, v___x_3491_);
v___x_3495_ = 0;
v___x_3781_ = lean_uint8_once(&l_main___closed__35, &l_main___closed__35_once, _init_l_main___closed__35);
if (v___x_3781_ == 0)
{
v___y_3754_ = v___x_3095_;
goto v___jp_3753_;
}
else
{
v___y_3754_ = v___x_3082_;
goto v___jp_3753_;
}
v___jp_3496_:
{
lean_object* v___x_3501_; lean_object* v_moduleData_3502_; lean_object* v___x_3503_; uint8_t v___x_3504_; 
v___x_3501_ = l_Lean_Environment_header(v___y_3500_);
v_moduleData_3502_ = lean_ctor_get(v___x_3501_, 7);
lean_inc_ref(v_moduleData_3502_);
lean_dec_ref(v___x_3501_);
v___x_3503_ = lean_array_get_size(v_moduleData_3502_);
v___x_3504_ = lean_nat_dec_lt(v___y_3499_, v___x_3503_);
if (v___x_3504_ == 0)
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
lean_dec_ref(v_moduleData_3502_);
lean_dec_ref(v___y_3500_);
lean_dec(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec(v___y_3497_);
lean_dec_ref(v___x_3099_);
lean_del_object(v___x_3092_);
lean_dec(v_fst_3089_);
lean_dec(v_name_3077_);
lean_dec(v_head_3061_);
lean_del_object(v___x_3059_);
lean_dec(v_head_3057_);
v___x_3505_ = lean_obj_once(&l_main___closed__19, &l_main___closed__19_once, _init_l_main___closed__19);
v___x_3506_ = l_panic___at___00main_spec__5(v___x_3505_);
return v___x_3506_;
}
else
{
lean_object* v_base_3507_; lean_object* v_private_3508_; lean_object* v_header_3509_; lean_object* v_serverBaseExts_3510_; lean_object* v_checked_3511_; lean_object* v_asyncConstsMap_3512_; lean_object* v_asyncCtx_x3f_3513_; lean_object* v_importRealizationCtx_x3f_3514_; lean_object* v_localRealizationCtxMap_3515_; lean_object* v_allRealizations_3516_; uint8_t v_isExporting_3517_; uint8_t v_isRecordingDeps_3518_; lean_object* v_synthCacheRaw_x3f_3519_; lean_object* v_declChangeLog_3520_; lean_object* v_recordingConstGen_3521_; lean_object* v_constAddedGens_3522_; lean_object* v_constGen_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3606_; 
v_base_3507_ = lean_ctor_get(v___y_3500_, 0);
lean_inc_ref(v_base_3507_);
v_private_3508_ = lean_ctor_get(v_base_3507_, 0);
lean_inc(v_private_3508_);
v_header_3509_ = lean_ctor_get(v_private_3508_, 7);
lean_inc_ref(v_header_3509_);
v_serverBaseExts_3510_ = lean_ctor_get(v___y_3500_, 1);
v_checked_3511_ = lean_ctor_get(v___y_3500_, 2);
v_asyncConstsMap_3512_ = lean_ctor_get(v___y_3500_, 3);
v_asyncCtx_x3f_3513_ = lean_ctor_get(v___y_3500_, 4);
v_importRealizationCtx_x3f_3514_ = lean_ctor_get(v___y_3500_, 5);
v_localRealizationCtxMap_3515_ = lean_ctor_get(v___y_3500_, 6);
v_allRealizations_3516_ = lean_ctor_get(v___y_3500_, 7);
v_isExporting_3517_ = lean_ctor_get_uint8(v___y_3500_, sizeof(void*)*13);
v_isRecordingDeps_3518_ = lean_ctor_get_uint8(v___y_3500_, sizeof(void*)*13 + 1);
v_synthCacheRaw_x3f_3519_ = lean_ctor_get(v___y_3500_, 8);
v_declChangeLog_3520_ = lean_ctor_get(v___y_3500_, 9);
v_recordingConstGen_3521_ = lean_ctor_get(v___y_3500_, 10);
v_constAddedGens_3522_ = lean_ctor_get(v___y_3500_, 11);
v_constGen_3523_ = lean_ctor_get(v___y_3500_, 12);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___y_3500_);
if (v_isSharedCheck_3606_ == 0)
{
lean_object* v_unused_3607_; 
v_unused_3607_ = lean_ctor_get(v___y_3500_, 0);
lean_dec(v_unused_3607_);
v___x_3525_ = v___y_3500_;
v_isShared_3526_ = v_isSharedCheck_3606_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_constGen_3523_);
lean_inc(v_constAddedGens_3522_);
lean_inc(v_recordingConstGen_3521_);
lean_inc(v_declChangeLog_3520_);
lean_inc(v_synthCacheRaw_x3f_3519_);
lean_inc(v_allRealizations_3516_);
lean_inc(v_localRealizationCtxMap_3515_);
lean_inc(v_importRealizationCtx_x3f_3514_);
lean_inc(v_asyncCtx_x3f_3513_);
lean_inc(v_asyncConstsMap_3512_);
lean_inc(v_checked_3511_);
lean_inc(v_serverBaseExts_3510_);
lean_dec(v___y_3500_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3606_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v_public_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3604_; 
v_public_3527_ = lean_ctor_get(v_base_3507_, 1);
v_isSharedCheck_3604_ = !lean_is_exclusive(v_base_3507_);
if (v_isSharedCheck_3604_ == 0)
{
lean_object* v_unused_3605_; 
v_unused_3605_ = lean_ctor_get(v_base_3507_, 0);
lean_dec(v_unused_3605_);
v___x_3529_ = v_base_3507_;
v_isShared_3530_ = v_isSharedCheck_3604_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_public_3527_);
lean_dec(v_base_3507_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3604_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v_constants_3531_; uint8_t v_quotInit_3532_; lean_object* v_diagnostics_3533_; lean_object* v_const2ModIdx_3534_; lean_object* v_extensions_3535_; lean_object* v_irBaseExts_3536_; lean_object* v_extGens_3537_; lean_object* v_trackedGen_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3602_; 
v_constants_3531_ = lean_ctor_get(v_private_3508_, 0);
v_quotInit_3532_ = lean_ctor_get_uint8(v_private_3508_, sizeof(void*)*8);
v_diagnostics_3533_ = lean_ctor_get(v_private_3508_, 1);
v_const2ModIdx_3534_ = lean_ctor_get(v_private_3508_, 2);
v_extensions_3535_ = lean_ctor_get(v_private_3508_, 3);
v_irBaseExts_3536_ = lean_ctor_get(v_private_3508_, 4);
v_extGens_3537_ = lean_ctor_get(v_private_3508_, 5);
v_trackedGen_3538_ = lean_ctor_get(v_private_3508_, 6);
v_isSharedCheck_3602_ = !lean_is_exclusive(v_private_3508_);
if (v_isSharedCheck_3602_ == 0)
{
lean_object* v_unused_3603_; 
v_unused_3603_ = lean_ctor_get(v_private_3508_, 7);
lean_dec(v_unused_3603_);
v___x_3540_ = v_private_3508_;
v_isShared_3541_ = v_isSharedCheck_3602_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_trackedGen_3538_);
lean_inc(v_extGens_3537_);
lean_inc(v_irBaseExts_3536_);
lean_inc(v_extensions_3535_);
lean_inc(v_const2ModIdx_3534_);
lean_inc(v_diagnostics_3533_);
lean_inc(v_constants_3531_);
lean_dec(v_private_3508_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3602_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
uint32_t v_trustLevel_3542_; lean_object* v_mainModule_3543_; uint8_t v_isModule_3544_; lean_object* v_regions_3545_; lean_object* v_modules_3546_; lean_object* v_moduleNames_3547_; lean_object* v_moduleName2Idx_3548_; lean_object* v_importAllModules_3549_; lean_object* v_moduleData_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3600_; 
v_trustLevel_3542_ = lean_ctor_get_uint32(v_header_3509_, sizeof(void*)*8);
v_mainModule_3543_ = lean_ctor_get(v_header_3509_, 0);
v_isModule_3544_ = lean_ctor_get_uint8(v_header_3509_, sizeof(void*)*8 + 4);
v_regions_3545_ = lean_ctor_get(v_header_3509_, 2);
v_modules_3546_ = lean_ctor_get(v_header_3509_, 3);
v_moduleNames_3547_ = lean_ctor_get(v_header_3509_, 4);
v_moduleName2Idx_3548_ = lean_ctor_get(v_header_3509_, 5);
v_importAllModules_3549_ = lean_ctor_get(v_header_3509_, 6);
v_moduleData_3550_ = lean_ctor_get(v_header_3509_, 7);
v_isSharedCheck_3600_ = !lean_is_exclusive(v_header_3509_);
if (v_isSharedCheck_3600_ == 0)
{
lean_object* v_unused_3601_; 
v_unused_3601_ = lean_ctor_get(v_header_3509_, 1);
lean_dec(v_unused_3601_);
v___x_3552_ = v_header_3509_;
v_isShared_3553_ = v_isSharedCheck_3600_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_moduleData_3550_);
lean_inc(v_importAllModules_3549_);
lean_inc(v_moduleName2Idx_3548_);
lean_inc(v_moduleNames_3547_);
lean_inc(v_modules_3546_);
lean_inc(v_regions_3545_);
lean_inc(v_mainModule_3543_);
lean_dec(v_header_3509_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3600_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3554_; lean_object* v_imports_3555_; lean_object* v___x_3557_; 
v___x_3554_ = lean_array_fget(v_moduleData_3502_, v___y_3499_);
lean_dec_ref(v_moduleData_3502_);
v_imports_3555_ = lean_ctor_get(v___x_3554_, 0);
lean_inc_ref(v_imports_3555_);
lean_dec(v___x_3554_);
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 1, v_imports_3555_);
v___x_3557_ = v___x_3552_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 8, 5);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_mainModule_3543_);
lean_ctor_set(v_reuseFailAlloc_3599_, 1, v_imports_3555_);
lean_ctor_set(v_reuseFailAlloc_3599_, 2, v_regions_3545_);
lean_ctor_set(v_reuseFailAlloc_3599_, 3, v_modules_3546_);
lean_ctor_set(v_reuseFailAlloc_3599_, 4, v_moduleNames_3547_);
lean_ctor_set(v_reuseFailAlloc_3599_, 5, v_moduleName2Idx_3548_);
lean_ctor_set(v_reuseFailAlloc_3599_, 6, v_importAllModules_3549_);
lean_ctor_set(v_reuseFailAlloc_3599_, 7, v_moduleData_3550_);
lean_ctor_set_uint32(v_reuseFailAlloc_3599_, sizeof(void*)*8, v_trustLevel_3542_);
lean_ctor_set_uint8(v_reuseFailAlloc_3599_, sizeof(void*)*8 + 4, v_isModule_3544_);
v___x_3557_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
lean_object* v___x_3559_; 
if (v_isShared_3541_ == 0)
{
lean_ctor_set(v___x_3540_, 7, v___x_3557_);
v___x_3559_ = v___x_3540_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_constants_3531_);
lean_ctor_set(v_reuseFailAlloc_3598_, 1, v_diagnostics_3533_);
lean_ctor_set(v_reuseFailAlloc_3598_, 2, v_const2ModIdx_3534_);
lean_ctor_set(v_reuseFailAlloc_3598_, 3, v_extensions_3535_);
lean_ctor_set(v_reuseFailAlloc_3598_, 4, v_irBaseExts_3536_);
lean_ctor_set(v_reuseFailAlloc_3598_, 5, v_extGens_3537_);
lean_ctor_set(v_reuseFailAlloc_3598_, 6, v_trackedGen_3538_);
lean_ctor_set(v_reuseFailAlloc_3598_, 7, v___x_3557_);
lean_ctor_set_uint8(v_reuseFailAlloc_3598_, sizeof(void*)*8, v_quotInit_3532_);
v___x_3559_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
lean_object* v___x_3561_; 
if (v_isShared_3530_ == 0)
{
lean_ctor_set(v___x_3529_, 0, v___x_3559_);
v___x_3561_ = v___x_3529_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v___x_3559_);
lean_ctor_set(v_reuseFailAlloc_3597_, 1, v_public_3527_);
v___x_3561_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
lean_object* v___x_3563_; 
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 0, v___x_3561_);
v___x_3563_ = v___x_3525_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v___x_3561_);
lean_ctor_set(v_reuseFailAlloc_3596_, 1, v_serverBaseExts_3510_);
lean_ctor_set(v_reuseFailAlloc_3596_, 2, v_checked_3511_);
lean_ctor_set(v_reuseFailAlloc_3596_, 3, v_asyncConstsMap_3512_);
lean_ctor_set(v_reuseFailAlloc_3596_, 4, v_asyncCtx_x3f_3513_);
lean_ctor_set(v_reuseFailAlloc_3596_, 5, v_importRealizationCtx_x3f_3514_);
lean_ctor_set(v_reuseFailAlloc_3596_, 6, v_localRealizationCtxMap_3515_);
lean_ctor_set(v_reuseFailAlloc_3596_, 7, v_allRealizations_3516_);
lean_ctor_set(v_reuseFailAlloc_3596_, 8, v_synthCacheRaw_x3f_3519_);
lean_ctor_set(v_reuseFailAlloc_3596_, 9, v_declChangeLog_3520_);
lean_ctor_set(v_reuseFailAlloc_3596_, 10, v_recordingConstGen_3521_);
lean_ctor_set(v_reuseFailAlloc_3596_, 11, v_constAddedGens_3522_);
lean_ctor_set(v_reuseFailAlloc_3596_, 12, v_constGen_3523_);
lean_ctor_set_uint8(v_reuseFailAlloc_3596_, sizeof(void*)*13, v_isExporting_3517_);
lean_ctor_set_uint8(v_reuseFailAlloc_3596_, sizeof(void*)*13 + 1, v_isRecordingDeps_3518_);
v___x_3563_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; uint16_t v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v_env_3590_; uint8_t v___x_3591_; uint16_t v___x_3592_; uint16_t v___x_3593_; uint16_t v___x_3594_; uint8_t v___x_3595_; 
v___x_3564_ = l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
v___x_3565_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3074_, v___x_3564_, v___x_3563_, v___y_3499_, v___x_3495_);
lean_dec(v___y_3499_);
v___x_3566_ = l_Lean_instInhabitedFileMap_default;
v___x_3567_ = lean_unsigned_to_nat(1000u);
v___x_3568_ = l_Lean_Core_getMaxHeartbeats(v___x_3099_);
v___x_3569_ = l_Lean_firstFrontendMacroScope;
v___x_3570_ = lean_box(0);
v___x_3571_ = lean_box(0);
v___x_3572_ = l_Lean_OptionFlags_ofOptions(v___x_3099_);
v___x_3573_ = lean_obj_once(&l_main___closed__20, &l_main___closed__20_once, _init_l_main___closed__20);
v___x_3574_ = ((lean_object*)(l_main___closed__23));
lean_inc_n(v___y_3498_, 3);
v___x_3575_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3575_, 0, v___y_3498_);
lean_ctor_set(v___x_3575_, 1, v___x_3492_);
lean_ctor_set(v___x_3575_, 2, v___x_3067_);
v___x_3576_ = lean_obj_once(&l_main___closed__24, &l_main___closed__24_once, _init_l_main___closed__24);
v___x_3577_ = lean_obj_once(&l_main___closed__27, &l_main___closed__27_once, _init_l_main___closed__27);
v___x_3578_ = ((lean_object*)(l_main___closed__28));
v___x_3579_ = l_Lean_Options_empty;
v___x_3580_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_3581_ = lean_obj_once(&l_main___closed__30, &l_main___closed__30_once, _init_l_main___closed__30);
v___x_3582_ = lean_obj_once(&l_main___closed__31, &l_main___closed__31_once, _init_l_main___closed__31);
lean_inc_ref(v___x_3575_);
v___x_3583_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3583_, 0, v___x_3563_);
lean_ctor_set(v___x_3583_, 1, v___x_3573_);
lean_ctor_set(v___x_3583_, 2, v___x_3574_);
lean_ctor_set(v___x_3583_, 3, v___x_3575_);
lean_ctor_set(v___x_3583_, 4, v___x_3576_);
lean_ctor_set(v___x_3583_, 5, v___x_3577_);
lean_ctor_set(v___x_3583_, 6, v___x_3580_);
lean_ctor_set(v___x_3583_, 7, v___x_3581_);
lean_ctor_set(v___x_3583_, 8, v___x_3582_);
lean_ctor_set(v___x_3583_, 9, v___x_3578_);
v___x_3584_ = lean_st_mk_ref(v___x_3583_);
v___x_3585_ = l_Lean_inheritedTraceOptions;
v___x_3586_ = lean_st_ref_get(v___x_3585_);
lean_inc_ref(v___x_3099_);
lean_inc(v_head_3057_);
v___x_3587_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3587_, 0, v_head_3057_);
lean_ctor_set(v___x_3587_, 1, v___x_3566_);
lean_ctor_set(v___x_3587_, 2, v___x_3099_);
lean_ctor_set(v___x_3587_, 3, v___x_3567_);
lean_ctor_set(v___x_3587_, 4, v___y_3498_);
lean_ctor_set(v___x_3587_, 5, v___x_3067_);
lean_ctor_set(v___x_3587_, 6, v___x_3098_);
lean_ctor_set(v___x_3587_, 7, v___x_3568_);
lean_ctor_set(v___x_3587_, 8, v___y_3498_);
lean_ctor_set(v___x_3587_, 9, v___x_3569_);
lean_ctor_set(v___x_3587_, 10, v___x_3570_);
lean_ctor_set(v___x_3587_, 11, v___x_3586_);
v___x_3588_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3588_, 0, v___x_3587_);
lean_ctor_set(v___x_3588_, 1, v___x_3098_);
lean_ctor_set(v___x_3588_, 2, v___x_3571_);
lean_ctor_set_uint16(v___x_3588_, sizeof(void*)*3, v___x_3572_);
lean_ctor_set_uint8(v___x_3588_, sizeof(void*)*3 + 2, v___x_3082_);
lean_ctor_set_uint8(v___x_3588_, sizeof(void*)*3 + 3, v___x_3082_);
v___x_3589_ = lean_st_ref_get(v___x_3584_);
v_env_3590_ = lean_ctor_get(v___x_3589_, 0);
lean_inc_ref(v_env_3590_);
lean_dec(v___x_3589_);
v___x_3591_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3590_);
lean_dec_ref(v_env_3590_);
v___x_3592_ = 512;
v___x_3593_ = lean_uint16_land(v___x_3572_, v___x_3592_);
v___x_3594_ = 0;
v___x_3595_ = lean_uint16_dec_eq(v___x_3593_, v___x_3594_);
if (v___x_3595_ == 0)
{
if (v___x_3504_ == 0)
{
v___y_3463_ = v___x_3579_;
v___y_3464_ = v___x_3571_;
v___y_3465_ = v___x_3565_;
v___y_3466_ = v___x_3576_;
v___y_3467_ = v___x_3570_;
v___y_3468_ = v___x_3067_;
v___y_3469_ = v___x_3573_;
v___y_3470_ = v___x_3577_;
v___y_3471_ = v___x_3569_;
v___y_3472_ = v___x_3575_;
v___y_3473_ = v___x_3504_;
v___y_3474_ = v___x_3564_;
v___y_3475_ = v___x_3572_;
v___y_3476_ = v___y_3497_;
v___y_3477_ = v___x_3566_;
v___y_3478_ = v___x_3574_;
v___y_3479_ = v___x_3578_;
v___y_3480_ = v___x_3582_;
v___y_3481_ = v___x_3584_;
v___y_3482_ = v___x_3580_;
v___y_3483_ = v___x_3581_;
v___y_3484_ = v___x_3504_;
v___y_3485_ = v___x_3591_;
v___y_3486_ = v___y_3498_;
v___y_3487_ = v___x_3588_;
v___y_3488_ = v___x_3504_;
goto v___jp_3462_;
}
else
{
v___y_3435_ = v___x_3569_;
v___y_3436_ = v___x_3577_;
v___y_3437_ = v___x_3579_;
v___y_3438_ = v___x_3504_;
v___y_3439_ = v___x_3571_;
v___y_3440_ = v___y_3497_;
v___y_3441_ = v___x_3570_;
v___y_3442_ = v___x_3566_;
v___y_3443_ = v___x_3067_;
v___y_3444_ = v___x_3578_;
v___y_3445_ = v___x_3579_;
v___y_3446_ = v___x_3565_;
v___y_3447_ = v___x_3582_;
v___y_3448_ = v___x_3576_;
v___y_3449_ = v___x_3584_;
v___y_3450_ = v___x_3580_;
v___y_3451_ = v___x_3504_;
v___y_3452_ = v___x_3573_;
v___y_3453_ = v___x_3577_;
v___y_3454_ = v___x_3581_;
v___y_3455_ = v___x_3575_;
v___y_3456_ = v___x_3564_;
v___y_3457_ = v___x_3572_;
v___y_3458_ = v___y_3498_;
v___y_3459_ = v___x_3588_;
v___y_3460_ = v___x_3574_;
v___y_3461_ = v___x_3591_;
goto v___jp_3434_;
}
}
else
{
v___y_3463_ = v___x_3579_;
v___y_3464_ = v___x_3571_;
v___y_3465_ = v___x_3565_;
v___y_3466_ = v___x_3576_;
v___y_3467_ = v___x_3570_;
v___y_3468_ = v___x_3067_;
v___y_3469_ = v___x_3573_;
v___y_3470_ = v___x_3577_;
v___y_3471_ = v___x_3569_;
v___y_3472_ = v___x_3575_;
v___y_3473_ = v___x_3504_;
v___y_3474_ = v___x_3564_;
v___y_3475_ = v___x_3572_;
v___y_3476_ = v___y_3497_;
v___y_3477_ = v___x_3566_;
v___y_3478_ = v___x_3574_;
v___y_3479_ = v___x_3578_;
v___y_3480_ = v___x_3582_;
v___y_3481_ = v___x_3584_;
v___y_3482_ = v___x_3580_;
v___y_3483_ = v___x_3581_;
v___y_3484_ = v___x_3504_;
v___y_3485_ = v___x_3591_;
v___y_3486_ = v___y_3498_;
v___y_3487_ = v___x_3588_;
v___y_3488_ = v___x_3082_;
goto v___jp_3462_;
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
v___jp_3608_:
{
lean_object* v___x_3618_; 
if (v_isShared_3056_ == 0)
{
lean_ctor_set_tag(v___x_3055_, 0);
lean_ctor_set(v___x_3055_, 1, v___y_3616_);
lean_ctor_set(v___x_3055_, 0, v___y_3612_);
v___x_3618_ = v___x_3055_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v___y_3612_);
lean_ctor_set(v_reuseFailAlloc_3624_, 1, v___y_3616_);
v___x_3618_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
lean_object* v___f_3619_; lean_object* v___x_3620_; 
v___f_3619_ = lean_alloc_closure((void*)(l_main___lam__3___boxed), 2, 1);
lean_closure_set(v___f_3619_, 0, v___x_3618_);
v___x_3620_ = lean_box(0);
if (v___y_3610_ == 0)
{
lean_object* v___x_3621_; 
lean_inc(v___y_3613_);
lean_inc_ref(v___y_3611_);
v___x_3621_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v___y_3611_, v___y_3614_, v___f_3619_, v___x_3620_, v___y_3613_, v___x_3095_);
v___y_3497_ = v___y_3609_;
v___y_3498_ = v___y_3613_;
v___y_3499_ = v___y_3615_;
v___y_3500_ = v___x_3621_;
goto v___jp_3496_;
}
else
{
lean_object* v___x_3622_; lean_object* v___x_3623_; 
lean_inc_ref_n(v___y_3611_, 2);
v___x_3622_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite___redArg(v___y_3611_, v___y_3614_);
lean_dec_ref(v___y_3614_);
lean_inc(v___y_3613_);
v___x_3623_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v___y_3611_, v___x_3622_, v___f_3619_, v___x_3620_, v___y_3613_, v___x_3095_);
v___y_3497_ = v___y_3609_;
v___y_3498_ = v___y_3613_;
v___y_3499_ = v___y_3615_;
v___y_3500_ = v___x_3623_;
goto v___jp_3496_;
}
}
}
v___jp_3625_:
{
lean_object* v___x_3630_; lean_object* v_toEnvExtension_3631_; lean_object* v_asyncMode_3632_; uint8_t v_logWrites_3633_; lean_object* v___x_3634_; lean_object* v_importedEntries_3635_; lean_object* v_state_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; uint8_t v___x_3639_; 
v___x_3630_ = l_Lean_Compiler_Bytecode_declMapExt;
v_toEnvExtension_3631_ = lean_ctor_get(v___x_3630_, 0);
v_asyncMode_3632_ = lean_ctor_get(v_toEnvExtension_3631_, 2);
v_logWrites_3633_ = lean_ctor_get_uint8(v_toEnvExtension_3631_, sizeof(void*)*6);
lean_inc(v___y_3627_);
lean_inc_ref(v___y_3629_);
v___x_3634_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3071_, v_toEnvExtension_3631_, v___y_3629_, v_asyncMode_3632_, v___y_3627_, v___x_3082_);
v_importedEntries_3635_ = lean_ctor_get(v___x_3634_, 0);
lean_inc_ref(v_importedEntries_3635_);
v_state_3636_ = lean_ctor_get(v___x_3634_, 1);
lean_inc(v_state_3636_);
lean_dec(v___x_3634_);
v___x_3637_ = lean_array_get_borrowed(v___x_3072_, v_importedEntries_3635_, v___y_3628_);
v___x_3638_ = lean_array_get_size(v___x_3637_);
v___x_3639_ = lean_nat_dec_lt(v___x_3098_, v___x_3638_);
if (v___x_3639_ == 0)
{
v___y_3609_ = v___y_3626_;
v___y_3610_ = v_logWrites_3633_;
v___y_3611_ = v_toEnvExtension_3631_;
v___y_3612_ = v_importedEntries_3635_;
v___y_3613_ = v___y_3627_;
v___y_3614_ = v___y_3629_;
v___y_3615_ = v___y_3628_;
v___y_3616_ = v_state_3636_;
goto v___jp_3608_;
}
else
{
uint8_t v___x_3640_; 
v___x_3640_ = lean_nat_dec_le(v___x_3638_, v___x_3638_);
if (v___x_3640_ == 0)
{
if (v___x_3639_ == 0)
{
v___y_3609_ = v___y_3626_;
v___y_3610_ = v_logWrites_3633_;
v___y_3611_ = v_toEnvExtension_3631_;
v___y_3612_ = v_importedEntries_3635_;
v___y_3613_ = v___y_3627_;
v___y_3614_ = v___y_3629_;
v___y_3615_ = v___y_3628_;
v___y_3616_ = v_state_3636_;
goto v___jp_3608_;
}
else
{
size_t v___x_3641_; size_t v___x_3642_; lean_object* v___x_3643_; 
v___x_3641_ = ((size_t)0ULL);
v___x_3642_ = lean_usize_of_nat(v___x_3638_);
lean_inc_ref(v___y_3629_);
v___x_3643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3629_, v___x_3637_, v___x_3641_, v___x_3642_, v_state_3636_);
v___y_3609_ = v___y_3626_;
v___y_3610_ = v_logWrites_3633_;
v___y_3611_ = v_toEnvExtension_3631_;
v___y_3612_ = v_importedEntries_3635_;
v___y_3613_ = v___y_3627_;
v___y_3614_ = v___y_3629_;
v___y_3615_ = v___y_3628_;
v___y_3616_ = v___x_3643_;
goto v___jp_3608_;
}
}
else
{
size_t v___x_3644_; size_t v___x_3645_; lean_object* v___x_3646_; 
v___x_3644_ = ((size_t)0ULL);
v___x_3645_ = lean_usize_of_nat(v___x_3638_);
lean_inc_ref(v___y_3629_);
v___x_3646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3629_, v___x_3637_, v___x_3644_, v___x_3645_, v_state_3636_);
v___y_3609_ = v___y_3626_;
v___y_3610_ = v_logWrites_3633_;
v___y_3611_ = v_toEnvExtension_3631_;
v___y_3612_ = v_importedEntries_3635_;
v___y_3613_ = v___y_3627_;
v___y_3614_ = v___y_3629_;
v___y_3615_ = v___y_3628_;
v___y_3616_ = v___x_3646_;
goto v___jp_3608_;
}
}
}
v___jp_3647_:
{
uint8_t v___x_3654_; 
v___x_3654_ = lean_nat_dec_lt(v___x_3098_, v___y_3650_);
if (v___x_3654_ == 0)
{
lean_dec_ref(v___y_3651_);
lean_dec(v___y_3650_);
v___y_3626_ = v___y_3648_;
v___y_3627_ = v___y_3649_;
v___y_3628_ = v___y_3652_;
v___y_3629_ = v___y_3653_;
goto v___jp_3625_;
}
else
{
uint8_t v___x_3655_; 
v___x_3655_ = lean_nat_dec_le(v___y_3650_, v___y_3650_);
if (v___x_3655_ == 0)
{
if (v___x_3654_ == 0)
{
lean_dec_ref(v___y_3651_);
lean_dec(v___y_3650_);
v___y_3626_ = v___y_3648_;
v___y_3627_ = v___y_3649_;
v___y_3628_ = v___y_3652_;
v___y_3629_ = v___y_3653_;
goto v___jp_3625_;
}
else
{
size_t v___x_3656_; size_t v___x_3657_; lean_object* v___x_3658_; 
v___x_3656_ = ((size_t)0ULL);
v___x_3657_ = lean_usize_of_nat(v___y_3650_);
lean_dec(v___y_3650_);
v___x_3658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3651_, v___x_3656_, v___x_3657_, v___y_3653_);
lean_dec_ref(v___y_3651_);
v___y_3626_ = v___y_3648_;
v___y_3627_ = v___y_3649_;
v___y_3628_ = v___y_3652_;
v___y_3629_ = v___x_3658_;
goto v___jp_3625_;
}
}
else
{
size_t v___x_3659_; size_t v___x_3660_; lean_object* v___x_3661_; 
v___x_3659_ = ((size_t)0ULL);
v___x_3660_ = lean_usize_of_nat(v___y_3650_);
lean_dec(v___y_3650_);
v___x_3661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3651_, v___x_3659_, v___x_3660_, v___y_3653_);
lean_dec_ref(v___y_3651_);
v___y_3626_ = v___y_3648_;
v___y_3627_ = v___y_3649_;
v___y_3628_ = v___y_3652_;
v___y_3629_ = v___x_3661_;
goto v___jp_3625_;
}
}
}
v___jp_3662_:
{
lean_object* v___x_3668_; uint8_t v___x_3669_; 
v___x_3668_ = lean_array_get_size(v___y_3667_);
v___x_3669_ = lean_nat_dec_lt(v___x_3098_, v___x_3668_);
if (v___x_3669_ == 0)
{
v___y_3648_ = v___y_3663_;
v___y_3649_ = v___y_3665_;
v___y_3650_ = v___x_3668_;
v___y_3651_ = v___y_3667_;
v___y_3652_ = v___y_3666_;
v___y_3653_ = v___y_3664_;
goto v___jp_3647_;
}
else
{
uint8_t v___x_3670_; 
v___x_3670_ = lean_nat_dec_le(v___x_3668_, v___x_3668_);
if (v___x_3670_ == 0)
{
if (v___x_3669_ == 0)
{
v___y_3648_ = v___y_3663_;
v___y_3649_ = v___y_3665_;
v___y_3650_ = v___x_3668_;
v___y_3651_ = v___y_3667_;
v___y_3652_ = v___y_3666_;
v___y_3653_ = v___y_3664_;
goto v___jp_3647_;
}
else
{
size_t v___x_3671_; size_t v___x_3672_; lean_object* v___x_3673_; 
v___x_3671_ = ((size_t)0ULL);
v___x_3672_ = lean_usize_of_nat(v___x_3668_);
v___x_3673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3667_, v___x_3671_, v___x_3672_, v___y_3664_);
v___y_3648_ = v___y_3663_;
v___y_3649_ = v___y_3665_;
v___y_3650_ = v___x_3668_;
v___y_3651_ = v___y_3667_;
v___y_3652_ = v___y_3666_;
v___y_3653_ = v___x_3673_;
goto v___jp_3647_;
}
}
else
{
size_t v___x_3674_; size_t v___x_3675_; lean_object* v___x_3676_; 
v___x_3674_ = ((size_t)0ULL);
v___x_3675_ = lean_usize_of_nat(v___x_3668_);
v___x_3676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3667_, v___x_3674_, v___x_3675_, v___y_3664_);
v___y_3648_ = v___y_3663_;
v___y_3649_ = v___y_3665_;
v___y_3650_ = v___x_3668_;
v___y_3651_ = v___y_3667_;
v___y_3652_ = v___y_3666_;
v___y_3653_ = v___x_3676_;
goto v___jp_3647_;
}
}
}
v___jp_3677_:
{
lean_object* v___x_3680_; lean_object* v_ext_3681_; lean_object* v___x_3682_; 
v___x_3680_ = l_Lean_Compiler_CSimp_ext;
v_ext_3681_ = lean_ctor_get(v___x_3680_, 1);
lean_inc_ref(v_ext_3681_);
lean_inc(v___y_3678_);
v___x_3682_ = l_main___elam__0___redArg(v___y_3678_, v___x_3082_, v___x_3066_, v_ext_3681_, v___y_3679_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v_a_3683_; lean_object* v___x_3684_; lean_object* v_ext_3685_; lean_object* v___x_3686_; 
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
lean_inc(v_a_3683_);
lean_dec_ref_known(v___x_3682_, 1);
v___x_3684_ = l_Lean_Meta_instanceExtension;
v_ext_3685_ = lean_ctor_get(v___x_3684_, 1);
lean_inc_ref(v_ext_3685_);
lean_inc(v___y_3678_);
v___x_3686_ = l_main___elam__0___redArg(v___y_3678_, v___x_3082_, v___x_3066_, v_ext_3685_, v_a_3683_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v_a_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; 
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
lean_inc(v_a_3687_);
lean_dec_ref_known(v___x_3686_, 1);
v___x_3688_ = l_Lean_classExtension;
lean_inc(v___y_3678_);
v___x_3689_ = l_main___elam__0___redArg(v___y_3678_, v___x_3082_, v___x_3068_, v___x_3688_, v_a_3687_);
if (lean_obj_tag(v___x_3689_) == 0)
{
lean_object* v_a_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
v_a_3690_ = lean_ctor_get(v___x_3689_, 0);
lean_inc(v_a_3690_);
lean_dec_ref_known(v___x_3689_, 1);
v___x_3691_ = l_Lean_Meta_Match_Extension_extension;
lean_inc(v___y_3678_);
v___x_3692_ = l_main___elam__0___redArg(v___y_3678_, v___x_3082_, v___x_3069_, v___x_3691_, v_a_3690_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v_a_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3720_; 
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3695_ = v___x_3692_;
v_isShared_3696_ = v_isSharedCheck_3720_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_a_3693_);
lean_dec(v___x_3692_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3720_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3697_; 
v___x_3697_ = l_Lean_Environment_getModuleIdx_x3f(v_a_3693_, v_name_3077_);
if (lean_obj_tag(v___x_3697_) == 1)
{
lean_object* v_val_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; uint8_t v___x_3703_; 
lean_del_object(v___x_3695_);
v_val_3698_ = lean_ctor_get(v___x_3697_, 0);
lean_inc(v_val_3698_);
lean_dec_ref_known(v___x_3697_, 1);
v___x_3699_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_3700_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3070_, v___x_3699_, v_a_3693_, v_val_3698_, v___x_3495_);
v___x_3701_ = lean_array_get_size(v___x_3700_);
v___x_3702_ = ((lean_object*)(l_main___closed__32));
v___x_3703_ = lean_nat_dec_lt(v___x_3098_, v___x_3701_);
if (v___x_3703_ == 0)
{
lean_dec_ref(v___x_3700_);
lean_inc(v___y_3678_);
v___y_3663_ = v___y_3678_;
v___y_3664_ = v_a_3693_;
v___y_3665_ = v___y_3678_;
v___y_3666_ = v_val_3698_;
v___y_3667_ = v___x_3702_;
goto v___jp_3662_;
}
else
{
uint8_t v___x_3704_; 
v___x_3704_ = lean_nat_dec_le(v___x_3701_, v___x_3701_);
if (v___x_3704_ == 0)
{
if (v___x_3703_ == 0)
{
lean_dec_ref(v___x_3700_);
lean_inc(v___y_3678_);
v___y_3663_ = v___y_3678_;
v___y_3664_ = v_a_3693_;
v___y_3665_ = v___y_3678_;
v___y_3666_ = v_val_3698_;
v___y_3667_ = v___x_3702_;
goto v___jp_3662_;
}
else
{
size_t v___x_3705_; size_t v___x_3706_; lean_object* v___x_3707_; 
v___x_3705_ = ((size_t)0ULL);
v___x_3706_ = lean_usize_of_nat(v___x_3701_);
lean_inc(v_a_3693_);
v___x_3707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_3693_, v___x_3700_, v___x_3705_, v___x_3706_, v___x_3702_);
lean_dec_ref(v___x_3700_);
lean_inc(v___y_3678_);
v___y_3663_ = v___y_3678_;
v___y_3664_ = v_a_3693_;
v___y_3665_ = v___y_3678_;
v___y_3666_ = v_val_3698_;
v___y_3667_ = v___x_3707_;
goto v___jp_3662_;
}
}
else
{
size_t v___x_3708_; size_t v___x_3709_; lean_object* v___x_3710_; 
v___x_3708_ = ((size_t)0ULL);
v___x_3709_ = lean_usize_of_nat(v___x_3701_);
lean_inc(v_a_3693_);
v___x_3710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_3693_, v___x_3700_, v___x_3708_, v___x_3709_, v___x_3702_);
lean_dec_ref(v___x_3700_);
lean_inc(v___y_3678_);
v___y_3663_ = v___y_3678_;
v___y_3664_ = v_a_3693_;
v___y_3665_ = v___y_3678_;
v___y_3666_ = v_val_3698_;
v___y_3667_ = v___x_3710_;
goto v___jp_3662_;
}
}
}
else
{
lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3718_; 
lean_dec(v___x_3697_);
lean_dec(v_a_3693_);
lean_dec(v___y_3678_);
lean_dec_ref(v___x_3099_);
lean_del_object(v___x_3092_);
lean_dec(v_fst_3089_);
lean_dec(v_head_3061_);
lean_del_object(v___x_3059_);
lean_dec(v_head_3057_);
lean_del_object(v___x_3055_);
v___x_3711_ = ((lean_object*)(l_main___closed__33));
v___x_3712_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3077_, v___x_3095_);
v___x_3713_ = lean_string_append(v___x_3711_, v___x_3712_);
lean_dec_ref(v___x_3712_);
v___x_3714_ = ((lean_object*)(l_main___closed__34));
v___x_3715_ = lean_string_append(v___x_3713_, v___x_3714_);
v___x_3716_ = lean_mk_io_user_error(v___x_3715_);
if (v_isShared_3696_ == 0)
{
lean_ctor_set_tag(v___x_3695_, 1);
lean_ctor_set(v___x_3695_, 0, v___x_3716_);
v___x_3718_ = v___x_3695_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3716_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
}
}
else
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3728_; 
lean_dec(v___y_3678_);
lean_dec_ref(v___x_3099_);
lean_del_object(v___x_3092_);
lean_dec(v_fst_3089_);
lean_dec(v_name_3077_);
lean_dec(v_head_3061_);
lean_del_object(v___x_3059_);
lean_dec(v_head_3057_);
lean_del_object(v___x_3055_);
v_a_3721_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3723_ = v___x_3692_;
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3692_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3726_; 
if (v_isShared_3724_ == 0)
{
v___x_3726_ = v___x_3723_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3721_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
}
else
{
lean_object* v_a_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3736_; 
lean_dec(v___y_3678_);
lean_dec_ref(v___x_3099_);
lean_del_object(v___x_3092_);
lean_dec(v_fst_3089_);
lean_dec(v_name_3077_);
lean_dec(v_head_3061_);
lean_del_object(v___x_3059_);
lean_dec(v_head_3057_);
lean_del_object(v___x_3055_);
v_a_3729_ = lean_ctor_get(v___x_3689_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3689_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3731_ = v___x_3689_;
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_a_3729_);
lean_dec(v___x_3689_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3734_; 
if (v_isShared_3732_ == 0)
{
v___x_3734_ = v___x_3731_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_a_3729_);
v___x_3734_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
return v___x_3734_;
}
}
}
}
else
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3744_; 
lean_dec(v___y_3678_);
lean_dec_ref(v___x_3099_);
lean_del_object(v___x_3092_);
lean_dec(v_fst_3089_);
lean_dec(v_name_3077_);
lean_dec(v_head_3061_);
lean_del_object(v___x_3059_);
lean_dec(v_head_3057_);
lean_del_object(v___x_3055_);
v_a_3737_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3739_ = v___x_3686_;
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3686_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3742_; 
if (v_isShared_3740_ == 0)
{
v___x_3742_ = v___x_3739_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_a_3737_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
}
}
else
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3752_; 
lean_dec(v___y_3678_);
lean_dec_ref(v___x_3099_);
lean_del_object(v___x_3092_);
lean_dec(v_fst_3089_);
lean_dec(v_name_3077_);
lean_dec(v_head_3061_);
lean_del_object(v___x_3059_);
lean_dec(v_head_3057_);
lean_del_object(v___x_3055_);
v_a_3745_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3747_ = v___x_3682_;
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3682_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3750_; 
if (v_isShared_3748_ == 0)
{
v___x_3750_ = v___x_3747_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3745_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
}
v___jp_3753_:
{
lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___f_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
v___x_3755_ = l_Lean_instInhabitedImportState_default;
v___x_3756_ = lean_box(v___x_3495_);
v___x_3757_ = lean_box(v___y_3754_);
v___x_3758_ = lean_box(v___x_3095_);
v___x_3759_ = lean_box(v___x_3082_);
lean_inc_ref(v___x_3099_);
lean_inc(v_name_3077_);
v___f_3760_ = lean_alloc_closure((void*)(l_main___lam__1___boxed), 10, 9);
lean_closure_set(v___f_3760_, 0, v___x_3755_);
lean_closure_set(v___f_3760_, 1, v___x_3494_);
lean_closure_set(v___f_3760_, 2, v___x_3756_);
lean_closure_set(v___f_3760_, 3, v_importArts_3079_);
lean_closure_set(v___f_3760_, 4, v___x_3757_);
lean_closure_set(v___f_3760_, 5, v___x_3758_);
lean_closure_set(v___f_3760_, 6, v_name_3077_);
lean_closure_set(v___f_3760_, 7, v___x_3099_);
lean_closure_set(v___f_3760_, 8, v___x_3759_);
v___x_3761_ = lean_alloc_closure((void*)(l_Lean_withImporting___boxed), 3, 2);
lean_closure_set(v___x_3761_, 0, lean_box(0));
lean_closure_set(v___x_3761_, 1, v___f_3760_);
v___x_3762_ = lean_box(0);
v___x_3763_ = l_Lean_profileitIOUnsafe___redArg(v___x_3490_, v___x_3099_, v___x_3761_, v___x_3762_);
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_object* v_a_3764_; lean_object* v___x_3765_; lean_object* v_toEnvExtension_3766_; lean_object* v_asyncMode_3767_; uint8_t v_logWrites_3768_; lean_object* v___x_3769_; 
v_a_3764_ = lean_ctor_get(v___x_3763_, 0);
lean_inc(v_a_3764_);
lean_dec_ref_known(v___x_3763_, 1);
v___x_3765_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_3766_ = lean_ctor_get(v___x_3765_, 0);
v_asyncMode_3767_ = lean_ctor_get(v_toEnvExtension_3766_, 2);
v_logWrites_3768_ = lean_ctor_get_uint8(v_toEnvExtension_3766_, sizeof(void*)*6);
lean_inc(v_name_3077_);
v___x_3769_ = l_Lean_Environment_setMainModule(v_a_3764_, v_name_3077_);
if (v_logWrites_3768_ == 0)
{
lean_object* v___x_3770_; 
lean_inc_ref(v_toEnvExtension_3766_);
v___x_3770_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_3766_, v___x_3769_, v___f_3081_, v_asyncMode_3767_, v___x_3762_, v___x_3095_);
v___y_3678_ = v___x_3762_;
v___y_3679_ = v___x_3770_;
goto v___jp_3677_;
}
else
{
lean_object* v___x_3771_; lean_object* v___x_3772_; 
lean_inc_ref_n(v_toEnvExtension_3766_, 2);
v___x_3771_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite___redArg(v_toEnvExtension_3766_, v___x_3769_);
lean_dec_ref(v___x_3769_);
v___x_3772_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_3766_, v___x_3771_, v___f_3081_, v_asyncMode_3767_, v___x_3762_, v___x_3095_);
v___y_3678_ = v___x_3762_;
v___y_3679_ = v___x_3772_;
goto v___jp_3677_;
}
}
else
{
lean_object* v_a_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3780_; 
lean_dec_ref(v___x_3099_);
lean_del_object(v___x_3092_);
lean_dec(v_fst_3089_);
lean_dec_ref(v___f_3081_);
lean_dec(v_name_3077_);
lean_dec(v_head_3061_);
lean_del_object(v___x_3059_);
lean_dec(v_head_3057_);
lean_del_object(v___x_3055_);
v_a_3773_ = lean_ctor_get(v___x_3763_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3775_ = v___x_3763_;
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_a_3773_);
lean_dec(v___x_3763_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v___x_3778_; 
if (v_isShared_3776_ == 0)
{
v___x_3778_ = v___x_3775_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_a_3773_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
}
}
else
{
lean_object* v_a_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3789_; 
lean_dec_ref(v___x_3099_);
lean_del_object(v___x_3092_);
lean_dec(v_fst_3089_);
lean_dec_ref(v___f_3081_);
lean_dec(v_importArts_3079_);
lean_dec(v_name_3077_);
lean_dec(v_head_3061_);
lean_del_object(v___x_3059_);
lean_dec(v_head_3057_);
lean_del_object(v___x_3055_);
v_a_3782_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3789_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3789_ == 0)
{
v___x_3784_ = v___x_3489_;
v_isShared_3785_ = v_isSharedCheck_3789_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_a_3782_);
lean_dec(v___x_3489_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3789_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v___x_3787_; 
if (v_isShared_3785_ == 0)
{
v___x_3787_ = v___x_3784_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v_a_3782_);
v___x_3787_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
return v___x_3787_;
}
}
}
v___jp_3100_:
{
lean_object* v___x_3122_; lean_object* v_messages_3123_; lean_object* v_env_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3249_; 
v___x_3122_ = lean_st_ref_get(v___y_3119_);
lean_dec(v___y_3119_);
v_messages_3123_ = lean_ctor_get(v___x_3122_, 7);
v_env_3124_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3249_ == 0)
{
lean_object* v_unused_3250_; lean_object* v_unused_3251_; lean_object* v_unused_3252_; lean_object* v_unused_3253_; lean_object* v_unused_3254_; lean_object* v_unused_3255_; lean_object* v_unused_3256_; lean_object* v_unused_3257_; 
v_unused_3250_ = lean_ctor_get(v___x_3122_, 9);
lean_dec(v_unused_3250_);
v_unused_3251_ = lean_ctor_get(v___x_3122_, 8);
lean_dec(v_unused_3251_);
v_unused_3252_ = lean_ctor_get(v___x_3122_, 6);
lean_dec(v_unused_3252_);
v_unused_3253_ = lean_ctor_get(v___x_3122_, 5);
lean_dec(v_unused_3253_);
v_unused_3254_ = lean_ctor_get(v___x_3122_, 4);
lean_dec(v_unused_3254_);
v_unused_3255_ = lean_ctor_get(v___x_3122_, 3);
lean_dec(v_unused_3255_);
v_unused_3256_ = lean_ctor_get(v___x_3122_, 2);
lean_dec(v_unused_3256_);
v_unused_3257_ = lean_ctor_get(v___x_3122_, 1);
lean_dec(v_unused_3257_);
v___x_3126_ = v___x_3122_;
v_isShared_3127_ = v_isSharedCheck_3249_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_messages_3123_);
lean_inc(v_env_3124_);
lean_dec(v___x_3122_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3249_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v_unreported_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v_unreported_3128_ = lean_ctor_get(v_messages_3123_, 1);
v___x_3129_ = lean_box(0);
v___x_3130_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_unreported_3128_, v___x_3129_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3239_; 
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3239_ == 0)
{
lean_object* v_unused_3240_; 
v_unused_3240_ = lean_ctor_get(v___x_3130_, 0);
lean_dec(v_unused_3240_);
v___x_3132_ = v___x_3130_;
v_isShared_3133_ = v_isSharedCheck_3239_;
goto v_resetjp_3131_;
}
else
{
lean_dec(v___x_3130_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3239_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
uint8_t v___x_3134_; 
v___x_3134_ = l_Lean_MessageLog_hasErrors(v_messages_3123_);
lean_dec_ref(v_messages_3123_);
if (v___x_3134_ == 0)
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
lean_del_object(v___x_3132_);
v___x_3135_ = ((lean_object*)(l_main___closed__9));
lean_inc(v_head_3057_);
v___x_3136_ = l_System_FilePath_addExtension(v_head_3057_, v___x_3135_);
lean_inc_ref(v_env_3124_);
v___x_3137_ = l___private_LeanIR_0__mkIRSigData(v_env_3124_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; lean_object* v___x_3139_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_a_3138_);
lean_dec_ref_known(v___x_3137_, 1);
lean_inc_ref(v_env_3124_);
v___x_3139_ = l___private_LeanIR_0__mkIRData(v_env_3124_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3145_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_a_3140_);
lean_dec_ref_known(v___x_3139_, 1);
v___x_3141_ = l_Lean_Environment_mainModule(v_env_3124_);
v___x_3142_ = ((lean_object*)(l_main___closed__11));
v___x_3143_ = l_Lean_Name_append(v___x_3141_, v___x_3142_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 1, v_a_3138_);
lean_ctor_set(v___x_3092_, 0, v___x_3136_);
v___x_3145_ = v___x_3092_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v___x_3136_);
lean_ctor_set(v_reuseFailAlloc_3218_, 1, v_a_3138_);
v___x_3145_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
lean_object* v___x_3147_; 
lean_inc(v_head_3057_);
if (v_isShared_3060_ == 0)
{
lean_ctor_set_tag(v___x_3059_, 0);
lean_ctor_set(v___x_3059_, 1, v_a_3140_);
v___x_3147_ = v___x_3059_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_head_3057_);
lean_ctor_set(v_reuseFailAlloc_3217_, 1, v_a_3140_);
v___x_3147_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3148_ = lean_unsigned_to_nat(2u);
v___x_3149_ = lean_mk_empty_array_with_capacity(v___x_3148_);
v___x_3150_ = lean_array_push(v___x_3149_, v___x_3145_);
v___x_3151_ = lean_array_push(v___x_3150_, v___x_3147_);
v___x_3152_ = l_Lean_saveModuleDataParts(v___x_3143_, v___x_3151_);
lean_dec_ref(v___x_3151_);
lean_dec(v___x_3143_);
if (lean_obj_tag(v___x_3152_) == 0)
{
uint8_t v___x_3153_; lean_object* v___x_3154_; 
lean_dec_ref_known(v___x_3152_, 1);
v___x_3153_ = 1;
v___x_3154_ = lean_io_prim_handle_mk(v_head_3061_, v___x_3153_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; uint16_t v___x_3158_; lean_object* v___x_3160_; 
lean_dec(v_head_3061_);
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
lean_inc(v_a_3155_);
lean_dec_ref_known(v___x_3154_, 1);
v___x_3156_ = ((lean_object*)(l_main___closed__12));
v___x_3157_ = l_Lean_Core_getMaxHeartbeats(v___y_3112_);
v___x_3158_ = l_Lean_OptionFlags_ofOptions(v___y_3112_);
lean_inc_ref(v___y_3110_);
lean_inc_ref(v___y_3115_);
lean_inc_ref(v___y_3113_);
lean_inc_ref(v___y_3118_);
lean_inc_ref(v___y_3111_);
lean_inc_ref(v___y_3117_);
lean_inc_ref(v___y_3121_);
lean_inc(v___y_3120_);
lean_inc_ref(v_env_3124_);
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 9, v___y_3110_);
lean_ctor_set(v___x_3126_, 8, v___y_3115_);
lean_ctor_set(v___x_3126_, 7, v___y_3113_);
lean_ctor_set(v___x_3126_, 6, v___y_3118_);
lean_ctor_set(v___x_3126_, 5, v___y_3111_);
lean_ctor_set(v___x_3126_, 4, v___y_3117_);
lean_ctor_set(v___x_3126_, 3, v___y_3114_);
lean_ctor_set(v___x_3126_, 2, v___y_3121_);
lean_ctor_set(v___x_3126_, 1, v___y_3120_);
v___x_3160_ = v___x_3126_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_env_3124_);
lean_ctor_set(v_reuseFailAlloc_3186_, 1, v___y_3120_);
lean_ctor_set(v_reuseFailAlloc_3186_, 2, v___y_3121_);
lean_ctor_set(v_reuseFailAlloc_3186_, 3, v___y_3114_);
lean_ctor_set(v_reuseFailAlloc_3186_, 4, v___y_3117_);
lean_ctor_set(v_reuseFailAlloc_3186_, 5, v___y_3111_);
lean_ctor_set(v_reuseFailAlloc_3186_, 6, v___y_3118_);
lean_ctor_set(v_reuseFailAlloc_3186_, 7, v___y_3113_);
lean_ctor_set(v_reuseFailAlloc_3186_, 8, v___y_3115_);
lean_ctor_set(v_reuseFailAlloc_3186_, 9, v___y_3110_);
v___x_3160_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___f_3165_; lean_object* v___x_3166_; 
v___x_3161_ = lean_box(v___x_3158_);
v___x_3162_ = lean_box(v___y_3104_);
v___x_3163_ = lean_box(v___x_3082_);
v___x_3164_ = lean_box(v___x_3134_);
lean_inc(v___y_3105_);
lean_inc(v___y_3107_);
lean_inc(v___y_3101_);
lean_inc(v___y_3109_);
lean_inc_ref(v___y_3108_);
lean_inc_ref(v___y_3102_);
lean_inc_ref(v___y_3103_);
v___f_3165_ = lean_alloc_closure((void*)(l_main___lam__2___boxed), 19, 18);
lean_closure_set(v___f_3165_, 0, v___x_3160_);
lean_closure_set(v___f_3165_, 1, v___y_3103_);
lean_closure_set(v___f_3165_, 2, v___x_3161_);
lean_closure_set(v___f_3165_, 3, v_name_3077_);
lean_closure_set(v___f_3165_, 4, v_a_3155_);
lean_closure_set(v___f_3165_, 5, v___x_3162_);
lean_closure_set(v___f_3165_, 6, v___y_3102_);
lean_closure_set(v___f_3165_, 7, v_head_3057_);
lean_closure_set(v___f_3165_, 8, v___y_3108_);
lean_closure_set(v___f_3165_, 9, v___y_3106_);
lean_closure_set(v___f_3165_, 10, v___y_3109_);
lean_closure_set(v___f_3165_, 11, v___x_3157_);
lean_closure_set(v___f_3165_, 12, v___y_3101_);
lean_closure_set(v___f_3165_, 13, v___y_3107_);
lean_closure_set(v___f_3165_, 14, v___x_3098_);
lean_closure_set(v___f_3165_, 15, v___y_3105_);
lean_closure_set(v___f_3165_, 16, v___x_3163_);
lean_closure_set(v___f_3165_, 17, v___x_3164_);
v___x_3166_ = l_Lean_profileitIOUnsafe___redArg(v___x_3156_, v___x_3099_, v___f_3165_, v___y_3116_);
lean_dec_ref(v___x_3099_);
if (lean_obj_tag(v___x_3166_) == 0)
{
lean_object* v___x_3167_; uint8_t v___x_3168_; 
lean_dec_ref_known(v___x_3166_, 1);
v___x_3167_ = lean_display_cumulative_profiling_times();
v___x_3168_ = lean_unbox(v_fst_3089_);
lean_dec(v_fst_3089_);
if (v___x_3168_ == 0)
{
lean_dec_ref(v_env_3124_);
goto v___jp_3028_;
}
else
{
lean_object* v___x_3169_; 
v___x_3169_ = l_Lean_Environment_displayStats(v_env_3124_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_dec_ref_known(v___x_3169_, 1);
goto v___jp_3028_;
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3169_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3169_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
}
}
else
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
lean_dec_ref(v_env_3124_);
lean_dec(v_fst_3089_);
v_a_3178_ = lean_ctor_get(v___x_3166_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v___x_3166_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3166_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3183_; 
if (v_isShared_3181_ == 0)
{
v___x_3183_ = v___x_3180_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3178_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
}
}
}
else
{
lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
lean_dec_ref_known(v___x_3154_, 1);
lean_del_object(v___x_3126_);
lean_dec_ref(v_env_3124_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3106_);
lean_dec_ref(v___x_3099_);
lean_dec(v_fst_3089_);
lean_dec(v_name_3077_);
lean_dec(v_head_3057_);
v___x_3187_ = ((lean_object*)(l_main___closed__13));
v___x_3188_ = lean_string_append(v___x_3187_, v_head_3061_);
lean_dec(v_head_3061_);
v___x_3189_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__1));
v___x_3190_ = lean_string_append(v___x_3188_, v___x_3189_);
v___x_3191_ = l_IO_eprintln___at___00main_spec__6(v___x_3190_);
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3199_; 
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3199_ == 0)
{
lean_object* v_unused_3200_; 
v_unused_3200_ = lean_ctor_get(v___x_3191_, 0);
lean_dec(v_unused_3200_);
v___x_3193_ = v___x_3191_;
v_isShared_3194_ = v_isSharedCheck_3199_;
goto v_resetjp_3192_;
}
else
{
lean_dec(v___x_3191_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3199_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3195_; lean_object* v___x_3197_; 
v___x_3195_ = l_main___boxed__const__2;
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 0, v___x_3195_);
v___x_3197_ = v___x_3193_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3195_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
else
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
v_a_3201_ = lean_ctor_get(v___x_3191_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3203_ = v___x_3191_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3191_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3204_ == 0)
{
v___x_3206_ = v___x_3203_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
}
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
lean_del_object(v___x_3126_);
lean_dec_ref(v_env_3124_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3106_);
lean_dec_ref(v___x_3099_);
lean_dec(v_fst_3089_);
lean_dec(v_name_3077_);
lean_dec(v_head_3061_);
lean_dec(v_head_3057_);
v_a_3209_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_3152_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3152_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3209_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
}
}
else
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
lean_dec(v_a_3138_);
lean_dec_ref(v___x_3136_);
lean_del_object(v___x_3126_);
lean_dec_ref(v_env_3124_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3106_);
lean_dec_ref(v___x_3099_);
lean_del_object(v___x_3092_);
lean_dec(v_fst_3089_);
lean_dec(v_name_3077_);
lean_dec(v_head_3061_);
lean_del_object(v___x_3059_);
lean_dec(v_head_3057_);
v_a_3219_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3221_ = v___x_3139_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3139_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3219_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
else
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3234_; 
lean_dec_ref(v___x_3136_);
lean_del_object(v___x_3126_);
lean_dec_ref(v_env_3124_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3106_);
lean_dec_ref(v___x_3099_);
lean_del_object(v___x_3092_);
lean_dec(v_fst_3089_);
lean_dec(v_name_3077_);
lean_dec(v_head_3061_);
lean_del_object(v___x_3059_);
lean_dec(v_head_3057_);
v_a_3227_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3229_ = v___x_3137_;
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_3137_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3232_; 
if (v_isShared_3230_ == 0)
{
v___x_3232_ = v___x_3229_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_a_3227_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
}
else
{
lean_object* v___x_3235_; lean_object* v___x_3237_; 
lean_del_object(v___x_3126_);
lean_dec_ref(v_env_3124_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3106_);
lean_dec_ref(v___x_3099_);
lean_del_object(v___x_3092_);
lean_dec(v_fst_3089_);
lean_dec(v_name_3077_);
lean_dec(v_head_3061_);
lean_del_object(v___x_3059_);
lean_dec(v_head_3057_);
v___x_3235_ = l_main___boxed__const__2;
if (v_isShared_3133_ == 0)
{
lean_ctor_set(v___x_3132_, 0, v___x_3235_);
v___x_3237_ = v___x_3132_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3235_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
else
{
lean_object* v_a_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3248_; 
lean_del_object(v___x_3126_);
lean_dec_ref(v_env_3124_);
lean_dec_ref(v_messages_3123_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3106_);
lean_dec_ref(v___x_3099_);
lean_del_object(v___x_3092_);
lean_dec(v_fst_3089_);
lean_dec(v_name_3077_);
lean_dec(v_head_3061_);
lean_del_object(v___x_3059_);
lean_dec(v_head_3057_);
v_a_3241_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3243_ = v___x_3130_;
v_isShared_3244_ = v_isSharedCheck_3248_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_a_3241_);
lean_dec(v___x_3130_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3248_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___x_3246_; 
if (v_isShared_3244_ == 0)
{
v___x_3246_ = v___x_3243_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_a_3241_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
}
}
}
v___jp_3258_:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; size_t v_sz_3295_; size_t v___x_3296_; lean_object* v___x_3297_; 
lean_inc_ref(v___y_3284_);
v___x_3292_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3292_, 0, v___y_3291_);
lean_ctor_set(v___x_3292_, 1, v_nextMacroScope_3270_);
lean_ctor_set(v___x_3292_, 2, v_ngen_3271_);
lean_ctor_set(v___x_3292_, 3, v_auxDeclNGen_3272_);
lean_ctor_set(v___x_3292_, 4, v_traceState_3273_);
lean_ctor_set(v___x_3292_, 5, v___y_3284_);
lean_ctor_set(v___x_3292_, 6, v_recordedDeps_3274_);
lean_ctor_set(v___x_3292_, 7, v_messages_3275_);
lean_ctor_set(v___x_3292_, 8, v_infoState_3276_);
lean_ctor_set(v___x_3292_, 9, v_snapshotTasks_3277_);
v___x_3293_ = lean_st_ref_put(v___y_3287_, v___x_3292_);
v___x_3294_ = lean_box(0);
v_sz_3295_ = lean_array_size(v___y_3278_);
v___x_3296_ = ((size_t)0ULL);
v___x_3297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(v___y_3278_, v_sz_3295_, v___x_3296_, v___x_3294_, v___y_3289_, v___y_3287_);
lean_dec_ref(v___y_3278_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_dec_ref_known(v___x_3297_, 1);
lean_dec_ref(v___y_3289_);
lean_dec(v___y_3287_);
v___y_3101_ = v___y_3260_;
v___y_3102_ = v___y_3259_;
v___y_3103_ = v___y_3261_;
v___y_3104_ = v___y_3262_;
v___y_3105_ = v___y_3263_;
v___y_3106_ = v___y_3264_;
v___y_3107_ = v___y_3266_;
v___y_3108_ = v___y_3265_;
v___y_3109_ = v___y_3267_;
v___y_3110_ = v___y_3268_;
v___y_3111_ = v___y_3284_;
v___y_3112_ = v___y_3269_;
v___y_3113_ = v___y_3285_;
v___y_3114_ = v___y_3286_;
v___y_3115_ = v___y_3279_;
v___y_3116_ = v___y_3288_;
v___y_3117_ = v___y_3280_;
v___y_3118_ = v___y_3282_;
v___y_3119_ = v___y_3281_;
v___y_3120_ = v___y_3283_;
v___y_3121_ = v___y_3290_;
goto v___jp_3100_;
}
else
{
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_dec_ref_known(v___x_3297_, 1);
lean_dec_ref(v___y_3289_);
lean_dec(v___y_3287_);
v___y_3101_ = v___y_3260_;
v___y_3102_ = v___y_3259_;
v___y_3103_ = v___y_3261_;
v___y_3104_ = v___y_3262_;
v___y_3105_ = v___y_3263_;
v___y_3106_ = v___y_3264_;
v___y_3107_ = v___y_3266_;
v___y_3108_ = v___y_3265_;
v___y_3109_ = v___y_3267_;
v___y_3110_ = v___y_3268_;
v___y_3111_ = v___y_3284_;
v___y_3112_ = v___y_3269_;
v___y_3113_ = v___y_3285_;
v___y_3114_ = v___y_3286_;
v___y_3115_ = v___y_3279_;
v___y_3116_ = v___y_3288_;
v___y_3117_ = v___y_3280_;
v___y_3118_ = v___y_3282_;
v___y_3119_ = v___y_3281_;
v___y_3120_ = v___y_3283_;
v___y_3121_ = v___y_3290_;
goto v___jp_3100_;
}
else
{
lean_object* v_a_3298_; uint8_t v___x_3299_; 
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3298_);
lean_dec_ref_known(v___x_3297_, 1);
v___x_3299_ = l_Lean_Exception_isInterrupt(v_a_3298_);
if (v___x_3299_ == 0)
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3300_ = l_Lean_Exception_toMessageData(v_a_3298_);
v___x_3301_ = l_Lean_logError___at___00main_spec__13(v___x_3300_, v___y_3289_, v___y_3287_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3289_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_dec_ref_known(v___x_3301_, 1);
v___y_3101_ = v___y_3260_;
v___y_3102_ = v___y_3259_;
v___y_3103_ = v___y_3261_;
v___y_3104_ = v___y_3262_;
v___y_3105_ = v___y_3263_;
v___y_3106_ = v___y_3264_;
v___y_3107_ = v___y_3266_;
v___y_3108_ = v___y_3265_;
v___y_3109_ = v___y_3267_;
v___y_3110_ = v___y_3268_;
v___y_3111_ = v___y_3284_;
v___y_3112_ = v___y_3269_;
v___y_3113_ = v___y_3285_;
v___y_3114_ = v___y_3286_;
v___y_3115_ = v___y_3279_;
v___y_3116_ = v___y_3288_;
v___y_3117_ = v___y_3280_;
v___y_3118_ = v___y_3282_;
v___y_3119_ = v___y_3281_;
v___y_3120_ = v___y_3283_;
v___y_3121_ = v___y_3290_;
goto v___jp_3100_;
}
else
{
lean_object* v___x_3302_; lean_object* v___x_3303_; 
lean_dec_ref_known(v___x_3301_, 1);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3286_);
lean_dec(v___y_3281_);
lean_dec(v___y_3264_);
lean_dec_ref(v___x_3099_);
lean_del_object(v___x_3092_);
lean_dec(v_fst_3089_);
lean_dec(v_name_3077_);
lean_dec(v_head_3061_);
lean_del_object(v___x_3059_);
lean_dec(v_head_3057_);
v___x_3302_ = lean_obj_once(&l_main___closed__17, &l_main___closed__17_once, _init_l_main___closed__17);
v___x_3303_ = l_panic___at___00main_spec__5(v___x_3302_);
return v___x_3303_;
}
}
else
{
lean_dec(v_a_3298_);
lean_dec_ref(v___y_3289_);
lean_dec(v___y_3287_);
v___y_3101_ = v___y_3260_;
v___y_3102_ = v___y_3259_;
v___y_3103_ = v___y_3261_;
v___y_3104_ = v___y_3262_;
v___y_3105_ = v___y_3263_;
v___y_3106_ = v___y_3264_;
v___y_3107_ = v___y_3266_;
v___y_3108_ = v___y_3265_;
v___y_3109_ = v___y_3267_;
v___y_3110_ = v___y_3268_;
v___y_3111_ = v___y_3284_;
v___y_3112_ = v___y_3269_;
v___y_3113_ = v___y_3285_;
v___y_3114_ = v___y_3286_;
v___y_3115_ = v___y_3279_;
v___y_3116_ = v___y_3288_;
v___y_3117_ = v___y_3280_;
v___y_3118_ = v___y_3282_;
v___y_3119_ = v___y_3281_;
v___y_3120_ = v___y_3283_;
v___y_3121_ = v___y_3290_;
goto v___jp_3100_;
}
}
}
}
v___jp_3304_:
{
lean_object* v_toCold_3331_; lean_object* v_currRecDepth_3332_; lean_object* v_ref_3333_; uint8_t v_suppressElabErrors_3334_; uint8_t v_isRecordingDeps_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3386_; 
v_toCold_3331_ = lean_ctor_get(v___y_3329_, 0);
v_currRecDepth_3332_ = lean_ctor_get(v___y_3329_, 1);
v_ref_3333_ = lean_ctor_get(v___y_3329_, 2);
v_suppressElabErrors_3334_ = lean_ctor_get_uint8(v___y_3329_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3335_ = lean_ctor_get_uint8(v___y_3329_, sizeof(void*)*3 + 3);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___y_3329_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3337_ = v___y_3329_;
v_isShared_3338_ = v_isSharedCheck_3386_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_ref_3333_);
lean_inc(v_currRecDepth_3332_);
lean_inc(v_toCold_3331_);
lean_dec(v___y_3329_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3386_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v_fileName_3339_; lean_object* v_fileMap_3340_; lean_object* v_currNamespace_3341_; lean_object* v_openDecls_3342_; lean_object* v_initHeartbeats_3343_; lean_object* v_maxHeartbeats_3344_; lean_object* v_quotContext_3345_; lean_object* v_currMacroScope_3346_; lean_object* v_cancelTk_x3f_3347_; lean_object* v_inheritedTraceOptions_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3383_; 
v_fileName_3339_ = lean_ctor_get(v_toCold_3331_, 0);
v_fileMap_3340_ = lean_ctor_get(v_toCold_3331_, 1);
v_currNamespace_3341_ = lean_ctor_get(v_toCold_3331_, 4);
v_openDecls_3342_ = lean_ctor_get(v_toCold_3331_, 5);
v_initHeartbeats_3343_ = lean_ctor_get(v_toCold_3331_, 6);
v_maxHeartbeats_3344_ = lean_ctor_get(v_toCold_3331_, 7);
v_quotContext_3345_ = lean_ctor_get(v_toCold_3331_, 8);
v_currMacroScope_3346_ = lean_ctor_get(v_toCold_3331_, 9);
v_cancelTk_x3f_3347_ = lean_ctor_get(v_toCold_3331_, 10);
v_inheritedTraceOptions_3348_ = lean_ctor_get(v_toCold_3331_, 11);
v_isSharedCheck_3383_ = !lean_is_exclusive(v_toCold_3331_);
if (v_isSharedCheck_3383_ == 0)
{
lean_object* v_unused_3384_; lean_object* v_unused_3385_; 
v_unused_3384_ = lean_ctor_get(v_toCold_3331_, 3);
lean_dec(v_unused_3384_);
v_unused_3385_ = lean_ctor_get(v_toCold_3331_, 2);
lean_dec(v_unused_3385_);
v___x_3350_ = v_toCold_3331_;
v_isShared_3351_ = v_isSharedCheck_3383_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_inheritedTraceOptions_3348_);
lean_inc(v_cancelTk_x3f_3347_);
lean_inc(v_currMacroScope_3346_);
lean_inc(v_quotContext_3345_);
lean_inc(v_maxHeartbeats_3344_);
lean_inc(v_initHeartbeats_3343_);
lean_inc(v_openDecls_3342_);
lean_inc(v_currNamespace_3341_);
lean_inc(v_fileMap_3340_);
lean_inc(v_fileName_3339_);
lean_dec(v_toCold_3331_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3383_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3355_; 
v___x_3352_ = l_Lean_maxRecDepth;
v___x_3353_ = l_Lean_Option_get___at___00main_spec__8(v___x_3099_, v___x_3352_);
lean_inc_ref(v___x_3099_);
if (v_isShared_3351_ == 0)
{
lean_ctor_set(v___x_3350_, 3, v___x_3353_);
lean_ctor_set(v___x_3350_, 2, v___x_3099_);
v___x_3355_ = v___x_3350_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_fileName_3339_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v_fileMap_3340_);
lean_ctor_set(v_reuseFailAlloc_3382_, 2, v___x_3099_);
lean_ctor_set(v_reuseFailAlloc_3382_, 3, v___x_3353_);
lean_ctor_set(v_reuseFailAlloc_3382_, 4, v_currNamespace_3341_);
lean_ctor_set(v_reuseFailAlloc_3382_, 5, v_openDecls_3342_);
lean_ctor_set(v_reuseFailAlloc_3382_, 6, v_initHeartbeats_3343_);
lean_ctor_set(v_reuseFailAlloc_3382_, 7, v_maxHeartbeats_3344_);
lean_ctor_set(v_reuseFailAlloc_3382_, 8, v_quotContext_3345_);
lean_ctor_set(v_reuseFailAlloc_3382_, 9, v_currMacroScope_3346_);
lean_ctor_set(v_reuseFailAlloc_3382_, 10, v_cancelTk_x3f_3347_);
lean_ctor_set(v_reuseFailAlloc_3382_, 11, v_inheritedTraceOptions_3348_);
v___x_3355_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
lean_object* v___x_3357_; 
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 0, v___x_3355_);
v___x_3357_ = v___x_3337_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3355_);
lean_ctor_set(v_reuseFailAlloc_3381_, 1, v_currRecDepth_3332_);
lean_ctor_set(v_reuseFailAlloc_3381_, 2, v_ref_3333_);
lean_ctor_set_uint8(v_reuseFailAlloc_3381_, sizeof(void*)*3 + 2, v_suppressElabErrors_3334_);
lean_ctor_set_uint8(v_reuseFailAlloc_3381_, sizeof(void*)*3 + 3, v_isRecordingDeps_3335_);
v___x_3357_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
lean_object* v___x_3358_; lean_object* v_env_3359_; lean_object* v_nextMacroScope_3360_; lean_object* v_ngen_3361_; lean_object* v_auxDeclNGen_3362_; lean_object* v_traceState_3363_; lean_object* v_recordedDeps_3364_; lean_object* v_messages_3365_; lean_object* v_infoState_3366_; lean_object* v_snapshotTasks_3367_; lean_object* v___x_3368_; uint8_t v___x_3369_; 
lean_ctor_set_uint16(v___x_3357_, sizeof(void*)*3, v___y_3326_);
v___x_3358_ = lean_st_ref_take(v___y_3330_);
v_env_3359_ = lean_ctor_get(v___x_3358_, 0);
lean_inc_ref(v_env_3359_);
v_nextMacroScope_3360_ = lean_ctor_get(v___x_3358_, 1);
lean_inc(v_nextMacroScope_3360_);
v_ngen_3361_ = lean_ctor_get(v___x_3358_, 2);
lean_inc_ref(v_ngen_3361_);
v_auxDeclNGen_3362_ = lean_ctor_get(v___x_3358_, 3);
lean_inc_ref(v_auxDeclNGen_3362_);
v_traceState_3363_ = lean_ctor_get(v___x_3358_, 4);
lean_inc_ref(v_traceState_3363_);
v_recordedDeps_3364_ = lean_ctor_get(v___x_3358_, 6);
lean_inc_ref(v_recordedDeps_3364_);
v_messages_3365_ = lean_ctor_get(v___x_3358_, 7);
lean_inc_ref(v_messages_3365_);
v_infoState_3366_ = lean_ctor_get(v___x_3358_, 8);
lean_inc_ref(v_infoState_3366_);
v_snapshotTasks_3367_ = lean_ctor_get(v___x_3358_, 9);
lean_inc_ref(v_snapshotTasks_3367_);
lean_dec(v___x_3358_);
v___x_3368_ = lean_array_get_size(v___y_3316_);
v___x_3369_ = lean_nat_dec_lt(v___x_3098_, v___x_3368_);
if (v___x_3369_ == 0)
{
lean_object* v___x_3370_; 
lean_inc_ref(v___y_3325_);
v___x_3370_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3325_, v_env_3359_, v___x_3073_);
v___y_3259_ = v___y_3306_;
v___y_3260_ = v___y_3305_;
v___y_3261_ = v___y_3307_;
v___y_3262_ = v___y_3308_;
v___y_3263_ = v___y_3309_;
v___y_3264_ = v___y_3310_;
v___y_3265_ = v___y_3312_;
v___y_3266_ = v___y_3311_;
v___y_3267_ = v___y_3313_;
v___y_3268_ = v___y_3314_;
v___y_3269_ = v___y_3315_;
v_nextMacroScope_3270_ = v_nextMacroScope_3360_;
v_ngen_3271_ = v_ngen_3361_;
v_auxDeclNGen_3272_ = v_auxDeclNGen_3362_;
v_traceState_3273_ = v_traceState_3363_;
v_recordedDeps_3274_ = v_recordedDeps_3364_;
v_messages_3275_ = v_messages_3365_;
v_infoState_3276_ = v_infoState_3366_;
v_snapshotTasks_3277_ = v_snapshotTasks_3367_;
v___y_3278_ = v___y_3316_;
v___y_3279_ = v___y_3317_;
v___y_3280_ = v___y_3318_;
v___y_3281_ = v___y_3319_;
v___y_3282_ = v___y_3320_;
v___y_3283_ = v___y_3321_;
v___y_3284_ = v___y_3322_;
v___y_3285_ = v___y_3323_;
v___y_3286_ = v___y_3324_;
v___y_3287_ = v___y_3330_;
v___y_3288_ = v___y_3327_;
v___y_3289_ = v___x_3357_;
v___y_3290_ = v___y_3328_;
v___y_3291_ = v___x_3370_;
goto v___jp_3258_;
}
else
{
uint8_t v___x_3371_; 
v___x_3371_ = lean_nat_dec_le(v___x_3368_, v___x_3368_);
if (v___x_3371_ == 0)
{
if (v___x_3369_ == 0)
{
lean_object* v___x_3372_; 
lean_inc_ref(v___y_3325_);
v___x_3372_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3325_, v_env_3359_, v___x_3073_);
v___y_3259_ = v___y_3306_;
v___y_3260_ = v___y_3305_;
v___y_3261_ = v___y_3307_;
v___y_3262_ = v___y_3308_;
v___y_3263_ = v___y_3309_;
v___y_3264_ = v___y_3310_;
v___y_3265_ = v___y_3312_;
v___y_3266_ = v___y_3311_;
v___y_3267_ = v___y_3313_;
v___y_3268_ = v___y_3314_;
v___y_3269_ = v___y_3315_;
v_nextMacroScope_3270_ = v_nextMacroScope_3360_;
v_ngen_3271_ = v_ngen_3361_;
v_auxDeclNGen_3272_ = v_auxDeclNGen_3362_;
v_traceState_3273_ = v_traceState_3363_;
v_recordedDeps_3274_ = v_recordedDeps_3364_;
v_messages_3275_ = v_messages_3365_;
v_infoState_3276_ = v_infoState_3366_;
v_snapshotTasks_3277_ = v_snapshotTasks_3367_;
v___y_3278_ = v___y_3316_;
v___y_3279_ = v___y_3317_;
v___y_3280_ = v___y_3318_;
v___y_3281_ = v___y_3319_;
v___y_3282_ = v___y_3320_;
v___y_3283_ = v___y_3321_;
v___y_3284_ = v___y_3322_;
v___y_3285_ = v___y_3323_;
v___y_3286_ = v___y_3324_;
v___y_3287_ = v___y_3330_;
v___y_3288_ = v___y_3327_;
v___y_3289_ = v___x_3357_;
v___y_3290_ = v___y_3328_;
v___y_3291_ = v___x_3372_;
goto v___jp_3258_;
}
else
{
size_t v___x_3373_; size_t v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3373_ = ((size_t)0ULL);
v___x_3374_ = lean_usize_of_nat(v___x_3368_);
v___x_3375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v___y_3316_, v___x_3373_, v___x_3374_, v___x_3073_);
lean_inc_ref(v___y_3325_);
v___x_3376_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3325_, v_env_3359_, v___x_3375_);
v___y_3259_ = v___y_3306_;
v___y_3260_ = v___y_3305_;
v___y_3261_ = v___y_3307_;
v___y_3262_ = v___y_3308_;
v___y_3263_ = v___y_3309_;
v___y_3264_ = v___y_3310_;
v___y_3265_ = v___y_3312_;
v___y_3266_ = v___y_3311_;
v___y_3267_ = v___y_3313_;
v___y_3268_ = v___y_3314_;
v___y_3269_ = v___y_3315_;
v_nextMacroScope_3270_ = v_nextMacroScope_3360_;
v_ngen_3271_ = v_ngen_3361_;
v_auxDeclNGen_3272_ = v_auxDeclNGen_3362_;
v_traceState_3273_ = v_traceState_3363_;
v_recordedDeps_3274_ = v_recordedDeps_3364_;
v_messages_3275_ = v_messages_3365_;
v_infoState_3276_ = v_infoState_3366_;
v_snapshotTasks_3277_ = v_snapshotTasks_3367_;
v___y_3278_ = v___y_3316_;
v___y_3279_ = v___y_3317_;
v___y_3280_ = v___y_3318_;
v___y_3281_ = v___y_3319_;
v___y_3282_ = v___y_3320_;
v___y_3283_ = v___y_3321_;
v___y_3284_ = v___y_3322_;
v___y_3285_ = v___y_3323_;
v___y_3286_ = v___y_3324_;
v___y_3287_ = v___y_3330_;
v___y_3288_ = v___y_3327_;
v___y_3289_ = v___x_3357_;
v___y_3290_ = v___y_3328_;
v___y_3291_ = v___x_3376_;
goto v___jp_3258_;
}
}
else
{
size_t v___x_3377_; size_t v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3377_ = ((size_t)0ULL);
v___x_3378_ = lean_usize_of_nat(v___x_3368_);
v___x_3379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v___y_3316_, v___x_3377_, v___x_3378_, v___x_3073_);
lean_inc_ref(v___y_3325_);
v___x_3380_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3325_, v_env_3359_, v___x_3379_);
v___y_3259_ = v___y_3306_;
v___y_3260_ = v___y_3305_;
v___y_3261_ = v___y_3307_;
v___y_3262_ = v___y_3308_;
v___y_3263_ = v___y_3309_;
v___y_3264_ = v___y_3310_;
v___y_3265_ = v___y_3312_;
v___y_3266_ = v___y_3311_;
v___y_3267_ = v___y_3313_;
v___y_3268_ = v___y_3314_;
v___y_3269_ = v___y_3315_;
v_nextMacroScope_3270_ = v_nextMacroScope_3360_;
v_ngen_3271_ = v_ngen_3361_;
v_auxDeclNGen_3272_ = v_auxDeclNGen_3362_;
v_traceState_3273_ = v_traceState_3363_;
v_recordedDeps_3274_ = v_recordedDeps_3364_;
v_messages_3275_ = v_messages_3365_;
v_infoState_3276_ = v_infoState_3366_;
v_snapshotTasks_3277_ = v_snapshotTasks_3367_;
v___y_3278_ = v___y_3316_;
v___y_3279_ = v___y_3317_;
v___y_3280_ = v___y_3318_;
v___y_3281_ = v___y_3319_;
v___y_3282_ = v___y_3320_;
v___y_3283_ = v___y_3321_;
v___y_3284_ = v___y_3322_;
v___y_3285_ = v___y_3323_;
v___y_3286_ = v___y_3324_;
v___y_3287_ = v___y_3330_;
v___y_3288_ = v___y_3327_;
v___y_3289_ = v___x_3357_;
v___y_3290_ = v___y_3328_;
v___y_3291_ = v___x_3380_;
goto v___jp_3258_;
}
}
}
}
}
}
}
v___jp_3387_:
{
lean_object* v___x_3414_; lean_object* v_env_3415_; lean_object* v_nextMacroScope_3416_; lean_object* v_ngen_3417_; lean_object* v_auxDeclNGen_3418_; lean_object* v_traceState_3419_; lean_object* v_recordedDeps_3420_; lean_object* v_messages_3421_; lean_object* v_infoState_3422_; lean_object* v_snapshotTasks_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3432_; 
v___x_3414_ = lean_st_ref_take(v___y_3402_);
v_env_3415_ = lean_ctor_get(v___x_3414_, 0);
v_nextMacroScope_3416_ = lean_ctor_get(v___x_3414_, 1);
v_ngen_3417_ = lean_ctor_get(v___x_3414_, 2);
v_auxDeclNGen_3418_ = lean_ctor_get(v___x_3414_, 3);
v_traceState_3419_ = lean_ctor_get(v___x_3414_, 4);
v_recordedDeps_3420_ = lean_ctor_get(v___x_3414_, 6);
v_messages_3421_ = lean_ctor_get(v___x_3414_, 7);
v_infoState_3422_ = lean_ctor_get(v___x_3414_, 8);
v_snapshotTasks_3423_ = lean_ctor_get(v___x_3414_, 9);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3432_ == 0)
{
lean_object* v_unused_3433_; 
v_unused_3433_ = lean_ctor_get(v___x_3414_, 5);
lean_dec(v_unused_3433_);
v___x_3425_ = v___x_3414_;
v_isShared_3426_ = v_isSharedCheck_3432_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_snapshotTasks_3423_);
lean_inc(v_infoState_3422_);
lean_inc(v_messages_3421_);
lean_inc(v_recordedDeps_3420_);
lean_inc(v_traceState_3419_);
lean_inc(v_auxDeclNGen_3418_);
lean_inc(v_ngen_3417_);
lean_inc(v_nextMacroScope_3416_);
lean_inc(v_env_3415_);
lean_dec(v___x_3414_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3432_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3427_; lean_object* v___x_3429_; 
v___x_3427_ = l_Lean_Kernel_enableDiag(v_env_3415_, v___y_3404_);
lean_inc_ref(v___y_3406_);
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 5, v___y_3406_);
lean_ctor_set(v___x_3425_, 0, v___x_3427_);
v___x_3429_ = v___x_3425_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3427_);
lean_ctor_set(v_reuseFailAlloc_3431_, 1, v_nextMacroScope_3416_);
lean_ctor_set(v_reuseFailAlloc_3431_, 2, v_ngen_3417_);
lean_ctor_set(v_reuseFailAlloc_3431_, 3, v_auxDeclNGen_3418_);
lean_ctor_set(v_reuseFailAlloc_3431_, 4, v_traceState_3419_);
lean_ctor_set(v_reuseFailAlloc_3431_, 5, v___y_3406_);
lean_ctor_set(v_reuseFailAlloc_3431_, 6, v_recordedDeps_3420_);
lean_ctor_set(v_reuseFailAlloc_3431_, 7, v_messages_3421_);
lean_ctor_set(v_reuseFailAlloc_3431_, 8, v_infoState_3422_);
lean_ctor_set(v_reuseFailAlloc_3431_, 9, v_snapshotTasks_3423_);
v___x_3429_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
lean_object* v___x_3430_; 
v___x_3430_ = lean_st_ref_put(v___y_3402_, v___x_3429_);
lean_inc(v___y_3402_);
v___y_3305_ = v___y_3389_;
v___y_3306_ = v___y_3388_;
v___y_3307_ = v___y_3390_;
v___y_3308_ = v___y_3391_;
v___y_3309_ = v___y_3392_;
v___y_3310_ = v___y_3393_;
v___y_3311_ = v___y_3395_;
v___y_3312_ = v___y_3394_;
v___y_3313_ = v___y_3396_;
v___y_3314_ = v___y_3397_;
v___y_3315_ = v___y_3398_;
v___y_3316_ = v___y_3399_;
v___y_3317_ = v___y_3400_;
v___y_3318_ = v___y_3401_;
v___y_3319_ = v___y_3402_;
v___y_3320_ = v___y_3403_;
v___y_3321_ = v___y_3405_;
v___y_3322_ = v___y_3406_;
v___y_3323_ = v___y_3407_;
v___y_3324_ = v___y_3408_;
v___y_3325_ = v___y_3411_;
v___y_3326_ = v___y_3410_;
v___y_3327_ = v___y_3409_;
v___y_3328_ = v___y_3413_;
v___y_3329_ = v___y_3412_;
v___y_3330_ = v___y_3402_;
goto v___jp_3304_;
}
}
}
v___jp_3434_:
{
if (v___y_3461_ == 0)
{
v___y_3388_ = v___y_3436_;
v___y_3389_ = v___y_3435_;
v___y_3390_ = v___y_3437_;
v___y_3391_ = v___y_3438_;
v___y_3392_ = v___y_3439_;
v___y_3393_ = v___y_3440_;
v___y_3394_ = v___y_3442_;
v___y_3395_ = v___y_3441_;
v___y_3396_ = v___y_3443_;
v___y_3397_ = v___y_3444_;
v___y_3398_ = v___y_3445_;
v___y_3399_ = v___y_3446_;
v___y_3400_ = v___y_3447_;
v___y_3401_ = v___y_3448_;
v___y_3402_ = v___y_3449_;
v___y_3403_ = v___y_3450_;
v___y_3404_ = v___y_3451_;
v___y_3405_ = v___y_3452_;
v___y_3406_ = v___y_3453_;
v___y_3407_ = v___y_3454_;
v___y_3408_ = v___y_3455_;
v___y_3409_ = v___y_3458_;
v___y_3410_ = v___y_3457_;
v___y_3411_ = v___y_3456_;
v___y_3412_ = v___y_3459_;
v___y_3413_ = v___y_3460_;
goto v___jp_3387_;
}
else
{
lean_inc(v___y_3449_);
v___y_3305_ = v___y_3435_;
v___y_3306_ = v___y_3436_;
v___y_3307_ = v___y_3437_;
v___y_3308_ = v___y_3438_;
v___y_3309_ = v___y_3439_;
v___y_3310_ = v___y_3440_;
v___y_3311_ = v___y_3441_;
v___y_3312_ = v___y_3442_;
v___y_3313_ = v___y_3443_;
v___y_3314_ = v___y_3444_;
v___y_3315_ = v___y_3445_;
v___y_3316_ = v___y_3446_;
v___y_3317_ = v___y_3447_;
v___y_3318_ = v___y_3448_;
v___y_3319_ = v___y_3449_;
v___y_3320_ = v___y_3450_;
v___y_3321_ = v___y_3452_;
v___y_3322_ = v___y_3453_;
v___y_3323_ = v___y_3454_;
v___y_3324_ = v___y_3455_;
v___y_3325_ = v___y_3456_;
v___y_3326_ = v___y_3457_;
v___y_3327_ = v___y_3458_;
v___y_3328_ = v___y_3460_;
v___y_3329_ = v___y_3459_;
v___y_3330_ = v___y_3449_;
goto v___jp_3304_;
}
}
v___jp_3462_:
{
if (v___y_3485_ == 0)
{
v___y_3435_ = v___y_3471_;
v___y_3436_ = v___y_3470_;
v___y_3437_ = v___y_3463_;
v___y_3438_ = v___y_3473_;
v___y_3439_ = v___y_3464_;
v___y_3440_ = v___y_3476_;
v___y_3441_ = v___y_3467_;
v___y_3442_ = v___y_3477_;
v___y_3443_ = v___y_3468_;
v___y_3444_ = v___y_3479_;
v___y_3445_ = v___y_3463_;
v___y_3446_ = v___y_3465_;
v___y_3447_ = v___y_3480_;
v___y_3448_ = v___y_3466_;
v___y_3449_ = v___y_3481_;
v___y_3450_ = v___y_3482_;
v___y_3451_ = v___y_3488_;
v___y_3452_ = v___y_3469_;
v___y_3453_ = v___y_3470_;
v___y_3454_ = v___y_3483_;
v___y_3455_ = v___y_3472_;
v___y_3456_ = v___y_3474_;
v___y_3457_ = v___y_3475_;
v___y_3458_ = v___y_3486_;
v___y_3459_ = v___y_3487_;
v___y_3460_ = v___y_3478_;
v___y_3461_ = v___y_3484_;
goto v___jp_3434_;
}
else
{
v___y_3388_ = v___y_3470_;
v___y_3389_ = v___y_3471_;
v___y_3390_ = v___y_3463_;
v___y_3391_ = v___y_3473_;
v___y_3392_ = v___y_3464_;
v___y_3393_ = v___y_3476_;
v___y_3394_ = v___y_3477_;
v___y_3395_ = v___y_3467_;
v___y_3396_ = v___y_3468_;
v___y_3397_ = v___y_3479_;
v___y_3398_ = v___y_3463_;
v___y_3399_ = v___y_3465_;
v___y_3400_ = v___y_3480_;
v___y_3401_ = v___y_3466_;
v___y_3402_ = v___y_3481_;
v___y_3403_ = v___y_3482_;
v___y_3404_ = v___y_3488_;
v___y_3405_ = v___y_3469_;
v___y_3406_ = v___y_3470_;
v___y_3407_ = v___y_3483_;
v___y_3408_ = v___y_3472_;
v___y_3409_ = v___y_3486_;
v___y_3410_ = v___y_3475_;
v___y_3411_ = v___y_3474_;
v___y_3412_ = v___y_3487_;
v___y_3413_ = v___y_3478_;
goto v___jp_3387_;
}
}
}
}
else
{
lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3798_; 
lean_dec_ref(v___f_3081_);
lean_dec(v_importArts_3079_);
lean_dec(v_name_3077_);
lean_dec(v_head_3061_);
lean_del_object(v___x_3059_);
lean_dec(v_head_3057_);
lean_del_object(v___x_3055_);
v_a_3791_ = lean_ctor_get(v___x_3087_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3793_ = v___x_3087_;
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v___x_3087_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3796_; 
if (v_isShared_3794_ == 0)
{
v___x_3796_ = v___x_3793_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_a_3791_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
}
}
else
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3807_; 
lean_del_object(v___x_3064_);
lean_dec(v_tail_3062_);
lean_dec(v_head_3061_);
lean_del_object(v___x_3059_);
lean_dec(v_head_3057_);
lean_del_object(v___x_3055_);
v_a_3800_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3802_ = v___x_3075_;
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v___x_3075_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3805_; 
if (v_isShared_3803_ == 0)
{
v___x_3805_ = v___x_3802_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_a_3800_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
}
}
}
}
else
{
lean_dec(v_tail_3052_);
lean_dec_ref_known(v_tail_3051_, 2);
lean_dec_ref_known(v_args_3026_, 2);
goto v___jp_3031_;
}
}
else
{
lean_dec_ref_known(v_args_3026_, 2);
lean_dec(v_tail_3051_);
goto v___jp_3031_;
}
}
else
{
lean_dec(v_args_3026_);
goto v___jp_3031_;
}
v___jp_3028_:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3029_ = l_main___boxed__const__1;
v___x_3030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3029_);
return v___x_3030_;
}
v___jp_3031_:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3032_ = ((lean_object*)(l_main___closed__0));
v___x_3033_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_3032_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3041_; 
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3041_ == 0)
{
lean_object* v_unused_3042_; 
v_unused_3042_ = lean_ctor_get(v___x_3033_, 0);
lean_dec(v_unused_3042_);
v___x_3035_ = v___x_3033_;
v_isShared_3036_ = v_isSharedCheck_3041_;
goto v_resetjp_3034_;
}
else
{
lean_dec(v___x_3033_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3041_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3037_; lean_object* v___x_3039_; 
v___x_3037_ = l_main___boxed__const__2;
if (v_isShared_3036_ == 0)
{
lean_ctor_set(v___x_3035_, 0, v___x_3037_);
v___x_3039_ = v___x_3035_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3037_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
else
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
v_a_3043_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_3033_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3033_);
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
}
LEAN_EXPORT void _lean_main_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_3026_ = stack[0].m_obj;
lean_object* v_res_3813_;
v_res_3813_ = _lean_main(v_args_3026_);
stack->m_obj
 = v_res_3813_;
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_3814_, lean_object* v_a_3815_){
_start:
{
lean_object* v_res_3816_; 
v_res_3816_ = _lean_main(v_args_3814_);
return v_res_3816_;
}
}
lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object* v_as_3817_, lean_object* v_as_x27_3818_, lean_object* v_b_3819_, lean_object* v_a_3820_){
_start:
{
lean_object* v___x_3822_; 
v___x_3822_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_3818_, v_b_3819_);
return v___x_3822_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00main_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3817_ = stack[0].m_obj;
lean_object* v_as_x27_3818_ = stack[1].m_obj;
lean_object* v_b_3819_ = stack[2].m_obj;
lean_object* v_res_3823_;
v_res_3823_ = l_List_forIn_x27_loop___at___00main_spec__1(v_as_3817_, v_as_x27_3818_, v_b_3819_, lean_box(0));
stack->m_obj
 = v_res_3823_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object* v_as_3824_, lean_object* v_as_x27_3825_, lean_object* v_b_3826_, lean_object* v_a_3827_, lean_object* v___y_3828_){
_start:
{
lean_object* v_res_3829_; 
v_res_3829_ = l_List_forIn_x27_loop___at___00main_spec__1(v_as_3824_, v_as_x27_3825_, v_b_3826_, v_a_3827_);
lean_dec(v_as_x27_3825_);
lean_dec(v_as_3824_);
return v_res_3829_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16(lean_object* v___y_3830_, lean_object* v___y_3831_){
_start:
{
lean_object* v___x_3833_; 
v___x_3833_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___y_3831_);
return v___x_3833_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3830_ = stack[0].m_obj;
lean_object* v___y_3831_ = stack[1].m_obj;
lean_object* v_res_3834_;
v_res_3834_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16(v___y_3830_, v___y_3831_);
stack->m_obj
 = v_res_3834_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___boxed(lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16(v___y_3835_, v___y_3836_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17(lean_object* v_00_u03b2_3839_, lean_object* v_m_3840_, lean_object* v_a_3841_, lean_object* v_fallback_3842_){
_start:
{
lean_object* v___x_3843_; 
v___x_3843_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_m_3840_, v_a_3841_, v_fallback_3842_);
return v___x_3843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___boxed(lean_object* v_00_u03b2_3844_, lean_object* v_m_3845_, lean_object* v_a_3846_, lean_object* v_fallback_3847_){
_start:
{
lean_object* v_res_3848_; 
v_res_3848_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17(v_00_u03b2_3844_, v_m_3845_, v_a_3846_, v_fallback_3847_);
lean_dec(v_fallback_3847_);
lean_dec_ref(v_a_3846_);
lean_dec_ref(v_m_3845_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18(lean_object* v_00_u03b2_3849_, lean_object* v_m_3850_, lean_object* v_a_3851_, lean_object* v_b_3852_){
_start:
{
lean_object* v___x_3853_; 
v___x_3853_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_m_3850_, v_a_3851_, v_b_3852_);
return v___x_3853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21(lean_object* v_n_3854_, lean_object* v_as_3855_, lean_object* v_lo_3856_, lean_object* v_hi_3857_, lean_object* v_w_3858_, lean_object* v_hlo_3859_, lean_object* v_hhi_3860_){
_start:
{
lean_object* v___x_3861_; 
v___x_3861_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v_n_3854_, v_as_3855_, v_lo_3856_, v_hi_3857_);
return v___x_3861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___boxed(lean_object* v_n_3862_, lean_object* v_as_3863_, lean_object* v_lo_3864_, lean_object* v_hi_3865_, lean_object* v_w_3866_, lean_object* v_hlo_3867_, lean_object* v_hhi_3868_){
_start:
{
lean_object* v_res_3869_; 
v_res_3869_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21(v_n_3862_, v_as_3863_, v_lo_3864_, v_hi_3865_, v_w_3866_, v_hlo_3867_, v_hhi_3868_);
lean_dec(v_hi_3865_);
lean_dec(v_n_3862_);
return v_res_3869_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21(lean_object* v_00_u03b2_3870_, lean_object* v_a_3871_, lean_object* v_fallback_3872_, lean_object* v_x_3873_){
_start:
{
lean_object* v___x_3874_; 
v___x_3874_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(v_a_3871_, v_fallback_3872_, v_x_3873_);
return v___x_3874_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3875_, lean_object* v_a_3876_, lean_object* v_fallback_3877_, lean_object* v_x_3878_){
_start:
{
lean_object* v_res_3879_; 
v_res_3879_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21(v_00_u03b2_3875_, v_a_3876_, v_fallback_3877_, v_x_3878_);
lean_dec(v_x_3878_);
lean_dec(v_fallback_3877_);
lean_dec_ref(v_a_3876_);
return v_res_3879_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23(lean_object* v_00_u03b2_3880_, lean_object* v_a_3881_, lean_object* v_x_3882_){
_start:
{
uint8_t v___x_3883_; 
v___x_3883_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(v_a_3881_, v_x_3882_);
return v___x_3883_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3881_ = stack[1].m_obj;
lean_object* v_x_3882_ = stack[2].m_obj;
uint8_t v_res_3884_;
v_res_3884_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23(lean_box(0), v_a_3881_, v_x_3882_);
stack->m_num = v_res_3884_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___boxed(lean_object* v_00_u03b2_3885_, lean_object* v_a_3886_, lean_object* v_x_3887_){
_start:
{
uint8_t v_res_3888_; lean_object* v_r_3889_; 
v_res_3888_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23(v_00_u03b2_3885_, v_a_3886_, v_x_3887_);
lean_dec(v_x_3887_);
lean_dec_ref(v_a_3886_);
v_r_3889_ = lean_box(v_res_3888_);
return v_r_3889_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24(lean_object* v_00_u03b2_3890_, lean_object* v_data_3891_){
_start:
{
lean_object* v___x_3892_; 
v___x_3892_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24___redArg(v_data_3891_);
return v___x_3892_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25(lean_object* v_00_u03b2_3893_, lean_object* v_a_3894_, lean_object* v_b_3895_, lean_object* v_x_3896_){
_start:
{
lean_object* v___x_3897_; 
v___x_3897_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(v_a_3894_, v_b_3895_, v_x_3896_);
return v___x_3897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31(lean_object* v_n_3898_, lean_object* v_lo_3899_, lean_object* v_hi_3900_, lean_object* v_hhi_3901_, lean_object* v_pivot_3902_, lean_object* v_as_3903_, lean_object* v_i_3904_, lean_object* v_k_3905_, lean_object* v_ilo_3906_, lean_object* v_ik_3907_, lean_object* v_w_3908_){
_start:
{
lean_object* v___x_3909_; 
v___x_3909_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(v_hi_3900_, v_pivot_3902_, v_as_3903_, v_i_3904_, v_k_3905_);
return v___x_3909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___boxed(lean_object* v_n_3910_, lean_object* v_lo_3911_, lean_object* v_hi_3912_, lean_object* v_hhi_3913_, lean_object* v_pivot_3914_, lean_object* v_as_3915_, lean_object* v_i_3916_, lean_object* v_k_3917_, lean_object* v_ilo_3918_, lean_object* v_ik_3919_, lean_object* v_w_3920_){
_start:
{
lean_object* v_res_3921_; 
v_res_3921_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31(v_n_3910_, v_lo_3911_, v_hi_3912_, v_hhi_3913_, v_pivot_3914_, v_as_3915_, v_i_3916_, v_k_3917_, v_ilo_3918_, v_ik_3919_, v_w_3920_);
lean_dec_ref(v_pivot_3914_);
lean_dec(v_hi_3912_);
lean_dec(v_lo_3911_);
lean_dec(v_n_3910_);
return v_res_3921_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40(lean_object* v_as_3922_, size_t v_sz_3923_, size_t v_i_3924_, lean_object* v_b_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_){
_start:
{
lean_object* v___x_3929_; 
v___x_3929_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(v_as_3922_, v_sz_3923_, v_i_3924_, v_b_3925_, v___y_3926_);
return v___x_3929_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3922_ = stack[0].m_obj;
size_t v_sz_3923_ = stack[1].m_num;
size_t v_i_3924_ = stack[2].m_num;
lean_object* v_b_3925_ = stack[3].m_obj;
lean_object* v___y_3926_ = stack[4].m_obj;
lean_object* v___y_3927_ = stack[5].m_obj;
lean_object* v_res_3930_;
v_res_3930_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40(v_as_3922_, v_sz_3923_, v_i_3924_, v_b_3925_, v___y_3926_, v___y_3927_);
stack->m_obj
 = v_res_3930_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___boxed(lean_object* v_as_3931_, lean_object* v_sz_3932_, lean_object* v_i_3933_, lean_object* v_b_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_){
_start:
{
size_t v_sz_boxed_3938_; size_t v_i_boxed_3939_; lean_object* v_res_3940_; 
v_sz_boxed_3938_ = lean_unbox_usize(v_sz_3932_);
lean_dec(v_sz_3932_);
v_i_boxed_3939_ = lean_unbox_usize(v_i_3933_);
lean_dec(v_i_3933_);
v_res_3940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40(v_as_3931_, v_sz_boxed_3938_, v_i_boxed_3939_, v_b_3934_, v___y_3935_, v___y_3936_);
lean_dec(v___y_3936_);
lean_dec_ref(v___y_3935_);
lean_dec_ref(v_as_3931_);
return v_res_3940_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35(lean_object* v_00_u03b2_3941_, lean_object* v_i_3942_, lean_object* v_source_3943_, lean_object* v_target_3944_){
_start:
{
lean_object* v___x_3945_; 
v___x_3945_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35___redArg(v_i_3942_, v_source_3943_, v_target_3944_);
return v___x_3945_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42(uint8_t v___x_3946_, lean_object* v_as_3947_, size_t v_sz_3948_, size_t v_i_3949_, lean_object* v_b_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_){
_start:
{
lean_object* v___x_3954_; 
v___x_3954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(v___x_3946_, v_as_3947_, v_sz_3948_, v_i_3949_, v_b_3950_, v___y_3951_);
return v___x_3954_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_3946_ = stack[0].m_num;
lean_object* v_as_3947_ = stack[1].m_obj;
size_t v_sz_3948_ = stack[2].m_num;
size_t v_i_3949_ = stack[3].m_num;
lean_object* v_b_3950_ = stack[4].m_obj;
lean_object* v___y_3951_ = stack[5].m_obj;
lean_object* v___y_3952_ = stack[6].m_obj;
lean_object* v_res_3955_;
v_res_3955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42(v___x_3946_, v_as_3947_, v_sz_3948_, v_i_3949_, v_b_3950_, v___y_3951_, v___y_3952_);
stack->m_obj
 = v_res_3955_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___boxed(lean_object* v___x_3956_, lean_object* v_as_3957_, lean_object* v_sz_3958_, lean_object* v_i_3959_, lean_object* v_b_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_){
_start:
{
uint8_t v___x_45197__boxed_3964_; size_t v_sz_boxed_3965_; size_t v_i_boxed_3966_; lean_object* v_res_3967_; 
v___x_45197__boxed_3964_ = lean_unbox(v___x_3956_);
v_sz_boxed_3965_ = lean_unbox_usize(v_sz_3958_);
lean_dec(v_sz_3958_);
v_i_boxed_3966_ = lean_unbox_usize(v_i_3959_);
lean_dec(v_i_3959_);
v_res_3967_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42(v___x_45197__boxed_3964_, v_as_3957_, v_sz_boxed_3965_, v_i_boxed_3966_, v_b_3960_, v___y_3961_, v___y_3962_);
lean_dec(v___y_3962_);
lean_dec_ref(v___y_3961_);
lean_dec_ref(v_as_3957_);
return v_res_3967_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51(lean_object* v_as_3968_, size_t v_sz_3969_, size_t v_i_3970_, lean_object* v_b_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_){
_start:
{
lean_object* v___x_3975_; 
v___x_3975_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(v_as_3968_, v_sz_3969_, v_i_3970_, v_b_3971_, v___y_3972_);
return v___x_3975_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3968_ = stack[0].m_obj;
size_t v_sz_3969_ = stack[1].m_num;
size_t v_i_3970_ = stack[2].m_num;
lean_object* v_b_3971_ = stack[3].m_obj;
lean_object* v___y_3972_ = stack[4].m_obj;
lean_object* v___y_3973_ = stack[5].m_obj;
lean_object* v_res_3976_;
v_res_3976_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51(v_as_3968_, v_sz_3969_, v_i_3970_, v_b_3971_, v___y_3972_, v___y_3973_);
stack->m_obj
 = v_res_3976_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___boxed(lean_object* v_as_3977_, lean_object* v_sz_3978_, lean_object* v_i_3979_, lean_object* v_b_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
size_t v_sz_boxed_3984_; size_t v_i_boxed_3985_; lean_object* v_res_3986_; 
v_sz_boxed_3984_ = lean_unbox_usize(v_sz_3978_);
lean_dec(v_sz_3978_);
v_i_boxed_3985_ = lean_unbox_usize(v_i_3979_);
lean_dec(v_i_3979_);
v_res_3986_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51(v_as_3977_, v_sz_boxed_3984_, v_i_boxed_3985_, v_b_3980_, v___y_3981_, v___y_3982_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec_ref(v_as_3977_);
return v_res_3986_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44(lean_object* v_00_u03b2_3987_, lean_object* v_x_3988_, lean_object* v_x_3989_){
_start:
{
lean_object* v___x_3990_; 
v___x_3990_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44___redArg(v_x_3988_, v_x_3989_);
return v___x_3990_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49(uint8_t v___x_3991_, lean_object* v_as_3992_, size_t v_sz_3993_, size_t v_i_3994_, lean_object* v_b_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_){
_start:
{
lean_object* v___x_3999_; 
v___x_3999_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(v___x_3991_, v_as_3992_, v_sz_3993_, v_i_3994_, v_b_3995_, v___y_3996_);
return v___x_3999_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_3991_ = stack[0].m_num;
lean_object* v_as_3992_ = stack[1].m_obj;
size_t v_sz_3993_ = stack[2].m_num;
size_t v_i_3994_ = stack[3].m_num;
lean_object* v_b_3995_ = stack[4].m_obj;
lean_object* v___y_3996_ = stack[5].m_obj;
lean_object* v___y_3997_ = stack[6].m_obj;
lean_object* v_res_4000_;
v_res_4000_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49(v___x_3991_, v_as_3992_, v_sz_3993_, v_i_3994_, v_b_3995_, v___y_3996_, v___y_3997_);
stack->m_obj
 = v_res_4000_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___boxed(lean_object* v___x_4001_, lean_object* v_as_4002_, lean_object* v_sz_4003_, lean_object* v_i_4004_, lean_object* v_b_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_){
_start:
{
uint8_t v___x_45247__boxed_4009_; size_t v_sz_boxed_4010_; size_t v_i_boxed_4011_; lean_object* v_res_4012_; 
v___x_45247__boxed_4009_ = lean_unbox(v___x_4001_);
v_sz_boxed_4010_ = lean_unbox_usize(v_sz_4003_);
lean_dec(v_sz_4003_);
v_i_boxed_4011_ = lean_unbox_usize(v_i_4004_);
lean_dec(v_i_4004_);
v_res_4012_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49(v___x_45247__boxed_4009_, v_as_4002_, v_sz_boxed_4010_, v_i_boxed_4011_, v_b_4005_, v___y_4006_, v___y_4007_);
lean_dec(v___y_4007_);
lean_dec_ref(v___y_4006_);
lean_dec_ref(v_as_4002_);
return v_res_4012_;
}
}
lean_object* runtime_initialize_Init(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_ForEachExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_Path(uint8_t builtin);
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Bytecode_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ModPkgExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_CSimpAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_EmitC(uint8_t builtin);
lean_object* runtime_initialize_Lean_Language_Lean(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_ExprDefEq(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_LevelDefEq(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_MatchEqs(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_Eqns(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser(uint8_t builtin);
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
res = runtime_initialize_Lean_Compiler_Bytecode_Basic(builtin);
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
res = runtime_initialize_Lean_Meta_ExprDefEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_LevelDefEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_MatchEqs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_Structural_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser(builtin);
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
lean_object* initialize_Lean_Compiler_Bytecode_Basic(uint8_t builtin);
lean_object* initialize_Lean_Compiler_ModPkgExt(uint8_t builtin);
lean_object* initialize_Lean_Compiler_CSimpAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_EmitC(uint8_t builtin);
lean_object* initialize_Lean_Language_Lean(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Main(uint8_t builtin);
lean_object* initialize_Lean_Meta_ExprDefEq(uint8_t builtin);
lean_object* initialize_Lean_Meta_LevelDefEq(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_MatchEqs(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_Structural_Eqns(uint8_t builtin);
lean_object* initialize_Lean_Parser(uint8_t builtin);
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
res = initialize_Lean_Compiler_Bytecode_Basic(builtin);
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
res = initialize_Lean_Meta_ExprDefEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LevelDefEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatchEqs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser(builtin);
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
