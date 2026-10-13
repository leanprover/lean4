// Lean compiler output
// Module: LeanIR
// Imports: public import Init public meta import Init import Lean.CoreM import Lean.Util.ForEachExpr import all Lean.Util.Path import all Lean.Environment import Lean.Compiler.Options import Lean.Compiler.IR.CompilerM import Lean.Compiler.ModPkgExt import all Lean.Compiler.CSimpAttr import Lean.Compiler.LCNF.EmitC import Lean.Language.Lean import Lean.Compiler.LCNF.PhaseExt import Lean.Compiler.LCNF.Main import Lean.Meta.ExprDefEq import Lean.Meta.LevelDefEq import Lean.Meta.Match.MatchEqs import Lean.Elab.PreDefinition.Structural.Eqns import Lean.Parser
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
lean_object* v_toEnvExtension_300_; lean_object* v_addImportedFn_301_; lean_object* v_asyncMode_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v_importedEntries_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_336_; 
v_toEnvExtension_300_ = lean_ctor_get(v_ext_297_, 0);
lean_inc_ref(v_toEnvExtension_300_);
v_addImportedFn_301_ = lean_ctor_get(v_ext_297_, 2);
lean_inc_ref(v_addImportedFn_301_);
lean_dec_ref(v_ext_297_);
v_asyncMode_302_ = lean_ctor_get(v_toEnvExtension_300_, 2);
v___x_303_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v_inst_296_);
lean_inc_ref(v_env_298_);
v___x_304_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_303_, v_toEnvExtension_300_, v_env_298_, v_asyncMode_302_, v___x_294_, v___x_295_);
lean_dec_ref(v___x_303_);
v_importedEntries_305_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_336_ == 0)
{
lean_object* v_unused_337_; 
v_unused_337_ = lean_ctor_get(v___x_304_, 1);
lean_dec(v_unused_337_);
v___x_307_ = v___x_304_;
v_isShared_308_ = v_isSharedCheck_336_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_importedEntries_305_);
lean_dec(v___x_304_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_336_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = l_Lean_Options_empty;
lean_inc_ref(v_env_298_);
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v_env_298_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
lean_inc_ref(v_importedEntries_305_);
v___x_311_ = lean_apply_3(v_addImportedFn_301_, v_importedEntries_305_, v___x_310_, lean_box(0));
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_327_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_327_ == 0)
{
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_327_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_327_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v_a_312_);
v___x_317_ = v___x_307_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_importedEntries_305_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_a_312_);
v___x_317_ = v_reuseFailAlloc_326_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
lean_object* v___f_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; lean_object* v___x_322_; lean_object* v___x_324_; 
v___f_318_ = lean_alloc_closure((void*)(l_main___elam__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_318_, 0, v___x_317_);
v___x_319_ = lean_box(0);
v___x_320_ = lean_box(0);
v___x_321_ = 1;
v___x_322_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_300_, v_env_298_, v___f_318_, v___x_319_, v___x_320_, v___x_321_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_322_);
v___x_324_ = v___x_314_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_322_);
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
else
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
lean_del_object(v___x_307_);
lean_dec_ref(v_importedEntries_305_);
lean_dec_ref(v_toEnvExtension_300_);
lean_dec_ref(v_env_298_);
v_a_328_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v___x_311_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_311_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg___boxed(lean_object* v___x_338_, lean_object* v___x_339_, lean_object* v_inst_340_, lean_object* v_ext_341_, lean_object* v_env_342_, lean_object* v___y_343_){
_start:
{
uint8_t v___x_36864__boxed_344_; lean_object* v_res_345_; 
v___x_36864__boxed_344_ = lean_unbox(v___x_339_);
v_res_345_ = l_main___elam__0___redArg(v___x_338_, v___x_36864__boxed_344_, v_inst_340_, v_ext_341_, v_env_342_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0(lean_object* v___x_346_, uint8_t v___x_347_, lean_object* v_00_u03b1_348_, lean_object* v_00_u03b2_349_, lean_object* v_00_u03c3_350_, lean_object* v_inst_351_, lean_object* v_ext_352_, lean_object* v_env_353_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_main___elam__0___redArg(v___x_346_, v___x_347_, v_inst_351_, v_ext_352_, v_env_353_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___boxed(lean_object* v___x_356_, lean_object* v___x_357_, lean_object* v_00_u03b1_358_, lean_object* v_00_u03b2_359_, lean_object* v_00_u03c3_360_, lean_object* v_inst_361_, lean_object* v_ext_362_, lean_object* v_env_363_, lean_object* v___y_364_){
_start:
{
uint8_t v___x_36944__boxed_365_; lean_object* v_res_366_; 
v___x_36944__boxed_365_ = lean_unbox(v___x_357_);
v_res_366_ = l_main___elam__0(v___x_356_, v___x_36944__boxed_365_, v_00_u03b1_358_, v_00_u03b2_359_, v_00_u03c3_360_, v_inst_361_, v_ext_362_, v_env_363_);
return v_res_366_;
}
}
static lean_object* _init_l_panic___at___00main_spec__5___closed__0(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = l_instInhabitedError;
v___x_368_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_368_, 0, lean_box(0));
lean_closure_set(v___x_368_, 1, lean_box(0));
lean_closure_set(v___x_368_, 2, v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5(lean_object* v_msg_369_){
_start:
{
lean_object* v___x_371_; lean_object* v___x_19992__overap_372_; lean_object* v___x_373_; 
v___x_371_ = lean_obj_once(&l_panic___at___00main_spec__5___closed__0, &l_panic___at___00main_spec__5___closed__0_once, _init_l_panic___at___00main_spec__5___closed__0);
v___x_19992__overap_372_ = lean_panic_fn_borrowed(v___x_371_, v_msg_369_);
v___x_373_ = lean_apply_1(v___x_19992__overap_372_, lean_box(0));
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5___boxed(lean_object* v_msg_374_, lean_object* v___y_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_panic___at___00main_spec__5(v_msg_374_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8(lean_object* v_opts_377_, lean_object* v_opt_378_){
_start:
{
lean_object* v_name_379_; lean_object* v_defValue_380_; lean_object* v_map_381_; lean_object* v___x_382_; 
v_name_379_ = lean_ctor_get(v_opt_378_, 0);
v_defValue_380_ = lean_ctor_get(v_opt_378_, 1);
v_map_381_ = lean_ctor_get(v_opts_377_, 0);
v___x_382_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_381_, v_name_379_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_inc(v_defValue_380_);
return v_defValue_380_;
}
else
{
lean_object* v_val_383_; 
v_val_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_val_383_);
lean_dec_ref_known(v___x_382_, 1);
if (lean_obj_tag(v_val_383_) == 3)
{
lean_object* v_v_384_; 
v_v_384_ = lean_ctor_get(v_val_383_, 0);
lean_inc(v_v_384_);
lean_dec_ref_known(v_val_383_, 1);
return v_v_384_;
}
else
{
lean_dec(v_val_383_);
lean_inc(v_defValue_380_);
return v_defValue_380_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8___boxed(lean_object* v_opts_385_, lean_object* v_opt_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Option_get___at___00main_spec__8(v_opts_385_, v_opt_386_);
lean_dec_ref(v_opt_386_);
lean_dec_ref(v_opts_385_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_main___lam__0(lean_object* v_package_x3f_388_, lean_object* v_ps_389_){
_start:
{
lean_object* v_importedEntries_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
v_importedEntries_390_ = lean_ctor_get(v_ps_389_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v_ps_389_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v_ps_389_, 1);
lean_dec(v_unused_398_);
v___x_392_ = v_ps_389_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_importedEntries_390_);
lean_dec(v_ps_389_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 1, v_package_x3f_388_);
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_importedEntries_390_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_package_x3f_388_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(lean_object* v_a_399_, lean_object* v_x_400_){
_start:
{
if (lean_obj_tag(v_x_400_) == 0)
{
lean_dec(v_a_399_);
return v_x_400_;
}
else
{
lean_object* v_key_401_; lean_object* v_value_402_; lean_object* v_tail_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_436_; 
v_key_401_ = lean_ctor_get(v_x_400_, 0);
v_value_402_ = lean_ctor_get(v_x_400_, 1);
v_tail_403_ = lean_ctor_get(v_x_400_, 2);
v_isSharedCheck_436_ = !lean_is_exclusive(v_x_400_);
if (v_isSharedCheck_436_ == 0)
{
v___x_405_ = v_x_400_;
v_isShared_406_ = v_isSharedCheck_436_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_tail_403_);
lean_inc(v_value_402_);
lean_inc(v_key_401_);
lean_dec(v_x_400_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_436_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
uint8_t v___x_407_; 
v___x_407_ = lean_name_eq(v_key_401_, v_a_399_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_408_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v_a_399_, v_tail_403_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 2, v___x_408_);
v___x_410_ = v___x_405_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_key_401_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_value_402_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v___x_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
else
{
lean_object* v_toEffectiveImport_412_; lean_object* v_parts_413_; lean_object* v_irParts_414_; uint8_t v_needsIRTrans_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_435_; 
lean_dec(v_key_401_);
v_toEffectiveImport_412_ = lean_ctor_get(v_value_402_, 0);
v_parts_413_ = lean_ctor_get(v_value_402_, 1);
v_irParts_414_ = lean_ctor_get(v_value_402_, 2);
v_needsIRTrans_415_ = lean_ctor_get_uint8(v_value_402_, sizeof(void*)*3);
v_isSharedCheck_435_ = !lean_is_exclusive(v_value_402_);
if (v_isSharedCheck_435_ == 0)
{
v___x_417_ = v_value_402_;
v_isShared_418_ = v_isSharedCheck_435_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_irParts_414_);
lean_inc(v_parts_413_);
lean_inc(v_toEffectiveImport_412_);
lean_dec(v_value_402_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_435_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v_toImport_419_; uint8_t v_hasData_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_434_; 
v_toImport_419_ = lean_ctor_get(v_toEffectiveImport_412_, 0);
v_hasData_420_ = lean_ctor_get_uint8(v_toEffectiveImport_412_, sizeof(void*)*1 + 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v_toEffectiveImport_412_);
if (v_isSharedCheck_434_ == 0)
{
v___x_422_ = v_toEffectiveImport_412_;
v_isShared_423_ = v_isSharedCheck_434_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_toImport_419_);
lean_dec(v_toEffectiveImport_412_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_434_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
uint8_t v___x_424_; lean_object* v___x_426_; 
v___x_424_ = 0;
if (v_isShared_423_ == 0)
{
v___x_426_ = v___x_422_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_toImport_419_);
lean_ctor_set_uint8(v_reuseFailAlloc_433_, sizeof(void*)*1 + 1, v_hasData_420_);
v___x_426_ = v_reuseFailAlloc_433_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_428_; 
lean_ctor_set_uint8(v___x_426_, sizeof(void*)*1, v___x_424_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_426_);
v___x_428_ = v___x_417_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_parts_413_);
lean_ctor_set(v_reuseFailAlloc_432_, 2, v_irParts_414_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, sizeof(void*)*3, v_needsIRTrans_415_);
v___x_428_ = v_reuseFailAlloc_432_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_430_; 
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 1, v___x_428_);
lean_ctor_set(v___x_405_, 0, v_a_399_);
v___x_430_ = v___x_405_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_399_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_431_, 2, v_tail_403_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(lean_object* v_m_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_size_439_; lean_object* v_buckets_440_; lean_object* v___x_441_; uint64_t v___y_443_; 
v_size_439_ = lean_ctor_get(v_m_437_, 0);
v_buckets_440_ = lean_ctor_get(v_m_437_, 1);
v___x_441_ = lean_array_get_size(v_buckets_440_);
if (lean_obj_tag(v_a_438_) == 0)
{
uint64_t v___x_470_; 
v___x_470_ = 1723ULL;
v___y_443_ = v___x_470_;
goto v___jp_442_;
}
else
{
uint64_t v_hash_471_; 
v_hash_471_ = lean_ctor_get_uint64(v_a_438_, sizeof(void*)*2);
v___y_443_ = v_hash_471_;
goto v___jp_442_;
}
v___jp_442_:
{
uint64_t v___x_444_; uint64_t v___x_445_; uint64_t v_fold_446_; uint64_t v___x_447_; uint64_t v___x_448_; uint64_t v___x_449_; size_t v___x_450_; size_t v___x_451_; size_t v___x_452_; size_t v___x_453_; size_t v___x_454_; lean_object* v_bucket_455_; uint8_t v___x_456_; 
v___x_444_ = 32ULL;
v___x_445_ = lean_uint64_shift_right(v___y_443_, v___x_444_);
v_fold_446_ = lean_uint64_xor(v___y_443_, v___x_445_);
v___x_447_ = 16ULL;
v___x_448_ = lean_uint64_shift_right(v_fold_446_, v___x_447_);
v___x_449_ = lean_uint64_xor(v_fold_446_, v___x_448_);
v___x_450_ = lean_uint64_to_usize(v___x_449_);
v___x_451_ = lean_usize_of_nat(v___x_441_);
v___x_452_ = ((size_t)1ULL);
v___x_453_ = lean_usize_sub(v___x_451_, v___x_452_);
v___x_454_ = lean_usize_land(v___x_450_, v___x_453_);
v_bucket_455_ = lean_array_uget_borrowed(v_buckets_440_, v___x_454_);
v___x_456_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_a_438_, v_bucket_455_);
if (v___x_456_ == 0)
{
lean_dec(v_a_438_);
return v_m_437_;
}
else
{
lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_467_; 
lean_inc(v_bucket_455_);
lean_inc_ref(v_buckets_440_);
lean_inc(v_size_439_);
v_isSharedCheck_467_ = !lean_is_exclusive(v_m_437_);
if (v_isSharedCheck_467_ == 0)
{
lean_object* v_unused_468_; lean_object* v_unused_469_; 
v_unused_468_ = lean_ctor_get(v_m_437_, 1);
lean_dec(v_unused_468_);
v_unused_469_ = lean_ctor_get(v_m_437_, 0);
lean_dec(v_unused_469_);
v___x_458_ = v_m_437_;
v_isShared_459_ = v_isSharedCheck_467_;
goto v_resetjp_457_;
}
else
{
lean_dec(v_m_437_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_467_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; lean_object* v_buckets_461_; lean_object* v_bucket_462_; lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_460_ = lean_box(0);
v_buckets_461_ = lean_array_uset(v_buckets_440_, v___x_454_, v___x_460_);
v_bucket_462_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v_a_438_, v_bucket_455_);
v___x_463_ = lean_array_uset(v_buckets_461_, v___x_454_, v_bucket_462_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 1, v___x_463_);
v___x_465_ = v___x_458_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_size_439_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v___x_463_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__1(lean_object* v___x_472_, lean_object* v___x_473_, uint8_t v___x_474_, lean_object* v_importArts_475_, uint8_t v___y_476_, uint8_t v___x_477_, lean_object* v_name_478_, lean_object* v___x_479_, uint8_t v___x_480_){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_st_mk_ref(v___x_472_);
v___x_483_ = l_Lean_importModulesCore(v___x_473_, v___x_474_, v_importArts_475_, v___y_476_, v___x_477_, v___x_482_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v___x_484_; lean_object* v_moduleNameMap_485_; lean_object* v_moduleNames_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_496_; 
lean_dec_ref_known(v___x_483_, 1);
v___x_484_ = lean_st_ref_get(v___x_482_);
lean_dec(v___x_482_);
v_moduleNameMap_485_ = lean_ctor_get(v___x_484_, 0);
v_moduleNames_486_ = lean_ctor_get(v___x_484_, 1);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_496_ == 0)
{
v___x_488_ = v___x_484_;
v_isShared_489_ = v_isSharedCheck_496_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_moduleNames_486_);
lean_inc(v_moduleNameMap_485_);
lean_dec(v___x_484_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_496_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_490_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(v_moduleNameMap_485_, v_name_478_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v___x_490_);
v___x_492_ = v___x_488_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_moduleNames_486_);
v___x_492_ = v_reuseFailAlloc_495_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
uint32_t v___x_493_; lean_object* v___x_494_; 
v___x_493_ = 0;
v___x_494_ = l_Lean_finalizeImport(v___x_492_, v___x_473_, v___x_479_, v___x_493_, v___x_477_, v___x_480_, v___x_474_, v___x_477_, v___x_477_);
lean_dec_ref(v___x_492_);
return v___x_494_;
}
}
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_dec(v___x_482_);
lean_dec_ref(v___x_479_);
lean_dec(v_name_478_);
lean_dec_ref(v___x_473_);
v_a_497_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_483_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_483_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__1___boxed(lean_object* v___x_505_, lean_object* v___x_506_, lean_object* v___x_507_, lean_object* v_importArts_508_, lean_object* v___y_509_, lean_object* v___x_510_, lean_object* v_name_511_, lean_object* v___x_512_, lean_object* v___x_513_, lean_object* v___y_514_){
_start:
{
uint8_t v___x_37112__boxed_515_; uint8_t v___y_37113__boxed_516_; uint8_t v___x_37114__boxed_517_; uint8_t v___x_37116__boxed_518_; lean_object* v_res_519_; 
v___x_37112__boxed_515_ = lean_unbox(v___x_507_);
v___y_37113__boxed_516_ = lean_unbox(v___y_509_);
v___x_37114__boxed_517_ = lean_unbox(v___x_510_);
v___x_37116__boxed_518_ = lean_unbox(v___x_513_);
v_res_519_ = l_main___lam__1(v___x_505_, v___x_506_, v___x_37112__boxed_515_, v_importArts_508_, v___y_37113__boxed_516_, v___x_37114__boxed_517_, v_name_511_, v___x_512_, v___x_37116__boxed_518_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_main___lam__2(lean_object* v___x_523_, lean_object* v___x_524_, uint16_t v___x_525_, lean_object* v_name_526_, lean_object* v_a_527_, uint8_t v___x_528_, lean_object* v___x_529_, lean_object* v_head_530_, lean_object* v___x_531_, lean_object* v___x_532_, lean_object* v___x_533_, lean_object* v___x_534_, lean_object* v___x_535_, lean_object* v___x_536_, lean_object* v___x_537_, lean_object* v___x_538_, uint8_t v___x_539_, uint8_t v___x_540_){
_start:
{
lean_object* v_a_543_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v_fileName_549_; lean_object* v_fileMap_550_; lean_object* v_currNamespace_551_; lean_object* v_openDecls_552_; lean_object* v_initHeartbeats_553_; lean_object* v_maxHeartbeats_554_; lean_object* v_quotContext_555_; lean_object* v_currMacroScope_556_; lean_object* v_cancelTk_x3f_557_; lean_object* v_inheritedTraceOptions_558_; lean_object* v_currRecDepth_559_; lean_object* v_ref_560_; uint8_t v_suppressElabErrors_561_; uint8_t v_isRecordingDeps_562_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___y_598_; uint8_t v___y_620_; uint8_t v___y_621_; lean_object* v_env_622_; uint8_t v___x_623_; uint8_t v___y_625_; uint16_t v___x_626_; uint16_t v___x_627_; uint16_t v___x_628_; uint8_t v___x_629_; 
v___x_546_ = lean_io_get_num_heartbeats();
v___x_547_ = lean_st_mk_ref(v___x_523_);
v___x_594_ = l_Lean_inheritedTraceOptions;
v___x_595_ = lean_st_ref_get(v___x_594_);
v___x_596_ = lean_st_ref_get(v___x_547_);
v_env_622_ = lean_ctor_get(v___x_596_, 0);
lean_inc_ref(v_env_622_);
lean_dec(v___x_596_);
v___x_623_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_622_);
lean_dec_ref(v_env_622_);
v___x_626_ = 512;
v___x_627_ = lean_uint16_land(v___x_525_, v___x_626_);
v___x_628_ = 0;
v___x_629_ = lean_uint16_dec_eq(v___x_627_, v___x_628_);
if (v___x_629_ == 0)
{
v___y_625_ = v___x_528_;
goto v___jp_624_;
}
else
{
v___y_625_ = v___x_540_;
goto v___jp_624_;
}
v___jp_542_:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = lean_mk_io_user_error(v_a_543_);
v___x_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
return v___x_545_;
}
v___jp_548_:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_563_ = l_Lean_maxRecDepth;
v___x_564_ = l_Lean_Option_get___at___00main_spec__8(v___x_524_, v___x_563_);
v___x_565_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_565_, 0, v_fileName_549_);
lean_ctor_set(v___x_565_, 1, v_fileMap_550_);
lean_ctor_set(v___x_565_, 2, v___x_524_);
lean_ctor_set(v___x_565_, 3, v___x_564_);
lean_ctor_set(v___x_565_, 4, v_currNamespace_551_);
lean_ctor_set(v___x_565_, 5, v_openDecls_552_);
lean_ctor_set(v___x_565_, 6, v_initHeartbeats_553_);
lean_ctor_set(v___x_565_, 7, v_maxHeartbeats_554_);
lean_ctor_set(v___x_565_, 8, v_quotContext_555_);
lean_ctor_set(v___x_565_, 9, v_currMacroScope_556_);
lean_ctor_set(v___x_565_, 10, v_cancelTk_x3f_557_);
lean_ctor_set(v___x_565_, 11, v_inheritedTraceOptions_558_);
v___x_566_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_566_, 0, v___x_565_);
lean_ctor_set(v___x_566_, 1, v_currRecDepth_559_);
lean_ctor_set(v___x_566_, 2, v_ref_560_);
lean_ctor_set_uint16(v___x_566_, sizeof(void*)*3, v___x_525_);
lean_ctor_set_uint8(v___x_566_, sizeof(void*)*3 + 2, v_suppressElabErrors_561_);
lean_ctor_set_uint8(v___x_566_, sizeof(void*)*3 + 3, v_isRecordingDeps_562_);
v___x_567_ = l_Lean_Compiler_LCNF_emitC(v_name_526_, v___x_566_, v___x_547_);
lean_dec_ref_known(v___x_566_, 3);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_a_568_);
lean_dec_ref_known(v___x_567_, 1);
v___x_569_ = lean_st_ref_get(v___x_547_);
lean_dec(v___x_547_);
lean_dec(v___x_569_);
v___x_570_ = lean_string_to_utf8(v_a_568_);
lean_dec(v_a_568_);
v___x_571_ = lean_io_prim_handle_write(v_a_527_, v___x_570_);
lean_dec_ref(v___x_570_);
return v___x_571_;
}
else
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_593_; 
lean_dec(v___x_547_);
v_a_572_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_593_ == 0)
{
v___x_574_ = v___x_567_;
v_isShared_575_ = v_isSharedCheck_593_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_567_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_593_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
if (lean_obj_tag(v_a_572_) == 0)
{
lean_object* v_msg_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
v_msg_576_ = lean_ctor_get(v_a_572_, 1);
lean_inc_ref(v_msg_576_);
lean_dec_ref_known(v_a_572_, 2);
v___x_577_ = l_Lean_MessageData_toString(v_msg_576_);
v___x_578_ = lean_mk_io_user_error(v___x_577_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_578_);
v___x_580_ = v___x_574_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
else
{
lean_object* v_id_582_; lean_object* v___x_583_; 
lean_del_object(v___x_574_);
v_id_582_ = lean_ctor_get(v_a_572_, 0);
lean_inc(v_id_582_);
lean_dec_ref_known(v_a_572_, 2);
v___x_583_ = l_Lean_InternalExceptionId_getName(v_id_582_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec(v_id_582_);
v_a_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_584_);
lean_dec_ref_known(v___x_583_, 1);
v___x_585_ = ((lean_object*)(l_main___lam__2___closed__0));
v___x_586_ = l_Lean_Name_toString(v_a_584_, v___x_528_);
v___x_587_ = lean_string_append(v___x_585_, v___x_586_);
lean_dec_ref(v___x_586_);
v_a_543_ = v___x_587_;
goto v___jp_542_;
}
else
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
lean_dec_ref_known(v___x_583_, 1);
v___x_588_ = ((lean_object*)(l_main___lam__2___closed__1));
v___x_589_ = l_Nat_reprFast(v_id_582_);
v___x_590_ = lean_string_append(v___x_588_, v___x_589_);
lean_dec_ref(v___x_589_);
v___x_591_ = ((lean_object*)(l_main___lam__2___closed__2));
v___x_592_ = lean_string_append(v___x_590_, v___x_591_);
v_a_543_ = v___x_592_;
goto v___jp_542_;
}
}
}
}
}
v___jp_597_:
{
lean_object* v___x_599_; lean_object* v_env_600_; lean_object* v_nextMacroScope_601_; lean_object* v_ngen_602_; lean_object* v_auxDeclNGen_603_; lean_object* v_traceState_604_; lean_object* v_recordedDeps_605_; lean_object* v_messages_606_; lean_object* v_infoState_607_; lean_object* v_snapshotTasks_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_617_; 
v___x_599_ = lean_st_ref_take(v___x_547_);
v_env_600_ = lean_ctor_get(v___x_599_, 0);
v_nextMacroScope_601_ = lean_ctor_get(v___x_599_, 1);
v_ngen_602_ = lean_ctor_get(v___x_599_, 2);
v_auxDeclNGen_603_ = lean_ctor_get(v___x_599_, 3);
v_traceState_604_ = lean_ctor_get(v___x_599_, 4);
v_recordedDeps_605_ = lean_ctor_get(v___x_599_, 6);
v_messages_606_ = lean_ctor_get(v___x_599_, 7);
v_infoState_607_ = lean_ctor_get(v___x_599_, 8);
v_snapshotTasks_608_ = lean_ctor_get(v___x_599_, 9);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; 
v_unused_618_ = lean_ctor_get(v___x_599_, 5);
lean_dec(v_unused_618_);
v___x_610_ = v___x_599_;
v_isShared_611_ = v_isSharedCheck_617_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_snapshotTasks_608_);
lean_inc(v_infoState_607_);
lean_inc(v_messages_606_);
lean_inc(v_recordedDeps_605_);
lean_inc(v_traceState_604_);
lean_inc(v_auxDeclNGen_603_);
lean_inc(v_ngen_602_);
lean_inc(v_nextMacroScope_601_);
lean_inc(v_env_600_);
lean_dec(v___x_599_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_617_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_612_ = l_Lean_Kernel_enableDiag(v_env_600_, v___y_598_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 5, v___x_529_);
lean_ctor_set(v___x_610_, 0, v___x_612_);
v___x_614_ = v___x_610_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_nextMacroScope_601_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v_ngen_602_);
lean_ctor_set(v_reuseFailAlloc_616_, 3, v_auxDeclNGen_603_);
lean_ctor_set(v_reuseFailAlloc_616_, 4, v_traceState_604_);
lean_ctor_set(v_reuseFailAlloc_616_, 5, v___x_529_);
lean_ctor_set(v_reuseFailAlloc_616_, 6, v_recordedDeps_605_);
lean_ctor_set(v_reuseFailAlloc_616_, 7, v_messages_606_);
lean_ctor_set(v_reuseFailAlloc_616_, 8, v_infoState_607_);
lean_ctor_set(v_reuseFailAlloc_616_, 9, v_snapshotTasks_608_);
v___x_614_ = v_reuseFailAlloc_616_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_615_; 
v___x_615_ = lean_st_ref_put(v___x_547_, v___x_614_);
lean_inc(v___x_532_);
v_fileName_549_ = v_head_530_;
v_fileMap_550_ = v___x_531_;
v_currNamespace_551_ = v___x_532_;
v_openDecls_552_ = v___x_533_;
v_initHeartbeats_553_ = v___x_546_;
v_maxHeartbeats_554_ = v___x_534_;
v_quotContext_555_ = v___x_532_;
v_currMacroScope_556_ = v___x_535_;
v_cancelTk_x3f_557_ = v___x_536_;
v_inheritedTraceOptions_558_ = v___x_595_;
v_currRecDepth_559_ = v___x_537_;
v_ref_560_ = v___x_538_;
v_suppressElabErrors_561_ = v___x_539_;
v_isRecordingDeps_562_ = v___x_539_;
goto v___jp_548_;
}
}
}
v___jp_619_:
{
if (v___y_621_ == 0)
{
v___y_598_ = v___y_620_;
goto v___jp_597_;
}
else
{
lean_dec_ref(v___x_529_);
lean_inc(v___x_532_);
v_fileName_549_ = v_head_530_;
v_fileMap_550_ = v___x_531_;
v_currNamespace_551_ = v___x_532_;
v_openDecls_552_ = v___x_533_;
v_initHeartbeats_553_ = v___x_546_;
v_maxHeartbeats_554_ = v___x_534_;
v_quotContext_555_ = v___x_532_;
v_currMacroScope_556_ = v___x_535_;
v_cancelTk_x3f_557_ = v___x_536_;
v_inheritedTraceOptions_558_ = v___x_595_;
v_currRecDepth_559_ = v___x_537_;
v_ref_560_ = v___x_538_;
v_suppressElabErrors_561_ = v___x_539_;
v_isRecordingDeps_562_ = v___x_539_;
goto v___jp_548_;
}
}
v___jp_624_:
{
if (v___y_625_ == 0)
{
if (v___x_623_ == 0)
{
v___y_620_ = v___y_625_;
v___y_621_ = v___x_528_;
goto v___jp_619_;
}
else
{
v___y_598_ = v___y_625_;
goto v___jp_597_;
}
}
else
{
v___y_620_ = v___y_625_;
v___y_621_ = v___x_623_;
goto v___jp_619_;
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__2___boxed(lean_object** _args){
lean_object* v___x_630_ = _args[0];
lean_object* v___x_631_ = _args[1];
lean_object* v___x_632_ = _args[2];
lean_object* v_name_633_ = _args[3];
lean_object* v_a_634_ = _args[4];
lean_object* v___x_635_ = _args[5];
lean_object* v___x_636_ = _args[6];
lean_object* v_head_637_ = _args[7];
lean_object* v___x_638_ = _args[8];
lean_object* v___x_639_ = _args[9];
lean_object* v___x_640_ = _args[10];
lean_object* v___x_641_ = _args[11];
lean_object* v___x_642_ = _args[12];
lean_object* v___x_643_ = _args[13];
lean_object* v___x_644_ = _args[14];
lean_object* v___x_645_ = _args[15];
lean_object* v___x_646_ = _args[16];
lean_object* v___x_647_ = _args[17];
lean_object* v___y_648_ = _args[18];
_start:
{
uint16_t v___x_37185__boxed_649_; uint8_t v___x_37187__boxed_650_; uint8_t v___x_37198__boxed_651_; uint8_t v___x_37199__boxed_652_; lean_object* v_res_653_; 
v___x_37185__boxed_649_ = lean_unbox(v___x_632_);
v___x_37187__boxed_650_ = lean_unbox(v___x_635_);
v___x_37198__boxed_651_ = lean_unbox(v___x_646_);
v___x_37199__boxed_652_ = lean_unbox(v___x_647_);
v_res_653_ = l_main___lam__2(v___x_630_, v___x_631_, v___x_37185__boxed_649_, v_name_633_, v_a_634_, v___x_37187__boxed_650_, v___x_636_, v_head_637_, v___x_638_, v___x_639_, v___x_640_, v___x_641_, v___x_642_, v___x_643_, v___x_644_, v___x_645_, v___x_37198__boxed_651_, v___x_37199__boxed_652_);
lean_dec(v_a_634_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_main___lam__3(lean_object* v___x_654_, lean_object* v_x_655_){
_start:
{
lean_inc_ref(v___x_654_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_main___lam__3___boxed(lean_object* v___x_656_, lean_object* v_x_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_main___lam__3(v___x_656_, v_x_657_);
lean_dec_ref(v_x_657_);
lean_dec_ref(v___x_656_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(lean_object* v_x2_659_, lean_object* v_as_660_, size_t v_i_661_, size_t v_stop_662_, lean_object* v_b_663_){
_start:
{
uint8_t v___x_664_; 
v___x_664_ = lean_usize_dec_eq(v_i_661_, v_stop_662_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; lean_object* v___x_666_; size_t v___x_667_; size_t v___x_668_; 
v___x_665_ = lean_array_uget_borrowed(v_as_660_, v_i_661_);
lean_inc_ref(v_x2_659_);
lean_inc(v___x_665_);
v___x_666_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_665_, v_x2_659_, v_b_663_);
v___x_667_ = ((size_t)1ULL);
v___x_668_ = lean_usize_add(v_i_661_, v___x_667_);
v_i_661_ = v___x_668_;
v_b_663_ = v___x_666_;
goto _start;
}
else
{
lean_dec_ref(v_x2_659_);
return v_b_663_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(lean_object* v_x2_670_, lean_object* v_as_671_, lean_object* v_i_672_, lean_object* v_stop_673_, lean_object* v_b_674_){
_start:
{
size_t v_i_boxed_675_; size_t v_stop_boxed_676_; lean_object* v_res_677_; 
v_i_boxed_675_ = lean_unbox_usize(v_i_672_);
lean_dec(v_i_672_);
v_stop_boxed_676_ = lean_unbox_usize(v_stop_673_);
lean_dec(v_stop_673_);
v_res_677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v_x2_670_, v_as_671_, v_i_boxed_675_, v_stop_boxed_676_, v_b_674_);
lean_dec_ref(v_as_671_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(lean_object* v_as_678_, size_t v_i_679_, size_t v_stop_680_, lean_object* v_b_681_){
_start:
{
lean_object* v___y_683_; uint8_t v___x_687_; 
v___x_687_ = lean_usize_dec_eq(v_i_679_, v_stop_680_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v_declNames_689_; lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_688_ = lean_array_uget_borrowed(v_as_678_, v_i_679_);
v_declNames_689_ = lean_ctor_get(v___x_688_, 0);
v___x_690_ = lean_unsigned_to_nat(0u);
v___x_691_ = lean_array_get_size(v_declNames_689_);
v___x_692_ = lean_nat_dec_lt(v___x_690_, v___x_691_);
if (v___x_692_ == 0)
{
v___y_683_ = v_b_681_;
goto v___jp_682_;
}
else
{
uint8_t v___x_693_; 
v___x_693_ = lean_nat_dec_le(v___x_691_, v___x_691_);
if (v___x_693_ == 0)
{
if (v___x_692_ == 0)
{
v___y_683_ = v_b_681_;
goto v___jp_682_;
}
else
{
size_t v___x_694_; size_t v___x_695_; lean_object* v___x_696_; 
v___x_694_ = ((size_t)0ULL);
v___x_695_ = lean_usize_of_nat(v___x_691_);
lean_inc(v___x_688_);
v___x_696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_688_, v_declNames_689_, v___x_694_, v___x_695_, v_b_681_);
v___y_683_ = v___x_696_;
goto v___jp_682_;
}
}
else
{
size_t v___x_697_; size_t v___x_698_; lean_object* v___x_699_; 
v___x_697_ = ((size_t)0ULL);
v___x_698_ = lean_usize_of_nat(v___x_691_);
lean_inc(v___x_688_);
v___x_699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_688_, v_declNames_689_, v___x_697_, v___x_698_, v_b_681_);
v___y_683_ = v___x_699_;
goto v___jp_682_;
}
}
}
else
{
return v_b_681_;
}
v___jp_682_:
{
size_t v___x_684_; size_t v___x_685_; 
v___x_684_ = ((size_t)1ULL);
v___x_685_ = lean_usize_add(v_i_679_, v___x_684_);
v_i_679_ = v___x_685_;
v_b_681_ = v___y_683_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14___boxed(lean_object* v_as_700_, lean_object* v_i_701_, lean_object* v_stop_702_, lean_object* v_b_703_){
_start:
{
size_t v_i_boxed_704_; size_t v_stop_boxed_705_; lean_object* v_res_706_; 
v_i_boxed_704_ = lean_unbox_usize(v_i_701_);
lean_dec(v_i_701_);
v_stop_boxed_705_ = lean_unbox_usize(v_stop_702_);
lean_dec(v_stop_702_);
v_res_706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v_as_700_, v_i_boxed_704_, v_stop_boxed_705_, v_b_703_);
lean_dec_ref(v_as_700_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(lean_object* v_s_707_){
_start:
{
lean_object* v___x_709_; lean_object* v_putStr_710_; lean_object* v___x_711_; 
v___x_709_ = lean_get_stderr();
v_putStr_710_ = lean_ctor_get(v___x_709_, 4);
lean_inc_ref(v_putStr_710_);
lean_dec_ref(v___x_709_);
v___x_711_ = lean_apply_2(v_putStr_710_, v_s_707_, lean_box(0));
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8___boxed(lean_object* v_s_712_, lean_object* v_a_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v_s_712_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6(lean_object* v_s_715_){
_start:
{
uint32_t v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_717_ = 10;
v___x_718_ = lean_string_push(v_s_715_, v___x_717_);
v___x_719_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v___x_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6___boxed(lean_object* v_s_720_, lean_object* v_a_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_IO_eprintln___at___00main_spec__6(v_s_720_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(lean_object* v_o_726_, lean_object* v_k_727_, lean_object* v_v_728_){
_start:
{
lean_object* v_map_729_; uint8_t v_hasTrace_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_744_; 
v_map_729_ = lean_ctor_get(v_o_726_, 0);
v_hasTrace_730_ = lean_ctor_get_uint8(v_o_726_, sizeof(void*)*1);
v_isSharedCheck_744_ = !lean_is_exclusive(v_o_726_);
if (v_isSharedCheck_744_ == 0)
{
v___x_732_ = v_o_726_;
v_isShared_733_ = v_isSharedCheck_744_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_map_729_);
lean_dec(v_o_726_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_744_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_734_, 0, v_v_728_);
lean_inc(v_k_727_);
v___x_735_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_727_, v___x_734_, v_map_729_);
if (v_hasTrace_730_ == 0)
{
lean_object* v___x_736_; uint8_t v___x_737_; lean_object* v___x_739_; 
v___x_736_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_737_ = l_Lean_Name_isPrefixOf(v___x_736_, v_k_727_);
lean_dec(v_k_727_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 0, v___x_735_);
v___x_739_ = v___x_732_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_735_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
lean_ctor_set_uint8(v___x_739_, sizeof(void*)*1, v___x_737_);
return v___x_739_;
}
}
else
{
lean_object* v___x_742_; 
lean_dec(v_k_727_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 0, v___x_735_);
v___x_742_ = v___x_732_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_735_);
lean_ctor_set_uint8(v_reuseFailAlloc_743_, sizeof(void*)*1, v_hasTrace_730_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00main_spec__3(lean_object* v_opts_745_, lean_object* v_opt_746_, lean_object* v_val_747_){
_start:
{
lean_object* v_name_748_; lean_object* v___x_749_; 
v_name_748_ = lean_ctor_get(v_opt_746_, 0);
lean_inc(v_name_748_);
lean_dec_ref(v_opt_746_);
v___x_749_ = l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(v_opts_745_, v_name_748_, v_val_747_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object* v_as_750_, size_t v_i_751_, size_t v_stop_752_, lean_object* v_b_753_){
_start:
{
uint8_t v___x_754_; 
v___x_754_ = lean_usize_dec_eq(v_i_751_, v_stop_752_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; lean_object* v_name_756_; lean_object* v___x_757_; size_t v___x_758_; size_t v___x_759_; 
v___x_755_ = lean_array_uget_borrowed(v_as_750_, v_i_751_);
v_name_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_name_756_);
v___x_757_ = l_Lean_Compiler_LCNF_setDeclPublic(v_b_753_, v_name_756_);
v___x_758_ = ((size_t)1ULL);
v___x_759_ = lean_usize_add(v_i_751_, v___x_758_);
v_i_751_ = v___x_759_;
v_b_753_ = v___x_757_;
goto _start;
}
else
{
return v_b_753_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object* v_as_761_, lean_object* v_i_762_, lean_object* v_stop_763_, lean_object* v_b_764_){
_start:
{
size_t v_i_boxed_765_; size_t v_stop_boxed_766_; lean_object* v_res_767_; 
v_i_boxed_765_ = lean_unbox_usize(v_i_762_);
lean_dec(v_i_762_);
v_stop_boxed_766_ = lean_unbox_usize(v_stop_763_);
lean_dec(v_stop_763_);
v_res_767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v_as_761_, v_i_boxed_765_, v_stop_boxed_766_, v_b_764_);
lean_dec_ref(v_as_761_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg(lean_object* v_as_x27_769_, lean_object* v_b_770_){
_start:
{
if (lean_obj_tag(v_as_x27_769_) == 0)
{
lean_object* v___x_772_; 
v___x_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_772_, 0, v_b_770_);
return v___x_772_;
}
else
{
lean_object* v_head_773_; lean_object* v_tail_774_; lean_object* v_fst_775_; lean_object* v_snd_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_801_; 
v_head_773_ = lean_ctor_get(v_as_x27_769_, 0);
v_tail_774_ = lean_ctor_get(v_as_x27_769_, 1);
v_fst_775_ = lean_ctor_get(v_b_770_, 0);
v_snd_776_ = lean_ctor_get(v_b_770_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v_b_770_);
if (v_isSharedCheck_801_ == 0)
{
v___x_778_ = v_b_770_;
v_isShared_779_ = v_isSharedCheck_801_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_snd_776_);
lean_inc(v_fst_775_);
lean_dec(v_b_770_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_801_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; uint8_t v___x_781_; 
v___x_780_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0));
v___x_781_ = lean_string_dec_eq(v_head_773_, v___x_780_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; 
lean_inc(v_head_773_);
v___x_782_ = l___private_LeanIR_0__setConfigOption(v_snd_776_, v_head_773_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; lean_object* v___x_785_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_783_);
lean_dec_ref_known(v___x_782_, 1);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 1, v_a_783_);
v___x_785_ = v___x_778_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_fst_775_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_a_783_);
v___x_785_ = v_reuseFailAlloc_787_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
v_as_x27_769_ = v_tail_774_;
v_b_770_ = v___x_785_;
goto _start;
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_del_object(v___x_778_);
lean_dec(v_fst_775_);
v_a_788_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_782_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_782_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
else
{
lean_object* v___x_796_; lean_object* v___x_798_; 
lean_dec(v_fst_775_);
v___x_796_ = lean_box(v___x_781_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_796_);
v___x_798_ = v___x_778_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_snd_776_);
v___x_798_ = v_reuseFailAlloc_800_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
v_as_x27_769_ = v_tail_774_;
v_b_770_ = v___x_798_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(lean_object* v_as_x27_802_, lean_object* v_b_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_802_, v_b_803_);
lean_dec(v_as_x27_802_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object* v_a_806_, lean_object* v_as_807_, size_t v_i_808_, size_t v_stop_809_, lean_object* v_b_810_){
_start:
{
lean_object* v___y_812_; uint8_t v___x_816_; 
v___x_816_ = lean_usize_dec_eq(v_i_808_, v_stop_809_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; lean_object* v_name_818_; uint8_t v___x_819_; 
v___x_817_ = lean_array_uget_borrowed(v_as_807_, v_i_808_);
v_name_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_name_818_);
lean_inc_ref(v_a_806_);
v___x_819_ = l_Lean_isExtern(v_a_806_, v_name_818_);
if (v___x_819_ == 0)
{
v___y_812_ = v_b_810_;
goto v___jp_811_;
}
else
{
lean_object* v___x_820_; 
lean_inc(v___x_817_);
v___x_820_ = lean_array_push(v_b_810_, v___x_817_);
v___y_812_ = v___x_820_;
goto v___jp_811_;
}
}
else
{
lean_dec_ref(v_a_806_);
return v_b_810_;
}
v___jp_811_:
{
size_t v___x_813_; size_t v___x_814_; 
v___x_813_ = ((size_t)1ULL);
v___x_814_ = lean_usize_add(v_i_808_, v___x_813_);
v_i_808_ = v___x_814_;
v_b_810_ = v___y_812_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object* v_a_821_, lean_object* v_as_822_, lean_object* v_i_823_, lean_object* v_stop_824_, lean_object* v_b_825_){
_start:
{
size_t v_i_boxed_826_; size_t v_stop_boxed_827_; lean_object* v_res_828_; 
v_i_boxed_826_ = lean_unbox_usize(v_i_823_);
lean_dec(v_i_823_);
v_stop_boxed_827_ = lean_unbox_usize(v_stop_824_);
lean_dec(v_stop_824_);
v_res_828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_821_, v_as_822_, v_i_boxed_826_, v_stop_boxed_827_, v_b_825_);
lean_dec_ref(v_as_822_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___lam__0(lean_object* v___x_829_, lean_object* v___x_830_, lean_object* v_s_831_){
_start:
{
lean_object* v_addEntryFn_832_; lean_object* v_importedEntries_833_; lean_object* v_state_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_842_; 
v_addEntryFn_832_ = lean_ctor_get(v___x_829_, 3);
lean_inc(v_addEntryFn_832_);
lean_dec_ref(v___x_829_);
v_importedEntries_833_ = lean_ctor_get(v_s_831_, 0);
v_state_834_ = lean_ctor_get(v_s_831_, 1);
v_isSharedCheck_842_ = !lean_is_exclusive(v_s_831_);
if (v_isSharedCheck_842_ == 0)
{
v___x_836_ = v_s_831_;
v_isShared_837_ = v_isSharedCheck_842_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_state_834_);
lean_inc(v_importedEntries_833_);
lean_dec(v_s_831_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_842_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v_state_838_; lean_object* v___x_840_; 
v_state_838_ = lean_apply_2(v_addEntryFn_832_, v_state_834_, v___x_830_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v_state_838_);
v___x_840_ = v___x_836_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_importedEntries_833_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_state_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object* v_as_843_, size_t v_i_844_, size_t v_stop_845_, lean_object* v_b_846_){
_start:
{
lean_object* v___y_848_; uint8_t v___x_852_; 
v___x_852_ = lean_usize_dec_eq(v_i_844_, v_stop_845_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; lean_object* v_toEnvExtension_854_; lean_object* v_asyncMode_855_; uint8_t v_logWrites_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___f_859_; uint8_t v___x_860_; 
v___x_853_ = l_Lean_Compiler_LCNF_impureSigExt;
v_toEnvExtension_854_ = lean_ctor_get(v___x_853_, 0);
v_asyncMode_855_ = lean_ctor_get(v_toEnvExtension_854_, 2);
v_logWrites_856_ = lean_ctor_get_uint8(v_toEnvExtension_854_, sizeof(void*)*6);
v___x_857_ = lean_box(0);
v___x_858_ = lean_array_uget_borrowed(v_as_843_, v_i_844_);
lean_inc(v___x_858_);
v___f_859_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___lam__0), 3, 2);
lean_closure_set(v___f_859_, 0, v___x_853_);
lean_closure_set(v___f_859_, 1, v___x_858_);
v___x_860_ = 1;
if (v_logWrites_856_ == 0)
{
lean_object* v___x_861_; 
lean_inc_ref(v_toEnvExtension_854_);
v___x_861_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_854_, v_b_846_, v___f_859_, v_asyncMode_855_, v___x_857_, v___x_860_);
v___y_848_ = v___x_861_;
goto v___jp_847_;
}
else
{
lean_object* v___x_862_; lean_object* v___x_863_; 
lean_inc_ref_n(v_toEnvExtension_854_, 2);
v___x_862_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite___redArg(v_toEnvExtension_854_, v_b_846_);
lean_dec_ref(v_b_846_);
v___x_863_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_854_, v___x_862_, v___f_859_, v_asyncMode_855_, v___x_857_, v___x_860_);
v___y_848_ = v___x_863_;
goto v___jp_847_;
}
}
else
{
return v_b_846_;
}
v___jp_847_:
{
size_t v___x_849_; size_t v___x_850_; 
v___x_849_ = ((size_t)1ULL);
v___x_850_ = lean_usize_add(v_i_844_, v___x_849_);
v_i_844_ = v___x_850_;
v_b_846_ = v___y_848_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object* v_as_864_, lean_object* v_i_865_, lean_object* v_stop_866_, lean_object* v_b_867_){
_start:
{
size_t v_i_boxed_868_; size_t v_stop_boxed_869_; lean_object* v_res_870_; 
v_i_boxed_868_ = lean_unbox_usize(v_i_865_);
lean_dec(v_i_865_);
v_stop_boxed_869_ = lean_unbox_usize(v_stop_866_);
lean_dec(v_stop_866_);
v_res_870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v_as_864_, v_i_boxed_868_, v_stop_boxed_869_, v_b_867_);
lean_dec_ref(v_as_864_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object* v___y_872_, lean_object* v_as_873_, size_t v_i_874_, size_t v_stop_875_, lean_object* v_b_876_){
_start:
{
lean_object* v___y_878_; uint8_t v___x_882_; 
v___x_882_ = lean_usize_dec_eq(v_i_874_, v_stop_875_);
if (v___x_882_ == 0)
{
lean_object* v_fst_883_; lean_object* v_snd_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___y_888_; 
v_fst_883_ = lean_ctor_get(v_b_876_, 0);
v_snd_884_ = lean_ctor_get(v_b_876_, 1);
v___x_885_ = lean_array_uget_borrowed(v_as_873_, v_i_874_);
v___x_886_ = l_Lean_IR_Decl_name(v___x_885_);
if (lean_obj_tag(v___x_886_) == 1)
{
lean_object* v_pre_901_; lean_object* v_str_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v_pre_901_ = lean_ctor_get(v___x_886_, 0);
v_str_902_ = lean_ctor_get(v___x_886_, 1);
v___x_903_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___closed__0));
v___x_904_ = lean_string_dec_eq(v_str_902_, v___x_903_);
if (v___x_904_ == 0)
{
lean_inc_ref(v___x_886_);
v___y_888_ = v___x_886_;
goto v___jp_887_;
}
else
{
lean_inc(v_pre_901_);
v___y_888_ = v_pre_901_;
goto v___jp_887_;
}
}
else
{
lean_inc(v___x_886_);
v___y_888_ = v___x_886_;
goto v___jp_887_;
}
v___jp_887_:
{
uint8_t v___x_889_; 
lean_inc_ref(v___y_872_);
v___x_889_ = l_Lean_isExtern(v___y_872_, v___y_888_);
if (v___x_889_ == 0)
{
lean_dec(v___x_886_);
v___y_878_ = v_b_876_;
goto v___jp_877_;
}
else
{
lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_898_; 
lean_inc(v_snd_884_);
lean_inc(v_fst_883_);
v_isSharedCheck_898_ = !lean_is_exclusive(v_b_876_);
if (v_isSharedCheck_898_ == 0)
{
lean_object* v_unused_899_; lean_object* v_unused_900_; 
v_unused_899_ = lean_ctor_get(v_b_876_, 1);
lean_dec(v_unused_899_);
v_unused_900_ = lean_ctor_get(v_b_876_, 0);
lean_dec(v_unused_900_);
v___x_891_ = v_b_876_;
v_isShared_892_ = v_isSharedCheck_898_;
goto v_resetjp_890_;
}
else
{
lean_dec(v_b_876_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_898_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_896_; 
lean_inc_n(v___x_885_, 2);
v___x_893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_885_);
lean_ctor_set(v___x_893_, 1, v_fst_883_);
v___x_894_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_884_, v___x_886_, v___x_885_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 1, v___x_894_);
lean_ctor_set(v___x_891_, 0, v___x_893_);
v___x_896_ = v___x_891_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
v___y_878_ = v___x_896_;
goto v___jp_877_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_872_);
return v_b_876_;
}
v___jp_877_:
{
size_t v___x_879_; size_t v___x_880_; 
v___x_879_ = ((size_t)1ULL);
v___x_880_ = lean_usize_add(v_i_874_, v___x_879_);
v_i_874_ = v___x_880_;
v_b_876_ = v___y_878_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object* v___y_905_, lean_object* v_as_906_, lean_object* v_i_907_, lean_object* v_stop_908_, lean_object* v_b_909_){
_start:
{
size_t v_i_boxed_910_; size_t v_stop_boxed_911_; lean_object* v_res_912_; 
v_i_boxed_910_ = lean_unbox_usize(v_i_907_);
lean_dec(v_i_907_);
v_stop_boxed_911_ = lean_unbox_usize(v_stop_908_);
lean_dec(v_stop_908_);
v_res_912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_905_, v_as_906_, v_i_boxed_910_, v_stop_boxed_911_, v_b_909_);
lean_dec_ref(v_as_906_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27(lean_object* v_as_916_, size_t v_sz_917_, size_t v_i_918_, lean_object* v_b_919_){
_start:
{
uint8_t v___x_921_; 
v___x_921_ = lean_usize_dec_lt(v_i_918_, v_sz_917_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; 
v___x_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_922_, 0, v_b_919_);
return v___x_922_;
}
else
{
uint8_t v___x_923_; lean_object* v_a_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
lean_dec_ref(v_b_919_);
v___x_923_ = 0;
v_a_924_ = lean_array_uget_borrowed(v_as_916_, v_i_918_);
lean_inc(v_a_924_);
v___x_925_ = l_Lean_Message_toString(v_a_924_, v___x_923_);
v___x_926_ = l_IO_eprintln___at___00main_spec__6(v___x_925_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v___x_927_; size_t v___x_928_; size_t v___x_929_; 
lean_dec_ref_known(v___x_926_, 1);
v___x_927_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_928_ = ((size_t)1ULL);
v___x_929_ = lean_usize_add(v_i_918_, v___x_928_);
v_i_918_ = v___x_929_;
v_b_919_ = v___x_927_;
goto _start;
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
v_a_931_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_926_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_926_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___boxed(lean_object* v_as_939_, lean_object* v_sz_940_, lean_object* v_i_941_, lean_object* v_b_942_, lean_object* v___y_943_){
_start:
{
size_t v_sz_boxed_944_; size_t v_i_boxed_945_; lean_object* v_res_946_; 
v_sz_boxed_944_ = lean_unbox_usize(v_sz_940_);
lean_dec(v_sz_940_);
v_i_boxed_945_ = lean_unbox_usize(v_i_941_);
lean_dec(v_i_941_);
v_res_946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27(v_as_939_, v_sz_boxed_944_, v_i_boxed_945_, v_b_942_);
lean_dec_ref(v_as_939_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(lean_object* v_as_947_, size_t v_sz_948_, size_t v_i_949_, lean_object* v_b_950_){
_start:
{
uint8_t v___x_952_; 
v___x_952_ = lean_usize_dec_lt(v_i_949_, v_sz_948_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; 
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v_b_950_);
return v___x_953_;
}
else
{
uint8_t v___x_954_; lean_object* v_a_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
lean_dec_ref(v_b_950_);
v___x_954_ = 0;
v_a_955_ = lean_array_uget_borrowed(v_as_947_, v_i_949_);
lean_inc(v_a_955_);
v___x_956_ = l_Lean_Message_toString(v_a_955_, v___x_954_);
v___x_957_ = l_IO_eprintln___at___00main_spec__6(v___x_956_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v___x_958_; size_t v___x_959_; size_t v___x_960_; lean_object* v___x_961_; 
lean_dec_ref_known(v___x_957_, 1);
v___x_958_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_959_ = ((size_t)1ULL);
v___x_960_ = lean_usize_add(v_i_949_, v___x_959_);
v___x_961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27(v_as_947_, v_sz_948_, v___x_960_, v___x_958_);
return v___x_961_;
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
v_a_962_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_957_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_957_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13___boxed(lean_object* v_as_970_, lean_object* v_sz_971_, lean_object* v_i_972_, lean_object* v_b_973_, lean_object* v___y_974_){
_start:
{
size_t v_sz_boxed_975_; size_t v_i_boxed_976_; lean_object* v_res_977_; 
v_sz_boxed_975_ = lean_unbox_usize(v_sz_971_);
lean_dec(v_sz_971_);
v_i_boxed_976_ = lean_unbox_usize(v_i_972_);
lean_dec(v_i_972_);
v_res_977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_as_970_, v_sz_boxed_975_, v_i_boxed_976_, v_b_973_);
lean_dec_ref(v_as_970_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(lean_object* v_init_978_, lean_object* v_n_979_, lean_object* v_b_980_){
_start:
{
if (lean_obj_tag(v_n_979_) == 0)
{
lean_object* v_cs_982_; lean_object* v___x_983_; lean_object* v___x_984_; size_t v_sz_985_; size_t v___x_986_; lean_object* v___x_987_; 
v_cs_982_ = lean_ctor_get(v_n_979_, 0);
v___x_983_ = lean_box(0);
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set(v___x_984_, 1, v_b_980_);
v_sz_985_ = lean_array_size(v_cs_982_);
v___x_986_ = ((size_t)0ULL);
v___x_987_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12(v_init_978_, v_cs_982_, v_sz_985_, v___x_986_, v___x_984_);
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
else
{
lean_object* v_vs_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; size_t v_sz_1014_; size_t v___x_1015_; lean_object* v___x_1016_; 
v_vs_1011_ = lean_ctor_get(v_n_979_, 0);
v___x_1012_ = lean_box(0);
v___x_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
lean_ctor_set(v___x_1013_, 1, v_b_980_);
v_sz_1014_ = lean_array_size(v_vs_1011_);
v___x_1015_ = ((size_t)0ULL);
v___x_1016_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_vs_1011_, v_sz_1014_, v___x_1015_, v___x_1013_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1031_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1019_ = v___x_1016_;
v_isShared_1020_ = v_isSharedCheck_1031_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1016_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1031_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v_fst_1021_; 
v_fst_1021_ = lean_ctor_get(v_a_1017_, 0);
if (lean_obj_tag(v_fst_1021_) == 0)
{
lean_object* v_snd_1022_; lean_object* v___x_1023_; lean_object* v___x_1025_; 
v_snd_1022_ = lean_ctor_get(v_a_1017_, 1);
lean_inc(v_snd_1022_);
lean_dec(v_a_1017_);
v___x_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1023_, 0, v_snd_1022_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 0, v___x_1023_);
v___x_1025_ = v___x_1019_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1023_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
else
{
lean_object* v_val_1027_; lean_object* v___x_1029_; 
lean_inc_ref(v_fst_1021_);
lean_dec(v_a_1017_);
v_val_1027_ = lean_ctor_get(v_fst_1021_, 0);
lean_inc(v_val_1027_);
lean_dec_ref_known(v_fst_1021_, 1);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 0, v_val_1027_);
v___x_1029_ = v___x_1019_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_val_1027_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
v_a_1032_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1016_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1016_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12(lean_object* v_init_1040_, lean_object* v_as_1041_, size_t v_sz_1042_, size_t v_i_1043_, lean_object* v_b_1044_){
_start:
{
uint8_t v___x_1046_; 
v___x_1046_ = lean_usize_dec_lt(v_i_1043_, v_sz_1042_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1047_, 0, v_b_1044_);
return v___x_1047_;
}
else
{
lean_object* v_snd_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1082_; 
v_snd_1048_ = lean_ctor_get(v_b_1044_, 1);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_b_1044_);
if (v_isSharedCheck_1082_ == 0)
{
lean_object* v_unused_1083_; 
v_unused_1083_ = lean_ctor_get(v_b_1044_, 0);
lean_dec(v_unused_1083_);
v___x_1050_ = v_b_1044_;
v_isShared_1051_ = v_isSharedCheck_1082_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_snd_1048_);
lean_dec(v_b_1044_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1082_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1052_; lean_object* v_a_1053_; lean_object* v___x_1054_; 
v___x_1052_ = lean_box(0);
v_a_1053_ = lean_array_uget_borrowed(v_as_1041_, v_i_1043_);
lean_inc(v_snd_1048_);
v___x_1054_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_1040_, v_a_1053_, v_snd_1048_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1073_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1057_ = v___x_1054_;
v_isShared_1058_ = v_isSharedCheck_1073_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1054_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1073_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
if (lean_obj_tag(v_a_1055_) == 0)
{
lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1059_, 0, v_a_1055_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 0, v___x_1059_);
v___x_1061_ = v___x_1050_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_snd_1048_);
v___x_1061_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1063_; 
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 0, v___x_1061_);
v___x_1063_ = v___x_1057_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; 
lean_del_object(v___x_1057_);
lean_dec(v_snd_1048_);
v_a_1066_ = lean_ctor_get(v_a_1055_, 0);
lean_inc(v_a_1066_);
lean_dec_ref_known(v_a_1055_, 1);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 1, v_a_1066_);
lean_ctor_set(v___x_1050_, 0, v___x_1052_);
v___x_1068_ = v___x_1050_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v_a_1066_);
v___x_1068_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
size_t v___x_1069_; size_t v___x_1070_; 
v___x_1069_ = ((size_t)1ULL);
v___x_1070_ = lean_usize_add(v_i_1043_, v___x_1069_);
v_i_1043_ = v___x_1070_;
v_b_1044_ = v___x_1068_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
lean_del_object(v___x_1050_);
lean_dec(v_snd_1048_);
v_a_1074_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1054_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1054_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12___boxed(lean_object* v_init_1084_, lean_object* v_as_1085_, lean_object* v_sz_1086_, lean_object* v_i_1087_, lean_object* v_b_1088_, lean_object* v___y_1089_){
_start:
{
size_t v_sz_boxed_1090_; size_t v_i_boxed_1091_; lean_object* v_res_1092_; 
v_sz_boxed_1090_ = lean_unbox_usize(v_sz_1086_);
lean_dec(v_sz_1086_);
v_i_boxed_1091_ = lean_unbox_usize(v_i_1087_);
lean_dec(v_i_1087_);
v_res_1092_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12(v_init_1084_, v_as_1085_, v_sz_boxed_1090_, v_i_boxed_1091_, v_b_1088_);
lean_dec_ref(v_as_1085_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10___boxed(lean_object* v_init_1093_, lean_object* v_n_1094_, lean_object* v_b_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_1093_, v_n_1094_, v_b_1095_);
lean_dec_ref(v_n_1094_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15(lean_object* v_as_1101_, size_t v_sz_1102_, size_t v_i_1103_, lean_object* v_b_1104_){
_start:
{
uint8_t v___x_1106_; 
v___x_1106_ = lean_usize_dec_lt(v_i_1103_, v_sz_1102_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; 
v___x_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1107_, 0, v_b_1104_);
return v___x_1107_;
}
else
{
uint8_t v___x_1108_; lean_object* v_a_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
lean_dec_ref(v_b_1104_);
v___x_1108_ = 0;
v_a_1109_ = lean_array_uget_borrowed(v_as_1101_, v_i_1103_);
lean_inc(v_a_1109_);
v___x_1110_ = l_Lean_Message_toString(v_a_1109_, v___x_1108_);
v___x_1111_ = l_IO_eprintln___at___00main_spec__6(v___x_1110_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v___x_1112_; size_t v___x_1113_; size_t v___x_1114_; 
lean_dec_ref_known(v___x_1111_, 1);
v___x_1112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_1113_ = ((size_t)1ULL);
v___x_1114_ = lean_usize_add(v_i_1103_, v___x_1113_);
v_i_1103_ = v___x_1114_;
v_b_1104_ = v___x_1112_;
goto _start;
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
v_a_1116_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1111_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1111_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___boxed(lean_object* v_as_1124_, lean_object* v_sz_1125_, lean_object* v_i_1126_, lean_object* v_b_1127_, lean_object* v___y_1128_){
_start:
{
size_t v_sz_boxed_1129_; size_t v_i_boxed_1130_; lean_object* v_res_1131_; 
v_sz_boxed_1129_ = lean_unbox_usize(v_sz_1125_);
lean_dec(v_sz_1125_);
v_i_boxed_1130_ = lean_unbox_usize(v_i_1126_);
lean_dec(v_i_1126_);
v_res_1131_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15(v_as_1124_, v_sz_boxed_1129_, v_i_boxed_1130_, v_b_1127_);
lean_dec_ref(v_as_1124_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(lean_object* v_as_1132_, size_t v_sz_1133_, size_t v_i_1134_, lean_object* v_b_1135_){
_start:
{
uint8_t v___x_1137_; 
v___x_1137_ = lean_usize_dec_lt(v_i_1134_, v_sz_1133_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1138_, 0, v_b_1135_);
return v___x_1138_;
}
else
{
uint8_t v___x_1139_; lean_object* v_a_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_dec_ref(v_b_1135_);
v___x_1139_ = 0;
v_a_1140_ = lean_array_uget_borrowed(v_as_1132_, v_i_1134_);
lean_inc(v_a_1140_);
v___x_1141_ = l_Lean_Message_toString(v_a_1140_, v___x_1139_);
v___x_1142_ = l_IO_eprintln___at___00main_spec__6(v___x_1141_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v___x_1143_; size_t v___x_1144_; size_t v___x_1145_; lean_object* v___x_1146_; 
lean_dec_ref_known(v___x_1142_, 1);
v___x_1143_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_1144_ = ((size_t)1ULL);
v___x_1145_ = lean_usize_add(v_i_1134_, v___x_1144_);
v___x_1146_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15(v_as_1132_, v_sz_1133_, v___x_1145_, v___x_1143_);
return v___x_1146_;
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
v_a_1147_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1142_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1142_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11___boxed(lean_object* v_as_1155_, lean_object* v_sz_1156_, lean_object* v_i_1157_, lean_object* v_b_1158_, lean_object* v___y_1159_){
_start:
{
size_t v_sz_boxed_1160_; size_t v_i_boxed_1161_; lean_object* v_res_1162_; 
v_sz_boxed_1160_ = lean_unbox_usize(v_sz_1156_);
lean_dec(v_sz_1156_);
v_i_boxed_1161_ = lean_unbox_usize(v_i_1157_);
lean_dec(v_i_1157_);
v_res_1162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_as_1155_, v_sz_boxed_1160_, v_i_boxed_1161_, v_b_1158_);
lean_dec_ref(v_as_1155_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7(lean_object* v_t_1163_, lean_object* v_init_1164_){
_start:
{
lean_object* v_root_1166_; lean_object* v_tail_1167_; lean_object* v___x_1168_; 
v_root_1166_ = lean_ctor_get(v_t_1163_, 0);
v_tail_1167_ = lean_ctor_get(v_t_1163_, 1);
v___x_1168_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_1164_, v_root_1166_, v_init_1164_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1205_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1171_ = v___x_1168_;
v_isShared_1172_ = v_isSharedCheck_1205_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1168_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1205_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
if (lean_obj_tag(v_a_1169_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1175_; 
v_a_1173_ = lean_ctor_get(v_a_1169_, 0);
lean_inc(v_a_1173_);
lean_dec_ref_known(v_a_1169_, 1);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v_a_1173_);
v___x_1175_ = v___x_1171_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1173_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; size_t v_sz_1180_; size_t v___x_1181_; lean_object* v___x_1182_; 
lean_del_object(v___x_1171_);
v_a_1177_ = lean_ctor_get(v_a_1169_, 0);
lean_inc(v_a_1177_);
lean_dec_ref_known(v_a_1169_, 1);
v___x_1178_ = lean_box(0);
v___x_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
lean_ctor_set(v___x_1179_, 1, v_a_1177_);
v_sz_1180_ = lean_array_size(v_tail_1167_);
v___x_1181_ = ((size_t)0ULL);
v___x_1182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_tail_1167_, v_sz_1180_, v___x_1181_, v___x_1179_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1196_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1185_ = v___x_1182_;
v_isShared_1186_ = v_isSharedCheck_1196_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1196_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v_fst_1187_; 
v_fst_1187_ = lean_ctor_get(v_a_1183_, 0);
if (lean_obj_tag(v_fst_1187_) == 0)
{
lean_object* v_snd_1188_; lean_object* v___x_1190_; 
v_snd_1188_ = lean_ctor_get(v_a_1183_, 1);
lean_inc(v_snd_1188_);
lean_dec(v_a_1183_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v_snd_1188_);
v___x_1190_ = v___x_1185_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_snd_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
else
{
lean_object* v_val_1192_; lean_object* v___x_1194_; 
lean_inc_ref(v_fst_1187_);
lean_dec(v_a_1183_);
v_val_1192_ = lean_ctor_get(v_fst_1187_, 0);
lean_inc(v_val_1192_);
lean_dec_ref_known(v_fst_1187_, 1);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v_val_1192_);
v___x_1194_ = v___x_1185_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_val_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
v_a_1197_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1182_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1182_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
v_a_1206_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1168_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1168_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7___boxed(lean_object* v_t_1214_, lean_object* v_init_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_t_1214_, v_init_1215_);
lean_dec_ref(v_t_1214_);
return v_res_1217_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0(uint8_t v_suppressElabErrors_1225_, uint8_t v___y_1226_, lean_object* v_x_1227_){
_start:
{
if (lean_obj_tag(v_x_1227_) == 1)
{
lean_object* v_pre_1228_; 
v_pre_1228_ = lean_ctor_get(v_x_1227_, 0);
switch(lean_obj_tag(v_pre_1228_))
{
case 1:
{
lean_object* v_pre_1229_; 
v_pre_1229_ = lean_ctor_get(v_pre_1228_, 0);
switch(lean_obj_tag(v_pre_1229_))
{
case 0:
{
lean_object* v_str_1230_; lean_object* v_str_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; 
v_str_1230_ = lean_ctor_get(v_x_1227_, 1);
v_str_1231_ = lean_ctor_get(v_pre_1228_, 1);
v___x_1232_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__0));
v___x_1233_ = lean_string_dec_eq(v_str_1231_, v___x_1232_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; uint8_t v___x_1235_; 
v___x_1234_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__1));
v___x_1235_ = lean_string_dec_eq(v_str_1231_, v___x_1234_);
if (v___x_1235_ == 0)
{
return v___x_1235_;
}
else
{
lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1236_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__2));
v___x_1237_ = lean_string_dec_eq(v_str_1230_, v___x_1236_);
if (v___x_1237_ == 0)
{
return v___x_1237_;
}
else
{
return v_suppressElabErrors_1225_;
}
}
}
else
{
lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1238_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__3));
v___x_1239_ = lean_string_dec_eq(v_str_1230_, v___x_1238_);
if (v___x_1239_ == 0)
{
return v___x_1239_;
}
else
{
return v_suppressElabErrors_1225_;
}
}
}
case 1:
{
lean_object* v_pre_1240_; 
v_pre_1240_ = lean_ctor_get(v_pre_1229_, 0);
if (lean_obj_tag(v_pre_1240_) == 0)
{
lean_object* v_str_1241_; lean_object* v_str_1242_; lean_object* v_str_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; 
v_str_1241_ = lean_ctor_get(v_x_1227_, 1);
v_str_1242_ = lean_ctor_get(v_pre_1228_, 1);
v_str_1243_ = lean_ctor_get(v_pre_1229_, 1);
v___x_1244_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__4));
v___x_1245_ = lean_string_dec_eq(v_str_1243_, v___x_1244_);
if (v___x_1245_ == 0)
{
return v___x_1245_;
}
else
{
lean_object* v___x_1246_; uint8_t v___x_1247_; 
v___x_1246_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__5));
v___x_1247_ = lean_string_dec_eq(v_str_1242_, v___x_1246_);
if (v___x_1247_ == 0)
{
return v___x_1247_;
}
else
{
lean_object* v___x_1248_; uint8_t v___x_1249_; 
v___x_1248_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__6));
v___x_1249_ = lean_string_dec_eq(v_str_1241_, v___x_1248_);
if (v___x_1249_ == 0)
{
return v___x_1249_;
}
else
{
return v_suppressElabErrors_1225_;
}
}
}
}
else
{
return v___y_1226_;
}
}
default: 
{
return v___y_1226_;
}
}
}
case 0:
{
lean_object* v_str_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v_str_1250_ = lean_ctor_get(v_x_1227_, 1);
v___x_1251_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_1252_ = lean_string_dec_eq(v_str_1250_, v___x_1251_);
if (v___x_1252_ == 0)
{
return v___x_1252_;
}
else
{
return v_suppressElabErrors_1225_;
}
}
default: 
{
return v___y_1226_;
}
}
}
else
{
return v___y_1226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___boxed(lean_object* v_suppressElabErrors_1253_, lean_object* v___y_1254_, lean_object* v_x_1255_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1256_; uint8_t v___y_38151__boxed_1257_; uint8_t v_res_1258_; lean_object* v_r_1259_; 
v_suppressElabErrors_boxed_1256_ = lean_unbox(v_suppressElabErrors_1253_);
v___y_38151__boxed_1257_ = lean_unbox(v___y_1254_);
v_res_1258_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0(v_suppressElabErrors_boxed_1256_, v___y_38151__boxed_1257_, v_x_1255_);
lean_dec(v_x_1255_);
v_r_1259_ = lean_box(v_res_1258_);
return v_r_1259_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(lean_object* v_opts_1260_, lean_object* v_opt_1261_){
_start:
{
lean_object* v_name_1262_; lean_object* v_defValue_1263_; lean_object* v_map_1264_; lean_object* v___x_1265_; 
v_name_1262_ = lean_ctor_get(v_opt_1261_, 0);
v_defValue_1263_ = lean_ctor_get(v_opt_1261_, 1);
v_map_1264_ = lean_ctor_get(v_opts_1260_, 0);
v___x_1265_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1264_, v_name_1262_);
if (lean_obj_tag(v___x_1265_) == 0)
{
uint8_t v___x_1266_; 
v___x_1266_ = lean_unbox(v_defValue_1263_);
return v___x_1266_;
}
else
{
lean_object* v_val_1267_; 
v_val_1267_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_val_1267_);
lean_dec_ref_known(v___x_1265_, 1);
if (lean_obj_tag(v_val_1267_) == 1)
{
uint8_t v_v_1268_; 
v_v_1268_ = lean_ctor_get_uint8(v_val_1267_, 0);
lean_dec_ref_known(v_val_1267_, 0);
return v_v_1268_;
}
else
{
uint8_t v___x_1269_; 
lean_dec(v_val_1267_);
v___x_1269_ = lean_unbox(v_defValue_1263_);
return v___x_1269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___boxed(lean_object* v_opts_1270_, lean_object* v_opt_1271_){
_start:
{
uint8_t v_res_1272_; lean_object* v_r_1273_; 
v_res_1272_ = l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(v_opts_1270_, v_opt_1271_);
lean_dec_ref(v_opt_1271_);
lean_dec_ref(v_opts_1270_);
v_r_1273_ = lean_box(v_res_1272_);
return v_r_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44(lean_object* v_ref_1275_, lean_object* v_msgData_1276_, uint8_t v_severity_1277_, uint8_t v_isSilent_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___y_1283_; lean_object* v___y_1284_; uint8_t v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; uint8_t v___y_1289_; lean_object* v_toCold_1290_; lean_object* v___y_1291_; lean_object* v___y_1320_; lean_object* v___y_1321_; uint8_t v___y_1322_; lean_object* v___y_1323_; uint8_t v___y_1324_; uint8_t v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1347_; uint8_t v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; uint8_t v___y_1351_; uint8_t v___y_1352_; lean_object* v___y_1353_; uint8_t v___y_1357_; uint8_t v___y_1358_; uint8_t v___y_1359_; uint8_t v___x_1370_; uint8_t v___y_1372_; uint8_t v___y_1373_; uint8_t v___y_1374_; uint8_t v___y_1376_; uint8_t v___x_1384_; 
v___x_1370_ = 2;
v___x_1384_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1277_, v___x_1370_);
if (v___x_1384_ == 0)
{
v___y_1376_ = v___x_1384_;
goto v___jp_1375_;
}
else
{
uint8_t v___x_1385_; 
lean_inc_ref(v_msgData_1276_);
v___x_1385_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1276_);
v___y_1376_ = v___x_1385_;
goto v___jp_1375_;
}
v___jp_1282_:
{
lean_object* v_currNamespace_1292_; lean_object* v_openDecls_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v_env_1298_; lean_object* v_nextMacroScope_1299_; lean_object* v_ngen_1300_; lean_object* v_auxDeclNGen_1301_; lean_object* v_traceState_1302_; lean_object* v_cache_1303_; lean_object* v_recordedDeps_1304_; lean_object* v_messages_1305_; lean_object* v_infoState_1306_; lean_object* v_snapshotTasks_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1318_; 
v_currNamespace_1292_ = lean_ctor_get(v_toCold_1290_, 4);
v_openDecls_1293_ = lean_ctor_get(v_toCold_1290_, 5);
lean_inc(v_openDecls_1293_);
lean_inc(v_currNamespace_1292_);
v___x_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1294_, 0, v_currNamespace_1292_);
lean_ctor_set(v___x_1294_, 1, v_openDecls_1293_);
v___x_1295_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
lean_ctor_set(v___x_1295_, 1, v___y_1288_);
lean_inc_ref(v___y_1284_);
lean_inc_ref(v___y_1287_);
v___x_1296_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1296_, 0, v___y_1287_);
lean_ctor_set(v___x_1296_, 1, v___y_1283_);
lean_ctor_set(v___x_1296_, 2, v___y_1286_);
lean_ctor_set(v___x_1296_, 3, v___y_1284_);
lean_ctor_set(v___x_1296_, 4, v___x_1295_);
lean_ctor_set_uint8(v___x_1296_, sizeof(void*)*5, v___y_1285_);
lean_ctor_set_uint8(v___x_1296_, sizeof(void*)*5 + 1, v___y_1289_);
lean_ctor_set_uint8(v___x_1296_, sizeof(void*)*5 + 2, v_isSilent_1278_);
v___x_1297_ = lean_st_ref_take(v___y_1291_);
v_env_1298_ = lean_ctor_get(v___x_1297_, 0);
v_nextMacroScope_1299_ = lean_ctor_get(v___x_1297_, 1);
v_ngen_1300_ = lean_ctor_get(v___x_1297_, 2);
v_auxDeclNGen_1301_ = lean_ctor_get(v___x_1297_, 3);
v_traceState_1302_ = lean_ctor_get(v___x_1297_, 4);
v_cache_1303_ = lean_ctor_get(v___x_1297_, 5);
v_recordedDeps_1304_ = lean_ctor_get(v___x_1297_, 6);
v_messages_1305_ = lean_ctor_get(v___x_1297_, 7);
v_infoState_1306_ = lean_ctor_get(v___x_1297_, 8);
v_snapshotTasks_1307_ = lean_ctor_get(v___x_1297_, 9);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1309_ = v___x_1297_;
v_isShared_1310_ = v_isSharedCheck_1318_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_snapshotTasks_1307_);
lean_inc(v_infoState_1306_);
lean_inc(v_messages_1305_);
lean_inc(v_recordedDeps_1304_);
lean_inc(v_cache_1303_);
lean_inc(v_traceState_1302_);
lean_inc(v_auxDeclNGen_1301_);
lean_inc(v_ngen_1300_);
lean_inc(v_nextMacroScope_1299_);
lean_inc(v_env_1298_);
lean_dec(v___x_1297_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1318_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1311_ = lean_box(0);
v___x_1312_ = l_Lean_MessageLog_add(v___x_1296_, v_messages_1305_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 7, v___x_1312_);
v___x_1314_ = v___x_1309_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_env_1298_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v_nextMacroScope_1299_);
lean_ctor_set(v_reuseFailAlloc_1317_, 2, v_ngen_1300_);
lean_ctor_set(v_reuseFailAlloc_1317_, 3, v_auxDeclNGen_1301_);
lean_ctor_set(v_reuseFailAlloc_1317_, 4, v_traceState_1302_);
lean_ctor_set(v_reuseFailAlloc_1317_, 5, v_cache_1303_);
lean_ctor_set(v_reuseFailAlloc_1317_, 6, v_recordedDeps_1304_);
lean_ctor_set(v_reuseFailAlloc_1317_, 7, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1317_, 8, v_infoState_1306_);
lean_ctor_set(v_reuseFailAlloc_1317_, 9, v_snapshotTasks_1307_);
v___x_1314_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = lean_st_ref_put(v___y_1291_, v___x_1314_);
v___x_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1311_);
return v___x_1316_;
}
}
}
v___jp_1319_:
{
lean_object* v_fileName_1328_; lean_object* v_fileMap_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1345_; 
v_fileName_1328_ = lean_ctor_get(v___y_1323_, 0);
v_fileMap_1329_ = lean_ctor_get(v___y_1323_, 1);
v___x_1330_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1276_);
v___x_1331_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v___x_1330_, v___y_1279_, v___y_1280_);
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1334_ = v___x_1331_;
v_isShared_1335_ = v_isSharedCheck_1345_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1331_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1345_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
lean_inc_ref_n(v_fileMap_1329_, 2);
v___x_1336_ = l_Lean_FileMap_toPosition(v_fileMap_1329_, v___y_1326_);
lean_dec(v___y_1326_);
v___x_1337_ = l_Lean_FileMap_toPosition(v_fileMap_1329_, v___y_1327_);
lean_dec(v___y_1327_);
v___x_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
v___x_1339_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___closed__0));
if (v___y_1322_ == 0)
{
lean_del_object(v___x_1334_);
lean_dec_ref(v___y_1320_);
v___y_1283_ = v___x_1336_;
v___y_1284_ = v___x_1339_;
v___y_1285_ = v___y_1324_;
v___y_1286_ = v___x_1338_;
v___y_1287_ = v_fileName_1328_;
v___y_1288_ = v_a_1332_;
v___y_1289_ = v___y_1325_;
v_toCold_1290_ = v___y_1321_;
v___y_1291_ = v___y_1280_;
goto v___jp_1282_;
}
else
{
uint8_t v___x_1340_; 
lean_inc(v_a_1332_);
v___x_1340_ = l_Lean_MessageData_hasTag(v___y_1320_, v_a_1332_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; lean_object* v___x_1343_; 
lean_dec_ref_known(v___x_1338_, 1);
lean_dec_ref(v___x_1336_);
lean_dec(v_a_1332_);
v___x_1341_ = lean_box(0);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1341_);
v___x_1343_ = v___x_1334_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
else
{
lean_del_object(v___x_1334_);
v___y_1283_ = v___x_1336_;
v___y_1284_ = v___x_1339_;
v___y_1285_ = v___y_1324_;
v___y_1286_ = v___x_1338_;
v___y_1287_ = v_fileName_1328_;
v___y_1288_ = v_a_1332_;
v___y_1289_ = v___y_1325_;
v_toCold_1290_ = v___y_1321_;
v___y_1291_ = v___y_1280_;
goto v___jp_1282_;
}
}
}
}
v___jp_1346_:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_Syntax_getTailPos_x3f(v___y_1350_, v___y_1351_);
lean_dec(v___y_1350_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_inc(v___y_1353_);
v___y_1320_ = v___y_1347_;
v___y_1321_ = v___y_1349_;
v___y_1322_ = v___y_1348_;
v___y_1323_ = v___y_1349_;
v___y_1324_ = v___y_1351_;
v___y_1325_ = v___y_1352_;
v___y_1326_ = v___y_1353_;
v___y_1327_ = v___y_1353_;
goto v___jp_1319_;
}
else
{
lean_object* v_val_1355_; 
v_val_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_val_1355_);
lean_dec_ref_known(v___x_1354_, 1);
v___y_1320_ = v___y_1347_;
v___y_1321_ = v___y_1349_;
v___y_1322_ = v___y_1348_;
v___y_1323_ = v___y_1349_;
v___y_1324_ = v___y_1351_;
v___y_1325_ = v___y_1352_;
v___y_1326_ = v___y_1353_;
v___y_1327_ = v_val_1355_;
goto v___jp_1319_;
}
}
v___jp_1356_:
{
lean_object* v_toCold_1360_; lean_object* v_ref_1361_; uint8_t v_suppressElabErrors_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___f_1365_; lean_object* v_ref_1366_; lean_object* v___x_1367_; 
v_toCold_1360_ = lean_ctor_get(v___y_1279_, 0);
v_ref_1361_ = lean_ctor_get(v___y_1279_, 2);
v_suppressElabErrors_1362_ = lean_ctor_get_uint8(v___y_1279_, sizeof(void*)*3 + 2);
v___x_1363_ = lean_box(v_suppressElabErrors_1362_);
v___x_1364_ = lean_box(v___y_1357_);
v___f_1365_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1365_, 0, v___x_1363_);
lean_closure_set(v___f_1365_, 1, v___x_1364_);
v_ref_1366_ = l_Lean_replaceRef(v_ref_1275_, v_ref_1361_);
v___x_1367_ = l_Lean_Syntax_getPos_x3f(v_ref_1366_, v___y_1358_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v___x_1368_; 
v___x_1368_ = lean_unsigned_to_nat(0u);
v___y_1347_ = v___f_1365_;
v___y_1348_ = v_suppressElabErrors_1362_;
v___y_1349_ = v_toCold_1360_;
v___y_1350_ = v_ref_1366_;
v___y_1351_ = v___y_1358_;
v___y_1352_ = v___y_1359_;
v___y_1353_ = v___x_1368_;
goto v___jp_1346_;
}
else
{
lean_object* v_val_1369_; 
v_val_1369_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_val_1369_);
lean_dec_ref_known(v___x_1367_, 1);
v___y_1347_ = v___f_1365_;
v___y_1348_ = v_suppressElabErrors_1362_;
v___y_1349_ = v_toCold_1360_;
v___y_1350_ = v_ref_1366_;
v___y_1351_ = v___y_1358_;
v___y_1352_ = v___y_1359_;
v___y_1353_ = v_val_1369_;
goto v___jp_1346_;
}
}
v___jp_1371_:
{
if (v___y_1374_ == 0)
{
v___y_1357_ = v___y_1372_;
v___y_1358_ = v___y_1373_;
v___y_1359_ = v_severity_1277_;
goto v___jp_1356_;
}
else
{
v___y_1357_ = v___y_1372_;
v___y_1358_ = v___y_1373_;
v___y_1359_ = v___x_1370_;
goto v___jp_1356_;
}
}
v___jp_1375_:
{
if (v___y_1376_ == 0)
{
uint8_t v___x_1377_; uint8_t v___x_1378_; 
v___x_1377_ = 1;
v___x_1378_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1277_, v___x_1377_);
if (v___x_1378_ == 0)
{
v___y_1372_ = v___y_1376_;
v___y_1373_ = v___y_1376_;
v___y_1374_ = v___x_1378_;
goto v___jp_1371_;
}
else
{
lean_object* v___x_1379_; lean_object* v___x_1380_; uint8_t v___x_1381_; 
v___x_1379_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1279_);
v___x_1380_ = l_Lean_warningAsError;
v___x_1381_ = l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(v___x_1379_, v___x_1380_);
lean_dec_ref(v___x_1379_);
v___y_1372_ = v___y_1376_;
v___y_1373_ = v___y_1376_;
v___y_1374_ = v___x_1381_;
goto v___jp_1371_;
}
}
else
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
lean_dec_ref(v_msgData_1276_);
v___x_1382_ = lean_box(0);
v___x_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
return v___x_1383_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___boxed(lean_object* v_ref_1386_, lean_object* v_msgData_1387_, lean_object* v_severity_1388_, lean_object* v_isSilent_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
uint8_t v_severity_boxed_1393_; uint8_t v_isSilent_boxed_1394_; lean_object* v_res_1395_; 
v_severity_boxed_1393_ = lean_unbox(v_severity_1388_);
v_isSilent_boxed_1394_ = lean_unbox(v_isSilent_1389_);
v_res_1395_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44(v_ref_1386_, v_msgData_1387_, v_severity_boxed_1393_, v_isSilent_boxed_1394_, v___y_1390_, v___y_1391_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v_ref_1386_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30(lean_object* v_msgData_1396_, uint8_t v_severity_1397_, uint8_t v_isSilent_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v_ref_1402_; lean_object* v___x_1403_; 
v_ref_1402_ = lean_ctor_get(v___y_1399_, 2);
v___x_1403_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44(v_ref_1402_, v_msgData_1396_, v_severity_1397_, v_isSilent_1398_, v___y_1399_, v___y_1400_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30___boxed(lean_object* v_msgData_1404_, lean_object* v_severity_1405_, lean_object* v_isSilent_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
uint8_t v_severity_boxed_1410_; uint8_t v_isSilent_boxed_1411_; lean_object* v_res_1412_; 
v_severity_boxed_1410_ = lean_unbox(v_severity_1405_);
v_isSilent_boxed_1411_ = lean_unbox(v_isSilent_1406_);
v_res_1412_ = l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30(v_msgData_1404_, v_severity_boxed_1410_, v_isSilent_boxed_1411_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13(lean_object* v_msgData_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
uint8_t v___x_1417_; uint8_t v___x_1418_; lean_object* v___x_1419_; 
v___x_1417_ = 2;
v___x_1418_ = 0;
v___x_1419_ = l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30(v_msgData_1413_, v___x_1417_, v___x_1418_, v___y_1414_, v___y_1415_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13___boxed(lean_object* v_msgData_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_logError___at___00main_spec__13(v_msgData_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(lean_object* v_opts_1425_, lean_object* v_opt_1426_){
_start:
{
lean_object* v_name_1427_; lean_object* v_map_1428_; lean_object* v___x_1429_; 
v_name_1427_ = lean_ctor_get(v_opt_1426_, 0);
v_map_1428_ = lean_ctor_get(v_opts_1425_, 0);
v___x_1429_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1428_, v_name_1427_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v___x_1430_; 
v___x_1430_ = lean_box(0);
return v___x_1430_;
}
else
{
lean_object* v_val_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1440_; 
v_val_1431_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1433_ = v___x_1429_;
v_isShared_1434_ = v_isSharedCheck_1440_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_val_1431_);
lean_dec(v___x_1429_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1440_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
if (lean_obj_tag(v_val_1431_) == 0)
{
lean_object* v_v_1435_; lean_object* v___x_1437_; 
v_v_1435_ = lean_ctor_get(v_val_1431_, 0);
lean_inc_ref(v_v_1435_);
lean_dec_ref_known(v_val_1431_, 1);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 0, v_v_1435_);
v___x_1437_ = v___x_1433_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_v_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
else
{
lean_object* v___x_1439_; 
lean_del_object(v___x_1433_);
lean_dec(v_val_1431_);
v___x_1439_ = lean_box(0);
return v___x_1439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___boxed(lean_object* v_opts_1441_, lean_object* v_opt_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(v_opts_1441_, v_opt_1442_);
lean_dec_ref(v_opt_1442_);
lean_dec_ref(v_opts_1441_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22(lean_object* v_x_1444_, lean_object* v_x_1445_){
_start:
{
if (lean_obj_tag(v_x_1445_) == 0)
{
return v_x_1444_;
}
else
{
lean_object* v_key_1446_; lean_object* v_value_1447_; lean_object* v_tail_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v_key_1446_ = lean_ctor_get(v_x_1445_, 0);
v_value_1447_ = lean_ctor_get(v_x_1445_, 1);
v_tail_1448_ = lean_ctor_get(v_x_1445_, 2);
lean_inc(v_value_1447_);
lean_inc(v_key_1446_);
v___x_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1449_, 0, v_key_1446_);
lean_ctor_set(v___x_1449_, 1, v_value_1447_);
v___x_1450_ = lean_array_push(v_x_1444_, v___x_1449_);
v_x_1444_ = v___x_1450_;
v_x_1445_ = v_tail_1448_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22___boxed(lean_object* v_x_1452_, lean_object* v_x_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22(v_x_1452_, v_x_1453_);
lean_dec(v_x_1453_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23(lean_object* v_as_1455_, size_t v_i_1456_, size_t v_stop_1457_, lean_object* v_b_1458_){
_start:
{
uint8_t v___x_1459_; 
v___x_1459_ = lean_usize_dec_eq(v_i_1456_, v_stop_1457_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; lean_object* v___x_1461_; size_t v___x_1462_; size_t v___x_1463_; 
v___x_1460_ = lean_array_uget_borrowed(v_as_1455_, v_i_1456_);
v___x_1461_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22(v_b_1458_, v___x_1460_);
v___x_1462_ = ((size_t)1ULL);
v___x_1463_ = lean_usize_add(v_i_1456_, v___x_1462_);
v_i_1456_ = v___x_1463_;
v_b_1458_ = v___x_1461_;
goto _start;
}
else
{
return v_b_1458_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23___boxed(lean_object* v_as_1465_, lean_object* v_i_1466_, lean_object* v_stop_1467_, lean_object* v_b_1468_){
_start:
{
size_t v_i_boxed_1469_; size_t v_stop_boxed_1470_; lean_object* v_res_1471_; 
v_i_boxed_1469_ = lean_unbox_usize(v_i_1466_);
lean_dec(v_i_1466_);
v_stop_boxed_1470_ = lean_unbox_usize(v_stop_1467_);
lean_dec(v_stop_1467_);
v_res_1471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23(v_as_1465_, v_i_boxed_1469_, v_stop_boxed_1470_, v_b_1468_);
lean_dec_ref(v_as_1465_);
return v_res_1471_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(lean_object* v_x_1472_, lean_object* v_x_1473_){
_start:
{
lean_object* v_fst_1474_; lean_object* v_fst_1475_; lean_object* v_fst_1476_; lean_object* v_fst_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; uint8_t v___x_1480_; 
v_fst_1474_ = lean_ctor_get(v_x_1472_, 0);
v_fst_1475_ = lean_ctor_get(v_x_1473_, 0);
v_fst_1476_ = lean_ctor_get(v_fst_1474_, 0);
v_fst_1477_ = lean_ctor_get(v_fst_1475_, 0);
v___x_1478_ = lean_unsigned_to_nat(1u);
v___x_1479_ = lean_nat_add(v_fst_1476_, v___x_1478_);
v___x_1480_ = lean_nat_dec_le(v___x_1479_, v_fst_1477_);
lean_dec(v___x_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0___boxed(lean_object* v_x_1481_, lean_object* v_x_1482_){
_start:
{
uint8_t v_res_1483_; lean_object* v_r_1484_; 
v_res_1483_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v_x_1481_, v_x_1482_);
lean_dec_ref(v_x_1482_);
lean_dec_ref(v_x_1481_);
v_r_1484_ = lean_box(v_res_1483_);
return v_r_1484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(lean_object* v_hi_1485_, lean_object* v_pivot_1486_, lean_object* v_as_1487_, lean_object* v_i_1488_, lean_object* v_k_1489_){
_start:
{
uint8_t v___x_1490_; 
v___x_1490_ = lean_nat_dec_lt(v_k_1489_, v_hi_1485_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
lean_dec(v_k_1489_);
v___x_1491_ = lean_array_fswap(v_as_1487_, v_i_1488_, v_hi_1485_);
v___x_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1492_, 0, v_i_1488_);
lean_ctor_set(v___x_1492_, 1, v___x_1491_);
return v___x_1492_;
}
else
{
lean_object* v___x_1493_; lean_object* v_fst_1494_; lean_object* v_fst_1495_; lean_object* v_fst_1496_; lean_object* v_fst_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; 
v___x_1493_ = lean_array_fget_borrowed(v_as_1487_, v_k_1489_);
v_fst_1494_ = lean_ctor_get(v___x_1493_, 0);
v_fst_1495_ = lean_ctor_get(v_pivot_1486_, 0);
v_fst_1496_ = lean_ctor_get(v_fst_1494_, 0);
v_fst_1497_ = lean_ctor_get(v_fst_1495_, 0);
v___x_1498_ = lean_unsigned_to_nat(1u);
v___x_1499_ = lean_nat_add(v_fst_1496_, v___x_1498_);
v___x_1500_ = lean_nat_dec_le(v___x_1499_, v_fst_1497_);
lean_dec(v___x_1499_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_nat_add(v_k_1489_, v___x_1498_);
lean_dec(v_k_1489_);
v_k_1489_ = v___x_1501_;
goto _start;
}
else
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1503_ = lean_array_fswap(v_as_1487_, v_i_1488_, v_k_1489_);
v___x_1504_ = lean_nat_add(v_i_1488_, v___x_1498_);
lean_dec(v_i_1488_);
v___x_1505_ = lean_nat_add(v_k_1489_, v___x_1498_);
lean_dec(v_k_1489_);
v_as_1487_ = v___x_1503_;
v_i_1488_ = v___x_1504_;
v_k_1489_ = v___x_1505_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg___boxed(lean_object* v_hi_1507_, lean_object* v_pivot_1508_, lean_object* v_as_1509_, lean_object* v_i_1510_, lean_object* v_k_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(v_hi_1507_, v_pivot_1508_, v_as_1509_, v_i_1510_, v_k_1511_);
lean_dec_ref(v_pivot_1508_);
lean_dec(v_hi_1507_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(lean_object* v_n_1513_, lean_object* v_as_1514_, lean_object* v_lo_1515_, lean_object* v_hi_1516_){
_start:
{
lean_object* v___y_1518_; uint8_t v___x_1528_; 
v___x_1528_ = lean_nat_dec_lt(v_lo_1515_, v_hi_1516_);
if (v___x_1528_ == 0)
{
lean_dec(v_lo_1515_);
return v_as_1514_;
}
else
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v_mid_1531_; lean_object* v___y_1533_; lean_object* v___y_1539_; lean_object* v___x_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; 
v___x_1529_ = lean_nat_add(v_lo_1515_, v_hi_1516_);
v___x_1530_ = lean_unsigned_to_nat(1u);
v_mid_1531_ = lean_nat_shiftr(v___x_1529_, v___x_1530_);
lean_dec(v___x_1529_);
v___x_1544_ = lean_array_fget_borrowed(v_as_1514_, v_mid_1531_);
v___x_1545_ = lean_array_fget_borrowed(v_as_1514_, v_lo_1515_);
v___x_1546_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v___x_1544_, v___x_1545_);
if (v___x_1546_ == 0)
{
v___y_1539_ = v_as_1514_;
goto v___jp_1538_;
}
else
{
lean_object* v___x_1547_; 
v___x_1547_ = lean_array_fswap(v_as_1514_, v_lo_1515_, v_mid_1531_);
v___y_1539_ = v___x_1547_;
goto v___jp_1538_;
}
v___jp_1532_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; 
v___x_1534_ = lean_array_fget_borrowed(v___y_1533_, v_mid_1531_);
v___x_1535_ = lean_array_fget_borrowed(v___y_1533_, v_hi_1516_);
v___x_1536_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v___x_1534_, v___x_1535_);
if (v___x_1536_ == 0)
{
lean_dec(v_mid_1531_);
v___y_1518_ = v___y_1533_;
goto v___jp_1517_;
}
else
{
lean_object* v___x_1537_; 
v___x_1537_ = lean_array_fswap(v___y_1533_, v_mid_1531_, v_hi_1516_);
lean_dec(v_mid_1531_);
v___y_1518_ = v___x_1537_;
goto v___jp_1517_;
}
}
v___jp_1538_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; uint8_t v___x_1542_; 
v___x_1540_ = lean_array_fget_borrowed(v___y_1539_, v_hi_1516_);
v___x_1541_ = lean_array_fget_borrowed(v___y_1539_, v_lo_1515_);
v___x_1542_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v___x_1540_, v___x_1541_);
if (v___x_1542_ == 0)
{
v___y_1533_ = v___y_1539_;
goto v___jp_1532_;
}
else
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_array_fswap(v___y_1539_, v_lo_1515_, v_hi_1516_);
v___y_1533_ = v___x_1543_;
goto v___jp_1532_;
}
}
}
v___jp_1517_:
{
lean_object* v_pivot_1519_; lean_object* v___x_1520_; lean_object* v_fst_1521_; lean_object* v_snd_1522_; uint8_t v___x_1523_; 
v_pivot_1519_ = lean_array_fget(v___y_1518_, v_hi_1516_);
lean_inc_n(v_lo_1515_, 2);
v___x_1520_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(v_hi_1516_, v_pivot_1519_, v___y_1518_, v_lo_1515_, v_lo_1515_);
lean_dec(v_pivot_1519_);
v_fst_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_fst_1521_);
v_snd_1522_ = lean_ctor_get(v___x_1520_, 1);
lean_inc(v_snd_1522_);
lean_dec_ref(v___x_1520_);
v___x_1523_ = lean_nat_dec_le(v_hi_1516_, v_fst_1521_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1524_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v_n_1513_, v_snd_1522_, v_lo_1515_, v_fst_1521_);
v___x_1525_ = lean_unsigned_to_nat(1u);
v___x_1526_ = lean_nat_add(v_fst_1521_, v___x_1525_);
lean_dec(v_fst_1521_);
v_as_1514_ = v___x_1524_;
v_lo_1515_ = v___x_1526_;
goto _start;
}
else
{
lean_dec(v_fst_1521_);
lean_dec(v_lo_1515_);
return v_snd_1522_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___boxed(lean_object* v_n_1548_, lean_object* v_as_1549_, lean_object* v_lo_1550_, lean_object* v_hi_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v_n_1548_, v_as_1549_, v_lo_1550_, v_hi_1551_);
lean_dec(v_hi_1551_);
lean_dec(v_n_1548_);
return v_res_1552_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0(uint8_t v_suppressElabErrors_1553_, uint8_t v___x_1554_, lean_object* v___x_1555_, lean_object* v_x_1556_){
_start:
{
if (lean_obj_tag(v_x_1556_) == 1)
{
lean_object* v_pre_1557_; 
v_pre_1557_ = lean_ctor_get(v_x_1556_, 0);
switch(lean_obj_tag(v_pre_1557_))
{
case 1:
{
lean_object* v_pre_1558_; 
v_pre_1558_ = lean_ctor_get(v_pre_1557_, 0);
switch(lean_obj_tag(v_pre_1558_))
{
case 0:
{
lean_object* v_str_1559_; lean_object* v_str_1560_; lean_object* v___x_1561_; uint8_t v___x_1562_; 
v_str_1559_ = lean_ctor_get(v_x_1556_, 1);
v_str_1560_ = lean_ctor_get(v_pre_1557_, 1);
v___x_1561_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__0));
v___x_1562_ = lean_string_dec_eq(v_str_1560_, v___x_1561_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; uint8_t v___x_1564_; 
v___x_1563_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__1));
v___x_1564_ = lean_string_dec_eq(v_str_1560_, v___x_1563_);
if (v___x_1564_ == 0)
{
return v___x_1564_;
}
else
{
lean_object* v___x_1565_; uint8_t v___x_1566_; 
v___x_1565_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__2));
v___x_1566_ = lean_string_dec_eq(v_str_1559_, v___x_1565_);
if (v___x_1566_ == 0)
{
return v___x_1566_;
}
else
{
return v_suppressElabErrors_1553_;
}
}
}
else
{
lean_object* v___x_1567_; uint8_t v___x_1568_; 
v___x_1567_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__3));
v___x_1568_ = lean_string_dec_eq(v_str_1559_, v___x_1567_);
if (v___x_1568_ == 0)
{
return v___x_1568_;
}
else
{
return v_suppressElabErrors_1553_;
}
}
}
case 1:
{
lean_object* v_pre_1569_; 
v_pre_1569_ = lean_ctor_get(v_pre_1558_, 0);
if (lean_obj_tag(v_pre_1569_) == 0)
{
lean_object* v_str_1570_; lean_object* v_str_1571_; lean_object* v_str_1572_; lean_object* v___x_1573_; uint8_t v___x_1574_; 
v_str_1570_ = lean_ctor_get(v_x_1556_, 1);
v_str_1571_ = lean_ctor_get(v_pre_1557_, 1);
v_str_1572_ = lean_ctor_get(v_pre_1558_, 1);
v___x_1573_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__4));
v___x_1574_ = lean_string_dec_eq(v_str_1572_, v___x_1573_);
if (v___x_1574_ == 0)
{
return v___x_1574_;
}
else
{
lean_object* v___x_1575_; uint8_t v___x_1576_; 
v___x_1575_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__5));
v___x_1576_ = lean_string_dec_eq(v_str_1571_, v___x_1575_);
if (v___x_1576_ == 0)
{
return v___x_1576_;
}
else
{
lean_object* v___x_1577_; uint8_t v___x_1578_; 
v___x_1577_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__6));
v___x_1578_ = lean_string_dec_eq(v_str_1570_, v___x_1577_);
if (v___x_1578_ == 0)
{
return v___x_1578_;
}
else
{
return v_suppressElabErrors_1553_;
}
}
}
}
else
{
return v___x_1554_;
}
}
default: 
{
return v___x_1554_;
}
}
}
case 0:
{
lean_object* v_str_1579_; uint8_t v___x_1580_; 
v_str_1579_ = lean_ctor_get(v_x_1556_, 1);
v___x_1580_ = lean_string_dec_eq(v_str_1579_, v___x_1555_);
if (v___x_1580_ == 0)
{
return v___x_1580_;
}
else
{
return v_suppressElabErrors_1553_;
}
}
default: 
{
return v___x_1554_;
}
}
}
else
{
return v___x_1554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0___boxed(lean_object* v_suppressElabErrors_1581_, lean_object* v___x_1582_, lean_object* v___x_1583_, lean_object* v_x_1584_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1585_; uint8_t v___x_38615__boxed_1586_; uint8_t v_res_1587_; lean_object* v_r_1588_; 
v_suppressElabErrors_boxed_1585_ = lean_unbox(v_suppressElabErrors_1581_);
v___x_38615__boxed_1586_ = lean_unbox(v___x_1582_);
v_res_1587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0(v_suppressElabErrors_boxed_1585_, v___x_38615__boxed_1586_, v___x_1583_, v_x_1584_);
lean_dec(v_x_1584_);
lean_dec_ref(v___x_1583_);
v_r_1588_ = lean_box(v_res_1587_);
return v_r_1588_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0(void){
_start:
{
lean_object* v___x_1589_; double v___x_1590_; 
v___x_1589_ = lean_unsigned_to_nat(0u);
v___x_1590_ = lean_float_of_nat(v___x_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(uint8_t v___x_1591_, lean_object* v_as_1592_, size_t v_sz_1593_, size_t v_i_1594_, lean_object* v_b_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v_a_1600_; uint8_t v___x_1604_; 
v___x_1604_ = lean_usize_dec_lt(v_i_1594_, v_sz_1593_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; 
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v_b_1595_);
return v___x_1605_;
}
else
{
lean_object* v_a_1606_; lean_object* v_fst_1607_; lean_object* v_snd_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1687_; 
v_a_1606_ = lean_array_uget(v_as_1592_, v_i_1594_);
v_fst_1607_ = lean_ctor_get(v_a_1606_, 0);
v_snd_1608_ = lean_ctor_get(v_a_1606_, 1);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_a_1606_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1610_ = v_a_1606_;
v_isShared_1611_ = v_isSharedCheck_1687_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_snd_1608_);
lean_inc(v_fst_1607_);
lean_dec(v_a_1606_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1687_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v_fst_1612_; lean_object* v_snd_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1686_; 
v_fst_1612_ = lean_ctor_get(v_fst_1607_, 0);
v_snd_1613_ = lean_ctor_get(v_fst_1607_, 1);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_fst_1607_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1615_ = v_fst_1607_;
v_isShared_1616_ = v_isSharedCheck_1686_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_snd_1613_);
lean_inc(v_fst_1612_);
lean_dec(v_fst_1607_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1686_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; double v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v_toCold_1622_; uint8_t v_suppressElabErrors_1623_; lean_object* v_fileName_1624_; lean_object* v_fileMap_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1632_; 
v___x_1617_ = lean_box(0);
v___x_1618_ = lean_box(0);
v___x_1619_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0);
v___x_1620_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___closed__0));
v___x_1621_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1621_, 0, v___x_1617_);
lean_ctor_set(v___x_1621_, 1, v___x_1618_);
lean_ctor_set(v___x_1621_, 2, v___x_1620_);
lean_ctor_set_float(v___x_1621_, sizeof(void*)*3, v___x_1619_);
lean_ctor_set_float(v___x_1621_, sizeof(void*)*3 + 8, v___x_1619_);
lean_ctor_set_uint8(v___x_1621_, sizeof(void*)*3 + 16, v___x_1604_);
v_toCold_1622_ = lean_ctor_get(v___y_1596_, 0);
v_suppressElabErrors_1623_ = lean_ctor_get_uint8(v___y_1596_, sizeof(void*)*3 + 2);
v_fileName_1624_ = lean_ctor_get(v_toCold_1622_, 0);
v_fileMap_1625_ = lean_ctor_get(v_toCold_1622_, 1);
v___x_1626_ = lean_box(0);
v___x_1627_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_1628_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_1629_ = l_Lean_MessageData_nil;
v___x_1630_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1621_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
lean_ctor_set(v___x_1630_, 2, v_snd_1608_);
if (v_isShared_1616_ == 0)
{
lean_ctor_set_tag(v___x_1615_, 8);
lean_ctor_set(v___x_1615_, 1, v___x_1630_);
lean_ctor_set(v___x_1615_, 0, v___x_1628_);
v___x_1632_ = v___x_1615_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1628_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v___x_1630_);
v___x_1632_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
uint8_t v___x_1633_; lean_object* v___x_1634_; lean_object* v___y_1636_; lean_object* v___y_1637_; 
v___x_1633_ = 0;
lean_inc_ref(v_fileMap_1625_);
lean_inc_ref(v_fileName_1624_);
v___x_1634_ = l_Lean_Elab_mkMessageCore(v_fileName_1624_, v_fileMap_1625_, v___x_1632_, v___x_1633_, v_fst_1612_, v_snd_1613_);
lean_dec(v_snd_1613_);
lean_dec(v_fst_1612_);
if (v_suppressElabErrors_1623_ == 0)
{
v___y_1636_ = v___y_1596_;
v___y_1637_ = v___y_1597_;
goto v___jp_1635_;
}
else
{
lean_object* v_data_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___f_1683_; uint8_t v___x_1684_; 
v_data_1680_ = lean_ctor_get(v___x_1634_, 4);
v___x_1681_ = lean_box(v_suppressElabErrors_1623_);
v___x_1682_ = lean_box(v___x_1591_);
v___f_1683_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1683_, 0, v___x_1681_);
lean_closure_set(v___f_1683_, 1, v___x_1682_);
lean_closure_set(v___f_1683_, 2, v___x_1627_);
lean_inc(v_data_1680_);
v___x_1684_ = l_Lean_MessageData_hasTag(v___f_1683_, v_data_1680_);
if (v___x_1684_ == 0)
{
lean_dec_ref(v___x_1634_);
lean_del_object(v___x_1610_);
v_a_1600_ = v___x_1626_;
goto v___jp_1599_;
}
else
{
v___y_1636_ = v___y_1596_;
v___y_1637_ = v___y_1597_;
goto v___jp_1635_;
}
}
v___jp_1635_:
{
lean_object* v_toCold_1638_; lean_object* v_fileName_1639_; lean_object* v_pos_1640_; lean_object* v_endPos_1641_; uint8_t v_keepFullRange_1642_; uint8_t v_severity_1643_; uint8_t v_isSilent_1644_; lean_object* v_caption_1645_; lean_object* v_data_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1679_; 
v_toCold_1638_ = lean_ctor_get(v___y_1636_, 0);
v_fileName_1639_ = lean_ctor_get(v___x_1634_, 0);
v_pos_1640_ = lean_ctor_get(v___x_1634_, 1);
v_endPos_1641_ = lean_ctor_get(v___x_1634_, 2);
v_keepFullRange_1642_ = lean_ctor_get_uint8(v___x_1634_, sizeof(void*)*5);
v_severity_1643_ = lean_ctor_get_uint8(v___x_1634_, sizeof(void*)*5 + 1);
v_isSilent_1644_ = lean_ctor_get_uint8(v___x_1634_, sizeof(void*)*5 + 2);
v_caption_1645_ = lean_ctor_get(v___x_1634_, 3);
v_data_1646_ = lean_ctor_get(v___x_1634_, 4);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1648_ = v___x_1634_;
v_isShared_1649_ = v_isSharedCheck_1679_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_data_1646_);
lean_inc(v_caption_1645_);
lean_inc(v_endPos_1641_);
lean_inc(v_pos_1640_);
lean_inc(v_fileName_1639_);
lean_dec(v___x_1634_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1679_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v_currNamespace_1650_; lean_object* v_openDecls_1651_; lean_object* v___x_1653_; 
v_currNamespace_1650_ = lean_ctor_get(v_toCold_1638_, 4);
v_openDecls_1651_ = lean_ctor_get(v_toCold_1638_, 5);
lean_inc(v_openDecls_1651_);
lean_inc(v_currNamespace_1650_);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 1, v_openDecls_1651_);
lean_ctor_set(v___x_1610_, 0, v_currNamespace_1650_);
v___x_1653_ = v___x_1610_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_currNamespace_1650_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v_openDecls_1651_);
v___x_1653_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1654_; lean_object* v___x_1656_; 
v___x_1654_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
lean_ctor_set(v___x_1654_, 1, v_data_1646_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 4, v___x_1654_);
v___x_1656_ = v___x_1648_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_fileName_1639_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v_pos_1640_);
lean_ctor_set(v_reuseFailAlloc_1677_, 2, v_endPos_1641_);
lean_ctor_set(v_reuseFailAlloc_1677_, 3, v_caption_1645_);
lean_ctor_set(v_reuseFailAlloc_1677_, 4, v___x_1654_);
lean_ctor_set_uint8(v_reuseFailAlloc_1677_, sizeof(void*)*5, v_keepFullRange_1642_);
lean_ctor_set_uint8(v_reuseFailAlloc_1677_, sizeof(void*)*5 + 1, v_severity_1643_);
lean_ctor_set_uint8(v_reuseFailAlloc_1677_, sizeof(void*)*5 + 2, v_isSilent_1644_);
v___x_1656_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
lean_object* v___x_1657_; lean_object* v_env_1658_; lean_object* v_nextMacroScope_1659_; lean_object* v_ngen_1660_; lean_object* v_auxDeclNGen_1661_; lean_object* v_traceState_1662_; lean_object* v_cache_1663_; lean_object* v_recordedDeps_1664_; lean_object* v_messages_1665_; lean_object* v_infoState_1666_; lean_object* v_snapshotTasks_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1676_; 
v___x_1657_ = lean_st_ref_take(v___y_1637_);
v_env_1658_ = lean_ctor_get(v___x_1657_, 0);
v_nextMacroScope_1659_ = lean_ctor_get(v___x_1657_, 1);
v_ngen_1660_ = lean_ctor_get(v___x_1657_, 2);
v_auxDeclNGen_1661_ = lean_ctor_get(v___x_1657_, 3);
v_traceState_1662_ = lean_ctor_get(v___x_1657_, 4);
v_cache_1663_ = lean_ctor_get(v___x_1657_, 5);
v_recordedDeps_1664_ = lean_ctor_get(v___x_1657_, 6);
v_messages_1665_ = lean_ctor_get(v___x_1657_, 7);
v_infoState_1666_ = lean_ctor_get(v___x_1657_, 8);
v_snapshotTasks_1667_ = lean_ctor_get(v___x_1657_, 9);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1669_ = v___x_1657_;
v_isShared_1670_ = v_isSharedCheck_1676_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_snapshotTasks_1667_);
lean_inc(v_infoState_1666_);
lean_inc(v_messages_1665_);
lean_inc(v_recordedDeps_1664_);
lean_inc(v_cache_1663_);
lean_inc(v_traceState_1662_);
lean_inc(v_auxDeclNGen_1661_);
lean_inc(v_ngen_1660_);
lean_inc(v_nextMacroScope_1659_);
lean_inc(v_env_1658_);
lean_dec(v___x_1657_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1676_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1671_; lean_object* v___x_1673_; 
v___x_1671_ = l_Lean_MessageLog_add(v___x_1656_, v_messages_1665_);
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 7, v___x_1671_);
v___x_1673_ = v___x_1669_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_env_1658_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_nextMacroScope_1659_);
lean_ctor_set(v_reuseFailAlloc_1675_, 2, v_ngen_1660_);
lean_ctor_set(v_reuseFailAlloc_1675_, 3, v_auxDeclNGen_1661_);
lean_ctor_set(v_reuseFailAlloc_1675_, 4, v_traceState_1662_);
lean_ctor_set(v_reuseFailAlloc_1675_, 5, v_cache_1663_);
lean_ctor_set(v_reuseFailAlloc_1675_, 6, v_recordedDeps_1664_);
lean_ctor_set(v_reuseFailAlloc_1675_, 7, v___x_1671_);
lean_ctor_set(v_reuseFailAlloc_1675_, 8, v_infoState_1666_);
lean_ctor_set(v_reuseFailAlloc_1675_, 9, v_snapshotTasks_1667_);
v___x_1673_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
lean_object* v___x_1674_; 
v___x_1674_ = lean_st_ref_put(v___y_1637_, v___x_1673_);
v_a_1600_ = v___x_1626_;
goto v___jp_1599_;
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
v___jp_1599_:
{
size_t v___x_1601_; size_t v___x_1602_; 
v___x_1601_ = ((size_t)1ULL);
v___x_1602_ = lean_usize_add(v_i_1594_, v___x_1601_);
v_i_1594_ = v___x_1602_;
v_b_1595_ = v_a_1600_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___boxed(lean_object* v___x_1688_, lean_object* v_as_1689_, lean_object* v_sz_1690_, lean_object* v_i_1691_, lean_object* v_b_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
uint8_t v___x_38680__boxed_1696_; size_t v_sz_boxed_1697_; size_t v_i_boxed_1698_; lean_object* v_res_1699_; 
v___x_38680__boxed_1696_ = lean_unbox(v___x_1688_);
v_sz_boxed_1697_ = lean_unbox_usize(v_sz_1690_);
lean_dec(v_sz_1690_);
v_i_boxed_1698_ = lean_unbox_usize(v_i_1691_);
lean_dec(v_i_1691_);
v_res_1699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(v___x_38680__boxed_1696_, v_as_1689_, v_sz_boxed_1697_, v_i_boxed_1698_, v_b_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec_ref(v_as_1689_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(lean_object* v_a_1700_, lean_object* v_fallback_1701_, lean_object* v_x_1702_){
_start:
{
if (lean_obj_tag(v_x_1702_) == 0)
{
lean_inc(v_fallback_1701_);
return v_fallback_1701_;
}
else
{
lean_object* v_key_1703_; lean_object* v_value_1704_; lean_object* v_tail_1705_; lean_object* v_fst_1706_; lean_object* v_snd_1707_; lean_object* v_fst_1708_; lean_object* v_snd_1709_; uint8_t v_decide_1710_; 
v_key_1703_ = lean_ctor_get(v_x_1702_, 0);
v_value_1704_ = lean_ctor_get(v_x_1702_, 1);
v_tail_1705_ = lean_ctor_get(v_x_1702_, 2);
v_fst_1706_ = lean_ctor_get(v_key_1703_, 0);
v_snd_1707_ = lean_ctor_get(v_key_1703_, 1);
v_fst_1708_ = lean_ctor_get(v_a_1700_, 0);
v_snd_1709_ = lean_ctor_get(v_a_1700_, 1);
v_decide_1710_ = lean_nat_dec_eq(v_fst_1706_, v_fst_1708_);
if (v_decide_1710_ == 0)
{
v_x_1702_ = v_tail_1705_;
goto _start;
}
else
{
uint8_t v_decide_1712_; 
v_decide_1712_ = lean_nat_dec_eq(v_snd_1707_, v_snd_1709_);
if (v_decide_1712_ == 0)
{
v_x_1702_ = v_tail_1705_;
goto _start;
}
else
{
lean_inc(v_value_1704_);
return v_value_1704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg___boxed(lean_object* v_a_1714_, lean_object* v_fallback_1715_, lean_object* v_x_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(v_a_1714_, v_fallback_1715_, v_x_1716_);
lean_dec(v_x_1716_);
lean_dec(v_fallback_1715_);
lean_dec_ref(v_a_1714_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(lean_object* v_m_1718_, lean_object* v_a_1719_, lean_object* v_fallback_1720_){
_start:
{
lean_object* v_buckets_1721_; lean_object* v_fst_1722_; lean_object* v_snd_1723_; lean_object* v___x_1724_; uint64_t v___x_1725_; uint64_t v___x_1726_; uint64_t v___x_1727_; uint64_t v___x_1728_; uint64_t v___x_1729_; uint64_t v_fold_1730_; uint64_t v___x_1731_; uint64_t v___x_1732_; uint64_t v___x_1733_; size_t v___x_1734_; size_t v___x_1735_; size_t v___x_1736_; size_t v___x_1737_; size_t v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v_buckets_1721_ = lean_ctor_get(v_m_1718_, 1);
v_fst_1722_ = lean_ctor_get(v_a_1719_, 0);
v_snd_1723_ = lean_ctor_get(v_a_1719_, 1);
v___x_1724_ = lean_array_get_size(v_buckets_1721_);
v___x_1725_ = l_String_instHashableRaw_hash(v_fst_1722_);
v___x_1726_ = l_String_instHashableRaw_hash(v_snd_1723_);
v___x_1727_ = lean_uint64_mix_hash(v___x_1725_, v___x_1726_);
v___x_1728_ = 32ULL;
v___x_1729_ = lean_uint64_shift_right(v___x_1727_, v___x_1728_);
v_fold_1730_ = lean_uint64_xor(v___x_1727_, v___x_1729_);
v___x_1731_ = 16ULL;
v___x_1732_ = lean_uint64_shift_right(v_fold_1730_, v___x_1731_);
v___x_1733_ = lean_uint64_xor(v_fold_1730_, v___x_1732_);
v___x_1734_ = lean_uint64_to_usize(v___x_1733_);
v___x_1735_ = lean_usize_of_nat(v___x_1724_);
v___x_1736_ = ((size_t)1ULL);
v___x_1737_ = lean_usize_sub(v___x_1735_, v___x_1736_);
v___x_1738_ = lean_usize_land(v___x_1734_, v___x_1737_);
v___x_1739_ = lean_array_uget_borrowed(v_buckets_1721_, v___x_1738_);
v___x_1740_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(v_a_1719_, v_fallback_1720_, v___x_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg___boxed(lean_object* v_m_1741_, lean_object* v_a_1742_, lean_object* v_fallback_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_m_1741_, v_a_1742_, v_fallback_1743_);
lean_dec(v_fallback_1743_);
lean_dec_ref(v_a_1742_);
lean_dec_ref(v_m_1741_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44___redArg(lean_object* v_x_1745_, lean_object* v_x_1746_){
_start:
{
if (lean_obj_tag(v_x_1746_) == 0)
{
return v_x_1745_;
}
else
{
lean_object* v_key_1747_; lean_object* v_value_1748_; lean_object* v_tail_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1776_; 
v_key_1747_ = lean_ctor_get(v_x_1746_, 0);
v_value_1748_ = lean_ctor_get(v_x_1746_, 1);
v_tail_1749_ = lean_ctor_get(v_x_1746_, 2);
v_isSharedCheck_1776_ = !lean_is_exclusive(v_x_1746_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1751_ = v_x_1746_;
v_isShared_1752_ = v_isSharedCheck_1776_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_tail_1749_);
lean_inc(v_value_1748_);
lean_inc(v_key_1747_);
lean_dec(v_x_1746_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1776_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v_fst_1753_; lean_object* v_snd_1754_; lean_object* v___x_1755_; uint64_t v___x_1756_; uint64_t v___x_1757_; uint64_t v___x_1758_; uint64_t v___x_1759_; uint64_t v___x_1760_; uint64_t v_fold_1761_; uint64_t v___x_1762_; uint64_t v___x_1763_; uint64_t v___x_1764_; size_t v___x_1765_; size_t v___x_1766_; size_t v___x_1767_; size_t v___x_1768_; size_t v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1772_; 
v_fst_1753_ = lean_ctor_get(v_key_1747_, 0);
v_snd_1754_ = lean_ctor_get(v_key_1747_, 1);
v___x_1755_ = lean_array_get_size(v_x_1745_);
v___x_1756_ = l_String_instHashableRaw_hash(v_fst_1753_);
v___x_1757_ = l_String_instHashableRaw_hash(v_snd_1754_);
v___x_1758_ = lean_uint64_mix_hash(v___x_1756_, v___x_1757_);
v___x_1759_ = 32ULL;
v___x_1760_ = lean_uint64_shift_right(v___x_1758_, v___x_1759_);
v_fold_1761_ = lean_uint64_xor(v___x_1758_, v___x_1760_);
v___x_1762_ = 16ULL;
v___x_1763_ = lean_uint64_shift_right(v_fold_1761_, v___x_1762_);
v___x_1764_ = lean_uint64_xor(v_fold_1761_, v___x_1763_);
v___x_1765_ = lean_uint64_to_usize(v___x_1764_);
v___x_1766_ = lean_usize_of_nat(v___x_1755_);
v___x_1767_ = ((size_t)1ULL);
v___x_1768_ = lean_usize_sub(v___x_1766_, v___x_1767_);
v___x_1769_ = lean_usize_land(v___x_1765_, v___x_1768_);
v___x_1770_ = lean_array_uget_borrowed(v_x_1745_, v___x_1769_);
lean_inc(v___x_1770_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 2, v___x_1770_);
v___x_1772_ = v___x_1751_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_key_1747_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v_value_1748_);
lean_ctor_set(v_reuseFailAlloc_1775_, 2, v___x_1770_);
v___x_1772_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1773_; 
v___x_1773_ = lean_array_uset(v_x_1745_, v___x_1769_, v___x_1772_);
v_x_1745_ = v___x_1773_;
v_x_1746_ = v_tail_1749_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35___redArg(lean_object* v_i_1777_, lean_object* v_source_1778_, lean_object* v_target_1779_){
_start:
{
lean_object* v___x_1780_; uint8_t v___x_1781_; 
v___x_1780_ = lean_array_get_size(v_source_1778_);
v___x_1781_ = lean_nat_dec_lt(v_i_1777_, v___x_1780_);
if (v___x_1781_ == 0)
{
lean_dec_ref(v_source_1778_);
lean_dec(v_i_1777_);
return v_target_1779_;
}
else
{
lean_object* v_es_1782_; lean_object* v___x_1783_; lean_object* v_source_1784_; lean_object* v_target_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v_es_1782_ = lean_array_fget(v_source_1778_, v_i_1777_);
v___x_1783_ = lean_box(0);
v_source_1784_ = lean_array_fset(v_source_1778_, v_i_1777_, v___x_1783_);
v_target_1785_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44___redArg(v_target_1779_, v_es_1782_);
v___x_1786_ = lean_unsigned_to_nat(1u);
v___x_1787_ = lean_nat_add(v_i_1777_, v___x_1786_);
lean_dec(v_i_1777_);
v_i_1777_ = v___x_1787_;
v_source_1778_ = v_source_1784_;
v_target_1779_ = v_target_1785_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24___redArg(lean_object* v_data_1789_){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v_nbuckets_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1790_ = lean_array_get_size(v_data_1789_);
v___x_1791_ = lean_unsigned_to_nat(2u);
v_nbuckets_1792_ = lean_nat_mul(v___x_1790_, v___x_1791_);
v___x_1793_ = lean_unsigned_to_nat(0u);
v___x_1794_ = lean_box(0);
v___x_1795_ = lean_mk_array(v_nbuckets_1792_, v___x_1794_);
v___x_1796_ = lean_array_propagate_mark(v_data_1789_, v___x_1795_);
v___x_1797_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35___redArg(v___x_1793_, v_data_1789_, v___x_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(lean_object* v_a_1798_, lean_object* v_b_1799_, lean_object* v_x_1800_){
_start:
{
if (lean_obj_tag(v_x_1800_) == 0)
{
lean_dec(v_b_1799_);
lean_dec_ref(v_a_1798_);
return v_x_1800_;
}
else
{
lean_object* v_key_1801_; lean_object* v_value_1802_; lean_object* v_tail_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1819_; 
v_key_1801_ = lean_ctor_get(v_x_1800_, 0);
v_value_1802_ = lean_ctor_get(v_x_1800_, 1);
v_tail_1803_ = lean_ctor_get(v_x_1800_, 2);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_x_1800_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1805_ = v_x_1800_;
v_isShared_1806_ = v_isSharedCheck_1819_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_tail_1803_);
lean_inc(v_value_1802_);
lean_inc(v_key_1801_);
lean_dec(v_x_1800_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1819_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v_fst_1812_; lean_object* v_snd_1813_; lean_object* v_fst_1814_; lean_object* v_snd_1815_; uint8_t v_decide_1816_; 
v_fst_1812_ = lean_ctor_get(v_key_1801_, 0);
v_snd_1813_ = lean_ctor_get(v_key_1801_, 1);
v_fst_1814_ = lean_ctor_get(v_a_1798_, 0);
v_snd_1815_ = lean_ctor_get(v_a_1798_, 1);
v_decide_1816_ = lean_nat_dec_eq(v_fst_1812_, v_fst_1814_);
if (v_decide_1816_ == 0)
{
goto v___jp_1807_;
}
else
{
uint8_t v_decide_1817_; 
v_decide_1817_ = lean_nat_dec_eq(v_snd_1813_, v_snd_1815_);
if (v_decide_1817_ == 0)
{
goto v___jp_1807_;
}
else
{
lean_object* v___x_1818_; 
lean_del_object(v___x_1805_);
lean_dec(v_value_1802_);
lean_dec(v_key_1801_);
v___x_1818_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1818_, 0, v_a_1798_);
lean_ctor_set(v___x_1818_, 1, v_b_1799_);
lean_ctor_set(v___x_1818_, 2, v_tail_1803_);
return v___x_1818_;
}
}
v___jp_1807_:
{
lean_object* v___x_1808_; lean_object* v___x_1810_; 
v___x_1808_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(v_a_1798_, v_b_1799_, v_tail_1803_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 2, v___x_1808_);
v___x_1810_ = v___x_1805_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_key_1801_);
lean_ctor_set(v_reuseFailAlloc_1811_, 1, v_value_1802_);
lean_ctor_set(v_reuseFailAlloc_1811_, 2, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(lean_object* v_a_1820_, lean_object* v_x_1821_){
_start:
{
if (lean_obj_tag(v_x_1821_) == 0)
{
uint8_t v___x_1822_; 
v___x_1822_ = 0;
return v___x_1822_;
}
else
{
lean_object* v_key_1823_; lean_object* v_tail_1824_; lean_object* v_fst_1825_; lean_object* v_snd_1826_; lean_object* v_fst_1827_; lean_object* v_snd_1828_; uint8_t v_decide_1829_; 
v_key_1823_ = lean_ctor_get(v_x_1821_, 0);
v_tail_1824_ = lean_ctor_get(v_x_1821_, 2);
v_fst_1825_ = lean_ctor_get(v_key_1823_, 0);
v_snd_1826_ = lean_ctor_get(v_key_1823_, 1);
v_fst_1827_ = lean_ctor_get(v_a_1820_, 0);
v_snd_1828_ = lean_ctor_get(v_a_1820_, 1);
v_decide_1829_ = lean_nat_dec_eq(v_fst_1825_, v_fst_1827_);
if (v_decide_1829_ == 0)
{
v_x_1821_ = v_tail_1824_;
goto _start;
}
else
{
uint8_t v_decide_1831_; 
v_decide_1831_ = lean_nat_dec_eq(v_snd_1826_, v_snd_1828_);
if (v_decide_1831_ == 0)
{
v_x_1821_ = v_tail_1824_;
goto _start;
}
else
{
return v_decide_1831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg___boxed(lean_object* v_a_1833_, lean_object* v_x_1834_){
_start:
{
uint8_t v_res_1835_; lean_object* v_r_1836_; 
v_res_1835_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(v_a_1833_, v_x_1834_);
lean_dec(v_x_1834_);
lean_dec_ref(v_a_1833_);
v_r_1836_ = lean_box(v_res_1835_);
return v_r_1836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(lean_object* v_m_1837_, lean_object* v_a_1838_, lean_object* v_b_1839_){
_start:
{
lean_object* v_size_1840_; lean_object* v_buckets_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1888_; 
v_size_1840_ = lean_ctor_get(v_m_1837_, 0);
v_buckets_1841_ = lean_ctor_get(v_m_1837_, 1);
v_isSharedCheck_1888_ = !lean_is_exclusive(v_m_1837_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1843_ = v_m_1837_;
v_isShared_1844_ = v_isSharedCheck_1888_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_buckets_1841_);
lean_inc(v_size_1840_);
lean_dec(v_m_1837_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1888_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v_fst_1845_; lean_object* v_snd_1846_; lean_object* v___x_1847_; uint64_t v___x_1848_; uint64_t v___x_1849_; uint64_t v___x_1850_; uint64_t v___x_1851_; uint64_t v___x_1852_; uint64_t v_fold_1853_; uint64_t v___x_1854_; uint64_t v___x_1855_; uint64_t v___x_1856_; size_t v___x_1857_; size_t v___x_1858_; size_t v___x_1859_; size_t v___x_1860_; size_t v___x_1861_; lean_object* v_bkt_1862_; uint8_t v___x_1863_; 
v_fst_1845_ = lean_ctor_get(v_a_1838_, 0);
v_snd_1846_ = lean_ctor_get(v_a_1838_, 1);
v___x_1847_ = lean_array_get_size(v_buckets_1841_);
v___x_1848_ = l_String_instHashableRaw_hash(v_fst_1845_);
v___x_1849_ = l_String_instHashableRaw_hash(v_snd_1846_);
v___x_1850_ = lean_uint64_mix_hash(v___x_1848_, v___x_1849_);
v___x_1851_ = 32ULL;
v___x_1852_ = lean_uint64_shift_right(v___x_1850_, v___x_1851_);
v_fold_1853_ = lean_uint64_xor(v___x_1850_, v___x_1852_);
v___x_1854_ = 16ULL;
v___x_1855_ = lean_uint64_shift_right(v_fold_1853_, v___x_1854_);
v___x_1856_ = lean_uint64_xor(v_fold_1853_, v___x_1855_);
v___x_1857_ = lean_uint64_to_usize(v___x_1856_);
v___x_1858_ = lean_usize_of_nat(v___x_1847_);
v___x_1859_ = ((size_t)1ULL);
v___x_1860_ = lean_usize_sub(v___x_1858_, v___x_1859_);
v___x_1861_ = lean_usize_land(v___x_1857_, v___x_1860_);
v_bkt_1862_ = lean_array_uget_borrowed(v_buckets_1841_, v___x_1861_);
v___x_1863_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(v_a_1838_, v_bkt_1862_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; lean_object* v_size_x27_1865_; lean_object* v___x_1866_; lean_object* v_buckets_x27_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; uint8_t v___x_1873_; 
v___x_1864_ = lean_unsigned_to_nat(1u);
v_size_x27_1865_ = lean_nat_add(v_size_1840_, v___x_1864_);
lean_dec(v_size_1840_);
lean_inc(v_bkt_1862_);
v___x_1866_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1866_, 0, v_a_1838_);
lean_ctor_set(v___x_1866_, 1, v_b_1839_);
lean_ctor_set(v___x_1866_, 2, v_bkt_1862_);
v_buckets_x27_1867_ = lean_array_uset(v_buckets_1841_, v___x_1861_, v___x_1866_);
v___x_1868_ = lean_unsigned_to_nat(4u);
v___x_1869_ = lean_nat_mul(v_size_x27_1865_, v___x_1868_);
v___x_1870_ = lean_unsigned_to_nat(3u);
v___x_1871_ = lean_nat_div(v___x_1869_, v___x_1870_);
lean_dec(v___x_1869_);
v___x_1872_ = lean_array_get_size(v_buckets_x27_1867_);
v___x_1873_ = lean_nat_dec_le(v___x_1871_, v___x_1872_);
lean_dec(v___x_1871_);
if (v___x_1873_ == 0)
{
lean_object* v_val_1874_; lean_object* v___x_1876_; 
v_val_1874_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24___redArg(v_buckets_x27_1867_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 1, v_val_1874_);
lean_ctor_set(v___x_1843_, 0, v_size_x27_1865_);
v___x_1876_ = v___x_1843_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_size_x27_1865_);
lean_ctor_set(v_reuseFailAlloc_1877_, 1, v_val_1874_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
else
{
lean_object* v___x_1879_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 1, v_buckets_x27_1867_);
lean_ctor_set(v___x_1843_, 0, v_size_x27_1865_);
v___x_1879_ = v___x_1843_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_size_x27_1865_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v_buckets_x27_1867_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
else
{
lean_object* v___x_1881_; lean_object* v_buckets_x27_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1886_; 
lean_inc(v_bkt_1862_);
v___x_1881_ = lean_box(0);
v_buckets_x27_1882_ = lean_array_uset(v_buckets_1841_, v___x_1861_, v___x_1881_);
v___x_1883_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(v_a_1838_, v_b_1839_, v_bkt_1862_);
v___x_1884_ = lean_array_uset(v_buckets_x27_1882_, v___x_1861_, v___x_1883_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 1, v___x_1884_);
v___x_1886_ = v___x_1843_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_size_1840_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v___x_1884_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(uint8_t v___x_1891_, lean_object* v_as_1892_, size_t v_sz_1893_, size_t v_i_1894_, lean_object* v_b_1895_, lean_object* v___y_1896_){
_start:
{
uint8_t v___x_1898_; 
v___x_1898_ = lean_usize_dec_lt(v_i_1894_, v_sz_1893_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; 
v___x_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1899_, 0, v_b_1895_);
return v___x_1899_;
}
else
{
lean_object* v_snd_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1937_; 
v_snd_1900_ = lean_ctor_get(v_b_1895_, 1);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_b_1895_);
if (v_isSharedCheck_1937_ == 0)
{
lean_object* v_unused_1938_; 
v_unused_1938_ = lean_ctor_get(v_b_1895_, 0);
lean_dec(v_unused_1938_);
v___x_1902_ = v_b_1895_;
v_isShared_1903_ = v_isSharedCheck_1937_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_snd_1900_);
lean_dec(v_b_1895_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1937_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v_ref_1904_; lean_object* v_a_1905_; lean_object* v_ref_1906_; lean_object* v_msg_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1936_; 
v_ref_1904_ = lean_ctor_get(v___y_1896_, 2);
v_a_1905_ = lean_array_uget(v_as_1892_, v_i_1894_);
v_ref_1906_ = lean_ctor_get(v_a_1905_, 0);
v_msg_1907_ = lean_ctor_get(v_a_1905_, 1);
v_isSharedCheck_1936_ = !lean_is_exclusive(v_a_1905_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1909_ = v_a_1905_;
v_isShared_1910_ = v_isSharedCheck_1936_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_msg_1907_);
lean_inc(v_ref_1906_);
lean_dec(v_a_1905_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1936_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1911_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v_ref_1928_; lean_object* v___y_1930_; lean_object* v___x_1933_; 
v___x_1911_ = lean_box(0);
v_ref_1928_ = l_Lean_replaceRef(v_ref_1906_, v_ref_1904_);
lean_dec(v_ref_1906_);
v___x_1933_ = l_Lean_Syntax_getPos_x3f(v_ref_1928_, v___x_1891_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v___x_1934_; 
v___x_1934_ = lean_unsigned_to_nat(0u);
v___y_1930_ = v___x_1934_;
goto v___jp_1929_;
}
else
{
lean_object* v_val_1935_; 
v_val_1935_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_val_1935_);
lean_dec_ref_known(v___x_1933_, 1);
v___y_1930_ = v_val_1935_;
goto v___jp_1929_;
}
v___jp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 1, v___y_1914_);
lean_ctor_set(v___x_1902_, 0, v___y_1913_);
v___x_1916_ = v___x_1902_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___y_1913_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v___y_1914_);
v___x_1916_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v_pos2traces_1920_; lean_object* v___x_1922_; 
v___x_1917_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1918_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1900_, v___x_1916_, v___x_1917_);
v___x_1919_ = lean_array_push(v___x_1918_, v_msg_1907_);
v_pos2traces_1920_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_1900_, v___x_1916_, v___x_1919_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 1, v_pos2traces_1920_);
lean_ctor_set(v___x_1909_, 0, v___x_1911_);
v___x_1922_ = v___x_1909_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1911_);
lean_ctor_set(v_reuseFailAlloc_1926_, 1, v_pos2traces_1920_);
v___x_1922_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
size_t v___x_1923_; size_t v___x_1924_; 
v___x_1923_ = ((size_t)1ULL);
v___x_1924_ = lean_usize_add(v_i_1894_, v___x_1923_);
v_i_1894_ = v___x_1924_;
v_b_1895_ = v___x_1922_;
goto _start;
}
}
}
v___jp_1929_:
{
lean_object* v___x_1931_; 
v___x_1931_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1928_, v___x_1891_);
lean_dec(v_ref_1928_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_inc(v___y_1930_);
v___y_1913_ = v___y_1930_;
v___y_1914_ = v___y_1930_;
goto v___jp_1912_;
}
else
{
lean_object* v_val_1932_; 
v_val_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_val_1932_);
lean_dec_ref_known(v___x_1931_, 1);
v___y_1913_ = v___y_1930_;
v___y_1914_ = v_val_1932_;
goto v___jp_1912_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___boxed(lean_object* v___x_1939_, lean_object* v_as_1940_, lean_object* v_sz_1941_, lean_object* v_i_1942_, lean_object* v_b_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
uint8_t v___x_39126__boxed_1946_; size_t v_sz_boxed_1947_; size_t v_i_boxed_1948_; lean_object* v_res_1949_; 
v___x_39126__boxed_1946_ = lean_unbox(v___x_1939_);
v_sz_boxed_1947_ = lean_unbox_usize(v_sz_1941_);
lean_dec(v_sz_1941_);
v_i_boxed_1948_ = lean_unbox_usize(v_i_1942_);
lean_dec(v_i_1942_);
v_res_1949_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(v___x_39126__boxed_1946_, v_as_1940_, v_sz_boxed_1947_, v_i_boxed_1948_, v_b_1943_, v___y_1944_);
lean_dec_ref(v___y_1944_);
lean_dec_ref(v_as_1940_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40(uint8_t v___x_1950_, lean_object* v_as_1951_, size_t v_sz_1952_, size_t v_i_1953_, lean_object* v_b_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
uint8_t v___x_1958_; 
v___x_1958_ = lean_usize_dec_lt(v_i_1953_, v_sz_1952_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; 
v___x_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1959_, 0, v_b_1954_);
return v___x_1959_;
}
else
{
lean_object* v_snd_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1997_; 
v_snd_1960_ = lean_ctor_get(v_b_1954_, 1);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_b_1954_);
if (v_isSharedCheck_1997_ == 0)
{
lean_object* v_unused_1998_; 
v_unused_1998_ = lean_ctor_get(v_b_1954_, 0);
lean_dec(v_unused_1998_);
v___x_1962_ = v_b_1954_;
v_isShared_1963_ = v_isSharedCheck_1997_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_snd_1960_);
lean_dec(v_b_1954_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1997_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v_ref_1964_; lean_object* v_a_1965_; lean_object* v_ref_1966_; lean_object* v_msg_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1996_; 
v_ref_1964_ = lean_ctor_get(v___y_1955_, 2);
v_a_1965_ = lean_array_uget(v_as_1951_, v_i_1953_);
v_ref_1966_ = lean_ctor_get(v_a_1965_, 0);
v_msg_1967_ = lean_ctor_get(v_a_1965_, 1);
v_isSharedCheck_1996_ = !lean_is_exclusive(v_a_1965_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1969_ = v_a_1965_;
v_isShared_1970_ = v_isSharedCheck_1996_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_msg_1967_);
lean_inc(v_ref_1966_);
lean_dec(v_a_1965_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1996_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1971_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v_ref_1988_; lean_object* v___y_1990_; lean_object* v___x_1993_; 
v___x_1971_ = lean_box(0);
v_ref_1988_ = l_Lean_replaceRef(v_ref_1966_, v_ref_1964_);
lean_dec(v_ref_1966_);
v___x_1993_ = l_Lean_Syntax_getPos_x3f(v_ref_1988_, v___x_1950_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v___x_1994_; 
v___x_1994_ = lean_unsigned_to_nat(0u);
v___y_1990_ = v___x_1994_;
goto v___jp_1989_;
}
else
{
lean_object* v_val_1995_; 
v_val_1995_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_val_1995_);
lean_dec_ref_known(v___x_1993_, 1);
v___y_1990_ = v_val_1995_;
goto v___jp_1989_;
}
v___jp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 1, v___y_1974_);
lean_ctor_set(v___x_1962_, 0, v___y_1973_);
v___x_1976_ = v___x_1962_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___y_1973_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v___y_1974_);
v___x_1976_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v_pos2traces_1980_; lean_object* v___x_1982_; 
v___x_1977_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1978_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1960_, v___x_1976_, v___x_1977_);
v___x_1979_ = lean_array_push(v___x_1978_, v_msg_1967_);
v_pos2traces_1980_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_1960_, v___x_1976_, v___x_1979_);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 1, v_pos2traces_1980_);
lean_ctor_set(v___x_1969_, 0, v___x_1971_);
v___x_1982_ = v___x_1969_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1971_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_pos2traces_1980_);
v___x_1982_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
size_t v___x_1983_; size_t v___x_1984_; lean_object* v___x_1985_; 
v___x_1983_ = ((size_t)1ULL);
v___x_1984_ = lean_usize_add(v_i_1953_, v___x_1983_);
v___x_1985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(v___x_1950_, v_as_1951_, v_sz_1952_, v___x_1984_, v___x_1982_, v___y_1955_);
return v___x_1985_;
}
}
}
v___jp_1989_:
{
lean_object* v___x_1991_; 
v___x_1991_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1988_, v___x_1950_);
lean_dec(v_ref_1988_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_inc(v___y_1990_);
v___y_1973_ = v___y_1990_;
v___y_1974_ = v___y_1990_;
goto v___jp_1972_;
}
else
{
lean_object* v_val_1992_; 
v_val_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_val_1992_);
lean_dec_ref_known(v___x_1991_, 1);
v___y_1973_ = v___y_1990_;
v___y_1974_ = v_val_1992_;
goto v___jp_1972_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40___boxed(lean_object* v___x_1999_, lean_object* v_as_2000_, lean_object* v_sz_2001_, lean_object* v_i_2002_, lean_object* v_b_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
uint8_t v___x_39207__boxed_2007_; size_t v_sz_boxed_2008_; size_t v_i_boxed_2009_; lean_object* v_res_2010_; 
v___x_39207__boxed_2007_ = lean_unbox(v___x_1999_);
v_sz_boxed_2008_ = lean_unbox_usize(v_sz_2001_);
lean_dec(v_sz_2001_);
v_i_boxed_2009_ = lean_unbox_usize(v_i_2002_);
lean_dec(v_i_2002_);
v_res_2010_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40(v___x_39207__boxed_2007_, v_as_2000_, v_sz_boxed_2008_, v_i_boxed_2009_, v_b_2003_, v___y_2004_, v___y_2005_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec_ref(v_as_2000_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(lean_object* v_init_2011_, uint8_t v___x_2012_, lean_object* v_n_2013_, lean_object* v_b_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
if (lean_obj_tag(v_n_2013_) == 0)
{
lean_object* v_cs_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; size_t v_sz_2021_; size_t v___x_2022_; lean_object* v___x_2023_; 
v_cs_2018_ = lean_ctor_get(v_n_2013_, 0);
v___x_2019_ = lean_box(0);
v___x_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
lean_ctor_set(v___x_2020_, 1, v_b_2014_);
v_sz_2021_ = lean_array_size(v_cs_2018_);
v___x_2022_ = ((size_t)0ULL);
v___x_2023_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39(v_init_2011_, v___x_2012_, v_cs_2018_, v_sz_2021_, v___x_2022_, v___x_2020_, v___y_2015_, v___y_2016_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2038_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2026_ = v___x_2023_;
v_isShared_2027_ = v_isSharedCheck_2038_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2038_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v_fst_2028_; 
v_fst_2028_ = lean_ctor_get(v_a_2024_, 0);
if (lean_obj_tag(v_fst_2028_) == 0)
{
lean_object* v_snd_2029_; lean_object* v___x_2030_; lean_object* v___x_2032_; 
v_snd_2029_ = lean_ctor_get(v_a_2024_, 1);
lean_inc(v_snd_2029_);
lean_dec(v_a_2024_);
v___x_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2030_, 0, v_snd_2029_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2030_);
v___x_2032_ = v___x_2026_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
else
{
lean_object* v_val_2034_; lean_object* v___x_2036_; 
lean_inc_ref(v_fst_2028_);
lean_dec(v_a_2024_);
v_val_2034_ = lean_ctor_get(v_fst_2028_, 0);
lean_inc(v_val_2034_);
lean_dec_ref_known(v_fst_2028_, 1);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v_val_2034_);
v___x_2036_ = v___x_2026_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_val_2034_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
v_a_2039_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2023_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2023_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
else
{
lean_object* v_vs_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; size_t v_sz_2050_; size_t v___x_2051_; lean_object* v___x_2052_; 
v_vs_2047_ = lean_ctor_get(v_n_2013_, 0);
v___x_2048_ = lean_box(0);
v___x_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
lean_ctor_set(v___x_2049_, 1, v_b_2014_);
v_sz_2050_ = lean_array_size(v_vs_2047_);
v___x_2051_ = ((size_t)0ULL);
v___x_2052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40(v___x_2012_, v_vs_2047_, v_sz_2050_, v___x_2051_, v___x_2049_, v___y_2015_, v___y_2016_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2067_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2055_ = v___x_2052_;
v_isShared_2056_ = v_isSharedCheck_2067_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2052_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2067_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v_fst_2057_; 
v_fst_2057_ = lean_ctor_get(v_a_2053_, 0);
if (lean_obj_tag(v_fst_2057_) == 0)
{
lean_object* v_snd_2058_; lean_object* v___x_2059_; lean_object* v___x_2061_; 
v_snd_2058_ = lean_ctor_get(v_a_2053_, 1);
lean_inc(v_snd_2058_);
lean_dec(v_a_2053_);
v___x_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2059_, 0, v_snd_2058_);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 0, v___x_2059_);
v___x_2061_ = v___x_2055_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2059_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
else
{
lean_object* v_val_2063_; lean_object* v___x_2065_; 
lean_inc_ref(v_fst_2057_);
lean_dec(v_a_2053_);
v_val_2063_ = lean_ctor_get(v_fst_2057_, 0);
lean_inc(v_val_2063_);
lean_dec_ref_known(v_fst_2057_, 1);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 0, v_val_2063_);
v___x_2065_ = v___x_2055_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_val_2063_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
v_a_2068_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2052_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2052_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39(lean_object* v_init_2076_, uint8_t v___x_2077_, lean_object* v_as_2078_, size_t v_sz_2079_, size_t v_i_2080_, lean_object* v_b_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
uint8_t v___x_2085_; 
v___x_2085_ = lean_usize_dec_lt(v_i_2080_, v_sz_2079_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; 
v___x_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2086_, 0, v_b_2081_);
return v___x_2086_;
}
else
{
lean_object* v_snd_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2121_; 
v_snd_2087_ = lean_ctor_get(v_b_2081_, 1);
v_isSharedCheck_2121_ = !lean_is_exclusive(v_b_2081_);
if (v_isSharedCheck_2121_ == 0)
{
lean_object* v_unused_2122_; 
v_unused_2122_ = lean_ctor_get(v_b_2081_, 0);
lean_dec(v_unused_2122_);
v___x_2089_ = v_b_2081_;
v_isShared_2090_ = v_isSharedCheck_2121_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_snd_2087_);
lean_dec(v_b_2081_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2121_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2091_; lean_object* v_a_2092_; lean_object* v___x_2093_; 
v___x_2091_ = lean_box(0);
v_a_2092_ = lean_array_uget_borrowed(v_as_2078_, v_i_2080_);
lean_inc(v_snd_2087_);
v___x_2093_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(v_init_2076_, v___x_2077_, v_a_2092_, v_snd_2087_, v___y_2082_, v___y_2083_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2112_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2096_ = v___x_2093_;
v_isShared_2097_ = v_isSharedCheck_2112_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2093_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2112_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
if (lean_obj_tag(v_a_2094_) == 0)
{
lean_object* v___x_2098_; lean_object* v___x_2100_; 
v___x_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2098_, 0, v_a_2094_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 0, v___x_2098_);
v___x_2100_ = v___x_2089_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v_snd_2087_);
v___x_2100_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2102_; 
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 0, v___x_2100_);
v___x_2102_ = v___x_2096_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; 
lean_del_object(v___x_2096_);
lean_dec(v_snd_2087_);
v_a_2105_ = lean_ctor_get(v_a_2094_, 0);
lean_inc(v_a_2105_);
lean_dec_ref_known(v_a_2094_, 1);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 1, v_a_2105_);
lean_ctor_set(v___x_2089_, 0, v___x_2091_);
v___x_2107_ = v___x_2089_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2091_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v_a_2105_);
v___x_2107_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
size_t v___x_2108_; size_t v___x_2109_; 
v___x_2108_ = ((size_t)1ULL);
v___x_2109_ = lean_usize_add(v_i_2080_, v___x_2108_);
v_i_2080_ = v___x_2109_;
v_b_2081_ = v___x_2107_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
lean_del_object(v___x_2089_);
lean_dec(v_snd_2087_);
v_a_2113_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___x_2093_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2093_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39___boxed(lean_object* v_init_2123_, lean_object* v___x_2124_, lean_object* v_as_2125_, lean_object* v_sz_2126_, lean_object* v_i_2127_, lean_object* v_b_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
uint8_t v___x_39288__boxed_2132_; size_t v_sz_boxed_2133_; size_t v_i_boxed_2134_; lean_object* v_res_2135_; 
v___x_39288__boxed_2132_ = lean_unbox(v___x_2124_);
v_sz_boxed_2133_ = lean_unbox_usize(v_sz_2126_);
lean_dec(v_sz_2126_);
v_i_boxed_2134_ = lean_unbox_usize(v_i_2127_);
lean_dec(v_i_2127_);
v_res_2135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39(v_init_2123_, v___x_39288__boxed_2132_, v_as_2125_, v_sz_boxed_2133_, v_i_boxed_2134_, v_b_2128_, v___y_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec_ref(v_as_2125_);
lean_dec_ref(v_init_2123_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27___boxed(lean_object* v_init_2136_, lean_object* v___x_2137_, lean_object* v_n_2138_, lean_object* v_b_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
uint8_t v___x_39308__boxed_2143_; lean_object* v_res_2144_; 
v___x_39308__boxed_2143_ = lean_unbox(v___x_2137_);
v_res_2144_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(v_init_2136_, v___x_39308__boxed_2143_, v_n_2138_, v_b_2139_, v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec_ref(v_n_2138_);
lean_dec_ref(v_init_2136_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(uint8_t v___x_2145_, lean_object* v_as_2146_, size_t v_sz_2147_, size_t v_i_2148_, lean_object* v_b_2149_, lean_object* v___y_2150_){
_start:
{
uint8_t v___x_2152_; 
v___x_2152_ = lean_usize_dec_lt(v_i_2148_, v_sz_2147_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; 
v___x_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2153_, 0, v_b_2149_);
return v___x_2153_;
}
else
{
lean_object* v_snd_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2191_; 
v_snd_2154_ = lean_ctor_get(v_b_2149_, 1);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_b_2149_);
if (v_isSharedCheck_2191_ == 0)
{
lean_object* v_unused_2192_; 
v_unused_2192_ = lean_ctor_get(v_b_2149_, 0);
lean_dec(v_unused_2192_);
v___x_2156_ = v_b_2149_;
v_isShared_2157_ = v_isSharedCheck_2191_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_snd_2154_);
lean_dec(v_b_2149_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2191_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v_ref_2158_; lean_object* v_a_2159_; lean_object* v_ref_2160_; lean_object* v_msg_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2190_; 
v_ref_2158_ = lean_ctor_get(v___y_2150_, 2);
v_a_2159_ = lean_array_uget(v_as_2146_, v_i_2148_);
v_ref_2160_ = lean_ctor_get(v_a_2159_, 0);
v_msg_2161_ = lean_ctor_get(v_a_2159_, 1);
v_isSharedCheck_2190_ = !lean_is_exclusive(v_a_2159_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2163_ = v_a_2159_;
v_isShared_2164_ = v_isSharedCheck_2190_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_msg_2161_);
lean_inc(v_ref_2160_);
lean_dec(v_a_2159_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2190_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2165_; lean_object* v___y_2167_; lean_object* v___y_2168_; lean_object* v_ref_2182_; lean_object* v___y_2184_; lean_object* v___x_2187_; 
v___x_2165_ = lean_box(0);
v_ref_2182_ = l_Lean_replaceRef(v_ref_2160_, v_ref_2158_);
lean_dec(v_ref_2160_);
v___x_2187_ = l_Lean_Syntax_getPos_x3f(v_ref_2182_, v___x_2145_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v___x_2188_; 
v___x_2188_ = lean_unsigned_to_nat(0u);
v___y_2184_ = v___x_2188_;
goto v___jp_2183_;
}
else
{
lean_object* v_val_2189_; 
v_val_2189_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_val_2189_);
lean_dec_ref_known(v___x_2187_, 1);
v___y_2184_ = v_val_2189_;
goto v___jp_2183_;
}
v___jp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 1, v___y_2168_);
lean_ctor_set(v___x_2156_, 0, v___y_2167_);
v___x_2170_ = v___x_2156_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___y_2167_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v___y_2168_);
v___x_2170_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v_pos2traces_2174_; lean_object* v___x_2176_; 
v___x_2171_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_2172_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_2154_, v___x_2170_, v___x_2171_);
v___x_2173_ = lean_array_push(v___x_2172_, v_msg_2161_);
v_pos2traces_2174_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_2154_, v___x_2170_, v___x_2173_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 1, v_pos2traces_2174_);
lean_ctor_set(v___x_2163_, 0, v___x_2165_);
v___x_2176_ = v___x_2163_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2165_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_pos2traces_2174_);
v___x_2176_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
size_t v___x_2177_; size_t v___x_2178_; 
v___x_2177_ = ((size_t)1ULL);
v___x_2178_ = lean_usize_add(v_i_2148_, v___x_2177_);
v_i_2148_ = v___x_2178_;
v_b_2149_ = v___x_2176_;
goto _start;
}
}
}
v___jp_2183_:
{
lean_object* v___x_2185_; 
v___x_2185_ = l_Lean_Syntax_getTailPos_x3f(v_ref_2182_, v___x_2145_);
lean_dec(v_ref_2182_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_inc(v___y_2184_);
v___y_2167_ = v___y_2184_;
v___y_2168_ = v___y_2184_;
goto v___jp_2166_;
}
else
{
lean_object* v_val_2186_; 
v_val_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_val_2186_);
lean_dec_ref_known(v___x_2185_, 1);
v___y_2167_ = v___y_2184_;
v___y_2168_ = v_val_2186_;
goto v___jp_2166_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg___boxed(lean_object* v___x_2193_, lean_object* v_as_2194_, lean_object* v_sz_2195_, lean_object* v_i_2196_, lean_object* v_b_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
uint8_t v___x_39491__boxed_2200_; size_t v_sz_boxed_2201_; size_t v_i_boxed_2202_; lean_object* v_res_2203_; 
v___x_39491__boxed_2200_ = lean_unbox(v___x_2193_);
v_sz_boxed_2201_ = lean_unbox_usize(v_sz_2195_);
lean_dec(v_sz_2195_);
v_i_boxed_2202_ = lean_unbox_usize(v_i_2196_);
lean_dec(v_i_2196_);
v_res_2203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(v___x_39491__boxed_2200_, v_as_2194_, v_sz_boxed_2201_, v_i_boxed_2202_, v_b_2197_, v___y_2198_);
lean_dec_ref(v___y_2198_);
lean_dec_ref(v_as_2194_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28(uint8_t v___x_2204_, lean_object* v_as_2205_, size_t v_sz_2206_, size_t v_i_2207_, lean_object* v_b_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
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
lean_object* v_snd_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2251_; 
v_snd_2214_ = lean_ctor_get(v_b_2208_, 1);
v_isSharedCheck_2251_ = !lean_is_exclusive(v_b_2208_);
if (v_isSharedCheck_2251_ == 0)
{
lean_object* v_unused_2252_; 
v_unused_2252_ = lean_ctor_get(v_b_2208_, 0);
lean_dec(v_unused_2252_);
v___x_2216_ = v_b_2208_;
v_isShared_2217_ = v_isSharedCheck_2251_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_snd_2214_);
lean_dec(v_b_2208_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2251_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v_ref_2218_; lean_object* v_a_2219_; lean_object* v_ref_2220_; lean_object* v_msg_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2250_; 
v_ref_2218_ = lean_ctor_get(v___y_2209_, 2);
v_a_2219_ = lean_array_uget(v_as_2205_, v_i_2207_);
v_ref_2220_ = lean_ctor_get(v_a_2219_, 0);
v_msg_2221_ = lean_ctor_get(v_a_2219_, 1);
v_isSharedCheck_2250_ = !lean_is_exclusive(v_a_2219_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2223_ = v_a_2219_;
v_isShared_2224_ = v_isSharedCheck_2250_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_msg_2221_);
lean_inc(v_ref_2220_);
lean_dec(v_a_2219_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2250_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2225_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v_ref_2242_; lean_object* v___y_2244_; lean_object* v___x_2247_; 
v___x_2225_ = lean_box(0);
v_ref_2242_ = l_Lean_replaceRef(v_ref_2220_, v_ref_2218_);
lean_dec(v_ref_2220_);
v___x_2247_ = l_Lean_Syntax_getPos_x3f(v_ref_2242_, v___x_2204_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v___x_2248_; 
v___x_2248_ = lean_unsigned_to_nat(0u);
v___y_2244_ = v___x_2248_;
goto v___jp_2243_;
}
else
{
lean_object* v_val_2249_; 
v_val_2249_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_val_2249_);
lean_dec_ref_known(v___x_2247_, 1);
v___y_2244_ = v_val_2249_;
goto v___jp_2243_;
}
v___jp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 1, v___y_2228_);
lean_ctor_set(v___x_2216_, 0, v___y_2227_);
v___x_2230_ = v___x_2216_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___y_2227_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v___y_2228_);
v___x_2230_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v_pos2traces_2234_; lean_object* v___x_2236_; 
v___x_2231_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_2232_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_2214_, v___x_2230_, v___x_2231_);
v___x_2233_ = lean_array_push(v___x_2232_, v_msg_2221_);
v_pos2traces_2234_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_2214_, v___x_2230_, v___x_2233_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 1, v_pos2traces_2234_);
lean_ctor_set(v___x_2223_, 0, v___x_2225_);
v___x_2236_ = v___x_2223_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2225_);
lean_ctor_set(v_reuseFailAlloc_2240_, 1, v_pos2traces_2234_);
v___x_2236_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
size_t v___x_2237_; size_t v___x_2238_; lean_object* v___x_2239_; 
v___x_2237_ = ((size_t)1ULL);
v___x_2238_ = lean_usize_add(v_i_2207_, v___x_2237_);
v___x_2239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(v___x_2204_, v_as_2205_, v_sz_2206_, v___x_2238_, v___x_2236_, v___y_2209_);
return v___x_2239_;
}
}
}
v___jp_2243_:
{
lean_object* v___x_2245_; 
v___x_2245_ = l_Lean_Syntax_getTailPos_x3f(v_ref_2242_, v___x_2204_);
lean_dec(v_ref_2242_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_inc(v___y_2244_);
v___y_2227_ = v___y_2244_;
v___y_2228_ = v___y_2244_;
goto v___jp_2226_;
}
else
{
lean_object* v_val_2246_; 
v_val_2246_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_val_2246_);
lean_dec_ref_known(v___x_2245_, 1);
v___y_2227_ = v___y_2244_;
v___y_2228_ = v_val_2246_;
goto v___jp_2226_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28___boxed(lean_object* v___x_2253_, lean_object* v_as_2254_, lean_object* v_sz_2255_, lean_object* v_i_2256_, lean_object* v_b_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
uint8_t v___x_39571__boxed_2261_; size_t v_sz_boxed_2262_; size_t v_i_boxed_2263_; lean_object* v_res_2264_; 
v___x_39571__boxed_2261_ = lean_unbox(v___x_2253_);
v_sz_boxed_2262_ = lean_unbox_usize(v_sz_2255_);
lean_dec(v_sz_2255_);
v_i_boxed_2263_ = lean_unbox_usize(v_i_2256_);
lean_dec(v_i_2256_);
v_res_2264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28(v___x_39571__boxed_2261_, v_as_2254_, v_sz_boxed_2262_, v_i_boxed_2263_, v_b_2257_, v___y_2258_, v___y_2259_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec_ref(v_as_2254_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(uint8_t v___x_2265_, lean_object* v_t_2266_, lean_object* v_init_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v_root_2271_; lean_object* v_tail_2272_; lean_object* v___x_2273_; 
v_root_2271_ = lean_ctor_get(v_t_2266_, 0);
v_tail_2272_ = lean_ctor_get(v_t_2266_, 1);
lean_inc_ref(v_init_2267_);
v___x_2273_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(v_init_2267_, v___x_2265_, v_root_2271_, v_init_2267_, v___y_2268_, v___y_2269_);
lean_dec_ref(v_init_2267_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2310_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2276_ = v___x_2273_;
v_isShared_2277_ = v_isSharedCheck_2310_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2273_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2310_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
if (lean_obj_tag(v_a_2274_) == 0)
{
lean_object* v_a_2278_; lean_object* v___x_2280_; 
v_a_2278_ = lean_ctor_get(v_a_2274_, 0);
lean_inc(v_a_2278_);
lean_dec_ref_known(v_a_2274_, 1);
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 0, v_a_2278_);
v___x_2280_ = v___x_2276_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2278_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; size_t v_sz_2285_; size_t v___x_2286_; lean_object* v___x_2287_; 
lean_del_object(v___x_2276_);
v_a_2282_ = lean_ctor_get(v_a_2274_, 0);
lean_inc(v_a_2282_);
lean_dec_ref_known(v_a_2274_, 1);
v___x_2283_ = lean_box(0);
v___x_2284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
lean_ctor_set(v___x_2284_, 1, v_a_2282_);
v_sz_2285_ = lean_array_size(v_tail_2272_);
v___x_2286_ = ((size_t)0ULL);
v___x_2287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28(v___x_2265_, v_tail_2272_, v_sz_2285_, v___x_2286_, v___x_2284_, v___y_2268_, v___y_2269_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2301_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2290_ = v___x_2287_;
v_isShared_2291_ = v_isSharedCheck_2301_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2287_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2301_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v_fst_2292_; 
v_fst_2292_ = lean_ctor_get(v_a_2288_, 0);
if (lean_obj_tag(v_fst_2292_) == 0)
{
lean_object* v_snd_2293_; lean_object* v___x_2295_; 
v_snd_2293_ = lean_ctor_get(v_a_2288_, 1);
lean_inc(v_snd_2293_);
lean_dec(v_a_2288_);
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 0, v_snd_2293_);
v___x_2295_ = v___x_2290_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_snd_2293_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
else
{
lean_object* v_val_2297_; lean_object* v___x_2299_; 
lean_inc_ref(v_fst_2292_);
lean_dec(v_a_2288_);
v_val_2297_ = lean_ctor_get(v_fst_2292_, 0);
lean_inc(v_val_2297_);
lean_dec_ref_known(v_fst_2292_, 1);
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 0, v_val_2297_);
v___x_2299_ = v___x_2290_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_val_2297_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
else
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
v_a_2302_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2304_ = v___x_2287_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2287_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2302_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
}
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
v_a_2311_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2273_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2273_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___boxed(lean_object* v___x_2319_, lean_object* v_t_2320_, lean_object* v_init_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
uint8_t v___x_39652__boxed_2325_; lean_object* v_res_2326_; 
v___x_39652__boxed_2325_ = lean_unbox(v___x_2319_);
v_res_2326_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(v___x_39652__boxed_2325_, v_t_2320_, v_init_2321_, v___y_2322_, v___y_2323_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec_ref(v_t_2320_);
return v_res_2326_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0(void){
_start:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2327_ = lean_unsigned_to_nat(32u);
v___x_2328_ = lean_mk_empty_array_with_capacity(v___x_2327_);
v___x_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
return v___x_2329_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1(void){
_start:
{
size_t v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2330_ = ((size_t)5ULL);
v___x_2331_ = lean_unsigned_to_nat(0u);
v___x_2332_ = lean_unsigned_to_nat(32u);
v___x_2333_ = lean_mk_empty_array_with_capacity(v___x_2332_);
v___x_2334_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0);
v___x_2335_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
lean_ctor_set(v___x_2335_, 1, v___x_2333_);
lean_ctor_set(v___x_2335_, 2, v___x_2331_);
lean_ctor_set(v___x_2335_, 3, v___x_2331_);
lean_ctor_set_usize(v___x_2335_, 4, v___x_2330_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(lean_object* v___y_2336_){
_start:
{
lean_object* v___x_2338_; lean_object* v_traceState_2339_; lean_object* v_traces_2340_; lean_object* v___x_2341_; lean_object* v_traceState_2342_; lean_object* v_env_2343_; lean_object* v_nextMacroScope_2344_; lean_object* v_ngen_2345_; lean_object* v_auxDeclNGen_2346_; lean_object* v_cache_2347_; lean_object* v_recordedDeps_2348_; lean_object* v_messages_2349_; lean_object* v_infoState_2350_; lean_object* v_snapshotTasks_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2370_; 
v___x_2338_ = lean_st_ref_get(v___y_2336_);
v_traceState_2339_ = lean_ctor_get(v___x_2338_, 4);
lean_inc_ref(v_traceState_2339_);
lean_dec(v___x_2338_);
v_traces_2340_ = lean_ctor_get(v_traceState_2339_, 0);
lean_inc_ref(v_traces_2340_);
lean_dec_ref(v_traceState_2339_);
v___x_2341_ = lean_st_ref_take(v___y_2336_);
v_traceState_2342_ = lean_ctor_get(v___x_2341_, 4);
v_env_2343_ = lean_ctor_get(v___x_2341_, 0);
v_nextMacroScope_2344_ = lean_ctor_get(v___x_2341_, 1);
v_ngen_2345_ = lean_ctor_get(v___x_2341_, 2);
v_auxDeclNGen_2346_ = lean_ctor_get(v___x_2341_, 3);
v_cache_2347_ = lean_ctor_get(v___x_2341_, 5);
v_recordedDeps_2348_ = lean_ctor_get(v___x_2341_, 6);
v_messages_2349_ = lean_ctor_get(v___x_2341_, 7);
v_infoState_2350_ = lean_ctor_get(v___x_2341_, 8);
v_snapshotTasks_2351_ = lean_ctor_get(v___x_2341_, 9);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2353_ = v___x_2341_;
v_isShared_2354_ = v_isSharedCheck_2370_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_snapshotTasks_2351_);
lean_inc(v_infoState_2350_);
lean_inc(v_messages_2349_);
lean_inc(v_recordedDeps_2348_);
lean_inc(v_cache_2347_);
lean_inc(v_traceState_2342_);
lean_inc(v_auxDeclNGen_2346_);
lean_inc(v_ngen_2345_);
lean_inc(v_nextMacroScope_2344_);
lean_inc(v_env_2343_);
lean_dec(v___x_2341_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2370_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
uint64_t v_tid_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2368_; 
v_tid_2355_ = lean_ctor_get_uint64(v_traceState_2342_, sizeof(void*)*1);
v_isSharedCheck_2368_ = !lean_is_exclusive(v_traceState_2342_);
if (v_isSharedCheck_2368_ == 0)
{
lean_object* v_unused_2369_; 
v_unused_2369_ = lean_ctor_get(v_traceState_2342_, 0);
lean_dec(v_unused_2369_);
v___x_2357_ = v_traceState_2342_;
v_isShared_2358_ = v_isSharedCheck_2368_;
goto v_resetjp_2356_;
}
else
{
lean_dec(v_traceState_2342_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2368_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2359_; lean_object* v___x_2361_; 
v___x_2359_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 0, v___x_2359_);
v___x_2361_ = v___x_2357_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v___x_2359_);
lean_ctor_set_uint64(v_reuseFailAlloc_2367_, sizeof(void*)*1, v_tid_2355_);
v___x_2361_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
lean_object* v___x_2363_; 
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 4, v___x_2361_);
v___x_2363_ = v___x_2353_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_env_2343_);
lean_ctor_set(v_reuseFailAlloc_2366_, 1, v_nextMacroScope_2344_);
lean_ctor_set(v_reuseFailAlloc_2366_, 2, v_ngen_2345_);
lean_ctor_set(v_reuseFailAlloc_2366_, 3, v_auxDeclNGen_2346_);
lean_ctor_set(v_reuseFailAlloc_2366_, 4, v___x_2361_);
lean_ctor_set(v_reuseFailAlloc_2366_, 5, v_cache_2347_);
lean_ctor_set(v_reuseFailAlloc_2366_, 6, v_recordedDeps_2348_);
lean_ctor_set(v_reuseFailAlloc_2366_, 7, v_messages_2349_);
lean_ctor_set(v_reuseFailAlloc_2366_, 8, v_infoState_2350_);
lean_ctor_set(v_reuseFailAlloc_2366_, 9, v_snapshotTasks_2351_);
v___x_2363_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2364_ = lean_st_ref_put(v___y_2336_, v___x_2363_);
v___x_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2365_, 0, v_traces_2340_);
return v___x_2365_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___boxed(lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___y_2371_);
lean_dec(v___y_2371_);
return v_res_2373_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0(void){
_start:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2374_ = lean_box(0);
v___x_2375_ = lean_unsigned_to_nat(16u);
v___x_2376_ = lean_mk_array(v___x_2375_, v___x_2374_);
return v___x_2376_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1(void){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v_pos2traces_2379_; 
v___x_2377_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0, &l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0);
v___x_2378_ = lean_unsigned_to_nat(0u);
v_pos2traces_2379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_2379_, 0, v___x_2378_);
lean_ctor_set(v_pos2traces_2379_, 1, v___x_2377_);
return v_pos2traces_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9(lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v_toCold_2386_; lean_object* v_options_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v_toCold_2386_ = lean_ctor_get(v___y_2380_, 0);
v_options_2387_ = lean_ctor_get(v_toCold_2386_, 2);
v___x_2388_ = l_Lean_trace_profiler_output;
v___x_2389_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(v_options_2387_, v___x_2388_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v___x_2390_; uint8_t v___x_2391_; 
v___x_2390_ = l_Lean_trace_profiler_serve;
v___x_2391_ = l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(v_options_2387_, v___x_2390_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2392_; lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2455_; 
v___x_2392_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___y_2381_);
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2395_ = v___x_2392_;
v_isShared_2396_ = v_isSharedCheck_2455_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2392_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2455_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
uint8_t v___x_2397_; 
v___x_2397_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_2393_);
if (v___x_2397_ == 0)
{
lean_object* v___x_2398_; lean_object* v_pos2traces_2399_; lean_object* v___x_2400_; 
lean_del_object(v___x_2395_);
v___x_2398_ = lean_unsigned_to_nat(0u);
v_pos2traces_2399_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1, &l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1);
v___x_2400_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(v___x_2397_, v_a_2393_, v_pos2traces_2399_, v___y_2380_, v___y_2381_);
lean_dec(v_a_2393_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; lean_object* v___y_2403_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2429_; lean_object* v_size_2435_; lean_object* v_buckets_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; uint8_t v___x_2439_; 
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_a_2401_);
lean_dec_ref_known(v___x_2400_, 1);
v_size_2435_ = lean_ctor_get(v_a_2401_, 0);
lean_inc(v_size_2435_);
v_buckets_2436_ = lean_ctor_get(v_a_2401_, 1);
lean_inc_ref(v_buckets_2436_);
lean_dec(v_a_2401_);
v___x_2437_ = lean_mk_empty_array_with_capacity(v_size_2435_);
lean_dec(v_size_2435_);
v___x_2438_ = lean_array_get_size(v_buckets_2436_);
v___x_2439_ = lean_nat_dec_lt(v___x_2398_, v___x_2438_);
if (v___x_2439_ == 0)
{
lean_dec_ref(v_buckets_2436_);
v___y_2429_ = v___x_2437_;
goto v___jp_2428_;
}
else
{
size_t v___x_2440_; size_t v___x_2441_; lean_object* v___x_2442_; 
v___x_2440_ = ((size_t)0ULL);
v___x_2441_ = lean_usize_of_nat(v___x_2438_);
v___x_2442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23(v_buckets_2436_, v___x_2440_, v___x_2441_, v___x_2437_);
lean_dec_ref(v_buckets_2436_);
v___y_2429_ = v___x_2442_;
goto v___jp_2428_;
}
v___jp_2402_:
{
lean_object* v___x_2404_; size_t v_sz_2405_; size_t v___x_2406_; lean_object* v___x_2407_; 
v___x_2404_ = lean_box(0);
v_sz_2405_ = lean_array_size(v___y_2403_);
v___x_2406_ = ((size_t)0ULL);
v___x_2407_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(v___x_2391_, v___y_2403_, v_sz_2405_, v___x_2406_, v___x_2404_, v___y_2380_, v___y_2381_);
lean_dec_ref(v___y_2403_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2414_; 
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2414_ == 0)
{
lean_object* v_unused_2415_; 
v_unused_2415_ = lean_ctor_get(v___x_2407_, 0);
lean_dec(v_unused_2415_);
v___x_2409_ = v___x_2407_;
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
else
{
lean_dec(v___x_2407_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 0, v___x_2404_);
v___x_2412_ = v___x_2409_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2404_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
else
{
return v___x_2407_;
}
}
v___jp_2416_:
{
lean_object* v___x_2421_; 
v___x_2421_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v___y_2419_, v___y_2417_, v___y_2418_, v___y_2420_);
lean_dec(v___y_2420_);
lean_dec(v___y_2419_);
v___y_2403_ = v___x_2421_;
goto v___jp_2402_;
}
v___jp_2422_:
{
uint8_t v___x_2427_; 
v___x_2427_ = lean_nat_dec_le(v___y_2426_, v___y_2424_);
if (v___x_2427_ == 0)
{
lean_dec(v___y_2424_);
lean_inc(v___y_2426_);
v___y_2417_ = v___y_2423_;
v___y_2418_ = v___y_2426_;
v___y_2419_ = v___y_2425_;
v___y_2420_ = v___y_2426_;
goto v___jp_2416_;
}
else
{
v___y_2417_ = v___y_2423_;
v___y_2418_ = v___y_2426_;
v___y_2419_ = v___y_2425_;
v___y_2420_ = v___y_2424_;
goto v___jp_2416_;
}
}
v___jp_2428_:
{
lean_object* v___x_2430_; uint8_t v___x_2431_; 
v___x_2430_ = lean_array_get_size(v___y_2429_);
v___x_2431_ = lean_nat_dec_eq(v___x_2430_, v___x_2398_);
if (v___x_2431_ == 0)
{
lean_object* v___x_2432_; lean_object* v___x_2433_; uint8_t v___x_2434_; 
v___x_2432_ = lean_unsigned_to_nat(1u);
v___x_2433_ = lean_nat_sub(v___x_2430_, v___x_2432_);
v___x_2434_ = lean_nat_dec_le(v___x_2398_, v___x_2433_);
if (v___x_2434_ == 0)
{
lean_inc(v___x_2433_);
v___y_2423_ = v___y_2429_;
v___y_2424_ = v___x_2433_;
v___y_2425_ = v___x_2430_;
v___y_2426_ = v___x_2433_;
goto v___jp_2422_;
}
else
{
v___y_2423_ = v___y_2429_;
v___y_2424_ = v___x_2433_;
v___y_2425_ = v___x_2430_;
v___y_2426_ = v___x_2398_;
goto v___jp_2422_;
}
}
else
{
v___y_2403_ = v___y_2429_;
goto v___jp_2402_;
}
}
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
v_a_2443_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2400_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2400_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
else
{
lean_object* v___x_2451_; lean_object* v___x_2453_; 
lean_dec(v_a_2393_);
v___x_2451_ = lean_box(0);
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 0, v___x_2451_);
v___x_2453_ = v___x_2395_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2451_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
else
{
goto v___jp_2383_;
}
}
else
{
lean_dec_ref_known(v___x_2389_, 1);
goto v___jp_2383_;
}
v___jp_2383_:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2384_ = lean_box(0);
v___x_2385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2384_);
return v___x_2385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9___boxed(lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2456_, v___y_2457_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(lean_object* v_as_2460_, size_t v_sz_2461_, size_t v_i_2462_, lean_object* v_b_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
uint8_t v___x_2467_; 
v___x_2467_ = lean_usize_dec_lt(v_i_2462_, v_sz_2461_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; 
v___x_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2468_, 0, v_b_2463_);
return v___x_2468_;
}
else
{
lean_object* v___x_2469_; lean_object* v_a_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2469_ = lean_box(0);
v_a_2470_ = lean_array_uget_borrowed(v_as_2460_, v_i_2462_);
v___x_2471_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2464_);
lean_inc(v_a_2470_);
v___x_2472_ = l_Lean_Compiler_LCNF_resumeCompilation(v_a_2470_, v___x_2471_, v___y_2464_, v___y_2465_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v___x_2473_; 
lean_dec_ref_known(v___x_2472_, 1);
v___x_2473_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2464_, v___y_2465_);
if (lean_obj_tag(v___x_2473_) == 0)
{
size_t v___x_2474_; size_t v___x_2475_; 
lean_dec_ref_known(v___x_2473_, 1);
v___x_2474_ = ((size_t)1ULL);
v___x_2475_ = lean_usize_add(v_i_2462_, v___x_2474_);
v_i_2462_ = v___x_2475_;
v_b_2463_ = v___x_2469_;
goto _start;
}
else
{
return v___x_2473_;
}
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2478_; 
v_a_2477_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_a_2477_);
lean_dec_ref_known(v___x_2472_, 1);
v___x_2478_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2464_, v___y_2465_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2485_ == 0)
{
lean_object* v_unused_2486_; 
v_unused_2486_ = lean_ctor_get(v___x_2478_, 0);
lean_dec(v_unused_2486_);
v___x_2480_ = v___x_2478_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_dec(v___x_2478_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set_tag(v___x_2480_, 1);
lean_ctor_set(v___x_2480_, 0, v_a_2477_);
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2477_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
else
{
lean_dec(v_a_2477_);
return v___x_2478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10___boxed(lean_object* v_as_2487_, lean_object* v_sz_2488_, lean_object* v_i_2489_, lean_object* v_b_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
size_t v_sz_boxed_2494_; size_t v_i_boxed_2495_; lean_object* v_res_2496_; 
v_sz_boxed_2494_ = lean_unbox_usize(v_sz_2488_);
lean_dec(v_sz_2488_);
v_i_boxed_2495_ = lean_unbox_usize(v_i_2489_);
lean_dec(v_i_2489_);
v_res_2496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(v_as_2487_, v_sz_boxed_2494_, v_i_boxed_2495_, v_b_2490_, v___y_2491_, v___y_2492_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec_ref(v_as_2487_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(lean_object* v_as_2497_, size_t v_sz_2498_, size_t v_i_2499_, lean_object* v_b_2500_, lean_object* v___y_2501_){
_start:
{
uint8_t v___x_2503_; 
v___x_2503_ = lean_usize_dec_lt(v_i_2499_, v_sz_2498_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2504_; 
v___x_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2504_, 0, v_b_2500_);
return v___x_2504_;
}
else
{
uint8_t v___x_2505_; lean_object* v_a_2506_; lean_object* v___x_2507_; lean_object* v_ref_2508_; lean_object* v___x_2509_; 
lean_dec_ref(v_b_2500_);
v___x_2505_ = 0;
v_a_2506_ = lean_array_uget_borrowed(v_as_2497_, v_i_2499_);
lean_inc(v_a_2506_);
v___x_2507_ = l_Lean_Message_toString(v_a_2506_, v___x_2505_);
v_ref_2508_ = lean_ctor_get(v___y_2501_, 2);
v___x_2509_ = l_IO_eprintln___at___00main_spec__6(v___x_2507_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v___x_2510_; size_t v___x_2511_; size_t v___x_2512_; 
lean_dec_ref_known(v___x_2509_, 1);
v___x_2510_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_2511_ = ((size_t)1ULL);
v___x_2512_ = lean_usize_add(v_i_2499_, v___x_2511_);
v_i_2499_ = v___x_2512_;
v_b_2500_ = v___x_2510_;
goto _start;
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2525_; 
v_a_2514_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2516_ = v___x_2509_;
v_isShared_2517_ = v_isSharedCheck_2525_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2509_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2525_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2523_; 
v___x_2518_ = lean_io_error_to_string(v_a_2514_);
v___x_2519_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2518_);
v___x_2520_ = l_Lean_MessageData_ofFormat(v___x_2519_);
lean_inc(v_ref_2508_);
v___x_2521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2521_, 0, v_ref_2508_);
lean_ctor_set(v___x_2521_, 1, v___x_2520_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 0, v___x_2521_);
v___x_2523_ = v___x_2516_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2521_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg___boxed(lean_object* v_as_2526_, lean_object* v_sz_2527_, lean_object* v_i_2528_, lean_object* v_b_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
size_t v_sz_boxed_2532_; size_t v_i_boxed_2533_; lean_object* v_res_2534_; 
v_sz_boxed_2532_ = lean_unbox_usize(v_sz_2527_);
lean_dec(v_sz_2527_);
v_i_boxed_2533_ = lean_unbox_usize(v_i_2528_);
lean_dec(v_i_2528_);
v_res_2534_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(v_as_2526_, v_sz_boxed_2532_, v_i_boxed_2533_, v_b_2529_, v___y_2530_);
lean_dec_ref(v___y_2530_);
lean_dec_ref(v_as_2526_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38(lean_object* v_as_2535_, size_t v_sz_2536_, size_t v_i_2537_, lean_object* v_b_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
uint8_t v___x_2542_; 
v___x_2542_ = lean_usize_dec_lt(v_i_2537_, v_sz_2536_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; 
v___x_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2543_, 0, v_b_2538_);
return v___x_2543_;
}
else
{
uint8_t v___x_2544_; lean_object* v_a_2545_; lean_object* v___x_2546_; lean_object* v_ref_2547_; lean_object* v___x_2548_; 
lean_dec_ref(v_b_2538_);
v___x_2544_ = 0;
v_a_2545_ = lean_array_uget_borrowed(v_as_2535_, v_i_2537_);
lean_inc(v_a_2545_);
v___x_2546_ = l_Lean_Message_toString(v_a_2545_, v___x_2544_);
v_ref_2547_ = lean_ctor_get(v___y_2539_, 2);
v___x_2548_ = l_IO_eprintln___at___00main_spec__6(v___x_2546_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v___x_2549_; size_t v___x_2550_; size_t v___x_2551_; lean_object* v___x_2552_; 
lean_dec_ref_known(v___x_2548_, 1);
v___x_2549_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_2550_ = ((size_t)1ULL);
v___x_2551_ = lean_usize_add(v_i_2537_, v___x_2550_);
v___x_2552_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(v_as_2535_, v_sz_2536_, v___x_2551_, v___x_2549_, v___y_2539_);
return v___x_2552_;
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2564_; 
v_a_2553_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2555_ = v___x_2548_;
v_isShared_2556_ = v_isSharedCheck_2564_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2548_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2564_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2562_; 
v___x_2557_ = lean_io_error_to_string(v_a_2553_);
v___x_2558_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2557_);
v___x_2559_ = l_Lean_MessageData_ofFormat(v___x_2558_);
lean_inc(v_ref_2547_);
v___x_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2560_, 0, v_ref_2547_);
lean_ctor_set(v___x_2560_, 1, v___x_2559_);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 0, v___x_2560_);
v___x_2562_ = v___x_2555_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2560_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38___boxed(lean_object* v_as_2565_, lean_object* v_sz_2566_, lean_object* v_i_2567_, lean_object* v_b_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
size_t v_sz_boxed_2572_; size_t v_i_boxed_2573_; lean_object* v_res_2574_; 
v_sz_boxed_2572_ = lean_unbox_usize(v_sz_2566_);
lean_dec(v_sz_2566_);
v_i_boxed_2573_ = lean_unbox_usize(v_i_2567_);
lean_dec(v_i_2567_);
v_res_2574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38(v_as_2565_, v_sz_boxed_2572_, v_i_boxed_2573_, v_b_2568_, v___y_2569_, v___y_2570_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec_ref(v_as_2565_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(lean_object* v_init_2575_, lean_object* v_n_2576_, lean_object* v_b_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
if (lean_obj_tag(v_n_2576_) == 0)
{
lean_object* v_cs_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; size_t v_sz_2584_; size_t v___x_2585_; lean_object* v___x_2586_; 
v_cs_2581_ = lean_ctor_get(v_n_2576_, 0);
v___x_2582_ = lean_box(0);
v___x_2583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2582_);
lean_ctor_set(v___x_2583_, 1, v_b_2577_);
v_sz_2584_ = lean_array_size(v_cs_2581_);
v___x_2585_ = ((size_t)0ULL);
v___x_2586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37(v_init_2575_, v_cs_2581_, v_sz_2584_, v___x_2585_, v___x_2583_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2601_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2589_ = v___x_2586_;
v_isShared_2590_ = v_isSharedCheck_2601_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2601_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v_fst_2591_; 
v_fst_2591_ = lean_ctor_get(v_a_2587_, 0);
if (lean_obj_tag(v_fst_2591_) == 0)
{
lean_object* v_snd_2592_; lean_object* v___x_2593_; lean_object* v___x_2595_; 
v_snd_2592_ = lean_ctor_get(v_a_2587_, 1);
lean_inc(v_snd_2592_);
lean_dec(v_a_2587_);
v___x_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2593_, 0, v_snd_2592_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v___x_2593_);
v___x_2595_ = v___x_2589_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2593_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
else
{
lean_object* v_val_2597_; lean_object* v___x_2599_; 
lean_inc_ref(v_fst_2591_);
lean_dec(v_a_2587_);
v_val_2597_ = lean_ctor_get(v_fst_2591_, 0);
lean_inc(v_val_2597_);
lean_dec_ref_known(v_fst_2591_, 1);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v_val_2597_);
v___x_2599_ = v___x_2589_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_val_2597_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
v_a_2602_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___x_2586_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2586_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
else
{
lean_object* v_vs_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; size_t v_sz_2613_; size_t v___x_2614_; lean_object* v___x_2615_; 
v_vs_2610_ = lean_ctor_get(v_n_2576_, 0);
v___x_2611_ = lean_box(0);
v___x_2612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
lean_ctor_set(v___x_2612_, 1, v_b_2577_);
v_sz_2613_ = lean_array_size(v_vs_2610_);
v___x_2614_ = ((size_t)0ULL);
v___x_2615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38(v_vs_2610_, v_sz_2613_, v___x_2614_, v___x_2612_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2630_; 
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2618_ = v___x_2615_;
v_isShared_2619_ = v_isSharedCheck_2630_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2615_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2630_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v_fst_2620_; 
v_fst_2620_ = lean_ctor_get(v_a_2616_, 0);
if (lean_obj_tag(v_fst_2620_) == 0)
{
lean_object* v_snd_2621_; lean_object* v___x_2622_; lean_object* v___x_2624_; 
v_snd_2621_ = lean_ctor_get(v_a_2616_, 1);
lean_inc(v_snd_2621_);
lean_dec(v_a_2616_);
v___x_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2622_, 0, v_snd_2621_);
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 0, v___x_2622_);
v___x_2624_ = v___x_2618_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2622_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
else
{
lean_object* v_val_2626_; lean_object* v___x_2628_; 
lean_inc_ref(v_fst_2620_);
lean_dec(v_a_2616_);
v_val_2626_ = lean_ctor_get(v_fst_2620_, 0);
lean_inc(v_val_2626_);
lean_dec_ref_known(v_fst_2620_, 1);
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 0, v_val_2626_);
v___x_2628_ = v___x_2618_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_val_2626_);
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
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
v_a_2631_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2633_ = v___x_2615_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2615_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37(lean_object* v_init_2639_, lean_object* v_as_2640_, size_t v_sz_2641_, size_t v_i_2642_, lean_object* v_b_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
uint8_t v___x_2647_; 
v___x_2647_ = lean_usize_dec_lt(v_i_2642_, v_sz_2641_);
if (v___x_2647_ == 0)
{
lean_object* v___x_2648_; 
v___x_2648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2648_, 0, v_b_2643_);
return v___x_2648_;
}
else
{
lean_object* v_snd_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2683_; 
v_snd_2649_ = lean_ctor_get(v_b_2643_, 1);
v_isSharedCheck_2683_ = !lean_is_exclusive(v_b_2643_);
if (v_isSharedCheck_2683_ == 0)
{
lean_object* v_unused_2684_; 
v_unused_2684_ = lean_ctor_get(v_b_2643_, 0);
lean_dec(v_unused_2684_);
v___x_2651_ = v_b_2643_;
v_isShared_2652_ = v_isSharedCheck_2683_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_snd_2649_);
lean_dec(v_b_2643_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2683_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2653_; lean_object* v_a_2654_; lean_object* v___x_2655_; 
v___x_2653_ = lean_box(0);
v_a_2654_ = lean_array_uget_borrowed(v_as_2640_, v_i_2642_);
lean_inc(v_snd_2649_);
v___x_2655_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(v_init_2639_, v_a_2654_, v_snd_2649_, v___y_2644_, v___y_2645_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2674_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2658_ = v___x_2655_;
v_isShared_2659_ = v_isSharedCheck_2674_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2655_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2674_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
if (lean_obj_tag(v_a_2656_) == 0)
{
lean_object* v___x_2660_; lean_object* v___x_2662_; 
v___x_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2660_, 0, v_a_2656_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 0, v___x_2660_);
v___x_2662_ = v___x_2651_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2660_);
lean_ctor_set(v_reuseFailAlloc_2666_, 1, v_snd_2649_);
v___x_2662_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
lean_object* v___x_2664_; 
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 0, v___x_2662_);
v___x_2664_ = v___x_2658_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2662_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; 
lean_del_object(v___x_2658_);
lean_dec(v_snd_2649_);
v_a_2667_ = lean_ctor_get(v_a_2656_, 0);
lean_inc(v_a_2667_);
lean_dec_ref_known(v_a_2656_, 1);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 1, v_a_2667_);
lean_ctor_set(v___x_2651_, 0, v___x_2653_);
v___x_2669_ = v___x_2651_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2653_);
lean_ctor_set(v_reuseFailAlloc_2673_, 1, v_a_2667_);
v___x_2669_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
size_t v___x_2670_; size_t v___x_2671_; 
v___x_2670_ = ((size_t)1ULL);
v___x_2671_ = lean_usize_add(v_i_2642_, v___x_2670_);
v_i_2642_ = v___x_2671_;
v_b_2643_ = v___x_2669_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_del_object(v___x_2651_);
lean_dec(v_snd_2649_);
v_a_2675_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2655_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2655_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37___boxed(lean_object* v_init_2685_, lean_object* v_as_2686_, lean_object* v_sz_2687_, lean_object* v_i_2688_, lean_object* v_b_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
size_t v_sz_boxed_2693_; size_t v_i_boxed_2694_; lean_object* v_res_2695_; 
v_sz_boxed_2693_ = lean_unbox_usize(v_sz_2687_);
lean_dec(v_sz_2687_);
v_i_boxed_2694_ = lean_unbox_usize(v_i_2688_);
lean_dec(v_i_2688_);
v_res_2695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37(v_init_2685_, v_as_2686_, v_sz_boxed_2693_, v_i_boxed_2694_, v_b_2689_, v___y_2690_, v___y_2691_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec_ref(v_as_2686_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26___boxed(lean_object* v_init_2696_, lean_object* v_n_2697_, lean_object* v_b_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(v_init_2696_, v_n_2697_, v_b_2698_, v___y_2699_, v___y_2700_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
lean_dec_ref(v_n_2697_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(lean_object* v_as_2703_, size_t v_sz_2704_, size_t v_i_2705_, lean_object* v_b_2706_, lean_object* v___y_2707_){
_start:
{
uint8_t v___x_2709_; 
v___x_2709_ = lean_usize_dec_lt(v_i_2705_, v_sz_2704_);
if (v___x_2709_ == 0)
{
lean_object* v___x_2710_; 
v___x_2710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2710_, 0, v_b_2706_);
return v___x_2710_;
}
else
{
uint8_t v___x_2711_; lean_object* v_a_2712_; lean_object* v___x_2713_; lean_object* v_ref_2714_; lean_object* v___x_2715_; 
lean_dec_ref(v_b_2706_);
v___x_2711_ = 0;
v_a_2712_ = lean_array_uget_borrowed(v_as_2703_, v_i_2705_);
lean_inc(v_a_2712_);
v___x_2713_ = l_Lean_Message_toString(v_a_2712_, v___x_2711_);
v_ref_2714_ = lean_ctor_get(v___y_2707_, 2);
v___x_2715_ = l_IO_eprintln___at___00main_spec__6(v___x_2713_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v___x_2716_; size_t v___x_2717_; size_t v___x_2718_; 
lean_dec_ref_known(v___x_2715_, 1);
v___x_2716_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_2717_ = ((size_t)1ULL);
v___x_2718_ = lean_usize_add(v_i_2705_, v___x_2717_);
v_i_2705_ = v___x_2718_;
v_b_2706_ = v___x_2716_;
goto _start;
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2731_; 
v_a_2720_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2722_ = v___x_2715_;
v_isShared_2723_ = v_isSharedCheck_2731_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2715_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2731_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2729_; 
v___x_2724_ = lean_io_error_to_string(v_a_2720_);
v___x_2725_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2724_);
v___x_2726_ = l_Lean_MessageData_ofFormat(v___x_2725_);
lean_inc(v_ref_2714_);
v___x_2727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2727_, 0, v_ref_2714_);
lean_ctor_set(v___x_2727_, 1, v___x_2726_);
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 0, v___x_2727_);
v___x_2729_ = v___x_2722_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2727_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg___boxed(lean_object* v_as_2732_, lean_object* v_sz_2733_, lean_object* v_i_2734_, lean_object* v_b_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
size_t v_sz_boxed_2738_; size_t v_i_boxed_2739_; lean_object* v_res_2740_; 
v_sz_boxed_2738_ = lean_unbox_usize(v_sz_2733_);
lean_dec(v_sz_2733_);
v_i_boxed_2739_ = lean_unbox_usize(v_i_2734_);
lean_dec(v_i_2734_);
v_res_2740_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(v_as_2732_, v_sz_boxed_2738_, v_i_boxed_2739_, v_b_2735_, v___y_2736_);
lean_dec_ref(v___y_2736_);
lean_dec_ref(v_as_2732_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27(lean_object* v_as_2741_, size_t v_sz_2742_, size_t v_i_2743_, lean_object* v_b_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
uint8_t v___x_2748_; 
v___x_2748_ = lean_usize_dec_lt(v_i_2743_, v_sz_2742_);
if (v___x_2748_ == 0)
{
lean_object* v___x_2749_; 
v___x_2749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2749_, 0, v_b_2744_);
return v___x_2749_;
}
else
{
uint8_t v___x_2750_; lean_object* v_a_2751_; lean_object* v___x_2752_; lean_object* v_ref_2753_; lean_object* v___x_2754_; 
lean_dec_ref(v_b_2744_);
v___x_2750_ = 0;
v_a_2751_ = lean_array_uget_borrowed(v_as_2741_, v_i_2743_);
lean_inc(v_a_2751_);
v___x_2752_ = l_Lean_Message_toString(v_a_2751_, v___x_2750_);
v_ref_2753_ = lean_ctor_get(v___y_2745_, 2);
v___x_2754_ = l_IO_eprintln___at___00main_spec__6(v___x_2752_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v___x_2755_; size_t v___x_2756_; size_t v___x_2757_; lean_object* v___x_2758_; 
lean_dec_ref_known(v___x_2754_, 1);
v___x_2755_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_2756_ = ((size_t)1ULL);
v___x_2757_ = lean_usize_add(v_i_2743_, v___x_2756_);
v___x_2758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(v_as_2741_, v_sz_2742_, v___x_2757_, v___x_2755_, v___y_2745_);
return v___x_2758_;
}
else
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2770_; 
v_a_2759_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2761_ = v___x_2754_;
v_isShared_2762_ = v_isSharedCheck_2770_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2754_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2770_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2768_; 
v___x_2763_ = lean_io_error_to_string(v_a_2759_);
v___x_2764_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2763_);
v___x_2765_ = l_Lean_MessageData_ofFormat(v___x_2764_);
lean_inc(v_ref_2753_);
v___x_2766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2766_, 0, v_ref_2753_);
lean_ctor_set(v___x_2766_, 1, v___x_2765_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 0, v___x_2766_);
v___x_2768_ = v___x_2761_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2766_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27___boxed(lean_object* v_as_2771_, lean_object* v_sz_2772_, lean_object* v_i_2773_, lean_object* v_b_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
size_t v_sz_boxed_2778_; size_t v_i_boxed_2779_; lean_object* v_res_2780_; 
v_sz_boxed_2778_ = lean_unbox_usize(v_sz_2772_);
lean_dec(v_sz_2772_);
v_i_boxed_2779_ = lean_unbox_usize(v_i_2773_);
lean_dec(v_i_2773_);
v_res_2780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27(v_as_2771_, v_sz_boxed_2778_, v_i_boxed_2779_, v_b_2774_, v___y_2775_, v___y_2776_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec_ref(v_as_2771_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__11(lean_object* v_t_2781_, lean_object* v_init_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_){
_start:
{
lean_object* v_root_2786_; lean_object* v_tail_2787_; lean_object* v___x_2788_; 
v_root_2786_ = lean_ctor_get(v_t_2781_, 0);
v_tail_2787_ = lean_ctor_get(v_t_2781_, 1);
v___x_2788_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(v_init_2782_, v_root_2786_, v_init_2782_, v___y_2783_, v___y_2784_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2825_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2791_ = v___x_2788_;
v_isShared_2792_ = v_isSharedCheck_2825_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2788_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2825_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
if (lean_obj_tag(v_a_2789_) == 0)
{
lean_object* v_a_2793_; lean_object* v___x_2795_; 
v_a_2793_ = lean_ctor_get(v_a_2789_, 0);
lean_inc(v_a_2793_);
lean_dec_ref_known(v_a_2789_, 1);
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 0, v_a_2793_);
v___x_2795_ = v___x_2791_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2793_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
else
{
lean_object* v_a_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; size_t v_sz_2800_; size_t v___x_2801_; lean_object* v___x_2802_; 
lean_del_object(v___x_2791_);
v_a_2797_ = lean_ctor_get(v_a_2789_, 0);
lean_inc(v_a_2797_);
lean_dec_ref_known(v_a_2789_, 1);
v___x_2798_ = lean_box(0);
v___x_2799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2798_);
lean_ctor_set(v___x_2799_, 1, v_a_2797_);
v_sz_2800_ = lean_array_size(v_tail_2787_);
v___x_2801_ = ((size_t)0ULL);
v___x_2802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27(v_tail_2787_, v_sz_2800_, v___x_2801_, v___x_2799_, v___y_2783_, v___y_2784_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2816_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2805_ = v___x_2802_;
v_isShared_2806_ = v_isSharedCheck_2816_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2802_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2816_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v_fst_2807_; 
v_fst_2807_ = lean_ctor_get(v_a_2803_, 0);
if (lean_obj_tag(v_fst_2807_) == 0)
{
lean_object* v_snd_2808_; lean_object* v___x_2810_; 
v_snd_2808_ = lean_ctor_get(v_a_2803_, 1);
lean_inc(v_snd_2808_);
lean_dec(v_a_2803_);
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 0, v_snd_2808_);
v___x_2810_ = v___x_2805_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_snd_2808_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
else
{
lean_object* v_val_2812_; lean_object* v___x_2814_; 
lean_inc_ref(v_fst_2807_);
lean_dec(v_a_2803_);
v_val_2812_ = lean_ctor_get(v_fst_2807_, 0);
lean_inc(v_val_2812_);
lean_dec_ref_known(v_fst_2807_, 1);
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 0, v_val_2812_);
v___x_2814_ = v___x_2805_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_val_2812_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
v_a_2817_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v___x_2802_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2802_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2822_; 
if (v_isShared_2820_ == 0)
{
v___x_2822_ = v___x_2819_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2817_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
}
}
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
v_a_2826_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2788_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2788_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2826_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__11___boxed(lean_object* v_t_2834_, lean_object* v_init_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l_Lean_PersistentArray_forIn___at___00main_spec__11(v_t_2834_, v_init_2835_, v___y_2836_, v___y_2837_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec_ref(v_t_2834_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(lean_object* v_as_2840_, size_t v_sz_2841_, size_t v_i_2842_, lean_object* v_b_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
uint8_t v___x_2847_; 
v___x_2847_ = lean_usize_dec_lt(v_i_2842_, v_sz_2841_);
if (v___x_2847_ == 0)
{
lean_object* v___x_2848_; 
v___x_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2848_, 0, v_b_2843_);
return v___x_2848_;
}
else
{
lean_object* v_a_2849_; lean_object* v_declNames_2850_; lean_object* v___x_2851_; size_t v_sz_2852_; size_t v___x_2853_; lean_object* v___x_2854_; 
v_a_2849_ = lean_array_uget_borrowed(v_as_2840_, v_i_2842_);
v_declNames_2850_ = lean_ctor_get(v_a_2849_, 0);
v___x_2851_ = lean_box(0);
v_sz_2852_ = lean_array_size(v_declNames_2850_);
v___x_2853_ = ((size_t)0ULL);
v___x_2854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(v_declNames_2850_, v_sz_2852_, v___x_2853_, v___x_2851_, v___y_2844_, v___y_2845_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v___x_2855_; 
lean_dec_ref_known(v___x_2854_, 1);
v___x_2855_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v___y_2845_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; lean_object* v_unreported_2857_; lean_object* v___x_2858_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref_known(v___x_2855_, 1);
v_unreported_2857_ = lean_ctor_get(v_a_2856_, 1);
lean_inc_ref(v_unreported_2857_);
lean_dec(v_a_2856_);
v___x_2858_ = l_Lean_PersistentArray_forIn___at___00main_spec__11(v_unreported_2857_, v___x_2851_, v___y_2844_, v___y_2845_);
lean_dec_ref(v_unreported_2857_);
if (lean_obj_tag(v___x_2858_) == 0)
{
size_t v___x_2859_; size_t v___x_2860_; 
lean_dec_ref_known(v___x_2858_, 1);
v___x_2859_ = ((size_t)1ULL);
v___x_2860_ = lean_usize_add(v_i_2842_, v___x_2859_);
v_i_2842_ = v___x_2860_;
v_b_2843_ = v___x_2851_;
goto _start;
}
else
{
return v___x_2858_;
}
}
else
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2869_; 
v_a_2862_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2864_ = v___x_2855_;
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2855_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2867_; 
if (v_isShared_2865_ == 0)
{
v___x_2867_ = v___x_2864_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2862_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
else
{
return v___x_2854_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___boxed(lean_object* v_as_2870_, lean_object* v_sz_2871_, lean_object* v_i_2872_, lean_object* v_b_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
size_t v_sz_boxed_2877_; size_t v_i_boxed_2878_; lean_object* v_res_2879_; 
v_sz_boxed_2877_ = lean_unbox_usize(v_sz_2871_);
lean_dec(v_sz_2871_);
v_i_boxed_2878_ = lean_unbox_usize(v_i_2872_);
lean_dec(v_i_2872_);
v_res_2879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(v_as_2870_, v_sz_boxed_2877_, v_i_boxed_2878_, v_b_2873_, v___y_2874_, v___y_2875_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec_ref(v_as_2870_);
return v_res_2879_;
}
}
static lean_object* _init_l_main___closed__1(void){
_start:
{
lean_object* v___x_2881_; 
v___x_2881_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg();
return v___x_2881_;
}
}
static lean_object* _init_l_main___closed__2(void){
_start:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2882_ = l_Lean_instInhabitedClassState_default;
v___x_2883_ = lean_box(0);
v___x_2884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2883_);
lean_ctor_set(v___x_2884_, 1, v___x_2882_);
return v___x_2884_;
}
}
static lean_object* _init_l_main___closed__3(void){
_start:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2885_ = l_Lean_Meta_Match_Extension_instInhabitedState;
v___x_2886_ = lean_box(0);
v___x_2887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
lean_ctor_set(v___x_2887_, 1, v___x_2885_);
return v___x_2887_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_2888_; 
v___x_2888_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_2888_;
}
}
static lean_object* _init_l_main___closed__5(void){
_start:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2889_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2890_ = lean_box(0);
v___x_2891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2890_);
lean_ctor_set(v___x_2891_, 1, v___x_2889_);
return v___x_2891_;
}
}
static lean_object* _init_l_main___closed__6(void){
_start:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2892_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_2893_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2892_);
return v___x_2893_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
lean_object* v___x_2894_; 
v___x_2894_ = l_Array_instInhabited___redArg();
return v___x_2894_;
}
}
static lean_object* _init_l_main___closed__17(void){
_start:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2907_ = ((lean_object*)(l_main___closed__16));
v___x_2908_ = lean_unsigned_to_nat(27u);
v___x_2909_ = lean_unsigned_to_nat(160u);
v___x_2910_ = ((lean_object*)(l_main___closed__15));
v___x_2911_ = ((lean_object*)(l_main___closed__14));
v___x_2912_ = l_mkPanicMessageWithDecl(v___x_2911_, v___x_2910_, v___x_2909_, v___x_2908_, v___x_2907_);
return v___x_2912_;
}
}
static lean_object* _init_l_main___closed__19(void){
_start:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2914_ = ((lean_object*)(l_main___closed__16));
v___x_2915_ = lean_unsigned_to_nat(51u);
v___x_2916_ = lean_unsigned_to_nat(133u);
v___x_2917_ = ((lean_object*)(l_main___closed__15));
v___x_2918_ = ((lean_object*)(l_main___closed__14));
v___x_2919_ = l_mkPanicMessageWithDecl(v___x_2918_, v___x_2917_, v___x_2916_, v___x_2915_, v___x_2914_);
return v___x_2919_;
}
}
static lean_object* _init_l_main___closed__20(void){
_start:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2920_ = lean_unsigned_to_nat(1u);
v___x_2921_ = l_Lean_firstFrontendMacroScope;
v___x_2922_ = lean_nat_add(v___x_2921_, v___x_2920_);
return v___x_2922_;
}
}
static lean_object* _init_l_main___closed__24(void){
_start:
{
lean_object* v___x_2929_; uint64_t v___x_2930_; lean_object* v___x_2931_; 
v___x_2929_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
v___x_2930_ = 0ULL;
v___x_2931_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2931_, 0, v___x_2929_);
lean_ctor_set_uint64(v___x_2931_, sizeof(void*)*1, v___x_2930_);
return v___x_2931_;
}
}
static lean_object* _init_l_main___closed__25(void){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2932_;
}
}
static lean_object* _init_l_main___closed__26(void){
_start:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2933_ = lean_obj_once(&l_main___closed__25, &l_main___closed__25_once, _init_l_main___closed__25);
v___x_2934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2933_);
return v___x_2934_;
}
}
static lean_object* _init_l_main___closed__27(void){
_start:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2935_ = lean_obj_once(&l_main___closed__26, &l_main___closed__26_once, _init_l_main___closed__26);
v___x_2936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2935_);
lean_ctor_set(v___x_2936_, 1, v___x_2935_);
return v___x_2936_;
}
}
static lean_object* _init_l_main___closed__29(void){
_start:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2939_ = lean_unsigned_to_nat(0u);
v___x_2940_ = l_Lean_Options_empty;
v___x_2941_ = ((lean_object*)(l_main___closed__28));
v___x_2942_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
lean_ctor_set(v___x_2942_, 1, v___x_2940_);
lean_ctor_set(v___x_2942_, 2, v___x_2941_);
lean_ctor_set(v___x_2942_, 3, v___x_2939_);
lean_ctor_set(v___x_2942_, 4, v___x_2939_);
lean_ctor_set(v___x_2942_, 5, v___x_2939_);
return v___x_2942_;
}
}
static lean_object* _init_l_main___closed__30(void){
_start:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2943_ = l_Lean_NameSet_empty;
v___x_2944_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
v___x_2945_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2944_);
lean_ctor_set(v___x_2945_, 1, v___x_2944_);
lean_ctor_set(v___x_2945_, 2, v___x_2943_);
return v___x_2945_;
}
}
static lean_object* _init_l_main___closed__31(void){
_start:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; uint8_t v___x_2948_; lean_object* v___x_2949_; 
v___x_2946_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
v___x_2947_ = lean_obj_once(&l_main___closed__26, &l_main___closed__26_once, _init_l_main___closed__26);
v___x_2948_ = 1;
v___x_2949_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2949_, 0, v___x_2947_);
lean_ctor_set(v___x_2949_, 1, v___x_2947_);
lean_ctor_set(v___x_2949_, 2, v___x_2946_);
lean_ctor_set_uint8(v___x_2949_, sizeof(void*)*3, v___x_2948_);
return v___x_2949_;
}
}
static uint8_t _init_l_main___closed__35(void){
_start:
{
uint8_t v___x_2954_; uint8_t v___x_2955_; uint8_t v___x_2956_; 
v___x_2954_ = 2;
v___x_2955_ = 0;
v___x_2956_ = l_Lean_instOrdOLeanLevel_ord(v___x_2955_, v___x_2954_);
return v___x_2956_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_2957_; lean_object* v___x_2958_; 
v___x_2957_ = 0;
v___x_2958_ = lean_box_uint32(v___x_2957_);
return v___x_2958_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_2959_; lean_object* v___x_2960_; 
v___x_2959_ = 1;
v___x_2960_ = lean_box_uint32(v___x_2959_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_2961_){
_start:
{
if (lean_obj_tag(v_args_2961_) == 1)
{
lean_object* v_tail_2986_; 
v_tail_2986_ = lean_ctor_get(v_args_2961_, 1);
lean_inc(v_tail_2986_);
if (lean_obj_tag(v_tail_2986_) == 1)
{
lean_object* v_tail_2987_; 
v_tail_2987_ = lean_ctor_get(v_tail_2986_, 1);
lean_inc(v_tail_2987_);
if (lean_obj_tag(v_tail_2987_) == 1)
{
lean_object* v_head_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_3746_; 
v_head_2988_ = lean_ctor_get(v_args_2961_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v_args_2961_);
if (v_isSharedCheck_3746_ == 0)
{
lean_object* v_unused_3747_; 
v_unused_3747_ = lean_ctor_get(v_args_2961_, 1);
lean_dec(v_unused_3747_);
v___x_2990_ = v_args_2961_;
v_isShared_2991_ = v_isSharedCheck_3746_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_head_2988_);
lean_dec(v_args_2961_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_3746_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v_head_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3744_; 
v_head_2992_ = lean_ctor_get(v_tail_2986_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v_tail_2986_);
if (v_isSharedCheck_3744_ == 0)
{
lean_object* v_unused_3745_; 
v_unused_3745_ = lean_ctor_get(v_tail_2986_, 1);
lean_dec(v_unused_3745_);
v___x_2994_ = v_tail_2986_;
v_isShared_2995_ = v_isSharedCheck_3744_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_head_2992_);
lean_dec(v_tail_2986_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3744_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v_head_2996_; lean_object* v_tail_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3743_; 
v_head_2996_ = lean_ctor_get(v_tail_2987_, 0);
v_tail_2997_ = lean_ctor_get(v_tail_2987_, 1);
v_isSharedCheck_3743_ = !lean_is_exclusive(v_tail_2987_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_2999_ = v_tail_2987_;
v_isShared_3000_ = v_isSharedCheck_3743_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_tail_2997_);
lean_inc(v_head_2996_);
lean_dec(v_tail_2987_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3743_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3001_ = lean_obj_once(&l_main___closed__1, &l_main___closed__1_once, _init_l_main___closed__1);
v___x_3002_ = lean_box(0);
v___x_3003_ = lean_obj_once(&l_main___closed__2, &l_main___closed__2_once, _init_l_main___closed__2);
v___x_3004_ = lean_obj_once(&l_main___closed__3, &l_main___closed__3_once, _init_l_main___closed__3);
v___x_3005_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_3006_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_3007_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_3008_ = lean_box(1);
v___x_3009_ = ((lean_object*)(l_main___closed__8));
v___x_3010_ = l_Lean_ModuleSetup_load(v_head_2988_);
lean_dec(v_head_2988_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; lean_object* v_name_3012_; lean_object* v_package_x3f_3013_; lean_object* v_importArts_3014_; lean_object* v_options_3015_; lean_object* v___f_3016_; uint8_t v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3021_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref_known(v___x_3010_, 1);
v_name_3012_ = lean_ctor_get(v_a_3011_, 0);
lean_inc(v_name_3012_);
v_package_x3f_3013_ = lean_ctor_get(v_a_3011_, 1);
lean_inc(v_package_x3f_3013_);
v_importArts_3014_ = lean_ctor_get(v_a_3011_, 3);
lean_inc(v_importArts_3014_);
v_options_3015_ = lean_ctor_get(v_a_3011_, 6);
lean_inc(v_options_3015_);
lean_dec(v_a_3011_);
v___f_3016_ = lean_alloc_closure((void*)(l_main___lam__0), 2, 1);
lean_closure_set(v___f_3016_, 0, v_package_x3f_3013_);
v___x_3017_ = 0;
v___x_3018_ = l_Lean_LeanOptions_toOptions(v_options_3015_);
v___x_3019_ = lean_box(v___x_3017_);
if (v_isShared_3000_ == 0)
{
lean_ctor_set_tag(v___x_2999_, 0);
lean_ctor_set(v___x_2999_, 1, v___x_3018_);
lean_ctor_set(v___x_2999_, 0, v___x_3019_);
v___x_3021_ = v___x_2999_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___x_3019_);
lean_ctor_set(v_reuseFailAlloc_3734_, 1, v___x_3018_);
v___x_3021_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
lean_object* v___x_3022_; 
v___x_3022_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_tail_2997_, v___x_3021_);
lean_dec(v_tail_2997_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; lean_object* v_fst_3024_; lean_object* v_snd_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3725_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_a_3023_);
lean_dec_ref_known(v___x_3022_, 1);
v_fst_3024_ = lean_ctor_get(v_a_3023_, 0);
v_snd_3025_ = lean_ctor_get(v_a_3023_, 1);
v_isSharedCheck_3725_ = !lean_is_exclusive(v_a_3023_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3027_ = v_a_3023_;
v_isShared_3028_ = v_isSharedCheck_3725_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_snd_3025_);
lean_inc(v_fst_3024_);
lean_dec(v_a_3023_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3725_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3029_; uint8_t v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___y_3036_; uint8_t v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; uint8_t v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v_nextMacroScope_3209_; lean_object* v_ngen_3210_; lean_object* v_auxDeclNGen_3211_; lean_object* v_traceState_3212_; lean_object* v_recordedDeps_3213_; lean_object* v_messages_3214_; lean_object* v_infoState_3215_; lean_object* v_snapshotTasks_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3240_; uint8_t v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; uint16_t v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; uint8_t v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; uint16_t v___y_3346_; uint8_t v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3370_; uint8_t v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; uint16_t v___y_3393_; uint8_t v___y_3394_; lean_object* v___y_3395_; uint8_t v___y_3396_; lean_object* v___y_3398_; uint8_t v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; uint16_t v___y_3412_; lean_object* v___y_3413_; uint8_t v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; uint8_t v___y_3422_; uint8_t v___y_3423_; lean_object* v___x_3424_; 
v___x_3029_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_3030_ = 1;
v___x_3031_ = l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(v_snd_3025_, v___x_3029_, v___x_3030_);
v___x_3032_ = l_Lean_maxHeartbeats;
v___x_3033_ = lean_unsigned_to_nat(0u);
v___x_3034_ = l_Lean_Option_set___at___00main_spec__3(v___x_3031_, v___x_3032_, v___x_3033_);
v___x_3424_ = lean_init_search_path();
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; uint8_t v___x_3430_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3544_; uint8_t v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3613_; lean_object* v___y_3614_; uint8_t v___y_3689_; uint8_t v___x_3716_; 
lean_dec_ref_known(v___x_3424_, 1);
v___x_3425_ = ((lean_object*)(l_main___closed__18));
lean_inc(v_name_3012_);
v___x_3426_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3426_, 0, v_name_3012_);
lean_ctor_set_uint8(v___x_3426_, sizeof(void*)*1, v___x_3030_);
lean_ctor_set_uint8(v___x_3426_, sizeof(void*)*1 + 1, v___x_3030_);
lean_ctor_set_uint8(v___x_3426_, sizeof(void*)*1 + 2, v___x_3017_);
v___x_3427_ = lean_unsigned_to_nat(1u);
v___x_3428_ = lean_mk_empty_array_with_capacity(v___x_3427_);
v___x_3429_ = lean_array_push(v___x_3428_, v___x_3426_);
v___x_3430_ = 0;
v___x_3716_ = lean_uint8_once(&l_main___closed__35, &l_main___closed__35_once, _init_l_main___closed__35);
if (v___x_3716_ == 0)
{
v___y_3689_ = v___x_3030_;
goto v___jp_3688_;
}
else
{
v___y_3689_ = v___x_3017_;
goto v___jp_3688_;
}
v___jp_3431_:
{
lean_object* v___x_3436_; lean_object* v_moduleData_3437_; lean_object* v___x_3438_; uint8_t v___x_3439_; 
v___x_3436_ = l_Lean_Environment_header(v___y_3435_);
v_moduleData_3437_ = lean_ctor_get(v___x_3436_, 7);
lean_inc_ref(v_moduleData_3437_);
lean_dec_ref(v___x_3436_);
v___x_3438_ = lean_array_get_size(v_moduleData_3437_);
v___x_3439_ = lean_nat_dec_lt(v___y_3434_, v___x_3438_);
if (v___x_3439_ == 0)
{
lean_object* v___x_3440_; lean_object* v___x_3441_; 
lean_dec_ref(v_moduleData_3437_);
lean_dec_ref(v___y_3435_);
lean_dec(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec_ref(v___x_3034_);
lean_del_object(v___x_3027_);
lean_dec(v_fst_3024_);
lean_dec(v_name_3012_);
lean_dec(v_head_2996_);
lean_del_object(v___x_2994_);
lean_dec(v_head_2992_);
v___x_3440_ = lean_obj_once(&l_main___closed__19, &l_main___closed__19_once, _init_l_main___closed__19);
v___x_3441_ = l_panic___at___00main_spec__5(v___x_3440_);
return v___x_3441_;
}
else
{
lean_object* v_base_3442_; lean_object* v_private_3443_; lean_object* v_header_3444_; lean_object* v_serverBaseExts_3445_; lean_object* v_checked_3446_; lean_object* v_asyncConstsMap_3447_; lean_object* v_asyncCtx_x3f_3448_; lean_object* v_importRealizationCtx_x3f_3449_; lean_object* v_localRealizationCtxMap_3450_; lean_object* v_allRealizations_3451_; uint8_t v_isExporting_3452_; uint8_t v_isRecordingDeps_3453_; lean_object* v_synthCacheRaw_x3f_3454_; lean_object* v_declChangeLog_3455_; lean_object* v_recordingConstGen_3456_; lean_object* v_constAddedGens_3457_; lean_object* v_constGen_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3541_; 
v_base_3442_ = lean_ctor_get(v___y_3435_, 0);
lean_inc_ref(v_base_3442_);
v_private_3443_ = lean_ctor_get(v_base_3442_, 0);
lean_inc(v_private_3443_);
v_header_3444_ = lean_ctor_get(v_private_3443_, 7);
lean_inc_ref(v_header_3444_);
v_serverBaseExts_3445_ = lean_ctor_get(v___y_3435_, 1);
v_checked_3446_ = lean_ctor_get(v___y_3435_, 2);
v_asyncConstsMap_3447_ = lean_ctor_get(v___y_3435_, 3);
v_asyncCtx_x3f_3448_ = lean_ctor_get(v___y_3435_, 4);
v_importRealizationCtx_x3f_3449_ = lean_ctor_get(v___y_3435_, 5);
v_localRealizationCtxMap_3450_ = lean_ctor_get(v___y_3435_, 6);
v_allRealizations_3451_ = lean_ctor_get(v___y_3435_, 7);
v_isExporting_3452_ = lean_ctor_get_uint8(v___y_3435_, sizeof(void*)*13);
v_isRecordingDeps_3453_ = lean_ctor_get_uint8(v___y_3435_, sizeof(void*)*13 + 1);
v_synthCacheRaw_x3f_3454_ = lean_ctor_get(v___y_3435_, 8);
v_declChangeLog_3455_ = lean_ctor_get(v___y_3435_, 9);
v_recordingConstGen_3456_ = lean_ctor_get(v___y_3435_, 10);
v_constAddedGens_3457_ = lean_ctor_get(v___y_3435_, 11);
v_constGen_3458_ = lean_ctor_get(v___y_3435_, 12);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___y_3435_);
if (v_isSharedCheck_3541_ == 0)
{
lean_object* v_unused_3542_; 
v_unused_3542_ = lean_ctor_get(v___y_3435_, 0);
lean_dec(v_unused_3542_);
v___x_3460_ = v___y_3435_;
v_isShared_3461_ = v_isSharedCheck_3541_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_constGen_3458_);
lean_inc(v_constAddedGens_3457_);
lean_inc(v_recordingConstGen_3456_);
lean_inc(v_declChangeLog_3455_);
lean_inc(v_synthCacheRaw_x3f_3454_);
lean_inc(v_allRealizations_3451_);
lean_inc(v_localRealizationCtxMap_3450_);
lean_inc(v_importRealizationCtx_x3f_3449_);
lean_inc(v_asyncCtx_x3f_3448_);
lean_inc(v_asyncConstsMap_3447_);
lean_inc(v_checked_3446_);
lean_inc(v_serverBaseExts_3445_);
lean_dec(v___y_3435_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3541_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v_public_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3539_; 
v_public_3462_ = lean_ctor_get(v_base_3442_, 1);
v_isSharedCheck_3539_ = !lean_is_exclusive(v_base_3442_);
if (v_isSharedCheck_3539_ == 0)
{
lean_object* v_unused_3540_; 
v_unused_3540_ = lean_ctor_get(v_base_3442_, 0);
lean_dec(v_unused_3540_);
v___x_3464_ = v_base_3442_;
v_isShared_3465_ = v_isSharedCheck_3539_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_public_3462_);
lean_dec(v_base_3442_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3539_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v_constants_3466_; uint8_t v_quotInit_3467_; lean_object* v_diagnostics_3468_; lean_object* v_const2ModIdx_3469_; lean_object* v_extensions_3470_; lean_object* v_irBaseExts_3471_; lean_object* v_extGens_3472_; lean_object* v_trackedGen_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3537_; 
v_constants_3466_ = lean_ctor_get(v_private_3443_, 0);
v_quotInit_3467_ = lean_ctor_get_uint8(v_private_3443_, sizeof(void*)*8);
v_diagnostics_3468_ = lean_ctor_get(v_private_3443_, 1);
v_const2ModIdx_3469_ = lean_ctor_get(v_private_3443_, 2);
v_extensions_3470_ = lean_ctor_get(v_private_3443_, 3);
v_irBaseExts_3471_ = lean_ctor_get(v_private_3443_, 4);
v_extGens_3472_ = lean_ctor_get(v_private_3443_, 5);
v_trackedGen_3473_ = lean_ctor_get(v_private_3443_, 6);
v_isSharedCheck_3537_ = !lean_is_exclusive(v_private_3443_);
if (v_isSharedCheck_3537_ == 0)
{
lean_object* v_unused_3538_; 
v_unused_3538_ = lean_ctor_get(v_private_3443_, 7);
lean_dec(v_unused_3538_);
v___x_3475_ = v_private_3443_;
v_isShared_3476_ = v_isSharedCheck_3537_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_trackedGen_3473_);
lean_inc(v_extGens_3472_);
lean_inc(v_irBaseExts_3471_);
lean_inc(v_extensions_3470_);
lean_inc(v_const2ModIdx_3469_);
lean_inc(v_diagnostics_3468_);
lean_inc(v_constants_3466_);
lean_dec(v_private_3443_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3537_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
uint32_t v_trustLevel_3477_; lean_object* v_mainModule_3478_; uint8_t v_isModule_3479_; lean_object* v_regions_3480_; lean_object* v_modules_3481_; lean_object* v_moduleNames_3482_; lean_object* v_moduleName2Idx_3483_; lean_object* v_importAllModules_3484_; lean_object* v_moduleData_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3535_; 
v_trustLevel_3477_ = lean_ctor_get_uint32(v_header_3444_, sizeof(void*)*8);
v_mainModule_3478_ = lean_ctor_get(v_header_3444_, 0);
v_isModule_3479_ = lean_ctor_get_uint8(v_header_3444_, sizeof(void*)*8 + 4);
v_regions_3480_ = lean_ctor_get(v_header_3444_, 2);
v_modules_3481_ = lean_ctor_get(v_header_3444_, 3);
v_moduleNames_3482_ = lean_ctor_get(v_header_3444_, 4);
v_moduleName2Idx_3483_ = lean_ctor_get(v_header_3444_, 5);
v_importAllModules_3484_ = lean_ctor_get(v_header_3444_, 6);
v_moduleData_3485_ = lean_ctor_get(v_header_3444_, 7);
v_isSharedCheck_3535_ = !lean_is_exclusive(v_header_3444_);
if (v_isSharedCheck_3535_ == 0)
{
lean_object* v_unused_3536_; 
v_unused_3536_ = lean_ctor_get(v_header_3444_, 1);
lean_dec(v_unused_3536_);
v___x_3487_ = v_header_3444_;
v_isShared_3488_ = v_isSharedCheck_3535_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_moduleData_3485_);
lean_inc(v_importAllModules_3484_);
lean_inc(v_moduleName2Idx_3483_);
lean_inc(v_moduleNames_3482_);
lean_inc(v_modules_3481_);
lean_inc(v_regions_3480_);
lean_inc(v_mainModule_3478_);
lean_dec(v_header_3444_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3535_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3489_; lean_object* v_imports_3490_; lean_object* v___x_3492_; 
v___x_3489_ = lean_array_fget(v_moduleData_3437_, v___y_3434_);
lean_dec_ref(v_moduleData_3437_);
v_imports_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc_ref(v_imports_3490_);
lean_dec(v___x_3489_);
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 1, v_imports_3490_);
v___x_3492_ = v___x_3487_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 8, 5);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_mainModule_3478_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v_imports_3490_);
lean_ctor_set(v_reuseFailAlloc_3534_, 2, v_regions_3480_);
lean_ctor_set(v_reuseFailAlloc_3534_, 3, v_modules_3481_);
lean_ctor_set(v_reuseFailAlloc_3534_, 4, v_moduleNames_3482_);
lean_ctor_set(v_reuseFailAlloc_3534_, 5, v_moduleName2Idx_3483_);
lean_ctor_set(v_reuseFailAlloc_3534_, 6, v_importAllModules_3484_);
lean_ctor_set(v_reuseFailAlloc_3534_, 7, v_moduleData_3485_);
lean_ctor_set_uint32(v_reuseFailAlloc_3534_, sizeof(void*)*8, v_trustLevel_3477_);
lean_ctor_set_uint8(v_reuseFailAlloc_3534_, sizeof(void*)*8 + 4, v_isModule_3479_);
v___x_3492_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
lean_object* v___x_3494_; 
if (v_isShared_3476_ == 0)
{
lean_ctor_set(v___x_3475_, 7, v___x_3492_);
v___x_3494_ = v___x_3475_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_constants_3466_);
lean_ctor_set(v_reuseFailAlloc_3533_, 1, v_diagnostics_3468_);
lean_ctor_set(v_reuseFailAlloc_3533_, 2, v_const2ModIdx_3469_);
lean_ctor_set(v_reuseFailAlloc_3533_, 3, v_extensions_3470_);
lean_ctor_set(v_reuseFailAlloc_3533_, 4, v_irBaseExts_3471_);
lean_ctor_set(v_reuseFailAlloc_3533_, 5, v_extGens_3472_);
lean_ctor_set(v_reuseFailAlloc_3533_, 6, v_trackedGen_3473_);
lean_ctor_set(v_reuseFailAlloc_3533_, 7, v___x_3492_);
lean_ctor_set_uint8(v_reuseFailAlloc_3533_, sizeof(void*)*8, v_quotInit_3467_);
v___x_3494_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
lean_object* v___x_3496_; 
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 0, v___x_3494_);
v___x_3496_ = v___x_3464_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3494_);
lean_ctor_set(v_reuseFailAlloc_3532_, 1, v_public_3462_);
v___x_3496_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
lean_object* v___x_3498_; 
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 0, v___x_3496_);
v___x_3498_ = v___x_3460_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v___x_3496_);
lean_ctor_set(v_reuseFailAlloc_3531_, 1, v_serverBaseExts_3445_);
lean_ctor_set(v_reuseFailAlloc_3531_, 2, v_checked_3446_);
lean_ctor_set(v_reuseFailAlloc_3531_, 3, v_asyncConstsMap_3447_);
lean_ctor_set(v_reuseFailAlloc_3531_, 4, v_asyncCtx_x3f_3448_);
lean_ctor_set(v_reuseFailAlloc_3531_, 5, v_importRealizationCtx_x3f_3449_);
lean_ctor_set(v_reuseFailAlloc_3531_, 6, v_localRealizationCtxMap_3450_);
lean_ctor_set(v_reuseFailAlloc_3531_, 7, v_allRealizations_3451_);
lean_ctor_set(v_reuseFailAlloc_3531_, 8, v_synthCacheRaw_x3f_3454_);
lean_ctor_set(v_reuseFailAlloc_3531_, 9, v_declChangeLog_3455_);
lean_ctor_set(v_reuseFailAlloc_3531_, 10, v_recordingConstGen_3456_);
lean_ctor_set(v_reuseFailAlloc_3531_, 11, v_constAddedGens_3457_);
lean_ctor_set(v_reuseFailAlloc_3531_, 12, v_constGen_3458_);
lean_ctor_set_uint8(v_reuseFailAlloc_3531_, sizeof(void*)*13, v_isExporting_3452_);
lean_ctor_set_uint8(v_reuseFailAlloc_3531_, sizeof(void*)*13 + 1, v_isRecordingDeps_3453_);
v___x_3498_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; uint16_t v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v_env_3525_; uint8_t v___x_3526_; uint16_t v___x_3527_; uint16_t v___x_3528_; uint16_t v___x_3529_; uint8_t v___x_3530_; 
v___x_3499_ = l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
v___x_3500_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3009_, v___x_3499_, v___x_3498_, v___y_3434_, v___x_3430_);
lean_dec(v___y_3434_);
v___x_3501_ = l_Lean_instInhabitedFileMap_default;
v___x_3502_ = lean_unsigned_to_nat(1000u);
v___x_3503_ = l_Lean_Core_getMaxHeartbeats(v___x_3034_);
v___x_3504_ = l_Lean_firstFrontendMacroScope;
v___x_3505_ = lean_box(0);
v___x_3506_ = lean_box(0);
v___x_3507_ = l_Lean_OptionFlags_ofOptions(v___x_3034_);
v___x_3508_ = lean_obj_once(&l_main___closed__20, &l_main___closed__20_once, _init_l_main___closed__20);
v___x_3509_ = ((lean_object*)(l_main___closed__23));
lean_inc_n(v___y_3433_, 3);
v___x_3510_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3510_, 0, v___y_3433_);
lean_ctor_set(v___x_3510_, 1, v___x_3427_);
lean_ctor_set(v___x_3510_, 2, v___x_3002_);
v___x_3511_ = lean_obj_once(&l_main___closed__24, &l_main___closed__24_once, _init_l_main___closed__24);
v___x_3512_ = lean_obj_once(&l_main___closed__27, &l_main___closed__27_once, _init_l_main___closed__27);
v___x_3513_ = ((lean_object*)(l_main___closed__28));
v___x_3514_ = l_Lean_Options_empty;
v___x_3515_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_3516_ = lean_obj_once(&l_main___closed__30, &l_main___closed__30_once, _init_l_main___closed__30);
v___x_3517_ = lean_obj_once(&l_main___closed__31, &l_main___closed__31_once, _init_l_main___closed__31);
lean_inc_ref(v___x_3510_);
v___x_3518_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3498_);
lean_ctor_set(v___x_3518_, 1, v___x_3508_);
lean_ctor_set(v___x_3518_, 2, v___x_3509_);
lean_ctor_set(v___x_3518_, 3, v___x_3510_);
lean_ctor_set(v___x_3518_, 4, v___x_3511_);
lean_ctor_set(v___x_3518_, 5, v___x_3512_);
lean_ctor_set(v___x_3518_, 6, v___x_3515_);
lean_ctor_set(v___x_3518_, 7, v___x_3516_);
lean_ctor_set(v___x_3518_, 8, v___x_3517_);
lean_ctor_set(v___x_3518_, 9, v___x_3513_);
v___x_3519_ = lean_st_mk_ref(v___x_3518_);
v___x_3520_ = l_Lean_inheritedTraceOptions;
v___x_3521_ = lean_st_ref_get(v___x_3520_);
lean_inc_ref(v___x_3034_);
lean_inc(v_head_2992_);
v___x_3522_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3522_, 0, v_head_2992_);
lean_ctor_set(v___x_3522_, 1, v___x_3501_);
lean_ctor_set(v___x_3522_, 2, v___x_3034_);
lean_ctor_set(v___x_3522_, 3, v___x_3502_);
lean_ctor_set(v___x_3522_, 4, v___y_3433_);
lean_ctor_set(v___x_3522_, 5, v___x_3002_);
lean_ctor_set(v___x_3522_, 6, v___x_3033_);
lean_ctor_set(v___x_3522_, 7, v___x_3503_);
lean_ctor_set(v___x_3522_, 8, v___y_3433_);
lean_ctor_set(v___x_3522_, 9, v___x_3504_);
lean_ctor_set(v___x_3522_, 10, v___x_3505_);
lean_ctor_set(v___x_3522_, 11, v___x_3521_);
v___x_3523_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3523_, 0, v___x_3522_);
lean_ctor_set(v___x_3523_, 1, v___x_3033_);
lean_ctor_set(v___x_3523_, 2, v___x_3506_);
lean_ctor_set_uint16(v___x_3523_, sizeof(void*)*3, v___x_3507_);
lean_ctor_set_uint8(v___x_3523_, sizeof(void*)*3 + 2, v___x_3017_);
lean_ctor_set_uint8(v___x_3523_, sizeof(void*)*3 + 3, v___x_3017_);
v___x_3524_ = lean_st_ref_get(v___x_3519_);
v_env_3525_ = lean_ctor_get(v___x_3524_, 0);
lean_inc_ref(v_env_3525_);
lean_dec(v___x_3524_);
v___x_3526_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3525_);
lean_dec_ref(v_env_3525_);
v___x_3527_ = 512;
v___x_3528_ = lean_uint16_land(v___x_3507_, v___x_3527_);
v___x_3529_ = 0;
v___x_3530_ = lean_uint16_dec_eq(v___x_3528_, v___x_3529_);
if (v___x_3530_ == 0)
{
if (v___x_3439_ == 0)
{
v___y_3398_ = v___x_3509_;
v___y_3399_ = v___x_3439_;
v___y_3400_ = v___x_3506_;
v___y_3401_ = v___x_3510_;
v___y_3402_ = v___x_3499_;
v___y_3403_ = v___x_3501_;
v___y_3404_ = v___y_3432_;
v___y_3405_ = v___x_3505_;
v___y_3406_ = v___x_3512_;
v___y_3407_ = v___x_3508_;
v___y_3408_ = v___x_3500_;
v___y_3409_ = v___x_3504_;
v___y_3410_ = v___x_3511_;
v___y_3411_ = v___x_3002_;
v___y_3412_ = v___x_3507_;
v___y_3413_ = v___x_3514_;
v___y_3414_ = v___x_3439_;
v___y_3415_ = v___x_3516_;
v___y_3416_ = v___y_3433_;
v___y_3417_ = v___x_3513_;
v___y_3418_ = v___x_3515_;
v___y_3419_ = v___x_3523_;
v___y_3420_ = v___x_3519_;
v___y_3421_ = v___x_3517_;
v___y_3422_ = v___x_3526_;
v___y_3423_ = v___x_3439_;
goto v___jp_3397_;
}
else
{
v___y_3370_ = v___x_3504_;
v___y_3371_ = v___x_3439_;
v___y_3372_ = v___x_3506_;
v___y_3373_ = v___x_3002_;
v___y_3374_ = v___x_3501_;
v___y_3375_ = v___y_3432_;
v___y_3376_ = v___x_3505_;
v___y_3377_ = v___x_3512_;
v___y_3378_ = v___x_3514_;
v___y_3379_ = v___x_3509_;
v___y_3380_ = v___x_3510_;
v___y_3381_ = v___x_3499_;
v___y_3382_ = v___x_3516_;
v___y_3383_ = v___y_3433_;
v___y_3384_ = v___x_3513_;
v___y_3385_ = v___x_3512_;
v___y_3386_ = v___x_3515_;
v___y_3387_ = v___x_3523_;
v___y_3388_ = v___x_3508_;
v___y_3389_ = v___x_3500_;
v___y_3390_ = v___x_3519_;
v___y_3391_ = v___x_3511_;
v___y_3392_ = v___x_3517_;
v___y_3393_ = v___x_3507_;
v___y_3394_ = v___x_3439_;
v___y_3395_ = v___x_3514_;
v___y_3396_ = v___x_3526_;
goto v___jp_3369_;
}
}
else
{
v___y_3398_ = v___x_3509_;
v___y_3399_ = v___x_3439_;
v___y_3400_ = v___x_3506_;
v___y_3401_ = v___x_3510_;
v___y_3402_ = v___x_3499_;
v___y_3403_ = v___x_3501_;
v___y_3404_ = v___y_3432_;
v___y_3405_ = v___x_3505_;
v___y_3406_ = v___x_3512_;
v___y_3407_ = v___x_3508_;
v___y_3408_ = v___x_3500_;
v___y_3409_ = v___x_3504_;
v___y_3410_ = v___x_3511_;
v___y_3411_ = v___x_3002_;
v___y_3412_ = v___x_3507_;
v___y_3413_ = v___x_3514_;
v___y_3414_ = v___x_3439_;
v___y_3415_ = v___x_3516_;
v___y_3416_ = v___y_3433_;
v___y_3417_ = v___x_3513_;
v___y_3418_ = v___x_3515_;
v___y_3419_ = v___x_3523_;
v___y_3420_ = v___x_3519_;
v___y_3421_ = v___x_3517_;
v___y_3422_ = v___x_3526_;
v___y_3423_ = v___x_3017_;
goto v___jp_3397_;
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
v___jp_3543_:
{
lean_object* v___x_3553_; 
if (v_isShared_2991_ == 0)
{
lean_ctor_set_tag(v___x_2990_, 0);
lean_ctor_set(v___x_2990_, 1, v___y_3551_);
lean_ctor_set(v___x_2990_, 0, v___y_3550_);
v___x_3553_ = v___x_2990_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___y_3550_);
lean_ctor_set(v_reuseFailAlloc_3559_, 1, v___y_3551_);
v___x_3553_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
lean_object* v___f_3554_; lean_object* v___x_3555_; 
v___f_3554_ = lean_alloc_closure((void*)(l_main___lam__3___boxed), 2, 1);
lean_closure_set(v___f_3554_, 0, v___x_3553_);
v___x_3555_ = lean_box(0);
if (v___y_3545_ == 0)
{
lean_object* v___x_3556_; 
lean_inc(v___y_3548_);
lean_inc_ref(v___y_3547_);
v___x_3556_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v___y_3547_, v___y_3546_, v___f_3554_, v___x_3555_, v___y_3548_, v___x_3030_);
v___y_3432_ = v___y_3544_;
v___y_3433_ = v___y_3548_;
v___y_3434_ = v___y_3549_;
v___y_3435_ = v___x_3556_;
goto v___jp_3431_;
}
else
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
lean_inc_ref_n(v___y_3547_, 2);
v___x_3557_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite___redArg(v___y_3547_, v___y_3546_);
lean_dec_ref(v___y_3546_);
lean_inc(v___y_3548_);
v___x_3558_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v___y_3547_, v___x_3557_, v___f_3554_, v___x_3555_, v___y_3548_, v___x_3030_);
v___y_3432_ = v___y_3544_;
v___y_3433_ = v___y_3548_;
v___y_3434_ = v___y_3549_;
v___y_3435_ = v___x_3558_;
goto v___jp_3431_;
}
}
}
v___jp_3560_:
{
lean_object* v___x_3565_; lean_object* v_toEnvExtension_3566_; lean_object* v_asyncMode_3567_; uint8_t v_logWrites_3568_; lean_object* v___x_3569_; lean_object* v_importedEntries_3570_; lean_object* v_state_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; uint8_t v___x_3574_; 
v___x_3565_ = l_Lean_IR_declMapExt;
v_toEnvExtension_3566_ = lean_ctor_get(v___x_3565_, 0);
v_asyncMode_3567_ = lean_ctor_get(v_toEnvExtension_3566_, 2);
v_logWrites_3568_ = lean_ctor_get_uint8(v_toEnvExtension_3566_, sizeof(void*)*6);
lean_inc(v___y_3562_);
lean_inc_ref(v___y_3564_);
v___x_3569_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3006_, v_toEnvExtension_3566_, v___y_3564_, v_asyncMode_3567_, v___y_3562_, v___x_3017_);
v_importedEntries_3570_ = lean_ctor_get(v___x_3569_, 0);
lean_inc_ref(v_importedEntries_3570_);
v_state_3571_ = lean_ctor_get(v___x_3569_, 1);
lean_inc(v_state_3571_);
lean_dec(v___x_3569_);
v___x_3572_ = lean_array_get_borrowed(v___x_3007_, v_importedEntries_3570_, v___y_3563_);
v___x_3573_ = lean_array_get_size(v___x_3572_);
v___x_3574_ = lean_nat_dec_lt(v___x_3033_, v___x_3573_);
if (v___x_3574_ == 0)
{
v___y_3544_ = v___y_3561_;
v___y_3545_ = v_logWrites_3568_;
v___y_3546_ = v___y_3564_;
v___y_3547_ = v_toEnvExtension_3566_;
v___y_3548_ = v___y_3562_;
v___y_3549_ = v___y_3563_;
v___y_3550_ = v_importedEntries_3570_;
v___y_3551_ = v_state_3571_;
goto v___jp_3543_;
}
else
{
uint8_t v___x_3575_; 
v___x_3575_ = lean_nat_dec_le(v___x_3573_, v___x_3573_);
if (v___x_3575_ == 0)
{
if (v___x_3574_ == 0)
{
v___y_3544_ = v___y_3561_;
v___y_3545_ = v_logWrites_3568_;
v___y_3546_ = v___y_3564_;
v___y_3547_ = v_toEnvExtension_3566_;
v___y_3548_ = v___y_3562_;
v___y_3549_ = v___y_3563_;
v___y_3550_ = v_importedEntries_3570_;
v___y_3551_ = v_state_3571_;
goto v___jp_3543_;
}
else
{
size_t v___x_3576_; size_t v___x_3577_; lean_object* v___x_3578_; 
v___x_3576_ = ((size_t)0ULL);
v___x_3577_ = lean_usize_of_nat(v___x_3573_);
lean_inc_ref(v___y_3564_);
v___x_3578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3564_, v___x_3572_, v___x_3576_, v___x_3577_, v_state_3571_);
v___y_3544_ = v___y_3561_;
v___y_3545_ = v_logWrites_3568_;
v___y_3546_ = v___y_3564_;
v___y_3547_ = v_toEnvExtension_3566_;
v___y_3548_ = v___y_3562_;
v___y_3549_ = v___y_3563_;
v___y_3550_ = v_importedEntries_3570_;
v___y_3551_ = v___x_3578_;
goto v___jp_3543_;
}
}
else
{
size_t v___x_3579_; size_t v___x_3580_; lean_object* v___x_3581_; 
v___x_3579_ = ((size_t)0ULL);
v___x_3580_ = lean_usize_of_nat(v___x_3573_);
lean_inc_ref(v___y_3564_);
v___x_3581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3564_, v___x_3572_, v___x_3579_, v___x_3580_, v_state_3571_);
v___y_3544_ = v___y_3561_;
v___y_3545_ = v_logWrites_3568_;
v___y_3546_ = v___y_3564_;
v___y_3547_ = v_toEnvExtension_3566_;
v___y_3548_ = v___y_3562_;
v___y_3549_ = v___y_3563_;
v___y_3550_ = v_importedEntries_3570_;
v___y_3551_ = v___x_3581_;
goto v___jp_3543_;
}
}
}
v___jp_3582_:
{
uint8_t v___x_3589_; 
v___x_3589_ = lean_nat_dec_lt(v___x_3033_, v___y_3586_);
if (v___x_3589_ == 0)
{
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
v___y_3561_ = v___y_3583_;
v___y_3562_ = v___y_3584_;
v___y_3563_ = v___y_3585_;
v___y_3564_ = v___y_3588_;
goto v___jp_3560_;
}
else
{
uint8_t v___x_3590_; 
v___x_3590_ = lean_nat_dec_le(v___y_3586_, v___y_3586_);
if (v___x_3590_ == 0)
{
if (v___x_3589_ == 0)
{
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
v___y_3561_ = v___y_3583_;
v___y_3562_ = v___y_3584_;
v___y_3563_ = v___y_3585_;
v___y_3564_ = v___y_3588_;
goto v___jp_3560_;
}
else
{
size_t v___x_3591_; size_t v___x_3592_; lean_object* v___x_3593_; 
v___x_3591_ = ((size_t)0ULL);
v___x_3592_ = lean_usize_of_nat(v___y_3586_);
lean_dec(v___y_3586_);
v___x_3593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3587_, v___x_3591_, v___x_3592_, v___y_3588_);
lean_dec_ref(v___y_3587_);
v___y_3561_ = v___y_3583_;
v___y_3562_ = v___y_3584_;
v___y_3563_ = v___y_3585_;
v___y_3564_ = v___x_3593_;
goto v___jp_3560_;
}
}
else
{
size_t v___x_3594_; size_t v___x_3595_; lean_object* v___x_3596_; 
v___x_3594_ = ((size_t)0ULL);
v___x_3595_ = lean_usize_of_nat(v___y_3586_);
lean_dec(v___y_3586_);
v___x_3596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3587_, v___x_3594_, v___x_3595_, v___y_3588_);
lean_dec_ref(v___y_3587_);
v___y_3561_ = v___y_3583_;
v___y_3562_ = v___y_3584_;
v___y_3563_ = v___y_3585_;
v___y_3564_ = v___x_3596_;
goto v___jp_3560_;
}
}
}
v___jp_3597_:
{
lean_object* v___x_3603_; uint8_t v___x_3604_; 
v___x_3603_ = lean_array_get_size(v___y_3602_);
v___x_3604_ = lean_nat_dec_lt(v___x_3033_, v___x_3603_);
if (v___x_3604_ == 0)
{
v___y_3583_ = v___y_3598_;
v___y_3584_ = v___y_3600_;
v___y_3585_ = v___y_3601_;
v___y_3586_ = v___x_3603_;
v___y_3587_ = v___y_3602_;
v___y_3588_ = v___y_3599_;
goto v___jp_3582_;
}
else
{
uint8_t v___x_3605_; 
v___x_3605_ = lean_nat_dec_le(v___x_3603_, v___x_3603_);
if (v___x_3605_ == 0)
{
if (v___x_3604_ == 0)
{
v___y_3583_ = v___y_3598_;
v___y_3584_ = v___y_3600_;
v___y_3585_ = v___y_3601_;
v___y_3586_ = v___x_3603_;
v___y_3587_ = v___y_3602_;
v___y_3588_ = v___y_3599_;
goto v___jp_3582_;
}
else
{
size_t v___x_3606_; size_t v___x_3607_; lean_object* v___x_3608_; 
v___x_3606_ = ((size_t)0ULL);
v___x_3607_ = lean_usize_of_nat(v___x_3603_);
v___x_3608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3602_, v___x_3606_, v___x_3607_, v___y_3599_);
v___y_3583_ = v___y_3598_;
v___y_3584_ = v___y_3600_;
v___y_3585_ = v___y_3601_;
v___y_3586_ = v___x_3603_;
v___y_3587_ = v___y_3602_;
v___y_3588_ = v___x_3608_;
goto v___jp_3582_;
}
}
else
{
size_t v___x_3609_; size_t v___x_3610_; lean_object* v___x_3611_; 
v___x_3609_ = ((size_t)0ULL);
v___x_3610_ = lean_usize_of_nat(v___x_3603_);
v___x_3611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3602_, v___x_3609_, v___x_3610_, v___y_3599_);
v___y_3583_ = v___y_3598_;
v___y_3584_ = v___y_3600_;
v___y_3585_ = v___y_3601_;
v___y_3586_ = v___x_3603_;
v___y_3587_ = v___y_3602_;
v___y_3588_ = v___x_3611_;
goto v___jp_3582_;
}
}
}
v___jp_3612_:
{
lean_object* v___x_3615_; lean_object* v_ext_3616_; lean_object* v___x_3617_; 
v___x_3615_ = l_Lean_Compiler_CSimp_ext;
v_ext_3616_ = lean_ctor_get(v___x_3615_, 1);
lean_inc_ref(v_ext_3616_);
lean_inc(v___y_3613_);
v___x_3617_ = l_main___elam__0___redArg(v___y_3613_, v___x_3017_, v___x_3001_, v_ext_3616_, v___y_3614_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v_a_3618_; lean_object* v___x_3619_; lean_object* v_ext_3620_; lean_object* v___x_3621_; 
v_a_3618_ = lean_ctor_get(v___x_3617_, 0);
lean_inc(v_a_3618_);
lean_dec_ref_known(v___x_3617_, 1);
v___x_3619_ = l_Lean_Meta_instanceExtension;
v_ext_3620_ = lean_ctor_get(v___x_3619_, 1);
lean_inc_ref(v_ext_3620_);
lean_inc(v___y_3613_);
v___x_3621_ = l_main___elam__0___redArg(v___y_3613_, v___x_3017_, v___x_3001_, v_ext_3620_, v_a_3618_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v_a_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; 
v_a_3622_ = lean_ctor_get(v___x_3621_, 0);
lean_inc(v_a_3622_);
lean_dec_ref_known(v___x_3621_, 1);
v___x_3623_ = l_Lean_classExtension;
lean_inc(v___y_3613_);
v___x_3624_ = l_main___elam__0___redArg(v___y_3613_, v___x_3017_, v___x_3003_, v___x_3623_, v_a_3622_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v_a_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
lean_inc(v_a_3625_);
lean_dec_ref_known(v___x_3624_, 1);
v___x_3626_ = l_Lean_Meta_Match_Extension_extension;
lean_inc(v___y_3613_);
v___x_3627_ = l_main___elam__0___redArg(v___y_3613_, v___x_3017_, v___x_3004_, v___x_3626_, v_a_3625_);
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3655_; 
v_a_3628_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3630_ = v___x_3627_;
v_isShared_3631_ = v_isSharedCheck_3655_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3627_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3655_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3632_; 
v___x_3632_ = l_Lean_Environment_getModuleIdx_x3f(v_a_3628_, v_name_3012_);
if (lean_obj_tag(v___x_3632_) == 1)
{
lean_object* v_val_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; uint8_t v___x_3638_; 
lean_del_object(v___x_3630_);
v_val_3633_ = lean_ctor_get(v___x_3632_, 0);
lean_inc(v_val_3633_);
lean_dec_ref_known(v___x_3632_, 1);
v___x_3634_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_3635_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3005_, v___x_3634_, v_a_3628_, v_val_3633_, v___x_3430_);
v___x_3636_ = lean_array_get_size(v___x_3635_);
v___x_3637_ = ((lean_object*)(l_main___closed__32));
v___x_3638_ = lean_nat_dec_lt(v___x_3033_, v___x_3636_);
if (v___x_3638_ == 0)
{
lean_dec_ref(v___x_3635_);
lean_inc(v___y_3613_);
v___y_3598_ = v___y_3613_;
v___y_3599_ = v_a_3628_;
v___y_3600_ = v___y_3613_;
v___y_3601_ = v_val_3633_;
v___y_3602_ = v___x_3637_;
goto v___jp_3597_;
}
else
{
uint8_t v___x_3639_; 
v___x_3639_ = lean_nat_dec_le(v___x_3636_, v___x_3636_);
if (v___x_3639_ == 0)
{
if (v___x_3638_ == 0)
{
lean_dec_ref(v___x_3635_);
lean_inc(v___y_3613_);
v___y_3598_ = v___y_3613_;
v___y_3599_ = v_a_3628_;
v___y_3600_ = v___y_3613_;
v___y_3601_ = v_val_3633_;
v___y_3602_ = v___x_3637_;
goto v___jp_3597_;
}
else
{
size_t v___x_3640_; size_t v___x_3641_; lean_object* v___x_3642_; 
v___x_3640_ = ((size_t)0ULL);
v___x_3641_ = lean_usize_of_nat(v___x_3636_);
lean_inc(v_a_3628_);
v___x_3642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_3628_, v___x_3635_, v___x_3640_, v___x_3641_, v___x_3637_);
lean_dec_ref(v___x_3635_);
lean_inc(v___y_3613_);
v___y_3598_ = v___y_3613_;
v___y_3599_ = v_a_3628_;
v___y_3600_ = v___y_3613_;
v___y_3601_ = v_val_3633_;
v___y_3602_ = v___x_3642_;
goto v___jp_3597_;
}
}
else
{
size_t v___x_3643_; size_t v___x_3644_; lean_object* v___x_3645_; 
v___x_3643_ = ((size_t)0ULL);
v___x_3644_ = lean_usize_of_nat(v___x_3636_);
lean_inc(v_a_3628_);
v___x_3645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_3628_, v___x_3635_, v___x_3643_, v___x_3644_, v___x_3637_);
lean_dec_ref(v___x_3635_);
lean_inc(v___y_3613_);
v___y_3598_ = v___y_3613_;
v___y_3599_ = v_a_3628_;
v___y_3600_ = v___y_3613_;
v___y_3601_ = v_val_3633_;
v___y_3602_ = v___x_3645_;
goto v___jp_3597_;
}
}
}
else
{
lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3653_; 
lean_dec(v___x_3632_);
lean_dec(v_a_3628_);
lean_dec(v___y_3613_);
lean_dec_ref(v___x_3034_);
lean_del_object(v___x_3027_);
lean_dec(v_fst_3024_);
lean_dec(v_head_2996_);
lean_del_object(v___x_2994_);
lean_dec(v_head_2992_);
lean_del_object(v___x_2990_);
v___x_3646_ = ((lean_object*)(l_main___closed__33));
v___x_3647_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3012_, v___x_3030_);
v___x_3648_ = lean_string_append(v___x_3646_, v___x_3647_);
lean_dec_ref(v___x_3647_);
v___x_3649_ = ((lean_object*)(l_main___closed__34));
v___x_3650_ = lean_string_append(v___x_3648_, v___x_3649_);
v___x_3651_ = lean_mk_io_user_error(v___x_3650_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set_tag(v___x_3630_, 1);
lean_ctor_set(v___x_3630_, 0, v___x_3651_);
v___x_3653_ = v___x_3630_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v___x_3651_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
}
}
else
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3663_; 
lean_dec(v___y_3613_);
lean_dec_ref(v___x_3034_);
lean_del_object(v___x_3027_);
lean_dec(v_fst_3024_);
lean_dec(v_name_3012_);
lean_dec(v_head_2996_);
lean_del_object(v___x_2994_);
lean_dec(v_head_2992_);
lean_del_object(v___x_2990_);
v_a_3656_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3658_ = v___x_3627_;
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3627_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3661_; 
if (v_isShared_3659_ == 0)
{
v___x_3661_ = v___x_3658_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_a_3656_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
}
else
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3671_; 
lean_dec(v___y_3613_);
lean_dec_ref(v___x_3034_);
lean_del_object(v___x_3027_);
lean_dec(v_fst_3024_);
lean_dec(v_name_3012_);
lean_dec(v_head_2996_);
lean_del_object(v___x_2994_);
lean_dec(v_head_2992_);
lean_del_object(v___x_2990_);
v_a_3664_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3666_ = v___x_3624_;
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3624_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3669_; 
if (v_isShared_3667_ == 0)
{
v___x_3669_ = v___x_3666_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3664_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
else
{
lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3679_; 
lean_dec(v___y_3613_);
lean_dec_ref(v___x_3034_);
lean_del_object(v___x_3027_);
lean_dec(v_fst_3024_);
lean_dec(v_name_3012_);
lean_dec(v_head_2996_);
lean_del_object(v___x_2994_);
lean_dec(v_head_2992_);
lean_del_object(v___x_2990_);
v_a_3672_ = lean_ctor_get(v___x_3621_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3674_ = v___x_3621_;
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3621_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3677_; 
if (v_isShared_3675_ == 0)
{
v___x_3677_ = v___x_3674_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_a_3672_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
}
else
{
lean_object* v_a_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3687_; 
lean_dec(v___y_3613_);
lean_dec_ref(v___x_3034_);
lean_del_object(v___x_3027_);
lean_dec(v_fst_3024_);
lean_dec(v_name_3012_);
lean_dec(v_head_2996_);
lean_del_object(v___x_2994_);
lean_dec(v_head_2992_);
lean_del_object(v___x_2990_);
v_a_3680_ = lean_ctor_get(v___x_3617_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3682_ = v___x_3617_;
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_a_3680_);
lean_dec(v___x_3617_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3685_; 
if (v_isShared_3683_ == 0)
{
v___x_3685_ = v___x_3682_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3680_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
}
v___jp_3688_:
{
lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___f_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3690_ = l_Lean_instInhabitedImportState_default;
v___x_3691_ = lean_box(v___x_3430_);
v___x_3692_ = lean_box(v___y_3689_);
v___x_3693_ = lean_box(v___x_3030_);
v___x_3694_ = lean_box(v___x_3017_);
lean_inc_ref(v___x_3034_);
lean_inc(v_name_3012_);
v___f_3695_ = lean_alloc_closure((void*)(l_main___lam__1___boxed), 10, 9);
lean_closure_set(v___f_3695_, 0, v___x_3690_);
lean_closure_set(v___f_3695_, 1, v___x_3429_);
lean_closure_set(v___f_3695_, 2, v___x_3691_);
lean_closure_set(v___f_3695_, 3, v_importArts_3014_);
lean_closure_set(v___f_3695_, 4, v___x_3692_);
lean_closure_set(v___f_3695_, 5, v___x_3693_);
lean_closure_set(v___f_3695_, 6, v_name_3012_);
lean_closure_set(v___f_3695_, 7, v___x_3034_);
lean_closure_set(v___f_3695_, 8, v___x_3694_);
v___x_3696_ = lean_alloc_closure((void*)(l_Lean_withImporting___boxed), 3, 2);
lean_closure_set(v___x_3696_, 0, lean_box(0));
lean_closure_set(v___x_3696_, 1, v___f_3695_);
v___x_3697_ = lean_box(0);
v___x_3698_ = l_Lean_profileitIOUnsafe___redArg(v___x_3425_, v___x_3034_, v___x_3696_, v___x_3697_);
if (lean_obj_tag(v___x_3698_) == 0)
{
lean_object* v_a_3699_; lean_object* v___x_3700_; lean_object* v_toEnvExtension_3701_; lean_object* v_asyncMode_3702_; uint8_t v_logWrites_3703_; lean_object* v___x_3704_; 
v_a_3699_ = lean_ctor_get(v___x_3698_, 0);
lean_inc(v_a_3699_);
lean_dec_ref_known(v___x_3698_, 1);
v___x_3700_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_3701_ = lean_ctor_get(v___x_3700_, 0);
v_asyncMode_3702_ = lean_ctor_get(v_toEnvExtension_3701_, 2);
v_logWrites_3703_ = lean_ctor_get_uint8(v_toEnvExtension_3701_, sizeof(void*)*6);
lean_inc(v_name_3012_);
v___x_3704_ = l_Lean_Environment_setMainModule(v_a_3699_, v_name_3012_);
if (v_logWrites_3703_ == 0)
{
lean_object* v___x_3705_; 
lean_inc_ref(v_toEnvExtension_3701_);
v___x_3705_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_3701_, v___x_3704_, v___f_3016_, v_asyncMode_3702_, v___x_3697_, v___x_3030_);
v___y_3613_ = v___x_3697_;
v___y_3614_ = v___x_3705_;
goto v___jp_3612_;
}
else
{
lean_object* v___x_3706_; lean_object* v___x_3707_; 
lean_inc_ref_n(v_toEnvExtension_3701_, 2);
v___x_3706_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite___redArg(v_toEnvExtension_3701_, v___x_3704_);
lean_dec_ref(v___x_3704_);
v___x_3707_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_3701_, v___x_3706_, v___f_3016_, v_asyncMode_3702_, v___x_3697_, v___x_3030_);
v___y_3613_ = v___x_3697_;
v___y_3614_ = v___x_3707_;
goto v___jp_3612_;
}
}
else
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3715_; 
lean_dec_ref(v___x_3034_);
lean_del_object(v___x_3027_);
lean_dec(v_fst_3024_);
lean_dec_ref(v___f_3016_);
lean_dec(v_name_3012_);
lean_dec(v_head_2996_);
lean_del_object(v___x_2994_);
lean_dec(v_head_2992_);
lean_del_object(v___x_2990_);
v_a_3708_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3710_ = v___x_3698_;
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3698_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3713_; 
if (v_isShared_3711_ == 0)
{
v___x_3713_ = v___x_3710_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3708_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
}
}
else
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3724_; 
lean_dec_ref(v___x_3034_);
lean_del_object(v___x_3027_);
lean_dec(v_fst_3024_);
lean_dec_ref(v___f_3016_);
lean_dec(v_importArts_3014_);
lean_dec(v_name_3012_);
lean_dec(v_head_2996_);
lean_del_object(v___x_2994_);
lean_dec(v_head_2992_);
lean_del_object(v___x_2990_);
v_a_3717_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3719_ = v___x_3424_;
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3424_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3722_; 
if (v_isShared_3720_ == 0)
{
v___x_3722_ = v___x_3719_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_a_3717_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
v___jp_3035_:
{
lean_object* v___x_3057_; lean_object* v_messages_3058_; lean_object* v_env_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3184_; 
v___x_3057_ = lean_st_ref_get(v___y_3047_);
lean_dec(v___y_3047_);
v_messages_3058_ = lean_ctor_get(v___x_3057_, 7);
v_env_3059_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3184_ == 0)
{
lean_object* v_unused_3185_; lean_object* v_unused_3186_; lean_object* v_unused_3187_; lean_object* v_unused_3188_; lean_object* v_unused_3189_; lean_object* v_unused_3190_; lean_object* v_unused_3191_; lean_object* v_unused_3192_; 
v_unused_3185_ = lean_ctor_get(v___x_3057_, 9);
lean_dec(v_unused_3185_);
v_unused_3186_ = lean_ctor_get(v___x_3057_, 8);
lean_dec(v_unused_3186_);
v_unused_3187_ = lean_ctor_get(v___x_3057_, 6);
lean_dec(v_unused_3187_);
v_unused_3188_ = lean_ctor_get(v___x_3057_, 5);
lean_dec(v_unused_3188_);
v_unused_3189_ = lean_ctor_get(v___x_3057_, 4);
lean_dec(v_unused_3189_);
v_unused_3190_ = lean_ctor_get(v___x_3057_, 3);
lean_dec(v_unused_3190_);
v_unused_3191_ = lean_ctor_get(v___x_3057_, 2);
lean_dec(v_unused_3191_);
v_unused_3192_ = lean_ctor_get(v___x_3057_, 1);
lean_dec(v_unused_3192_);
v___x_3061_ = v___x_3057_;
v_isShared_3062_ = v_isSharedCheck_3184_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_messages_3058_);
lean_inc(v_env_3059_);
lean_dec(v___x_3057_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3184_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v_unreported_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
v_unreported_3063_ = lean_ctor_get(v_messages_3058_, 1);
v___x_3064_ = lean_box(0);
v___x_3065_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_unreported_3063_, v___x_3064_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3174_; 
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3174_ == 0)
{
lean_object* v_unused_3175_; 
v_unused_3175_ = lean_ctor_get(v___x_3065_, 0);
lean_dec(v_unused_3175_);
v___x_3067_ = v___x_3065_;
v_isShared_3068_ = v_isSharedCheck_3174_;
goto v_resetjp_3066_;
}
else
{
lean_dec(v___x_3065_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3174_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
uint8_t v___x_3069_; 
v___x_3069_ = l_Lean_MessageLog_hasErrors(v_messages_3058_);
lean_dec_ref(v_messages_3058_);
if (v___x_3069_ == 0)
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
lean_del_object(v___x_3067_);
v___x_3070_ = ((lean_object*)(l_main___closed__9));
lean_inc(v_head_2992_);
v___x_3071_ = l_System_FilePath_addExtension(v_head_2992_, v___x_3070_);
lean_inc_ref(v_env_3059_);
v___x_3072_ = l___private_LeanIR_0__mkIRSigData(v_env_3059_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v_a_3073_; lean_object* v___x_3074_; 
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
lean_inc(v_a_3073_);
lean_dec_ref_known(v___x_3072_, 1);
lean_inc_ref(v_env_3059_);
v___x_3074_ = l___private_LeanIR_0__mkIRData(v_env_3059_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_object* v_a_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3080_; 
v_a_3075_ = lean_ctor_get(v___x_3074_, 0);
lean_inc(v_a_3075_);
lean_dec_ref_known(v___x_3074_, 1);
v___x_3076_ = l_Lean_Environment_mainModule(v_env_3059_);
v___x_3077_ = ((lean_object*)(l_main___closed__11));
v___x_3078_ = l_Lean_Name_append(v___x_3076_, v___x_3077_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 1, v_a_3073_);
lean_ctor_set(v___x_3027_, 0, v___x_3071_);
v___x_3080_ = v___x_3027_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___x_3071_);
lean_ctor_set(v_reuseFailAlloc_3153_, 1, v_a_3073_);
v___x_3080_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
lean_object* v___x_3082_; 
lean_inc(v_head_2992_);
if (v_isShared_2995_ == 0)
{
lean_ctor_set_tag(v___x_2994_, 0);
lean_ctor_set(v___x_2994_, 1, v_a_3075_);
v___x_3082_ = v___x_2994_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_head_2992_);
lean_ctor_set(v_reuseFailAlloc_3152_, 1, v_a_3075_);
v___x_3082_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3083_ = lean_unsigned_to_nat(2u);
v___x_3084_ = lean_mk_empty_array_with_capacity(v___x_3083_);
v___x_3085_ = lean_array_push(v___x_3084_, v___x_3080_);
v___x_3086_ = lean_array_push(v___x_3085_, v___x_3082_);
v___x_3087_ = l_Lean_saveModuleDataParts(v___x_3078_, v___x_3086_);
lean_dec_ref(v___x_3086_);
lean_dec(v___x_3078_);
if (lean_obj_tag(v___x_3087_) == 0)
{
uint8_t v___x_3088_; lean_object* v___x_3089_; 
lean_dec_ref_known(v___x_3087_, 1);
v___x_3088_ = 1;
v___x_3089_ = lean_io_prim_handle_mk(v_head_2996_, v___x_3088_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v_a_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; uint16_t v___x_3093_; lean_object* v___x_3095_; 
lean_dec(v_head_2996_);
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
lean_inc(v_a_3090_);
lean_dec_ref_known(v___x_3089_, 1);
v___x_3091_ = ((lean_object*)(l_main___closed__12));
v___x_3092_ = l_Lean_Core_getMaxHeartbeats(v___y_3056_);
v___x_3093_ = l_Lean_OptionFlags_ofOptions(v___y_3056_);
lean_inc_ref(v___y_3053_);
lean_inc_ref(v___y_3051_);
lean_inc_ref(v___y_3050_);
lean_inc_ref(v___y_3054_);
lean_inc_ref(v___y_3055_);
lean_inc_ref(v___y_3049_);
lean_inc_ref(v___y_3045_);
lean_inc(v___y_3046_);
lean_inc_ref(v_env_3059_);
if (v_isShared_3062_ == 0)
{
lean_ctor_set(v___x_3061_, 9, v___y_3053_);
lean_ctor_set(v___x_3061_, 8, v___y_3051_);
lean_ctor_set(v___x_3061_, 7, v___y_3050_);
lean_ctor_set(v___x_3061_, 6, v___y_3054_);
lean_ctor_set(v___x_3061_, 5, v___y_3055_);
lean_ctor_set(v___x_3061_, 4, v___y_3049_);
lean_ctor_set(v___x_3061_, 3, v___y_3048_);
lean_ctor_set(v___x_3061_, 2, v___y_3045_);
lean_ctor_set(v___x_3061_, 1, v___y_3046_);
v___x_3095_ = v___x_3061_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_env_3059_);
lean_ctor_set(v_reuseFailAlloc_3121_, 1, v___y_3046_);
lean_ctor_set(v_reuseFailAlloc_3121_, 2, v___y_3045_);
lean_ctor_set(v_reuseFailAlloc_3121_, 3, v___y_3048_);
lean_ctor_set(v_reuseFailAlloc_3121_, 4, v___y_3049_);
lean_ctor_set(v_reuseFailAlloc_3121_, 5, v___y_3055_);
lean_ctor_set(v_reuseFailAlloc_3121_, 6, v___y_3054_);
lean_ctor_set(v_reuseFailAlloc_3121_, 7, v___y_3050_);
lean_ctor_set(v_reuseFailAlloc_3121_, 8, v___y_3051_);
lean_ctor_set(v_reuseFailAlloc_3121_, 9, v___y_3053_);
v___x_3095_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___f_3100_; lean_object* v___x_3101_; 
v___x_3096_ = lean_box(v___x_3093_);
v___x_3097_ = lean_box(v___y_3037_);
v___x_3098_ = lean_box(v___x_3017_);
v___x_3099_ = lean_box(v___x_3069_);
lean_inc(v___y_3038_);
lean_inc(v___y_3042_);
lean_inc(v___y_3036_);
lean_inc(v___y_3039_);
lean_inc_ref(v___y_3040_);
lean_inc_ref(v___y_3043_);
lean_inc_ref(v___y_3044_);
v___f_3100_ = lean_alloc_closure((void*)(l_main___lam__2___boxed), 19, 18);
lean_closure_set(v___f_3100_, 0, v___x_3095_);
lean_closure_set(v___f_3100_, 1, v___y_3044_);
lean_closure_set(v___f_3100_, 2, v___x_3096_);
lean_closure_set(v___f_3100_, 3, v_name_3012_);
lean_closure_set(v___f_3100_, 4, v_a_3090_);
lean_closure_set(v___f_3100_, 5, v___x_3097_);
lean_closure_set(v___f_3100_, 6, v___y_3043_);
lean_closure_set(v___f_3100_, 7, v_head_2992_);
lean_closure_set(v___f_3100_, 8, v___y_3040_);
lean_closure_set(v___f_3100_, 9, v___y_3041_);
lean_closure_set(v___f_3100_, 10, v___y_3039_);
lean_closure_set(v___f_3100_, 11, v___x_3092_);
lean_closure_set(v___f_3100_, 12, v___y_3036_);
lean_closure_set(v___f_3100_, 13, v___y_3042_);
lean_closure_set(v___f_3100_, 14, v___x_3033_);
lean_closure_set(v___f_3100_, 15, v___y_3038_);
lean_closure_set(v___f_3100_, 16, v___x_3098_);
lean_closure_set(v___f_3100_, 17, v___x_3099_);
v___x_3101_ = l_Lean_profileitIOUnsafe___redArg(v___x_3091_, v___x_3034_, v___f_3100_, v___y_3052_);
lean_dec_ref(v___x_3034_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v___x_3102_; uint8_t v___x_3103_; 
lean_dec_ref_known(v___x_3101_, 1);
v___x_3102_ = lean_display_cumulative_profiling_times();
v___x_3103_ = lean_unbox(v_fst_3024_);
lean_dec(v_fst_3024_);
if (v___x_3103_ == 0)
{
lean_dec_ref(v_env_3059_);
goto v___jp_2963_;
}
else
{
lean_object* v___x_3104_; 
v___x_3104_ = l_Lean_Environment_displayStats(v_env_3059_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_dec_ref_known(v___x_3104_, 1);
goto v___jp_2963_;
}
else
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3104_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3104_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3105_);
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
}
else
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3120_; 
lean_dec_ref(v_env_3059_);
lean_dec(v_fst_3024_);
v_a_3113_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3101_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3101_);
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
else
{
lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
lean_dec_ref_known(v___x_3089_, 1);
lean_del_object(v___x_3061_);
lean_dec_ref(v_env_3059_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3041_);
lean_dec_ref(v___x_3034_);
lean_dec(v_fst_3024_);
lean_dec(v_name_3012_);
lean_dec(v_head_2992_);
v___x_3122_ = ((lean_object*)(l_main___closed__13));
v___x_3123_ = lean_string_append(v___x_3122_, v_head_2996_);
lean_dec(v_head_2996_);
v___x_3124_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__1));
v___x_3125_ = lean_string_append(v___x_3123_, v___x_3124_);
v___x_3126_ = l_IO_eprintln___at___00main_spec__6(v___x_3125_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3134_; 
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3134_ == 0)
{
lean_object* v_unused_3135_; 
v_unused_3135_ = lean_ctor_get(v___x_3126_, 0);
lean_dec(v_unused_3135_);
v___x_3128_ = v___x_3126_;
v_isShared_3129_ = v_isSharedCheck_3134_;
goto v_resetjp_3127_;
}
else
{
lean_dec(v___x_3126_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3134_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3130_; lean_object* v___x_3132_; 
v___x_3130_ = l_main___boxed__const__2;
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 0, v___x_3130_);
v___x_3132_ = v___x_3128_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v___x_3130_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
v_a_3136_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3126_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3126_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
lean_del_object(v___x_3061_);
lean_dec_ref(v_env_3059_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3041_);
lean_dec_ref(v___x_3034_);
lean_dec(v_fst_3024_);
lean_dec(v_name_3012_);
lean_dec(v_head_2996_);
lean_dec(v_head_2992_);
v_a_3144_ = lean_ctor_get(v___x_3087_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3087_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3087_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
}
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
lean_dec(v_a_3073_);
lean_dec_ref(v___x_3071_);
lean_del_object(v___x_3061_);
lean_dec_ref(v_env_3059_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3041_);
lean_dec_ref(v___x_3034_);
lean_del_object(v___x_3027_);
lean_dec(v_fst_3024_);
lean_dec(v_name_3012_);
lean_dec(v_head_2996_);
lean_del_object(v___x_2994_);
lean_dec(v_head_2992_);
v_a_3154_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_3074_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3074_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3154_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
lean_dec_ref(v___x_3071_);
lean_del_object(v___x_3061_);
lean_dec_ref(v_env_3059_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3041_);
lean_dec_ref(v___x_3034_);
lean_del_object(v___x_3027_);
lean_dec(v_fst_3024_);
lean_dec(v_name_3012_);
lean_dec(v_head_2996_);
lean_del_object(v___x_2994_);
lean_dec(v_head_2992_);
v_a_3162_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3072_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3072_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
else
{
lean_object* v___x_3170_; lean_object* v___x_3172_; 
lean_del_object(v___x_3061_);
lean_dec_ref(v_env_3059_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3041_);
lean_dec_ref(v___x_3034_);
lean_del_object(v___x_3027_);
lean_dec(v_fst_3024_);
lean_dec(v_name_3012_);
lean_dec(v_head_2996_);
lean_del_object(v___x_2994_);
lean_dec(v_head_2992_);
v___x_3170_ = l_main___boxed__const__2;
if (v_isShared_3068_ == 0)
{
lean_ctor_set(v___x_3067_, 0, v___x_3170_);
v___x_3172_ = v___x_3067_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v___x_3170_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
}
}
else
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3183_; 
lean_del_object(v___x_3061_);
lean_dec_ref(v_env_3059_);
lean_dec_ref(v_messages_3058_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3041_);
lean_dec_ref(v___x_3034_);
lean_del_object(v___x_3027_);
lean_dec(v_fst_3024_);
lean_dec(v_name_3012_);
lean_dec(v_head_2996_);
lean_del_object(v___x_2994_);
lean_dec(v_head_2992_);
v_a_3176_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3178_ = v___x_3065_;
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3065_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3181_; 
if (v_isShared_3179_ == 0)
{
v___x_3181_ = v___x_3178_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_a_3176_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
}
}
}
v___jp_3193_:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; size_t v_sz_3230_; size_t v___x_3231_; lean_object* v___x_3232_; 
lean_inc_ref(v___y_3218_);
v___x_3227_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3227_, 0, v___y_3226_);
lean_ctor_set(v___x_3227_, 1, v_nextMacroScope_3209_);
lean_ctor_set(v___x_3227_, 2, v_ngen_3210_);
lean_ctor_set(v___x_3227_, 3, v_auxDeclNGen_3211_);
lean_ctor_set(v___x_3227_, 4, v_traceState_3212_);
lean_ctor_set(v___x_3227_, 5, v___y_3218_);
lean_ctor_set(v___x_3227_, 6, v_recordedDeps_3213_);
lean_ctor_set(v___x_3227_, 7, v_messages_3214_);
lean_ctor_set(v___x_3227_, 8, v_infoState_3215_);
lean_ctor_set(v___x_3227_, 9, v_snapshotTasks_3216_);
v___x_3228_ = lean_st_ref_put(v___y_3222_, v___x_3227_);
v___x_3229_ = lean_box(0);
v_sz_3230_ = lean_array_size(v___y_3219_);
v___x_3231_ = ((size_t)0ULL);
v___x_3232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(v___y_3219_, v_sz_3230_, v___x_3231_, v___x_3229_, v___y_3207_, v___y_3222_);
lean_dec_ref(v___y_3219_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_dec_ref_known(v___x_3232_, 1);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3207_);
v___y_3036_ = v___y_3195_;
v___y_3037_ = v___y_3194_;
v___y_3038_ = v___y_3196_;
v___y_3039_ = v___y_3197_;
v___y_3040_ = v___y_3198_;
v___y_3041_ = v___y_3199_;
v___y_3042_ = v___y_3200_;
v___y_3043_ = v___y_3201_;
v___y_3044_ = v___y_3202_;
v___y_3045_ = v___y_3203_;
v___y_3046_ = v___y_3220_;
v___y_3047_ = v___y_3221_;
v___y_3048_ = v___y_3204_;
v___y_3049_ = v___y_3223_;
v___y_3050_ = v___y_3205_;
v___y_3051_ = v___y_3224_;
v___y_3052_ = v___y_3206_;
v___y_3053_ = v___y_3208_;
v___y_3054_ = v___y_3217_;
v___y_3055_ = v___y_3218_;
v___y_3056_ = v___y_3225_;
goto v___jp_3035_;
}
else
{
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_dec_ref_known(v___x_3232_, 1);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3207_);
v___y_3036_ = v___y_3195_;
v___y_3037_ = v___y_3194_;
v___y_3038_ = v___y_3196_;
v___y_3039_ = v___y_3197_;
v___y_3040_ = v___y_3198_;
v___y_3041_ = v___y_3199_;
v___y_3042_ = v___y_3200_;
v___y_3043_ = v___y_3201_;
v___y_3044_ = v___y_3202_;
v___y_3045_ = v___y_3203_;
v___y_3046_ = v___y_3220_;
v___y_3047_ = v___y_3221_;
v___y_3048_ = v___y_3204_;
v___y_3049_ = v___y_3223_;
v___y_3050_ = v___y_3205_;
v___y_3051_ = v___y_3224_;
v___y_3052_ = v___y_3206_;
v___y_3053_ = v___y_3208_;
v___y_3054_ = v___y_3217_;
v___y_3055_ = v___y_3218_;
v___y_3056_ = v___y_3225_;
goto v___jp_3035_;
}
else
{
lean_object* v_a_3233_; uint8_t v___x_3234_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_a_3233_);
lean_dec_ref_known(v___x_3232_, 1);
v___x_3234_ = l_Lean_Exception_isInterrupt(v_a_3233_);
if (v___x_3234_ == 0)
{
lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3235_ = l_Lean_Exception_toMessageData(v_a_3233_);
v___x_3236_ = l_Lean_logError___at___00main_spec__13(v___x_3235_, v___y_3207_, v___y_3222_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3207_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_dec_ref_known(v___x_3236_, 1);
v___y_3036_ = v___y_3195_;
v___y_3037_ = v___y_3194_;
v___y_3038_ = v___y_3196_;
v___y_3039_ = v___y_3197_;
v___y_3040_ = v___y_3198_;
v___y_3041_ = v___y_3199_;
v___y_3042_ = v___y_3200_;
v___y_3043_ = v___y_3201_;
v___y_3044_ = v___y_3202_;
v___y_3045_ = v___y_3203_;
v___y_3046_ = v___y_3220_;
v___y_3047_ = v___y_3221_;
v___y_3048_ = v___y_3204_;
v___y_3049_ = v___y_3223_;
v___y_3050_ = v___y_3205_;
v___y_3051_ = v___y_3224_;
v___y_3052_ = v___y_3206_;
v___y_3053_ = v___y_3208_;
v___y_3054_ = v___y_3217_;
v___y_3055_ = v___y_3218_;
v___y_3056_ = v___y_3225_;
goto v___jp_3035_;
}
else
{
lean_object* v___x_3237_; lean_object* v___x_3238_; 
lean_dec_ref_known(v___x_3236_, 1);
lean_dec(v___y_3221_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3199_);
lean_dec_ref(v___x_3034_);
lean_del_object(v___x_3027_);
lean_dec(v_fst_3024_);
lean_dec(v_name_3012_);
lean_dec(v_head_2996_);
lean_del_object(v___x_2994_);
lean_dec(v_head_2992_);
v___x_3237_ = lean_obj_once(&l_main___closed__17, &l_main___closed__17_once, _init_l_main___closed__17);
v___x_3238_ = l_panic___at___00main_spec__5(v___x_3237_);
return v___x_3238_;
}
}
else
{
lean_dec(v_a_3233_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3207_);
v___y_3036_ = v___y_3195_;
v___y_3037_ = v___y_3194_;
v___y_3038_ = v___y_3196_;
v___y_3039_ = v___y_3197_;
v___y_3040_ = v___y_3198_;
v___y_3041_ = v___y_3199_;
v___y_3042_ = v___y_3200_;
v___y_3043_ = v___y_3201_;
v___y_3044_ = v___y_3202_;
v___y_3045_ = v___y_3203_;
v___y_3046_ = v___y_3220_;
v___y_3047_ = v___y_3221_;
v___y_3048_ = v___y_3204_;
v___y_3049_ = v___y_3223_;
v___y_3050_ = v___y_3205_;
v___y_3051_ = v___y_3224_;
v___y_3052_ = v___y_3206_;
v___y_3053_ = v___y_3208_;
v___y_3054_ = v___y_3217_;
v___y_3055_ = v___y_3218_;
v___y_3056_ = v___y_3225_;
goto v___jp_3035_;
}
}
}
}
v___jp_3239_:
{
lean_object* v_toCold_3266_; lean_object* v_currRecDepth_3267_; lean_object* v_ref_3268_; uint8_t v_suppressElabErrors_3269_; uint8_t v_isRecordingDeps_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3321_; 
v_toCold_3266_ = lean_ctor_get(v___y_3264_, 0);
v_currRecDepth_3267_ = lean_ctor_get(v___y_3264_, 1);
v_ref_3268_ = lean_ctor_get(v___y_3264_, 2);
v_suppressElabErrors_3269_ = lean_ctor_get_uint8(v___y_3264_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3270_ = lean_ctor_get_uint8(v___y_3264_, sizeof(void*)*3 + 3);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___y_3264_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3272_ = v___y_3264_;
v_isShared_3273_ = v_isSharedCheck_3321_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_ref_3268_);
lean_inc(v_currRecDepth_3267_);
lean_inc(v_toCold_3266_);
lean_dec(v___y_3264_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3321_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v_fileName_3274_; lean_object* v_fileMap_3275_; lean_object* v_currNamespace_3276_; lean_object* v_openDecls_3277_; lean_object* v_initHeartbeats_3278_; lean_object* v_maxHeartbeats_3279_; lean_object* v_quotContext_3280_; lean_object* v_currMacroScope_3281_; lean_object* v_cancelTk_x3f_3282_; lean_object* v_inheritedTraceOptions_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3318_; 
v_fileName_3274_ = lean_ctor_get(v_toCold_3266_, 0);
v_fileMap_3275_ = lean_ctor_get(v_toCold_3266_, 1);
v_currNamespace_3276_ = lean_ctor_get(v_toCold_3266_, 4);
v_openDecls_3277_ = lean_ctor_get(v_toCold_3266_, 5);
v_initHeartbeats_3278_ = lean_ctor_get(v_toCold_3266_, 6);
v_maxHeartbeats_3279_ = lean_ctor_get(v_toCold_3266_, 7);
v_quotContext_3280_ = lean_ctor_get(v_toCold_3266_, 8);
v_currMacroScope_3281_ = lean_ctor_get(v_toCold_3266_, 9);
v_cancelTk_x3f_3282_ = lean_ctor_get(v_toCold_3266_, 10);
v_inheritedTraceOptions_3283_ = lean_ctor_get(v_toCold_3266_, 11);
v_isSharedCheck_3318_ = !lean_is_exclusive(v_toCold_3266_);
if (v_isSharedCheck_3318_ == 0)
{
lean_object* v_unused_3319_; lean_object* v_unused_3320_; 
v_unused_3319_ = lean_ctor_get(v_toCold_3266_, 3);
lean_dec(v_unused_3319_);
v_unused_3320_ = lean_ctor_get(v_toCold_3266_, 2);
lean_dec(v_unused_3320_);
v___x_3285_ = v_toCold_3266_;
v_isShared_3286_ = v_isSharedCheck_3318_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_inheritedTraceOptions_3283_);
lean_inc(v_cancelTk_x3f_3282_);
lean_inc(v_currMacroScope_3281_);
lean_inc(v_quotContext_3280_);
lean_inc(v_maxHeartbeats_3279_);
lean_inc(v_initHeartbeats_3278_);
lean_inc(v_openDecls_3277_);
lean_inc(v_currNamespace_3276_);
lean_inc(v_fileMap_3275_);
lean_inc(v_fileName_3274_);
lean_dec(v_toCold_3266_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3318_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3290_; 
v___x_3287_ = l_Lean_maxRecDepth;
v___x_3288_ = l_Lean_Option_get___at___00main_spec__8(v___x_3034_, v___x_3287_);
lean_inc_ref(v___x_3034_);
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 3, v___x_3288_);
lean_ctor_set(v___x_3285_, 2, v___x_3034_);
v___x_3290_ = v___x_3285_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_fileName_3274_);
lean_ctor_set(v_reuseFailAlloc_3317_, 1, v_fileMap_3275_);
lean_ctor_set(v_reuseFailAlloc_3317_, 2, v___x_3034_);
lean_ctor_set(v_reuseFailAlloc_3317_, 3, v___x_3288_);
lean_ctor_set(v_reuseFailAlloc_3317_, 4, v_currNamespace_3276_);
lean_ctor_set(v_reuseFailAlloc_3317_, 5, v_openDecls_3277_);
lean_ctor_set(v_reuseFailAlloc_3317_, 6, v_initHeartbeats_3278_);
lean_ctor_set(v_reuseFailAlloc_3317_, 7, v_maxHeartbeats_3279_);
lean_ctor_set(v_reuseFailAlloc_3317_, 8, v_quotContext_3280_);
lean_ctor_set(v_reuseFailAlloc_3317_, 9, v_currMacroScope_3281_);
lean_ctor_set(v_reuseFailAlloc_3317_, 10, v_cancelTk_x3f_3282_);
lean_ctor_set(v_reuseFailAlloc_3317_, 11, v_inheritedTraceOptions_3283_);
v___x_3290_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
lean_object* v___x_3292_; 
if (v_isShared_3273_ == 0)
{
lean_ctor_set(v___x_3272_, 0, v___x_3290_);
v___x_3292_ = v___x_3272_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3290_);
lean_ctor_set(v_reuseFailAlloc_3316_, 1, v_currRecDepth_3267_);
lean_ctor_set(v_reuseFailAlloc_3316_, 2, v_ref_3268_);
lean_ctor_set_uint8(v_reuseFailAlloc_3316_, sizeof(void*)*3 + 2, v_suppressElabErrors_3269_);
lean_ctor_set_uint8(v_reuseFailAlloc_3316_, sizeof(void*)*3 + 3, v_isRecordingDeps_3270_);
v___x_3292_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
lean_object* v___x_3293_; lean_object* v_env_3294_; lean_object* v_nextMacroScope_3295_; lean_object* v_ngen_3296_; lean_object* v_auxDeclNGen_3297_; lean_object* v_traceState_3298_; lean_object* v_recordedDeps_3299_; lean_object* v_messages_3300_; lean_object* v_infoState_3301_; lean_object* v_snapshotTasks_3302_; lean_object* v___x_3303_; uint8_t v___x_3304_; 
lean_ctor_set_uint16(v___x_3292_, sizeof(void*)*3, v___y_3262_);
v___x_3293_ = lean_st_ref_take(v___y_3265_);
v_env_3294_ = lean_ctor_get(v___x_3293_, 0);
lean_inc_ref(v_env_3294_);
v_nextMacroScope_3295_ = lean_ctor_get(v___x_3293_, 1);
lean_inc(v_nextMacroScope_3295_);
v_ngen_3296_ = lean_ctor_get(v___x_3293_, 2);
lean_inc_ref(v_ngen_3296_);
v_auxDeclNGen_3297_ = lean_ctor_get(v___x_3293_, 3);
lean_inc_ref(v_auxDeclNGen_3297_);
v_traceState_3298_ = lean_ctor_get(v___x_3293_, 4);
lean_inc_ref(v_traceState_3298_);
v_recordedDeps_3299_ = lean_ctor_get(v___x_3293_, 6);
lean_inc_ref(v_recordedDeps_3299_);
v_messages_3300_ = lean_ctor_get(v___x_3293_, 7);
lean_inc_ref(v_messages_3300_);
v_infoState_3301_ = lean_ctor_get(v___x_3293_, 8);
lean_inc_ref(v_infoState_3301_);
v_snapshotTasks_3302_ = lean_ctor_get(v___x_3293_, 9);
lean_inc_ref(v_snapshotTasks_3302_);
lean_dec(v___x_3293_);
v___x_3303_ = lean_array_get_size(v___y_3257_);
v___x_3304_ = lean_nat_dec_lt(v___x_3033_, v___x_3303_);
if (v___x_3304_ == 0)
{
lean_object* v___x_3305_; 
lean_inc_ref(v___y_3251_);
v___x_3305_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3251_, v_env_3294_, v___x_3008_);
v___y_3194_ = v___y_3241_;
v___y_3195_ = v___y_3240_;
v___y_3196_ = v___y_3242_;
v___y_3197_ = v___y_3243_;
v___y_3198_ = v___y_3244_;
v___y_3199_ = v___y_3245_;
v___y_3200_ = v___y_3246_;
v___y_3201_ = v___y_3247_;
v___y_3202_ = v___y_3248_;
v___y_3203_ = v___y_3249_;
v___y_3204_ = v___y_3250_;
v___y_3205_ = v___y_3252_;
v___y_3206_ = v___y_3253_;
v___y_3207_ = v___x_3292_;
v___y_3208_ = v___y_3254_;
v_nextMacroScope_3209_ = v_nextMacroScope_3295_;
v_ngen_3210_ = v_ngen_3296_;
v_auxDeclNGen_3211_ = v_auxDeclNGen_3297_;
v_traceState_3212_ = v_traceState_3298_;
v_recordedDeps_3213_ = v_recordedDeps_3299_;
v_messages_3214_ = v_messages_3300_;
v_infoState_3215_ = v_infoState_3301_;
v_snapshotTasks_3216_ = v_snapshotTasks_3302_;
v___y_3217_ = v___y_3255_;
v___y_3218_ = v___y_3256_;
v___y_3219_ = v___y_3257_;
v___y_3220_ = v___y_3258_;
v___y_3221_ = v___y_3259_;
v___y_3222_ = v___y_3265_;
v___y_3223_ = v___y_3260_;
v___y_3224_ = v___y_3261_;
v___y_3225_ = v___y_3263_;
v___y_3226_ = v___x_3305_;
goto v___jp_3193_;
}
else
{
uint8_t v___x_3306_; 
v___x_3306_ = lean_nat_dec_le(v___x_3303_, v___x_3303_);
if (v___x_3306_ == 0)
{
if (v___x_3304_ == 0)
{
lean_object* v___x_3307_; 
lean_inc_ref(v___y_3251_);
v___x_3307_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3251_, v_env_3294_, v___x_3008_);
v___y_3194_ = v___y_3241_;
v___y_3195_ = v___y_3240_;
v___y_3196_ = v___y_3242_;
v___y_3197_ = v___y_3243_;
v___y_3198_ = v___y_3244_;
v___y_3199_ = v___y_3245_;
v___y_3200_ = v___y_3246_;
v___y_3201_ = v___y_3247_;
v___y_3202_ = v___y_3248_;
v___y_3203_ = v___y_3249_;
v___y_3204_ = v___y_3250_;
v___y_3205_ = v___y_3252_;
v___y_3206_ = v___y_3253_;
v___y_3207_ = v___x_3292_;
v___y_3208_ = v___y_3254_;
v_nextMacroScope_3209_ = v_nextMacroScope_3295_;
v_ngen_3210_ = v_ngen_3296_;
v_auxDeclNGen_3211_ = v_auxDeclNGen_3297_;
v_traceState_3212_ = v_traceState_3298_;
v_recordedDeps_3213_ = v_recordedDeps_3299_;
v_messages_3214_ = v_messages_3300_;
v_infoState_3215_ = v_infoState_3301_;
v_snapshotTasks_3216_ = v_snapshotTasks_3302_;
v___y_3217_ = v___y_3255_;
v___y_3218_ = v___y_3256_;
v___y_3219_ = v___y_3257_;
v___y_3220_ = v___y_3258_;
v___y_3221_ = v___y_3259_;
v___y_3222_ = v___y_3265_;
v___y_3223_ = v___y_3260_;
v___y_3224_ = v___y_3261_;
v___y_3225_ = v___y_3263_;
v___y_3226_ = v___x_3307_;
goto v___jp_3193_;
}
else
{
size_t v___x_3308_; size_t v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3308_ = ((size_t)0ULL);
v___x_3309_ = lean_usize_of_nat(v___x_3303_);
v___x_3310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v___y_3257_, v___x_3308_, v___x_3309_, v___x_3008_);
lean_inc_ref(v___y_3251_);
v___x_3311_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3251_, v_env_3294_, v___x_3310_);
v___y_3194_ = v___y_3241_;
v___y_3195_ = v___y_3240_;
v___y_3196_ = v___y_3242_;
v___y_3197_ = v___y_3243_;
v___y_3198_ = v___y_3244_;
v___y_3199_ = v___y_3245_;
v___y_3200_ = v___y_3246_;
v___y_3201_ = v___y_3247_;
v___y_3202_ = v___y_3248_;
v___y_3203_ = v___y_3249_;
v___y_3204_ = v___y_3250_;
v___y_3205_ = v___y_3252_;
v___y_3206_ = v___y_3253_;
v___y_3207_ = v___x_3292_;
v___y_3208_ = v___y_3254_;
v_nextMacroScope_3209_ = v_nextMacroScope_3295_;
v_ngen_3210_ = v_ngen_3296_;
v_auxDeclNGen_3211_ = v_auxDeclNGen_3297_;
v_traceState_3212_ = v_traceState_3298_;
v_recordedDeps_3213_ = v_recordedDeps_3299_;
v_messages_3214_ = v_messages_3300_;
v_infoState_3215_ = v_infoState_3301_;
v_snapshotTasks_3216_ = v_snapshotTasks_3302_;
v___y_3217_ = v___y_3255_;
v___y_3218_ = v___y_3256_;
v___y_3219_ = v___y_3257_;
v___y_3220_ = v___y_3258_;
v___y_3221_ = v___y_3259_;
v___y_3222_ = v___y_3265_;
v___y_3223_ = v___y_3260_;
v___y_3224_ = v___y_3261_;
v___y_3225_ = v___y_3263_;
v___y_3226_ = v___x_3311_;
goto v___jp_3193_;
}
}
else
{
size_t v___x_3312_; size_t v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3312_ = ((size_t)0ULL);
v___x_3313_ = lean_usize_of_nat(v___x_3303_);
v___x_3314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v___y_3257_, v___x_3312_, v___x_3313_, v___x_3008_);
lean_inc_ref(v___y_3251_);
v___x_3315_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3251_, v_env_3294_, v___x_3314_);
v___y_3194_ = v___y_3241_;
v___y_3195_ = v___y_3240_;
v___y_3196_ = v___y_3242_;
v___y_3197_ = v___y_3243_;
v___y_3198_ = v___y_3244_;
v___y_3199_ = v___y_3245_;
v___y_3200_ = v___y_3246_;
v___y_3201_ = v___y_3247_;
v___y_3202_ = v___y_3248_;
v___y_3203_ = v___y_3249_;
v___y_3204_ = v___y_3250_;
v___y_3205_ = v___y_3252_;
v___y_3206_ = v___y_3253_;
v___y_3207_ = v___x_3292_;
v___y_3208_ = v___y_3254_;
v_nextMacroScope_3209_ = v_nextMacroScope_3295_;
v_ngen_3210_ = v_ngen_3296_;
v_auxDeclNGen_3211_ = v_auxDeclNGen_3297_;
v_traceState_3212_ = v_traceState_3298_;
v_recordedDeps_3213_ = v_recordedDeps_3299_;
v_messages_3214_ = v_messages_3300_;
v_infoState_3215_ = v_infoState_3301_;
v_snapshotTasks_3216_ = v_snapshotTasks_3302_;
v___y_3217_ = v___y_3255_;
v___y_3218_ = v___y_3256_;
v___y_3219_ = v___y_3257_;
v___y_3220_ = v___y_3258_;
v___y_3221_ = v___y_3259_;
v___y_3222_ = v___y_3265_;
v___y_3223_ = v___y_3260_;
v___y_3224_ = v___y_3261_;
v___y_3225_ = v___y_3263_;
v___y_3226_ = v___x_3315_;
goto v___jp_3193_;
}
}
}
}
}
}
}
v___jp_3322_:
{
lean_object* v___x_3349_; lean_object* v_env_3350_; lean_object* v_nextMacroScope_3351_; lean_object* v_ngen_3352_; lean_object* v_auxDeclNGen_3353_; lean_object* v_traceState_3354_; lean_object* v_recordedDeps_3355_; lean_object* v_messages_3356_; lean_object* v_infoState_3357_; lean_object* v_snapshotTasks_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3367_; 
v___x_3349_ = lean_st_ref_take(v___y_3343_);
v_env_3350_ = lean_ctor_get(v___x_3349_, 0);
v_nextMacroScope_3351_ = lean_ctor_get(v___x_3349_, 1);
v_ngen_3352_ = lean_ctor_get(v___x_3349_, 2);
v_auxDeclNGen_3353_ = lean_ctor_get(v___x_3349_, 3);
v_traceState_3354_ = lean_ctor_get(v___x_3349_, 4);
v_recordedDeps_3355_ = lean_ctor_get(v___x_3349_, 6);
v_messages_3356_ = lean_ctor_get(v___x_3349_, 7);
v_infoState_3357_ = lean_ctor_get(v___x_3349_, 8);
v_snapshotTasks_3358_ = lean_ctor_get(v___x_3349_, 9);
v_isSharedCheck_3367_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3367_ == 0)
{
lean_object* v_unused_3368_; 
v_unused_3368_ = lean_ctor_get(v___x_3349_, 5);
lean_dec(v_unused_3368_);
v___x_3360_ = v___x_3349_;
v_isShared_3361_ = v_isSharedCheck_3367_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_snapshotTasks_3358_);
lean_inc(v_infoState_3357_);
lean_inc(v_messages_3356_);
lean_inc(v_recordedDeps_3355_);
lean_inc(v_traceState_3354_);
lean_inc(v_auxDeclNGen_3353_);
lean_inc(v_ngen_3352_);
lean_inc(v_nextMacroScope_3351_);
lean_inc(v_env_3350_);
lean_dec(v___x_3349_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3367_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3362_; lean_object* v___x_3364_; 
v___x_3362_ = l_Lean_Kernel_enableDiag(v_env_3350_, v___y_3347_);
lean_inc_ref(v___y_3338_);
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 5, v___y_3338_);
lean_ctor_set(v___x_3360_, 0, v___x_3362_);
v___x_3364_ = v___x_3360_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v___x_3362_);
lean_ctor_set(v_reuseFailAlloc_3366_, 1, v_nextMacroScope_3351_);
lean_ctor_set(v_reuseFailAlloc_3366_, 2, v_ngen_3352_);
lean_ctor_set(v_reuseFailAlloc_3366_, 3, v_auxDeclNGen_3353_);
lean_ctor_set(v_reuseFailAlloc_3366_, 4, v_traceState_3354_);
lean_ctor_set(v_reuseFailAlloc_3366_, 5, v___y_3338_);
lean_ctor_set(v_reuseFailAlloc_3366_, 6, v_recordedDeps_3355_);
lean_ctor_set(v_reuseFailAlloc_3366_, 7, v_messages_3356_);
lean_ctor_set(v_reuseFailAlloc_3366_, 8, v_infoState_3357_);
lean_ctor_set(v_reuseFailAlloc_3366_, 9, v_snapshotTasks_3358_);
v___x_3364_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
lean_object* v___x_3365_; 
v___x_3365_ = lean_st_ref_put(v___y_3343_, v___x_3364_);
lean_inc(v___y_3343_);
v___y_3240_ = v___y_3324_;
v___y_3241_ = v___y_3323_;
v___y_3242_ = v___y_3325_;
v___y_3243_ = v___y_3326_;
v___y_3244_ = v___y_3327_;
v___y_3245_ = v___y_3328_;
v___y_3246_ = v___y_3329_;
v___y_3247_ = v___y_3330_;
v___y_3248_ = v___y_3331_;
v___y_3249_ = v___y_3332_;
v___y_3250_ = v___y_3333_;
v___y_3251_ = v___y_3334_;
v___y_3252_ = v___y_3335_;
v___y_3253_ = v___y_3336_;
v___y_3254_ = v___y_3337_;
v___y_3255_ = v___y_3339_;
v___y_3256_ = v___y_3338_;
v___y_3257_ = v___y_3342_;
v___y_3258_ = v___y_3341_;
v___y_3259_ = v___y_3343_;
v___y_3260_ = v___y_3344_;
v___y_3261_ = v___y_3345_;
v___y_3262_ = v___y_3346_;
v___y_3263_ = v___y_3348_;
v___y_3264_ = v___y_3340_;
v___y_3265_ = v___y_3343_;
goto v___jp_3239_;
}
}
}
v___jp_3369_:
{
if (v___y_3396_ == 0)
{
v___y_3323_ = v___y_3371_;
v___y_3324_ = v___y_3370_;
v___y_3325_ = v___y_3372_;
v___y_3326_ = v___y_3373_;
v___y_3327_ = v___y_3374_;
v___y_3328_ = v___y_3375_;
v___y_3329_ = v___y_3376_;
v___y_3330_ = v___y_3377_;
v___y_3331_ = v___y_3378_;
v___y_3332_ = v___y_3379_;
v___y_3333_ = v___y_3380_;
v___y_3334_ = v___y_3381_;
v___y_3335_ = v___y_3382_;
v___y_3336_ = v___y_3383_;
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
goto v___jp_3322_;
}
else
{
lean_inc(v___y_3390_);
v___y_3240_ = v___y_3370_;
v___y_3241_ = v___y_3371_;
v___y_3242_ = v___y_3372_;
v___y_3243_ = v___y_3373_;
v___y_3244_ = v___y_3374_;
v___y_3245_ = v___y_3375_;
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
v___y_3256_ = v___y_3385_;
v___y_3257_ = v___y_3389_;
v___y_3258_ = v___y_3388_;
v___y_3259_ = v___y_3390_;
v___y_3260_ = v___y_3391_;
v___y_3261_ = v___y_3392_;
v___y_3262_ = v___y_3393_;
v___y_3263_ = v___y_3395_;
v___y_3264_ = v___y_3387_;
v___y_3265_ = v___y_3390_;
goto v___jp_3239_;
}
}
v___jp_3397_:
{
if (v___y_3422_ == 0)
{
v___y_3370_ = v___y_3409_;
v___y_3371_ = v___y_3399_;
v___y_3372_ = v___y_3400_;
v___y_3373_ = v___y_3411_;
v___y_3374_ = v___y_3403_;
v___y_3375_ = v___y_3404_;
v___y_3376_ = v___y_3405_;
v___y_3377_ = v___y_3406_;
v___y_3378_ = v___y_3413_;
v___y_3379_ = v___y_3398_;
v___y_3380_ = v___y_3401_;
v___y_3381_ = v___y_3402_;
v___y_3382_ = v___y_3415_;
v___y_3383_ = v___y_3416_;
v___y_3384_ = v___y_3417_;
v___y_3385_ = v___y_3406_;
v___y_3386_ = v___y_3418_;
v___y_3387_ = v___y_3419_;
v___y_3388_ = v___y_3407_;
v___y_3389_ = v___y_3408_;
v___y_3390_ = v___y_3420_;
v___y_3391_ = v___y_3410_;
v___y_3392_ = v___y_3421_;
v___y_3393_ = v___y_3412_;
v___y_3394_ = v___y_3423_;
v___y_3395_ = v___y_3413_;
v___y_3396_ = v___y_3414_;
goto v___jp_3369_;
}
else
{
v___y_3323_ = v___y_3399_;
v___y_3324_ = v___y_3409_;
v___y_3325_ = v___y_3400_;
v___y_3326_ = v___y_3411_;
v___y_3327_ = v___y_3403_;
v___y_3328_ = v___y_3404_;
v___y_3329_ = v___y_3405_;
v___y_3330_ = v___y_3406_;
v___y_3331_ = v___y_3413_;
v___y_3332_ = v___y_3398_;
v___y_3333_ = v___y_3401_;
v___y_3334_ = v___y_3402_;
v___y_3335_ = v___y_3415_;
v___y_3336_ = v___y_3416_;
v___y_3337_ = v___y_3417_;
v___y_3338_ = v___y_3406_;
v___y_3339_ = v___y_3418_;
v___y_3340_ = v___y_3419_;
v___y_3341_ = v___y_3407_;
v___y_3342_ = v___y_3408_;
v___y_3343_ = v___y_3420_;
v___y_3344_ = v___y_3410_;
v___y_3345_ = v___y_3421_;
v___y_3346_ = v___y_3412_;
v___y_3347_ = v___y_3423_;
v___y_3348_ = v___y_3413_;
goto v___jp_3322_;
}
}
}
}
else
{
lean_object* v_a_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3733_; 
lean_dec_ref(v___f_3016_);
lean_dec(v_importArts_3014_);
lean_dec(v_name_3012_);
lean_dec(v_head_2996_);
lean_del_object(v___x_2994_);
lean_dec(v_head_2992_);
lean_del_object(v___x_2990_);
v_a_3726_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3728_ = v___x_3022_;
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
else
{
lean_inc(v_a_3726_);
lean_dec(v___x_3022_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
lean_object* v___x_3731_; 
if (v_isShared_3729_ == 0)
{
v___x_3731_ = v___x_3728_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v_a_3726_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
}
}
else
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
lean_del_object(v___x_2999_);
lean_dec(v_tail_2997_);
lean_dec(v_head_2996_);
lean_del_object(v___x_2994_);
lean_dec(v_head_2992_);
lean_del_object(v___x_2990_);
v_a_3735_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3737_ = v___x_3010_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3010_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3735_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_tail_2986_, 2);
lean_dec(v_tail_2987_);
lean_dec_ref_known(v_args_2961_, 2);
goto v___jp_2966_;
}
}
else
{
lean_dec(v_tail_2986_);
lean_dec_ref_known(v_args_2961_, 2);
goto v___jp_2966_;
}
}
else
{
lean_dec(v_args_2961_);
goto v___jp_2966_;
}
v___jp_2963_:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2964_ = l_main___boxed__const__1;
v___x_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
return v___x_2965_;
}
v___jp_2966_:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2967_ = ((lean_object*)(l_main___closed__0));
v___x_2968_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_2967_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2976_; 
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_2976_ == 0)
{
lean_object* v_unused_2977_; 
v_unused_2977_ = lean_ctor_get(v___x_2968_, 0);
lean_dec(v_unused_2977_);
v___x_2970_ = v___x_2968_;
v_isShared_2971_ = v_isSharedCheck_2976_;
goto v_resetjp_2969_;
}
else
{
lean_dec(v___x_2968_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2976_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2972_; lean_object* v___x_2974_; 
v___x_2972_ = l_main___boxed__const__2;
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 0, v___x_2972_);
v___x_2974_ = v___x_2970_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2972_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
else
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
v_a_2978_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v___x_2968_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2968_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_a_2978_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_3748_, lean_object* v_a_3749_){
_start:
{
lean_object* v_res_3750_; 
v_res_3750_ = _lean_main(v_args_3748_);
return v_res_3750_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object* v_as_3751_, lean_object* v_as_x27_3752_, lean_object* v_b_3753_, lean_object* v_a_3754_){
_start:
{
lean_object* v___x_3756_; 
v___x_3756_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_3752_, v_b_3753_);
return v___x_3756_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object* v_as_3757_, lean_object* v_as_x27_3758_, lean_object* v_b_3759_, lean_object* v_a_3760_, lean_object* v___y_3761_){
_start:
{
lean_object* v_res_3762_; 
v_res_3762_ = l_List_forIn_x27_loop___at___00main_spec__1(v_as_3757_, v_as_x27_3758_, v_b_3759_, v_a_3760_);
lean_dec(v_as_x27_3758_);
lean_dec(v_as_3757_);
return v_res_3762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16(lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
lean_object* v___x_3766_; 
v___x_3766_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___y_3764_);
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___boxed(lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_){
_start:
{
lean_object* v_res_3770_; 
v_res_3770_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16(v___y_3767_, v___y_3768_);
lean_dec(v___y_3768_);
lean_dec_ref(v___y_3767_);
return v_res_3770_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17(lean_object* v_00_u03b2_3771_, lean_object* v_m_3772_, lean_object* v_a_3773_, lean_object* v_fallback_3774_){
_start:
{
lean_object* v___x_3775_; 
v___x_3775_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_m_3772_, v_a_3773_, v_fallback_3774_);
return v___x_3775_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___boxed(lean_object* v_00_u03b2_3776_, lean_object* v_m_3777_, lean_object* v_a_3778_, lean_object* v_fallback_3779_){
_start:
{
lean_object* v_res_3780_; 
v_res_3780_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17(v_00_u03b2_3776_, v_m_3777_, v_a_3778_, v_fallback_3779_);
lean_dec(v_fallback_3779_);
lean_dec_ref(v_a_3778_);
lean_dec_ref(v_m_3777_);
return v_res_3780_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18(lean_object* v_00_u03b2_3781_, lean_object* v_m_3782_, lean_object* v_a_3783_, lean_object* v_b_3784_){
_start:
{
lean_object* v___x_3785_; 
v___x_3785_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_m_3782_, v_a_3783_, v_b_3784_);
return v___x_3785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21(lean_object* v_n_3786_, lean_object* v_as_3787_, lean_object* v_lo_3788_, lean_object* v_hi_3789_, lean_object* v_w_3790_, lean_object* v_hlo_3791_, lean_object* v_hhi_3792_){
_start:
{
lean_object* v___x_3793_; 
v___x_3793_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v_n_3786_, v_as_3787_, v_lo_3788_, v_hi_3789_);
return v___x_3793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___boxed(lean_object* v_n_3794_, lean_object* v_as_3795_, lean_object* v_lo_3796_, lean_object* v_hi_3797_, lean_object* v_w_3798_, lean_object* v_hlo_3799_, lean_object* v_hhi_3800_){
_start:
{
lean_object* v_res_3801_; 
v_res_3801_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21(v_n_3794_, v_as_3795_, v_lo_3796_, v_hi_3797_, v_w_3798_, v_hlo_3799_, v_hhi_3800_);
lean_dec(v_hi_3797_);
lean_dec(v_n_3794_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21(lean_object* v_00_u03b2_3802_, lean_object* v_a_3803_, lean_object* v_fallback_3804_, lean_object* v_x_3805_){
_start:
{
lean_object* v___x_3806_; 
v___x_3806_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(v_a_3803_, v_fallback_3804_, v_x_3805_);
return v___x_3806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3807_, lean_object* v_a_3808_, lean_object* v_fallback_3809_, lean_object* v_x_3810_){
_start:
{
lean_object* v_res_3811_; 
v_res_3811_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21(v_00_u03b2_3807_, v_a_3808_, v_fallback_3809_, v_x_3810_);
lean_dec(v_x_3810_);
lean_dec(v_fallback_3809_);
lean_dec_ref(v_a_3808_);
return v_res_3811_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23(lean_object* v_00_u03b2_3812_, lean_object* v_a_3813_, lean_object* v_x_3814_){
_start:
{
uint8_t v___x_3815_; 
v___x_3815_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(v_a_3813_, v_x_3814_);
return v___x_3815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___boxed(lean_object* v_00_u03b2_3816_, lean_object* v_a_3817_, lean_object* v_x_3818_){
_start:
{
uint8_t v_res_3819_; lean_object* v_r_3820_; 
v_res_3819_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23(v_00_u03b2_3816_, v_a_3817_, v_x_3818_);
lean_dec(v_x_3818_);
lean_dec_ref(v_a_3817_);
v_r_3820_ = lean_box(v_res_3819_);
return v_r_3820_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24(lean_object* v_00_u03b2_3821_, lean_object* v_data_3822_){
_start:
{
lean_object* v___x_3823_; 
v___x_3823_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24___redArg(v_data_3822_);
return v___x_3823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25(lean_object* v_00_u03b2_3824_, lean_object* v_a_3825_, lean_object* v_b_3826_, lean_object* v_x_3827_){
_start:
{
lean_object* v___x_3828_; 
v___x_3828_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(v_a_3825_, v_b_3826_, v_x_3827_);
return v___x_3828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31(lean_object* v_n_3829_, lean_object* v_lo_3830_, lean_object* v_hi_3831_, lean_object* v_hhi_3832_, lean_object* v_pivot_3833_, lean_object* v_as_3834_, lean_object* v_i_3835_, lean_object* v_k_3836_, lean_object* v_ilo_3837_, lean_object* v_ik_3838_, lean_object* v_w_3839_){
_start:
{
lean_object* v___x_3840_; 
v___x_3840_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(v_hi_3831_, v_pivot_3833_, v_as_3834_, v_i_3835_, v_k_3836_);
return v___x_3840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___boxed(lean_object* v_n_3841_, lean_object* v_lo_3842_, lean_object* v_hi_3843_, lean_object* v_hhi_3844_, lean_object* v_pivot_3845_, lean_object* v_as_3846_, lean_object* v_i_3847_, lean_object* v_k_3848_, lean_object* v_ilo_3849_, lean_object* v_ik_3850_, lean_object* v_w_3851_){
_start:
{
lean_object* v_res_3852_; 
v_res_3852_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31(v_n_3841_, v_lo_3842_, v_hi_3843_, v_hhi_3844_, v_pivot_3845_, v_as_3846_, v_i_3847_, v_k_3848_, v_ilo_3849_, v_ik_3850_, v_w_3851_);
lean_dec_ref(v_pivot_3845_);
lean_dec(v_hi_3843_);
lean_dec(v_lo_3842_);
lean_dec(v_n_3841_);
return v_res_3852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40(lean_object* v_as_3853_, size_t v_sz_3854_, size_t v_i_3855_, lean_object* v_b_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_){
_start:
{
lean_object* v___x_3860_; 
v___x_3860_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(v_as_3853_, v_sz_3854_, v_i_3855_, v_b_3856_, v___y_3857_);
return v___x_3860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___boxed(lean_object* v_as_3861_, lean_object* v_sz_3862_, lean_object* v_i_3863_, lean_object* v_b_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_){
_start:
{
size_t v_sz_boxed_3868_; size_t v_i_boxed_3869_; lean_object* v_res_3870_; 
v_sz_boxed_3868_ = lean_unbox_usize(v_sz_3862_);
lean_dec(v_sz_3862_);
v_i_boxed_3869_ = lean_unbox_usize(v_i_3863_);
lean_dec(v_i_3863_);
v_res_3870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40(v_as_3861_, v_sz_boxed_3868_, v_i_boxed_3869_, v_b_3864_, v___y_3865_, v___y_3866_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
lean_dec_ref(v_as_3861_);
return v_res_3870_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35(lean_object* v_00_u03b2_3871_, lean_object* v_i_3872_, lean_object* v_source_3873_, lean_object* v_target_3874_){
_start:
{
lean_object* v___x_3875_; 
v___x_3875_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35___redArg(v_i_3872_, v_source_3873_, v_target_3874_);
return v___x_3875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42(uint8_t v___x_3876_, lean_object* v_as_3877_, size_t v_sz_3878_, size_t v_i_3879_, lean_object* v_b_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_){
_start:
{
lean_object* v___x_3884_; 
v___x_3884_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(v___x_3876_, v_as_3877_, v_sz_3878_, v_i_3879_, v_b_3880_, v___y_3881_);
return v___x_3884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___boxed(lean_object* v___x_3885_, lean_object* v_as_3886_, lean_object* v_sz_3887_, lean_object* v_i_3888_, lean_object* v_b_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
uint8_t v___x_42385__boxed_3893_; size_t v_sz_boxed_3894_; size_t v_i_boxed_3895_; lean_object* v_res_3896_; 
v___x_42385__boxed_3893_ = lean_unbox(v___x_3885_);
v_sz_boxed_3894_ = lean_unbox_usize(v_sz_3887_);
lean_dec(v_sz_3887_);
v_i_boxed_3895_ = lean_unbox_usize(v_i_3888_);
lean_dec(v_i_3888_);
v_res_3896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42(v___x_42385__boxed_3893_, v_as_3886_, v_sz_boxed_3894_, v_i_boxed_3895_, v_b_3889_, v___y_3890_, v___y_3891_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec_ref(v_as_3886_);
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51(lean_object* v_as_3897_, size_t v_sz_3898_, size_t v_i_3899_, lean_object* v_b_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_){
_start:
{
lean_object* v___x_3904_; 
v___x_3904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(v_as_3897_, v_sz_3898_, v_i_3899_, v_b_3900_, v___y_3901_);
return v___x_3904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___boxed(lean_object* v_as_3905_, lean_object* v_sz_3906_, lean_object* v_i_3907_, lean_object* v_b_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_){
_start:
{
size_t v_sz_boxed_3912_; size_t v_i_boxed_3913_; lean_object* v_res_3914_; 
v_sz_boxed_3912_ = lean_unbox_usize(v_sz_3906_);
lean_dec(v_sz_3906_);
v_i_boxed_3913_ = lean_unbox_usize(v_i_3907_);
lean_dec(v_i_3907_);
v_res_3914_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51(v_as_3905_, v_sz_boxed_3912_, v_i_boxed_3913_, v_b_3908_, v___y_3909_, v___y_3910_);
lean_dec(v___y_3910_);
lean_dec_ref(v___y_3909_);
lean_dec_ref(v_as_3905_);
return v_res_3914_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44(lean_object* v_00_u03b2_3915_, lean_object* v_x_3916_, lean_object* v_x_3917_){
_start:
{
lean_object* v___x_3918_; 
v___x_3918_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44___redArg(v_x_3916_, v_x_3917_);
return v___x_3918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49(uint8_t v___x_3919_, lean_object* v_as_3920_, size_t v_sz_3921_, size_t v_i_3922_, lean_object* v_b_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_){
_start:
{
lean_object* v___x_3927_; 
v___x_3927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(v___x_3919_, v_as_3920_, v_sz_3921_, v_i_3922_, v_b_3923_, v___y_3924_);
return v___x_3927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___boxed(lean_object* v___x_3928_, lean_object* v_as_3929_, lean_object* v_sz_3930_, lean_object* v_i_3931_, lean_object* v_b_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_){
_start:
{
uint8_t v___x_42416__boxed_3936_; size_t v_sz_boxed_3937_; size_t v_i_boxed_3938_; lean_object* v_res_3939_; 
v___x_42416__boxed_3936_ = lean_unbox(v___x_3928_);
v_sz_boxed_3937_ = lean_unbox_usize(v_sz_3930_);
lean_dec(v_sz_3930_);
v_i_boxed_3938_ = lean_unbox_usize(v_i_3931_);
lean_dec(v_i_3931_);
v_res_3939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49(v___x_42416__boxed_3936_, v_as_3929_, v_sz_boxed_3937_, v_i_boxed_3938_, v_b_3932_, v___y_3933_, v___y_3934_);
lean_dec(v___y_3934_);
lean_dec_ref(v___y_3933_);
lean_dec_ref(v_as_3929_);
return v_res_3939_;
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
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
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
