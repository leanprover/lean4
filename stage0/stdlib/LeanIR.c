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
LEAN_EXPORT lean_object* l_main___lam__2(lean_object*, lean_object*, uint16_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___boxed(lean_object*, lean_object*);
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
lean_object* v_a_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_30_; 
v_a_6_ = lean_ctor_get(v___x_5_, 0);
v_isSharedCheck_30_ = !lean_is_exclusive(v___x_5_);
if (v_isSharedCheck_30_ == 0)
{
v___x_8_ = v___x_5_;
v_isShared_9_ = v_isSharedCheck_30_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_a_6_);
lean_dec(v___x_5_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_30_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
uint8_t v_isModule_10_; lean_object* v_imports_11_; lean_object* v_constNames_12_; lean_object* v_constants_13_; lean_object* v_entries_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_26_; 
v_isModule_10_ = lean_ctor_get_uint8(v_a_6_, sizeof(void*)*7);
v_imports_11_ = lean_ctor_get(v_a_6_, 0);
v_constNames_12_ = lean_ctor_get(v_a_6_, 1);
v_constants_13_ = lean_ctor_get(v_a_6_, 2);
v_entries_14_ = lean_ctor_get(v_a_6_, 4);
v_isSharedCheck_26_ = !lean_is_exclusive(v_a_6_);
if (v_isSharedCheck_26_ == 0)
{
lean_object* v_unused_27_; lean_object* v_unused_28_; lean_object* v_unused_29_; 
v_unused_27_ = lean_ctor_get(v_a_6_, 6);
lean_dec(v_unused_27_);
v_unused_28_ = lean_ctor_get(v_a_6_, 5);
lean_dec(v_unused_28_);
v_unused_29_ = lean_ctor_get(v_a_6_, 3);
lean_dec(v_unused_29_);
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
lean_ctor_set(v___x_16_, 6, v___x_4_);
lean_ctor_set(v___x_16_, 5, v___x_4_);
lean_ctor_set(v___x_16_, 3, v___x_19_);
v___x_21_ = v___x_16_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v_imports_11_);
lean_ctor_set(v_reuseFailAlloc_25_, 1, v_constNames_12_);
lean_ctor_set(v_reuseFailAlloc_25_, 2, v_constants_13_);
lean_ctor_set(v_reuseFailAlloc_25_, 3, v___x_19_);
lean_ctor_set(v_reuseFailAlloc_25_, 4, v_entries_14_);
lean_ctor_set(v_reuseFailAlloc_25_, 5, v___x_4_);
lean_ctor_set(v_reuseFailAlloc_25_, 6, v___x_4_);
lean_ctor_set_uint8(v_reuseFailAlloc_25_, sizeof(void*)*7, v_isModule_10_);
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
LEAN_EXPORT lean_object* l___private_LeanIR_0__mkIRSigData___boxed(lean_object* v_env_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l___private_LeanIR_0__mkIRSigData(v_env_31_);
return v_res_33_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1(lean_object* v_a_34_, lean_object* v_as_35_, size_t v_i_36_, size_t v_stop_37_){
_start:
{
uint8_t v___x_38_; 
v___x_38_ = lean_usize_dec_eq(v_i_36_, v_stop_37_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; uint8_t v___x_40_; 
v___x_39_ = lean_array_uget_borrowed(v_as_35_, v_i_36_);
v___x_40_ = lean_name_eq(v_a_34_, v___x_39_);
if (v___x_40_ == 0)
{
size_t v___x_41_; size_t v___x_42_; 
v___x_41_ = ((size_t)1ULL);
v___x_42_ = lean_usize_add(v_i_36_, v___x_41_);
v_i_36_ = v___x_42_;
goto _start;
}
else
{
return v___x_40_;
}
}
else
{
uint8_t v___x_44_; 
v___x_44_ = 0;
return v___x_44_;
}
}
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
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1(lean_object* v_as_53_, lean_object* v_a_54_){
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
size_t v___x_58_; size_t v___x_59_; uint8_t v___x_60_; 
v___x_58_ = ((size_t)0ULL);
v___x_59_ = lean_usize_of_nat(v___x_56_);
v___x_60_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1(v_a_54_, v_as_53_, v___x_58_, v___x_59_);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1___boxed(lean_object* v_as_61_, lean_object* v_a_62_){
_start:
{
uint8_t v_res_63_; lean_object* v_r_64_; 
v_res_63_ = l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1(v_as_61_, v_a_62_);
lean_dec(v_a_62_);
lean_dec_ref(v_as_61_);
v_r_64_ = lean_box(v_res_63_);
return v_r_64_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(lean_object* v_irExtNames_65_, lean_object* v_as_66_, size_t v_i_67_, size_t v_stop_68_, lean_object* v_b_69_){
_start:
{
lean_object* v___y_71_; uint8_t v___x_75_; 
v___x_75_ = lean_usize_dec_eq(v_i_67_, v_stop_68_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; lean_object* v_fst_77_; uint8_t v___x_78_; 
v___x_76_ = lean_array_uget_borrowed(v_as_66_, v_i_67_);
v_fst_77_ = lean_ctor_get(v___x_76_, 0);
v___x_78_ = l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1(v_irExtNames_65_, v_fst_77_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; 
lean_inc(v___x_76_);
v___x_79_ = lean_array_push(v_b_69_, v___x_76_);
v___y_71_ = v___x_79_;
goto v___jp_70_;
}
else
{
v___y_71_ = v_b_69_;
goto v___jp_70_;
}
}
else
{
return v_b_69_;
}
v___jp_70_:
{
size_t v___x_72_; size_t v___x_73_; 
v___x_72_ = ((size_t)1ULL);
v___x_73_ = lean_usize_add(v_i_67_, v___x_72_);
v_i_67_ = v___x_73_;
v_b_69_ = v___y_71_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2___boxed(lean_object* v_irExtNames_80_, lean_object* v_as_81_, lean_object* v_i_82_, lean_object* v_stop_83_, lean_object* v_b_84_){
_start:
{
size_t v_i_boxed_85_; size_t v_stop_boxed_86_; lean_object* v_res_87_; 
v_i_boxed_85_ = lean_unbox_usize(v_i_82_);
lean_dec(v_i_82_);
v_stop_boxed_86_ = lean_unbox_usize(v_stop_83_);
lean_dec(v_stop_83_);
v_res_87_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(v_irExtNames_80_, v_as_81_, v_i_boxed_85_, v_stop_boxed_86_, v_b_84_);
lean_dec_ref(v_as_81_);
lean_dec_ref(v_irExtNames_80_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0(size_t v_sz_88_, size_t v_i_89_, lean_object* v_bs_90_){
_start:
{
uint8_t v___x_91_; 
v___x_91_ = lean_usize_dec_lt(v_i_89_, v_sz_88_);
if (v___x_91_ == 0)
{
return v_bs_90_;
}
else
{
lean_object* v_v_92_; lean_object* v_fst_93_; lean_object* v___x_94_; lean_object* v_bs_x27_95_; size_t v___x_96_; size_t v___x_97_; lean_object* v___x_98_; 
v_v_92_ = lean_array_uget_borrowed(v_bs_90_, v_i_89_);
v_fst_93_ = lean_ctor_get(v_v_92_, 0);
lean_inc(v_fst_93_);
v___x_94_ = lean_unsigned_to_nat(0u);
v_bs_x27_95_ = lean_array_uset(v_bs_90_, v_i_89_, v___x_94_);
v___x_96_ = ((size_t)1ULL);
v___x_97_ = lean_usize_add(v_i_89_, v___x_96_);
v___x_98_ = lean_array_uset(v_bs_x27_95_, v_i_89_, v_fst_93_);
v_i_89_ = v___x_97_;
v_bs_90_ = v___x_98_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0___boxed(lean_object* v_sz_100_, lean_object* v_i_101_, lean_object* v_bs_102_){
_start:
{
size_t v_sz_boxed_103_; size_t v_i_boxed_104_; lean_object* v_res_105_; 
v_sz_boxed_103_ = lean_unbox_usize(v_sz_100_);
lean_dec(v_sz_100_);
v_i_boxed_104_ = lean_unbox_usize(v_i_101_);
lean_dec(v_i_101_);
v_res_105_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0(v_sz_boxed_103_, v_i_boxed_104_, v_bs_102_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__mkIRData(lean_object* v_env_110_){
_start:
{
lean_object* v_irEntries_112_; size_t v_sz_113_; size_t v___x_114_; lean_object* v_irExtNames_115_; uint8_t v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
lean_inc_ref_n(v_env_110_, 2);
v_irEntries_112_ = lean_ir_export_entries(v_env_110_);
v_sz_113_ = lean_array_size(v_irEntries_112_);
v___x_114_ = ((size_t)0ULL);
lean_inc_ref(v_irEntries_112_);
v_irExtNames_115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0(v_sz_113_, v___x_114_, v_irEntries_112_);
v___x_116_ = 2;
v___x_117_ = lean_box(0);
v___x_118_ = l_Lean_mkModuleData(v_env_110_, v___x_116_, v___x_117_);
if (lean_obj_tag(v___x_118_) == 0)
{
lean_object* v_a_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_143_; 
v_a_119_ = lean_ctor_get(v___x_118_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_143_ == 0)
{
v___x_121_ = v___x_118_;
v_isShared_122_ = v_isSharedCheck_143_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_a_119_);
lean_dec(v___x_118_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_143_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___y_124_; lean_object* v_entries_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v_entries_136_ = lean_ctor_get(v_a_119_, 4);
lean_inc_ref(v_entries_136_);
lean_dec(v_a_119_);
v___x_137_ = lean_unsigned_to_nat(0u);
v___x_138_ = lean_array_get_size(v_entries_136_);
v___x_139_ = ((lean_object*)(l___private_LeanIR_0__mkIRData___closed__1));
v___x_140_ = lean_nat_dec_lt(v___x_137_, v___x_138_);
if (v___x_140_ == 0)
{
lean_dec_ref(v_entries_136_);
lean_dec_ref(v_irExtNames_115_);
v___y_124_ = v___x_139_;
goto v___jp_123_;
}
else
{
size_t v___x_141_; lean_object* v___x_142_; 
v___x_141_ = lean_usize_of_nat(v___x_138_);
v___x_142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(v_irExtNames_115_, v_entries_136_, v___x_114_, v___x_141_, v___x_139_);
lean_dec_ref(v_entries_136_);
lean_dec_ref(v_irExtNames_115_);
v___y_124_ = v___x_142_;
goto v___jp_123_;
}
v___jp_123_:
{
lean_object* v___x_125_; uint8_t v_isModule_126_; lean_object* v_imports_127_; lean_object* v___x_128_; uint8_t v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_125_ = l_Lean_Environment_header(v_env_110_);
v_isModule_126_ = lean_ctor_get_uint8(v___x_125_, sizeof(void*)*8 + 4);
v_imports_127_ = lean_ctor_get(v___x_125_, 1);
lean_inc_ref(v_imports_127_);
lean_dec_ref(v___x_125_);
v___x_128_ = ((lean_object*)(l___private_LeanIR_0__mkIRData___closed__0));
v___x_129_ = 1;
v___x_130_ = lean_get_ir_extra_const_names(v_env_110_, v___x_116_, v___x_129_);
v___x_131_ = l_Array_append___redArg(v_irEntries_112_, v___y_124_);
lean_dec_ref(v___y_124_);
v___x_132_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_132_, 0, v_imports_127_);
lean_ctor_set(v___x_132_, 1, v___x_128_);
lean_ctor_set(v___x_132_, 2, v___x_128_);
lean_ctor_set(v___x_132_, 3, v___x_130_);
lean_ctor_set(v___x_132_, 4, v___x_131_);
lean_ctor_set(v___x_132_, 5, v___x_117_);
lean_ctor_set(v___x_132_, 6, v___x_117_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*7, v_isModule_126_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 0, v___x_132_);
v___x_134_ = v___x_121_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
else
{
lean_dec_ref(v_irExtNames_115_);
lean_dec_ref(v_irEntries_112_);
lean_dec_ref(v_env_110_);
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__mkIRData___boxed(lean_object* v_env_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_LeanIR_0__mkIRData(v_env_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(lean_object* v_s_148_){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; 
v___x_149_ = lean_string_utf8_byte_size(v_s_148_);
v___x_150_ = lean_unsigned_to_nat(2u);
v___x_151_ = lean_nat_dec_le(v___x_150_, v___x_149_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; 
lean_dec_ref(v_s_148_);
v___x_152_ = lean_box(0);
return v___x_152_;
}
else
{
lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_153_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__0));
v___x_154_ = lean_unsigned_to_nat(0u);
v___x_155_ = lean_string_memcmp(v_s_148_, v___x_153_, v___x_154_, v___x_154_, v___x_150_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; 
lean_dec_ref(v_s_148_);
v___x_156_ = lean_box(0);
return v___x_156_;
}
else
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
lean_inc_ref(v_s_148_);
v___x_157_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_157_, 0, v_s_148_);
lean_ctor_set(v___x_157_, 1, v___x_154_);
lean_ctor_set(v___x_157_, 2, v___x_149_);
v___x_158_ = l_String_Slice_pos_x21(v___x_157_, v___x_150_);
lean_dec_ref_known(v___x_157_, 3);
v___x_159_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_159_, 0, v_s_148_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
lean_ctor_set(v___x_159_, 2, v___x_149_);
v___x_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0(lean_object* v_s_161_, lean_object* v_pat_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(v_s_161_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___boxed(lean_object* v_s_164_, lean_object* v_pat_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0(v_s_164_, v_pat_165_);
lean_dec_ref(v_pat_165_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(lean_object* v_val_167_, lean_object* v_a_168_, lean_object* v_b_169_){
_start:
{
lean_object* v_str_170_; lean_object* v_startInclusive_171_; lean_object* v_endExclusive_172_; lean_object* v___x_173_; uint8_t v_decide_174_; 
v_str_170_ = lean_ctor_get(v_val_167_, 0);
v_startInclusive_171_ = lean_ctor_get(v_val_167_, 1);
v_endExclusive_172_ = lean_ctor_get(v_val_167_, 2);
v___x_173_ = lean_nat_sub(v_endExclusive_172_, v_startInclusive_171_);
v_decide_174_ = lean_nat_dec_eq(v_a_168_, v___x_173_);
lean_dec(v___x_173_);
if (v_decide_174_ == 0)
{
lean_object* v___x_175_; uint32_t v___x_176_; uint32_t v___x_177_; uint8_t v___x_178_; 
v___x_175_ = lean_nat_add(v_startInclusive_171_, v_a_168_);
v___x_176_ = lean_string_utf8_get_fast(v_str_170_, v___x_175_);
v___x_177_ = 61;
v___x_178_ = lean_uint32_dec_eq(v___x_176_, v___x_177_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
lean_dec(v_a_168_);
v___x_179_ = lean_box(0);
v___x_180_ = lean_string_utf8_next_fast(v_str_170_, v___x_175_);
lean_dec(v___x_175_);
v___x_181_ = lean_nat_sub(v___x_180_, v_startInclusive_171_);
v_a_168_ = v___x_181_;
v_b_169_ = v___x_179_;
goto _start;
}
else
{
lean_object* v___x_183_; 
lean_dec(v___x_175_);
v___x_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_183_, 0, v_a_168_);
return v___x_183_;
}
}
else
{
lean_dec(v_a_168_);
lean_inc(v_b_169_);
return v_b_169_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg___boxed(lean_object* v_val_184_, lean_object* v_a_185_, lean_object* v_b_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(v_val_184_, v_a_185_, v_b_186_);
lean_dec(v_b_186_);
lean_dec_ref(v_val_184_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption(lean_object* v_opts_195_, lean_object* v_arg_196_){
_start:
{
lean_object* v___x_198_; 
lean_inc_ref(v_arg_196_);
v___x_198_ = l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(v_arg_196_);
if (lean_obj_tag(v___x_198_) == 1)
{
lean_object* v_val_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_263_; 
lean_dec_ref(v_arg_196_);
v_val_199_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_263_ == 0)
{
v___x_201_ = v___x_198_;
v_isShared_202_ = v_isSharedCheck_263_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_val_199_);
lean_dec(v___x_198_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_263_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___y_204_; lean_object* v_searcher_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_searcher_256_ = lean_unsigned_to_nat(0u);
v___x_257_ = lean_box(0);
v___x_258_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(v_val_199_, v_searcher_256_, v___x_257_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v_startInclusive_259_; lean_object* v_endExclusive_260_; lean_object* v___x_261_; 
v_startInclusive_259_ = lean_ctor_get(v_val_199_, 1);
v_endExclusive_260_ = lean_ctor_get(v_val_199_, 2);
v___x_261_ = lean_nat_sub(v_endExclusive_260_, v_startInclusive_259_);
v___y_204_ = v___x_261_;
goto v___jp_203_;
}
else
{
lean_object* v_val_262_; 
v_val_262_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_val_262_);
lean_dec_ref_known(v___x_258_, 1);
v___y_204_ = v_val_262_;
goto v___jp_203_;
}
v___jp_203_:
{
lean_object* v_str_205_; lean_object* v_startInclusive_206_; lean_object* v_endExclusive_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_255_; 
v_str_205_ = lean_ctor_get(v_val_199_, 0);
v_startInclusive_206_ = lean_ctor_get(v_val_199_, 1);
v_endExclusive_207_ = lean_ctor_get(v_val_199_, 2);
v_isSharedCheck_255_ = !lean_is_exclusive(v_val_199_);
if (v_isSharedCheck_255_ == 0)
{
v___x_209_ = v_val_199_;
v_isShared_210_ = v_isSharedCheck_255_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_endExclusive_207_);
lean_inc(v_startInclusive_206_);
lean_inc(v_str_205_);
lean_dec(v_val_199_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_255_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; uint8_t v_decide_212_; 
v___x_211_ = lean_nat_sub(v_endExclusive_207_, v_startInclusive_206_);
v_decide_212_ = lean_nat_dec_eq(v___y_204_, v___x_211_);
lean_dec(v___x_211_);
if (v_decide_212_ == 0)
{
lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_213_ = lean_nat_add(v_startInclusive_206_, v___y_204_);
lean_dec(v___y_204_);
lean_inc(v___x_213_);
lean_inc(v_startInclusive_206_);
lean_inc_ref(v_str_205_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 2, v___x_213_);
v___x_215_ = v___x_209_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_str_205_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_startInclusive_206_);
lean_ctor_set(v_reuseFailAlloc_250_, 2, v___x_213_);
v___x_215_ = v_reuseFailAlloc_250_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v_name_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v_val_220_; lean_object* v___x_221_; 
v_name_216_ = l_String_Slice_toName(v___x_215_);
lean_dec_ref(v___x_215_);
v___x_217_ = lean_string_utf8_next_fast(v_str_205_, v___x_213_);
lean_dec(v___x_213_);
v___x_218_ = lean_nat_sub(v___x_217_, v_startInclusive_206_);
v___x_219_ = lean_nat_add(v_startInclusive_206_, v___x_218_);
lean_dec(v___x_218_);
lean_dec(v_startInclusive_206_);
v_val_220_ = lean_string_utf8_extract_fast(v_str_205_, v___x_219_, v_endExclusive_207_);
lean_dec(v_endExclusive_207_);
lean_dec(v___x_219_);
lean_dec_ref(v_str_205_);
v___x_221_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_241_; 
v_a_222_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_241_ == 0)
{
v___x_224_ = v___x_221_;
v_isShared_225_ = v_isSharedCheck_241_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_221_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_241_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; 
v___x_226_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_222_, v_name_216_);
lean_dec(v_a_222_);
if (lean_obj_tag(v___x_226_) == 1)
{
lean_object* v_val_227_; lean_object* v___x_228_; 
lean_del_object(v___x_224_);
lean_del_object(v___x_201_);
v_val_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_val_227_);
lean_dec_ref_known(v___x_226_, 1);
v___x_228_ = l_Lean_Language_Lean_setOption(v_opts_195_, v_val_227_, v_name_216_, v_val_220_);
return v___x_228_;
}
else
{
lean_object* v___x_229_; uint8_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
lean_dec(v___x_226_);
lean_dec_ref(v_val_220_);
lean_dec_ref(v_opts_195_);
v___x_229_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__0));
v___x_230_ = 1;
v___x_231_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_216_, v___x_230_);
v___x_232_ = lean_string_append(v___x_229_, v___x_231_);
lean_dec_ref(v___x_231_);
v___x_233_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__1));
v___x_234_ = lean_string_append(v___x_232_, v___x_233_);
if (v_isShared_202_ == 0)
{
lean_ctor_set_tag(v___x_201_, 18);
lean_ctor_set(v___x_201_, 0, v___x_234_);
v___x_236_ = v___x_201_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_234_);
v___x_236_ = v_reuseFailAlloc_240_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_238_; 
if (v_isShared_225_ == 0)
{
lean_ctor_set_tag(v___x_224_, 1);
lean_ctor_set(v___x_224_, 0, v___x_236_);
v___x_238_ = v___x_224_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_236_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
}
else
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
lean_dec_ref(v_val_220_);
lean_dec(v_name_216_);
lean_del_object(v___x_201_);
lean_dec_ref(v_opts_195_);
v_a_242_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v___x_221_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_221_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_a_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
}
else
{
lean_object* v___x_251_; lean_object* v___x_253_; 
lean_del_object(v___x_209_);
lean_dec(v_endExclusive_207_);
lean_dec(v_startInclusive_206_);
lean_dec_ref(v_str_205_);
lean_dec(v___y_204_);
lean_dec_ref(v_opts_195_);
v___x_251_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__3));
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v___x_251_);
v___x_253_ = v___x_201_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_251_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
}
}
else
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec(v___x_198_);
lean_dec_ref(v_opts_195_);
v___x_264_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__4));
v___x_265_ = lean_string_append(v___x_264_, v_arg_196_);
lean_dec_ref(v_arg_196_);
v___x_266_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__5));
v___x_267_ = lean_string_append(v___x_265_, v___x_266_);
v___x_268_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
v___x_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
return v___x_269_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption___boxed(lean_object* v_opts_270_, lean_object* v_arg_271_, lean_object* v_a_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l___private_LeanIR_0__setConfigOption(v_opts_270_, v_arg_271_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1(lean_object* v_val_274_, lean_object* v_inst_275_, lean_object* v_R_276_, lean_object* v_a_277_, lean_object* v_b_278_, lean_object* v_c_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(v_val_274_, v_a_277_, v_b_278_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___boxed(lean_object* v_val_281_, lean_object* v_inst_282_, lean_object* v_R_283_, lean_object* v_a_284_, lean_object* v_b_285_, lean_object* v_c_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1(v_val_281_, v_inst_282_, v_R_283_, v_a_284_, v_b_285_, v_c_286_);
lean_dec(v_b_285_);
lean_dec_ref(v_val_281_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg___lam__0(lean_object* v___x_288_, lean_object* v_x_289_){
_start:
{
lean_inc_ref(v___x_288_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg___lam__0___boxed(lean_object* v___x_290_, lean_object* v_x_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_main___elam__0___redArg___lam__0(v___x_290_, v_x_291_);
lean_dec_ref(v_x_291_);
lean_dec_ref(v___x_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg(lean_object* v___x_293_, uint8_t v___x_294_, lean_object* v_inst_295_, lean_object* v_ext_296_, lean_object* v_env_297_){
_start:
{
lean_object* v_toEnvExtension_299_; lean_object* v_addImportedFn_300_; lean_object* v_asyncMode_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v_importedEntries_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_335_; 
v_toEnvExtension_299_ = lean_ctor_get(v_ext_296_, 0);
lean_inc_ref(v_toEnvExtension_299_);
v_addImportedFn_300_ = lean_ctor_get(v_ext_296_, 2);
lean_inc_ref(v_addImportedFn_300_);
lean_dec_ref(v_ext_296_);
v_asyncMode_301_ = lean_ctor_get(v_toEnvExtension_299_, 2);
v___x_302_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v_inst_295_);
lean_inc_ref(v_env_297_);
v___x_303_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_302_, v_toEnvExtension_299_, v_env_297_, v_asyncMode_301_, v___x_293_, v___x_294_);
lean_dec_ref(v___x_302_);
v_importedEntries_304_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_335_ == 0)
{
lean_object* v_unused_336_; 
v_unused_336_ = lean_ctor_get(v___x_303_, 1);
lean_dec(v_unused_336_);
v___x_306_ = v___x_303_;
v_isShared_307_ = v_isSharedCheck_335_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_importedEntries_304_);
lean_dec(v___x_303_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_335_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = l_Lean_Options_empty;
lean_inc_ref(v_env_297_);
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v_env_297_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
lean_inc_ref(v_importedEntries_304_);
v___x_310_ = lean_apply_3(v_addImportedFn_300_, v_importedEntries_304_, v___x_309_, lean_box(0));
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_326_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_326_ == 0)
{
v___x_313_ = v___x_310_;
v_isShared_314_ = v_isSharedCheck_326_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_310_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_326_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 1, v_a_311_);
v___x_316_ = v___x_306_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_importedEntries_304_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_a_311_);
v___x_316_ = v_reuseFailAlloc_325_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___f_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
v___f_317_ = lean_alloc_closure((void*)(l_main___elam__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_317_, 0, v___x_316_);
v___x_318_ = lean_box(0);
v___x_319_ = lean_box(0);
v___x_320_ = 1;
v___x_321_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_299_, v_env_297_, v___f_317_, v___x_318_, v___x_319_, v___x_320_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v___x_321_);
v___x_323_ = v___x_313_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
else
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
lean_del_object(v___x_306_);
lean_dec_ref(v_importedEntries_304_);
lean_dec_ref(v_toEnvExtension_299_);
lean_dec_ref(v_env_297_);
v_a_327_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_310_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_310_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg___boxed(lean_object* v___x_337_, lean_object* v___x_338_, lean_object* v_inst_339_, lean_object* v_ext_340_, lean_object* v_env_341_, lean_object* v___y_342_){
_start:
{
uint8_t v___x_37024__boxed_343_; lean_object* v_res_344_; 
v___x_37024__boxed_343_ = lean_unbox(v___x_338_);
v_res_344_ = l_main___elam__0___redArg(v___x_337_, v___x_37024__boxed_343_, v_inst_339_, v_ext_340_, v_env_341_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0(lean_object* v___x_345_, uint8_t v___x_346_, lean_object* v_00_u03b1_347_, lean_object* v_00_u03b2_348_, lean_object* v_00_u03c3_349_, lean_object* v_inst_350_, lean_object* v_ext_351_, lean_object* v_env_352_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_main___elam__0___redArg(v___x_345_, v___x_346_, v_inst_350_, v_ext_351_, v_env_352_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___boxed(lean_object* v___x_355_, lean_object* v___x_356_, lean_object* v_00_u03b1_357_, lean_object* v_00_u03b2_358_, lean_object* v_00_u03c3_359_, lean_object* v_inst_360_, lean_object* v_ext_361_, lean_object* v_env_362_, lean_object* v___y_363_){
_start:
{
uint8_t v___x_37104__boxed_364_; lean_object* v_res_365_; 
v___x_37104__boxed_364_ = lean_unbox(v___x_356_);
v_res_365_ = l_main___elam__0(v___x_355_, v___x_37104__boxed_364_, v_00_u03b1_357_, v_00_u03b2_358_, v_00_u03c3_359_, v_inst_360_, v_ext_361_, v_env_362_);
return v_res_365_;
}
}
static lean_object* _init_l_panic___at___00main_spec__5___closed__0(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = l_instInhabitedError;
v___x_367_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_367_, 0, lean_box(0));
lean_closure_set(v___x_367_, 1, lean_box(0));
lean_closure_set(v___x_367_, 2, v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5(lean_object* v_msg_368_){
_start:
{
lean_object* v___x_370_; lean_object* v___x_20061__overap_371_; lean_object* v___x_372_; 
v___x_370_ = lean_obj_once(&l_panic___at___00main_spec__5___closed__0, &l_panic___at___00main_spec__5___closed__0_once, _init_l_panic___at___00main_spec__5___closed__0);
v___x_20061__overap_371_ = lean_panic_fn_borrowed(v___x_370_, v_msg_368_);
v___x_372_ = lean_apply_1(v___x_20061__overap_371_, lean_box(0));
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5___boxed(lean_object* v_msg_373_, lean_object* v___y_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_panic___at___00main_spec__5(v_msg_373_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8(lean_object* v_opts_376_, lean_object* v_opt_377_){
_start:
{
lean_object* v_name_378_; lean_object* v_defValue_379_; lean_object* v_map_380_; lean_object* v___x_381_; 
v_name_378_ = lean_ctor_get(v_opt_377_, 0);
v_defValue_379_ = lean_ctor_get(v_opt_377_, 1);
v_map_380_ = lean_ctor_get(v_opts_376_, 0);
v___x_381_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_380_, v_name_378_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_inc(v_defValue_379_);
return v_defValue_379_;
}
else
{
lean_object* v_val_382_; 
v_val_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_val_382_);
lean_dec_ref_known(v___x_381_, 1);
if (lean_obj_tag(v_val_382_) == 3)
{
lean_object* v_v_383_; 
v_v_383_ = lean_ctor_get(v_val_382_, 0);
lean_inc(v_v_383_);
lean_dec_ref_known(v_val_382_, 1);
return v_v_383_;
}
else
{
lean_dec(v_val_382_);
lean_inc(v_defValue_379_);
return v_defValue_379_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8___boxed(lean_object* v_opts_384_, lean_object* v_opt_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Option_get___at___00main_spec__8(v_opts_384_, v_opt_385_);
lean_dec_ref(v_opt_385_);
lean_dec_ref(v_opts_384_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_main___lam__0(lean_object* v_package_x3f_387_, lean_object* v_ps_388_){
_start:
{
lean_object* v_importedEntries_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
v_importedEntries_389_ = lean_ctor_get(v_ps_388_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v_ps_388_);
if (v_isSharedCheck_396_ == 0)
{
lean_object* v_unused_397_; 
v_unused_397_ = lean_ctor_get(v_ps_388_, 1);
lean_dec(v_unused_397_);
v___x_391_ = v_ps_388_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_importedEntries_389_);
lean_dec(v_ps_388_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 1, v_package_x3f_387_);
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_importedEntries_389_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_package_x3f_387_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(lean_object* v_a_398_, lean_object* v_x_399_){
_start:
{
if (lean_obj_tag(v_x_399_) == 0)
{
lean_dec(v_a_398_);
return v_x_399_;
}
else
{
lean_object* v_key_400_; lean_object* v_value_401_; lean_object* v_tail_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_435_; 
v_key_400_ = lean_ctor_get(v_x_399_, 0);
v_value_401_ = lean_ctor_get(v_x_399_, 1);
v_tail_402_ = lean_ctor_get(v_x_399_, 2);
v_isSharedCheck_435_ = !lean_is_exclusive(v_x_399_);
if (v_isSharedCheck_435_ == 0)
{
v___x_404_ = v_x_399_;
v_isShared_405_ = v_isSharedCheck_435_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_tail_402_);
lean_inc(v_value_401_);
lean_inc(v_key_400_);
lean_dec(v_x_399_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_435_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
uint8_t v___x_406_; 
v___x_406_ = lean_name_eq(v_key_400_, v_a_398_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_407_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v_a_398_, v_tail_402_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 2, v___x_407_);
v___x_409_ = v___x_404_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_key_400_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_value_401_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
else
{
lean_object* v_toEffectiveImport_411_; lean_object* v_parts_412_; lean_object* v_irParts_413_; uint8_t v_needsIRTrans_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_434_; 
lean_dec(v_key_400_);
v_toEffectiveImport_411_ = lean_ctor_get(v_value_401_, 0);
v_parts_412_ = lean_ctor_get(v_value_401_, 1);
v_irParts_413_ = lean_ctor_get(v_value_401_, 2);
v_needsIRTrans_414_ = lean_ctor_get_uint8(v_value_401_, sizeof(void*)*3);
v_isSharedCheck_434_ = !lean_is_exclusive(v_value_401_);
if (v_isSharedCheck_434_ == 0)
{
v___x_416_ = v_value_401_;
v_isShared_417_ = v_isSharedCheck_434_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_irParts_413_);
lean_inc(v_parts_412_);
lean_inc(v_toEffectiveImport_411_);
lean_dec(v_value_401_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_434_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v_toImport_418_; uint8_t v_hasData_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_433_; 
v_toImport_418_ = lean_ctor_get(v_toEffectiveImport_411_, 0);
v_hasData_419_ = lean_ctor_get_uint8(v_toEffectiveImport_411_, sizeof(void*)*1 + 1);
v_isSharedCheck_433_ = !lean_is_exclusive(v_toEffectiveImport_411_);
if (v_isSharedCheck_433_ == 0)
{
v___x_421_ = v_toEffectiveImport_411_;
v_isShared_422_ = v_isSharedCheck_433_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_toImport_418_);
lean_dec(v_toEffectiveImport_411_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_433_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
uint8_t v___x_423_; lean_object* v___x_425_; 
v___x_423_ = 0;
if (v_isShared_422_ == 0)
{
v___x_425_ = v___x_421_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_toImport_418_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, sizeof(void*)*1 + 1, v_hasData_419_);
v___x_425_ = v_reuseFailAlloc_432_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_427_; 
lean_ctor_set_uint8(v___x_425_, sizeof(void*)*1, v___x_423_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_425_);
v___x_427_ = v___x_416_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_425_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_parts_412_);
lean_ctor_set(v_reuseFailAlloc_431_, 2, v_irParts_413_);
lean_ctor_set_uint8(v_reuseFailAlloc_431_, sizeof(void*)*3, v_needsIRTrans_414_);
v___x_427_ = v_reuseFailAlloc_431_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
lean_object* v___x_429_; 
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 1, v___x_427_);
lean_ctor_set(v___x_404_, 0, v_a_398_);
v___x_429_ = v___x_404_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_398_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_430_, 2, v_tail_402_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(lean_object* v_m_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_size_438_; lean_object* v_buckets_439_; lean_object* v___x_440_; uint64_t v___y_442_; 
v_size_438_ = lean_ctor_get(v_m_436_, 0);
v_buckets_439_ = lean_ctor_get(v_m_436_, 1);
v___x_440_ = lean_array_get_size(v_buckets_439_);
if (lean_obj_tag(v_a_437_) == 0)
{
uint64_t v___x_469_; 
v___x_469_ = 1723ULL;
v___y_442_ = v___x_469_;
goto v___jp_441_;
}
else
{
uint64_t v_hash_470_; 
v_hash_470_ = lean_ctor_get_uint64(v_a_437_, sizeof(void*)*2);
v___y_442_ = v_hash_470_;
goto v___jp_441_;
}
v___jp_441_:
{
uint64_t v___x_443_; uint64_t v___x_444_; uint64_t v_fold_445_; uint64_t v___x_446_; uint64_t v___x_447_; uint64_t v___x_448_; size_t v___x_449_; size_t v___x_450_; size_t v___x_451_; size_t v___x_452_; size_t v___x_453_; lean_object* v_bucket_454_; uint8_t v___x_455_; 
v___x_443_ = 32ULL;
v___x_444_ = lean_uint64_shift_right(v___y_442_, v___x_443_);
v_fold_445_ = lean_uint64_xor(v___y_442_, v___x_444_);
v___x_446_ = 16ULL;
v___x_447_ = lean_uint64_shift_right(v_fold_445_, v___x_446_);
v___x_448_ = lean_uint64_xor(v_fold_445_, v___x_447_);
v___x_449_ = lean_uint64_to_usize(v___x_448_);
v___x_450_ = lean_usize_of_nat(v___x_440_);
v___x_451_ = ((size_t)1ULL);
v___x_452_ = lean_usize_sub(v___x_450_, v___x_451_);
v___x_453_ = lean_usize_land(v___x_449_, v___x_452_);
v_bucket_454_ = lean_array_uget_borrowed(v_buckets_439_, v___x_453_);
v___x_455_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_a_437_, v_bucket_454_);
if (v___x_455_ == 0)
{
lean_dec(v_a_437_);
return v_m_436_;
}
else
{
lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_466_; 
lean_inc(v_bucket_454_);
lean_inc_ref(v_buckets_439_);
lean_inc(v_size_438_);
v_isSharedCheck_466_ = !lean_is_exclusive(v_m_436_);
if (v_isSharedCheck_466_ == 0)
{
lean_object* v_unused_467_; lean_object* v_unused_468_; 
v_unused_467_ = lean_ctor_get(v_m_436_, 1);
lean_dec(v_unused_467_);
v_unused_468_ = lean_ctor_get(v_m_436_, 0);
lean_dec(v_unused_468_);
v___x_457_ = v_m_436_;
v_isShared_458_ = v_isSharedCheck_466_;
goto v_resetjp_456_;
}
else
{
lean_dec(v_m_436_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_466_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v_buckets_460_; lean_object* v_bucket_461_; lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_459_ = lean_box(0);
v_buckets_460_ = lean_array_uset(v_buckets_439_, v___x_453_, v___x_459_);
v_bucket_461_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v_a_437_, v_bucket_454_);
v___x_462_ = lean_array_uset(v_buckets_460_, v___x_453_, v_bucket_461_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 1, v___x_462_);
v___x_464_ = v___x_457_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_size_438_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v___x_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__1(lean_object* v___x_471_, lean_object* v___x_472_, uint8_t v___x_473_, lean_object* v_importArts_474_, uint8_t v___y_475_, uint8_t v___x_476_, lean_object* v_name_477_, lean_object* v___x_478_, uint8_t v___x_479_){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_st_mk_ref(v___x_471_);
v___x_482_ = l_Lean_importModulesCore(v___x_472_, v___x_473_, v_importArts_474_, v___y_475_, v___x_476_, v___x_481_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v___x_483_; lean_object* v_moduleNameMap_484_; lean_object* v_moduleNames_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_495_; 
lean_dec_ref_known(v___x_482_, 1);
v___x_483_ = lean_st_ref_get(v___x_481_);
lean_dec(v___x_481_);
v_moduleNameMap_484_ = lean_ctor_get(v___x_483_, 0);
v_moduleNames_485_ = lean_ctor_get(v___x_483_, 1);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_495_ == 0)
{
v___x_487_ = v___x_483_;
v_isShared_488_ = v_isSharedCheck_495_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_moduleNames_485_);
lean_inc(v_moduleNameMap_484_);
lean_dec(v___x_483_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_495_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_489_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(v_moduleNameMap_484_, v_name_477_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v___x_489_);
v___x_491_ = v___x_487_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_moduleNames_485_);
v___x_491_ = v_reuseFailAlloc_494_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
uint32_t v___x_492_; lean_object* v___x_493_; 
v___x_492_ = 0;
v___x_493_ = l_Lean_finalizeImport(v___x_491_, v___x_472_, v___x_478_, v___x_492_, v___x_476_, v___x_479_, v___x_473_, v___x_476_, v___x_476_);
return v___x_493_;
}
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec(v___x_481_);
lean_dec_ref(v___x_478_);
lean_dec(v_name_477_);
lean_dec_ref(v___x_472_);
v_a_496_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_482_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_482_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__1___boxed(lean_object* v___x_504_, lean_object* v___x_505_, lean_object* v___x_506_, lean_object* v_importArts_507_, lean_object* v___y_508_, lean_object* v___x_509_, lean_object* v_name_510_, lean_object* v___x_511_, lean_object* v___x_512_, lean_object* v___y_513_){
_start:
{
uint8_t v___x_37272__boxed_514_; uint8_t v___y_37273__boxed_515_; uint8_t v___x_37274__boxed_516_; uint8_t v___x_37276__boxed_517_; lean_object* v_res_518_; 
v___x_37272__boxed_514_ = lean_unbox(v___x_506_);
v___y_37273__boxed_515_ = lean_unbox(v___y_508_);
v___x_37274__boxed_516_ = lean_unbox(v___x_509_);
v___x_37276__boxed_517_ = lean_unbox(v___x_512_);
v_res_518_ = l_main___lam__1(v___x_504_, v___x_505_, v___x_37272__boxed_514_, v_importArts_507_, v___y_37273__boxed_515_, v___x_37274__boxed_516_, v_name_510_, v___x_511_, v___x_37276__boxed_517_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_main___lam__2(lean_object* v___x_522_, lean_object* v___x_523_, uint16_t v___x_524_, lean_object* v_name_525_, lean_object* v_a_526_, uint8_t v___x_527_, lean_object* v___x_528_, lean_object* v_head_529_, lean_object* v___x_530_, lean_object* v___x_531_, lean_object* v___x_532_, lean_object* v___x_533_, lean_object* v___x_534_, lean_object* v___x_535_, lean_object* v___x_536_, lean_object* v___x_537_, uint8_t v___x_538_, uint8_t v___x_539_, uint8_t v___x_540_){
_start:
{
lean_object* v_a_543_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v_fileName_549_; lean_object* v_fileMap_550_; lean_object* v_currNamespace_551_; lean_object* v_openDecls_552_; lean_object* v_initHeartbeats_553_; lean_object* v_maxHeartbeats_554_; lean_object* v_quotContext_555_; lean_object* v_currMacroScope_556_; lean_object* v_cancelTk_x3f_557_; lean_object* v_inheritedTraceOptions_558_; lean_object* v_currRecDepth_559_; lean_object* v_ref_560_; uint8_t v_suppressElabErrors_561_; uint8_t v_checkDeprecated_562_; uint8_t v_isRecordingDeps_563_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___y_599_; lean_object* v_env_620_; uint8_t v___x_621_; uint16_t v___x_622_; uint16_t v___x_623_; uint16_t v___x_624_; uint8_t v___x_625_; 
v___x_546_ = lean_io_get_num_heartbeats();
v___x_547_ = lean_st_mk_ref(v___x_522_);
v___x_595_ = l_Lean_inheritedTraceOptions;
v___x_596_ = lean_st_ref_get(v___x_595_);
v___x_597_ = lean_st_ref_get(v___x_547_);
v_env_620_ = lean_ctor_get(v___x_597_, 0);
lean_inc_ref(v_env_620_);
lean_dec(v___x_597_);
v___x_621_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_620_);
lean_dec_ref(v_env_620_);
v___x_622_ = 512;
v___x_623_ = lean_uint16_land(v___x_524_, v___x_622_);
v___x_624_ = 0;
v___x_625_ = lean_uint16_dec_eq(v___x_623_, v___x_624_);
if (v___x_625_ == 0)
{
if (v___x_621_ == 0)
{
v___y_599_ = v___x_527_;
goto v___jp_598_;
}
else
{
lean_dec_ref(v___x_528_);
lean_inc(v___x_531_);
v_fileName_549_ = v_head_529_;
v_fileMap_550_ = v___x_530_;
v_currNamespace_551_ = v___x_531_;
v_openDecls_552_ = v___x_532_;
v_initHeartbeats_553_ = v___x_546_;
v_maxHeartbeats_554_ = v___x_533_;
v_quotContext_555_ = v___x_531_;
v_currMacroScope_556_ = v___x_534_;
v_cancelTk_x3f_557_ = v___x_535_;
v_inheritedTraceOptions_558_ = v___x_596_;
v_currRecDepth_559_ = v___x_536_;
v_ref_560_ = v___x_537_;
v_suppressElabErrors_561_ = v___x_538_;
v_checkDeprecated_562_ = v___x_539_;
v_isRecordingDeps_563_ = v___x_538_;
goto v___jp_548_;
}
}
else
{
if (v___x_621_ == 0)
{
lean_dec_ref(v___x_528_);
lean_inc(v___x_531_);
v_fileName_549_ = v_head_529_;
v_fileMap_550_ = v___x_530_;
v_currNamespace_551_ = v___x_531_;
v_openDecls_552_ = v___x_532_;
v_initHeartbeats_553_ = v___x_546_;
v_maxHeartbeats_554_ = v___x_533_;
v_quotContext_555_ = v___x_531_;
v_currMacroScope_556_ = v___x_534_;
v_cancelTk_x3f_557_ = v___x_535_;
v_inheritedTraceOptions_558_ = v___x_596_;
v_currRecDepth_559_ = v___x_536_;
v_ref_560_ = v___x_537_;
v_suppressElabErrors_561_ = v___x_538_;
v_checkDeprecated_562_ = v___x_539_;
v_isRecordingDeps_563_ = v___x_538_;
goto v___jp_548_;
}
else
{
v___y_599_ = v___x_540_;
goto v___jp_598_;
}
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
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_564_ = l_Lean_maxRecDepth;
v___x_565_ = l_Lean_Option_get___at___00main_spec__8(v___x_523_, v___x_564_);
v___x_566_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_566_, 0, v_fileName_549_);
lean_ctor_set(v___x_566_, 1, v_fileMap_550_);
lean_ctor_set(v___x_566_, 2, v___x_523_);
lean_ctor_set(v___x_566_, 3, v___x_565_);
lean_ctor_set(v___x_566_, 4, v_currNamespace_551_);
lean_ctor_set(v___x_566_, 5, v_openDecls_552_);
lean_ctor_set(v___x_566_, 6, v_initHeartbeats_553_);
lean_ctor_set(v___x_566_, 7, v_maxHeartbeats_554_);
lean_ctor_set(v___x_566_, 8, v_quotContext_555_);
lean_ctor_set(v___x_566_, 9, v_currMacroScope_556_);
lean_ctor_set(v___x_566_, 10, v_cancelTk_x3f_557_);
lean_ctor_set(v___x_566_, 11, v_inheritedTraceOptions_558_);
v___x_567_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_567_, 0, v___x_566_);
lean_ctor_set(v___x_567_, 1, v_currRecDepth_559_);
lean_ctor_set(v___x_567_, 2, v_ref_560_);
lean_ctor_set_uint16(v___x_567_, sizeof(void*)*3, v___x_524_);
lean_ctor_set_uint8(v___x_567_, sizeof(void*)*3 + 2, v_suppressElabErrors_561_);
lean_ctor_set_uint8(v___x_567_, sizeof(void*)*3 + 3, v_checkDeprecated_562_);
lean_ctor_set_uint8(v___x_567_, sizeof(void*)*3 + 4, v_isRecordingDeps_563_);
v___x_568_ = l_Lean_Compiler_LCNF_emitC(v_name_525_, v___x_567_, v___x_547_);
lean_dec_ref_known(v___x_567_, 3);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_a_569_);
lean_dec_ref_known(v___x_568_, 1);
v___x_570_ = lean_st_ref_get(v___x_547_);
lean_dec(v___x_547_);
lean_dec(v___x_570_);
v___x_571_ = lean_string_to_utf8(v_a_569_);
v___x_572_ = lean_io_prim_handle_write(v_a_526_, v___x_571_);
lean_dec_ref(v___x_571_);
return v___x_572_;
}
else
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_594_; 
lean_dec(v___x_547_);
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
v___x_586_ = ((lean_object*)(l_main___lam__2___closed__0));
v___x_587_ = l_Lean_Name_toString(v_a_585_, v___x_527_);
v___x_588_ = lean_string_append(v___x_586_, v___x_587_);
lean_dec_ref(v___x_587_);
v_a_543_ = v___x_588_;
goto v___jp_542_;
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
lean_dec_ref_known(v___x_584_, 1);
v___x_589_ = ((lean_object*)(l_main___lam__2___closed__1));
v___x_590_ = l_Nat_reprFast(v_id_583_);
v___x_591_ = lean_string_append(v___x_589_, v___x_590_);
lean_dec_ref(v___x_590_);
v___x_592_ = ((lean_object*)(l_main___lam__2___closed__2));
v___x_593_ = lean_string_append(v___x_591_, v___x_592_);
v_a_543_ = v___x_593_;
goto v___jp_542_;
}
}
}
}
}
v___jp_598_:
{
lean_object* v___x_600_; lean_object* v_env_601_; lean_object* v_nextMacroScope_602_; lean_object* v_ngen_603_; lean_object* v_auxDeclNGen_604_; lean_object* v_traceState_605_; lean_object* v_recordedDeps_606_; lean_object* v_messages_607_; lean_object* v_infoState_608_; lean_object* v_snapshotTasks_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_618_; 
v___x_600_ = lean_st_ref_take(v___x_547_);
v_env_601_ = lean_ctor_get(v___x_600_, 0);
v_nextMacroScope_602_ = lean_ctor_get(v___x_600_, 1);
v_ngen_603_ = lean_ctor_get(v___x_600_, 2);
v_auxDeclNGen_604_ = lean_ctor_get(v___x_600_, 3);
v_traceState_605_ = lean_ctor_get(v___x_600_, 4);
v_recordedDeps_606_ = lean_ctor_get(v___x_600_, 6);
v_messages_607_ = lean_ctor_get(v___x_600_, 7);
v_infoState_608_ = lean_ctor_get(v___x_600_, 8);
v_snapshotTasks_609_ = lean_ctor_get(v___x_600_, 9);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_618_ == 0)
{
lean_object* v_unused_619_; 
v_unused_619_ = lean_ctor_get(v___x_600_, 5);
lean_dec(v_unused_619_);
v___x_611_ = v___x_600_;
v_isShared_612_ = v_isSharedCheck_618_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_snapshotTasks_609_);
lean_inc(v_infoState_608_);
lean_inc(v_messages_607_);
lean_inc(v_recordedDeps_606_);
lean_inc(v_traceState_605_);
lean_inc(v_auxDeclNGen_604_);
lean_inc(v_ngen_603_);
lean_inc(v_nextMacroScope_602_);
lean_inc(v_env_601_);
lean_dec(v___x_600_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_618_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_613_ = l_Lean_Kernel_enableDiag(v_env_601_, v___y_599_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 5, v___x_528_);
lean_ctor_set(v___x_611_, 0, v___x_613_);
v___x_615_ = v___x_611_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_nextMacroScope_602_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v_ngen_603_);
lean_ctor_set(v_reuseFailAlloc_617_, 3, v_auxDeclNGen_604_);
lean_ctor_set(v_reuseFailAlloc_617_, 4, v_traceState_605_);
lean_ctor_set(v_reuseFailAlloc_617_, 5, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_617_, 6, v_recordedDeps_606_);
lean_ctor_set(v_reuseFailAlloc_617_, 7, v_messages_607_);
lean_ctor_set(v_reuseFailAlloc_617_, 8, v_infoState_608_);
lean_ctor_set(v_reuseFailAlloc_617_, 9, v_snapshotTasks_609_);
v___x_615_ = v_reuseFailAlloc_617_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_616_; 
v___x_616_ = lean_st_ref_put(v___x_547_, v___x_615_);
lean_inc(v___x_531_);
v_fileName_549_ = v_head_529_;
v_fileMap_550_ = v___x_530_;
v_currNamespace_551_ = v___x_531_;
v_openDecls_552_ = v___x_532_;
v_initHeartbeats_553_ = v___x_546_;
v_maxHeartbeats_554_ = v___x_533_;
v_quotContext_555_ = v___x_531_;
v_currMacroScope_556_ = v___x_534_;
v_cancelTk_x3f_557_ = v___x_535_;
v_inheritedTraceOptions_558_ = v___x_596_;
v_currRecDepth_559_ = v___x_536_;
v_ref_560_ = v___x_537_;
v_suppressElabErrors_561_ = v___x_538_;
v_checkDeprecated_562_ = v___x_539_;
v_isRecordingDeps_563_ = v___x_538_;
goto v___jp_548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__2___boxed(lean_object** _args){
lean_object* v___x_626_ = _args[0];
lean_object* v___x_627_ = _args[1];
lean_object* v___x_628_ = _args[2];
lean_object* v_name_629_ = _args[3];
lean_object* v_a_630_ = _args[4];
lean_object* v___x_631_ = _args[5];
lean_object* v___x_632_ = _args[6];
lean_object* v_head_633_ = _args[7];
lean_object* v___x_634_ = _args[8];
lean_object* v___x_635_ = _args[9];
lean_object* v___x_636_ = _args[10];
lean_object* v___x_637_ = _args[11];
lean_object* v___x_638_ = _args[12];
lean_object* v___x_639_ = _args[13];
lean_object* v___x_640_ = _args[14];
lean_object* v___x_641_ = _args[15];
lean_object* v___x_642_ = _args[16];
lean_object* v___x_643_ = _args[17];
lean_object* v___x_644_ = _args[18];
lean_object* v___y_645_ = _args[19];
_start:
{
uint16_t v___x_37345__boxed_646_; uint8_t v___x_37347__boxed_647_; uint8_t v___x_37358__boxed_648_; uint8_t v___x_37359__boxed_649_; uint8_t v___x_37360__boxed_650_; lean_object* v_res_651_; 
v___x_37345__boxed_646_ = lean_unbox(v___x_628_);
v___x_37347__boxed_647_ = lean_unbox(v___x_631_);
v___x_37358__boxed_648_ = lean_unbox(v___x_642_);
v___x_37359__boxed_649_ = lean_unbox(v___x_643_);
v___x_37360__boxed_650_ = lean_unbox(v___x_644_);
v_res_651_ = l_main___lam__2(v___x_626_, v___x_627_, v___x_37345__boxed_646_, v_name_629_, v_a_630_, v___x_37347__boxed_647_, v___x_632_, v_head_633_, v___x_634_, v___x_635_, v___x_636_, v___x_637_, v___x_638_, v___x_639_, v___x_640_, v___x_641_, v___x_37358__boxed_648_, v___x_37359__boxed_649_, v___x_37360__boxed_650_);
lean_dec(v_a_630_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_main___lam__3(lean_object* v___x_652_, lean_object* v_x_653_){
_start:
{
lean_inc_ref(v___x_652_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_main___lam__3___boxed(lean_object* v___x_654_, lean_object* v_x_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_main___lam__3(v___x_654_, v_x_655_);
lean_dec_ref(v_x_655_);
lean_dec_ref(v___x_654_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(lean_object* v_x2_657_, lean_object* v_as_658_, size_t v_i_659_, size_t v_stop_660_, lean_object* v_b_661_){
_start:
{
uint8_t v___x_662_; 
v___x_662_ = lean_usize_dec_eq(v_i_659_, v_stop_660_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; lean_object* v___x_664_; size_t v___x_665_; size_t v___x_666_; 
v___x_663_ = lean_array_uget_borrowed(v_as_658_, v_i_659_);
lean_inc_ref(v_x2_657_);
lean_inc(v___x_663_);
v___x_664_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_663_, v_x2_657_, v_b_661_);
v___x_665_ = ((size_t)1ULL);
v___x_666_ = lean_usize_add(v_i_659_, v___x_665_);
v_i_659_ = v___x_666_;
v_b_661_ = v___x_664_;
goto _start;
}
else
{
lean_dec_ref(v_x2_657_);
return v_b_661_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(lean_object* v_x2_668_, lean_object* v_as_669_, lean_object* v_i_670_, lean_object* v_stop_671_, lean_object* v_b_672_){
_start:
{
size_t v_i_boxed_673_; size_t v_stop_boxed_674_; lean_object* v_res_675_; 
v_i_boxed_673_ = lean_unbox_usize(v_i_670_);
lean_dec(v_i_670_);
v_stop_boxed_674_ = lean_unbox_usize(v_stop_671_);
lean_dec(v_stop_671_);
v_res_675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v_x2_668_, v_as_669_, v_i_boxed_673_, v_stop_boxed_674_, v_b_672_);
lean_dec_ref(v_as_669_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(lean_object* v_as_676_, size_t v_i_677_, size_t v_stop_678_, lean_object* v_b_679_){
_start:
{
lean_object* v___y_681_; uint8_t v___x_685_; 
v___x_685_ = lean_usize_dec_eq(v_i_677_, v_stop_678_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; lean_object* v_declNames_687_; lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_686_ = lean_array_uget_borrowed(v_as_676_, v_i_677_);
v_declNames_687_ = lean_ctor_get(v___x_686_, 0);
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = lean_array_get_size(v_declNames_687_);
v___x_690_ = lean_nat_dec_lt(v___x_688_, v___x_689_);
if (v___x_690_ == 0)
{
v___y_681_ = v_b_679_;
goto v___jp_680_;
}
else
{
size_t v___x_691_; size_t v___x_692_; lean_object* v___x_693_; 
v___x_691_ = ((size_t)0ULL);
v___x_692_ = lean_usize_of_nat(v___x_689_);
lean_inc(v___x_686_);
v___x_693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_686_, v_declNames_687_, v___x_691_, v___x_692_, v_b_679_);
v___y_681_ = v___x_693_;
goto v___jp_680_;
}
}
else
{
return v_b_679_;
}
v___jp_680_:
{
size_t v___x_682_; size_t v___x_683_; 
v___x_682_ = ((size_t)1ULL);
v___x_683_ = lean_usize_add(v_i_677_, v___x_682_);
v_i_677_ = v___x_683_;
v_b_679_ = v___y_681_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14___boxed(lean_object* v_as_694_, lean_object* v_i_695_, lean_object* v_stop_696_, lean_object* v_b_697_){
_start:
{
size_t v_i_boxed_698_; size_t v_stop_boxed_699_; lean_object* v_res_700_; 
v_i_boxed_698_ = lean_unbox_usize(v_i_695_);
lean_dec(v_i_695_);
v_stop_boxed_699_ = lean_unbox_usize(v_stop_696_);
lean_dec(v_stop_696_);
v_res_700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v_as_694_, v_i_boxed_698_, v_stop_boxed_699_, v_b_697_);
lean_dec_ref(v_as_694_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(lean_object* v_s_701_){
_start:
{
lean_object* v___x_703_; lean_object* v_putStr_704_; lean_object* v___x_705_; 
v___x_703_ = lean_get_stderr();
v_putStr_704_ = lean_ctor_get(v___x_703_, 4);
lean_inc_ref(v_putStr_704_);
lean_dec_ref(v___x_703_);
v___x_705_ = lean_apply_2(v_putStr_704_, v_s_701_, lean_box(0));
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8___boxed(lean_object* v_s_706_, lean_object* v_a_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v_s_706_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6(lean_object* v_s_709_){
_start:
{
uint32_t v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_711_ = 10;
v___x_712_ = lean_string_push(v_s_709_, v___x_711_);
v___x_713_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v___x_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6___boxed(lean_object* v_s_714_, lean_object* v_a_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_IO_eprintln___at___00main_spec__6(v_s_714_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(lean_object* v_o_720_, lean_object* v_k_721_, lean_object* v_v_722_){
_start:
{
lean_object* v_map_723_; uint8_t v_hasTrace_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_738_; 
v_map_723_ = lean_ctor_get(v_o_720_, 0);
v_hasTrace_724_ = lean_ctor_get_uint8(v_o_720_, sizeof(void*)*1);
v_isSharedCheck_738_ = !lean_is_exclusive(v_o_720_);
if (v_isSharedCheck_738_ == 0)
{
v___x_726_ = v_o_720_;
v_isShared_727_ = v_isSharedCheck_738_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_map_723_);
lean_dec(v_o_720_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_738_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_728_, 0, v_v_722_);
lean_inc(v_k_721_);
v___x_729_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_721_, v___x_728_, v_map_723_);
if (v_hasTrace_724_ == 0)
{
lean_object* v___x_730_; uint8_t v___x_731_; lean_object* v___x_733_; 
v___x_730_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_731_ = l_Lean_Name_isPrefixOf(v___x_730_, v_k_721_);
lean_dec(v_k_721_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 0, v___x_729_);
v___x_733_ = v___x_726_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_729_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_ctor_set_uint8(v___x_733_, sizeof(void*)*1, v___x_731_);
return v___x_733_;
}
}
else
{
lean_object* v___x_736_; 
lean_dec(v_k_721_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 0, v___x_729_);
v___x_736_ = v___x_726_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_729_);
lean_ctor_set_uint8(v_reuseFailAlloc_737_, sizeof(void*)*1, v_hasTrace_724_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00main_spec__3(lean_object* v_opts_739_, lean_object* v_opt_740_, lean_object* v_val_741_){
_start:
{
lean_object* v_name_742_; lean_object* v___x_743_; 
v_name_742_ = lean_ctor_get(v_opt_740_, 0);
lean_inc(v_name_742_);
lean_dec_ref(v_opt_740_);
v___x_743_ = l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(v_opts_739_, v_name_742_, v_val_741_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object* v_as_744_, size_t v_i_745_, size_t v_stop_746_, lean_object* v_b_747_){
_start:
{
uint8_t v___x_748_; 
v___x_748_ = lean_usize_dec_eq(v_i_745_, v_stop_746_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; lean_object* v_name_750_; lean_object* v___x_751_; size_t v___x_752_; size_t v___x_753_; 
v___x_749_ = lean_array_uget_borrowed(v_as_744_, v_i_745_);
v_name_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_name_750_);
v___x_751_ = l_Lean_Compiler_LCNF_setDeclPublic(v_b_747_, v_name_750_);
v___x_752_ = ((size_t)1ULL);
v___x_753_ = lean_usize_add(v_i_745_, v___x_752_);
v_i_745_ = v___x_753_;
v_b_747_ = v___x_751_;
goto _start;
}
else
{
return v_b_747_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object* v_as_755_, lean_object* v_i_756_, lean_object* v_stop_757_, lean_object* v_b_758_){
_start:
{
size_t v_i_boxed_759_; size_t v_stop_boxed_760_; lean_object* v_res_761_; 
v_i_boxed_759_ = lean_unbox_usize(v_i_756_);
lean_dec(v_i_756_);
v_stop_boxed_760_ = lean_unbox_usize(v_stop_757_);
lean_dec(v_stop_757_);
v_res_761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v_as_755_, v_i_boxed_759_, v_stop_boxed_760_, v_b_758_);
lean_dec_ref(v_as_755_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg(lean_object* v_as_x27_763_, lean_object* v_b_764_){
_start:
{
if (lean_obj_tag(v_as_x27_763_) == 0)
{
lean_object* v___x_766_; 
v___x_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_766_, 0, v_b_764_);
return v___x_766_;
}
else
{
lean_object* v_head_767_; lean_object* v_tail_768_; lean_object* v_fst_769_; lean_object* v_snd_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_795_; 
v_head_767_ = lean_ctor_get(v_as_x27_763_, 0);
v_tail_768_ = lean_ctor_get(v_as_x27_763_, 1);
v_fst_769_ = lean_ctor_get(v_b_764_, 0);
v_snd_770_ = lean_ctor_get(v_b_764_, 1);
v_isSharedCheck_795_ = !lean_is_exclusive(v_b_764_);
if (v_isSharedCheck_795_ == 0)
{
v___x_772_ = v_b_764_;
v_isShared_773_ = v_isSharedCheck_795_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_snd_770_);
lean_inc(v_fst_769_);
lean_dec(v_b_764_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_795_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_774_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0));
v___x_775_ = lean_string_dec_eq(v_head_767_, v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; 
lean_inc(v_head_767_);
v___x_776_ = l___private_LeanIR_0__setConfigOption(v_snd_770_, v_head_767_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; lean_object* v___x_779_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_a_777_);
lean_dec_ref_known(v___x_776_, 1);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 1, v_a_777_);
v___x_779_ = v___x_772_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_fst_769_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_a_777_);
v___x_779_ = v_reuseFailAlloc_781_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
v_as_x27_763_ = v_tail_768_;
v_b_764_ = v___x_779_;
goto _start;
}
}
else
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
lean_del_object(v___x_772_);
lean_dec(v_fst_769_);
v_a_782_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_776_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_776_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_782_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
else
{
lean_object* v___x_790_; lean_object* v___x_792_; 
lean_dec(v_fst_769_);
v___x_790_ = lean_box(v___x_775_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_790_);
v___x_792_ = v___x_772_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_snd_770_);
v___x_792_ = v_reuseFailAlloc_794_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
v_as_x27_763_ = v_tail_768_;
v_b_764_ = v___x_792_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(lean_object* v_as_x27_796_, lean_object* v_b_797_, lean_object* v___y_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_796_, v_b_797_);
lean_dec(v_as_x27_796_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object* v_a_800_, lean_object* v_as_801_, size_t v_i_802_, size_t v_stop_803_, lean_object* v_b_804_){
_start:
{
lean_object* v___y_806_; uint8_t v___x_810_; 
v___x_810_ = lean_usize_dec_eq(v_i_802_, v_stop_803_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; lean_object* v_name_812_; uint8_t v___x_813_; 
v___x_811_ = lean_array_uget_borrowed(v_as_801_, v_i_802_);
v_name_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_name_812_);
lean_inc_ref(v_a_800_);
v___x_813_ = l_Lean_isExtern(v_a_800_, v_name_812_);
if (v___x_813_ == 0)
{
v___y_806_ = v_b_804_;
goto v___jp_805_;
}
else
{
lean_object* v___x_814_; 
lean_inc(v___x_811_);
v___x_814_ = lean_array_push(v_b_804_, v___x_811_);
v___y_806_ = v___x_814_;
goto v___jp_805_;
}
}
else
{
lean_dec_ref(v_a_800_);
return v_b_804_;
}
v___jp_805_:
{
size_t v___x_807_; size_t v___x_808_; 
v___x_807_ = ((size_t)1ULL);
v___x_808_ = lean_usize_add(v_i_802_, v___x_807_);
v_i_802_ = v___x_808_;
v_b_804_ = v___y_806_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object* v_a_815_, lean_object* v_as_816_, lean_object* v_i_817_, lean_object* v_stop_818_, lean_object* v_b_819_){
_start:
{
size_t v_i_boxed_820_; size_t v_stop_boxed_821_; lean_object* v_res_822_; 
v_i_boxed_820_ = lean_unbox_usize(v_i_817_);
lean_dec(v_i_817_);
v_stop_boxed_821_ = lean_unbox_usize(v_stop_818_);
lean_dec(v_stop_818_);
v_res_822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_815_, v_as_816_, v_i_boxed_820_, v_stop_boxed_821_, v_b_819_);
lean_dec_ref(v_as_816_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___lam__0(lean_object* v_addEntryFn_823_, lean_object* v___x_824_, lean_object* v_s_825_){
_start:
{
lean_object* v_importedEntries_826_; lean_object* v_state_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_835_; 
v_importedEntries_826_ = lean_ctor_get(v_s_825_, 0);
v_state_827_ = lean_ctor_get(v_s_825_, 1);
v_isSharedCheck_835_ = !lean_is_exclusive(v_s_825_);
if (v_isSharedCheck_835_ == 0)
{
v___x_829_ = v_s_825_;
v_isShared_830_ = v_isSharedCheck_835_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_state_827_);
lean_inc(v_importedEntries_826_);
lean_dec(v_s_825_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_835_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v_state_831_; lean_object* v___x_833_; 
v_state_831_ = lean_apply_2(v_addEntryFn_823_, v_state_827_, v___x_824_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 1, v_state_831_);
v___x_833_ = v___x_829_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_importedEntries_826_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v_state_831_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object* v_as_836_, size_t v_i_837_, size_t v_stop_838_, lean_object* v_b_839_){
_start:
{
lean_object* v___y_841_; uint8_t v___x_845_; 
v___x_845_ = lean_usize_dec_eq(v_i_837_, v_stop_838_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; lean_object* v_toEnvExtension_847_; lean_object* v_addEntryFn_848_; lean_object* v_asyncMode_849_; uint8_t v_logWrites_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___f_853_; uint8_t v___x_854_; 
v___x_846_ = l_Lean_Compiler_LCNF_impureSigExt;
v_toEnvExtension_847_ = lean_ctor_get(v___x_846_, 0);
v_addEntryFn_848_ = lean_ctor_get(v___x_846_, 3);
v_asyncMode_849_ = lean_ctor_get(v_toEnvExtension_847_, 2);
v_logWrites_850_ = lean_ctor_get_uint8(v_toEnvExtension_847_, sizeof(void*)*6);
v___x_851_ = lean_box(0);
v___x_852_ = lean_array_uget_borrowed(v_as_836_, v_i_837_);
lean_inc(v___x_852_);
lean_inc(v_addEntryFn_848_);
v___f_853_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___lam__0), 3, 2);
lean_closure_set(v___f_853_, 0, v_addEntryFn_848_);
lean_closure_set(v___f_853_, 1, v___x_852_);
v___x_854_ = 1;
if (v_logWrites_850_ == 0)
{
lean_object* v___x_855_; 
lean_inc_ref(v_toEnvExtension_847_);
v___x_855_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_847_, v_b_839_, v___f_853_, v_asyncMode_849_, v___x_851_, v___x_854_);
v___y_841_ = v___x_855_;
goto v___jp_840_;
}
else
{
lean_object* v___x_856_; lean_object* v___x_857_; 
lean_inc_ref_n(v_toEnvExtension_847_, 2);
v___x_856_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite___redArg(v_toEnvExtension_847_, v_b_839_);
lean_dec_ref(v_b_839_);
v___x_857_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_847_, v___x_856_, v___f_853_, v_asyncMode_849_, v___x_851_, v___x_854_);
v___y_841_ = v___x_857_;
goto v___jp_840_;
}
}
else
{
return v_b_839_;
}
v___jp_840_:
{
size_t v___x_842_; size_t v___x_843_; 
v___x_842_ = ((size_t)1ULL);
v___x_843_ = lean_usize_add(v_i_837_, v___x_842_);
v_i_837_ = v___x_843_;
v_b_839_ = v___y_841_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object* v_as_858_, lean_object* v_i_859_, lean_object* v_stop_860_, lean_object* v_b_861_){
_start:
{
size_t v_i_boxed_862_; size_t v_stop_boxed_863_; lean_object* v_res_864_; 
v_i_boxed_862_ = lean_unbox_usize(v_i_859_);
lean_dec(v_i_859_);
v_stop_boxed_863_ = lean_unbox_usize(v_stop_860_);
lean_dec(v_stop_860_);
v_res_864_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v_as_858_, v_i_boxed_862_, v_stop_boxed_863_, v_b_861_);
lean_dec_ref(v_as_858_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object* v___y_866_, lean_object* v_as_867_, size_t v_i_868_, size_t v_stop_869_, lean_object* v_b_870_){
_start:
{
lean_object* v___y_872_; uint8_t v___x_876_; 
v___x_876_ = lean_usize_dec_eq(v_i_868_, v_stop_869_);
if (v___x_876_ == 0)
{
lean_object* v_fst_877_; lean_object* v_snd_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___y_882_; 
v_fst_877_ = lean_ctor_get(v_b_870_, 0);
v_snd_878_ = lean_ctor_get(v_b_870_, 1);
v___x_879_ = lean_array_uget_borrowed(v_as_867_, v_i_868_);
v___x_880_ = l_Lean_IR_Decl_name(v___x_879_);
if (lean_obj_tag(v___x_880_) == 1)
{
lean_object* v_pre_895_; lean_object* v_str_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
v_pre_895_ = lean_ctor_get(v___x_880_, 0);
v_str_896_ = lean_ctor_get(v___x_880_, 1);
v___x_897_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___closed__0));
v___x_898_ = lean_string_dec_eq(v_str_896_, v___x_897_);
if (v___x_898_ == 0)
{
lean_inc_ref(v___x_880_);
v___y_882_ = v___x_880_;
goto v___jp_881_;
}
else
{
lean_inc(v_pre_895_);
v___y_882_ = v_pre_895_;
goto v___jp_881_;
}
}
else
{
lean_inc(v___x_880_);
v___y_882_ = v___x_880_;
goto v___jp_881_;
}
v___jp_881_:
{
uint8_t v___x_883_; 
lean_inc_ref(v___y_866_);
v___x_883_ = l_Lean_isExtern(v___y_866_, v___y_882_);
if (v___x_883_ == 0)
{
lean_dec(v___x_880_);
v___y_872_ = v_b_870_;
goto v___jp_871_;
}
else
{
lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_892_; 
lean_inc(v_snd_878_);
lean_inc(v_fst_877_);
v_isSharedCheck_892_ = !lean_is_exclusive(v_b_870_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; lean_object* v_unused_894_; 
v_unused_893_ = lean_ctor_get(v_b_870_, 1);
lean_dec(v_unused_893_);
v_unused_894_ = lean_ctor_get(v_b_870_, 0);
lean_dec(v_unused_894_);
v___x_885_ = v_b_870_;
v_isShared_886_ = v_isSharedCheck_892_;
goto v_resetjp_884_;
}
else
{
lean_dec(v_b_870_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_892_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
lean_inc_n(v___x_879_, 2);
v___x_887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_879_);
lean_ctor_set(v___x_887_, 1, v_fst_877_);
v___x_888_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_878_, v___x_880_, v___x_879_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 1, v___x_888_);
lean_ctor_set(v___x_885_, 0, v___x_887_);
v___x_890_ = v___x_885_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v___x_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
v___y_872_ = v___x_890_;
goto v___jp_871_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_866_);
return v_b_870_;
}
v___jp_871_:
{
size_t v___x_873_; size_t v___x_874_; 
v___x_873_ = ((size_t)1ULL);
v___x_874_ = lean_usize_add(v_i_868_, v___x_873_);
v_i_868_ = v___x_874_;
v_b_870_ = v___y_872_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object* v___y_899_, lean_object* v_as_900_, lean_object* v_i_901_, lean_object* v_stop_902_, lean_object* v_b_903_){
_start:
{
size_t v_i_boxed_904_; size_t v_stop_boxed_905_; lean_object* v_res_906_; 
v_i_boxed_904_ = lean_unbox_usize(v_i_901_);
lean_dec(v_i_901_);
v_stop_boxed_905_ = lean_unbox_usize(v_stop_902_);
lean_dec(v_stop_902_);
v_res_906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_899_, v_as_900_, v_i_boxed_904_, v_stop_boxed_905_, v_b_903_);
lean_dec_ref(v_as_900_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27(lean_object* v_as_910_, size_t v_sz_911_, size_t v_i_912_, lean_object* v_b_913_){
_start:
{
uint8_t v___x_915_; 
v___x_915_ = lean_usize_dec_lt(v_i_912_, v_sz_911_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; 
v___x_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_916_, 0, v_b_913_);
return v___x_916_;
}
else
{
uint8_t v___x_917_; lean_object* v_a_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec_ref(v_b_913_);
v___x_917_ = 0;
v_a_918_ = lean_array_uget_borrowed(v_as_910_, v_i_912_);
lean_inc(v_a_918_);
v___x_919_ = l_Lean_Message_toString(v_a_918_, v___x_917_);
v___x_920_ = l_IO_eprintln___at___00main_spec__6(v___x_919_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v___x_921_; size_t v___x_922_; size_t v___x_923_; 
lean_dec_ref_known(v___x_920_, 1);
v___x_921_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_922_ = ((size_t)1ULL);
v___x_923_ = lean_usize_add(v_i_912_, v___x_922_);
v_i_912_ = v___x_923_;
v_b_913_ = v___x_921_;
goto _start;
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
v_a_925_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_920_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_920_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___boxed(lean_object* v_as_933_, lean_object* v_sz_934_, lean_object* v_i_935_, lean_object* v_b_936_, lean_object* v___y_937_){
_start:
{
size_t v_sz_boxed_938_; size_t v_i_boxed_939_; lean_object* v_res_940_; 
v_sz_boxed_938_ = lean_unbox_usize(v_sz_934_);
lean_dec(v_sz_934_);
v_i_boxed_939_ = lean_unbox_usize(v_i_935_);
lean_dec(v_i_935_);
v_res_940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27(v_as_933_, v_sz_boxed_938_, v_i_boxed_939_, v_b_936_);
lean_dec_ref(v_as_933_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(lean_object* v_as_941_, size_t v_sz_942_, size_t v_i_943_, lean_object* v_b_944_){
_start:
{
uint8_t v___x_946_; 
v___x_946_ = lean_usize_dec_lt(v_i_943_, v_sz_942_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; 
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v_b_944_);
return v___x_947_;
}
else
{
uint8_t v___x_948_; lean_object* v_a_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
lean_dec_ref(v_b_944_);
v___x_948_ = 0;
v_a_949_ = lean_array_uget_borrowed(v_as_941_, v_i_943_);
lean_inc(v_a_949_);
v___x_950_ = l_Lean_Message_toString(v_a_949_, v___x_948_);
v___x_951_ = l_IO_eprintln___at___00main_spec__6(v___x_950_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v___x_952_; size_t v___x_953_; size_t v___x_954_; lean_object* v___x_955_; 
lean_dec_ref_known(v___x_951_, 1);
v___x_952_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_953_ = ((size_t)1ULL);
v___x_954_ = lean_usize_add(v_i_943_, v___x_953_);
v___x_955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27(v_as_941_, v_sz_942_, v___x_954_, v___x_952_);
return v___x_955_;
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
v_a_956_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_951_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_951_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13___boxed(lean_object* v_as_964_, lean_object* v_sz_965_, lean_object* v_i_966_, lean_object* v_b_967_, lean_object* v___y_968_){
_start:
{
size_t v_sz_boxed_969_; size_t v_i_boxed_970_; lean_object* v_res_971_; 
v_sz_boxed_969_ = lean_unbox_usize(v_sz_965_);
lean_dec(v_sz_965_);
v_i_boxed_970_ = lean_unbox_usize(v_i_966_);
lean_dec(v_i_966_);
v_res_971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_as_964_, v_sz_boxed_969_, v_i_boxed_970_, v_b_967_);
lean_dec_ref(v_as_964_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(lean_object* v_init_972_, lean_object* v_n_973_, lean_object* v_b_974_){
_start:
{
if (lean_obj_tag(v_n_973_) == 0)
{
lean_object* v_cs_976_; lean_object* v___x_977_; lean_object* v___x_978_; size_t v_sz_979_; size_t v___x_980_; lean_object* v___x_981_; 
v_cs_976_ = lean_ctor_get(v_n_973_, 0);
v___x_977_ = lean_box(0);
v___x_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v_b_974_);
v_sz_979_ = lean_array_size(v_cs_976_);
v___x_980_ = ((size_t)0ULL);
v___x_981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12(v_init_972_, v_cs_976_, v_sz_979_, v___x_980_, v___x_978_);
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
else
{
lean_object* v_vs_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; size_t v_sz_1008_; size_t v___x_1009_; lean_object* v___x_1010_; 
v_vs_1005_ = lean_ctor_get(v_n_973_, 0);
v___x_1006_ = lean_box(0);
v___x_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v_b_974_);
v_sz_1008_ = lean_array_size(v_vs_1005_);
v___x_1009_ = ((size_t)0ULL);
v___x_1010_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_vs_1005_, v_sz_1008_, v___x_1009_, v___x_1007_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1025_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1013_ = v___x_1010_;
v_isShared_1014_ = v_isSharedCheck_1025_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1010_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1025_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v_fst_1015_; 
v_fst_1015_ = lean_ctor_get(v_a_1011_, 0);
if (lean_obj_tag(v_fst_1015_) == 0)
{
lean_object* v_snd_1016_; lean_object* v___x_1017_; lean_object* v___x_1019_; 
v_snd_1016_ = lean_ctor_get(v_a_1011_, 1);
lean_inc(v_snd_1016_);
lean_dec(v_a_1011_);
v___x_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1017_, 0, v_snd_1016_);
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
else
{
lean_object* v_val_1021_; lean_object* v___x_1023_; 
lean_inc_ref(v_fst_1015_);
lean_dec(v_a_1011_);
v_val_1021_ = lean_ctor_get(v_fst_1015_, 0);
lean_inc(v_val_1021_);
lean_dec_ref_known(v_fst_1015_, 1);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v_val_1021_);
v___x_1023_ = v___x_1013_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_val_1021_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
v_a_1026_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1010_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1010_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12(lean_object* v_init_1034_, lean_object* v_as_1035_, size_t v_sz_1036_, size_t v_i_1037_, lean_object* v_b_1038_){
_start:
{
uint8_t v___x_1040_; 
v___x_1040_ = lean_usize_dec_lt(v_i_1037_, v_sz_1036_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1041_, 0, v_b_1038_);
return v___x_1041_;
}
else
{
lean_object* v_snd_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1076_; 
v_snd_1042_ = lean_ctor_get(v_b_1038_, 1);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_b_1038_);
if (v_isSharedCheck_1076_ == 0)
{
lean_object* v_unused_1077_; 
v_unused_1077_ = lean_ctor_get(v_b_1038_, 0);
lean_dec(v_unused_1077_);
v___x_1044_ = v_b_1038_;
v_isShared_1045_ = v_isSharedCheck_1076_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_snd_1042_);
lean_dec(v_b_1038_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1076_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1046_; lean_object* v_a_1047_; lean_object* v___x_1048_; 
v___x_1046_ = lean_box(0);
v_a_1047_ = lean_array_uget_borrowed(v_as_1035_, v_i_1037_);
lean_inc(v_snd_1042_);
v___x_1048_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_1034_, v_a_1047_, v_snd_1042_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1067_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1051_ = v___x_1048_;
v_isShared_1052_ = v_isSharedCheck_1067_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1048_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1067_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
if (lean_obj_tag(v_a_1049_) == 0)
{
lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1053_, 0, v_a_1049_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v___x_1053_);
v___x_1055_ = v___x_1044_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_snd_1042_);
v___x_1055_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1057_; 
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
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; 
lean_del_object(v___x_1051_);
lean_dec(v_snd_1042_);
v_a_1060_ = lean_ctor_get(v_a_1049_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v_a_1049_, 1);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 1, v_a_1060_);
lean_ctor_set(v___x_1044_, 0, v___x_1046_);
v___x_1062_ = v___x_1044_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v_a_1060_);
v___x_1062_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
size_t v___x_1063_; size_t v___x_1064_; 
v___x_1063_ = ((size_t)1ULL);
v___x_1064_ = lean_usize_add(v_i_1037_, v___x_1063_);
v_i_1037_ = v___x_1064_;
v_b_1038_ = v___x_1062_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
lean_del_object(v___x_1044_);
lean_dec(v_snd_1042_);
v_a_1068_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1048_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1048_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12___boxed(lean_object* v_init_1078_, lean_object* v_as_1079_, lean_object* v_sz_1080_, lean_object* v_i_1081_, lean_object* v_b_1082_, lean_object* v___y_1083_){
_start:
{
size_t v_sz_boxed_1084_; size_t v_i_boxed_1085_; lean_object* v_res_1086_; 
v_sz_boxed_1084_ = lean_unbox_usize(v_sz_1080_);
lean_dec(v_sz_1080_);
v_i_boxed_1085_ = lean_unbox_usize(v_i_1081_);
lean_dec(v_i_1081_);
v_res_1086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12(v_init_1078_, v_as_1079_, v_sz_boxed_1084_, v_i_boxed_1085_, v_b_1082_);
lean_dec_ref(v_as_1079_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10___boxed(lean_object* v_init_1087_, lean_object* v_n_1088_, lean_object* v_b_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_1087_, v_n_1088_, v_b_1089_);
lean_dec_ref(v_n_1088_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15(lean_object* v_as_1095_, size_t v_sz_1096_, size_t v_i_1097_, lean_object* v_b_1098_){
_start:
{
uint8_t v___x_1100_; 
v___x_1100_ = lean_usize_dec_lt(v_i_1097_, v_sz_1096_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; 
v___x_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1101_, 0, v_b_1098_);
return v___x_1101_;
}
else
{
uint8_t v___x_1102_; lean_object* v_a_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_dec_ref(v_b_1098_);
v___x_1102_ = 0;
v_a_1103_ = lean_array_uget_borrowed(v_as_1095_, v_i_1097_);
lean_inc(v_a_1103_);
v___x_1104_ = l_Lean_Message_toString(v_a_1103_, v___x_1102_);
v___x_1105_ = l_IO_eprintln___at___00main_spec__6(v___x_1104_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v___x_1106_; size_t v___x_1107_; size_t v___x_1108_; 
lean_dec_ref_known(v___x_1105_, 1);
v___x_1106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_1107_ = ((size_t)1ULL);
v___x_1108_ = lean_usize_add(v_i_1097_, v___x_1107_);
v_i_1097_ = v___x_1108_;
v_b_1098_ = v___x_1106_;
goto _start;
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
v_a_1110_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1105_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1105_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___boxed(lean_object* v_as_1118_, lean_object* v_sz_1119_, lean_object* v_i_1120_, lean_object* v_b_1121_, lean_object* v___y_1122_){
_start:
{
size_t v_sz_boxed_1123_; size_t v_i_boxed_1124_; lean_object* v_res_1125_; 
v_sz_boxed_1123_ = lean_unbox_usize(v_sz_1119_);
lean_dec(v_sz_1119_);
v_i_boxed_1124_ = lean_unbox_usize(v_i_1120_);
lean_dec(v_i_1120_);
v_res_1125_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15(v_as_1118_, v_sz_boxed_1123_, v_i_boxed_1124_, v_b_1121_);
lean_dec_ref(v_as_1118_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(lean_object* v_as_1126_, size_t v_sz_1127_, size_t v_i_1128_, lean_object* v_b_1129_){
_start:
{
uint8_t v___x_1131_; 
v___x_1131_ = lean_usize_dec_lt(v_i_1128_, v_sz_1127_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1132_, 0, v_b_1129_);
return v___x_1132_;
}
else
{
uint8_t v___x_1133_; lean_object* v_a_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
lean_dec_ref(v_b_1129_);
v___x_1133_ = 0;
v_a_1134_ = lean_array_uget_borrowed(v_as_1126_, v_i_1128_);
lean_inc(v_a_1134_);
v___x_1135_ = l_Lean_Message_toString(v_a_1134_, v___x_1133_);
v___x_1136_ = l_IO_eprintln___at___00main_spec__6(v___x_1135_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v___x_1137_; size_t v___x_1138_; size_t v___x_1139_; lean_object* v___x_1140_; 
lean_dec_ref_known(v___x_1136_, 1);
v___x_1137_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_1138_ = ((size_t)1ULL);
v___x_1139_ = lean_usize_add(v_i_1128_, v___x_1138_);
v___x_1140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15(v_as_1126_, v_sz_1127_, v___x_1139_, v___x_1137_);
return v___x_1140_;
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
v_a_1141_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1136_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1136_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11___boxed(lean_object* v_as_1149_, lean_object* v_sz_1150_, lean_object* v_i_1151_, lean_object* v_b_1152_, lean_object* v___y_1153_){
_start:
{
size_t v_sz_boxed_1154_; size_t v_i_boxed_1155_; lean_object* v_res_1156_; 
v_sz_boxed_1154_ = lean_unbox_usize(v_sz_1150_);
lean_dec(v_sz_1150_);
v_i_boxed_1155_ = lean_unbox_usize(v_i_1151_);
lean_dec(v_i_1151_);
v_res_1156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_as_1149_, v_sz_boxed_1154_, v_i_boxed_1155_, v_b_1152_);
lean_dec_ref(v_as_1149_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7(lean_object* v_t_1157_, lean_object* v_init_1158_){
_start:
{
lean_object* v_root_1160_; lean_object* v_tail_1161_; lean_object* v___x_1162_; 
v_root_1160_ = lean_ctor_get(v_t_1157_, 0);
v_tail_1161_ = lean_ctor_get(v_t_1157_, 1);
v___x_1162_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_1158_, v_root_1160_, v_init_1158_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1199_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1165_ = v___x_1162_;
v_isShared_1166_ = v_isSharedCheck_1199_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1162_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1199_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
if (lean_obj_tag(v_a_1163_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1169_; 
v_a_1167_ = lean_ctor_get(v_a_1163_, 0);
lean_inc(v_a_1167_);
lean_dec_ref_known(v_a_1163_, 1);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v_a_1167_);
v___x_1169_ = v___x_1165_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; size_t v_sz_1174_; size_t v___x_1175_; lean_object* v___x_1176_; 
lean_del_object(v___x_1165_);
v_a_1171_ = lean_ctor_get(v_a_1163_, 0);
lean_inc(v_a_1171_);
lean_dec_ref_known(v_a_1163_, 1);
v___x_1172_ = lean_box(0);
v___x_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
lean_ctor_set(v___x_1173_, 1, v_a_1171_);
v_sz_1174_ = lean_array_size(v_tail_1161_);
v___x_1175_ = ((size_t)0ULL);
v___x_1176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_tail_1161_, v_sz_1174_, v___x_1175_, v___x_1173_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1190_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1179_ = v___x_1176_;
v_isShared_1180_ = v_isSharedCheck_1190_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1176_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1190_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v_fst_1181_; 
v_fst_1181_ = lean_ctor_get(v_a_1177_, 0);
if (lean_obj_tag(v_fst_1181_) == 0)
{
lean_object* v_snd_1182_; lean_object* v___x_1184_; 
v_snd_1182_ = lean_ctor_get(v_a_1177_, 1);
lean_inc(v_snd_1182_);
lean_dec(v_a_1177_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v_snd_1182_);
v___x_1184_ = v___x_1179_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_snd_1182_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
else
{
lean_object* v_val_1186_; lean_object* v___x_1188_; 
lean_inc_ref(v_fst_1181_);
lean_dec(v_a_1177_);
v_val_1186_ = lean_ctor_get(v_fst_1181_, 0);
lean_inc(v_val_1186_);
lean_dec_ref_known(v_fst_1181_, 1);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v_val_1186_);
v___x_1188_ = v___x_1179_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_val_1186_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
v_a_1191_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1176_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1176_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
v_a_1200_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1162_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1162_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7___boxed(lean_object* v_t_1208_, lean_object* v_init_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_t_1208_, v_init_1209_);
lean_dec_ref(v_t_1208_);
return v_res_1211_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0(uint8_t v_suppressElabErrors_1219_, lean_object* v_x_1220_){
_start:
{
if (lean_obj_tag(v_x_1220_) == 1)
{
lean_object* v_pre_1221_; 
v_pre_1221_ = lean_ctor_get(v_x_1220_, 0);
switch(lean_obj_tag(v_pre_1221_))
{
case 1:
{
lean_object* v_pre_1222_; 
v_pre_1222_ = lean_ctor_get(v_pre_1221_, 0);
switch(lean_obj_tag(v_pre_1222_))
{
case 0:
{
lean_object* v_str_1223_; lean_object* v_str_1224_; lean_object* v___x_1225_; uint8_t v___x_1226_; 
v_str_1223_ = lean_ctor_get(v_x_1220_, 1);
v_str_1224_ = lean_ctor_get(v_pre_1221_, 1);
v___x_1225_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__0));
v___x_1226_ = lean_string_dec_eq(v_str_1224_, v___x_1225_);
if (v___x_1226_ == 0)
{
lean_object* v___x_1227_; uint8_t v___x_1228_; 
v___x_1227_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__1));
v___x_1228_ = lean_string_dec_eq(v_str_1224_, v___x_1227_);
if (v___x_1228_ == 0)
{
return v___x_1228_;
}
else
{
lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__2));
v___x_1230_ = lean_string_dec_eq(v_str_1223_, v___x_1229_);
if (v___x_1230_ == 0)
{
return v___x_1230_;
}
else
{
return v_suppressElabErrors_1219_;
}
}
}
else
{
lean_object* v___x_1231_; uint8_t v___x_1232_; 
v___x_1231_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__3));
v___x_1232_ = lean_string_dec_eq(v_str_1223_, v___x_1231_);
if (v___x_1232_ == 0)
{
return v___x_1232_;
}
else
{
return v_suppressElabErrors_1219_;
}
}
}
case 1:
{
lean_object* v_pre_1233_; 
v_pre_1233_ = lean_ctor_get(v_pre_1222_, 0);
if (lean_obj_tag(v_pre_1233_) == 0)
{
lean_object* v_str_1234_; lean_object* v_str_1235_; lean_object* v_str_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
v_str_1234_ = lean_ctor_get(v_x_1220_, 1);
v_str_1235_ = lean_ctor_get(v_pre_1221_, 1);
v_str_1236_ = lean_ctor_get(v_pre_1222_, 1);
v___x_1237_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__4));
v___x_1238_ = lean_string_dec_eq(v_str_1236_, v___x_1237_);
if (v___x_1238_ == 0)
{
return v___x_1238_;
}
else
{
lean_object* v___x_1239_; uint8_t v___x_1240_; 
v___x_1239_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__5));
v___x_1240_ = lean_string_dec_eq(v_str_1235_, v___x_1239_);
if (v___x_1240_ == 0)
{
return v___x_1240_;
}
else
{
lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1241_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__6));
v___x_1242_ = lean_string_dec_eq(v_str_1234_, v___x_1241_);
if (v___x_1242_ == 0)
{
return v___x_1242_;
}
else
{
return v_suppressElabErrors_1219_;
}
}
}
}
else
{
uint8_t v___x_1243_; 
v___x_1243_ = 0;
return v___x_1243_;
}
}
default: 
{
uint8_t v___x_1244_; 
v___x_1244_ = 0;
return v___x_1244_;
}
}
}
case 0:
{
lean_object* v_str_1245_; lean_object* v___x_1246_; uint8_t v___x_1247_; 
v_str_1245_ = lean_ctor_get(v_x_1220_, 1);
v___x_1246_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_1247_ = lean_string_dec_eq(v_str_1245_, v___x_1246_);
if (v___x_1247_ == 0)
{
return v___x_1247_;
}
else
{
return v_suppressElabErrors_1219_;
}
}
default: 
{
uint8_t v___x_1248_; 
v___x_1248_ = 0;
return v___x_1248_;
}
}
}
else
{
uint8_t v___x_1249_; 
v___x_1249_ = 0;
return v___x_1249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___boxed(lean_object* v_suppressElabErrors_1250_, lean_object* v_x_1251_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1252_; uint8_t v_res_1253_; lean_object* v_r_1254_; 
v_suppressElabErrors_boxed_1252_ = lean_unbox(v_suppressElabErrors_1250_);
v_res_1253_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0(v_suppressElabErrors_boxed_1252_, v_x_1251_);
lean_dec(v_x_1251_);
v_r_1254_ = lean_box(v_res_1253_);
return v_r_1254_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(lean_object* v_opts_1255_, lean_object* v_opt_1256_){
_start:
{
lean_object* v_name_1257_; lean_object* v_defValue_1258_; lean_object* v_map_1259_; lean_object* v___x_1260_; 
v_name_1257_ = lean_ctor_get(v_opt_1256_, 0);
v_defValue_1258_ = lean_ctor_get(v_opt_1256_, 1);
v_map_1259_ = lean_ctor_get(v_opts_1255_, 0);
v___x_1260_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1259_, v_name_1257_);
if (lean_obj_tag(v___x_1260_) == 0)
{
uint8_t v___x_1261_; 
v___x_1261_ = lean_unbox(v_defValue_1258_);
return v___x_1261_;
}
else
{
lean_object* v_val_1262_; 
v_val_1262_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_val_1262_);
lean_dec_ref_known(v___x_1260_, 1);
if (lean_obj_tag(v_val_1262_) == 1)
{
uint8_t v_v_1263_; 
v_v_1263_ = lean_ctor_get_uint8(v_val_1262_, 0);
lean_dec_ref_known(v_val_1262_, 0);
return v_v_1263_;
}
else
{
uint8_t v___x_1264_; 
lean_dec(v_val_1262_);
v___x_1264_ = lean_unbox(v_defValue_1258_);
return v___x_1264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___boxed(lean_object* v_opts_1265_, lean_object* v_opt_1266_){
_start:
{
uint8_t v_res_1267_; lean_object* v_r_1268_; 
v_res_1267_ = l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(v_opts_1265_, v_opt_1266_);
lean_dec_ref(v_opt_1266_);
lean_dec_ref(v_opts_1265_);
v_r_1268_ = lean_box(v_res_1267_);
return v_r_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44(lean_object* v_ref_1270_, lean_object* v_msgData_1271_, uint8_t v_severity_1272_, uint8_t v_isSilent_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v___y_1278_; uint8_t v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; uint8_t v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v_toCold_1285_; lean_object* v___y_1286_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; uint8_t v___y_1318_; lean_object* v___y_1319_; uint8_t v___y_1320_; uint8_t v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1342_; uint8_t v___y_1343_; lean_object* v___y_1344_; uint8_t v___y_1345_; uint8_t v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; uint8_t v___y_1352_; uint8_t v___y_1353_; uint8_t v___x_1363_; uint8_t v___y_1365_; uint8_t v___x_1371_; 
v___x_1363_ = 2;
v___x_1371_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1272_, v___x_1363_);
if (v___x_1371_ == 0)
{
v___y_1365_ = v___x_1371_;
goto v___jp_1364_;
}
else
{
uint8_t v___x_1372_; 
lean_inc_ref(v_msgData_1271_);
v___x_1372_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1271_);
if (v___x_1372_ == 0)
{
v___y_1365_ = v___x_1372_;
goto v___jp_1364_;
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
lean_dec_ref(v_msgData_1271_);
v___x_1373_ = lean_box(0);
v___x_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
return v___x_1374_;
}
}
v___jp_1277_:
{
lean_object* v_currNamespace_1287_; lean_object* v_openDecls_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v_env_1293_; lean_object* v_nextMacroScope_1294_; lean_object* v_ngen_1295_; lean_object* v_auxDeclNGen_1296_; lean_object* v_traceState_1297_; lean_object* v_cache_1298_; lean_object* v_recordedDeps_1299_; lean_object* v_messages_1300_; lean_object* v_infoState_1301_; lean_object* v_snapshotTasks_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1313_; 
v_currNamespace_1287_ = lean_ctor_get(v_toCold_1285_, 4);
v_openDecls_1288_ = lean_ctor_get(v_toCold_1285_, 5);
lean_inc(v_openDecls_1288_);
lean_inc(v_currNamespace_1287_);
v___x_1289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1289_, 0, v_currNamespace_1287_);
lean_ctor_set(v___x_1289_, 1, v_openDecls_1288_);
v___x_1290_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
lean_ctor_set(v___x_1290_, 1, v___y_1280_);
lean_inc_ref(v___y_1281_);
lean_inc_ref(v___y_1283_);
v___x_1291_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1291_, 0, v___y_1283_);
lean_ctor_set(v___x_1291_, 1, v___y_1284_);
lean_ctor_set(v___x_1291_, 2, v___y_1278_);
lean_ctor_set(v___x_1291_, 3, v___y_1281_);
lean_ctor_set(v___x_1291_, 4, v___x_1290_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*5, v___y_1282_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*5 + 1, v___y_1279_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*5 + 2, v_isSilent_1273_);
v___x_1292_ = lean_st_ref_take(v___y_1286_);
v_env_1293_ = lean_ctor_get(v___x_1292_, 0);
v_nextMacroScope_1294_ = lean_ctor_get(v___x_1292_, 1);
v_ngen_1295_ = lean_ctor_get(v___x_1292_, 2);
v_auxDeclNGen_1296_ = lean_ctor_get(v___x_1292_, 3);
v_traceState_1297_ = lean_ctor_get(v___x_1292_, 4);
v_cache_1298_ = lean_ctor_get(v___x_1292_, 5);
v_recordedDeps_1299_ = lean_ctor_get(v___x_1292_, 6);
v_messages_1300_ = lean_ctor_get(v___x_1292_, 7);
v_infoState_1301_ = lean_ctor_get(v___x_1292_, 8);
v_snapshotTasks_1302_ = lean_ctor_get(v___x_1292_, 9);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1304_ = v___x_1292_;
v_isShared_1305_ = v_isSharedCheck_1313_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_snapshotTasks_1302_);
lean_inc(v_infoState_1301_);
lean_inc(v_messages_1300_);
lean_inc(v_recordedDeps_1299_);
lean_inc(v_cache_1298_);
lean_inc(v_traceState_1297_);
lean_inc(v_auxDeclNGen_1296_);
lean_inc(v_ngen_1295_);
lean_inc(v_nextMacroScope_1294_);
lean_inc(v_env_1293_);
lean_dec(v___x_1292_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1313_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1309_; 
v___x_1306_ = lean_box(0);
v___x_1307_ = l_Lean_MessageLog_add(v___x_1291_, v_messages_1300_);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 7, v___x_1307_);
v___x_1309_ = v___x_1304_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_env_1293_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v_nextMacroScope_1294_);
lean_ctor_set(v_reuseFailAlloc_1312_, 2, v_ngen_1295_);
lean_ctor_set(v_reuseFailAlloc_1312_, 3, v_auxDeclNGen_1296_);
lean_ctor_set(v_reuseFailAlloc_1312_, 4, v_traceState_1297_);
lean_ctor_set(v_reuseFailAlloc_1312_, 5, v_cache_1298_);
lean_ctor_set(v_reuseFailAlloc_1312_, 6, v_recordedDeps_1299_);
lean_ctor_set(v_reuseFailAlloc_1312_, 7, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1312_, 8, v_infoState_1301_);
lean_ctor_set(v_reuseFailAlloc_1312_, 9, v_snapshotTasks_1302_);
v___x_1309_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = lean_st_ref_put(v___y_1286_, v___x_1309_);
v___x_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1306_);
return v___x_1311_;
}
}
}
v___jp_1314_:
{
lean_object* v_fileName_1323_; lean_object* v_fileMap_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1340_; 
v_fileName_1323_ = lean_ctor_get(v___y_1317_, 0);
v_fileMap_1324_ = lean_ctor_get(v___y_1317_, 1);
v___x_1325_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1271_);
v___x_1326_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v___x_1325_, v___y_1274_, v___y_1275_);
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1329_ = v___x_1326_;
v_isShared_1330_ = v_isSharedCheck_1340_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1326_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1340_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
lean_inc_ref_n(v_fileMap_1324_, 2);
v___x_1331_ = l_Lean_FileMap_toPosition(v_fileMap_1324_, v___y_1319_);
lean_dec(v___y_1319_);
v___x_1332_ = l_Lean_FileMap_toPosition(v_fileMap_1324_, v___y_1322_);
lean_dec(v___y_1322_);
v___x_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
v___x_1334_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___closed__0));
if (v___y_1318_ == 0)
{
lean_del_object(v___x_1329_);
lean_dec_ref(v___y_1316_);
v___y_1278_ = v___x_1333_;
v___y_1279_ = v___y_1320_;
v___y_1280_ = v_a_1327_;
v___y_1281_ = v___x_1334_;
v___y_1282_ = v___y_1321_;
v___y_1283_ = v_fileName_1323_;
v___y_1284_ = v___x_1331_;
v_toCold_1285_ = v___y_1315_;
v___y_1286_ = v___y_1275_;
goto v___jp_1277_;
}
else
{
uint8_t v___x_1335_; 
lean_inc(v_a_1327_);
v___x_1335_ = l_Lean_MessageData_hasTag(v___y_1316_, v_a_1327_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; lean_object* v___x_1338_; 
lean_dec_ref_known(v___x_1333_, 1);
lean_dec_ref(v___x_1331_);
lean_dec(v_a_1327_);
v___x_1336_ = lean_box(0);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v___x_1336_);
v___x_1338_ = v___x_1329_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
else
{
lean_del_object(v___x_1329_);
v___y_1278_ = v___x_1333_;
v___y_1279_ = v___y_1320_;
v___y_1280_ = v_a_1327_;
v___y_1281_ = v___x_1334_;
v___y_1282_ = v___y_1321_;
v___y_1283_ = v_fileName_1323_;
v___y_1284_ = v___x_1331_;
v_toCold_1285_ = v___y_1315_;
v___y_1286_ = v___y_1275_;
goto v___jp_1277_;
}
}
}
}
v___jp_1341_:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_Syntax_getTailPos_x3f(v___y_1347_, v___y_1346_);
lean_dec(v___y_1347_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_inc(v___y_1348_);
v___y_1315_ = v___y_1342_;
v___y_1316_ = v___y_1344_;
v___y_1317_ = v___y_1342_;
v___y_1318_ = v___y_1343_;
v___y_1319_ = v___y_1348_;
v___y_1320_ = v___y_1345_;
v___y_1321_ = v___y_1346_;
v___y_1322_ = v___y_1348_;
goto v___jp_1314_;
}
else
{
lean_object* v_val_1350_; 
v_val_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_val_1350_);
lean_dec_ref_known(v___x_1349_, 1);
v___y_1315_ = v___y_1342_;
v___y_1316_ = v___y_1344_;
v___y_1317_ = v___y_1342_;
v___y_1318_ = v___y_1343_;
v___y_1319_ = v___y_1348_;
v___y_1320_ = v___y_1345_;
v___y_1321_ = v___y_1346_;
v___y_1322_ = v_val_1350_;
goto v___jp_1314_;
}
}
v___jp_1351_:
{
lean_object* v_toCold_1354_; lean_object* v_ref_1355_; uint8_t v_suppressElabErrors_1356_; lean_object* v___x_1357_; lean_object* v___f_1358_; lean_object* v_ref_1359_; lean_object* v___x_1360_; 
v_toCold_1354_ = lean_ctor_get(v___y_1274_, 0);
v_ref_1355_ = lean_ctor_get(v___y_1274_, 2);
v_suppressElabErrors_1356_ = lean_ctor_get_uint8(v___y_1274_, sizeof(void*)*3 + 2);
v___x_1357_ = lean_box(v_suppressElabErrors_1356_);
v___f_1358_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1358_, 0, v___x_1357_);
v_ref_1359_ = l_Lean_replaceRef(v_ref_1270_, v_ref_1355_);
v___x_1360_ = l_Lean_Syntax_getPos_x3f(v_ref_1359_, v___y_1352_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v___x_1361_; 
v___x_1361_ = lean_unsigned_to_nat(0u);
v___y_1342_ = v_toCold_1354_;
v___y_1343_ = v_suppressElabErrors_1356_;
v___y_1344_ = v___f_1358_;
v___y_1345_ = v___y_1353_;
v___y_1346_ = v___y_1352_;
v___y_1347_ = v_ref_1359_;
v___y_1348_ = v___x_1361_;
goto v___jp_1341_;
}
else
{
lean_object* v_val_1362_; 
v_val_1362_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_val_1362_);
lean_dec_ref_known(v___x_1360_, 1);
v___y_1342_ = v_toCold_1354_;
v___y_1343_ = v_suppressElabErrors_1356_;
v___y_1344_ = v___f_1358_;
v___y_1345_ = v___y_1353_;
v___y_1346_ = v___y_1352_;
v___y_1347_ = v_ref_1359_;
v___y_1348_ = v_val_1362_;
goto v___jp_1341_;
}
}
v___jp_1364_:
{
uint8_t v___x_1366_; uint8_t v___x_1367_; 
v___x_1366_ = 1;
v___x_1367_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1272_, v___x_1366_);
if (v___x_1367_ == 0)
{
v___y_1352_ = v___y_1365_;
v___y_1353_ = v_severity_1272_;
goto v___jp_1351_;
}
else
{
lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1368_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1274_);
v___x_1369_ = l_Lean_warningAsError;
v___x_1370_ = l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(v___x_1368_, v___x_1369_);
lean_dec_ref(v___x_1368_);
if (v___x_1370_ == 0)
{
v___y_1352_ = v___y_1365_;
v___y_1353_ = v_severity_1272_;
goto v___jp_1351_;
}
else
{
v___y_1352_ = v___y_1365_;
v___y_1353_ = v___x_1363_;
goto v___jp_1351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___boxed(lean_object* v_ref_1375_, lean_object* v_msgData_1376_, lean_object* v_severity_1377_, lean_object* v_isSilent_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
uint8_t v_severity_boxed_1382_; uint8_t v_isSilent_boxed_1383_; lean_object* v_res_1384_; 
v_severity_boxed_1382_ = lean_unbox(v_severity_1377_);
v_isSilent_boxed_1383_ = lean_unbox(v_isSilent_1378_);
v_res_1384_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44(v_ref_1375_, v_msgData_1376_, v_severity_boxed_1382_, v_isSilent_boxed_1383_, v___y_1379_, v___y_1380_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec(v_ref_1375_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30(lean_object* v_msgData_1385_, uint8_t v_severity_1386_, uint8_t v_isSilent_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v_ref_1391_; lean_object* v___x_1392_; 
v_ref_1391_ = lean_ctor_get(v___y_1388_, 2);
v___x_1392_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44(v_ref_1391_, v_msgData_1385_, v_severity_1386_, v_isSilent_1387_, v___y_1388_, v___y_1389_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30___boxed(lean_object* v_msgData_1393_, lean_object* v_severity_1394_, lean_object* v_isSilent_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
uint8_t v_severity_boxed_1399_; uint8_t v_isSilent_boxed_1400_; lean_object* v_res_1401_; 
v_severity_boxed_1399_ = lean_unbox(v_severity_1394_);
v_isSilent_boxed_1400_ = lean_unbox(v_isSilent_1395_);
v_res_1401_ = l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30(v_msgData_1393_, v_severity_boxed_1399_, v_isSilent_boxed_1400_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13(lean_object* v_msgData_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
uint8_t v___x_1406_; uint8_t v___x_1407_; lean_object* v___x_1408_; 
v___x_1406_ = 2;
v___x_1407_ = 0;
v___x_1408_ = l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30(v_msgData_1402_, v___x_1406_, v___x_1407_, v___y_1403_, v___y_1404_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13___boxed(lean_object* v_msgData_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lean_logError___at___00main_spec__13(v_msgData_1409_, v___y_1410_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(lean_object* v_opts_1414_, lean_object* v_opt_1415_){
_start:
{
lean_object* v_name_1416_; lean_object* v_map_1417_; lean_object* v___x_1418_; 
v_name_1416_ = lean_ctor_get(v_opt_1415_, 0);
v_map_1417_ = lean_ctor_get(v_opts_1414_, 0);
v___x_1418_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1417_, v_name_1416_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_box(0);
return v___x_1419_;
}
else
{
lean_object* v_val_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1429_; 
v_val_1420_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1422_ = v___x_1418_;
v_isShared_1423_ = v_isSharedCheck_1429_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_val_1420_);
lean_dec(v___x_1418_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1429_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
if (lean_obj_tag(v_val_1420_) == 0)
{
lean_object* v_v_1424_; lean_object* v___x_1426_; 
v_v_1424_ = lean_ctor_get(v_val_1420_, 0);
lean_inc_ref(v_v_1424_);
lean_dec_ref_known(v_val_1420_, 1);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 0, v_v_1424_);
v___x_1426_ = v___x_1422_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_v_1424_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
else
{
lean_object* v___x_1428_; 
lean_del_object(v___x_1422_);
lean_dec(v_val_1420_);
v___x_1428_ = lean_box(0);
return v___x_1428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___boxed(lean_object* v_opts_1430_, lean_object* v_opt_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(v_opts_1430_, v_opt_1431_);
lean_dec_ref(v_opt_1431_);
lean_dec_ref(v_opts_1430_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22(lean_object* v_x_1433_, lean_object* v_x_1434_){
_start:
{
if (lean_obj_tag(v_x_1434_) == 0)
{
return v_x_1433_;
}
else
{
lean_object* v_key_1435_; lean_object* v_value_1436_; lean_object* v_tail_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v_key_1435_ = lean_ctor_get(v_x_1434_, 0);
v_value_1436_ = lean_ctor_get(v_x_1434_, 1);
v_tail_1437_ = lean_ctor_get(v_x_1434_, 2);
lean_inc(v_value_1436_);
lean_inc(v_key_1435_);
v___x_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1438_, 0, v_key_1435_);
lean_ctor_set(v___x_1438_, 1, v_value_1436_);
v___x_1439_ = lean_array_push(v_x_1433_, v___x_1438_);
v_x_1433_ = v___x_1439_;
v_x_1434_ = v_tail_1437_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22___boxed(lean_object* v_x_1441_, lean_object* v_x_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22(v_x_1441_, v_x_1442_);
lean_dec(v_x_1442_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23(lean_object* v_as_1444_, size_t v_i_1445_, size_t v_stop_1446_, lean_object* v_b_1447_){
_start:
{
uint8_t v___x_1448_; 
v___x_1448_ = lean_usize_dec_eq(v_i_1445_, v_stop_1446_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; lean_object* v___x_1450_; size_t v___x_1451_; size_t v___x_1452_; 
v___x_1449_ = lean_array_uget_borrowed(v_as_1444_, v_i_1445_);
v___x_1450_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22(v_b_1447_, v___x_1449_);
v___x_1451_ = ((size_t)1ULL);
v___x_1452_ = lean_usize_add(v_i_1445_, v___x_1451_);
v_i_1445_ = v___x_1452_;
v_b_1447_ = v___x_1450_;
goto _start;
}
else
{
return v_b_1447_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23___boxed(lean_object* v_as_1454_, lean_object* v_i_1455_, lean_object* v_stop_1456_, lean_object* v_b_1457_){
_start:
{
size_t v_i_boxed_1458_; size_t v_stop_boxed_1459_; lean_object* v_res_1460_; 
v_i_boxed_1458_ = lean_unbox_usize(v_i_1455_);
lean_dec(v_i_1455_);
v_stop_boxed_1459_ = lean_unbox_usize(v_stop_1456_);
lean_dec(v_stop_1456_);
v_res_1460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23(v_as_1454_, v_i_boxed_1458_, v_stop_boxed_1459_, v_b_1457_);
lean_dec_ref(v_as_1454_);
return v_res_1460_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(lean_object* v_x_1461_, lean_object* v_x_1462_){
_start:
{
lean_object* v_fst_1463_; lean_object* v_fst_1464_; lean_object* v_fst_1465_; lean_object* v_fst_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v_fst_1463_ = lean_ctor_get(v_x_1461_, 0);
v_fst_1464_ = lean_ctor_get(v_x_1462_, 0);
v_fst_1465_ = lean_ctor_get(v_fst_1463_, 0);
v_fst_1466_ = lean_ctor_get(v_fst_1464_, 0);
v___x_1467_ = lean_unsigned_to_nat(1u);
v___x_1468_ = lean_nat_add(v_fst_1465_, v___x_1467_);
v___x_1469_ = lean_nat_dec_le(v___x_1468_, v_fst_1466_);
lean_dec(v___x_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0___boxed(lean_object* v_x_1470_, lean_object* v_x_1471_){
_start:
{
uint8_t v_res_1472_; lean_object* v_r_1473_; 
v_res_1472_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v_x_1470_, v_x_1471_);
lean_dec_ref(v_x_1471_);
lean_dec_ref(v_x_1470_);
v_r_1473_ = lean_box(v_res_1472_);
return v_r_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(lean_object* v_hi_1474_, lean_object* v_pivot_1475_, lean_object* v_as_1476_, lean_object* v_i_1477_, lean_object* v_k_1478_){
_start:
{
uint8_t v___x_1479_; 
v___x_1479_ = lean_nat_dec_lt(v_k_1478_, v_hi_1474_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
lean_dec(v_k_1478_);
v___x_1480_ = lean_array_fswap(v_as_1476_, v_i_1477_, v_hi_1474_);
v___x_1481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1481_, 0, v_i_1477_);
lean_ctor_set(v___x_1481_, 1, v___x_1480_);
return v___x_1481_;
}
else
{
lean_object* v___x_1482_; lean_object* v_fst_1483_; lean_object* v_fst_1484_; lean_object* v_fst_1485_; lean_object* v_fst_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; uint8_t v___x_1489_; 
v___x_1482_ = lean_array_fget_borrowed(v_as_1476_, v_k_1478_);
v_fst_1483_ = lean_ctor_get(v___x_1482_, 0);
v_fst_1484_ = lean_ctor_get(v_pivot_1475_, 0);
v_fst_1485_ = lean_ctor_get(v_fst_1483_, 0);
v_fst_1486_ = lean_ctor_get(v_fst_1484_, 0);
v___x_1487_ = lean_unsigned_to_nat(1u);
v___x_1488_ = lean_nat_add(v_fst_1485_, v___x_1487_);
v___x_1489_ = lean_nat_dec_le(v___x_1488_, v_fst_1486_);
lean_dec(v___x_1488_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_nat_add(v_k_1478_, v___x_1487_);
lean_dec(v_k_1478_);
v_k_1478_ = v___x_1490_;
goto _start;
}
else
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1492_ = lean_array_fswap(v_as_1476_, v_i_1477_, v_k_1478_);
v___x_1493_ = lean_nat_add(v_i_1477_, v___x_1487_);
lean_dec(v_i_1477_);
v___x_1494_ = lean_nat_add(v_k_1478_, v___x_1487_);
lean_dec(v_k_1478_);
v_as_1476_ = v___x_1492_;
v_i_1477_ = v___x_1493_;
v_k_1478_ = v___x_1494_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg___boxed(lean_object* v_hi_1496_, lean_object* v_pivot_1497_, lean_object* v_as_1498_, lean_object* v_i_1499_, lean_object* v_k_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(v_hi_1496_, v_pivot_1497_, v_as_1498_, v_i_1499_, v_k_1500_);
lean_dec_ref(v_pivot_1497_);
lean_dec(v_hi_1496_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(lean_object* v_n_1502_, lean_object* v_as_1503_, lean_object* v_lo_1504_, lean_object* v_hi_1505_){
_start:
{
lean_object* v___y_1507_; uint8_t v___x_1517_; 
v___x_1517_ = lean_nat_dec_lt(v_lo_1504_, v_hi_1505_);
if (v___x_1517_ == 0)
{
lean_dec(v_lo_1504_);
return v_as_1503_;
}
else
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v_mid_1520_; lean_object* v___y_1522_; lean_object* v___y_1528_; lean_object* v___x_1533_; lean_object* v___x_1534_; uint8_t v___x_1535_; 
v___x_1518_ = lean_nat_add(v_lo_1504_, v_hi_1505_);
v___x_1519_ = lean_unsigned_to_nat(1u);
v_mid_1520_ = lean_nat_shiftr(v___x_1518_, v___x_1519_);
lean_dec(v___x_1518_);
v___x_1533_ = lean_array_fget_borrowed(v_as_1503_, v_mid_1520_);
v___x_1534_ = lean_array_fget_borrowed(v_as_1503_, v_lo_1504_);
v___x_1535_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v___x_1533_, v___x_1534_);
if (v___x_1535_ == 0)
{
v___y_1528_ = v_as_1503_;
goto v___jp_1527_;
}
else
{
lean_object* v___x_1536_; 
v___x_1536_ = lean_array_fswap(v_as_1503_, v_lo_1504_, v_mid_1520_);
v___y_1528_ = v___x_1536_;
goto v___jp_1527_;
}
v___jp_1521_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; 
v___x_1523_ = lean_array_fget_borrowed(v___y_1522_, v_mid_1520_);
v___x_1524_ = lean_array_fget_borrowed(v___y_1522_, v_hi_1505_);
v___x_1525_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v___x_1523_, v___x_1524_);
if (v___x_1525_ == 0)
{
lean_dec(v_mid_1520_);
v___y_1507_ = v___y_1522_;
goto v___jp_1506_;
}
else
{
lean_object* v___x_1526_; 
v___x_1526_ = lean_array_fswap(v___y_1522_, v_mid_1520_, v_hi_1505_);
lean_dec(v_mid_1520_);
v___y_1507_ = v___x_1526_;
goto v___jp_1506_;
}
}
v___jp_1527_:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
v___x_1529_ = lean_array_fget_borrowed(v___y_1528_, v_hi_1505_);
v___x_1530_ = lean_array_fget_borrowed(v___y_1528_, v_lo_1504_);
v___x_1531_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v___x_1529_, v___x_1530_);
if (v___x_1531_ == 0)
{
v___y_1522_ = v___y_1528_;
goto v___jp_1521_;
}
else
{
lean_object* v___x_1532_; 
v___x_1532_ = lean_array_fswap(v___y_1528_, v_lo_1504_, v_hi_1505_);
v___y_1522_ = v___x_1532_;
goto v___jp_1521_;
}
}
}
v___jp_1506_:
{
lean_object* v_pivot_1508_; lean_object* v___x_1509_; lean_object* v_fst_1510_; lean_object* v_snd_1511_; uint8_t v___x_1512_; 
v_pivot_1508_ = lean_array_fget(v___y_1507_, v_hi_1505_);
lean_inc_n(v_lo_1504_, 2);
v___x_1509_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(v_hi_1505_, v_pivot_1508_, v___y_1507_, v_lo_1504_, v_lo_1504_);
lean_dec(v_pivot_1508_);
v_fst_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_fst_1510_);
v_snd_1511_ = lean_ctor_get(v___x_1509_, 1);
lean_inc(v_snd_1511_);
lean_dec_ref(v___x_1509_);
v___x_1512_ = lean_nat_dec_le(v_hi_1505_, v_fst_1510_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1513_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v_n_1502_, v_snd_1511_, v_lo_1504_, v_fst_1510_);
v___x_1514_ = lean_unsigned_to_nat(1u);
v___x_1515_ = lean_nat_add(v_fst_1510_, v___x_1514_);
lean_dec(v_fst_1510_);
v_as_1503_ = v___x_1513_;
v_lo_1504_ = v___x_1515_;
goto _start;
}
else
{
lean_dec(v_fst_1510_);
lean_dec(v_lo_1504_);
return v_snd_1511_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___boxed(lean_object* v_n_1537_, lean_object* v_as_1538_, lean_object* v_lo_1539_, lean_object* v_hi_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v_n_1537_, v_as_1538_, v_lo_1539_, v_hi_1540_);
lean_dec(v_hi_1540_);
lean_dec(v_n_1537_);
return v_res_1541_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0(uint8_t v_suppressElabErrors_1542_, uint8_t v___x_1543_, lean_object* v___x_1544_, lean_object* v_x_1545_){
_start:
{
if (lean_obj_tag(v_x_1545_) == 1)
{
lean_object* v_pre_1546_; 
v_pre_1546_ = lean_ctor_get(v_x_1545_, 0);
switch(lean_obj_tag(v_pre_1546_))
{
case 1:
{
lean_object* v_pre_1547_; 
v_pre_1547_ = lean_ctor_get(v_pre_1546_, 0);
switch(lean_obj_tag(v_pre_1547_))
{
case 0:
{
lean_object* v_str_1548_; lean_object* v_str_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; 
v_str_1548_ = lean_ctor_get(v_x_1545_, 1);
v_str_1549_ = lean_ctor_get(v_pre_1546_, 1);
v___x_1550_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__0));
v___x_1551_ = lean_string_dec_eq(v_str_1549_, v___x_1550_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; uint8_t v___x_1553_; 
v___x_1552_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__1));
v___x_1553_ = lean_string_dec_eq(v_str_1549_, v___x_1552_);
if (v___x_1553_ == 0)
{
return v___x_1553_;
}
else
{
lean_object* v___x_1554_; uint8_t v___x_1555_; 
v___x_1554_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__2));
v___x_1555_ = lean_string_dec_eq(v_str_1548_, v___x_1554_);
if (v___x_1555_ == 0)
{
return v___x_1555_;
}
else
{
return v_suppressElabErrors_1542_;
}
}
}
else
{
lean_object* v___x_1556_; uint8_t v___x_1557_; 
v___x_1556_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__3));
v___x_1557_ = lean_string_dec_eq(v_str_1548_, v___x_1556_);
if (v___x_1557_ == 0)
{
return v___x_1557_;
}
else
{
return v_suppressElabErrors_1542_;
}
}
}
case 1:
{
lean_object* v_pre_1558_; 
v_pre_1558_ = lean_ctor_get(v_pre_1547_, 0);
if (lean_obj_tag(v_pre_1558_) == 0)
{
lean_object* v_str_1559_; lean_object* v_str_1560_; lean_object* v_str_1561_; lean_object* v___x_1562_; uint8_t v___x_1563_; 
v_str_1559_ = lean_ctor_get(v_x_1545_, 1);
v_str_1560_ = lean_ctor_get(v_pre_1546_, 1);
v_str_1561_ = lean_ctor_get(v_pre_1547_, 1);
v___x_1562_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__4));
v___x_1563_ = lean_string_dec_eq(v_str_1561_, v___x_1562_);
if (v___x_1563_ == 0)
{
return v___x_1563_;
}
else
{
lean_object* v___x_1564_; uint8_t v___x_1565_; 
v___x_1564_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__5));
v___x_1565_ = lean_string_dec_eq(v_str_1560_, v___x_1564_);
if (v___x_1565_ == 0)
{
return v___x_1565_;
}
else
{
lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___x_1566_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__6));
v___x_1567_ = lean_string_dec_eq(v_str_1559_, v___x_1566_);
if (v___x_1567_ == 0)
{
return v___x_1567_;
}
else
{
return v_suppressElabErrors_1542_;
}
}
}
}
else
{
return v___x_1543_;
}
}
default: 
{
return v___x_1543_;
}
}
}
case 0:
{
lean_object* v_str_1568_; uint8_t v___x_1569_; 
v_str_1568_ = lean_ctor_get(v_x_1545_, 1);
v___x_1569_ = lean_string_dec_eq(v_str_1568_, v___x_1544_);
if (v___x_1569_ == 0)
{
return v___x_1569_;
}
else
{
return v_suppressElabErrors_1542_;
}
}
default: 
{
return v___x_1543_;
}
}
}
else
{
return v___x_1543_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0___boxed(lean_object* v_suppressElabErrors_1570_, lean_object* v___x_1571_, lean_object* v___x_1572_, lean_object* v_x_1573_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1574_; uint8_t v___x_38749__boxed_1575_; uint8_t v_res_1576_; lean_object* v_r_1577_; 
v_suppressElabErrors_boxed_1574_ = lean_unbox(v_suppressElabErrors_1570_);
v___x_38749__boxed_1575_ = lean_unbox(v___x_1571_);
v_res_1576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0(v_suppressElabErrors_boxed_1574_, v___x_38749__boxed_1575_, v___x_1572_, v_x_1573_);
lean_dec(v_x_1573_);
lean_dec_ref(v___x_1572_);
v_r_1577_ = lean_box(v_res_1576_);
return v_r_1577_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0(void){
_start:
{
lean_object* v___x_1578_; double v___x_1579_; 
v___x_1578_ = lean_unsigned_to_nat(0u);
v___x_1579_ = lean_float_of_nat(v___x_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(uint8_t v___x_1580_, lean_object* v_as_1581_, size_t v_sz_1582_, size_t v_i_1583_, lean_object* v_b_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v_a_1589_; uint8_t v___x_1593_; 
v___x_1593_ = lean_usize_dec_lt(v_i_1583_, v_sz_1582_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; 
v___x_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1594_, 0, v_b_1584_);
return v___x_1594_;
}
else
{
lean_object* v_a_1595_; lean_object* v_fst_1596_; lean_object* v_snd_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1676_; 
v_a_1595_ = lean_array_uget(v_as_1581_, v_i_1583_);
v_fst_1596_ = lean_ctor_get(v_a_1595_, 0);
v_snd_1597_ = lean_ctor_get(v_a_1595_, 1);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_a_1595_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1599_ = v_a_1595_;
v_isShared_1600_ = v_isSharedCheck_1676_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_snd_1597_);
lean_inc(v_fst_1596_);
lean_dec(v_a_1595_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1676_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v_fst_1601_; lean_object* v_snd_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1675_; 
v_fst_1601_ = lean_ctor_get(v_fst_1596_, 0);
v_snd_1602_ = lean_ctor_get(v_fst_1596_, 1);
v_isSharedCheck_1675_ = !lean_is_exclusive(v_fst_1596_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1604_ = v_fst_1596_;
v_isShared_1605_ = v_isSharedCheck_1675_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_snd_1602_);
lean_inc(v_fst_1601_);
lean_dec(v_fst_1596_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1675_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; double v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v_toCold_1611_; uint8_t v_suppressElabErrors_1612_; lean_object* v_fileName_1613_; lean_object* v_fileMap_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1621_; 
v___x_1606_ = lean_box(0);
v___x_1607_ = lean_box(0);
v___x_1608_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0);
v___x_1609_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___closed__0));
v___x_1610_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1610_, 0, v___x_1606_);
lean_ctor_set(v___x_1610_, 1, v___x_1607_);
lean_ctor_set(v___x_1610_, 2, v___x_1609_);
lean_ctor_set_float(v___x_1610_, sizeof(void*)*3, v___x_1608_);
lean_ctor_set_float(v___x_1610_, sizeof(void*)*3 + 8, v___x_1608_);
lean_ctor_set_uint8(v___x_1610_, sizeof(void*)*3 + 16, v___x_1593_);
v_toCold_1611_ = lean_ctor_get(v___y_1585_, 0);
v_suppressElabErrors_1612_ = lean_ctor_get_uint8(v___y_1585_, sizeof(void*)*3 + 2);
v_fileName_1613_ = lean_ctor_get(v_toCold_1611_, 0);
v_fileMap_1614_ = lean_ctor_get(v_toCold_1611_, 1);
v___x_1615_ = lean_box(0);
v___x_1616_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_1617_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_1618_ = l_Lean_MessageData_nil;
v___x_1619_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1610_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
lean_ctor_set(v___x_1619_, 2, v_snd_1597_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set_tag(v___x_1604_, 8);
lean_ctor_set(v___x_1604_, 1, v___x_1619_);
lean_ctor_set(v___x_1604_, 0, v___x_1617_);
v___x_1621_ = v___x_1604_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1617_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
uint8_t v___x_1622_; lean_object* v___x_1623_; lean_object* v___y_1625_; lean_object* v___y_1626_; 
v___x_1622_ = 0;
lean_inc_ref(v_fileMap_1614_);
lean_inc_ref(v_fileName_1613_);
v___x_1623_ = l_Lean_Elab_mkMessageCore(v_fileName_1613_, v_fileMap_1614_, v___x_1621_, v___x_1622_, v_fst_1601_, v_snd_1602_);
lean_dec(v_snd_1602_);
lean_dec(v_fst_1601_);
if (v_suppressElabErrors_1612_ == 0)
{
v___y_1625_ = v___y_1585_;
v___y_1626_ = v___y_1586_;
goto v___jp_1624_;
}
else
{
lean_object* v_data_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___f_1672_; uint8_t v___x_1673_; 
v_data_1669_ = lean_ctor_get(v___x_1623_, 4);
v___x_1670_ = lean_box(v_suppressElabErrors_1612_);
v___x_1671_ = lean_box(v___x_1580_);
v___f_1672_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1672_, 0, v___x_1670_);
lean_closure_set(v___f_1672_, 1, v___x_1671_);
lean_closure_set(v___f_1672_, 2, v___x_1616_);
lean_inc(v_data_1669_);
v___x_1673_ = l_Lean_MessageData_hasTag(v___f_1672_, v_data_1669_);
if (v___x_1673_ == 0)
{
lean_dec_ref(v___x_1623_);
lean_del_object(v___x_1599_);
v_a_1589_ = v___x_1615_;
goto v___jp_1588_;
}
else
{
v___y_1625_ = v___y_1585_;
v___y_1626_ = v___y_1586_;
goto v___jp_1624_;
}
}
v___jp_1624_:
{
lean_object* v_toCold_1627_; lean_object* v_fileName_1628_; lean_object* v_pos_1629_; lean_object* v_endPos_1630_; uint8_t v_keepFullRange_1631_; uint8_t v_severity_1632_; uint8_t v_isSilent_1633_; lean_object* v_caption_1634_; lean_object* v_data_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1668_; 
v_toCold_1627_ = lean_ctor_get(v___y_1625_, 0);
v_fileName_1628_ = lean_ctor_get(v___x_1623_, 0);
v_pos_1629_ = lean_ctor_get(v___x_1623_, 1);
v_endPos_1630_ = lean_ctor_get(v___x_1623_, 2);
v_keepFullRange_1631_ = lean_ctor_get_uint8(v___x_1623_, sizeof(void*)*5);
v_severity_1632_ = lean_ctor_get_uint8(v___x_1623_, sizeof(void*)*5 + 1);
v_isSilent_1633_ = lean_ctor_get_uint8(v___x_1623_, sizeof(void*)*5 + 2);
v_caption_1634_ = lean_ctor_get(v___x_1623_, 3);
v_data_1635_ = lean_ctor_get(v___x_1623_, 4);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1637_ = v___x_1623_;
v_isShared_1638_ = v_isSharedCheck_1668_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_data_1635_);
lean_inc(v_caption_1634_);
lean_inc(v_endPos_1630_);
lean_inc(v_pos_1629_);
lean_inc(v_fileName_1628_);
lean_dec(v___x_1623_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1668_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v_currNamespace_1639_; lean_object* v_openDecls_1640_; lean_object* v___x_1642_; 
v_currNamespace_1639_ = lean_ctor_get(v_toCold_1627_, 4);
v_openDecls_1640_ = lean_ctor_get(v_toCold_1627_, 5);
lean_inc(v_openDecls_1640_);
lean_inc(v_currNamespace_1639_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 1, v_openDecls_1640_);
lean_ctor_set(v___x_1599_, 0, v_currNamespace_1639_);
v___x_1642_ = v___x_1599_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_currNamespace_1639_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_openDecls_1640_);
v___x_1642_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
lean_object* v___x_1643_; lean_object* v___x_1645_; 
v___x_1643_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
lean_ctor_set(v___x_1643_, 1, v_data_1635_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 4, v___x_1643_);
v___x_1645_ = v___x_1637_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_fileName_1628_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_pos_1629_);
lean_ctor_set(v_reuseFailAlloc_1666_, 2, v_endPos_1630_);
lean_ctor_set(v_reuseFailAlloc_1666_, 3, v_caption_1634_);
lean_ctor_set(v_reuseFailAlloc_1666_, 4, v___x_1643_);
lean_ctor_set_uint8(v_reuseFailAlloc_1666_, sizeof(void*)*5, v_keepFullRange_1631_);
lean_ctor_set_uint8(v_reuseFailAlloc_1666_, sizeof(void*)*5 + 1, v_severity_1632_);
lean_ctor_set_uint8(v_reuseFailAlloc_1666_, sizeof(void*)*5 + 2, v_isSilent_1633_);
v___x_1645_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
lean_object* v___x_1646_; lean_object* v_env_1647_; lean_object* v_nextMacroScope_1648_; lean_object* v_ngen_1649_; lean_object* v_auxDeclNGen_1650_; lean_object* v_traceState_1651_; lean_object* v_cache_1652_; lean_object* v_recordedDeps_1653_; lean_object* v_messages_1654_; lean_object* v_infoState_1655_; lean_object* v_snapshotTasks_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1665_; 
v___x_1646_ = lean_st_ref_take(v___y_1626_);
v_env_1647_ = lean_ctor_get(v___x_1646_, 0);
v_nextMacroScope_1648_ = lean_ctor_get(v___x_1646_, 1);
v_ngen_1649_ = lean_ctor_get(v___x_1646_, 2);
v_auxDeclNGen_1650_ = lean_ctor_get(v___x_1646_, 3);
v_traceState_1651_ = lean_ctor_get(v___x_1646_, 4);
v_cache_1652_ = lean_ctor_get(v___x_1646_, 5);
v_recordedDeps_1653_ = lean_ctor_get(v___x_1646_, 6);
v_messages_1654_ = lean_ctor_get(v___x_1646_, 7);
v_infoState_1655_ = lean_ctor_get(v___x_1646_, 8);
v_snapshotTasks_1656_ = lean_ctor_get(v___x_1646_, 9);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1658_ = v___x_1646_;
v_isShared_1659_ = v_isSharedCheck_1665_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_snapshotTasks_1656_);
lean_inc(v_infoState_1655_);
lean_inc(v_messages_1654_);
lean_inc(v_recordedDeps_1653_);
lean_inc(v_cache_1652_);
lean_inc(v_traceState_1651_);
lean_inc(v_auxDeclNGen_1650_);
lean_inc(v_ngen_1649_);
lean_inc(v_nextMacroScope_1648_);
lean_inc(v_env_1647_);
lean_dec(v___x_1646_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1665_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1660_; lean_object* v___x_1662_; 
v___x_1660_ = l_Lean_MessageLog_add(v___x_1645_, v_messages_1654_);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 7, v___x_1660_);
v___x_1662_ = v___x_1658_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_env_1647_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_nextMacroScope_1648_);
lean_ctor_set(v_reuseFailAlloc_1664_, 2, v_ngen_1649_);
lean_ctor_set(v_reuseFailAlloc_1664_, 3, v_auxDeclNGen_1650_);
lean_ctor_set(v_reuseFailAlloc_1664_, 4, v_traceState_1651_);
lean_ctor_set(v_reuseFailAlloc_1664_, 5, v_cache_1652_);
lean_ctor_set(v_reuseFailAlloc_1664_, 6, v_recordedDeps_1653_);
lean_ctor_set(v_reuseFailAlloc_1664_, 7, v___x_1660_);
lean_ctor_set(v_reuseFailAlloc_1664_, 8, v_infoState_1655_);
lean_ctor_set(v_reuseFailAlloc_1664_, 9, v_snapshotTasks_1656_);
v___x_1662_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1663_; 
v___x_1663_ = lean_st_ref_put(v___y_1626_, v___x_1662_);
v_a_1589_ = v___x_1615_;
goto v___jp_1588_;
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
v___jp_1588_:
{
size_t v___x_1590_; size_t v___x_1591_; 
v___x_1590_ = ((size_t)1ULL);
v___x_1591_ = lean_usize_add(v_i_1583_, v___x_1590_);
v_i_1583_ = v___x_1591_;
v_b_1584_ = v_a_1589_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___boxed(lean_object* v___x_1677_, lean_object* v_as_1678_, lean_object* v_sz_1679_, lean_object* v_i_1680_, lean_object* v_b_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
uint8_t v___x_38814__boxed_1685_; size_t v_sz_boxed_1686_; size_t v_i_boxed_1687_; lean_object* v_res_1688_; 
v___x_38814__boxed_1685_ = lean_unbox(v___x_1677_);
v_sz_boxed_1686_ = lean_unbox_usize(v_sz_1679_);
lean_dec(v_sz_1679_);
v_i_boxed_1687_ = lean_unbox_usize(v_i_1680_);
lean_dec(v_i_1680_);
v_res_1688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(v___x_38814__boxed_1685_, v_as_1678_, v_sz_boxed_1686_, v_i_boxed_1687_, v_b_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec_ref(v_as_1678_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(lean_object* v_a_1689_, lean_object* v_fallback_1690_, lean_object* v_x_1691_){
_start:
{
if (lean_obj_tag(v_x_1691_) == 0)
{
lean_inc(v_fallback_1690_);
return v_fallback_1690_;
}
else
{
lean_object* v_key_1692_; lean_object* v_value_1693_; lean_object* v_tail_1694_; lean_object* v_fst_1695_; lean_object* v_snd_1696_; lean_object* v_fst_1697_; lean_object* v_snd_1698_; uint8_t v_decide_1699_; 
v_key_1692_ = lean_ctor_get(v_x_1691_, 0);
v_value_1693_ = lean_ctor_get(v_x_1691_, 1);
v_tail_1694_ = lean_ctor_get(v_x_1691_, 2);
v_fst_1695_ = lean_ctor_get(v_key_1692_, 0);
v_snd_1696_ = lean_ctor_get(v_key_1692_, 1);
v_fst_1697_ = lean_ctor_get(v_a_1689_, 0);
v_snd_1698_ = lean_ctor_get(v_a_1689_, 1);
v_decide_1699_ = lean_nat_dec_eq(v_fst_1695_, v_fst_1697_);
if (v_decide_1699_ == 0)
{
v_x_1691_ = v_tail_1694_;
goto _start;
}
else
{
uint8_t v_decide_1701_; 
v_decide_1701_ = lean_nat_dec_eq(v_snd_1696_, v_snd_1698_);
if (v_decide_1701_ == 0)
{
v_x_1691_ = v_tail_1694_;
goto _start;
}
else
{
lean_inc(v_value_1693_);
return v_value_1693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg___boxed(lean_object* v_a_1703_, lean_object* v_fallback_1704_, lean_object* v_x_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(v_a_1703_, v_fallback_1704_, v_x_1705_);
lean_dec(v_x_1705_);
lean_dec(v_fallback_1704_);
lean_dec_ref(v_a_1703_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(lean_object* v_m_1707_, lean_object* v_a_1708_, lean_object* v_fallback_1709_){
_start:
{
lean_object* v_buckets_1710_; lean_object* v_fst_1711_; lean_object* v_snd_1712_; lean_object* v___x_1713_; uint64_t v___x_1714_; uint64_t v___x_1715_; uint64_t v___x_1716_; uint64_t v___x_1717_; uint64_t v___x_1718_; uint64_t v_fold_1719_; uint64_t v___x_1720_; uint64_t v___x_1721_; uint64_t v___x_1722_; size_t v___x_1723_; size_t v___x_1724_; size_t v___x_1725_; size_t v___x_1726_; size_t v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v_buckets_1710_ = lean_ctor_get(v_m_1707_, 1);
v_fst_1711_ = lean_ctor_get(v_a_1708_, 0);
v_snd_1712_ = lean_ctor_get(v_a_1708_, 1);
v___x_1713_ = lean_array_get_size(v_buckets_1710_);
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
v___x_1728_ = lean_array_uget_borrowed(v_buckets_1710_, v___x_1727_);
v___x_1729_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(v_a_1708_, v_fallback_1709_, v___x_1728_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg___boxed(lean_object* v_m_1730_, lean_object* v_a_1731_, lean_object* v_fallback_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_m_1730_, v_a_1731_, v_fallback_1732_);
lean_dec(v_fallback_1732_);
lean_dec_ref(v_a_1731_);
lean_dec_ref(v_m_1730_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44___redArg(lean_object* v_x_1734_, lean_object* v_x_1735_){
_start:
{
if (lean_obj_tag(v_x_1735_) == 0)
{
return v_x_1734_;
}
else
{
lean_object* v_key_1736_; lean_object* v_value_1737_; lean_object* v_tail_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1765_; 
v_key_1736_ = lean_ctor_get(v_x_1735_, 0);
v_value_1737_ = lean_ctor_get(v_x_1735_, 1);
v_tail_1738_ = lean_ctor_get(v_x_1735_, 2);
v_isSharedCheck_1765_ = !lean_is_exclusive(v_x_1735_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1740_ = v_x_1735_;
v_isShared_1741_ = v_isSharedCheck_1765_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_tail_1738_);
lean_inc(v_value_1737_);
lean_inc(v_key_1736_);
lean_dec(v_x_1735_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1765_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v_fst_1742_; lean_object* v_snd_1743_; lean_object* v___x_1744_; uint64_t v___x_1745_; uint64_t v___x_1746_; uint64_t v___x_1747_; uint64_t v___x_1748_; uint64_t v___x_1749_; uint64_t v_fold_1750_; uint64_t v___x_1751_; uint64_t v___x_1752_; uint64_t v___x_1753_; size_t v___x_1754_; size_t v___x_1755_; size_t v___x_1756_; size_t v___x_1757_; size_t v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1761_; 
v_fst_1742_ = lean_ctor_get(v_key_1736_, 0);
v_snd_1743_ = lean_ctor_get(v_key_1736_, 1);
v___x_1744_ = lean_array_get_size(v_x_1734_);
v___x_1745_ = l_String_instHashableRaw_hash(v_fst_1742_);
v___x_1746_ = l_String_instHashableRaw_hash(v_snd_1743_);
v___x_1747_ = lean_uint64_mix_hash(v___x_1745_, v___x_1746_);
v___x_1748_ = 32ULL;
v___x_1749_ = lean_uint64_shift_right(v___x_1747_, v___x_1748_);
v_fold_1750_ = lean_uint64_xor(v___x_1747_, v___x_1749_);
v___x_1751_ = 16ULL;
v___x_1752_ = lean_uint64_shift_right(v_fold_1750_, v___x_1751_);
v___x_1753_ = lean_uint64_xor(v_fold_1750_, v___x_1752_);
v___x_1754_ = lean_uint64_to_usize(v___x_1753_);
v___x_1755_ = lean_usize_of_nat(v___x_1744_);
v___x_1756_ = ((size_t)1ULL);
v___x_1757_ = lean_usize_sub(v___x_1755_, v___x_1756_);
v___x_1758_ = lean_usize_land(v___x_1754_, v___x_1757_);
v___x_1759_ = lean_array_uget_borrowed(v_x_1734_, v___x_1758_);
lean_inc(v___x_1759_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 2, v___x_1759_);
v___x_1761_ = v___x_1740_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_key_1736_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v_value_1737_);
lean_ctor_set(v_reuseFailAlloc_1764_, 2, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v___x_1762_; 
v___x_1762_ = lean_array_uset(v_x_1734_, v___x_1758_, v___x_1761_);
v_x_1734_ = v___x_1762_;
v_x_1735_ = v_tail_1738_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35___redArg(lean_object* v_i_1766_, lean_object* v_source_1767_, lean_object* v_target_1768_){
_start:
{
lean_object* v___x_1769_; uint8_t v___x_1770_; 
v___x_1769_ = lean_array_get_size(v_source_1767_);
v___x_1770_ = lean_nat_dec_lt(v_i_1766_, v___x_1769_);
if (v___x_1770_ == 0)
{
lean_dec_ref(v_source_1767_);
lean_dec(v_i_1766_);
return v_target_1768_;
}
else
{
lean_object* v_es_1771_; lean_object* v___x_1772_; lean_object* v_source_1773_; lean_object* v_target_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v_es_1771_ = lean_array_fget(v_source_1767_, v_i_1766_);
v___x_1772_ = lean_box(0);
v_source_1773_ = lean_array_fset(v_source_1767_, v_i_1766_, v___x_1772_);
v_target_1774_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44___redArg(v_target_1768_, v_es_1771_);
v___x_1775_ = lean_unsigned_to_nat(1u);
v___x_1776_ = lean_nat_add(v_i_1766_, v___x_1775_);
lean_dec(v_i_1766_);
v_i_1766_ = v___x_1776_;
v_source_1767_ = v_source_1773_;
v_target_1768_ = v_target_1774_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24___redArg(lean_object* v_data_1778_){
_start:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v_nbuckets_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1779_ = lean_array_get_size(v_data_1778_);
v___x_1780_ = lean_unsigned_to_nat(2u);
v_nbuckets_1781_ = lean_nat_mul(v___x_1779_, v___x_1780_);
v___x_1782_ = lean_unsigned_to_nat(0u);
v___x_1783_ = lean_box(0);
v___x_1784_ = lean_mk_array(v_nbuckets_1781_, v___x_1783_);
v___x_1785_ = lean_array_propagate_mark(v_data_1778_, v___x_1784_);
v___x_1786_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35___redArg(v___x_1782_, v_data_1778_, v___x_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(lean_object* v_a_1787_, lean_object* v_b_1788_, lean_object* v_x_1789_){
_start:
{
if (lean_obj_tag(v_x_1789_) == 0)
{
lean_dec(v_b_1788_);
lean_dec_ref(v_a_1787_);
return v_x_1789_;
}
else
{
lean_object* v_key_1790_; lean_object* v_value_1791_; lean_object* v_tail_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1808_; 
v_key_1790_ = lean_ctor_get(v_x_1789_, 0);
v_value_1791_ = lean_ctor_get(v_x_1789_, 1);
v_tail_1792_ = lean_ctor_get(v_x_1789_, 2);
v_isSharedCheck_1808_ = !lean_is_exclusive(v_x_1789_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1794_ = v_x_1789_;
v_isShared_1795_ = v_isSharedCheck_1808_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_tail_1792_);
lean_inc(v_value_1791_);
lean_inc(v_key_1790_);
lean_dec(v_x_1789_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1808_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v_fst_1801_; lean_object* v_snd_1802_; lean_object* v_fst_1803_; lean_object* v_snd_1804_; uint8_t v_decide_1805_; 
v_fst_1801_ = lean_ctor_get(v_key_1790_, 0);
v_snd_1802_ = lean_ctor_get(v_key_1790_, 1);
v_fst_1803_ = lean_ctor_get(v_a_1787_, 0);
v_snd_1804_ = lean_ctor_get(v_a_1787_, 1);
v_decide_1805_ = lean_nat_dec_eq(v_fst_1801_, v_fst_1803_);
if (v_decide_1805_ == 0)
{
goto v___jp_1796_;
}
else
{
uint8_t v_decide_1806_; 
v_decide_1806_ = lean_nat_dec_eq(v_snd_1802_, v_snd_1804_);
if (v_decide_1806_ == 0)
{
goto v___jp_1796_;
}
else
{
lean_object* v___x_1807_; 
lean_del_object(v___x_1794_);
lean_dec(v_value_1791_);
lean_dec(v_key_1790_);
v___x_1807_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1807_, 0, v_a_1787_);
lean_ctor_set(v___x_1807_, 1, v_b_1788_);
lean_ctor_set(v___x_1807_, 2, v_tail_1792_);
return v___x_1807_;
}
}
v___jp_1796_:
{
lean_object* v___x_1797_; lean_object* v___x_1799_; 
v___x_1797_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(v_a_1787_, v_b_1788_, v_tail_1792_);
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 2, v___x_1797_);
v___x_1799_ = v___x_1794_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_key_1790_);
lean_ctor_set(v_reuseFailAlloc_1800_, 1, v_value_1791_);
lean_ctor_set(v_reuseFailAlloc_1800_, 2, v___x_1797_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(lean_object* v_a_1809_, lean_object* v_x_1810_){
_start:
{
if (lean_obj_tag(v_x_1810_) == 0)
{
uint8_t v___x_1811_; 
v___x_1811_ = 0;
return v___x_1811_;
}
else
{
lean_object* v_key_1812_; lean_object* v_tail_1813_; lean_object* v_fst_1814_; lean_object* v_snd_1815_; lean_object* v_fst_1816_; lean_object* v_snd_1817_; uint8_t v_decide_1818_; 
v_key_1812_ = lean_ctor_get(v_x_1810_, 0);
v_tail_1813_ = lean_ctor_get(v_x_1810_, 2);
v_fst_1814_ = lean_ctor_get(v_key_1812_, 0);
v_snd_1815_ = lean_ctor_get(v_key_1812_, 1);
v_fst_1816_ = lean_ctor_get(v_a_1809_, 0);
v_snd_1817_ = lean_ctor_get(v_a_1809_, 1);
v_decide_1818_ = lean_nat_dec_eq(v_fst_1814_, v_fst_1816_);
if (v_decide_1818_ == 0)
{
v_x_1810_ = v_tail_1813_;
goto _start;
}
else
{
uint8_t v_decide_1820_; 
v_decide_1820_ = lean_nat_dec_eq(v_snd_1815_, v_snd_1817_);
if (v_decide_1820_ == 0)
{
v_x_1810_ = v_tail_1813_;
goto _start;
}
else
{
return v_decide_1820_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg___boxed(lean_object* v_a_1822_, lean_object* v_x_1823_){
_start:
{
uint8_t v_res_1824_; lean_object* v_r_1825_; 
v_res_1824_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(v_a_1822_, v_x_1823_);
lean_dec(v_x_1823_);
lean_dec_ref(v_a_1822_);
v_r_1825_ = lean_box(v_res_1824_);
return v_r_1825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(lean_object* v_m_1826_, lean_object* v_a_1827_, lean_object* v_b_1828_){
_start:
{
lean_object* v_size_1829_; lean_object* v_buckets_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1877_; 
v_size_1829_ = lean_ctor_get(v_m_1826_, 0);
v_buckets_1830_ = lean_ctor_get(v_m_1826_, 1);
v_isSharedCheck_1877_ = !lean_is_exclusive(v_m_1826_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1832_ = v_m_1826_;
v_isShared_1833_ = v_isSharedCheck_1877_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_buckets_1830_);
lean_inc(v_size_1829_);
lean_dec(v_m_1826_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1877_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v_fst_1834_; lean_object* v_snd_1835_; lean_object* v___x_1836_; uint64_t v___x_1837_; uint64_t v___x_1838_; uint64_t v___x_1839_; uint64_t v___x_1840_; uint64_t v___x_1841_; uint64_t v_fold_1842_; uint64_t v___x_1843_; uint64_t v___x_1844_; uint64_t v___x_1845_; size_t v___x_1846_; size_t v___x_1847_; size_t v___x_1848_; size_t v___x_1849_; size_t v___x_1850_; lean_object* v_bkt_1851_; uint8_t v___x_1852_; 
v_fst_1834_ = lean_ctor_get(v_a_1827_, 0);
v_snd_1835_ = lean_ctor_get(v_a_1827_, 1);
v___x_1836_ = lean_array_get_size(v_buckets_1830_);
v___x_1837_ = l_String_instHashableRaw_hash(v_fst_1834_);
v___x_1838_ = l_String_instHashableRaw_hash(v_snd_1835_);
v___x_1839_ = lean_uint64_mix_hash(v___x_1837_, v___x_1838_);
v___x_1840_ = 32ULL;
v___x_1841_ = lean_uint64_shift_right(v___x_1839_, v___x_1840_);
v_fold_1842_ = lean_uint64_xor(v___x_1839_, v___x_1841_);
v___x_1843_ = 16ULL;
v___x_1844_ = lean_uint64_shift_right(v_fold_1842_, v___x_1843_);
v___x_1845_ = lean_uint64_xor(v_fold_1842_, v___x_1844_);
v___x_1846_ = lean_uint64_to_usize(v___x_1845_);
v___x_1847_ = lean_usize_of_nat(v___x_1836_);
v___x_1848_ = ((size_t)1ULL);
v___x_1849_ = lean_usize_sub(v___x_1847_, v___x_1848_);
v___x_1850_ = lean_usize_land(v___x_1846_, v___x_1849_);
v_bkt_1851_ = lean_array_uget_borrowed(v_buckets_1830_, v___x_1850_);
v___x_1852_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(v_a_1827_, v_bkt_1851_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1853_; lean_object* v_size_x27_1854_; lean_object* v___x_1855_; lean_object* v_buckets_x27_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; uint8_t v___x_1862_; 
v___x_1853_ = lean_unsigned_to_nat(1u);
v_size_x27_1854_ = lean_nat_add(v_size_1829_, v___x_1853_);
lean_dec(v_size_1829_);
lean_inc(v_bkt_1851_);
v___x_1855_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1855_, 0, v_a_1827_);
lean_ctor_set(v___x_1855_, 1, v_b_1828_);
lean_ctor_set(v___x_1855_, 2, v_bkt_1851_);
v_buckets_x27_1856_ = lean_array_uset(v_buckets_1830_, v___x_1850_, v___x_1855_);
v___x_1857_ = lean_unsigned_to_nat(4u);
v___x_1858_ = lean_nat_mul(v_size_x27_1854_, v___x_1857_);
v___x_1859_ = lean_unsigned_to_nat(3u);
v___x_1860_ = lean_nat_div(v___x_1858_, v___x_1859_);
lean_dec(v___x_1858_);
v___x_1861_ = lean_array_get_size(v_buckets_x27_1856_);
v___x_1862_ = lean_nat_dec_le(v___x_1860_, v___x_1861_);
lean_dec(v___x_1860_);
if (v___x_1862_ == 0)
{
lean_object* v_val_1863_; lean_object* v___x_1865_; 
v_val_1863_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24___redArg(v_buckets_x27_1856_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 1, v_val_1863_);
lean_ctor_set(v___x_1832_, 0, v_size_x27_1854_);
v___x_1865_ = v___x_1832_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_size_x27_1854_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_val_1863_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
else
{
lean_object* v___x_1868_; 
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 1, v_buckets_x27_1856_);
lean_ctor_set(v___x_1832_, 0, v_size_x27_1854_);
v___x_1868_ = v___x_1832_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_size_x27_1854_);
lean_ctor_set(v_reuseFailAlloc_1869_, 1, v_buckets_x27_1856_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
else
{
lean_object* v___x_1870_; lean_object* v_buckets_x27_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1875_; 
lean_inc(v_bkt_1851_);
v___x_1870_ = lean_box(0);
v_buckets_x27_1871_ = lean_array_uset(v_buckets_1830_, v___x_1850_, v___x_1870_);
v___x_1872_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(v_a_1827_, v_b_1828_, v_bkt_1851_);
v___x_1873_ = lean_array_uset(v_buckets_x27_1871_, v___x_1850_, v___x_1872_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 1, v___x_1873_);
v___x_1875_ = v___x_1832_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_size_1829_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v___x_1873_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(uint8_t v___x_1880_, lean_object* v_as_1881_, size_t v_sz_1882_, size_t v_i_1883_, lean_object* v_b_1884_, lean_object* v___y_1885_){
_start:
{
uint8_t v___x_1887_; 
v___x_1887_ = lean_usize_dec_lt(v_i_1883_, v_sz_1882_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1888_; 
v___x_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1888_, 0, v_b_1884_);
return v___x_1888_;
}
else
{
lean_object* v_snd_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1926_; 
v_snd_1889_ = lean_ctor_get(v_b_1884_, 1);
v_isSharedCheck_1926_ = !lean_is_exclusive(v_b_1884_);
if (v_isSharedCheck_1926_ == 0)
{
lean_object* v_unused_1927_; 
v_unused_1927_ = lean_ctor_get(v_b_1884_, 0);
lean_dec(v_unused_1927_);
v___x_1891_ = v_b_1884_;
v_isShared_1892_ = v_isSharedCheck_1926_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_snd_1889_);
lean_dec(v_b_1884_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1926_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v_ref_1893_; lean_object* v_a_1894_; lean_object* v_ref_1895_; lean_object* v_msg_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1925_; 
v_ref_1893_ = lean_ctor_get(v___y_1885_, 2);
v_a_1894_ = lean_array_uget(v_as_1881_, v_i_1883_);
v_ref_1895_ = lean_ctor_get(v_a_1894_, 0);
v_msg_1896_ = lean_ctor_get(v_a_1894_, 1);
v_isSharedCheck_1925_ = !lean_is_exclusive(v_a_1894_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1898_ = v_a_1894_;
v_isShared_1899_ = v_isSharedCheck_1925_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_msg_1896_);
lean_inc(v_ref_1895_);
lean_dec(v_a_1894_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1925_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1900_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v_ref_1917_; lean_object* v___y_1919_; lean_object* v___x_1922_; 
v___x_1900_ = lean_box(0);
v_ref_1917_ = l_Lean_replaceRef(v_ref_1895_, v_ref_1893_);
lean_dec(v_ref_1895_);
v___x_1922_ = l_Lean_Syntax_getPos_x3f(v_ref_1917_, v___x_1880_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v___x_1923_; 
v___x_1923_ = lean_unsigned_to_nat(0u);
v___y_1919_ = v___x_1923_;
goto v___jp_1918_;
}
else
{
lean_object* v_val_1924_; 
v_val_1924_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_val_1924_);
lean_dec_ref_known(v___x_1922_, 1);
v___y_1919_ = v_val_1924_;
goto v___jp_1918_;
}
v___jp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 1, v___y_1903_);
lean_ctor_set(v___x_1891_, 0, v___y_1902_);
v___x_1905_ = v___x_1891_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___y_1902_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v___y_1903_);
v___x_1905_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v_pos2traces_1909_; lean_object* v___x_1911_; 
v___x_1906_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1907_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1889_, v___x_1905_, v___x_1906_);
v___x_1908_ = lean_array_push(v___x_1907_, v_msg_1896_);
v_pos2traces_1909_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_1889_, v___x_1905_, v___x_1908_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 1, v_pos2traces_1909_);
lean_ctor_set(v___x_1898_, 0, v___x_1900_);
v___x_1911_ = v___x_1898_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1900_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v_pos2traces_1909_);
v___x_1911_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
size_t v___x_1912_; size_t v___x_1913_; 
v___x_1912_ = ((size_t)1ULL);
v___x_1913_ = lean_usize_add(v_i_1883_, v___x_1912_);
v_i_1883_ = v___x_1913_;
v_b_1884_ = v___x_1911_;
goto _start;
}
}
}
v___jp_1918_:
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1917_, v___x_1880_);
lean_dec(v_ref_1917_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_inc(v___y_1919_);
v___y_1902_ = v___y_1919_;
v___y_1903_ = v___y_1919_;
goto v___jp_1901_;
}
else
{
lean_object* v_val_1921_; 
v_val_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_val_1921_);
lean_dec_ref_known(v___x_1920_, 1);
v___y_1902_ = v___y_1919_;
v___y_1903_ = v_val_1921_;
goto v___jp_1901_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___boxed(lean_object* v___x_1928_, lean_object* v_as_1929_, lean_object* v_sz_1930_, lean_object* v_i_1931_, lean_object* v_b_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
uint8_t v___x_39260__boxed_1935_; size_t v_sz_boxed_1936_; size_t v_i_boxed_1937_; lean_object* v_res_1938_; 
v___x_39260__boxed_1935_ = lean_unbox(v___x_1928_);
v_sz_boxed_1936_ = lean_unbox_usize(v_sz_1930_);
lean_dec(v_sz_1930_);
v_i_boxed_1937_ = lean_unbox_usize(v_i_1931_);
lean_dec(v_i_1931_);
v_res_1938_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(v___x_39260__boxed_1935_, v_as_1929_, v_sz_boxed_1936_, v_i_boxed_1937_, v_b_1932_, v___y_1933_);
lean_dec_ref(v___y_1933_);
lean_dec_ref(v_as_1929_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40(uint8_t v___x_1939_, lean_object* v_as_1940_, size_t v_sz_1941_, size_t v_i_1942_, lean_object* v_b_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
uint8_t v___x_1947_; 
v___x_1947_ = lean_usize_dec_lt(v_i_1942_, v_sz_1941_);
if (v___x_1947_ == 0)
{
lean_object* v___x_1948_; 
v___x_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1948_, 0, v_b_1943_);
return v___x_1948_;
}
else
{
lean_object* v_snd_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1986_; 
v_snd_1949_ = lean_ctor_get(v_b_1943_, 1);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_b_1943_);
if (v_isSharedCheck_1986_ == 0)
{
lean_object* v_unused_1987_; 
v_unused_1987_ = lean_ctor_get(v_b_1943_, 0);
lean_dec(v_unused_1987_);
v___x_1951_ = v_b_1943_;
v_isShared_1952_ = v_isSharedCheck_1986_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_snd_1949_);
lean_dec(v_b_1943_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1986_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v_ref_1953_; lean_object* v_a_1954_; lean_object* v_ref_1955_; lean_object* v_msg_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1985_; 
v_ref_1953_ = lean_ctor_get(v___y_1944_, 2);
v_a_1954_ = lean_array_uget(v_as_1940_, v_i_1942_);
v_ref_1955_ = lean_ctor_get(v_a_1954_, 0);
v_msg_1956_ = lean_ctor_get(v_a_1954_, 1);
v_isSharedCheck_1985_ = !lean_is_exclusive(v_a_1954_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1958_ = v_a_1954_;
v_isShared_1959_ = v_isSharedCheck_1985_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_msg_1956_);
lean_inc(v_ref_1955_);
lean_dec(v_a_1954_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1985_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1960_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v_ref_1977_; lean_object* v___y_1979_; lean_object* v___x_1982_; 
v___x_1960_ = lean_box(0);
v_ref_1977_ = l_Lean_replaceRef(v_ref_1955_, v_ref_1953_);
lean_dec(v_ref_1955_);
v___x_1982_ = l_Lean_Syntax_getPos_x3f(v_ref_1977_, v___x_1939_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v___x_1983_; 
v___x_1983_ = lean_unsigned_to_nat(0u);
v___y_1979_ = v___x_1983_;
goto v___jp_1978_;
}
else
{
lean_object* v_val_1984_; 
v_val_1984_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_val_1984_);
lean_dec_ref_known(v___x_1982_, 1);
v___y_1979_ = v_val_1984_;
goto v___jp_1978_;
}
v___jp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 1, v___y_1963_);
lean_ctor_set(v___x_1951_, 0, v___y_1962_);
v___x_1965_ = v___x_1951_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___y_1962_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v___y_1963_);
v___x_1965_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v_pos2traces_1969_; lean_object* v___x_1971_; 
v___x_1966_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1967_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1949_, v___x_1965_, v___x_1966_);
v___x_1968_ = lean_array_push(v___x_1967_, v_msg_1956_);
v_pos2traces_1969_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_1949_, v___x_1965_, v___x_1968_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 1, v_pos2traces_1969_);
lean_ctor_set(v___x_1958_, 0, v___x_1960_);
v___x_1971_ = v___x_1958_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1960_);
lean_ctor_set(v_reuseFailAlloc_1975_, 1, v_pos2traces_1969_);
v___x_1971_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
size_t v___x_1972_; size_t v___x_1973_; lean_object* v___x_1974_; 
v___x_1972_ = ((size_t)1ULL);
v___x_1973_ = lean_usize_add(v_i_1942_, v___x_1972_);
v___x_1974_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(v___x_1939_, v_as_1940_, v_sz_1941_, v___x_1973_, v___x_1971_, v___y_1944_);
return v___x_1974_;
}
}
}
v___jp_1978_:
{
lean_object* v___x_1980_; 
v___x_1980_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1977_, v___x_1939_);
lean_dec(v_ref_1977_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_inc(v___y_1979_);
v___y_1962_ = v___y_1979_;
v___y_1963_ = v___y_1979_;
goto v___jp_1961_;
}
else
{
lean_object* v_val_1981_; 
v_val_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_val_1981_);
lean_dec_ref_known(v___x_1980_, 1);
v___y_1962_ = v___y_1979_;
v___y_1963_ = v_val_1981_;
goto v___jp_1961_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40___boxed(lean_object* v___x_1988_, lean_object* v_as_1989_, lean_object* v_sz_1990_, lean_object* v_i_1991_, lean_object* v_b_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
uint8_t v___x_39341__boxed_1996_; size_t v_sz_boxed_1997_; size_t v_i_boxed_1998_; lean_object* v_res_1999_; 
v___x_39341__boxed_1996_ = lean_unbox(v___x_1988_);
v_sz_boxed_1997_ = lean_unbox_usize(v_sz_1990_);
lean_dec(v_sz_1990_);
v_i_boxed_1998_ = lean_unbox_usize(v_i_1991_);
lean_dec(v_i_1991_);
v_res_1999_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40(v___x_39341__boxed_1996_, v_as_1989_, v_sz_boxed_1997_, v_i_boxed_1998_, v_b_1992_, v___y_1993_, v___y_1994_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec_ref(v_as_1989_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(lean_object* v_init_2000_, uint8_t v___x_2001_, lean_object* v_n_2002_, lean_object* v_b_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
if (lean_obj_tag(v_n_2002_) == 0)
{
lean_object* v_cs_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; size_t v_sz_2010_; size_t v___x_2011_; lean_object* v___x_2012_; 
v_cs_2007_ = lean_ctor_get(v_n_2002_, 0);
v___x_2008_ = lean_box(0);
v___x_2009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2008_);
lean_ctor_set(v___x_2009_, 1, v_b_2003_);
v_sz_2010_ = lean_array_size(v_cs_2007_);
v___x_2011_ = ((size_t)0ULL);
v___x_2012_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39(v_init_2000_, v___x_2001_, v_cs_2007_, v_sz_2010_, v___x_2011_, v___x_2009_, v___y_2004_, v___y_2005_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2027_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2015_ = v___x_2012_;
v_isShared_2016_ = v_isSharedCheck_2027_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2012_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2027_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v_fst_2017_; 
v_fst_2017_ = lean_ctor_get(v_a_2013_, 0);
if (lean_obj_tag(v_fst_2017_) == 0)
{
lean_object* v_snd_2018_; lean_object* v___x_2019_; lean_object* v___x_2021_; 
v_snd_2018_ = lean_ctor_get(v_a_2013_, 1);
lean_inc(v_snd_2018_);
lean_dec(v_a_2013_);
v___x_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2019_, 0, v_snd_2018_);
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 0, v___x_2019_);
v___x_2021_ = v___x_2015_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2019_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
else
{
lean_object* v_val_2023_; lean_object* v___x_2025_; 
lean_inc_ref(v_fst_2017_);
lean_dec(v_a_2013_);
v_val_2023_ = lean_ctor_get(v_fst_2017_, 0);
lean_inc(v_val_2023_);
lean_dec_ref_known(v_fst_2017_, 1);
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 0, v_val_2023_);
v___x_2025_ = v___x_2015_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_val_2023_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
v_a_2028_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2012_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2012_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
else
{
lean_object* v_vs_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; size_t v_sz_2039_; size_t v___x_2040_; lean_object* v___x_2041_; 
v_vs_2036_ = lean_ctor_get(v_n_2002_, 0);
v___x_2037_ = lean_box(0);
v___x_2038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
lean_ctor_set(v___x_2038_, 1, v_b_2003_);
v_sz_2039_ = lean_array_size(v_vs_2036_);
v___x_2040_ = ((size_t)0ULL);
v___x_2041_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40(v___x_2001_, v_vs_2036_, v_sz_2039_, v___x_2040_, v___x_2038_, v___y_2004_, v___y_2005_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2056_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2044_ = v___x_2041_;
v_isShared_2045_ = v_isSharedCheck_2056_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2041_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2056_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v_fst_2046_; 
v_fst_2046_ = lean_ctor_get(v_a_2042_, 0);
if (lean_obj_tag(v_fst_2046_) == 0)
{
lean_object* v_snd_2047_; lean_object* v___x_2048_; lean_object* v___x_2050_; 
v_snd_2047_ = lean_ctor_get(v_a_2042_, 1);
lean_inc(v_snd_2047_);
lean_dec(v_a_2042_);
v___x_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2048_, 0, v_snd_2047_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 0, v___x_2048_);
v___x_2050_ = v___x_2044_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2048_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
else
{
lean_object* v_val_2052_; lean_object* v___x_2054_; 
lean_inc_ref(v_fst_2046_);
lean_dec(v_a_2042_);
v_val_2052_ = lean_ctor_get(v_fst_2046_, 0);
lean_inc(v_val_2052_);
lean_dec_ref_known(v_fst_2046_, 1);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 0, v_val_2052_);
v___x_2054_ = v___x_2044_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_val_2052_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
v_a_2057_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2041_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2041_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39(lean_object* v_init_2065_, uint8_t v___x_2066_, lean_object* v_as_2067_, size_t v_sz_2068_, size_t v_i_2069_, lean_object* v_b_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
uint8_t v___x_2074_; 
v___x_2074_ = lean_usize_dec_lt(v_i_2069_, v_sz_2068_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; 
v___x_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2075_, 0, v_b_2070_);
return v___x_2075_;
}
else
{
lean_object* v_snd_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2110_; 
v_snd_2076_ = lean_ctor_get(v_b_2070_, 1);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_b_2070_);
if (v_isSharedCheck_2110_ == 0)
{
lean_object* v_unused_2111_; 
v_unused_2111_ = lean_ctor_get(v_b_2070_, 0);
lean_dec(v_unused_2111_);
v___x_2078_ = v_b_2070_;
v_isShared_2079_ = v_isSharedCheck_2110_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_snd_2076_);
lean_dec(v_b_2070_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2110_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2080_; lean_object* v_a_2081_; lean_object* v___x_2082_; 
v___x_2080_ = lean_box(0);
v_a_2081_ = lean_array_uget_borrowed(v_as_2067_, v_i_2069_);
lean_inc(v_snd_2076_);
v___x_2082_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(v_init_2065_, v___x_2066_, v_a_2081_, v_snd_2076_, v___y_2071_, v___y_2072_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2101_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2085_ = v___x_2082_;
v_isShared_2086_ = v_isSharedCheck_2101_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2082_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2101_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
if (lean_obj_tag(v_a_2083_) == 0)
{
lean_object* v___x_2087_; lean_object* v___x_2089_; 
v___x_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2087_, 0, v_a_2083_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v___x_2087_);
v___x_2089_ = v___x_2078_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2087_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v_snd_2076_);
v___x_2089_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
lean_object* v___x_2091_; 
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 0, v___x_2089_);
v___x_2091_ = v___x_2085_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2089_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
else
{
lean_object* v_a_2094_; lean_object* v___x_2096_; 
lean_del_object(v___x_2085_);
lean_dec(v_snd_2076_);
v_a_2094_ = lean_ctor_get(v_a_2083_, 0);
lean_inc(v_a_2094_);
lean_dec_ref_known(v_a_2083_, 1);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 1, v_a_2094_);
lean_ctor_set(v___x_2078_, 0, v___x_2080_);
v___x_2096_ = v___x_2078_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2080_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v_a_2094_);
v___x_2096_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
size_t v___x_2097_; size_t v___x_2098_; 
v___x_2097_ = ((size_t)1ULL);
v___x_2098_ = lean_usize_add(v_i_2069_, v___x_2097_);
v_i_2069_ = v___x_2098_;
v_b_2070_ = v___x_2096_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_del_object(v___x_2078_);
lean_dec(v_snd_2076_);
v_a_2102_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2082_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2082_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39___boxed(lean_object* v_init_2112_, lean_object* v___x_2113_, lean_object* v_as_2114_, lean_object* v_sz_2115_, lean_object* v_i_2116_, lean_object* v_b_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
uint8_t v___x_39422__boxed_2121_; size_t v_sz_boxed_2122_; size_t v_i_boxed_2123_; lean_object* v_res_2124_; 
v___x_39422__boxed_2121_ = lean_unbox(v___x_2113_);
v_sz_boxed_2122_ = lean_unbox_usize(v_sz_2115_);
lean_dec(v_sz_2115_);
v_i_boxed_2123_ = lean_unbox_usize(v_i_2116_);
lean_dec(v_i_2116_);
v_res_2124_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39(v_init_2112_, v___x_39422__boxed_2121_, v_as_2114_, v_sz_boxed_2122_, v_i_boxed_2123_, v_b_2117_, v___y_2118_, v___y_2119_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec_ref(v_as_2114_);
lean_dec_ref(v_init_2112_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27___boxed(lean_object* v_init_2125_, lean_object* v___x_2126_, lean_object* v_n_2127_, lean_object* v_b_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
uint8_t v___x_39442__boxed_2132_; lean_object* v_res_2133_; 
v___x_39442__boxed_2132_ = lean_unbox(v___x_2126_);
v_res_2133_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(v_init_2125_, v___x_39442__boxed_2132_, v_n_2127_, v_b_2128_, v___y_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec_ref(v_n_2127_);
lean_dec_ref(v_init_2125_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(uint8_t v___x_2134_, lean_object* v_as_2135_, size_t v_sz_2136_, size_t v_i_2137_, lean_object* v_b_2138_, lean_object* v___y_2139_){
_start:
{
uint8_t v___x_2141_; 
v___x_2141_ = lean_usize_dec_lt(v_i_2137_, v_sz_2136_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; 
v___x_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2142_, 0, v_b_2138_);
return v___x_2142_;
}
else
{
lean_object* v_snd_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2180_; 
v_snd_2143_ = lean_ctor_get(v_b_2138_, 1);
v_isSharedCheck_2180_ = !lean_is_exclusive(v_b_2138_);
if (v_isSharedCheck_2180_ == 0)
{
lean_object* v_unused_2181_; 
v_unused_2181_ = lean_ctor_get(v_b_2138_, 0);
lean_dec(v_unused_2181_);
v___x_2145_ = v_b_2138_;
v_isShared_2146_ = v_isSharedCheck_2180_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_snd_2143_);
lean_dec(v_b_2138_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2180_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v_ref_2147_; lean_object* v_a_2148_; lean_object* v_ref_2149_; lean_object* v_msg_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2179_; 
v_ref_2147_ = lean_ctor_get(v___y_2139_, 2);
v_a_2148_ = lean_array_uget(v_as_2135_, v_i_2137_);
v_ref_2149_ = lean_ctor_get(v_a_2148_, 0);
v_msg_2150_ = lean_ctor_get(v_a_2148_, 1);
v_isSharedCheck_2179_ = !lean_is_exclusive(v_a_2148_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2152_ = v_a_2148_;
v_isShared_2153_ = v_isSharedCheck_2179_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_msg_2150_);
lean_inc(v_ref_2149_);
lean_dec(v_a_2148_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2179_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2154_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v_ref_2171_; lean_object* v___y_2173_; lean_object* v___x_2176_; 
v___x_2154_ = lean_box(0);
v_ref_2171_ = l_Lean_replaceRef(v_ref_2149_, v_ref_2147_);
lean_dec(v_ref_2149_);
v___x_2176_ = l_Lean_Syntax_getPos_x3f(v_ref_2171_, v___x_2134_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v___x_2177_; 
v___x_2177_ = lean_unsigned_to_nat(0u);
v___y_2173_ = v___x_2177_;
goto v___jp_2172_;
}
else
{
lean_object* v_val_2178_; 
v_val_2178_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_val_2178_);
lean_dec_ref_known(v___x_2176_, 1);
v___y_2173_ = v_val_2178_;
goto v___jp_2172_;
}
v___jp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 1, v___y_2157_);
lean_ctor_set(v___x_2145_, 0, v___y_2156_);
v___x_2159_ = v___x_2145_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___y_2156_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v___y_2157_);
v___x_2159_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v_pos2traces_2163_; lean_object* v___x_2165_; 
v___x_2160_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_2161_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_2143_, v___x_2159_, v___x_2160_);
v___x_2162_ = lean_array_push(v___x_2161_, v_msg_2150_);
v_pos2traces_2163_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_2143_, v___x_2159_, v___x_2162_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 1, v_pos2traces_2163_);
lean_ctor_set(v___x_2152_, 0, v___x_2154_);
v___x_2165_ = v___x_2152_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2154_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v_pos2traces_2163_);
v___x_2165_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
size_t v___x_2166_; size_t v___x_2167_; 
v___x_2166_ = ((size_t)1ULL);
v___x_2167_ = lean_usize_add(v_i_2137_, v___x_2166_);
v_i_2137_ = v___x_2167_;
v_b_2138_ = v___x_2165_;
goto _start;
}
}
}
v___jp_2172_:
{
lean_object* v___x_2174_; 
v___x_2174_ = l_Lean_Syntax_getTailPos_x3f(v_ref_2171_, v___x_2134_);
lean_dec(v_ref_2171_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_inc(v___y_2173_);
v___y_2156_ = v___y_2173_;
v___y_2157_ = v___y_2173_;
goto v___jp_2155_;
}
else
{
lean_object* v_val_2175_; 
v_val_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_val_2175_);
lean_dec_ref_known(v___x_2174_, 1);
v___y_2156_ = v___y_2173_;
v___y_2157_ = v_val_2175_;
goto v___jp_2155_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg___boxed(lean_object* v___x_2182_, lean_object* v_as_2183_, lean_object* v_sz_2184_, lean_object* v_i_2185_, lean_object* v_b_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
uint8_t v___x_39625__boxed_2189_; size_t v_sz_boxed_2190_; size_t v_i_boxed_2191_; lean_object* v_res_2192_; 
v___x_39625__boxed_2189_ = lean_unbox(v___x_2182_);
v_sz_boxed_2190_ = lean_unbox_usize(v_sz_2184_);
lean_dec(v_sz_2184_);
v_i_boxed_2191_ = lean_unbox_usize(v_i_2185_);
lean_dec(v_i_2185_);
v_res_2192_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(v___x_39625__boxed_2189_, v_as_2183_, v_sz_boxed_2190_, v_i_boxed_2191_, v_b_2186_, v___y_2187_);
lean_dec_ref(v___y_2187_);
lean_dec_ref(v_as_2183_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28(uint8_t v___x_2193_, lean_object* v_as_2194_, size_t v_sz_2195_, size_t v_i_2196_, lean_object* v_b_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
uint8_t v___x_2201_; 
v___x_2201_ = lean_usize_dec_lt(v_i_2196_, v_sz_2195_);
if (v___x_2201_ == 0)
{
lean_object* v___x_2202_; 
v___x_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2202_, 0, v_b_2197_);
return v___x_2202_;
}
else
{
lean_object* v_snd_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2240_; 
v_snd_2203_ = lean_ctor_get(v_b_2197_, 1);
v_isSharedCheck_2240_ = !lean_is_exclusive(v_b_2197_);
if (v_isSharedCheck_2240_ == 0)
{
lean_object* v_unused_2241_; 
v_unused_2241_ = lean_ctor_get(v_b_2197_, 0);
lean_dec(v_unused_2241_);
v___x_2205_ = v_b_2197_;
v_isShared_2206_ = v_isSharedCheck_2240_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_snd_2203_);
lean_dec(v_b_2197_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2240_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v_ref_2207_; lean_object* v_a_2208_; lean_object* v_ref_2209_; lean_object* v_msg_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2239_; 
v_ref_2207_ = lean_ctor_get(v___y_2198_, 2);
v_a_2208_ = lean_array_uget(v_as_2194_, v_i_2196_);
v_ref_2209_ = lean_ctor_get(v_a_2208_, 0);
v_msg_2210_ = lean_ctor_get(v_a_2208_, 1);
v_isSharedCheck_2239_ = !lean_is_exclusive(v_a_2208_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2212_ = v_a_2208_;
v_isShared_2213_ = v_isSharedCheck_2239_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_msg_2210_);
lean_inc(v_ref_2209_);
lean_dec(v_a_2208_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2239_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2214_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v_ref_2231_; lean_object* v___y_2233_; lean_object* v___x_2236_; 
v___x_2214_ = lean_box(0);
v_ref_2231_ = l_Lean_replaceRef(v_ref_2209_, v_ref_2207_);
lean_dec(v_ref_2209_);
v___x_2236_ = l_Lean_Syntax_getPos_x3f(v_ref_2231_, v___x_2193_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v___x_2237_; 
v___x_2237_ = lean_unsigned_to_nat(0u);
v___y_2233_ = v___x_2237_;
goto v___jp_2232_;
}
else
{
lean_object* v_val_2238_; 
v_val_2238_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_val_2238_);
lean_dec_ref_known(v___x_2236_, 1);
v___y_2233_ = v_val_2238_;
goto v___jp_2232_;
}
v___jp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 1, v___y_2217_);
lean_ctor_set(v___x_2205_, 0, v___y_2216_);
v___x_2219_ = v___x_2205_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___y_2216_);
lean_ctor_set(v_reuseFailAlloc_2230_, 1, v___y_2217_);
v___x_2219_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v_pos2traces_2223_; lean_object* v___x_2225_; 
v___x_2220_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_2221_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_2203_, v___x_2219_, v___x_2220_);
v___x_2222_ = lean_array_push(v___x_2221_, v_msg_2210_);
v_pos2traces_2223_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_2203_, v___x_2219_, v___x_2222_);
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 1, v_pos2traces_2223_);
lean_ctor_set(v___x_2212_, 0, v___x_2214_);
v___x_2225_ = v___x_2212_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2214_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_pos2traces_2223_);
v___x_2225_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
size_t v___x_2226_; size_t v___x_2227_; lean_object* v___x_2228_; 
v___x_2226_ = ((size_t)1ULL);
v___x_2227_ = lean_usize_add(v_i_2196_, v___x_2226_);
v___x_2228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(v___x_2193_, v_as_2194_, v_sz_2195_, v___x_2227_, v___x_2225_, v___y_2198_);
return v___x_2228_;
}
}
}
v___jp_2232_:
{
lean_object* v___x_2234_; 
v___x_2234_ = l_Lean_Syntax_getTailPos_x3f(v_ref_2231_, v___x_2193_);
lean_dec(v_ref_2231_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_inc(v___y_2233_);
v___y_2216_ = v___y_2233_;
v___y_2217_ = v___y_2233_;
goto v___jp_2215_;
}
else
{
lean_object* v_val_2235_; 
v_val_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_val_2235_);
lean_dec_ref_known(v___x_2234_, 1);
v___y_2216_ = v___y_2233_;
v___y_2217_ = v_val_2235_;
goto v___jp_2215_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28___boxed(lean_object* v___x_2242_, lean_object* v_as_2243_, lean_object* v_sz_2244_, lean_object* v_i_2245_, lean_object* v_b_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
uint8_t v___x_39705__boxed_2250_; size_t v_sz_boxed_2251_; size_t v_i_boxed_2252_; lean_object* v_res_2253_; 
v___x_39705__boxed_2250_ = lean_unbox(v___x_2242_);
v_sz_boxed_2251_ = lean_unbox_usize(v_sz_2244_);
lean_dec(v_sz_2244_);
v_i_boxed_2252_ = lean_unbox_usize(v_i_2245_);
lean_dec(v_i_2245_);
v_res_2253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28(v___x_39705__boxed_2250_, v_as_2243_, v_sz_boxed_2251_, v_i_boxed_2252_, v_b_2246_, v___y_2247_, v___y_2248_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec_ref(v_as_2243_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(uint8_t v___x_2254_, lean_object* v_t_2255_, lean_object* v_init_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v_root_2260_; lean_object* v_tail_2261_; lean_object* v___x_2262_; 
v_root_2260_ = lean_ctor_get(v_t_2255_, 0);
v_tail_2261_ = lean_ctor_get(v_t_2255_, 1);
lean_inc_ref(v_init_2256_);
v___x_2262_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(v_init_2256_, v___x_2254_, v_root_2260_, v_init_2256_, v___y_2257_, v___y_2258_);
lean_dec_ref(v_init_2256_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2299_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2265_ = v___x_2262_;
v_isShared_2266_ = v_isSharedCheck_2299_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2262_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2299_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
if (lean_obj_tag(v_a_2263_) == 0)
{
lean_object* v_a_2267_; lean_object* v___x_2269_; 
v_a_2267_ = lean_ctor_get(v_a_2263_, 0);
lean_inc(v_a_2267_);
lean_dec_ref_known(v_a_2263_, 1);
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 0, v_a_2267_);
v___x_2269_ = v___x_2265_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2267_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; size_t v_sz_2274_; size_t v___x_2275_; lean_object* v___x_2276_; 
lean_del_object(v___x_2265_);
v_a_2271_ = lean_ctor_get(v_a_2263_, 0);
lean_inc(v_a_2271_);
lean_dec_ref_known(v_a_2263_, 1);
v___x_2272_ = lean_box(0);
v___x_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
lean_ctor_set(v___x_2273_, 1, v_a_2271_);
v_sz_2274_ = lean_array_size(v_tail_2261_);
v___x_2275_ = ((size_t)0ULL);
v___x_2276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28(v___x_2254_, v_tail_2261_, v_sz_2274_, v___x_2275_, v___x_2273_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2290_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2279_ = v___x_2276_;
v_isShared_2280_ = v_isSharedCheck_2290_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2276_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2290_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v_fst_2281_; 
v_fst_2281_ = lean_ctor_get(v_a_2277_, 0);
if (lean_obj_tag(v_fst_2281_) == 0)
{
lean_object* v_snd_2282_; lean_object* v___x_2284_; 
v_snd_2282_ = lean_ctor_get(v_a_2277_, 1);
lean_inc(v_snd_2282_);
lean_dec(v_a_2277_);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v_snd_2282_);
v___x_2284_ = v___x_2279_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_snd_2282_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
else
{
lean_object* v_val_2286_; lean_object* v___x_2288_; 
lean_inc_ref(v_fst_2281_);
lean_dec(v_a_2277_);
v_val_2286_ = lean_ctor_get(v_fst_2281_, 0);
lean_inc(v_val_2286_);
lean_dec_ref_known(v_fst_2281_, 1);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v_val_2286_);
v___x_2288_ = v___x_2279_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_val_2286_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
v_a_2291_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2276_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2276_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
}
}
else
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2307_; 
v_a_2300_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2302_ = v___x_2262_;
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2262_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2303_ == 0)
{
v___x_2305_ = v___x_2302_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_a_2300_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___boxed(lean_object* v___x_2308_, lean_object* v_t_2309_, lean_object* v_init_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
uint8_t v___x_39786__boxed_2314_; lean_object* v_res_2315_; 
v___x_39786__boxed_2314_ = lean_unbox(v___x_2308_);
v_res_2315_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(v___x_39786__boxed_2314_, v_t_2309_, v_init_2310_, v___y_2311_, v___y_2312_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec_ref(v_t_2309_);
return v_res_2315_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0(void){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2316_ = lean_unsigned_to_nat(32u);
v___x_2317_ = lean_mk_empty_array_with_capacity(v___x_2316_);
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
return v___x_2318_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1(void){
_start:
{
size_t v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2319_ = ((size_t)5ULL);
v___x_2320_ = lean_unsigned_to_nat(0u);
v___x_2321_ = lean_unsigned_to_nat(32u);
v___x_2322_ = lean_mk_empty_array_with_capacity(v___x_2321_);
v___x_2323_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0);
v___x_2324_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2324_, 0, v___x_2323_);
lean_ctor_set(v___x_2324_, 1, v___x_2322_);
lean_ctor_set(v___x_2324_, 2, v___x_2320_);
lean_ctor_set(v___x_2324_, 3, v___x_2320_);
lean_ctor_set_usize(v___x_2324_, 4, v___x_2319_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(lean_object* v___y_2325_){
_start:
{
lean_object* v___x_2327_; lean_object* v_traceState_2328_; lean_object* v_traces_2329_; lean_object* v___x_2330_; lean_object* v_traceState_2331_; lean_object* v_env_2332_; lean_object* v_nextMacroScope_2333_; lean_object* v_ngen_2334_; lean_object* v_auxDeclNGen_2335_; lean_object* v_cache_2336_; lean_object* v_recordedDeps_2337_; lean_object* v_messages_2338_; lean_object* v_infoState_2339_; lean_object* v_snapshotTasks_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2359_; 
v___x_2327_ = lean_st_ref_get(v___y_2325_);
v_traceState_2328_ = lean_ctor_get(v___x_2327_, 4);
lean_inc_ref(v_traceState_2328_);
lean_dec(v___x_2327_);
v_traces_2329_ = lean_ctor_get(v_traceState_2328_, 0);
lean_inc_ref(v_traces_2329_);
lean_dec_ref(v_traceState_2328_);
v___x_2330_ = lean_st_ref_take(v___y_2325_);
v_traceState_2331_ = lean_ctor_get(v___x_2330_, 4);
v_env_2332_ = lean_ctor_get(v___x_2330_, 0);
v_nextMacroScope_2333_ = lean_ctor_get(v___x_2330_, 1);
v_ngen_2334_ = lean_ctor_get(v___x_2330_, 2);
v_auxDeclNGen_2335_ = lean_ctor_get(v___x_2330_, 3);
v_cache_2336_ = lean_ctor_get(v___x_2330_, 5);
v_recordedDeps_2337_ = lean_ctor_get(v___x_2330_, 6);
v_messages_2338_ = lean_ctor_get(v___x_2330_, 7);
v_infoState_2339_ = lean_ctor_get(v___x_2330_, 8);
v_snapshotTasks_2340_ = lean_ctor_get(v___x_2330_, 9);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2342_ = v___x_2330_;
v_isShared_2343_ = v_isSharedCheck_2359_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_snapshotTasks_2340_);
lean_inc(v_infoState_2339_);
lean_inc(v_messages_2338_);
lean_inc(v_recordedDeps_2337_);
lean_inc(v_cache_2336_);
lean_inc(v_traceState_2331_);
lean_inc(v_auxDeclNGen_2335_);
lean_inc(v_ngen_2334_);
lean_inc(v_nextMacroScope_2333_);
lean_inc(v_env_2332_);
lean_dec(v___x_2330_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2359_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
uint64_t v_tid_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2357_; 
v_tid_2344_ = lean_ctor_get_uint64(v_traceState_2331_, sizeof(void*)*1);
v_isSharedCheck_2357_ = !lean_is_exclusive(v_traceState_2331_);
if (v_isSharedCheck_2357_ == 0)
{
lean_object* v_unused_2358_; 
v_unused_2358_ = lean_ctor_get(v_traceState_2331_, 0);
lean_dec(v_unused_2358_);
v___x_2346_ = v_traceState_2331_;
v_isShared_2347_ = v_isSharedCheck_2357_;
goto v_resetjp_2345_;
}
else
{
lean_dec(v_traceState_2331_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2357_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2348_; lean_object* v___x_2350_; 
v___x_2348_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
if (v_isShared_2347_ == 0)
{
lean_ctor_set(v___x_2346_, 0, v___x_2348_);
v___x_2350_ = v___x_2346_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2348_);
lean_ctor_set_uint64(v_reuseFailAlloc_2356_, sizeof(void*)*1, v_tid_2344_);
v___x_2350_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
lean_object* v___x_2352_; 
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 4, v___x_2350_);
v___x_2352_ = v___x_2342_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_env_2332_);
lean_ctor_set(v_reuseFailAlloc_2355_, 1, v_nextMacroScope_2333_);
lean_ctor_set(v_reuseFailAlloc_2355_, 2, v_ngen_2334_);
lean_ctor_set(v_reuseFailAlloc_2355_, 3, v_auxDeclNGen_2335_);
lean_ctor_set(v_reuseFailAlloc_2355_, 4, v___x_2350_);
lean_ctor_set(v_reuseFailAlloc_2355_, 5, v_cache_2336_);
lean_ctor_set(v_reuseFailAlloc_2355_, 6, v_recordedDeps_2337_);
lean_ctor_set(v_reuseFailAlloc_2355_, 7, v_messages_2338_);
lean_ctor_set(v_reuseFailAlloc_2355_, 8, v_infoState_2339_);
lean_ctor_set(v_reuseFailAlloc_2355_, 9, v_snapshotTasks_2340_);
v___x_2352_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2353_ = lean_st_ref_put(v___y_2325_, v___x_2352_);
v___x_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2354_, 0, v_traces_2329_);
return v___x_2354_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___boxed(lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___y_2360_);
lean_dec(v___y_2360_);
return v_res_2362_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0(void){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2363_ = lean_box(0);
v___x_2364_ = lean_unsigned_to_nat(16u);
v___x_2365_ = lean_mk_array(v___x_2364_, v___x_2363_);
return v___x_2365_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1(void){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v_pos2traces_2368_; 
v___x_2366_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0, &l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0);
v___x_2367_ = lean_unsigned_to_nat(0u);
v_pos2traces_2368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_2368_, 0, v___x_2367_);
lean_ctor_set(v_pos2traces_2368_, 1, v___x_2366_);
return v_pos2traces_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9(lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v_toCold_2375_; lean_object* v_options_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v_toCold_2375_ = lean_ctor_get(v___y_2369_, 0);
v_options_2376_ = lean_ctor_get(v_toCold_2375_, 2);
v___x_2377_ = l_Lean_trace_profiler_output;
v___x_2378_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(v_options_2376_, v___x_2377_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v___x_2379_; uint8_t v___x_2380_; 
v___x_2379_ = l_Lean_trace_profiler_serve;
v___x_2380_ = l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(v_options_2376_, v___x_2379_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2444_; 
v___x_2381_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___y_2370_);
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2384_ = v___x_2381_;
v_isShared_2385_ = v_isSharedCheck_2444_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2381_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2444_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
uint8_t v___x_2386_; 
v___x_2386_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_2382_);
if (v___x_2386_ == 0)
{
lean_object* v___x_2387_; lean_object* v_pos2traces_2388_; lean_object* v___x_2389_; 
lean_del_object(v___x_2384_);
v___x_2387_ = lean_unsigned_to_nat(0u);
v_pos2traces_2388_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1, &l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1);
v___x_2389_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(v___x_2386_, v_a_2382_, v_pos2traces_2388_, v___y_2369_, v___y_2370_);
lean_dec(v_a_2382_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; lean_object* v___y_2392_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2418_; lean_object* v_size_2424_; lean_object* v_buckets_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; uint8_t v___x_2428_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
lean_inc(v_a_2390_);
lean_dec_ref_known(v___x_2389_, 1);
v_size_2424_ = lean_ctor_get(v_a_2390_, 0);
lean_inc(v_size_2424_);
v_buckets_2425_ = lean_ctor_get(v_a_2390_, 1);
lean_inc_ref(v_buckets_2425_);
lean_dec(v_a_2390_);
v___x_2426_ = lean_mk_empty_array_with_capacity(v_size_2424_);
lean_dec(v_size_2424_);
v___x_2427_ = lean_array_get_size(v_buckets_2425_);
v___x_2428_ = lean_nat_dec_lt(v___x_2387_, v___x_2427_);
if (v___x_2428_ == 0)
{
lean_dec_ref(v_buckets_2425_);
v___y_2418_ = v___x_2426_;
goto v___jp_2417_;
}
else
{
size_t v___x_2429_; size_t v___x_2430_; lean_object* v___x_2431_; 
v___x_2429_ = ((size_t)0ULL);
v___x_2430_ = lean_usize_of_nat(v___x_2427_);
v___x_2431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23(v_buckets_2425_, v___x_2429_, v___x_2430_, v___x_2426_);
lean_dec_ref(v_buckets_2425_);
v___y_2418_ = v___x_2431_;
goto v___jp_2417_;
}
v___jp_2391_:
{
lean_object* v___x_2393_; size_t v_sz_2394_; size_t v___x_2395_; lean_object* v___x_2396_; 
v___x_2393_ = lean_box(0);
v_sz_2394_ = lean_array_size(v___y_2392_);
v___x_2395_ = ((size_t)0ULL);
v___x_2396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(v___x_2380_, v___y_2392_, v_sz_2394_, v___x_2395_, v___x_2393_, v___y_2369_, v___y_2370_);
lean_dec_ref(v___y_2392_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2403_ == 0)
{
lean_object* v_unused_2404_; 
v_unused_2404_ = lean_ctor_get(v___x_2396_, 0);
lean_dec(v_unused_2404_);
v___x_2398_ = v___x_2396_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_dec(v___x_2396_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 0, v___x_2393_);
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2393_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
else
{
return v___x_2396_;
}
}
v___jp_2405_:
{
lean_object* v___x_2410_; 
v___x_2410_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v___y_2407_, v___y_2406_, v___y_2408_, v___y_2409_);
lean_dec(v___y_2409_);
lean_dec(v___y_2407_);
v___y_2392_ = v___x_2410_;
goto v___jp_2391_;
}
v___jp_2411_:
{
uint8_t v___x_2416_; 
v___x_2416_ = lean_nat_dec_le(v___y_2415_, v___y_2414_);
if (v___x_2416_ == 0)
{
lean_dec(v___y_2414_);
lean_inc(v___y_2415_);
v___y_2406_ = v___y_2413_;
v___y_2407_ = v___y_2412_;
v___y_2408_ = v___y_2415_;
v___y_2409_ = v___y_2415_;
goto v___jp_2405_;
}
else
{
v___y_2406_ = v___y_2413_;
v___y_2407_ = v___y_2412_;
v___y_2408_ = v___y_2415_;
v___y_2409_ = v___y_2414_;
goto v___jp_2405_;
}
}
v___jp_2417_:
{
lean_object* v___x_2419_; uint8_t v___x_2420_; 
v___x_2419_ = lean_array_get_size(v___y_2418_);
v___x_2420_ = lean_nat_dec_eq(v___x_2419_, v___x_2387_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2421_; lean_object* v___x_2422_; uint8_t v___x_2423_; 
v___x_2421_ = lean_unsigned_to_nat(1u);
v___x_2422_ = lean_nat_sub(v___x_2419_, v___x_2421_);
v___x_2423_ = lean_nat_dec_le(v___x_2387_, v___x_2422_);
if (v___x_2423_ == 0)
{
lean_inc(v___x_2422_);
v___y_2412_ = v___x_2419_;
v___y_2413_ = v___y_2418_;
v___y_2414_ = v___x_2422_;
v___y_2415_ = v___x_2422_;
goto v___jp_2411_;
}
else
{
v___y_2412_ = v___x_2419_;
v___y_2413_ = v___y_2418_;
v___y_2414_ = v___x_2422_;
v___y_2415_ = v___x_2387_;
goto v___jp_2411_;
}
}
else
{
v___y_2392_ = v___y_2418_;
goto v___jp_2391_;
}
}
}
else
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
v_a_2432_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v___x_2389_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2389_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2432_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
else
{
lean_object* v___x_2440_; lean_object* v___x_2442_; 
lean_dec(v_a_2382_);
v___x_2440_ = lean_box(0);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 0, v___x_2440_);
v___x_2442_ = v___x_2384_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2440_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
else
{
goto v___jp_2372_;
}
}
else
{
lean_dec_ref_known(v___x_2378_, 1);
goto v___jp_2372_;
}
v___jp_2372_:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = lean_box(0);
v___x_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
return v___x_2374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9___boxed(lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2445_, v___y_2446_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(lean_object* v_as_2449_, size_t v_sz_2450_, size_t v_i_2451_, lean_object* v_b_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
uint8_t v___x_2456_; 
v___x_2456_ = lean_usize_dec_lt(v_i_2451_, v_sz_2450_);
if (v___x_2456_ == 0)
{
lean_object* v___x_2457_; 
v___x_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2457_, 0, v_b_2452_);
return v___x_2457_;
}
else
{
lean_object* v___x_2458_; lean_object* v_a_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2458_ = lean_box(0);
v_a_2459_ = lean_array_uget_borrowed(v_as_2449_, v_i_2451_);
v___x_2460_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2453_);
lean_inc(v_a_2459_);
v___x_2461_ = l_Lean_Compiler_LCNF_resumeCompilation(v_a_2459_, v___x_2460_, v___y_2453_, v___y_2454_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v___x_2462_; 
lean_dec_ref_known(v___x_2461_, 1);
v___x_2462_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2453_, v___y_2454_);
if (lean_obj_tag(v___x_2462_) == 0)
{
size_t v___x_2463_; size_t v___x_2464_; 
lean_dec_ref_known(v___x_2462_, 1);
v___x_2463_ = ((size_t)1ULL);
v___x_2464_ = lean_usize_add(v_i_2451_, v___x_2463_);
v_i_2451_ = v___x_2464_;
v_b_2452_ = v___x_2458_;
goto _start;
}
else
{
return v___x_2462_;
}
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2467_; 
v_a_2466_ = lean_ctor_get(v___x_2461_, 0);
lean_inc(v_a_2466_);
lean_dec_ref_known(v___x_2461_, 1);
v___x_2467_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2453_, v___y_2454_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2474_ == 0)
{
lean_object* v_unused_2475_; 
v_unused_2475_ = lean_ctor_get(v___x_2467_, 0);
lean_dec(v_unused_2475_);
v___x_2469_ = v___x_2467_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_dec(v___x_2467_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
lean_ctor_set_tag(v___x_2469_, 1);
lean_ctor_set(v___x_2469_, 0, v_a_2466_);
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2466_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
else
{
lean_dec(v_a_2466_);
return v___x_2467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10___boxed(lean_object* v_as_2476_, lean_object* v_sz_2477_, lean_object* v_i_2478_, lean_object* v_b_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
size_t v_sz_boxed_2483_; size_t v_i_boxed_2484_; lean_object* v_res_2485_; 
v_sz_boxed_2483_ = lean_unbox_usize(v_sz_2477_);
lean_dec(v_sz_2477_);
v_i_boxed_2484_ = lean_unbox_usize(v_i_2478_);
lean_dec(v_i_2478_);
v_res_2485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(v_as_2476_, v_sz_boxed_2483_, v_i_boxed_2484_, v_b_2479_, v___y_2480_, v___y_2481_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec_ref(v_as_2476_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(lean_object* v_as_2486_, size_t v_sz_2487_, size_t v_i_2488_, lean_object* v_b_2489_, lean_object* v___y_2490_){
_start:
{
uint8_t v___x_2492_; 
v___x_2492_ = lean_usize_dec_lt(v_i_2488_, v_sz_2487_);
if (v___x_2492_ == 0)
{
lean_object* v___x_2493_; 
v___x_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2493_, 0, v_b_2489_);
return v___x_2493_;
}
else
{
uint8_t v___x_2494_; lean_object* v_a_2495_; lean_object* v___x_2496_; lean_object* v_ref_2497_; lean_object* v___x_2498_; 
lean_dec_ref(v_b_2489_);
v___x_2494_ = 0;
v_a_2495_ = lean_array_uget_borrowed(v_as_2486_, v_i_2488_);
lean_inc(v_a_2495_);
v___x_2496_ = l_Lean_Message_toString(v_a_2495_, v___x_2494_);
v_ref_2497_ = lean_ctor_get(v___y_2490_, 2);
v___x_2498_ = l_IO_eprintln___at___00main_spec__6(v___x_2496_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v___x_2499_; size_t v___x_2500_; size_t v___x_2501_; 
lean_dec_ref_known(v___x_2498_, 1);
v___x_2499_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_2500_ = ((size_t)1ULL);
v___x_2501_ = lean_usize_add(v_i_2488_, v___x_2500_);
v_i_2488_ = v___x_2501_;
v_b_2489_ = v___x_2499_;
goto _start;
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2514_; 
v_a_2503_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2505_ = v___x_2498_;
v_isShared_2506_ = v_isSharedCheck_2514_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2498_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2514_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2512_; 
v___x_2507_ = lean_io_error_to_string(v_a_2503_);
v___x_2508_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2507_);
v___x_2509_ = l_Lean_MessageData_ofFormat(v___x_2508_);
lean_inc(v_ref_2497_);
v___x_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2510_, 0, v_ref_2497_);
lean_ctor_set(v___x_2510_, 1, v___x_2509_);
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 0, v___x_2510_);
v___x_2512_ = v___x_2505_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2510_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg___boxed(lean_object* v_as_2515_, lean_object* v_sz_2516_, lean_object* v_i_2517_, lean_object* v_b_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
size_t v_sz_boxed_2521_; size_t v_i_boxed_2522_; lean_object* v_res_2523_; 
v_sz_boxed_2521_ = lean_unbox_usize(v_sz_2516_);
lean_dec(v_sz_2516_);
v_i_boxed_2522_ = lean_unbox_usize(v_i_2517_);
lean_dec(v_i_2517_);
v_res_2523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(v_as_2515_, v_sz_boxed_2521_, v_i_boxed_2522_, v_b_2518_, v___y_2519_);
lean_dec_ref(v___y_2519_);
lean_dec_ref(v_as_2515_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38(lean_object* v_as_2524_, size_t v_sz_2525_, size_t v_i_2526_, lean_object* v_b_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
uint8_t v___x_2531_; 
v___x_2531_ = lean_usize_dec_lt(v_i_2526_, v_sz_2525_);
if (v___x_2531_ == 0)
{
lean_object* v___x_2532_; 
v___x_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2532_, 0, v_b_2527_);
return v___x_2532_;
}
else
{
uint8_t v___x_2533_; lean_object* v_a_2534_; lean_object* v___x_2535_; lean_object* v_ref_2536_; lean_object* v___x_2537_; 
lean_dec_ref(v_b_2527_);
v___x_2533_ = 0;
v_a_2534_ = lean_array_uget_borrowed(v_as_2524_, v_i_2526_);
lean_inc(v_a_2534_);
v___x_2535_ = l_Lean_Message_toString(v_a_2534_, v___x_2533_);
v_ref_2536_ = lean_ctor_get(v___y_2528_, 2);
v___x_2537_ = l_IO_eprintln___at___00main_spec__6(v___x_2535_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v___x_2538_; size_t v___x_2539_; size_t v___x_2540_; lean_object* v___x_2541_; 
lean_dec_ref_known(v___x_2537_, 1);
v___x_2538_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_2539_ = ((size_t)1ULL);
v___x_2540_ = lean_usize_add(v_i_2526_, v___x_2539_);
v___x_2541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(v_as_2524_, v_sz_2525_, v___x_2540_, v___x_2538_, v___y_2528_);
return v___x_2541_;
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2553_; 
v_a_2542_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2544_ = v___x_2537_;
v_isShared_2545_ = v_isSharedCheck_2553_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2537_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2553_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2551_; 
v___x_2546_ = lean_io_error_to_string(v_a_2542_);
v___x_2547_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2546_);
v___x_2548_ = l_Lean_MessageData_ofFormat(v___x_2547_);
lean_inc(v_ref_2536_);
v___x_2549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2549_, 0, v_ref_2536_);
lean_ctor_set(v___x_2549_, 1, v___x_2548_);
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 0, v___x_2549_);
v___x_2551_ = v___x_2544_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2549_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38___boxed(lean_object* v_as_2554_, lean_object* v_sz_2555_, lean_object* v_i_2556_, lean_object* v_b_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
size_t v_sz_boxed_2561_; size_t v_i_boxed_2562_; lean_object* v_res_2563_; 
v_sz_boxed_2561_ = lean_unbox_usize(v_sz_2555_);
lean_dec(v_sz_2555_);
v_i_boxed_2562_ = lean_unbox_usize(v_i_2556_);
lean_dec(v_i_2556_);
v_res_2563_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38(v_as_2554_, v_sz_boxed_2561_, v_i_boxed_2562_, v_b_2557_, v___y_2558_, v___y_2559_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
lean_dec_ref(v_as_2554_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(lean_object* v_init_2564_, lean_object* v_n_2565_, lean_object* v_b_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
if (lean_obj_tag(v_n_2565_) == 0)
{
lean_object* v_cs_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; size_t v_sz_2573_; size_t v___x_2574_; lean_object* v___x_2575_; 
v_cs_2570_ = lean_ctor_get(v_n_2565_, 0);
v___x_2571_ = lean_box(0);
v___x_2572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
lean_ctor_set(v___x_2572_, 1, v_b_2566_);
v_sz_2573_ = lean_array_size(v_cs_2570_);
v___x_2574_ = ((size_t)0ULL);
v___x_2575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37(v_init_2564_, v_cs_2570_, v_sz_2573_, v___x_2574_, v___x_2572_, v___y_2567_, v___y_2568_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2590_; 
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2578_ = v___x_2575_;
v_isShared_2579_ = v_isSharedCheck_2590_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___x_2575_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2590_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v_fst_2580_; 
v_fst_2580_ = lean_ctor_get(v_a_2576_, 0);
if (lean_obj_tag(v_fst_2580_) == 0)
{
lean_object* v_snd_2581_; lean_object* v___x_2582_; lean_object* v___x_2584_; 
v_snd_2581_ = lean_ctor_get(v_a_2576_, 1);
lean_inc(v_snd_2581_);
lean_dec(v_a_2576_);
v___x_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2582_, 0, v_snd_2581_);
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 0, v___x_2582_);
v___x_2584_ = v___x_2578_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2582_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
else
{
lean_object* v_val_2586_; lean_object* v___x_2588_; 
lean_inc_ref(v_fst_2580_);
lean_dec(v_a_2576_);
v_val_2586_ = lean_ctor_get(v_fst_2580_, 0);
lean_inc(v_val_2586_);
lean_dec_ref_known(v_fst_2580_, 1);
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 0, v_val_2586_);
v___x_2588_ = v___x_2578_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_val_2586_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
v_a_2591_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2575_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2575_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
else
{
lean_object* v_vs_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; size_t v_sz_2602_; size_t v___x_2603_; lean_object* v___x_2604_; 
v_vs_2599_ = lean_ctor_get(v_n_2565_, 0);
v___x_2600_ = lean_box(0);
v___x_2601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
lean_ctor_set(v___x_2601_, 1, v_b_2566_);
v_sz_2602_ = lean_array_size(v_vs_2599_);
v___x_2603_ = ((size_t)0ULL);
v___x_2604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38(v_vs_2599_, v_sz_2602_, v___x_2603_, v___x_2601_, v___y_2567_, v___y_2568_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2619_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2607_ = v___x_2604_;
v_isShared_2608_ = v_isSharedCheck_2619_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2604_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2619_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v_fst_2609_; 
v_fst_2609_ = lean_ctor_get(v_a_2605_, 0);
if (lean_obj_tag(v_fst_2609_) == 0)
{
lean_object* v_snd_2610_; lean_object* v___x_2611_; lean_object* v___x_2613_; 
v_snd_2610_ = lean_ctor_get(v_a_2605_, 1);
lean_inc(v_snd_2610_);
lean_dec(v_a_2605_);
v___x_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2611_, 0, v_snd_2610_);
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 0, v___x_2611_);
v___x_2613_ = v___x_2607_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v___x_2611_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
else
{
lean_object* v_val_2615_; lean_object* v___x_2617_; 
lean_inc_ref(v_fst_2609_);
lean_dec(v_a_2605_);
v_val_2615_ = lean_ctor_get(v_fst_2609_, 0);
lean_inc(v_val_2615_);
lean_dec_ref_known(v_fst_2609_, 1);
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 0, v_val_2615_);
v___x_2617_ = v___x_2607_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_val_2615_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
v_a_2620_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2604_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2604_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37(lean_object* v_init_2628_, lean_object* v_as_2629_, size_t v_sz_2630_, size_t v_i_2631_, lean_object* v_b_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
uint8_t v___x_2636_; 
v___x_2636_ = lean_usize_dec_lt(v_i_2631_, v_sz_2630_);
if (v___x_2636_ == 0)
{
lean_object* v___x_2637_; 
v___x_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2637_, 0, v_b_2632_);
return v___x_2637_;
}
else
{
lean_object* v_snd_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2672_; 
v_snd_2638_ = lean_ctor_get(v_b_2632_, 1);
v_isSharedCheck_2672_ = !lean_is_exclusive(v_b_2632_);
if (v_isSharedCheck_2672_ == 0)
{
lean_object* v_unused_2673_; 
v_unused_2673_ = lean_ctor_get(v_b_2632_, 0);
lean_dec(v_unused_2673_);
v___x_2640_ = v_b_2632_;
v_isShared_2641_ = v_isSharedCheck_2672_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_snd_2638_);
lean_dec(v_b_2632_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2672_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2642_; lean_object* v_a_2643_; lean_object* v___x_2644_; 
v___x_2642_ = lean_box(0);
v_a_2643_ = lean_array_uget_borrowed(v_as_2629_, v_i_2631_);
lean_inc(v_snd_2638_);
v___x_2644_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(v_init_2628_, v_a_2643_, v_snd_2638_, v___y_2633_, v___y_2634_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2663_; 
v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2647_ = v___x_2644_;
v_isShared_2648_ = v_isSharedCheck_2663_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2644_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2663_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
if (lean_obj_tag(v_a_2645_) == 0)
{
lean_object* v___x_2649_; lean_object* v___x_2651_; 
v___x_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2649_, 0, v_a_2645_);
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 0, v___x_2649_);
v___x_2651_ = v___x_2640_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2649_);
lean_ctor_set(v_reuseFailAlloc_2655_, 1, v_snd_2638_);
v___x_2651_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
lean_object* v___x_2653_; 
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 0, v___x_2651_);
v___x_2653_ = v___x_2647_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2651_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2658_; 
lean_del_object(v___x_2647_);
lean_dec(v_snd_2638_);
v_a_2656_ = lean_ctor_get(v_a_2645_, 0);
lean_inc(v_a_2656_);
lean_dec_ref_known(v_a_2645_, 1);
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 1, v_a_2656_);
lean_ctor_set(v___x_2640_, 0, v___x_2642_);
v___x_2658_ = v___x_2640_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2642_);
lean_ctor_set(v_reuseFailAlloc_2662_, 1, v_a_2656_);
v___x_2658_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
size_t v___x_2659_; size_t v___x_2660_; 
v___x_2659_ = ((size_t)1ULL);
v___x_2660_ = lean_usize_add(v_i_2631_, v___x_2659_);
v_i_2631_ = v___x_2660_;
v_b_2632_ = v___x_2658_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2671_; 
lean_del_object(v___x_2640_);
lean_dec(v_snd_2638_);
v_a_2664_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2666_ = v___x_2644_;
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2644_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2669_; 
if (v_isShared_2667_ == 0)
{
v___x_2669_ = v___x_2666_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2664_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37___boxed(lean_object* v_init_2674_, lean_object* v_as_2675_, lean_object* v_sz_2676_, lean_object* v_i_2677_, lean_object* v_b_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
size_t v_sz_boxed_2682_; size_t v_i_boxed_2683_; lean_object* v_res_2684_; 
v_sz_boxed_2682_ = lean_unbox_usize(v_sz_2676_);
lean_dec(v_sz_2676_);
v_i_boxed_2683_ = lean_unbox_usize(v_i_2677_);
lean_dec(v_i_2677_);
v_res_2684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37(v_init_2674_, v_as_2675_, v_sz_boxed_2682_, v_i_boxed_2683_, v_b_2678_, v___y_2679_, v___y_2680_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec_ref(v_as_2675_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26___boxed(lean_object* v_init_2685_, lean_object* v_n_2686_, lean_object* v_b_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
lean_object* v_res_2691_; 
v_res_2691_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(v_init_2685_, v_n_2686_, v_b_2687_, v___y_2688_, v___y_2689_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec_ref(v_n_2686_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(lean_object* v_as_2692_, size_t v_sz_2693_, size_t v_i_2694_, lean_object* v_b_2695_, lean_object* v___y_2696_){
_start:
{
uint8_t v___x_2698_; 
v___x_2698_ = lean_usize_dec_lt(v_i_2694_, v_sz_2693_);
if (v___x_2698_ == 0)
{
lean_object* v___x_2699_; 
v___x_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2699_, 0, v_b_2695_);
return v___x_2699_;
}
else
{
uint8_t v___x_2700_; lean_object* v_a_2701_; lean_object* v___x_2702_; lean_object* v_ref_2703_; lean_object* v___x_2704_; 
lean_dec_ref(v_b_2695_);
v___x_2700_ = 0;
v_a_2701_ = lean_array_uget_borrowed(v_as_2692_, v_i_2694_);
lean_inc(v_a_2701_);
v___x_2702_ = l_Lean_Message_toString(v_a_2701_, v___x_2700_);
v_ref_2703_ = lean_ctor_get(v___y_2696_, 2);
v___x_2704_ = l_IO_eprintln___at___00main_spec__6(v___x_2702_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v___x_2705_; size_t v___x_2706_; size_t v___x_2707_; 
lean_dec_ref_known(v___x_2704_, 1);
v___x_2705_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_2706_ = ((size_t)1ULL);
v___x_2707_ = lean_usize_add(v_i_2694_, v___x_2706_);
v_i_2694_ = v___x_2707_;
v_b_2695_ = v___x_2705_;
goto _start;
}
else
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2720_; 
v_a_2709_ = lean_ctor_get(v___x_2704_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2711_ = v___x_2704_;
v_isShared_2712_ = v_isSharedCheck_2720_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2704_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2720_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2718_; 
v___x_2713_ = lean_io_error_to_string(v_a_2709_);
v___x_2714_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2713_);
v___x_2715_ = l_Lean_MessageData_ofFormat(v___x_2714_);
lean_inc(v_ref_2703_);
v___x_2716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2716_, 0, v_ref_2703_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 0, v___x_2716_);
v___x_2718_ = v___x_2711_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2716_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg___boxed(lean_object* v_as_2721_, lean_object* v_sz_2722_, lean_object* v_i_2723_, lean_object* v_b_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
size_t v_sz_boxed_2727_; size_t v_i_boxed_2728_; lean_object* v_res_2729_; 
v_sz_boxed_2727_ = lean_unbox_usize(v_sz_2722_);
lean_dec(v_sz_2722_);
v_i_boxed_2728_ = lean_unbox_usize(v_i_2723_);
lean_dec(v_i_2723_);
v_res_2729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(v_as_2721_, v_sz_boxed_2727_, v_i_boxed_2728_, v_b_2724_, v___y_2725_);
lean_dec_ref(v___y_2725_);
lean_dec_ref(v_as_2721_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27(lean_object* v_as_2730_, size_t v_sz_2731_, size_t v_i_2732_, lean_object* v_b_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
uint8_t v___x_2737_; 
v___x_2737_ = lean_usize_dec_lt(v_i_2732_, v_sz_2731_);
if (v___x_2737_ == 0)
{
lean_object* v___x_2738_; 
v___x_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2738_, 0, v_b_2733_);
return v___x_2738_;
}
else
{
uint8_t v___x_2739_; lean_object* v_a_2740_; lean_object* v___x_2741_; lean_object* v_ref_2742_; lean_object* v___x_2743_; 
lean_dec_ref(v_b_2733_);
v___x_2739_ = 0;
v_a_2740_ = lean_array_uget_borrowed(v_as_2730_, v_i_2732_);
lean_inc(v_a_2740_);
v___x_2741_ = l_Lean_Message_toString(v_a_2740_, v___x_2739_);
v_ref_2742_ = lean_ctor_get(v___y_2734_, 2);
v___x_2743_ = l_IO_eprintln___at___00main_spec__6(v___x_2741_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v___x_2744_; size_t v___x_2745_; size_t v___x_2746_; lean_object* v___x_2747_; 
lean_dec_ref_known(v___x_2743_, 1);
v___x_2744_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_2745_ = ((size_t)1ULL);
v___x_2746_ = lean_usize_add(v_i_2732_, v___x_2745_);
v___x_2747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(v_as_2730_, v_sz_2731_, v___x_2746_, v___x_2744_, v___y_2734_);
return v___x_2747_;
}
else
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2759_; 
v_a_2748_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2750_ = v___x_2743_;
v_isShared_2751_ = v_isSharedCheck_2759_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2743_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2759_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2757_; 
v___x_2752_ = lean_io_error_to_string(v_a_2748_);
v___x_2753_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2752_);
v___x_2754_ = l_Lean_MessageData_ofFormat(v___x_2753_);
lean_inc(v_ref_2742_);
v___x_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2755_, 0, v_ref_2742_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 0, v___x_2755_);
v___x_2757_ = v___x_2750_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2755_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27___boxed(lean_object* v_as_2760_, lean_object* v_sz_2761_, lean_object* v_i_2762_, lean_object* v_b_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
size_t v_sz_boxed_2767_; size_t v_i_boxed_2768_; lean_object* v_res_2769_; 
v_sz_boxed_2767_ = lean_unbox_usize(v_sz_2761_);
lean_dec(v_sz_2761_);
v_i_boxed_2768_ = lean_unbox_usize(v_i_2762_);
lean_dec(v_i_2762_);
v_res_2769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27(v_as_2760_, v_sz_boxed_2767_, v_i_boxed_2768_, v_b_2763_, v___y_2764_, v___y_2765_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
lean_dec_ref(v_as_2760_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__11(lean_object* v_t_2770_, lean_object* v_init_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v_root_2775_; lean_object* v_tail_2776_; lean_object* v___x_2777_; 
v_root_2775_ = lean_ctor_get(v_t_2770_, 0);
v_tail_2776_ = lean_ctor_get(v_t_2770_, 1);
v___x_2777_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(v_init_2771_, v_root_2775_, v_init_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2814_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2780_ = v___x_2777_;
v_isShared_2781_ = v_isSharedCheck_2814_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2777_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2814_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
if (lean_obj_tag(v_a_2778_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2784_; 
v_a_2782_ = lean_ctor_get(v_a_2778_, 0);
lean_inc(v_a_2782_);
lean_dec_ref_known(v_a_2778_, 1);
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 0, v_a_2782_);
v___x_2784_ = v___x_2780_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2782_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; size_t v_sz_2789_; size_t v___x_2790_; lean_object* v___x_2791_; 
lean_del_object(v___x_2780_);
v_a_2786_ = lean_ctor_get(v_a_2778_, 0);
lean_inc(v_a_2786_);
lean_dec_ref_known(v_a_2778_, 1);
v___x_2787_ = lean_box(0);
v___x_2788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2787_);
lean_ctor_set(v___x_2788_, 1, v_a_2786_);
v_sz_2789_ = lean_array_size(v_tail_2776_);
v___x_2790_ = ((size_t)0ULL);
v___x_2791_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27(v_tail_2776_, v_sz_2789_, v___x_2790_, v___x_2788_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2805_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2794_ = v___x_2791_;
v_isShared_2795_ = v_isSharedCheck_2805_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2791_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2805_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v_fst_2796_; 
v_fst_2796_ = lean_ctor_get(v_a_2792_, 0);
if (lean_obj_tag(v_fst_2796_) == 0)
{
lean_object* v_snd_2797_; lean_object* v___x_2799_; 
v_snd_2797_ = lean_ctor_get(v_a_2792_, 1);
lean_inc(v_snd_2797_);
lean_dec(v_a_2792_);
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 0, v_snd_2797_);
v___x_2799_ = v___x_2794_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_snd_2797_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
else
{
lean_object* v_val_2801_; lean_object* v___x_2803_; 
lean_inc_ref(v_fst_2796_);
lean_dec(v_a_2792_);
v_val_2801_ = lean_ctor_get(v_fst_2796_, 0);
lean_inc(v_val_2801_);
lean_dec_ref_known(v_fst_2796_, 1);
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 0, v_val_2801_);
v___x_2803_ = v___x_2794_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_val_2801_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
else
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
v_a_2806_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2808_ = v___x_2791_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2791_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
if (v_isShared_2809_ == 0)
{
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_a_2806_);
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
}
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
v_a_2815_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v___x_2777_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2777_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__11___boxed(lean_object* v_t_2823_, lean_object* v_init_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l_Lean_PersistentArray_forIn___at___00main_spec__11(v_t_2823_, v_init_2824_, v___y_2825_, v___y_2826_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec_ref(v_t_2823_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(lean_object* v_as_2829_, size_t v_sz_2830_, size_t v_i_2831_, lean_object* v_b_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
uint8_t v___x_2836_; 
v___x_2836_ = lean_usize_dec_lt(v_i_2831_, v_sz_2830_);
if (v___x_2836_ == 0)
{
lean_object* v___x_2837_; 
v___x_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2837_, 0, v_b_2832_);
return v___x_2837_;
}
else
{
lean_object* v_a_2838_; lean_object* v_declNames_2839_; lean_object* v___x_2840_; size_t v_sz_2841_; size_t v___x_2842_; lean_object* v___x_2843_; 
v_a_2838_ = lean_array_uget_borrowed(v_as_2829_, v_i_2831_);
v_declNames_2839_ = lean_ctor_get(v_a_2838_, 0);
v___x_2840_ = lean_box(0);
v_sz_2841_ = lean_array_size(v_declNames_2839_);
v___x_2842_ = ((size_t)0ULL);
v___x_2843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(v_declNames_2839_, v_sz_2841_, v___x_2842_, v___x_2840_, v___y_2833_, v___y_2834_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v___x_2844_; 
lean_dec_ref_known(v___x_2843_, 1);
v___x_2844_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v___y_2834_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v_unreported_2846_; lean_object* v___x_2847_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_a_2845_);
lean_dec_ref_known(v___x_2844_, 1);
v_unreported_2846_ = lean_ctor_get(v_a_2845_, 1);
lean_inc_ref(v_unreported_2846_);
lean_dec(v_a_2845_);
v___x_2847_ = l_Lean_PersistentArray_forIn___at___00main_spec__11(v_unreported_2846_, v___x_2840_, v___y_2833_, v___y_2834_);
lean_dec_ref(v_unreported_2846_);
if (lean_obj_tag(v___x_2847_) == 0)
{
size_t v___x_2848_; size_t v___x_2849_; 
lean_dec_ref_known(v___x_2847_, 1);
v___x_2848_ = ((size_t)1ULL);
v___x_2849_ = lean_usize_add(v_i_2831_, v___x_2848_);
v_i_2831_ = v___x_2849_;
v_b_2832_ = v___x_2840_;
goto _start;
}
else
{
return v___x_2847_;
}
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
v_a_2851_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v___x_2844_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2844_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
else
{
return v___x_2843_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___boxed(lean_object* v_as_2859_, lean_object* v_sz_2860_, lean_object* v_i_2861_, lean_object* v_b_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
size_t v_sz_boxed_2866_; size_t v_i_boxed_2867_; lean_object* v_res_2868_; 
v_sz_boxed_2866_ = lean_unbox_usize(v_sz_2860_);
lean_dec(v_sz_2860_);
v_i_boxed_2867_ = lean_unbox_usize(v_i_2861_);
lean_dec(v_i_2861_);
v_res_2868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(v_as_2859_, v_sz_boxed_2866_, v_i_boxed_2867_, v_b_2862_, v___y_2863_, v___y_2864_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec_ref(v_as_2859_);
return v_res_2868_;
}
}
static lean_object* _init_l_main___closed__1(void){
_start:
{
lean_object* v___x_2870_; 
v___x_2870_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg();
return v___x_2870_;
}
}
static lean_object* _init_l_main___closed__2(void){
_start:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2871_ = l_Lean_instInhabitedClassState_default;
v___x_2872_ = lean_box(0);
v___x_2873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2872_);
lean_ctor_set(v___x_2873_, 1, v___x_2871_);
return v___x_2873_;
}
}
static lean_object* _init_l_main___closed__3(void){
_start:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2874_ = l_Lean_Meta_Match_Extension_instInhabitedState;
v___x_2875_ = lean_box(0);
v___x_2876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
lean_ctor_set(v___x_2876_, 1, v___x_2874_);
return v___x_2876_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_2877_; 
v___x_2877_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_2877_;
}
}
static lean_object* _init_l_main___closed__5(void){
_start:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2878_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2879_ = lean_box(0);
v___x_2880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
lean_ctor_set(v___x_2880_, 1, v___x_2878_);
return v___x_2880_;
}
}
static lean_object* _init_l_main___closed__6(void){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2881_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_2882_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2881_);
return v___x_2882_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
lean_object* v___x_2883_; 
v___x_2883_ = l_Array_instInhabited___redArg();
return v___x_2883_;
}
}
static lean_object* _init_l_main___closed__17(void){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2896_ = ((lean_object*)(l_main___closed__16));
v___x_2897_ = lean_unsigned_to_nat(27u);
v___x_2898_ = lean_unsigned_to_nat(160u);
v___x_2899_ = ((lean_object*)(l_main___closed__15));
v___x_2900_ = ((lean_object*)(l_main___closed__14));
v___x_2901_ = l_mkPanicMessageWithDecl(v___x_2900_, v___x_2899_, v___x_2898_, v___x_2897_, v___x_2896_);
return v___x_2901_;
}
}
static lean_object* _init_l_main___closed__19(void){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2903_ = ((lean_object*)(l_main___closed__16));
v___x_2904_ = lean_unsigned_to_nat(51u);
v___x_2905_ = lean_unsigned_to_nat(133u);
v___x_2906_ = ((lean_object*)(l_main___closed__15));
v___x_2907_ = ((lean_object*)(l_main___closed__14));
v___x_2908_ = l_mkPanicMessageWithDecl(v___x_2907_, v___x_2906_, v___x_2905_, v___x_2904_, v___x_2903_);
return v___x_2908_;
}
}
static lean_object* _init_l_main___closed__20(void){
_start:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2909_ = lean_unsigned_to_nat(1u);
v___x_2910_ = l_Lean_firstFrontendMacroScope;
v___x_2911_ = lean_nat_add(v___x_2910_, v___x_2909_);
return v___x_2911_;
}
}
static lean_object* _init_l_main___closed__24(void){
_start:
{
lean_object* v___x_2918_; uint64_t v___x_2919_; lean_object* v___x_2920_; 
v___x_2918_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
v___x_2919_ = 0ULL;
v___x_2920_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2920_, 0, v___x_2918_);
lean_ctor_set_uint64(v___x_2920_, sizeof(void*)*1, v___x_2919_);
return v___x_2920_;
}
}
static lean_object* _init_l_main___closed__25(void){
_start:
{
lean_object* v___x_2921_; 
v___x_2921_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2921_;
}
}
static lean_object* _init_l_main___closed__26(void){
_start:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2922_ = lean_obj_once(&l_main___closed__25, &l_main___closed__25_once, _init_l_main___closed__25);
v___x_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2922_);
return v___x_2923_;
}
}
static lean_object* _init_l_main___closed__27(void){
_start:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2924_ = lean_obj_once(&l_main___closed__26, &l_main___closed__26_once, _init_l_main___closed__26);
v___x_2925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2924_);
lean_ctor_set(v___x_2925_, 1, v___x_2924_);
return v___x_2925_;
}
}
static lean_object* _init_l_main___closed__29(void){
_start:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2928_ = lean_unsigned_to_nat(0u);
v___x_2929_ = l_Lean_Options_empty;
v___x_2930_ = ((lean_object*)(l_main___closed__28));
v___x_2931_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2930_);
lean_ctor_set(v___x_2931_, 1, v___x_2929_);
lean_ctor_set(v___x_2931_, 2, v___x_2930_);
lean_ctor_set(v___x_2931_, 3, v___x_2928_);
lean_ctor_set(v___x_2931_, 4, v___x_2928_);
lean_ctor_set(v___x_2931_, 5, v___x_2928_);
return v___x_2931_;
}
}
static lean_object* _init_l_main___closed__30(void){
_start:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2932_ = l_Lean_NameSet_empty;
v___x_2933_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
v___x_2934_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2933_);
lean_ctor_set(v___x_2934_, 1, v___x_2933_);
lean_ctor_set(v___x_2934_, 2, v___x_2932_);
return v___x_2934_;
}
}
static lean_object* _init_l_main___closed__31(void){
_start:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; uint8_t v___x_2937_; lean_object* v___x_2938_; 
v___x_2935_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
v___x_2936_ = lean_obj_once(&l_main___closed__26, &l_main___closed__26_once, _init_l_main___closed__26);
v___x_2937_ = 1;
v___x_2938_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2938_, 0, v___x_2936_);
lean_ctor_set(v___x_2938_, 1, v___x_2936_);
lean_ctor_set(v___x_2938_, 2, v___x_2935_);
lean_ctor_set_uint8(v___x_2938_, sizeof(void*)*3, v___x_2937_);
return v___x_2938_;
}
}
static uint8_t _init_l_main___closed__35(void){
_start:
{
uint8_t v___x_2943_; uint8_t v___x_2944_; uint8_t v___x_2945_; 
v___x_2943_ = 2;
v___x_2944_ = 0;
v___x_2945_ = l_Lean_instOrdOLeanLevel_ord(v___x_2944_, v___x_2943_);
return v___x_2945_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_2946_; lean_object* v___x_2947_; 
v___x_2946_ = 1;
v___x_2947_ = lean_box_uint32(v___x_2946_);
return v___x_2947_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_2948_; lean_object* v___x_2949_; 
v___x_2948_ = 0;
v___x_2949_ = lean_box_uint32(v___x_2948_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_2950_){
_start:
{
if (lean_obj_tag(v_args_2950_) == 1)
{
lean_object* v_tail_2975_; 
v_tail_2975_ = lean_ctor_get(v_args_2950_, 1);
lean_inc(v_tail_2975_);
if (lean_obj_tag(v_tail_2975_) == 1)
{
lean_object* v_tail_2976_; 
v_tail_2976_ = lean_ctor_get(v_tail_2975_, 1);
lean_inc(v_tail_2976_);
if (lean_obj_tag(v_tail_2976_) == 1)
{
lean_object* v_head_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_3665_; 
v_head_2977_ = lean_ctor_get(v_args_2950_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v_args_2950_);
if (v_isSharedCheck_3665_ == 0)
{
lean_object* v_unused_3666_; 
v_unused_3666_ = lean_ctor_get(v_args_2950_, 1);
lean_dec(v_unused_3666_);
v___x_2979_ = v_args_2950_;
v_isShared_2980_ = v_isSharedCheck_3665_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_head_2977_);
lean_dec(v_args_2950_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_3665_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v_head_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_3663_; 
v_head_2981_ = lean_ctor_get(v_tail_2975_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v_tail_2975_);
if (v_isSharedCheck_3663_ == 0)
{
lean_object* v_unused_3664_; 
v_unused_3664_ = lean_ctor_get(v_tail_2975_, 1);
lean_dec(v_unused_3664_);
v___x_2983_ = v_tail_2975_;
v_isShared_2984_ = v_isSharedCheck_3663_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_head_2981_);
lean_dec(v_tail_2975_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_3663_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v_head_2985_; lean_object* v_tail_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_3662_; 
v_head_2985_ = lean_ctor_get(v_tail_2976_, 0);
v_tail_2986_ = lean_ctor_get(v_tail_2976_, 1);
v_isSharedCheck_3662_ = !lean_is_exclusive(v_tail_2976_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_2988_ = v_tail_2976_;
v_isShared_2989_ = v_isSharedCheck_3662_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_tail_2986_);
lean_inc(v_head_2985_);
lean_dec(v_tail_2976_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_3662_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2990_ = lean_obj_once(&l_main___closed__1, &l_main___closed__1_once, _init_l_main___closed__1);
v___x_2991_ = lean_box(0);
v___x_2992_ = lean_obj_once(&l_main___closed__2, &l_main___closed__2_once, _init_l_main___closed__2);
v___x_2993_ = lean_obj_once(&l_main___closed__3, &l_main___closed__3_once, _init_l_main___closed__3);
v___x_2994_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2995_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2996_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_2997_ = lean_box(1);
v___x_2998_ = ((lean_object*)(l_main___closed__8));
v___x_2999_ = l_Lean_ModuleSetup_load(v_head_2977_);
lean_dec(v_head_2977_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; lean_object* v_name_3001_; lean_object* v_package_x3f_3002_; lean_object* v_importArts_3003_; lean_object* v_options_3004_; lean_object* v___f_3005_; uint8_t v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3010_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc(v_a_3000_);
lean_dec_ref_known(v___x_2999_, 1);
v_name_3001_ = lean_ctor_get(v_a_3000_, 0);
lean_inc(v_name_3001_);
v_package_x3f_3002_ = lean_ctor_get(v_a_3000_, 1);
lean_inc(v_package_x3f_3002_);
v_importArts_3003_ = lean_ctor_get(v_a_3000_, 3);
lean_inc(v_importArts_3003_);
v_options_3004_ = lean_ctor_get(v_a_3000_, 6);
lean_inc(v_options_3004_);
lean_dec(v_a_3000_);
v___f_3005_ = lean_alloc_closure((void*)(l_main___lam__0), 2, 1);
lean_closure_set(v___f_3005_, 0, v_package_x3f_3002_);
v___x_3006_ = 0;
v___x_3007_ = l_Lean_LeanOptions_toOptions(v_options_3004_);
v___x_3008_ = lean_box(v___x_3006_);
if (v_isShared_2989_ == 0)
{
lean_ctor_set_tag(v___x_2988_, 0);
lean_ctor_set(v___x_2988_, 1, v___x_3007_);
lean_ctor_set(v___x_2988_, 0, v___x_3008_);
v___x_3010_ = v___x_2988_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3008_);
lean_ctor_set(v_reuseFailAlloc_3653_, 1, v___x_3007_);
v___x_3010_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
lean_object* v___x_3011_; 
v___x_3011_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_tail_2986_, v___x_3010_);
lean_dec(v_tail_2986_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; lean_object* v_fst_3013_; lean_object* v_snd_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3644_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_a_3012_);
lean_dec_ref_known(v___x_3011_, 1);
v_fst_3013_ = lean_ctor_get(v_a_3012_, 0);
v_snd_3014_ = lean_ctor_get(v_a_3012_, 1);
v_isSharedCheck_3644_ = !lean_is_exclusive(v_a_3012_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3016_ = v_a_3012_;
v_isShared_3017_ = v_isSharedCheck_3644_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_snd_3014_);
lean_inc(v_fst_3013_);
lean_dec(v_a_3012_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3644_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3018_; uint8_t v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___y_3025_; uint8_t v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; uint8_t v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; uint8_t v___y_3188_; lean_object* v___y_3189_; uint8_t v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v_nextMacroScope_3207_; lean_object* v_ngen_3208_; lean_object* v_auxDeclNGen_3209_; lean_object* v_traceState_3210_; lean_object* v_recordedDeps_3211_; lean_object* v_messages_3212_; lean_object* v_infoState_3213_; lean_object* v_snapshotTasks_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3232_; uint8_t v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; uint8_t v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; uint16_t v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v_fileName_3257_; lean_object* v_fileMap_3258_; lean_object* v_currNamespace_3259_; lean_object* v_openDecls_3260_; lean_object* v_initHeartbeats_3261_; lean_object* v_maxHeartbeats_3262_; lean_object* v_quotContext_3263_; lean_object* v_currMacroScope_3264_; lean_object* v_cancelTk_x3f_3265_; lean_object* v_inheritedTraceOptions_3266_; lean_object* v_currRecDepth_3267_; lean_object* v_ref_3268_; uint8_t v_suppressElabErrors_3269_; uint8_t v_checkDeprecated_3270_; uint8_t v_isRecordingDeps_3271_; lean_object* v___y_3272_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; uint8_t v___y_3298_; lean_object* v___y_3299_; uint8_t v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; uint8_t v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; uint16_t v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___x_3358_; 
v___x_3018_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_3019_ = 1;
v___x_3020_ = l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(v_snd_3014_, v___x_3018_, v___x_3019_);
v___x_3021_ = l_Lean_maxHeartbeats;
v___x_3022_ = lean_unsigned_to_nat(0u);
v___x_3023_ = l_Lean_Option_set___at___00main_spec__3(v___x_3020_, v___x_3021_, v___x_3022_);
v___x_3358_ = lean_init_search_path();
if (lean_obj_tag(v___x_3358_) == 0)
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; uint8_t v___x_3364_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3479_; uint8_t v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3536_; lean_object* v___y_3537_; uint8_t v___y_3608_; uint8_t v___x_3635_; 
lean_dec_ref_known(v___x_3358_, 1);
v___x_3359_ = ((lean_object*)(l_main___closed__18));
lean_inc(v_name_3001_);
v___x_3360_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3360_, 0, v_name_3001_);
lean_ctor_set_uint8(v___x_3360_, sizeof(void*)*1, v___x_3019_);
lean_ctor_set_uint8(v___x_3360_, sizeof(void*)*1 + 1, v___x_3019_);
lean_ctor_set_uint8(v___x_3360_, sizeof(void*)*1 + 2, v___x_3006_);
v___x_3361_ = lean_unsigned_to_nat(1u);
v___x_3362_ = lean_mk_empty_array_with_capacity(v___x_3361_);
v___x_3363_ = lean_array_push(v___x_3362_, v___x_3360_);
v___x_3364_ = 0;
v___x_3635_ = lean_uint8_once(&l_main___closed__35, &l_main___closed__35_once, _init_l_main___closed__35);
if (v___x_3635_ == 0)
{
v___y_3608_ = v___x_3019_;
goto v___jp_3607_;
}
else
{
v___y_3608_ = v___x_3006_;
goto v___jp_3607_;
}
v___jp_3365_:
{
lean_object* v___x_3370_; lean_object* v_moduleData_3371_; lean_object* v___x_3372_; uint8_t v___x_3373_; 
v___x_3370_ = l_Lean_Environment_header(v___y_3369_);
v_moduleData_3371_ = lean_ctor_get(v___x_3370_, 7);
lean_inc_ref(v_moduleData_3371_);
lean_dec_ref(v___x_3370_);
v___x_3372_ = lean_array_get_size(v_moduleData_3371_);
v___x_3373_ = lean_nat_dec_lt(v___y_3367_, v___x_3372_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3374_; lean_object* v___x_3375_; 
lean_dec_ref(v_moduleData_3371_);
lean_dec_ref(v___y_3369_);
lean_dec(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec(v___y_3366_);
lean_dec_ref(v___x_3023_);
lean_del_object(v___x_3016_);
lean_dec(v_fst_3013_);
lean_dec(v_name_3001_);
lean_dec(v_head_2985_);
lean_del_object(v___x_2983_);
lean_dec(v_head_2981_);
v___x_3374_ = lean_obj_once(&l_main___closed__19, &l_main___closed__19_once, _init_l_main___closed__19);
v___x_3375_ = l_panic___at___00main_spec__5(v___x_3374_);
return v___x_3375_;
}
else
{
lean_object* v_base_3376_; lean_object* v_private_3377_; lean_object* v_header_3378_; lean_object* v_serverBaseExts_3379_; lean_object* v_checked_3380_; lean_object* v_asyncConstsMap_3381_; lean_object* v_asyncCtx_x3f_3382_; lean_object* v_importRealizationCtx_x3f_3383_; lean_object* v_localRealizationCtxMap_3384_; lean_object* v_allRealizations_3385_; uint8_t v_isExporting_3386_; uint8_t v_isRecordingDeps_3387_; lean_object* v_synthCacheRaw_x3f_3388_; lean_object* v_declChangeLog_3389_; lean_object* v_recordingConstGen_3390_; lean_object* v_constAddedGens_3391_; lean_object* v_constGen_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3476_; 
v_base_3376_ = lean_ctor_get(v___y_3369_, 0);
lean_inc_ref(v_base_3376_);
v_private_3377_ = lean_ctor_get(v_base_3376_, 0);
lean_inc(v_private_3377_);
v_header_3378_ = lean_ctor_get(v_private_3377_, 7);
lean_inc_ref(v_header_3378_);
v_serverBaseExts_3379_ = lean_ctor_get(v___y_3369_, 1);
v_checked_3380_ = lean_ctor_get(v___y_3369_, 2);
v_asyncConstsMap_3381_ = lean_ctor_get(v___y_3369_, 3);
v_asyncCtx_x3f_3382_ = lean_ctor_get(v___y_3369_, 4);
v_importRealizationCtx_x3f_3383_ = lean_ctor_get(v___y_3369_, 5);
v_localRealizationCtxMap_3384_ = lean_ctor_get(v___y_3369_, 6);
v_allRealizations_3385_ = lean_ctor_get(v___y_3369_, 7);
v_isExporting_3386_ = lean_ctor_get_uint8(v___y_3369_, sizeof(void*)*13);
v_isRecordingDeps_3387_ = lean_ctor_get_uint8(v___y_3369_, sizeof(void*)*13 + 1);
v_synthCacheRaw_x3f_3388_ = lean_ctor_get(v___y_3369_, 8);
v_declChangeLog_3389_ = lean_ctor_get(v___y_3369_, 9);
v_recordingConstGen_3390_ = lean_ctor_get(v___y_3369_, 10);
v_constAddedGens_3391_ = lean_ctor_get(v___y_3369_, 11);
v_constGen_3392_ = lean_ctor_get(v___y_3369_, 12);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___y_3369_);
if (v_isSharedCheck_3476_ == 0)
{
lean_object* v_unused_3477_; 
v_unused_3477_ = lean_ctor_get(v___y_3369_, 0);
lean_dec(v_unused_3477_);
v___x_3394_ = v___y_3369_;
v_isShared_3395_ = v_isSharedCheck_3476_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_constGen_3392_);
lean_inc(v_constAddedGens_3391_);
lean_inc(v_recordingConstGen_3390_);
lean_inc(v_declChangeLog_3389_);
lean_inc(v_synthCacheRaw_x3f_3388_);
lean_inc(v_allRealizations_3385_);
lean_inc(v_localRealizationCtxMap_3384_);
lean_inc(v_importRealizationCtx_x3f_3383_);
lean_inc(v_asyncCtx_x3f_3382_);
lean_inc(v_asyncConstsMap_3381_);
lean_inc(v_checked_3380_);
lean_inc(v_serverBaseExts_3379_);
lean_dec(v___y_3369_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3476_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v_public_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3474_; 
v_public_3396_ = lean_ctor_get(v_base_3376_, 1);
v_isSharedCheck_3474_ = !lean_is_exclusive(v_base_3376_);
if (v_isSharedCheck_3474_ == 0)
{
lean_object* v_unused_3475_; 
v_unused_3475_ = lean_ctor_get(v_base_3376_, 0);
lean_dec(v_unused_3475_);
v___x_3398_ = v_base_3376_;
v_isShared_3399_ = v_isSharedCheck_3474_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_public_3396_);
lean_dec(v_base_3376_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3474_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v_constants_3400_; uint8_t v_quotInit_3401_; lean_object* v_diagnostics_3402_; lean_object* v_importedExtraConsts_3403_; lean_object* v_extensions_3404_; lean_object* v_irBaseExts_3405_; lean_object* v_extGens_3406_; lean_object* v_trackedGen_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3472_; 
v_constants_3400_ = lean_ctor_get(v_private_3377_, 0);
v_quotInit_3401_ = lean_ctor_get_uint8(v_private_3377_, sizeof(void*)*8);
v_diagnostics_3402_ = lean_ctor_get(v_private_3377_, 1);
v_importedExtraConsts_3403_ = lean_ctor_get(v_private_3377_, 2);
v_extensions_3404_ = lean_ctor_get(v_private_3377_, 3);
v_irBaseExts_3405_ = lean_ctor_get(v_private_3377_, 4);
v_extGens_3406_ = lean_ctor_get(v_private_3377_, 5);
v_trackedGen_3407_ = lean_ctor_get(v_private_3377_, 6);
v_isSharedCheck_3472_ = !lean_is_exclusive(v_private_3377_);
if (v_isSharedCheck_3472_ == 0)
{
lean_object* v_unused_3473_; 
v_unused_3473_ = lean_ctor_get(v_private_3377_, 7);
lean_dec(v_unused_3473_);
v___x_3409_ = v_private_3377_;
v_isShared_3410_ = v_isSharedCheck_3472_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_trackedGen_3407_);
lean_inc(v_extGens_3406_);
lean_inc(v_irBaseExts_3405_);
lean_inc(v_extensions_3404_);
lean_inc(v_importedExtraConsts_3403_);
lean_inc(v_diagnostics_3402_);
lean_inc(v_constants_3400_);
lean_dec(v_private_3377_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3472_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
uint32_t v_trustLevel_3411_; lean_object* v_mainModule_3412_; uint8_t v_isModule_3413_; lean_object* v_regions_3414_; lean_object* v_modules_3415_; lean_object* v_moduleNames_3416_; lean_object* v_moduleName2Idx_3417_; lean_object* v_importAllModules_3418_; lean_object* v_moduleData_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3470_; 
v_trustLevel_3411_ = lean_ctor_get_uint32(v_header_3378_, sizeof(void*)*8);
v_mainModule_3412_ = lean_ctor_get(v_header_3378_, 0);
v_isModule_3413_ = lean_ctor_get_uint8(v_header_3378_, sizeof(void*)*8 + 4);
v_regions_3414_ = lean_ctor_get(v_header_3378_, 2);
v_modules_3415_ = lean_ctor_get(v_header_3378_, 3);
v_moduleNames_3416_ = lean_ctor_get(v_header_3378_, 4);
v_moduleName2Idx_3417_ = lean_ctor_get(v_header_3378_, 5);
v_importAllModules_3418_ = lean_ctor_get(v_header_3378_, 6);
v_moduleData_3419_ = lean_ctor_get(v_header_3378_, 7);
v_isSharedCheck_3470_ = !lean_is_exclusive(v_header_3378_);
if (v_isSharedCheck_3470_ == 0)
{
lean_object* v_unused_3471_; 
v_unused_3471_ = lean_ctor_get(v_header_3378_, 1);
lean_dec(v_unused_3471_);
v___x_3421_ = v_header_3378_;
v_isShared_3422_ = v_isSharedCheck_3470_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_moduleData_3419_);
lean_inc(v_importAllModules_3418_);
lean_inc(v_moduleName2Idx_3417_);
lean_inc(v_moduleNames_3416_);
lean_inc(v_modules_3415_);
lean_inc(v_regions_3414_);
lean_inc(v_mainModule_3412_);
lean_dec(v_header_3378_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3470_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3423_; lean_object* v_imports_3424_; lean_object* v___x_3426_; 
v___x_3423_ = lean_array_fget(v_moduleData_3371_, v___y_3367_);
lean_dec_ref(v_moduleData_3371_);
v_imports_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc_ref(v_imports_3424_);
lean_dec(v___x_3423_);
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 1, v_imports_3424_);
v___x_3426_ = v___x_3421_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 8, 5);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_mainModule_3412_);
lean_ctor_set(v_reuseFailAlloc_3469_, 1, v_imports_3424_);
lean_ctor_set(v_reuseFailAlloc_3469_, 2, v_regions_3414_);
lean_ctor_set(v_reuseFailAlloc_3469_, 3, v_modules_3415_);
lean_ctor_set(v_reuseFailAlloc_3469_, 4, v_moduleNames_3416_);
lean_ctor_set(v_reuseFailAlloc_3469_, 5, v_moduleName2Idx_3417_);
lean_ctor_set(v_reuseFailAlloc_3469_, 6, v_importAllModules_3418_);
lean_ctor_set(v_reuseFailAlloc_3469_, 7, v_moduleData_3419_);
lean_ctor_set_uint32(v_reuseFailAlloc_3469_, sizeof(void*)*8, v_trustLevel_3411_);
lean_ctor_set_uint8(v_reuseFailAlloc_3469_, sizeof(void*)*8 + 4, v_isModule_3413_);
v___x_3426_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
lean_object* v___x_3428_; 
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 7, v___x_3426_);
v___x_3428_ = v___x_3409_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_constants_3400_);
lean_ctor_set(v_reuseFailAlloc_3468_, 1, v_diagnostics_3402_);
lean_ctor_set(v_reuseFailAlloc_3468_, 2, v_importedExtraConsts_3403_);
lean_ctor_set(v_reuseFailAlloc_3468_, 3, v_extensions_3404_);
lean_ctor_set(v_reuseFailAlloc_3468_, 4, v_irBaseExts_3405_);
lean_ctor_set(v_reuseFailAlloc_3468_, 5, v_extGens_3406_);
lean_ctor_set(v_reuseFailAlloc_3468_, 6, v_trackedGen_3407_);
lean_ctor_set(v_reuseFailAlloc_3468_, 7, v___x_3426_);
lean_ctor_set_uint8(v_reuseFailAlloc_3468_, sizeof(void*)*8, v_quotInit_3401_);
v___x_3428_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
lean_object* v___x_3430_; 
if (v_isShared_3399_ == 0)
{
lean_ctor_set(v___x_3398_, 0, v___x_3428_);
v___x_3430_ = v___x_3398_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3428_);
lean_ctor_set(v_reuseFailAlloc_3467_, 1, v_public_3396_);
v___x_3430_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
lean_object* v___x_3432_; 
if (v_isShared_3395_ == 0)
{
lean_ctor_set(v___x_3394_, 0, v___x_3430_);
v___x_3432_ = v___x_3394_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3430_);
lean_ctor_set(v_reuseFailAlloc_3466_, 1, v_serverBaseExts_3379_);
lean_ctor_set(v_reuseFailAlloc_3466_, 2, v_checked_3380_);
lean_ctor_set(v_reuseFailAlloc_3466_, 3, v_asyncConstsMap_3381_);
lean_ctor_set(v_reuseFailAlloc_3466_, 4, v_asyncCtx_x3f_3382_);
lean_ctor_set(v_reuseFailAlloc_3466_, 5, v_importRealizationCtx_x3f_3383_);
lean_ctor_set(v_reuseFailAlloc_3466_, 6, v_localRealizationCtxMap_3384_);
lean_ctor_set(v_reuseFailAlloc_3466_, 7, v_allRealizations_3385_);
lean_ctor_set(v_reuseFailAlloc_3466_, 8, v_synthCacheRaw_x3f_3388_);
lean_ctor_set(v_reuseFailAlloc_3466_, 9, v_declChangeLog_3389_);
lean_ctor_set(v_reuseFailAlloc_3466_, 10, v_recordingConstGen_3390_);
lean_ctor_set(v_reuseFailAlloc_3466_, 11, v_constAddedGens_3391_);
lean_ctor_set(v_reuseFailAlloc_3466_, 12, v_constGen_3392_);
lean_ctor_set_uint8(v_reuseFailAlloc_3466_, sizeof(void*)*13, v_isExporting_3386_);
lean_ctor_set_uint8(v_reuseFailAlloc_3466_, sizeof(void*)*13 + 1, v_isRecordingDeps_3387_);
v___x_3432_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; uint16_t v___x_3441_; uint8_t v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v_env_3460_; uint8_t v___x_3461_; uint16_t v___x_3462_; uint16_t v___x_3463_; uint16_t v___x_3464_; uint8_t v___x_3465_; 
v___x_3433_ = l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
v___x_3434_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2998_, v___x_3433_, v___x_3432_, v___y_3367_, v___x_3364_);
lean_dec(v___y_3367_);
v___x_3435_ = l_Lean_instInhabitedFileMap_default;
v___x_3436_ = lean_unsigned_to_nat(1000u);
v___x_3437_ = l_Lean_Core_getMaxHeartbeats(v___x_3023_);
v___x_3438_ = l_Lean_firstFrontendMacroScope;
v___x_3439_ = lean_box(0);
v___x_3440_ = lean_box(0);
v___x_3441_ = l_Lean_OptionFlags_ofOptions(v___x_3023_);
v___x_3442_ = 0;
v___x_3443_ = lean_obj_once(&l_main___closed__20, &l_main___closed__20_once, _init_l_main___closed__20);
v___x_3444_ = ((lean_object*)(l_main___closed__23));
lean_inc_n(v___y_3368_, 3);
v___x_3445_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3445_, 0, v___y_3368_);
lean_ctor_set(v___x_3445_, 1, v___x_3361_);
lean_ctor_set(v___x_3445_, 2, v___x_2991_);
v___x_3446_ = lean_obj_once(&l_main___closed__24, &l_main___closed__24_once, _init_l_main___closed__24);
v___x_3447_ = lean_obj_once(&l_main___closed__27, &l_main___closed__27_once, _init_l_main___closed__27);
v___x_3448_ = ((lean_object*)(l_main___closed__28));
v___x_3449_ = l_Lean_Options_empty;
v___x_3450_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_3451_ = lean_obj_once(&l_main___closed__30, &l_main___closed__30_once, _init_l_main___closed__30);
v___x_3452_ = lean_obj_once(&l_main___closed__31, &l_main___closed__31_once, _init_l_main___closed__31);
lean_inc_ref(v___x_3445_);
v___x_3453_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3432_);
lean_ctor_set(v___x_3453_, 1, v___x_3443_);
lean_ctor_set(v___x_3453_, 2, v___x_3444_);
lean_ctor_set(v___x_3453_, 3, v___x_3445_);
lean_ctor_set(v___x_3453_, 4, v___x_3446_);
lean_ctor_set(v___x_3453_, 5, v___x_3447_);
lean_ctor_set(v___x_3453_, 6, v___x_3450_);
lean_ctor_set(v___x_3453_, 7, v___x_3451_);
lean_ctor_set(v___x_3453_, 8, v___x_3452_);
lean_ctor_set(v___x_3453_, 9, v___x_3448_);
v___x_3454_ = lean_st_mk_ref(v___x_3453_);
v___x_3455_ = l_Lean_inheritedTraceOptions;
v___x_3456_ = lean_st_ref_get(v___x_3455_);
lean_inc(v___x_3456_);
lean_inc(v___x_3437_);
lean_inc_ref(v___x_3023_);
lean_inc(v_head_2981_);
v___x_3457_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3457_, 0, v_head_2981_);
lean_ctor_set(v___x_3457_, 1, v___x_3435_);
lean_ctor_set(v___x_3457_, 2, v___x_3023_);
lean_ctor_set(v___x_3457_, 3, v___x_3436_);
lean_ctor_set(v___x_3457_, 4, v___y_3368_);
lean_ctor_set(v___x_3457_, 5, v___x_2991_);
lean_ctor_set(v___x_3457_, 6, v___x_3022_);
lean_ctor_set(v___x_3457_, 7, v___x_3437_);
lean_ctor_set(v___x_3457_, 8, v___y_3368_);
lean_ctor_set(v___x_3457_, 9, v___x_3438_);
lean_ctor_set(v___x_3457_, 10, v___x_3439_);
lean_ctor_set(v___x_3457_, 11, v___x_3456_);
v___x_3458_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3458_, 0, v___x_3457_);
lean_ctor_set(v___x_3458_, 1, v___x_3022_);
lean_ctor_set(v___x_3458_, 2, v___x_3440_);
lean_ctor_set_uint16(v___x_3458_, sizeof(void*)*3, v___x_3441_);
lean_ctor_set_uint8(v___x_3458_, sizeof(void*)*3 + 2, v___x_3006_);
lean_ctor_set_uint8(v___x_3458_, sizeof(void*)*3 + 3, v___x_3442_);
lean_ctor_set_uint8(v___x_3458_, sizeof(void*)*3 + 4, v___x_3006_);
v___x_3459_ = lean_st_ref_get(v___x_3454_);
v_env_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc_ref(v_env_3460_);
lean_dec(v___x_3459_);
v___x_3461_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3460_);
lean_dec_ref(v_env_3460_);
v___x_3462_ = 512;
v___x_3463_ = lean_uint16_land(v___x_3441_, v___x_3462_);
v___x_3464_ = 0;
v___x_3465_ = lean_uint16_dec_eq(v___x_3463_, v___x_3464_);
if (v___x_3465_ == 0)
{
if (v___x_3461_ == 0)
{
lean_dec(v___x_3456_);
lean_dec(v___x_3437_);
v___y_3295_ = v___x_2991_;
v___y_3296_ = v___x_3439_;
v___y_3297_ = v___x_3440_;
v___y_3298_ = v___x_3442_;
v___y_3299_ = v___x_3447_;
v___y_3300_ = v___x_3373_;
v___y_3301_ = v___x_3449_;
v___y_3302_ = v___x_3435_;
v___y_3303_ = v___x_3438_;
v___y_3304_ = v___y_3366_;
v___y_3305_ = v___x_3450_;
v___y_3306_ = v___x_3445_;
v___y_3307_ = v___x_3446_;
v___y_3308_ = v___x_3443_;
v___y_3309_ = v___x_3451_;
v___y_3310_ = v___x_3458_;
v___y_3311_ = v___x_3444_;
v___y_3312_ = v___x_3434_;
v___y_3313_ = v___x_3447_;
v___y_3314_ = v___x_3373_;
v___y_3315_ = v___x_3452_;
v___y_3316_ = v___x_3433_;
v___y_3317_ = v___x_3449_;
v___y_3318_ = v___x_3454_;
v___y_3319_ = v___x_3441_;
v___y_3320_ = v___x_3448_;
v___y_3321_ = v___y_3368_;
goto v___jp_3294_;
}
else
{
lean_dec_ref_known(v___x_3458_, 3);
lean_inc(v_head_2981_);
lean_inc_n(v___y_3368_, 2);
lean_inc(v___x_3454_);
v___y_3232_ = v___x_2991_;
v___y_3233_ = v___x_3442_;
v___y_3234_ = v___x_3440_;
v___y_3235_ = v___x_3439_;
v___y_3236_ = v___x_3447_;
v___y_3237_ = v___x_3373_;
v___y_3238_ = v___x_3449_;
v___y_3239_ = v___x_3435_;
v___y_3240_ = v___x_3438_;
v___y_3241_ = v___y_3366_;
v___y_3242_ = v___x_3450_;
v___y_3243_ = v___x_3445_;
v___y_3244_ = v___x_3446_;
v___y_3245_ = v___x_3443_;
v___y_3246_ = v___x_3451_;
v___y_3247_ = v___x_3444_;
v___y_3248_ = v___x_3434_;
v___y_3249_ = v___x_3447_;
v___y_3250_ = v___x_3452_;
v___y_3251_ = v___x_3433_;
v___y_3252_ = v___x_3449_;
v___y_3253_ = v___x_3454_;
v___y_3254_ = v___x_3441_;
v___y_3255_ = v___x_3448_;
v___y_3256_ = v___y_3368_;
v_fileName_3257_ = v_head_2981_;
v_fileMap_3258_ = v___x_3435_;
v_currNamespace_3259_ = v___y_3368_;
v_openDecls_3260_ = v___x_2991_;
v_initHeartbeats_3261_ = v___x_3022_;
v_maxHeartbeats_3262_ = v___x_3437_;
v_quotContext_3263_ = v___y_3368_;
v_currMacroScope_3264_ = v___x_3438_;
v_cancelTk_x3f_3265_ = v___x_3439_;
v_inheritedTraceOptions_3266_ = v___x_3456_;
v_currRecDepth_3267_ = v___x_3022_;
v_ref_3268_ = v___x_3440_;
v_suppressElabErrors_3269_ = v___x_3006_;
v_checkDeprecated_3270_ = v___x_3442_;
v_isRecordingDeps_3271_ = v___x_3006_;
v___y_3272_ = v___x_3454_;
goto v___jp_3231_;
}
}
else
{
if (v___x_3461_ == 0)
{
lean_dec_ref_known(v___x_3458_, 3);
lean_inc(v_head_2981_);
lean_inc_n(v___y_3368_, 2);
lean_inc(v___x_3454_);
v___y_3232_ = v___x_2991_;
v___y_3233_ = v___x_3442_;
v___y_3234_ = v___x_3440_;
v___y_3235_ = v___x_3439_;
v___y_3236_ = v___x_3447_;
v___y_3237_ = v___x_3373_;
v___y_3238_ = v___x_3449_;
v___y_3239_ = v___x_3435_;
v___y_3240_ = v___x_3438_;
v___y_3241_ = v___y_3366_;
v___y_3242_ = v___x_3450_;
v___y_3243_ = v___x_3445_;
v___y_3244_ = v___x_3446_;
v___y_3245_ = v___x_3443_;
v___y_3246_ = v___x_3451_;
v___y_3247_ = v___x_3444_;
v___y_3248_ = v___x_3434_;
v___y_3249_ = v___x_3447_;
v___y_3250_ = v___x_3452_;
v___y_3251_ = v___x_3433_;
v___y_3252_ = v___x_3449_;
v___y_3253_ = v___x_3454_;
v___y_3254_ = v___x_3441_;
v___y_3255_ = v___x_3448_;
v___y_3256_ = v___y_3368_;
v_fileName_3257_ = v_head_2981_;
v_fileMap_3258_ = v___x_3435_;
v_currNamespace_3259_ = v___y_3368_;
v_openDecls_3260_ = v___x_2991_;
v_initHeartbeats_3261_ = v___x_3022_;
v_maxHeartbeats_3262_ = v___x_3437_;
v_quotContext_3263_ = v___y_3368_;
v_currMacroScope_3264_ = v___x_3438_;
v_cancelTk_x3f_3265_ = v___x_3439_;
v_inheritedTraceOptions_3266_ = v___x_3456_;
v_currRecDepth_3267_ = v___x_3022_;
v_ref_3268_ = v___x_3440_;
v_suppressElabErrors_3269_ = v___x_3006_;
v_checkDeprecated_3270_ = v___x_3442_;
v_isRecordingDeps_3271_ = v___x_3006_;
v___y_3272_ = v___x_3454_;
goto v___jp_3231_;
}
else
{
lean_dec(v___x_3456_);
lean_dec(v___x_3437_);
v___y_3295_ = v___x_2991_;
v___y_3296_ = v___x_3439_;
v___y_3297_ = v___x_3440_;
v___y_3298_ = v___x_3442_;
v___y_3299_ = v___x_3447_;
v___y_3300_ = v___x_3373_;
v___y_3301_ = v___x_3449_;
v___y_3302_ = v___x_3435_;
v___y_3303_ = v___x_3438_;
v___y_3304_ = v___y_3366_;
v___y_3305_ = v___x_3450_;
v___y_3306_ = v___x_3445_;
v___y_3307_ = v___x_3446_;
v___y_3308_ = v___x_3443_;
v___y_3309_ = v___x_3451_;
v___y_3310_ = v___x_3458_;
v___y_3311_ = v___x_3444_;
v___y_3312_ = v___x_3434_;
v___y_3313_ = v___x_3447_;
v___y_3314_ = v___x_3006_;
v___y_3315_ = v___x_3452_;
v___y_3316_ = v___x_3433_;
v___y_3317_ = v___x_3449_;
v___y_3318_ = v___x_3454_;
v___y_3319_ = v___x_3441_;
v___y_3320_ = v___x_3448_;
v___y_3321_ = v___y_3368_;
goto v___jp_3294_;
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
v___jp_3478_:
{
lean_object* v___x_3488_; 
if (v_isShared_2980_ == 0)
{
lean_ctor_set_tag(v___x_2979_, 0);
lean_ctor_set(v___x_2979_, 1, v___y_3486_);
lean_ctor_set(v___x_2979_, 0, v___y_3484_);
v___x_3488_ = v___x_2979_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___y_3484_);
lean_ctor_set(v_reuseFailAlloc_3494_, 1, v___y_3486_);
v___x_3488_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
lean_object* v___f_3489_; lean_object* v___x_3490_; 
v___f_3489_ = lean_alloc_closure((void*)(l_main___lam__3___boxed), 2, 1);
lean_closure_set(v___f_3489_, 0, v___x_3488_);
v___x_3490_ = lean_box(0);
if (v___y_3480_ == 0)
{
lean_object* v___x_3491_; 
lean_inc(v___y_3485_);
lean_inc_ref(v___y_3482_);
v___x_3491_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v___y_3482_, v___y_3481_, v___f_3489_, v___x_3490_, v___y_3485_, v___x_3019_);
v___y_3366_ = v___y_3479_;
v___y_3367_ = v___y_3483_;
v___y_3368_ = v___y_3485_;
v___y_3369_ = v___x_3491_;
goto v___jp_3365_;
}
else
{
lean_object* v___x_3492_; lean_object* v___x_3493_; 
lean_inc_ref_n(v___y_3482_, 2);
v___x_3492_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite___redArg(v___y_3482_, v___y_3481_);
lean_dec_ref(v___y_3481_);
lean_inc(v___y_3485_);
v___x_3493_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v___y_3482_, v___x_3492_, v___f_3489_, v___x_3490_, v___y_3485_, v___x_3019_);
v___y_3366_ = v___y_3479_;
v___y_3367_ = v___y_3483_;
v___y_3368_ = v___y_3485_;
v___y_3369_ = v___x_3493_;
goto v___jp_3365_;
}
}
}
v___jp_3495_:
{
lean_object* v___x_3500_; lean_object* v_toEnvExtension_3501_; lean_object* v_asyncMode_3502_; uint8_t v_logWrites_3503_; lean_object* v___x_3504_; lean_object* v_importedEntries_3505_; lean_object* v_state_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; uint8_t v___x_3509_; 
v___x_3500_ = l_Lean_IR_declMapExt;
v_toEnvExtension_3501_ = lean_ctor_get(v___x_3500_, 0);
v_asyncMode_3502_ = lean_ctor_get(v_toEnvExtension_3501_, 2);
v_logWrites_3503_ = lean_ctor_get_uint8(v_toEnvExtension_3501_, sizeof(void*)*6);
lean_inc(v___y_3498_);
lean_inc_ref(v___y_3499_);
v___x_3504_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2995_, v_toEnvExtension_3501_, v___y_3499_, v_asyncMode_3502_, v___y_3498_, v___x_3006_);
v_importedEntries_3505_ = lean_ctor_get(v___x_3504_, 0);
lean_inc_ref(v_importedEntries_3505_);
v_state_3506_ = lean_ctor_get(v___x_3504_, 1);
lean_inc(v_state_3506_);
lean_dec(v___x_3504_);
v___x_3507_ = lean_array_get_borrowed(v___x_2996_, v_importedEntries_3505_, v___y_3497_);
v___x_3508_ = lean_array_get_size(v___x_3507_);
v___x_3509_ = lean_nat_dec_lt(v___x_3022_, v___x_3508_);
if (v___x_3509_ == 0)
{
v___y_3479_ = v___y_3496_;
v___y_3480_ = v_logWrites_3503_;
v___y_3481_ = v___y_3499_;
v___y_3482_ = v_toEnvExtension_3501_;
v___y_3483_ = v___y_3497_;
v___y_3484_ = v_importedEntries_3505_;
v___y_3485_ = v___y_3498_;
v___y_3486_ = v_state_3506_;
goto v___jp_3478_;
}
else
{
size_t v___x_3510_; size_t v___x_3511_; lean_object* v___x_3512_; 
v___x_3510_ = ((size_t)0ULL);
v___x_3511_ = lean_usize_of_nat(v___x_3508_);
lean_inc_ref(v___y_3499_);
v___x_3512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3499_, v___x_3507_, v___x_3510_, v___x_3511_, v_state_3506_);
v___y_3479_ = v___y_3496_;
v___y_3480_ = v_logWrites_3503_;
v___y_3481_ = v___y_3499_;
v___y_3482_ = v_toEnvExtension_3501_;
v___y_3483_ = v___y_3497_;
v___y_3484_ = v_importedEntries_3505_;
v___y_3485_ = v___y_3498_;
v___y_3486_ = v___x_3512_;
goto v___jp_3478_;
}
}
v___jp_3513_:
{
uint8_t v___x_3520_; 
v___x_3520_ = lean_nat_dec_lt(v___x_3022_, v___y_3515_);
if (v___x_3520_ == 0)
{
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3515_);
v___y_3496_ = v___y_3514_;
v___y_3497_ = v___y_3516_;
v___y_3498_ = v___y_3518_;
v___y_3499_ = v___y_3519_;
goto v___jp_3495_;
}
else
{
size_t v___x_3521_; size_t v___x_3522_; lean_object* v___x_3523_; 
v___x_3521_ = ((size_t)0ULL);
v___x_3522_ = lean_usize_of_nat(v___y_3515_);
lean_dec(v___y_3515_);
v___x_3523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3517_, v___x_3521_, v___x_3522_, v___y_3519_);
lean_dec_ref(v___y_3517_);
v___y_3496_ = v___y_3514_;
v___y_3497_ = v___y_3516_;
v___y_3498_ = v___y_3518_;
v___y_3499_ = v___x_3523_;
goto v___jp_3495_;
}
}
v___jp_3524_:
{
lean_object* v___x_3530_; uint8_t v___x_3531_; 
v___x_3530_ = lean_array_get_size(v___y_3529_);
v___x_3531_ = lean_nat_dec_lt(v___x_3022_, v___x_3530_);
if (v___x_3531_ == 0)
{
v___y_3514_ = v___y_3525_;
v___y_3515_ = v___x_3530_;
v___y_3516_ = v___y_3527_;
v___y_3517_ = v___y_3529_;
v___y_3518_ = v___y_3528_;
v___y_3519_ = v___y_3526_;
goto v___jp_3513_;
}
else
{
size_t v___x_3532_; size_t v___x_3533_; lean_object* v___x_3534_; 
v___x_3532_ = ((size_t)0ULL);
v___x_3533_ = lean_usize_of_nat(v___x_3530_);
v___x_3534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3529_, v___x_3532_, v___x_3533_, v___y_3526_);
v___y_3514_ = v___y_3525_;
v___y_3515_ = v___x_3530_;
v___y_3516_ = v___y_3527_;
v___y_3517_ = v___y_3529_;
v___y_3518_ = v___y_3528_;
v___y_3519_ = v___x_3534_;
goto v___jp_3513_;
}
}
v___jp_3535_:
{
lean_object* v___x_3538_; lean_object* v_ext_3539_; lean_object* v___x_3540_; 
v___x_3538_ = l_Lean_Compiler_CSimp_ext;
v_ext_3539_ = lean_ctor_get(v___x_3538_, 1);
lean_inc_ref(v_ext_3539_);
lean_inc(v___y_3536_);
v___x_3540_ = l_main___elam__0___redArg(v___y_3536_, v___x_3006_, v___x_2990_, v_ext_3539_, v___y_3537_);
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_object* v_a_3541_; lean_object* v___x_3542_; lean_object* v_ext_3543_; lean_object* v___x_3544_; 
v_a_3541_ = lean_ctor_get(v___x_3540_, 0);
lean_inc(v_a_3541_);
lean_dec_ref_known(v___x_3540_, 1);
v___x_3542_ = l_Lean_Meta_instanceExtension;
v_ext_3543_ = lean_ctor_get(v___x_3542_, 1);
lean_inc_ref(v_ext_3543_);
lean_inc(v___y_3536_);
v___x_3544_ = l_main___elam__0___redArg(v___y_3536_, v___x_3006_, v___x_2990_, v_ext_3543_, v_a_3541_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_object* v_a_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
lean_inc(v_a_3545_);
lean_dec_ref_known(v___x_3544_, 1);
v___x_3546_ = l_Lean_classExtension;
lean_inc(v___y_3536_);
v___x_3547_ = l_main___elam__0___redArg(v___y_3536_, v___x_3006_, v___x_2992_, v___x_3546_, v_a_3545_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v_a_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_a_3548_);
lean_dec_ref_known(v___x_3547_, 1);
v___x_3549_ = l_Lean_Meta_Match_Extension_extension;
lean_inc(v___y_3536_);
v___x_3550_ = l_main___elam__0___redArg(v___y_3536_, v___x_3006_, v___x_2993_, v___x_3549_, v_a_3548_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3574_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3553_ = v___x_3550_;
v_isShared_3554_ = v_isSharedCheck_3574_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3550_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3574_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3555_; 
v___x_3555_ = l_Lean_Environment_getModuleIdx_x3f(v_a_3551_, v_name_3001_);
if (lean_obj_tag(v___x_3555_) == 1)
{
lean_object* v_val_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; uint8_t v___x_3561_; 
lean_del_object(v___x_3553_);
v_val_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_val_3556_);
lean_dec_ref_known(v___x_3555_, 1);
v___x_3557_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_3558_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2994_, v___x_3557_, v_a_3551_, v_val_3556_, v___x_3364_);
v___x_3559_ = lean_array_get_size(v___x_3558_);
v___x_3560_ = ((lean_object*)(l_main___closed__32));
v___x_3561_ = lean_nat_dec_lt(v___x_3022_, v___x_3559_);
if (v___x_3561_ == 0)
{
lean_dec_ref(v___x_3558_);
lean_inc(v___y_3536_);
v___y_3525_ = v___y_3536_;
v___y_3526_ = v_a_3551_;
v___y_3527_ = v_val_3556_;
v___y_3528_ = v___y_3536_;
v___y_3529_ = v___x_3560_;
goto v___jp_3524_;
}
else
{
size_t v___x_3562_; size_t v___x_3563_; lean_object* v___x_3564_; 
v___x_3562_ = ((size_t)0ULL);
v___x_3563_ = lean_usize_of_nat(v___x_3559_);
lean_inc(v_a_3551_);
v___x_3564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_3551_, v___x_3558_, v___x_3562_, v___x_3563_, v___x_3560_);
lean_dec_ref(v___x_3558_);
lean_inc(v___y_3536_);
v___y_3525_ = v___y_3536_;
v___y_3526_ = v_a_3551_;
v___y_3527_ = v_val_3556_;
v___y_3528_ = v___y_3536_;
v___y_3529_ = v___x_3564_;
goto v___jp_3524_;
}
}
else
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3572_; 
lean_dec(v___x_3555_);
lean_dec(v_a_3551_);
lean_dec(v___y_3536_);
lean_dec_ref(v___x_3023_);
lean_del_object(v___x_3016_);
lean_dec(v_fst_3013_);
lean_dec(v_head_2985_);
lean_del_object(v___x_2983_);
lean_dec(v_head_2981_);
lean_del_object(v___x_2979_);
v___x_3565_ = ((lean_object*)(l_main___closed__33));
v___x_3566_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3001_, v___x_3019_);
v___x_3567_ = lean_string_append(v___x_3565_, v___x_3566_);
lean_dec_ref(v___x_3566_);
v___x_3568_ = ((lean_object*)(l_main___closed__34));
v___x_3569_ = lean_string_append(v___x_3567_, v___x_3568_);
v___x_3570_ = lean_mk_io_user_error(v___x_3569_);
if (v_isShared_3554_ == 0)
{
lean_ctor_set_tag(v___x_3553_, 1);
lean_ctor_set(v___x_3553_, 0, v___x_3570_);
v___x_3572_ = v___x_3553_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v___x_3570_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
else
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3582_; 
lean_dec(v___y_3536_);
lean_dec_ref(v___x_3023_);
lean_del_object(v___x_3016_);
lean_dec(v_fst_3013_);
lean_dec(v_name_3001_);
lean_dec(v_head_2985_);
lean_del_object(v___x_2983_);
lean_dec(v_head_2981_);
lean_del_object(v___x_2979_);
v_a_3575_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3577_ = v___x_3550_;
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_3550_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3580_; 
if (v_isShared_3578_ == 0)
{
v___x_3580_ = v___x_3577_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3575_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
}
else
{
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
lean_dec(v___y_3536_);
lean_dec_ref(v___x_3023_);
lean_del_object(v___x_3016_);
lean_dec(v_fst_3013_);
lean_dec(v_name_3001_);
lean_dec(v_head_2985_);
lean_del_object(v___x_2983_);
lean_dec(v_head_2981_);
lean_del_object(v___x_2979_);
v_a_3583_ = lean_ctor_get(v___x_3547_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3585_ = v___x_3547_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3547_);
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
else
{
lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3598_; 
lean_dec(v___y_3536_);
lean_dec_ref(v___x_3023_);
lean_del_object(v___x_3016_);
lean_dec(v_fst_3013_);
lean_dec(v_name_3001_);
lean_dec(v_head_2985_);
lean_del_object(v___x_2983_);
lean_dec(v_head_2981_);
lean_del_object(v___x_2979_);
v_a_3591_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3593_ = v___x_3544_;
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_a_3591_);
lean_dec(v___x_3544_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3596_; 
if (v_isShared_3594_ == 0)
{
v___x_3596_ = v___x_3593_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_a_3591_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
}
else
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3606_; 
lean_dec(v___y_3536_);
lean_dec_ref(v___x_3023_);
lean_del_object(v___x_3016_);
lean_dec(v_fst_3013_);
lean_dec(v_name_3001_);
lean_dec(v_head_2985_);
lean_del_object(v___x_2983_);
lean_dec(v_head_2981_);
lean_del_object(v___x_2979_);
v_a_3599_ = lean_ctor_get(v___x_3540_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3540_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3601_ = v___x_3540_;
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v___x_3540_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3604_; 
if (v_isShared_3602_ == 0)
{
v___x_3604_ = v___x_3601_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3599_);
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
v___jp_3607_:
{
lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___f_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; 
v___x_3609_ = l_Lean_instInhabitedImportState_default;
v___x_3610_ = lean_box(v___x_3364_);
v___x_3611_ = lean_box(v___y_3608_);
v___x_3612_ = lean_box(v___x_3019_);
v___x_3613_ = lean_box(v___x_3006_);
lean_inc_ref(v___x_3023_);
lean_inc(v_name_3001_);
v___f_3614_ = lean_alloc_closure((void*)(l_main___lam__1___boxed), 10, 9);
lean_closure_set(v___f_3614_, 0, v___x_3609_);
lean_closure_set(v___f_3614_, 1, v___x_3363_);
lean_closure_set(v___f_3614_, 2, v___x_3610_);
lean_closure_set(v___f_3614_, 3, v_importArts_3003_);
lean_closure_set(v___f_3614_, 4, v___x_3611_);
lean_closure_set(v___f_3614_, 5, v___x_3612_);
lean_closure_set(v___f_3614_, 6, v_name_3001_);
lean_closure_set(v___f_3614_, 7, v___x_3023_);
lean_closure_set(v___f_3614_, 8, v___x_3613_);
v___x_3615_ = lean_alloc_closure((void*)(l_Lean_withImporting___boxed), 3, 2);
lean_closure_set(v___x_3615_, 0, lean_box(0));
lean_closure_set(v___x_3615_, 1, v___f_3614_);
v___x_3616_ = lean_box(0);
v___x_3617_ = l_Lean_profileitIOUnsafe___redArg(v___x_3359_, v___x_3023_, v___x_3615_, v___x_3616_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v_a_3618_; lean_object* v___x_3619_; lean_object* v_toEnvExtension_3620_; lean_object* v_asyncMode_3621_; uint8_t v_logWrites_3622_; lean_object* v___x_3623_; 
v_a_3618_ = lean_ctor_get(v___x_3617_, 0);
lean_inc(v_a_3618_);
lean_dec_ref_known(v___x_3617_, 1);
v___x_3619_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_3620_ = lean_ctor_get(v___x_3619_, 0);
v_asyncMode_3621_ = lean_ctor_get(v_toEnvExtension_3620_, 2);
v_logWrites_3622_ = lean_ctor_get_uint8(v_toEnvExtension_3620_, sizeof(void*)*6);
lean_inc(v_name_3001_);
v___x_3623_ = l_Lean_Environment_setMainModule(v_a_3618_, v_name_3001_);
if (v_logWrites_3622_ == 0)
{
lean_object* v___x_3624_; 
lean_inc_ref(v_toEnvExtension_3620_);
v___x_3624_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_3620_, v___x_3623_, v___f_3005_, v_asyncMode_3621_, v___x_3616_, v___x_3019_);
v___y_3536_ = v___x_3616_;
v___y_3537_ = v___x_3624_;
goto v___jp_3535_;
}
else
{
lean_object* v___x_3625_; lean_object* v___x_3626_; 
lean_inc_ref_n(v_toEnvExtension_3620_, 2);
v___x_3625_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite___redArg(v_toEnvExtension_3620_, v___x_3623_);
lean_dec_ref(v___x_3623_);
v___x_3626_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_3620_, v___x_3625_, v___f_3005_, v_asyncMode_3621_, v___x_3616_, v___x_3019_);
v___y_3536_ = v___x_3616_;
v___y_3537_ = v___x_3626_;
goto v___jp_3535_;
}
}
else
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3634_; 
lean_dec_ref(v___x_3023_);
lean_del_object(v___x_3016_);
lean_dec(v_fst_3013_);
lean_dec_ref(v___f_3005_);
lean_dec(v_name_3001_);
lean_dec(v_head_2985_);
lean_del_object(v___x_2983_);
lean_dec(v_head_2981_);
lean_del_object(v___x_2979_);
v_a_3627_ = lean_ctor_get(v___x_3617_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3629_ = v___x_3617_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3617_);
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
lean_dec_ref(v___x_3023_);
lean_del_object(v___x_3016_);
lean_dec(v_fst_3013_);
lean_dec_ref(v___f_3005_);
lean_dec(v_importArts_3003_);
lean_dec(v_name_3001_);
lean_dec(v_head_2985_);
lean_del_object(v___x_2983_);
lean_dec(v_head_2981_);
lean_del_object(v___x_2979_);
v_a_3636_ = lean_ctor_get(v___x_3358_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3638_ = v___x_3358_;
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_a_3636_);
lean_dec(v___x_3358_);
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
v___jp_3024_:
{
lean_object* v___x_3047_; lean_object* v_messages_3048_; lean_object* v_env_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3175_; 
v___x_3047_ = lean_st_ref_get(v___y_3042_);
lean_dec(v___y_3042_);
v_messages_3048_ = lean_ctor_get(v___x_3047_, 7);
v_env_3049_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3175_ == 0)
{
lean_object* v_unused_3176_; lean_object* v_unused_3177_; lean_object* v_unused_3178_; lean_object* v_unused_3179_; lean_object* v_unused_3180_; lean_object* v_unused_3181_; lean_object* v_unused_3182_; lean_object* v_unused_3183_; 
v_unused_3176_ = lean_ctor_get(v___x_3047_, 9);
lean_dec(v_unused_3176_);
v_unused_3177_ = lean_ctor_get(v___x_3047_, 8);
lean_dec(v_unused_3177_);
v_unused_3178_ = lean_ctor_get(v___x_3047_, 6);
lean_dec(v_unused_3178_);
v_unused_3179_ = lean_ctor_get(v___x_3047_, 5);
lean_dec(v_unused_3179_);
v_unused_3180_ = lean_ctor_get(v___x_3047_, 4);
lean_dec(v_unused_3180_);
v_unused_3181_ = lean_ctor_get(v___x_3047_, 3);
lean_dec(v_unused_3181_);
v_unused_3182_ = lean_ctor_get(v___x_3047_, 2);
lean_dec(v_unused_3182_);
v_unused_3183_ = lean_ctor_get(v___x_3047_, 1);
lean_dec(v_unused_3183_);
v___x_3051_ = v___x_3047_;
v_isShared_3052_ = v_isSharedCheck_3175_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_messages_3048_);
lean_inc(v_env_3049_);
lean_dec(v___x_3047_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3175_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v_unreported_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v_unreported_3053_ = lean_ctor_get(v_messages_3048_, 1);
v___x_3054_ = lean_box(0);
v___x_3055_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_unreported_3053_, v___x_3054_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3165_; 
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3165_ == 0)
{
lean_object* v_unused_3166_; 
v_unused_3166_ = lean_ctor_get(v___x_3055_, 0);
lean_dec(v_unused_3166_);
v___x_3057_ = v___x_3055_;
v_isShared_3058_ = v_isSharedCheck_3165_;
goto v_resetjp_3056_;
}
else
{
lean_dec(v___x_3055_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3165_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
uint8_t v___x_3059_; 
v___x_3059_ = l_Lean_MessageLog_hasErrors(v_messages_3048_);
lean_dec_ref(v_messages_3048_);
if (v___x_3059_ == 0)
{
lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
lean_del_object(v___x_3057_);
v___x_3060_ = ((lean_object*)(l_main___closed__9));
lean_inc(v_head_2981_);
v___x_3061_ = l_System_FilePath_addExtension(v_head_2981_, v___x_3060_);
lean_inc_ref(v_env_3049_);
v___x_3062_ = l___private_LeanIR_0__mkIRSigData(v_env_3049_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_object* v_a_3063_; lean_object* v___x_3064_; 
v_a_3063_ = lean_ctor_get(v___x_3062_, 0);
lean_inc(v_a_3063_);
lean_dec_ref_known(v___x_3062_, 1);
lean_inc_ref(v_env_3049_);
v___x_3064_ = l___private_LeanIR_0__mkIRData(v_env_3049_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_object* v_a_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3070_; 
v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
lean_inc(v_a_3065_);
lean_dec_ref_known(v___x_3064_, 1);
v___x_3066_ = l_Lean_Environment_mainModule(v_env_3049_);
v___x_3067_ = ((lean_object*)(l_main___closed__11));
v___x_3068_ = l_Lean_Name_append(v___x_3066_, v___x_3067_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 1, v_a_3063_);
lean_ctor_set(v___x_3016_, 0, v___x_3061_);
v___x_3070_ = v___x_3016_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3061_);
lean_ctor_set(v_reuseFailAlloc_3144_, 1, v_a_3063_);
v___x_3070_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
lean_object* v___x_3072_; 
lean_inc(v_head_2981_);
if (v_isShared_2984_ == 0)
{
lean_ctor_set_tag(v___x_2983_, 0);
lean_ctor_set(v___x_2983_, 1, v_a_3065_);
v___x_3072_ = v___x_2983_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_head_2981_);
lean_ctor_set(v_reuseFailAlloc_3143_, 1, v_a_3065_);
v___x_3072_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3073_ = lean_unsigned_to_nat(2u);
v___x_3074_ = lean_mk_empty_array_with_capacity(v___x_3073_);
v___x_3075_ = lean_array_push(v___x_3074_, v___x_3070_);
v___x_3076_ = lean_array_push(v___x_3075_, v___x_3072_);
v___x_3077_ = l_Lean_saveModuleDataParts(v___x_3068_, v___x_3076_);
lean_dec(v___x_3068_);
if (lean_obj_tag(v___x_3077_) == 0)
{
uint8_t v___x_3078_; lean_object* v___x_3079_; 
lean_dec_ref_known(v___x_3077_, 1);
v___x_3078_ = 1;
v___x_3079_ = lean_io_prim_handle_mk(v_head_2985_, v___x_3078_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v_a_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; uint16_t v___x_3083_; lean_object* v___x_3085_; 
lean_dec(v_head_2985_);
v_a_3080_ = lean_ctor_get(v___x_3079_, 0);
lean_inc(v_a_3080_);
lean_dec_ref_known(v___x_3079_, 1);
v___x_3081_ = ((lean_object*)(l_main___closed__12));
v___x_3082_ = l_Lean_Core_getMaxHeartbeats(v___y_3041_);
v___x_3083_ = l_Lean_OptionFlags_ofOptions(v___y_3041_);
lean_inc_ref(v___y_3045_);
lean_inc_ref(v___y_3038_);
lean_inc_ref(v___y_3044_);
lean_inc_ref(v___y_3036_);
lean_inc_ref(v___y_3037_);
lean_inc_ref(v___y_3040_);
lean_inc_ref(v___y_3035_);
lean_inc(v___y_3043_);
lean_inc_ref(v_env_3049_);
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 9, v___y_3045_);
lean_ctor_set(v___x_3051_, 8, v___y_3038_);
lean_ctor_set(v___x_3051_, 7, v___y_3044_);
lean_ctor_set(v___x_3051_, 6, v___y_3036_);
lean_ctor_set(v___x_3051_, 5, v___y_3037_);
lean_ctor_set(v___x_3051_, 4, v___y_3040_);
lean_ctor_set(v___x_3051_, 3, v___y_3039_);
lean_ctor_set(v___x_3051_, 2, v___y_3035_);
lean_ctor_set(v___x_3051_, 1, v___y_3043_);
v___x_3085_ = v___x_3051_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_env_3049_);
lean_ctor_set(v_reuseFailAlloc_3112_, 1, v___y_3043_);
lean_ctor_set(v_reuseFailAlloc_3112_, 2, v___y_3035_);
lean_ctor_set(v_reuseFailAlloc_3112_, 3, v___y_3039_);
lean_ctor_set(v_reuseFailAlloc_3112_, 4, v___y_3040_);
lean_ctor_set(v_reuseFailAlloc_3112_, 5, v___y_3037_);
lean_ctor_set(v_reuseFailAlloc_3112_, 6, v___y_3036_);
lean_ctor_set(v_reuseFailAlloc_3112_, 7, v___y_3044_);
lean_ctor_set(v_reuseFailAlloc_3112_, 8, v___y_3038_);
lean_ctor_set(v_reuseFailAlloc_3112_, 9, v___y_3045_);
v___x_3085_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___f_3091_; lean_object* v___x_3092_; 
v___x_3086_ = lean_box(v___x_3083_);
v___x_3087_ = lean_box(v___y_3030_);
v___x_3088_ = lean_box(v___x_3006_);
v___x_3089_ = lean_box(v___y_3026_);
v___x_3090_ = lean_box(v___x_3059_);
lean_inc_ref(v___y_3029_);
lean_inc_ref(v___y_3031_);
v___f_3091_ = lean_alloc_closure((void*)(l_main___lam__2___boxed), 20, 19);
lean_closure_set(v___f_3091_, 0, v___x_3085_);
lean_closure_set(v___f_3091_, 1, v___y_3031_);
lean_closure_set(v___f_3091_, 2, v___x_3086_);
lean_closure_set(v___f_3091_, 3, v_name_3001_);
lean_closure_set(v___f_3091_, 4, v_a_3080_);
lean_closure_set(v___f_3091_, 5, v___x_3087_);
lean_closure_set(v___f_3091_, 6, v___y_3029_);
lean_closure_set(v___f_3091_, 7, v_head_2981_);
lean_closure_set(v___f_3091_, 8, v___y_3032_);
lean_closure_set(v___f_3091_, 9, v___y_3034_);
lean_closure_set(v___f_3091_, 10, v___y_3025_);
lean_closure_set(v___f_3091_, 11, v___x_3082_);
lean_closure_set(v___f_3091_, 12, v___y_3033_);
lean_closure_set(v___f_3091_, 13, v___y_3028_);
lean_closure_set(v___f_3091_, 14, v___x_3022_);
lean_closure_set(v___f_3091_, 15, v___y_3027_);
lean_closure_set(v___f_3091_, 16, v___x_3088_);
lean_closure_set(v___f_3091_, 17, v___x_3089_);
lean_closure_set(v___f_3091_, 18, v___x_3090_);
v___x_3092_ = l_Lean_profileitIOUnsafe___redArg(v___x_3081_, v___x_3023_, v___f_3091_, v___y_3046_);
lean_dec_ref(v___x_3023_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_object* v___x_3093_; uint8_t v___x_3094_; 
lean_dec_ref_known(v___x_3092_, 1);
v___x_3093_ = lean_display_cumulative_profiling_times();
v___x_3094_ = lean_unbox(v_fst_3013_);
lean_dec(v_fst_3013_);
if (v___x_3094_ == 0)
{
lean_dec_ref(v_env_3049_);
goto v___jp_2972_;
}
else
{
lean_object* v___x_3095_; 
v___x_3095_ = l_Lean_Environment_displayStats(v_env_3049_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_dec_ref_known(v___x_3095_, 1);
goto v___jp_2972_;
}
else
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_3095_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3095_);
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
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_dec_ref(v_env_3049_);
lean_dec(v_fst_3013_);
v_a_3104_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3092_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3092_);
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
}
else
{
lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
lean_dec_ref_known(v___x_3079_, 1);
lean_del_object(v___x_3051_);
lean_dec_ref(v_env_3049_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec(v___y_3025_);
lean_dec_ref(v___x_3023_);
lean_dec(v_fst_3013_);
lean_dec(v_name_3001_);
lean_dec(v_head_2981_);
v___x_3113_ = ((lean_object*)(l_main___closed__13));
v___x_3114_ = lean_string_append(v___x_3113_, v_head_2985_);
lean_dec(v_head_2985_);
v___x_3115_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__1));
v___x_3116_ = lean_string_append(v___x_3114_, v___x_3115_);
v___x_3117_ = l_IO_eprintln___at___00main_spec__6(v___x_3116_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3125_; 
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3125_ == 0)
{
lean_object* v_unused_3126_; 
v_unused_3126_ = lean_ctor_get(v___x_3117_, 0);
lean_dec(v_unused_3126_);
v___x_3119_ = v___x_3117_;
v_isShared_3120_ = v_isSharedCheck_3125_;
goto v_resetjp_3118_;
}
else
{
lean_dec(v___x_3117_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3125_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3121_; lean_object* v___x_3123_; 
v___x_3121_ = l_main___boxed__const__1;
if (v_isShared_3120_ == 0)
{
lean_ctor_set(v___x_3119_, 0, v___x_3121_);
v___x_3123_ = v___x_3119_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3121_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
else
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
v_a_3127_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v___x_3117_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3117_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3132_; 
if (v_isShared_3130_ == 0)
{
v___x_3132_ = v___x_3129_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
}
}
else
{
lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3142_; 
lean_del_object(v___x_3051_);
lean_dec_ref(v_env_3049_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec(v___y_3025_);
lean_dec_ref(v___x_3023_);
lean_dec(v_fst_3013_);
lean_dec(v_name_3001_);
lean_dec(v_head_2985_);
lean_dec(v_head_2981_);
v_a_3135_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3137_ = v___x_3077_;
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_a_3135_);
lean_dec(v___x_3077_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3140_; 
if (v_isShared_3138_ == 0)
{
v___x_3140_ = v___x_3137_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_3135_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
}
}
}
else
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
lean_dec(v_a_3063_);
lean_dec_ref(v___x_3061_);
lean_del_object(v___x_3051_);
lean_dec_ref(v_env_3049_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec(v___y_3025_);
lean_dec_ref(v___x_3023_);
lean_del_object(v___x_3016_);
lean_dec(v_fst_3013_);
lean_dec(v_name_3001_);
lean_dec(v_head_2985_);
lean_del_object(v___x_2983_);
lean_dec(v_head_2981_);
v_a_3145_ = lean_ctor_get(v___x_3064_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v___x_3064_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3064_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3145_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
}
else
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
lean_dec_ref(v___x_3061_);
lean_del_object(v___x_3051_);
lean_dec_ref(v_env_3049_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec(v___y_3025_);
lean_dec_ref(v___x_3023_);
lean_del_object(v___x_3016_);
lean_dec(v_fst_3013_);
lean_dec(v_name_3001_);
lean_dec(v_head_2985_);
lean_del_object(v___x_2983_);
lean_dec(v_head_2981_);
v_a_3153_ = lean_ctor_get(v___x_3062_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3155_ = v___x_3062_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3062_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3153_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
}
else
{
lean_object* v___x_3161_; lean_object* v___x_3163_; 
lean_del_object(v___x_3051_);
lean_dec_ref(v_env_3049_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec(v___y_3025_);
lean_dec_ref(v___x_3023_);
lean_del_object(v___x_3016_);
lean_dec(v_fst_3013_);
lean_dec(v_name_3001_);
lean_dec(v_head_2985_);
lean_del_object(v___x_2983_);
lean_dec(v_head_2981_);
v___x_3161_ = l_main___boxed__const__1;
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 0, v___x_3161_);
v___x_3163_ = v___x_3057_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v___x_3161_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
}
}
else
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3174_; 
lean_del_object(v___x_3051_);
lean_dec_ref(v_env_3049_);
lean_dec_ref(v_messages_3048_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec(v___y_3025_);
lean_dec_ref(v___x_3023_);
lean_del_object(v___x_3016_);
lean_dec(v_fst_3013_);
lean_dec(v_name_3001_);
lean_dec(v_head_2985_);
lean_del_object(v___x_2983_);
lean_dec(v_head_2981_);
v_a_3167_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3169_ = v___x_3055_;
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_3055_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3172_; 
if (v_isShared_3170_ == 0)
{
v___x_3172_ = v___x_3169_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_a_3167_);
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
}
v___jp_3184_:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; size_t v_sz_3222_; size_t v___x_3223_; lean_object* v___x_3224_; 
lean_inc_ref(v___y_3203_);
v___x_3219_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3219_, 0, v___y_3218_);
lean_ctor_set(v___x_3219_, 1, v_nextMacroScope_3207_);
lean_ctor_set(v___x_3219_, 2, v_ngen_3208_);
lean_ctor_set(v___x_3219_, 3, v_auxDeclNGen_3209_);
lean_ctor_set(v___x_3219_, 4, v_traceState_3210_);
lean_ctor_set(v___x_3219_, 5, v___y_3203_);
lean_ctor_set(v___x_3219_, 6, v_recordedDeps_3211_);
lean_ctor_set(v___x_3219_, 7, v_messages_3212_);
lean_ctor_set(v___x_3219_, 8, v_infoState_3213_);
lean_ctor_set(v___x_3219_, 9, v_snapshotTasks_3214_);
v___x_3220_ = lean_st_ref_put(v___y_3196_, v___x_3219_);
v___x_3221_ = lean_box(0);
v_sz_3222_ = lean_array_size(v___y_3202_);
v___x_3223_ = ((size_t)0ULL);
v___x_3224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(v___y_3202_, v_sz_3222_, v___x_3223_, v___x_3221_, v___y_3215_, v___y_3196_);
lean_dec_ref(v___y_3202_);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_dec_ref_known(v___x_3224_, 1);
lean_dec_ref(v___y_3215_);
lean_dec(v___y_3196_);
v___y_3025_ = v___y_3185_;
v___y_3026_ = v___y_3188_;
v___y_3027_ = v___y_3187_;
v___y_3028_ = v___y_3186_;
v___y_3029_ = v___y_3189_;
v___y_3030_ = v___y_3190_;
v___y_3031_ = v___y_3191_;
v___y_3032_ = v___y_3192_;
v___y_3033_ = v___y_3193_;
v___y_3034_ = v___y_3194_;
v___y_3035_ = v___y_3201_;
v___y_3036_ = v___y_3195_;
v___y_3037_ = v___y_3203_;
v___y_3038_ = v___y_3204_;
v___y_3039_ = v___y_3197_;
v___y_3040_ = v___y_3198_;
v___y_3041_ = v___y_3205_;
v___y_3042_ = v___y_3206_;
v___y_3043_ = v___y_3199_;
v___y_3044_ = v___y_3200_;
v___y_3045_ = v___y_3216_;
v___y_3046_ = v___y_3217_;
goto v___jp_3024_;
}
else
{
lean_object* v_a_3225_; uint8_t v___x_3226_; 
v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc(v_a_3225_);
lean_dec_ref_known(v___x_3224_, 1);
v___x_3226_ = l_Lean_Exception_isInterrupt(v_a_3225_);
if (v___x_3226_ == 0)
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3227_ = l_Lean_Exception_toMessageData(v_a_3225_);
v___x_3228_ = l_Lean_logError___at___00main_spec__13(v___x_3227_, v___y_3215_, v___y_3196_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3215_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_dec_ref_known(v___x_3228_, 1);
v___y_3025_ = v___y_3185_;
v___y_3026_ = v___y_3188_;
v___y_3027_ = v___y_3187_;
v___y_3028_ = v___y_3186_;
v___y_3029_ = v___y_3189_;
v___y_3030_ = v___y_3190_;
v___y_3031_ = v___y_3191_;
v___y_3032_ = v___y_3192_;
v___y_3033_ = v___y_3193_;
v___y_3034_ = v___y_3194_;
v___y_3035_ = v___y_3201_;
v___y_3036_ = v___y_3195_;
v___y_3037_ = v___y_3203_;
v___y_3038_ = v___y_3204_;
v___y_3039_ = v___y_3197_;
v___y_3040_ = v___y_3198_;
v___y_3041_ = v___y_3205_;
v___y_3042_ = v___y_3206_;
v___y_3043_ = v___y_3199_;
v___y_3044_ = v___y_3200_;
v___y_3045_ = v___y_3216_;
v___y_3046_ = v___y_3217_;
goto v___jp_3024_;
}
else
{
lean_object* v___x_3229_; lean_object* v___x_3230_; 
lean_dec_ref_known(v___x_3228_, 1);
lean_dec(v___y_3217_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3187_);
lean_dec(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___x_3023_);
lean_del_object(v___x_3016_);
lean_dec(v_fst_3013_);
lean_dec(v_name_3001_);
lean_dec(v_head_2985_);
lean_del_object(v___x_2983_);
lean_dec(v_head_2981_);
v___x_3229_ = lean_obj_once(&l_main___closed__17, &l_main___closed__17_once, _init_l_main___closed__17);
v___x_3230_ = l_panic___at___00main_spec__5(v___x_3229_);
return v___x_3230_;
}
}
else
{
lean_dec(v_a_3225_);
lean_dec_ref(v___y_3215_);
lean_dec(v___y_3196_);
v___y_3025_ = v___y_3185_;
v___y_3026_ = v___y_3188_;
v___y_3027_ = v___y_3187_;
v___y_3028_ = v___y_3186_;
v___y_3029_ = v___y_3189_;
v___y_3030_ = v___y_3190_;
v___y_3031_ = v___y_3191_;
v___y_3032_ = v___y_3192_;
v___y_3033_ = v___y_3193_;
v___y_3034_ = v___y_3194_;
v___y_3035_ = v___y_3201_;
v___y_3036_ = v___y_3195_;
v___y_3037_ = v___y_3203_;
v___y_3038_ = v___y_3204_;
v___y_3039_ = v___y_3197_;
v___y_3040_ = v___y_3198_;
v___y_3041_ = v___y_3205_;
v___y_3042_ = v___y_3206_;
v___y_3043_ = v___y_3199_;
v___y_3044_ = v___y_3200_;
v___y_3045_ = v___y_3216_;
v___y_3046_ = v___y_3217_;
goto v___jp_3024_;
}
}
}
v___jp_3231_:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v_env_3278_; lean_object* v_nextMacroScope_3279_; lean_object* v_ngen_3280_; lean_object* v_auxDeclNGen_3281_; lean_object* v_traceState_3282_; lean_object* v_recordedDeps_3283_; lean_object* v_messages_3284_; lean_object* v_infoState_3285_; lean_object* v_snapshotTasks_3286_; lean_object* v___x_3287_; uint8_t v___x_3288_; 
v___x_3273_ = l_Lean_maxRecDepth;
v___x_3274_ = l_Lean_Option_get___at___00main_spec__8(v___x_3023_, v___x_3273_);
lean_inc_ref(v___x_3023_);
v___x_3275_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3275_, 0, v_fileName_3257_);
lean_ctor_set(v___x_3275_, 1, v_fileMap_3258_);
lean_ctor_set(v___x_3275_, 2, v___x_3023_);
lean_ctor_set(v___x_3275_, 3, v___x_3274_);
lean_ctor_set(v___x_3275_, 4, v_currNamespace_3259_);
lean_ctor_set(v___x_3275_, 5, v_openDecls_3260_);
lean_ctor_set(v___x_3275_, 6, v_initHeartbeats_3261_);
lean_ctor_set(v___x_3275_, 7, v_maxHeartbeats_3262_);
lean_ctor_set(v___x_3275_, 8, v_quotContext_3263_);
lean_ctor_set(v___x_3275_, 9, v_currMacroScope_3264_);
lean_ctor_set(v___x_3275_, 10, v_cancelTk_x3f_3265_);
lean_ctor_set(v___x_3275_, 11, v_inheritedTraceOptions_3266_);
v___x_3276_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3276_, 0, v___x_3275_);
lean_ctor_set(v___x_3276_, 1, v_currRecDepth_3267_);
lean_ctor_set(v___x_3276_, 2, v_ref_3268_);
lean_ctor_set_uint16(v___x_3276_, sizeof(void*)*3, v___y_3254_);
lean_ctor_set_uint8(v___x_3276_, sizeof(void*)*3 + 2, v_suppressElabErrors_3269_);
lean_ctor_set_uint8(v___x_3276_, sizeof(void*)*3 + 3, v_checkDeprecated_3270_);
lean_ctor_set_uint8(v___x_3276_, sizeof(void*)*3 + 4, v_isRecordingDeps_3271_);
v___x_3277_ = lean_st_ref_take(v___y_3272_);
v_env_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc_ref(v_env_3278_);
v_nextMacroScope_3279_ = lean_ctor_get(v___x_3277_, 1);
lean_inc(v_nextMacroScope_3279_);
v_ngen_3280_ = lean_ctor_get(v___x_3277_, 2);
lean_inc_ref(v_ngen_3280_);
v_auxDeclNGen_3281_ = lean_ctor_get(v___x_3277_, 3);
lean_inc_ref(v_auxDeclNGen_3281_);
v_traceState_3282_ = lean_ctor_get(v___x_3277_, 4);
lean_inc_ref(v_traceState_3282_);
v_recordedDeps_3283_ = lean_ctor_get(v___x_3277_, 6);
lean_inc_ref(v_recordedDeps_3283_);
v_messages_3284_ = lean_ctor_get(v___x_3277_, 7);
lean_inc_ref(v_messages_3284_);
v_infoState_3285_ = lean_ctor_get(v___x_3277_, 8);
lean_inc_ref(v_infoState_3285_);
v_snapshotTasks_3286_ = lean_ctor_get(v___x_3277_, 9);
lean_inc_ref(v_snapshotTasks_3286_);
lean_dec(v___x_3277_);
v___x_3287_ = lean_array_get_size(v___y_3248_);
v___x_3288_ = lean_nat_dec_lt(v___x_3022_, v___x_3287_);
if (v___x_3288_ == 0)
{
lean_object* v___x_3289_; 
lean_inc_ref(v___y_3251_);
v___x_3289_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3251_, v_env_3278_, v___x_2997_);
v___y_3185_ = v___y_3232_;
v___y_3186_ = v___y_3235_;
v___y_3187_ = v___y_3234_;
v___y_3188_ = v___y_3233_;
v___y_3189_ = v___y_3236_;
v___y_3190_ = v___y_3237_;
v___y_3191_ = v___y_3238_;
v___y_3192_ = v___y_3239_;
v___y_3193_ = v___y_3240_;
v___y_3194_ = v___y_3241_;
v___y_3195_ = v___y_3242_;
v___y_3196_ = v___y_3272_;
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
v_nextMacroScope_3207_ = v_nextMacroScope_3279_;
v_ngen_3208_ = v_ngen_3280_;
v_auxDeclNGen_3209_ = v_auxDeclNGen_3281_;
v_traceState_3210_ = v_traceState_3282_;
v_recordedDeps_3211_ = v_recordedDeps_3283_;
v_messages_3212_ = v_messages_3284_;
v_infoState_3213_ = v_infoState_3285_;
v_snapshotTasks_3214_ = v_snapshotTasks_3286_;
v___y_3215_ = v___x_3276_;
v___y_3216_ = v___y_3255_;
v___y_3217_ = v___y_3256_;
v___y_3218_ = v___x_3289_;
goto v___jp_3184_;
}
else
{
size_t v___x_3290_; size_t v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3290_ = ((size_t)0ULL);
v___x_3291_ = lean_usize_of_nat(v___x_3287_);
v___x_3292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v___y_3248_, v___x_3290_, v___x_3291_, v___x_2997_);
lean_inc_ref(v___y_3251_);
v___x_3293_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3251_, v_env_3278_, v___x_3292_);
v___y_3185_ = v___y_3232_;
v___y_3186_ = v___y_3235_;
v___y_3187_ = v___y_3234_;
v___y_3188_ = v___y_3233_;
v___y_3189_ = v___y_3236_;
v___y_3190_ = v___y_3237_;
v___y_3191_ = v___y_3238_;
v___y_3192_ = v___y_3239_;
v___y_3193_ = v___y_3240_;
v___y_3194_ = v___y_3241_;
v___y_3195_ = v___y_3242_;
v___y_3196_ = v___y_3272_;
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
v_nextMacroScope_3207_ = v_nextMacroScope_3279_;
v_ngen_3208_ = v_ngen_3280_;
v_auxDeclNGen_3209_ = v_auxDeclNGen_3281_;
v_traceState_3210_ = v_traceState_3282_;
v_recordedDeps_3211_ = v_recordedDeps_3283_;
v_messages_3212_ = v_messages_3284_;
v_infoState_3213_ = v_infoState_3285_;
v_snapshotTasks_3214_ = v_snapshotTasks_3286_;
v___y_3215_ = v___x_3276_;
v___y_3216_ = v___y_3255_;
v___y_3217_ = v___y_3256_;
v___y_3218_ = v___x_3293_;
goto v___jp_3184_;
}
}
v___jp_3294_:
{
lean_object* v___x_3322_; lean_object* v_env_3323_; lean_object* v_nextMacroScope_3324_; lean_object* v_ngen_3325_; lean_object* v_auxDeclNGen_3326_; lean_object* v_traceState_3327_; lean_object* v_recordedDeps_3328_; lean_object* v_messages_3329_; lean_object* v_infoState_3330_; lean_object* v_snapshotTasks_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3356_; 
v___x_3322_ = lean_st_ref_take(v___y_3318_);
v_env_3323_ = lean_ctor_get(v___x_3322_, 0);
v_nextMacroScope_3324_ = lean_ctor_get(v___x_3322_, 1);
v_ngen_3325_ = lean_ctor_get(v___x_3322_, 2);
v_auxDeclNGen_3326_ = lean_ctor_get(v___x_3322_, 3);
v_traceState_3327_ = lean_ctor_get(v___x_3322_, 4);
v_recordedDeps_3328_ = lean_ctor_get(v___x_3322_, 6);
v_messages_3329_ = lean_ctor_get(v___x_3322_, 7);
v_infoState_3330_ = lean_ctor_get(v___x_3322_, 8);
v_snapshotTasks_3331_ = lean_ctor_get(v___x_3322_, 9);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3356_ == 0)
{
lean_object* v_unused_3357_; 
v_unused_3357_ = lean_ctor_get(v___x_3322_, 5);
lean_dec(v_unused_3357_);
v___x_3333_ = v___x_3322_;
v_isShared_3334_ = v_isSharedCheck_3356_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_snapshotTasks_3331_);
lean_inc(v_infoState_3330_);
lean_inc(v_messages_3329_);
lean_inc(v_recordedDeps_3328_);
lean_inc(v_traceState_3327_);
lean_inc(v_auxDeclNGen_3326_);
lean_inc(v_ngen_3325_);
lean_inc(v_nextMacroScope_3324_);
lean_inc(v_env_3323_);
lean_dec(v___x_3322_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3356_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3335_; lean_object* v___x_3337_; 
v___x_3335_ = l_Lean_Kernel_enableDiag(v_env_3323_, v___y_3314_);
lean_inc_ref(v___y_3313_);
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 5, v___y_3313_);
lean_ctor_set(v___x_3333_, 0, v___x_3335_);
v___x_3337_ = v___x_3333_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v___x_3335_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v_nextMacroScope_3324_);
lean_ctor_set(v_reuseFailAlloc_3355_, 2, v_ngen_3325_);
lean_ctor_set(v_reuseFailAlloc_3355_, 3, v_auxDeclNGen_3326_);
lean_ctor_set(v_reuseFailAlloc_3355_, 4, v_traceState_3327_);
lean_ctor_set(v_reuseFailAlloc_3355_, 5, v___y_3313_);
lean_ctor_set(v_reuseFailAlloc_3355_, 6, v_recordedDeps_3328_);
lean_ctor_set(v_reuseFailAlloc_3355_, 7, v_messages_3329_);
lean_ctor_set(v_reuseFailAlloc_3355_, 8, v_infoState_3330_);
lean_ctor_set(v_reuseFailAlloc_3355_, 9, v_snapshotTasks_3331_);
v___x_3337_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
lean_object* v___x_3338_; lean_object* v_toCold_3339_; lean_object* v_currRecDepth_3340_; lean_object* v_ref_3341_; uint8_t v_suppressElabErrors_3342_; uint8_t v_checkDeprecated_3343_; uint8_t v_isRecordingDeps_3344_; lean_object* v_fileName_3345_; lean_object* v_fileMap_3346_; lean_object* v_currNamespace_3347_; lean_object* v_openDecls_3348_; lean_object* v_initHeartbeats_3349_; lean_object* v_maxHeartbeats_3350_; lean_object* v_quotContext_3351_; lean_object* v_currMacroScope_3352_; lean_object* v_cancelTk_x3f_3353_; lean_object* v_inheritedTraceOptions_3354_; 
v___x_3338_ = lean_st_ref_put(v___y_3318_, v___x_3337_);
v_toCold_3339_ = lean_ctor_get(v___y_3310_, 0);
lean_inc_ref(v_toCold_3339_);
v_currRecDepth_3340_ = lean_ctor_get(v___y_3310_, 1);
lean_inc(v_currRecDepth_3340_);
v_ref_3341_ = lean_ctor_get(v___y_3310_, 2);
lean_inc(v_ref_3341_);
v_suppressElabErrors_3342_ = lean_ctor_get_uint8(v___y_3310_, sizeof(void*)*3 + 2);
v_checkDeprecated_3343_ = lean_ctor_get_uint8(v___y_3310_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3344_ = lean_ctor_get_uint8(v___y_3310_, sizeof(void*)*3 + 4);
lean_dec_ref(v___y_3310_);
v_fileName_3345_ = lean_ctor_get(v_toCold_3339_, 0);
lean_inc_ref(v_fileName_3345_);
v_fileMap_3346_ = lean_ctor_get(v_toCold_3339_, 1);
lean_inc_ref(v_fileMap_3346_);
v_currNamespace_3347_ = lean_ctor_get(v_toCold_3339_, 4);
lean_inc(v_currNamespace_3347_);
v_openDecls_3348_ = lean_ctor_get(v_toCold_3339_, 5);
lean_inc(v_openDecls_3348_);
v_initHeartbeats_3349_ = lean_ctor_get(v_toCold_3339_, 6);
lean_inc(v_initHeartbeats_3349_);
v_maxHeartbeats_3350_ = lean_ctor_get(v_toCold_3339_, 7);
lean_inc(v_maxHeartbeats_3350_);
v_quotContext_3351_ = lean_ctor_get(v_toCold_3339_, 8);
lean_inc(v_quotContext_3351_);
v_currMacroScope_3352_ = lean_ctor_get(v_toCold_3339_, 9);
lean_inc(v_currMacroScope_3352_);
v_cancelTk_x3f_3353_ = lean_ctor_get(v_toCold_3339_, 10);
lean_inc(v_cancelTk_x3f_3353_);
v_inheritedTraceOptions_3354_ = lean_ctor_get(v_toCold_3339_, 11);
lean_inc_ref(v_inheritedTraceOptions_3354_);
lean_dec_ref(v_toCold_3339_);
lean_inc(v___y_3318_);
v___y_3232_ = v___y_3295_;
v___y_3233_ = v___y_3298_;
v___y_3234_ = v___y_3297_;
v___y_3235_ = v___y_3296_;
v___y_3236_ = v___y_3299_;
v___y_3237_ = v___y_3300_;
v___y_3238_ = v___y_3301_;
v___y_3239_ = v___y_3302_;
v___y_3240_ = v___y_3303_;
v___y_3241_ = v___y_3304_;
v___y_3242_ = v___y_3305_;
v___y_3243_ = v___y_3306_;
v___y_3244_ = v___y_3307_;
v___y_3245_ = v___y_3308_;
v___y_3246_ = v___y_3309_;
v___y_3247_ = v___y_3311_;
v___y_3248_ = v___y_3312_;
v___y_3249_ = v___y_3313_;
v___y_3250_ = v___y_3315_;
v___y_3251_ = v___y_3316_;
v___y_3252_ = v___y_3317_;
v___y_3253_ = v___y_3318_;
v___y_3254_ = v___y_3319_;
v___y_3255_ = v___y_3320_;
v___y_3256_ = v___y_3321_;
v_fileName_3257_ = v_fileName_3345_;
v_fileMap_3258_ = v_fileMap_3346_;
v_currNamespace_3259_ = v_currNamespace_3347_;
v_openDecls_3260_ = v_openDecls_3348_;
v_initHeartbeats_3261_ = v_initHeartbeats_3349_;
v_maxHeartbeats_3262_ = v_maxHeartbeats_3350_;
v_quotContext_3263_ = v_quotContext_3351_;
v_currMacroScope_3264_ = v_currMacroScope_3352_;
v_cancelTk_x3f_3265_ = v_cancelTk_x3f_3353_;
v_inheritedTraceOptions_3266_ = v_inheritedTraceOptions_3354_;
v_currRecDepth_3267_ = v_currRecDepth_3340_;
v_ref_3268_ = v_ref_3341_;
v_suppressElabErrors_3269_ = v_suppressElabErrors_3342_;
v_checkDeprecated_3270_ = v_checkDeprecated_3343_;
v_isRecordingDeps_3271_ = v_isRecordingDeps_3344_;
v___y_3272_ = v___y_3318_;
goto v___jp_3231_;
}
}
}
}
}
else
{
lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3652_; 
lean_dec_ref(v___f_3005_);
lean_dec(v_importArts_3003_);
lean_dec(v_name_3001_);
lean_dec(v_head_2985_);
lean_del_object(v___x_2983_);
lean_dec(v_head_2981_);
lean_del_object(v___x_2979_);
v_a_3645_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3647_ = v___x_3011_;
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_dec(v___x_3011_);
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
lean_del_object(v___x_2988_);
lean_dec(v_tail_2986_);
lean_dec(v_head_2985_);
lean_del_object(v___x_2983_);
lean_dec(v_head_2981_);
lean_del_object(v___x_2979_);
v_a_3654_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3656_ = v___x_2999_;
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_a_3654_);
lean_dec(v___x_2999_);
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
lean_dec(v_tail_2976_);
lean_dec_ref_known(v_tail_2975_, 2);
lean_dec_ref_known(v_args_2950_, 2);
goto v___jp_2952_;
}
}
else
{
lean_dec_ref_known(v_args_2950_, 2);
lean_dec(v_tail_2975_);
goto v___jp_2952_;
}
}
else
{
lean_dec(v_args_2950_);
goto v___jp_2952_;
}
v___jp_2952_:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2953_ = ((lean_object*)(l_main___closed__0));
v___x_2954_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_2953_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2962_; 
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2962_ == 0)
{
lean_object* v_unused_2963_; 
v_unused_2963_ = lean_ctor_get(v___x_2954_, 0);
lean_dec(v_unused_2963_);
v___x_2956_ = v___x_2954_;
v_isShared_2957_ = v_isSharedCheck_2962_;
goto v_resetjp_2955_;
}
else
{
lean_dec(v___x_2954_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2962_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2958_; lean_object* v___x_2960_; 
v___x_2958_ = l_main___boxed__const__1;
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 0, v___x_2958_);
v___x_2960_ = v___x_2956_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v___x_2958_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
else
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
v_a_2964_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2954_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2954_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2969_; 
if (v_isShared_2967_ == 0)
{
v___x_2969_ = v___x_2966_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2964_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
v___jp_2972_:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2973_ = l_main___boxed__const__2;
v___x_2974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2973_);
return v___x_2974_;
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
uint8_t v___x_42325__boxed_3812_; size_t v_sz_boxed_3813_; size_t v_i_boxed_3814_; lean_object* v_res_3815_; 
v___x_42325__boxed_3812_ = lean_unbox(v___x_3804_);
v_sz_boxed_3813_ = lean_unbox_usize(v_sz_3806_);
lean_dec(v_sz_3806_);
v_i_boxed_3814_ = lean_unbox_usize(v_i_3807_);
lean_dec(v_i_3807_);
v_res_3815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42(v___x_42325__boxed_3812_, v_as_3805_, v_sz_boxed_3813_, v_i_boxed_3814_, v_b_3808_, v___y_3809_, v___y_3810_);
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
uint8_t v___x_42356__boxed_3855_; size_t v_sz_boxed_3856_; size_t v_i_boxed_3857_; lean_object* v_res_3858_; 
v___x_42356__boxed_3855_ = lean_unbox(v___x_3847_);
v_sz_boxed_3856_ = lean_unbox_usize(v_sz_3849_);
lean_dec(v_sz_3849_);
v_i_boxed_3857_ = lean_unbox_usize(v_i_3850_);
lean_dec(v_i_3850_);
v_res_3858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49(v___x_42356__boxed_3855_, v_as_3848_, v_sz_boxed_3856_, v_i_boxed_3857_, v_b_3851_, v___y_3852_, v___y_3853_);
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
