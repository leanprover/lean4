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
size_t v___x_56_; size_t v___x_57_; uint8_t v___x_58_; 
v___x_56_ = ((size_t)0ULL);
v___x_57_ = lean_usize_of_nat(v___x_54_);
v___x_58_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1(v_a_52_, v_as_51_, v___x_56_, v___x_57_);
return v___x_58_;
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
lean_object* v_a_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_141_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_141_ == 0)
{
v___x_119_ = v___x_116_;
v_isShared_120_ = v_isSharedCheck_141_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_a_117_);
lean_dec(v___x_116_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_141_;
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
size_t v___x_139_; lean_object* v___x_140_; 
v___x_139_ = lean_usize_of_nat(v___x_136_);
v___x_140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(v_irExtNames_113_, v_entries_134_, v___x_112_, v___x_139_, v___x_137_);
lean_dec_ref(v_entries_134_);
lean_dec_ref(v_irExtNames_113_);
v___y_122_ = v___x_140_;
goto v___jp_121_;
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
LEAN_EXPORT lean_object* l___private_LeanIR_0__mkIRData___boxed(lean_object* v_env_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_LeanIR_0__mkIRData(v_env_142_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(lean_object* v_s_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_147_ = lean_string_utf8_byte_size(v_s_146_);
v___x_148_ = lean_unsigned_to_nat(2u);
v___x_149_ = lean_nat_dec_le(v___x_148_, v___x_147_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; 
lean_dec_ref(v_s_146_);
v___x_150_ = lean_box(0);
return v___x_150_;
}
else
{
lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_151_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__0));
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = lean_string_memcmp(v_s_146_, v___x_151_, v___x_152_, v___x_152_, v___x_148_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; 
lean_dec_ref(v_s_146_);
v___x_154_ = lean_box(0);
return v___x_154_;
}
else
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
lean_inc_ref(v_s_146_);
v___x_155_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_155_, 0, v_s_146_);
lean_ctor_set(v___x_155_, 1, v___x_152_);
lean_ctor_set(v___x_155_, 2, v___x_147_);
v___x_156_ = l_String_Slice_pos_x21(v___x_155_, v___x_148_);
lean_dec_ref_known(v___x_155_, 3);
v___x_157_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_157_, 0, v_s_146_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
lean_ctor_set(v___x_157_, 2, v___x_147_);
v___x_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
return v___x_158_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0(lean_object* v_s_159_, lean_object* v_pat_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(v_s_159_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___boxed(lean_object* v_s_162_, lean_object* v_pat_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0(v_s_162_, v_pat_163_);
lean_dec_ref(v_pat_163_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(lean_object* v_val_165_, lean_object* v_a_166_, lean_object* v_b_167_){
_start:
{
lean_object* v_str_168_; lean_object* v_startInclusive_169_; lean_object* v_endExclusive_170_; lean_object* v___x_171_; uint8_t v_decide_172_; 
v_str_168_ = lean_ctor_get(v_val_165_, 0);
v_startInclusive_169_ = lean_ctor_get(v_val_165_, 1);
v_endExclusive_170_ = lean_ctor_get(v_val_165_, 2);
v___x_171_ = lean_nat_sub(v_endExclusive_170_, v_startInclusive_169_);
v_decide_172_ = lean_nat_dec_eq(v_a_166_, v___x_171_);
lean_dec(v___x_171_);
if (v_decide_172_ == 0)
{
lean_object* v___x_173_; uint32_t v___x_174_; uint32_t v___x_175_; uint8_t v___x_176_; 
v___x_173_ = lean_nat_add(v_startInclusive_169_, v_a_166_);
v___x_174_ = lean_string_utf8_get_fast(v_str_168_, v___x_173_);
v___x_175_ = 61;
v___x_176_ = lean_uint32_dec_eq(v___x_174_, v___x_175_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
lean_dec(v_a_166_);
v___x_177_ = lean_box(0);
v___x_178_ = lean_string_utf8_next_fast(v_str_168_, v___x_173_);
lean_dec(v___x_173_);
v___x_179_ = lean_nat_sub(v___x_178_, v_startInclusive_169_);
v_a_166_ = v___x_179_;
v_b_167_ = v___x_177_;
goto _start;
}
else
{
lean_object* v___x_181_; 
lean_dec(v___x_173_);
v___x_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_181_, 0, v_a_166_);
return v___x_181_;
}
}
else
{
lean_dec(v_a_166_);
lean_inc(v_b_167_);
return v_b_167_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg___boxed(lean_object* v_val_182_, lean_object* v_a_183_, lean_object* v_b_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(v_val_182_, v_a_183_, v_b_184_);
lean_dec(v_b_184_);
lean_dec_ref(v_val_182_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption(lean_object* v_opts_193_, lean_object* v_arg_194_){
_start:
{
lean_object* v___x_196_; 
lean_inc_ref(v_arg_194_);
v___x_196_ = l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(v_arg_194_);
if (lean_obj_tag(v___x_196_) == 1)
{
lean_object* v_val_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_261_; 
lean_dec_ref(v_arg_194_);
v_val_197_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_261_ == 0)
{
v___x_199_ = v___x_196_;
v_isShared_200_ = v_isSharedCheck_261_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_val_197_);
lean_dec(v___x_196_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_261_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___y_202_; lean_object* v_searcher_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v_searcher_254_ = lean_unsigned_to_nat(0u);
v___x_255_ = lean_box(0);
v___x_256_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(v_val_197_, v_searcher_254_, v___x_255_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_startInclusive_257_; lean_object* v_endExclusive_258_; lean_object* v___x_259_; 
v_startInclusive_257_ = lean_ctor_get(v_val_197_, 1);
v_endExclusive_258_ = lean_ctor_get(v_val_197_, 2);
v___x_259_ = lean_nat_sub(v_endExclusive_258_, v_startInclusive_257_);
v___y_202_ = v___x_259_;
goto v___jp_201_;
}
else
{
lean_object* v_val_260_; 
v_val_260_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_val_260_);
lean_dec_ref_known(v___x_256_, 1);
v___y_202_ = v_val_260_;
goto v___jp_201_;
}
v___jp_201_:
{
lean_object* v_str_203_; lean_object* v_startInclusive_204_; lean_object* v_endExclusive_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_253_; 
v_str_203_ = lean_ctor_get(v_val_197_, 0);
v_startInclusive_204_ = lean_ctor_get(v_val_197_, 1);
v_endExclusive_205_ = lean_ctor_get(v_val_197_, 2);
v_isSharedCheck_253_ = !lean_is_exclusive(v_val_197_);
if (v_isSharedCheck_253_ == 0)
{
v___x_207_ = v_val_197_;
v_isShared_208_ = v_isSharedCheck_253_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_endExclusive_205_);
lean_inc(v_startInclusive_204_);
lean_inc(v_str_203_);
lean_dec(v_val_197_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_253_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; uint8_t v_decide_210_; 
v___x_209_ = lean_nat_sub(v_endExclusive_205_, v_startInclusive_204_);
v_decide_210_ = lean_nat_dec_eq(v___y_202_, v___x_209_);
lean_dec(v___x_209_);
if (v_decide_210_ == 0)
{
lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_211_ = lean_nat_add(v_startInclusive_204_, v___y_202_);
lean_dec(v___y_202_);
lean_inc(v___x_211_);
lean_inc(v_startInclusive_204_);
lean_inc_ref(v_str_203_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 2, v___x_211_);
v___x_213_ = v___x_207_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_str_203_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v_startInclusive_204_);
lean_ctor_set(v_reuseFailAlloc_248_, 2, v___x_211_);
v___x_213_ = v_reuseFailAlloc_248_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v_name_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v_val_218_; lean_object* v___x_219_; 
v_name_214_ = l_String_Slice_toName(v___x_213_);
lean_dec_ref(v___x_213_);
v___x_215_ = lean_string_utf8_next_fast(v_str_203_, v___x_211_);
lean_dec(v___x_211_);
v___x_216_ = lean_nat_sub(v___x_215_, v_startInclusive_204_);
v___x_217_ = lean_nat_add(v_startInclusive_204_, v___x_216_);
lean_dec(v___x_216_);
lean_dec(v_startInclusive_204_);
v_val_218_ = lean_string_utf8_extract_fast(v_str_203_, v___x_217_, v_endExclusive_205_);
lean_dec(v_endExclusive_205_);
lean_dec(v___x_217_);
lean_dec_ref(v_str_203_);
v___x_219_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_219_) == 0)
{
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_239_; 
v_a_220_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_239_ == 0)
{
v___x_222_ = v___x_219_;
v_isShared_223_ = v_isSharedCheck_239_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_219_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_239_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; 
v___x_224_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_220_, v_name_214_);
lean_dec(v_a_220_);
if (lean_obj_tag(v___x_224_) == 1)
{
lean_object* v_val_225_; lean_object* v___x_226_; 
lean_del_object(v___x_222_);
lean_del_object(v___x_199_);
v_val_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_val_225_);
lean_dec_ref_known(v___x_224_, 1);
v___x_226_ = l_Lean_Language_Lean_setOption(v_opts_193_, v_val_225_, v_name_214_, v_val_218_);
return v___x_226_;
}
else
{
lean_object* v___x_227_; uint8_t v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_234_; 
lean_dec(v___x_224_);
lean_dec_ref(v_val_218_);
lean_dec_ref(v_opts_193_);
v___x_227_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__0));
v___x_228_ = 1;
v___x_229_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_214_, v___x_228_);
v___x_230_ = lean_string_append(v___x_227_, v___x_229_);
lean_dec_ref(v___x_229_);
v___x_231_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__1));
v___x_232_ = lean_string_append(v___x_230_, v___x_231_);
if (v_isShared_200_ == 0)
{
lean_ctor_set_tag(v___x_199_, 18);
lean_ctor_set(v___x_199_, 0, v___x_232_);
v___x_234_ = v___x_199_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_232_);
v___x_234_ = v_reuseFailAlloc_238_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_236_; 
if (v_isShared_223_ == 0)
{
lean_ctor_set_tag(v___x_222_, 1);
lean_ctor_set(v___x_222_, 0, v___x_234_);
v___x_236_ = v___x_222_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_234_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
}
else
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
lean_dec_ref(v_val_218_);
lean_dec(v_name_214_);
lean_del_object(v___x_199_);
lean_dec_ref(v_opts_193_);
v_a_240_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v___x_219_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_219_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
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
lean_object* v___x_249_; lean_object* v___x_251_; 
lean_del_object(v___x_207_);
lean_dec(v_endExclusive_205_);
lean_dec(v_startInclusive_204_);
lean_dec_ref(v_str_203_);
lean_dec(v___y_202_);
lean_dec_ref(v_opts_193_);
v___x_249_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__3));
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 0, v___x_249_);
v___x_251_ = v___x_199_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_249_);
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
}
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
lean_dec(v___x_196_);
lean_dec_ref(v_opts_193_);
v___x_262_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__4));
v___x_263_ = lean_string_append(v___x_262_, v_arg_194_);
lean_dec_ref(v_arg_194_);
v___x_264_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__5));
v___x_265_ = lean_string_append(v___x_263_, v___x_264_);
v___x_266_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
v___x_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
return v___x_267_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption___boxed(lean_object* v_opts_268_, lean_object* v_arg_269_, lean_object* v_a_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l___private_LeanIR_0__setConfigOption(v_opts_268_, v_arg_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1(lean_object* v_val_272_, lean_object* v_inst_273_, lean_object* v_R_274_, lean_object* v_a_275_, lean_object* v_b_276_, lean_object* v_c_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(v_val_272_, v_a_275_, v_b_276_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___boxed(lean_object* v_val_279_, lean_object* v_inst_280_, lean_object* v_R_281_, lean_object* v_a_282_, lean_object* v_b_283_, lean_object* v_c_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1(v_val_279_, v_inst_280_, v_R_281_, v_a_282_, v_b_283_, v_c_284_);
lean_dec(v_b_283_);
lean_dec_ref(v_val_279_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg___lam__0(lean_object* v___x_286_, lean_object* v_x_287_){
_start:
{
lean_inc_ref(v___x_286_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg___lam__0___boxed(lean_object* v___x_288_, lean_object* v_x_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_main___elam__0___redArg___lam__0(v___x_288_, v_x_289_);
lean_dec_ref(v_x_289_);
lean_dec_ref(v___x_288_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg(lean_object* v___x_291_, uint8_t v___x_292_, lean_object* v_inst_293_, lean_object* v_ext_294_, lean_object* v_env_295_){
_start:
{
lean_object* v_toEnvExtension_297_; lean_object* v_addImportedFn_298_; lean_object* v_asyncMode_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v_importedEntries_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_333_; 
v_toEnvExtension_297_ = lean_ctor_get(v_ext_294_, 0);
lean_inc_ref(v_toEnvExtension_297_);
v_addImportedFn_298_ = lean_ctor_get(v_ext_294_, 2);
lean_inc_ref(v_addImportedFn_298_);
lean_dec_ref(v_ext_294_);
v_asyncMode_299_ = lean_ctor_get(v_toEnvExtension_297_, 2);
v___x_300_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v_inst_293_);
lean_inc_ref(v_env_295_);
v___x_301_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_300_, v_toEnvExtension_297_, v_env_295_, v_asyncMode_299_, v___x_291_, v___x_292_);
lean_dec_ref(v___x_300_);
v_importedEntries_302_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; 
v_unused_334_ = lean_ctor_get(v___x_301_, 1);
lean_dec(v_unused_334_);
v___x_304_ = v___x_301_;
v_isShared_305_ = v_isSharedCheck_333_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_importedEntries_302_);
lean_dec(v___x_301_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_333_;
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
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_324_; 
v_a_309_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_324_ == 0)
{
v___x_311_ = v___x_308_;
v_isShared_312_ = v_isSharedCheck_324_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_308_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_324_;
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
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_importedEntries_302_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v_a_309_);
v___x_314_ = v_reuseFailAlloc_323_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v___f_315_; lean_object* v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; lean_object* v___x_319_; lean_object* v___x_321_; 
v___f_315_ = lean_alloc_closure((void*)(l_main___elam__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_315_, 0, v___x_314_);
v___x_316_ = lean_box(0);
v___x_317_ = lean_box(0);
v___x_318_ = 1;
v___x_319_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_297_, v_env_295_, v___f_315_, v___x_316_, v___x_317_, v___x_318_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_319_);
v___x_321_ = v___x_311_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
else
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
lean_del_object(v___x_304_);
lean_dec_ref(v_importedEntries_302_);
lean_dec_ref(v_toEnvExtension_297_);
lean_dec_ref(v_env_295_);
v_a_325_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_308_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_308_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
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
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg___boxed(lean_object* v___x_335_, lean_object* v___x_336_, lean_object* v_inst_337_, lean_object* v_ext_338_, lean_object* v_env_339_, lean_object* v___y_340_){
_start:
{
uint8_t v___x_36983__boxed_341_; lean_object* v_res_342_; 
v___x_36983__boxed_341_ = lean_unbox(v___x_336_);
v_res_342_ = l_main___elam__0___redArg(v___x_335_, v___x_36983__boxed_341_, v_inst_337_, v_ext_338_, v_env_339_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0(lean_object* v___x_343_, uint8_t v___x_344_, lean_object* v_00_u03b1_345_, lean_object* v_00_u03b2_346_, lean_object* v_00_u03c3_347_, lean_object* v_inst_348_, lean_object* v_ext_349_, lean_object* v_env_350_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_main___elam__0___redArg(v___x_343_, v___x_344_, v_inst_348_, v_ext_349_, v_env_350_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___boxed(lean_object* v___x_353_, lean_object* v___x_354_, lean_object* v_00_u03b1_355_, lean_object* v_00_u03b2_356_, lean_object* v_00_u03c3_357_, lean_object* v_inst_358_, lean_object* v_ext_359_, lean_object* v_env_360_, lean_object* v___y_361_){
_start:
{
uint8_t v___x_37063__boxed_362_; lean_object* v_res_363_; 
v___x_37063__boxed_362_ = lean_unbox(v___x_354_);
v_res_363_ = l_main___elam__0(v___x_353_, v___x_37063__boxed_362_, v_00_u03b1_355_, v_00_u03b2_356_, v_00_u03c3_357_, v_inst_358_, v_ext_359_, v_env_360_);
return v_res_363_;
}
}
static lean_object* _init_l_panic___at___00main_spec__5___closed__0(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = l_instInhabitedError;
v___x_365_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_365_, 0, lean_box(0));
lean_closure_set(v___x_365_, 1, lean_box(0));
lean_closure_set(v___x_365_, 2, v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5(lean_object* v_msg_366_){
_start:
{
lean_object* v___x_368_; lean_object* v___x_20022__overap_369_; lean_object* v___x_370_; 
v___x_368_ = lean_obj_once(&l_panic___at___00main_spec__5___closed__0, &l_panic___at___00main_spec__5___closed__0_once, _init_l_panic___at___00main_spec__5___closed__0);
v___x_20022__overap_369_ = lean_panic_fn_borrowed(v___x_368_, v_msg_366_);
v___x_370_ = lean_apply_1(v___x_20022__overap_369_, lean_box(0));
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5___boxed(lean_object* v_msg_371_, lean_object* v___y_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_panic___at___00main_spec__5(v_msg_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8(lean_object* v_opts_374_, lean_object* v_opt_375_){
_start:
{
lean_object* v_name_376_; lean_object* v_defValue_377_; lean_object* v_map_378_; lean_object* v___x_379_; 
v_name_376_ = lean_ctor_get(v_opt_375_, 0);
v_defValue_377_ = lean_ctor_get(v_opt_375_, 1);
v_map_378_ = lean_ctor_get(v_opts_374_, 0);
v___x_379_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_378_, v_name_376_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_inc(v_defValue_377_);
return v_defValue_377_;
}
else
{
lean_object* v_val_380_; 
v_val_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_val_380_);
lean_dec_ref_known(v___x_379_, 1);
if (lean_obj_tag(v_val_380_) == 3)
{
lean_object* v_v_381_; 
v_v_381_ = lean_ctor_get(v_val_380_, 0);
lean_inc(v_v_381_);
lean_dec_ref_known(v_val_380_, 1);
return v_v_381_;
}
else
{
lean_dec(v_val_380_);
lean_inc(v_defValue_377_);
return v_defValue_377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8___boxed(lean_object* v_opts_382_, lean_object* v_opt_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_Option_get___at___00main_spec__8(v_opts_382_, v_opt_383_);
lean_dec_ref(v_opt_383_);
lean_dec_ref(v_opts_382_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_main___lam__0(lean_object* v_package_x3f_385_, lean_object* v_ps_386_){
_start:
{
lean_object* v_importedEntries_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
v_importedEntries_387_ = lean_ctor_get(v_ps_386_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v_ps_386_);
if (v_isSharedCheck_394_ == 0)
{
lean_object* v_unused_395_; 
v_unused_395_ = lean_ctor_get(v_ps_386_, 1);
lean_dec(v_unused_395_);
v___x_389_ = v_ps_386_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_importedEntries_387_);
lean_dec(v_ps_386_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 1, v_package_x3f_385_);
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_importedEntries_387_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_package_x3f_385_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(lean_object* v_a_396_, lean_object* v_x_397_){
_start:
{
if (lean_obj_tag(v_x_397_) == 0)
{
lean_dec(v_a_396_);
return v_x_397_;
}
else
{
lean_object* v_key_398_; lean_object* v_value_399_; lean_object* v_tail_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_433_; 
v_key_398_ = lean_ctor_get(v_x_397_, 0);
v_value_399_ = lean_ctor_get(v_x_397_, 1);
v_tail_400_ = lean_ctor_get(v_x_397_, 2);
v_isSharedCheck_433_ = !lean_is_exclusive(v_x_397_);
if (v_isSharedCheck_433_ == 0)
{
v___x_402_ = v_x_397_;
v_isShared_403_ = v_isSharedCheck_433_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_tail_400_);
lean_inc(v_value_399_);
lean_inc(v_key_398_);
lean_dec(v_x_397_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_433_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
uint8_t v___x_404_; 
v___x_404_ = lean_name_eq(v_key_398_, v_a_396_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_405_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v_a_396_, v_tail_400_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 2, v___x_405_);
v___x_407_ = v___x_402_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_key_398_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_value_399_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v___x_405_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
else
{
lean_object* v_toEffectiveImport_409_; lean_object* v_parts_410_; lean_object* v_irParts_411_; uint8_t v_needsIRTrans_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_432_; 
lean_dec(v_key_398_);
v_toEffectiveImport_409_ = lean_ctor_get(v_value_399_, 0);
v_parts_410_ = lean_ctor_get(v_value_399_, 1);
v_irParts_411_ = lean_ctor_get(v_value_399_, 2);
v_needsIRTrans_412_ = lean_ctor_get_uint8(v_value_399_, sizeof(void*)*3);
v_isSharedCheck_432_ = !lean_is_exclusive(v_value_399_);
if (v_isSharedCheck_432_ == 0)
{
v___x_414_ = v_value_399_;
v_isShared_415_ = v_isSharedCheck_432_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_irParts_411_);
lean_inc(v_parts_410_);
lean_inc(v_toEffectiveImport_409_);
lean_dec(v_value_399_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_432_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v_toImport_416_; uint8_t v_hasData_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_431_; 
v_toImport_416_ = lean_ctor_get(v_toEffectiveImport_409_, 0);
v_hasData_417_ = lean_ctor_get_uint8(v_toEffectiveImport_409_, sizeof(void*)*1 + 1);
v_isSharedCheck_431_ = !lean_is_exclusive(v_toEffectiveImport_409_);
if (v_isSharedCheck_431_ == 0)
{
v___x_419_ = v_toEffectiveImport_409_;
v_isShared_420_ = v_isSharedCheck_431_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_toImport_416_);
lean_dec(v_toEffectiveImport_409_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_431_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
uint8_t v___x_421_; lean_object* v___x_423_; 
v___x_421_ = 0;
if (v_isShared_420_ == 0)
{
v___x_423_ = v___x_419_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_toImport_416_);
lean_ctor_set_uint8(v_reuseFailAlloc_430_, sizeof(void*)*1 + 1, v_hasData_417_);
v___x_423_ = v_reuseFailAlloc_430_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_425_; 
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*1, v___x_421_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v___x_423_);
v___x_425_ = v___x_414_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_parts_410_);
lean_ctor_set(v_reuseFailAlloc_429_, 2, v_irParts_411_);
lean_ctor_set_uint8(v_reuseFailAlloc_429_, sizeof(void*)*3, v_needsIRTrans_412_);
v___x_425_ = v_reuseFailAlloc_429_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_427_; 
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 1, v___x_425_);
lean_ctor_set(v___x_402_, 0, v_a_396_);
v___x_427_ = v___x_402_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_396_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v___x_425_);
lean_ctor_set(v_reuseFailAlloc_428_, 2, v_tail_400_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(lean_object* v_m_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_size_436_; lean_object* v_buckets_437_; lean_object* v___x_438_; uint64_t v___y_440_; 
v_size_436_ = lean_ctor_get(v_m_434_, 0);
v_buckets_437_ = lean_ctor_get(v_m_434_, 1);
v___x_438_ = lean_array_get_size(v_buckets_437_);
if (lean_obj_tag(v_a_435_) == 0)
{
uint64_t v___x_467_; 
v___x_467_ = 1723ULL;
v___y_440_ = v___x_467_;
goto v___jp_439_;
}
else
{
uint64_t v_hash_468_; 
v_hash_468_ = lean_ctor_get_uint64(v_a_435_, sizeof(void*)*2);
v___y_440_ = v_hash_468_;
goto v___jp_439_;
}
v___jp_439_:
{
uint64_t v___x_441_; uint64_t v___x_442_; uint64_t v_fold_443_; uint64_t v___x_444_; uint64_t v___x_445_; uint64_t v___x_446_; size_t v___x_447_; size_t v___x_448_; size_t v___x_449_; size_t v___x_450_; size_t v___x_451_; lean_object* v_bucket_452_; uint8_t v___x_453_; 
v___x_441_ = 32ULL;
v___x_442_ = lean_uint64_shift_right(v___y_440_, v___x_441_);
v_fold_443_ = lean_uint64_xor(v___y_440_, v___x_442_);
v___x_444_ = 16ULL;
v___x_445_ = lean_uint64_shift_right(v_fold_443_, v___x_444_);
v___x_446_ = lean_uint64_xor(v_fold_443_, v___x_445_);
v___x_447_ = lean_uint64_to_usize(v___x_446_);
v___x_448_ = lean_usize_of_nat(v___x_438_);
v___x_449_ = ((size_t)1ULL);
v___x_450_ = lean_usize_sub(v___x_448_, v___x_449_);
v___x_451_ = lean_usize_land(v___x_447_, v___x_450_);
v_bucket_452_ = lean_array_uget_borrowed(v_buckets_437_, v___x_451_);
v___x_453_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_a_435_, v_bucket_452_);
if (v___x_453_ == 0)
{
lean_dec(v_a_435_);
return v_m_434_;
}
else
{
lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_464_; 
lean_inc(v_bucket_452_);
lean_inc_ref(v_buckets_437_);
lean_inc(v_size_436_);
v_isSharedCheck_464_ = !lean_is_exclusive(v_m_434_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; lean_object* v_unused_466_; 
v_unused_465_ = lean_ctor_get(v_m_434_, 1);
lean_dec(v_unused_465_);
v_unused_466_ = lean_ctor_get(v_m_434_, 0);
lean_dec(v_unused_466_);
v___x_455_ = v_m_434_;
v_isShared_456_ = v_isSharedCheck_464_;
goto v_resetjp_454_;
}
else
{
lean_dec(v_m_434_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_464_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; lean_object* v_buckets_458_; lean_object* v_bucket_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_457_ = lean_box(0);
v_buckets_458_ = lean_array_uset(v_buckets_437_, v___x_451_, v___x_457_);
v_bucket_459_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v_a_435_, v_bucket_452_);
v___x_460_ = lean_array_uset(v_buckets_458_, v___x_451_, v_bucket_459_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 1, v___x_460_);
v___x_462_ = v___x_455_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_size_436_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__1(lean_object* v___x_469_, lean_object* v___x_470_, uint8_t v___x_471_, lean_object* v_importArts_472_, uint8_t v___y_473_, uint8_t v___x_474_, lean_object* v_name_475_, lean_object* v___x_476_, uint8_t v___x_477_){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_st_mk_ref(v___x_469_);
v___x_480_ = l_Lean_importModulesCore(v___x_470_, v___x_471_, v_importArts_472_, v___y_473_, v___x_474_, v___x_479_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v___x_481_; lean_object* v_moduleNameMap_482_; lean_object* v_moduleNames_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_493_; 
lean_dec_ref_known(v___x_480_, 1);
v___x_481_ = lean_st_ref_get(v___x_479_);
lean_dec(v___x_479_);
v_moduleNameMap_482_ = lean_ctor_get(v___x_481_, 0);
v_moduleNames_483_ = lean_ctor_get(v___x_481_, 1);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_493_ == 0)
{
v___x_485_ = v___x_481_;
v_isShared_486_ = v_isSharedCheck_493_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_moduleNames_483_);
lean_inc(v_moduleNameMap_482_);
lean_dec(v___x_481_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_493_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; lean_object* v___x_489_; 
v___x_487_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(v_moduleNameMap_482_, v_name_475_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_487_);
v___x_489_ = v___x_485_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_487_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_moduleNames_483_);
v___x_489_ = v_reuseFailAlloc_492_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
uint32_t v___x_490_; lean_object* v___x_491_; 
v___x_490_ = 0;
v___x_491_ = l_Lean_finalizeImport(v___x_489_, v___x_470_, v___x_476_, v___x_490_, v___x_474_, v___x_477_, v___x_471_, v___x_474_, v___x_474_);
lean_dec_ref(v___x_489_);
return v___x_491_;
}
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_dec(v___x_479_);
lean_dec_ref(v___x_476_);
lean_dec(v_name_475_);
lean_dec_ref(v___x_470_);
v_a_494_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_480_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_480_);
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
LEAN_EXPORT lean_object* l_main___lam__1___boxed(lean_object* v___x_502_, lean_object* v___x_503_, lean_object* v___x_504_, lean_object* v_importArts_505_, lean_object* v___y_506_, lean_object* v___x_507_, lean_object* v_name_508_, lean_object* v___x_509_, lean_object* v___x_510_, lean_object* v___y_511_){
_start:
{
uint8_t v___x_37231__boxed_512_; uint8_t v___y_37232__boxed_513_; uint8_t v___x_37233__boxed_514_; uint8_t v___x_37235__boxed_515_; lean_object* v_res_516_; 
v___x_37231__boxed_512_ = lean_unbox(v___x_504_);
v___y_37232__boxed_513_ = lean_unbox(v___y_506_);
v___x_37233__boxed_514_ = lean_unbox(v___x_507_);
v___x_37235__boxed_515_ = lean_unbox(v___x_510_);
v_res_516_ = l_main___lam__1(v___x_502_, v___x_503_, v___x_37231__boxed_512_, v_importArts_505_, v___y_37232__boxed_513_, v___x_37233__boxed_514_, v_name_508_, v___x_509_, v___x_37235__boxed_515_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_main___lam__2(lean_object* v___x_520_, lean_object* v___x_521_, uint16_t v___x_522_, lean_object* v_name_523_, lean_object* v_a_524_, uint8_t v___x_525_, lean_object* v___x_526_, lean_object* v_head_527_, lean_object* v___x_528_, lean_object* v___x_529_, lean_object* v___x_530_, lean_object* v___x_531_, lean_object* v___x_532_, lean_object* v___x_533_, lean_object* v___x_534_, lean_object* v___x_535_, uint8_t v___x_536_, uint8_t v___x_537_){
_start:
{
lean_object* v_a_540_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v_fileName_546_; lean_object* v_fileMap_547_; lean_object* v_currNamespace_548_; lean_object* v_openDecls_549_; lean_object* v_initHeartbeats_550_; lean_object* v_maxHeartbeats_551_; lean_object* v_quotContext_552_; lean_object* v_currMacroScope_553_; lean_object* v_cancelTk_x3f_554_; lean_object* v_inheritedTraceOptions_555_; lean_object* v_currRecDepth_556_; lean_object* v_ref_557_; uint8_t v_suppressElabErrors_558_; uint8_t v_isRecordingDeps_559_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___y_595_; lean_object* v_env_616_; uint8_t v___x_617_; uint16_t v___x_618_; uint16_t v___x_619_; uint16_t v___x_620_; uint8_t v___x_621_; 
v___x_543_ = lean_io_get_num_heartbeats();
v___x_544_ = lean_st_mk_ref(v___x_520_);
v___x_591_ = l_Lean_inheritedTraceOptions;
v___x_592_ = lean_st_ref_get(v___x_591_);
v___x_593_ = lean_st_ref_get(v___x_544_);
v_env_616_ = lean_ctor_get(v___x_593_, 0);
lean_inc_ref(v_env_616_);
lean_dec(v___x_593_);
v___x_617_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_616_);
lean_dec_ref(v_env_616_);
v___x_618_ = 512;
v___x_619_ = lean_uint16_land(v___x_522_, v___x_618_);
v___x_620_ = 0;
v___x_621_ = lean_uint16_dec_eq(v___x_619_, v___x_620_);
if (v___x_621_ == 0)
{
if (v___x_617_ == 0)
{
v___y_595_ = v___x_525_;
goto v___jp_594_;
}
else
{
lean_dec_ref(v___x_526_);
lean_inc(v___x_529_);
v_fileName_546_ = v_head_527_;
v_fileMap_547_ = v___x_528_;
v_currNamespace_548_ = v___x_529_;
v_openDecls_549_ = v___x_530_;
v_initHeartbeats_550_ = v___x_543_;
v_maxHeartbeats_551_ = v___x_531_;
v_quotContext_552_ = v___x_529_;
v_currMacroScope_553_ = v___x_532_;
v_cancelTk_x3f_554_ = v___x_533_;
v_inheritedTraceOptions_555_ = v___x_592_;
v_currRecDepth_556_ = v___x_534_;
v_ref_557_ = v___x_535_;
v_suppressElabErrors_558_ = v___x_536_;
v_isRecordingDeps_559_ = v___x_536_;
goto v___jp_545_;
}
}
else
{
if (v___x_617_ == 0)
{
lean_dec_ref(v___x_526_);
lean_inc(v___x_529_);
v_fileName_546_ = v_head_527_;
v_fileMap_547_ = v___x_528_;
v_currNamespace_548_ = v___x_529_;
v_openDecls_549_ = v___x_530_;
v_initHeartbeats_550_ = v___x_543_;
v_maxHeartbeats_551_ = v___x_531_;
v_quotContext_552_ = v___x_529_;
v_currMacroScope_553_ = v___x_532_;
v_cancelTk_x3f_554_ = v___x_533_;
v_inheritedTraceOptions_555_ = v___x_592_;
v_currRecDepth_556_ = v___x_534_;
v_ref_557_ = v___x_535_;
v_suppressElabErrors_558_ = v___x_536_;
v_isRecordingDeps_559_ = v___x_536_;
goto v___jp_545_;
}
else
{
v___y_595_ = v___x_537_;
goto v___jp_594_;
}
}
v___jp_539_:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_mk_io_user_error(v_a_540_);
v___x_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
return v___x_542_;
}
v___jp_545_:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_560_ = l_Lean_maxRecDepth;
v___x_561_ = l_Lean_Option_get___at___00main_spec__8(v___x_521_, v___x_560_);
v___x_562_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_562_, 0, v_fileName_546_);
lean_ctor_set(v___x_562_, 1, v_fileMap_547_);
lean_ctor_set(v___x_562_, 2, v___x_521_);
lean_ctor_set(v___x_562_, 3, v___x_561_);
lean_ctor_set(v___x_562_, 4, v_currNamespace_548_);
lean_ctor_set(v___x_562_, 5, v_openDecls_549_);
lean_ctor_set(v___x_562_, 6, v_initHeartbeats_550_);
lean_ctor_set(v___x_562_, 7, v_maxHeartbeats_551_);
lean_ctor_set(v___x_562_, 8, v_quotContext_552_);
lean_ctor_set(v___x_562_, 9, v_currMacroScope_553_);
lean_ctor_set(v___x_562_, 10, v_cancelTk_x3f_554_);
lean_ctor_set(v___x_562_, 11, v_inheritedTraceOptions_555_);
v___x_563_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_563_, 0, v___x_562_);
lean_ctor_set(v___x_563_, 1, v_currRecDepth_556_);
lean_ctor_set(v___x_563_, 2, v_ref_557_);
lean_ctor_set_uint16(v___x_563_, sizeof(void*)*3, v___x_522_);
lean_ctor_set_uint8(v___x_563_, sizeof(void*)*3 + 2, v_suppressElabErrors_558_);
lean_ctor_set_uint8(v___x_563_, sizeof(void*)*3 + 3, v_isRecordingDeps_559_);
v___x_564_ = l_Lean_Compiler_LCNF_emitC(v_name_523_, v___x_563_, v___x_544_);
lean_dec_ref_known(v___x_563_, 3);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_a_565_);
lean_dec_ref_known(v___x_564_, 1);
v___x_566_ = lean_st_ref_get(v___x_544_);
lean_dec(v___x_544_);
lean_dec(v___x_566_);
v___x_567_ = lean_string_to_utf8(v_a_565_);
v___x_568_ = lean_io_prim_handle_write(v_a_524_, v___x_567_);
lean_dec_ref(v___x_567_);
return v___x_568_;
}
else
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_590_; 
lean_dec(v___x_544_);
v_a_569_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_590_ == 0)
{
v___x_571_ = v___x_564_;
v_isShared_572_ = v_isSharedCheck_590_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_564_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_590_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
if (lean_obj_tag(v_a_569_) == 0)
{
lean_object* v_msg_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
v_msg_573_ = lean_ctor_get(v_a_569_, 1);
lean_inc_ref(v_msg_573_);
lean_dec_ref_known(v_a_569_, 2);
v___x_574_ = l_Lean_MessageData_toString(v_msg_573_);
v___x_575_ = lean_mk_io_user_error(v___x_574_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_575_);
v___x_577_ = v___x_571_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
else
{
lean_object* v_id_579_; lean_object* v___x_580_; 
lean_del_object(v___x_571_);
v_id_579_ = lean_ctor_get(v_a_569_, 0);
lean_inc(v_id_579_);
lean_dec_ref_known(v_a_569_, 2);
v___x_580_ = l_Lean_InternalExceptionId_getName(v_id_579_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
lean_dec(v_id_579_);
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_581_);
lean_dec_ref_known(v___x_580_, 1);
v___x_582_ = ((lean_object*)(l_main___lam__2___closed__0));
v___x_583_ = l_Lean_Name_toString(v_a_581_, v___x_525_);
v___x_584_ = lean_string_append(v___x_582_, v___x_583_);
lean_dec_ref(v___x_583_);
v_a_540_ = v___x_584_;
goto v___jp_539_;
}
else
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
lean_dec_ref_known(v___x_580_, 1);
v___x_585_ = ((lean_object*)(l_main___lam__2___closed__1));
v___x_586_ = l_Nat_reprFast(v_id_579_);
v___x_587_ = lean_string_append(v___x_585_, v___x_586_);
lean_dec_ref(v___x_586_);
v___x_588_ = ((lean_object*)(l_main___lam__2___closed__2));
v___x_589_ = lean_string_append(v___x_587_, v___x_588_);
v_a_540_ = v___x_589_;
goto v___jp_539_;
}
}
}
}
}
v___jp_594_:
{
lean_object* v___x_596_; lean_object* v_env_597_; lean_object* v_nextMacroScope_598_; lean_object* v_ngen_599_; lean_object* v_auxDeclNGen_600_; lean_object* v_traceState_601_; lean_object* v_recordedDeps_602_; lean_object* v_messages_603_; lean_object* v_infoState_604_; lean_object* v_snapshotTasks_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_614_; 
v___x_596_ = lean_st_ref_take(v___x_544_);
v_env_597_ = lean_ctor_get(v___x_596_, 0);
v_nextMacroScope_598_ = lean_ctor_get(v___x_596_, 1);
v_ngen_599_ = lean_ctor_get(v___x_596_, 2);
v_auxDeclNGen_600_ = lean_ctor_get(v___x_596_, 3);
v_traceState_601_ = lean_ctor_get(v___x_596_, 4);
v_recordedDeps_602_ = lean_ctor_get(v___x_596_, 6);
v_messages_603_ = lean_ctor_get(v___x_596_, 7);
v_infoState_604_ = lean_ctor_get(v___x_596_, 8);
v_snapshotTasks_605_ = lean_ctor_get(v___x_596_, 9);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; 
v_unused_615_ = lean_ctor_get(v___x_596_, 5);
lean_dec(v_unused_615_);
v___x_607_ = v___x_596_;
v_isShared_608_ = v_isSharedCheck_614_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_snapshotTasks_605_);
lean_inc(v_infoState_604_);
lean_inc(v_messages_603_);
lean_inc(v_recordedDeps_602_);
lean_inc(v_traceState_601_);
lean_inc(v_auxDeclNGen_600_);
lean_inc(v_ngen_599_);
lean_inc(v_nextMacroScope_598_);
lean_inc(v_env_597_);
lean_dec(v___x_596_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_614_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_609_ = l_Lean_Kernel_enableDiag(v_env_597_, v___y_595_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 5, v___x_526_);
lean_ctor_set(v___x_607_, 0, v___x_609_);
v___x_611_ = v___x_607_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_nextMacroScope_598_);
lean_ctor_set(v_reuseFailAlloc_613_, 2, v_ngen_599_);
lean_ctor_set(v_reuseFailAlloc_613_, 3, v_auxDeclNGen_600_);
lean_ctor_set(v_reuseFailAlloc_613_, 4, v_traceState_601_);
lean_ctor_set(v_reuseFailAlloc_613_, 5, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_613_, 6, v_recordedDeps_602_);
lean_ctor_set(v_reuseFailAlloc_613_, 7, v_messages_603_);
lean_ctor_set(v_reuseFailAlloc_613_, 8, v_infoState_604_);
lean_ctor_set(v_reuseFailAlloc_613_, 9, v_snapshotTasks_605_);
v___x_611_ = v_reuseFailAlloc_613_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_612_; 
v___x_612_ = lean_st_ref_put(v___x_544_, v___x_611_);
lean_inc(v___x_529_);
v_fileName_546_ = v_head_527_;
v_fileMap_547_ = v___x_528_;
v_currNamespace_548_ = v___x_529_;
v_openDecls_549_ = v___x_530_;
v_initHeartbeats_550_ = v___x_543_;
v_maxHeartbeats_551_ = v___x_531_;
v_quotContext_552_ = v___x_529_;
v_currMacroScope_553_ = v___x_532_;
v_cancelTk_x3f_554_ = v___x_533_;
v_inheritedTraceOptions_555_ = v___x_592_;
v_currRecDepth_556_ = v___x_534_;
v_ref_557_ = v___x_535_;
v_suppressElabErrors_558_ = v___x_536_;
v_isRecordingDeps_559_ = v___x_536_;
goto v___jp_545_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__2___boxed(lean_object** _args){
lean_object* v___x_622_ = _args[0];
lean_object* v___x_623_ = _args[1];
lean_object* v___x_624_ = _args[2];
lean_object* v_name_625_ = _args[3];
lean_object* v_a_626_ = _args[4];
lean_object* v___x_627_ = _args[5];
lean_object* v___x_628_ = _args[6];
lean_object* v_head_629_ = _args[7];
lean_object* v___x_630_ = _args[8];
lean_object* v___x_631_ = _args[9];
lean_object* v___x_632_ = _args[10];
lean_object* v___x_633_ = _args[11];
lean_object* v___x_634_ = _args[12];
lean_object* v___x_635_ = _args[13];
lean_object* v___x_636_ = _args[14];
lean_object* v___x_637_ = _args[15];
lean_object* v___x_638_ = _args[16];
lean_object* v___x_639_ = _args[17];
lean_object* v___y_640_ = _args[18];
_start:
{
uint16_t v___x_37304__boxed_641_; uint8_t v___x_37306__boxed_642_; uint8_t v___x_37317__boxed_643_; uint8_t v___x_37318__boxed_644_; lean_object* v_res_645_; 
v___x_37304__boxed_641_ = lean_unbox(v___x_624_);
v___x_37306__boxed_642_ = lean_unbox(v___x_627_);
v___x_37317__boxed_643_ = lean_unbox(v___x_638_);
v___x_37318__boxed_644_ = lean_unbox(v___x_639_);
v_res_645_ = l_main___lam__2(v___x_622_, v___x_623_, v___x_37304__boxed_641_, v_name_625_, v_a_626_, v___x_37306__boxed_642_, v___x_628_, v_head_629_, v___x_630_, v___x_631_, v___x_632_, v___x_633_, v___x_634_, v___x_635_, v___x_636_, v___x_637_, v___x_37317__boxed_643_, v___x_37318__boxed_644_);
lean_dec(v_a_626_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_main___lam__3(lean_object* v___x_646_, lean_object* v_x_647_){
_start:
{
lean_inc_ref(v___x_646_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_main___lam__3___boxed(lean_object* v___x_648_, lean_object* v_x_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_main___lam__3(v___x_648_, v_x_649_);
lean_dec_ref(v_x_649_);
lean_dec_ref(v___x_648_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(lean_object* v_x2_651_, lean_object* v_as_652_, size_t v_i_653_, size_t v_stop_654_, lean_object* v_b_655_){
_start:
{
uint8_t v___x_656_; 
v___x_656_ = lean_usize_dec_eq(v_i_653_, v_stop_654_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; lean_object* v___x_658_; size_t v___x_659_; size_t v___x_660_; 
v___x_657_ = lean_array_uget_borrowed(v_as_652_, v_i_653_);
lean_inc_ref(v_x2_651_);
lean_inc(v___x_657_);
v___x_658_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_657_, v_x2_651_, v_b_655_);
v___x_659_ = ((size_t)1ULL);
v___x_660_ = lean_usize_add(v_i_653_, v___x_659_);
v_i_653_ = v___x_660_;
v_b_655_ = v___x_658_;
goto _start;
}
else
{
lean_dec_ref(v_x2_651_);
return v_b_655_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(lean_object* v_x2_662_, lean_object* v_as_663_, lean_object* v_i_664_, lean_object* v_stop_665_, lean_object* v_b_666_){
_start:
{
size_t v_i_boxed_667_; size_t v_stop_boxed_668_; lean_object* v_res_669_; 
v_i_boxed_667_ = lean_unbox_usize(v_i_664_);
lean_dec(v_i_664_);
v_stop_boxed_668_ = lean_unbox_usize(v_stop_665_);
lean_dec(v_stop_665_);
v_res_669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v_x2_662_, v_as_663_, v_i_boxed_667_, v_stop_boxed_668_, v_b_666_);
lean_dec_ref(v_as_663_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(lean_object* v_as_670_, size_t v_i_671_, size_t v_stop_672_, lean_object* v_b_673_){
_start:
{
lean_object* v___y_675_; uint8_t v___x_679_; 
v___x_679_ = lean_usize_dec_eq(v_i_671_, v_stop_672_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; lean_object* v_declNames_681_; lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_680_ = lean_array_uget_borrowed(v_as_670_, v_i_671_);
v_declNames_681_ = lean_ctor_get(v___x_680_, 0);
v___x_682_ = lean_unsigned_to_nat(0u);
v___x_683_ = lean_array_get_size(v_declNames_681_);
v___x_684_ = lean_nat_dec_lt(v___x_682_, v___x_683_);
if (v___x_684_ == 0)
{
v___y_675_ = v_b_673_;
goto v___jp_674_;
}
else
{
size_t v___x_685_; size_t v___x_686_; lean_object* v___x_687_; 
v___x_685_ = ((size_t)0ULL);
v___x_686_ = lean_usize_of_nat(v___x_683_);
lean_inc(v___x_680_);
v___x_687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_680_, v_declNames_681_, v___x_685_, v___x_686_, v_b_673_);
v___y_675_ = v___x_687_;
goto v___jp_674_;
}
}
else
{
return v_b_673_;
}
v___jp_674_:
{
size_t v___x_676_; size_t v___x_677_; 
v___x_676_ = ((size_t)1ULL);
v___x_677_ = lean_usize_add(v_i_671_, v___x_676_);
v_i_671_ = v___x_677_;
v_b_673_ = v___y_675_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14___boxed(lean_object* v_as_688_, lean_object* v_i_689_, lean_object* v_stop_690_, lean_object* v_b_691_){
_start:
{
size_t v_i_boxed_692_; size_t v_stop_boxed_693_; lean_object* v_res_694_; 
v_i_boxed_692_ = lean_unbox_usize(v_i_689_);
lean_dec(v_i_689_);
v_stop_boxed_693_ = lean_unbox_usize(v_stop_690_);
lean_dec(v_stop_690_);
v_res_694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v_as_688_, v_i_boxed_692_, v_stop_boxed_693_, v_b_691_);
lean_dec_ref(v_as_688_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(lean_object* v_s_695_){
_start:
{
lean_object* v___x_697_; lean_object* v_putStr_698_; lean_object* v___x_699_; 
v___x_697_ = lean_get_stderr();
v_putStr_698_ = lean_ctor_get(v___x_697_, 4);
lean_inc_ref(v_putStr_698_);
lean_dec_ref(v___x_697_);
v___x_699_ = lean_apply_2(v_putStr_698_, v_s_695_, lean_box(0));
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8___boxed(lean_object* v_s_700_, lean_object* v_a_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v_s_700_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6(lean_object* v_s_703_){
_start:
{
uint32_t v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_705_ = 10;
v___x_706_ = lean_string_push(v_s_703_, v___x_705_);
v___x_707_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v___x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6___boxed(lean_object* v_s_708_, lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_IO_eprintln___at___00main_spec__6(v_s_708_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(lean_object* v_o_714_, lean_object* v_k_715_, lean_object* v_v_716_){
_start:
{
lean_object* v_map_717_; uint8_t v_hasTrace_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_732_; 
v_map_717_ = lean_ctor_get(v_o_714_, 0);
v_hasTrace_718_ = lean_ctor_get_uint8(v_o_714_, sizeof(void*)*1);
v_isSharedCheck_732_ = !lean_is_exclusive(v_o_714_);
if (v_isSharedCheck_732_ == 0)
{
v___x_720_ = v_o_714_;
v_isShared_721_ = v_isSharedCheck_732_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_map_717_);
lean_dec(v_o_714_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_732_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_722_, 0, v_v_716_);
lean_inc(v_k_715_);
v___x_723_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_715_, v___x_722_, v_map_717_);
if (v_hasTrace_718_ == 0)
{
lean_object* v___x_724_; uint8_t v___x_725_; lean_object* v___x_727_; 
v___x_724_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_725_ = l_Lean_Name_isPrefixOf(v___x_724_, v_k_715_);
lean_dec(v_k_715_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v___x_723_);
v___x_727_ = v___x_720_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_723_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_ctor_set_uint8(v___x_727_, sizeof(void*)*1, v___x_725_);
return v___x_727_;
}
}
else
{
lean_object* v___x_730_; 
lean_dec(v_k_715_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v___x_723_);
v___x_730_ = v___x_720_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_723_);
lean_ctor_set_uint8(v_reuseFailAlloc_731_, sizeof(void*)*1, v_hasTrace_718_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00main_spec__3(lean_object* v_opts_733_, lean_object* v_opt_734_, lean_object* v_val_735_){
_start:
{
lean_object* v_name_736_; lean_object* v___x_737_; 
v_name_736_ = lean_ctor_get(v_opt_734_, 0);
lean_inc(v_name_736_);
lean_dec_ref(v_opt_734_);
v___x_737_ = l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(v_opts_733_, v_name_736_, v_val_735_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object* v_as_738_, size_t v_i_739_, size_t v_stop_740_, lean_object* v_b_741_){
_start:
{
uint8_t v___x_742_; 
v___x_742_ = lean_usize_dec_eq(v_i_739_, v_stop_740_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; lean_object* v_name_744_; lean_object* v___x_745_; size_t v___x_746_; size_t v___x_747_; 
v___x_743_ = lean_array_uget_borrowed(v_as_738_, v_i_739_);
v_name_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_name_744_);
v___x_745_ = l_Lean_Compiler_LCNF_setDeclPublic(v_b_741_, v_name_744_);
v___x_746_ = ((size_t)1ULL);
v___x_747_ = lean_usize_add(v_i_739_, v___x_746_);
v_i_739_ = v___x_747_;
v_b_741_ = v___x_745_;
goto _start;
}
else
{
return v_b_741_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object* v_as_749_, lean_object* v_i_750_, lean_object* v_stop_751_, lean_object* v_b_752_){
_start:
{
size_t v_i_boxed_753_; size_t v_stop_boxed_754_; lean_object* v_res_755_; 
v_i_boxed_753_ = lean_unbox_usize(v_i_750_);
lean_dec(v_i_750_);
v_stop_boxed_754_ = lean_unbox_usize(v_stop_751_);
lean_dec(v_stop_751_);
v_res_755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v_as_749_, v_i_boxed_753_, v_stop_boxed_754_, v_b_752_);
lean_dec_ref(v_as_749_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg(lean_object* v_as_x27_757_, lean_object* v_b_758_){
_start:
{
if (lean_obj_tag(v_as_x27_757_) == 0)
{
lean_object* v___x_760_; 
v___x_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_760_, 0, v_b_758_);
return v___x_760_;
}
else
{
lean_object* v_head_761_; lean_object* v_tail_762_; lean_object* v_fst_763_; lean_object* v_snd_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_789_; 
v_head_761_ = lean_ctor_get(v_as_x27_757_, 0);
v_tail_762_ = lean_ctor_get(v_as_x27_757_, 1);
v_fst_763_ = lean_ctor_get(v_b_758_, 0);
v_snd_764_ = lean_ctor_get(v_b_758_, 1);
v_isSharedCheck_789_ = !lean_is_exclusive(v_b_758_);
if (v_isSharedCheck_789_ == 0)
{
v___x_766_ = v_b_758_;
v_isShared_767_ = v_isSharedCheck_789_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_snd_764_);
lean_inc(v_fst_763_);
lean_dec(v_b_758_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_789_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_768_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0));
v___x_769_ = lean_string_dec_eq(v_head_761_, v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; 
lean_inc(v_head_761_);
v___x_770_ = l___private_LeanIR_0__setConfigOption(v_snd_764_, v_head_761_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_773_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref_known(v___x_770_, 1);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 1, v_a_771_);
v___x_773_ = v___x_766_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_fst_763_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_a_771_);
v___x_773_ = v_reuseFailAlloc_775_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
v_as_x27_757_ = v_tail_762_;
v_b_758_ = v___x_773_;
goto _start;
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_del_object(v___x_766_);
lean_dec(v_fst_763_);
v_a_776_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_770_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_770_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
else
{
lean_object* v___x_784_; lean_object* v___x_786_; 
lean_dec(v_fst_763_);
v___x_784_ = lean_box(v___x_769_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 0, v___x_784_);
v___x_786_ = v___x_766_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_snd_764_);
v___x_786_ = v_reuseFailAlloc_788_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
v_as_x27_757_ = v_tail_762_;
v_b_758_ = v___x_786_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(lean_object* v_as_x27_790_, lean_object* v_b_791_, lean_object* v___y_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_790_, v_b_791_);
lean_dec(v_as_x27_790_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object* v_a_794_, lean_object* v_as_795_, size_t v_i_796_, size_t v_stop_797_, lean_object* v_b_798_){
_start:
{
lean_object* v___y_800_; uint8_t v___x_804_; 
v___x_804_ = lean_usize_dec_eq(v_i_796_, v_stop_797_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; lean_object* v_name_806_; uint8_t v___x_807_; 
v___x_805_ = lean_array_uget_borrowed(v_as_795_, v_i_796_);
v_name_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_name_806_);
lean_inc_ref(v_a_794_);
v___x_807_ = l_Lean_isExtern(v_a_794_, v_name_806_);
if (v___x_807_ == 0)
{
v___y_800_ = v_b_798_;
goto v___jp_799_;
}
else
{
lean_object* v___x_808_; 
lean_inc(v___x_805_);
v___x_808_ = lean_array_push(v_b_798_, v___x_805_);
v___y_800_ = v___x_808_;
goto v___jp_799_;
}
}
else
{
lean_dec_ref(v_a_794_);
return v_b_798_;
}
v___jp_799_:
{
size_t v___x_801_; size_t v___x_802_; 
v___x_801_ = ((size_t)1ULL);
v___x_802_ = lean_usize_add(v_i_796_, v___x_801_);
v_i_796_ = v___x_802_;
v_b_798_ = v___y_800_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object* v_a_809_, lean_object* v_as_810_, lean_object* v_i_811_, lean_object* v_stop_812_, lean_object* v_b_813_){
_start:
{
size_t v_i_boxed_814_; size_t v_stop_boxed_815_; lean_object* v_res_816_; 
v_i_boxed_814_ = lean_unbox_usize(v_i_811_);
lean_dec(v_i_811_);
v_stop_boxed_815_ = lean_unbox_usize(v_stop_812_);
lean_dec(v_stop_812_);
v_res_816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_809_, v_as_810_, v_i_boxed_814_, v_stop_boxed_815_, v_b_813_);
lean_dec_ref(v_as_810_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___lam__0(lean_object* v_addEntryFn_817_, lean_object* v___x_818_, lean_object* v_s_819_){
_start:
{
lean_object* v_importedEntries_820_; lean_object* v_state_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_829_; 
v_importedEntries_820_ = lean_ctor_get(v_s_819_, 0);
v_state_821_ = lean_ctor_get(v_s_819_, 1);
v_isSharedCheck_829_ = !lean_is_exclusive(v_s_819_);
if (v_isSharedCheck_829_ == 0)
{
v___x_823_ = v_s_819_;
v_isShared_824_ = v_isSharedCheck_829_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_state_821_);
lean_inc(v_importedEntries_820_);
lean_dec(v_s_819_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_829_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v_state_825_; lean_object* v___x_827_; 
v_state_825_ = lean_apply_2(v_addEntryFn_817_, v_state_821_, v___x_818_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 1, v_state_825_);
v___x_827_ = v___x_823_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_importedEntries_820_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_state_825_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object* v_as_830_, size_t v_i_831_, size_t v_stop_832_, lean_object* v_b_833_){
_start:
{
lean_object* v___y_835_; uint8_t v___x_839_; 
v___x_839_ = lean_usize_dec_eq(v_i_831_, v_stop_832_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; lean_object* v_toEnvExtension_841_; lean_object* v_addEntryFn_842_; lean_object* v_asyncMode_843_; uint8_t v_logWrites_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___f_847_; uint8_t v___x_848_; 
v___x_840_ = l_Lean_Compiler_LCNF_impureSigExt;
v_toEnvExtension_841_ = lean_ctor_get(v___x_840_, 0);
v_addEntryFn_842_ = lean_ctor_get(v___x_840_, 3);
v_asyncMode_843_ = lean_ctor_get(v_toEnvExtension_841_, 2);
v_logWrites_844_ = lean_ctor_get_uint8(v_toEnvExtension_841_, sizeof(void*)*6);
v___x_845_ = lean_box(0);
v___x_846_ = lean_array_uget_borrowed(v_as_830_, v_i_831_);
lean_inc(v___x_846_);
lean_inc(v_addEntryFn_842_);
v___f_847_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___lam__0), 3, 2);
lean_closure_set(v___f_847_, 0, v_addEntryFn_842_);
lean_closure_set(v___f_847_, 1, v___x_846_);
v___x_848_ = 1;
if (v_logWrites_844_ == 0)
{
lean_object* v___x_849_; 
lean_inc_ref(v_toEnvExtension_841_);
v___x_849_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_841_, v_b_833_, v___f_847_, v_asyncMode_843_, v___x_845_, v___x_848_);
v___y_835_ = v___x_849_;
goto v___jp_834_;
}
else
{
lean_object* v___x_850_; lean_object* v___x_851_; 
lean_inc_ref_n(v_toEnvExtension_841_, 2);
v___x_850_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite___redArg(v_toEnvExtension_841_, v_b_833_);
lean_dec_ref(v_b_833_);
v___x_851_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_841_, v___x_850_, v___f_847_, v_asyncMode_843_, v___x_845_, v___x_848_);
v___y_835_ = v___x_851_;
goto v___jp_834_;
}
}
else
{
return v_b_833_;
}
v___jp_834_:
{
size_t v___x_836_; size_t v___x_837_; 
v___x_836_ = ((size_t)1ULL);
v___x_837_ = lean_usize_add(v_i_831_, v___x_836_);
v_i_831_ = v___x_837_;
v_b_833_ = v___y_835_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object* v_as_852_, lean_object* v_i_853_, lean_object* v_stop_854_, lean_object* v_b_855_){
_start:
{
size_t v_i_boxed_856_; size_t v_stop_boxed_857_; lean_object* v_res_858_; 
v_i_boxed_856_ = lean_unbox_usize(v_i_853_);
lean_dec(v_i_853_);
v_stop_boxed_857_ = lean_unbox_usize(v_stop_854_);
lean_dec(v_stop_854_);
v_res_858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v_as_852_, v_i_boxed_856_, v_stop_boxed_857_, v_b_855_);
lean_dec_ref(v_as_852_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object* v___y_860_, lean_object* v_as_861_, size_t v_i_862_, size_t v_stop_863_, lean_object* v_b_864_){
_start:
{
lean_object* v___y_866_; uint8_t v___x_870_; 
v___x_870_ = lean_usize_dec_eq(v_i_862_, v_stop_863_);
if (v___x_870_ == 0)
{
lean_object* v_fst_871_; lean_object* v_snd_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___y_876_; 
v_fst_871_ = lean_ctor_get(v_b_864_, 0);
v_snd_872_ = lean_ctor_get(v_b_864_, 1);
v___x_873_ = lean_array_uget_borrowed(v_as_861_, v_i_862_);
v___x_874_ = l_Lean_IR_Decl_name(v___x_873_);
if (lean_obj_tag(v___x_874_) == 1)
{
lean_object* v_pre_889_; lean_object* v_str_890_; lean_object* v___x_891_; uint8_t v___x_892_; 
v_pre_889_ = lean_ctor_get(v___x_874_, 0);
v_str_890_ = lean_ctor_get(v___x_874_, 1);
v___x_891_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___closed__0));
v___x_892_ = lean_string_dec_eq(v_str_890_, v___x_891_);
if (v___x_892_ == 0)
{
lean_inc_ref(v___x_874_);
v___y_876_ = v___x_874_;
goto v___jp_875_;
}
else
{
lean_inc(v_pre_889_);
v___y_876_ = v_pre_889_;
goto v___jp_875_;
}
}
else
{
lean_inc(v___x_874_);
v___y_876_ = v___x_874_;
goto v___jp_875_;
}
v___jp_875_:
{
uint8_t v___x_877_; 
lean_inc_ref(v___y_860_);
v___x_877_ = l_Lean_isExtern(v___y_860_, v___y_876_);
if (v___x_877_ == 0)
{
lean_dec(v___x_874_);
v___y_866_ = v_b_864_;
goto v___jp_865_;
}
else
{
lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_886_; 
lean_inc(v_snd_872_);
lean_inc(v_fst_871_);
v_isSharedCheck_886_ = !lean_is_exclusive(v_b_864_);
if (v_isSharedCheck_886_ == 0)
{
lean_object* v_unused_887_; lean_object* v_unused_888_; 
v_unused_887_ = lean_ctor_get(v_b_864_, 1);
lean_dec(v_unused_887_);
v_unused_888_ = lean_ctor_get(v_b_864_, 0);
lean_dec(v_unused_888_);
v___x_879_ = v_b_864_;
v_isShared_880_ = v_isSharedCheck_886_;
goto v_resetjp_878_;
}
else
{
lean_dec(v_b_864_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_886_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_884_; 
lean_inc_n(v___x_873_, 2);
v___x_881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_873_);
lean_ctor_set(v___x_881_, 1, v_fst_871_);
v___x_882_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_872_, v___x_874_, v___x_873_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 1, v___x_882_);
lean_ctor_set(v___x_879_, 0, v___x_881_);
v___x_884_ = v___x_879_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
v___y_866_ = v___x_884_;
goto v___jp_865_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_860_);
return v_b_864_;
}
v___jp_865_:
{
size_t v___x_867_; size_t v___x_868_; 
v___x_867_ = ((size_t)1ULL);
v___x_868_ = lean_usize_add(v_i_862_, v___x_867_);
v_i_862_ = v___x_868_;
v_b_864_ = v___y_866_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object* v___y_893_, lean_object* v_as_894_, lean_object* v_i_895_, lean_object* v_stop_896_, lean_object* v_b_897_){
_start:
{
size_t v_i_boxed_898_; size_t v_stop_boxed_899_; lean_object* v_res_900_; 
v_i_boxed_898_ = lean_unbox_usize(v_i_895_);
lean_dec(v_i_895_);
v_stop_boxed_899_ = lean_unbox_usize(v_stop_896_);
lean_dec(v_stop_896_);
v_res_900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_893_, v_as_894_, v_i_boxed_898_, v_stop_boxed_899_, v_b_897_);
lean_dec_ref(v_as_894_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27(lean_object* v_as_904_, size_t v_sz_905_, size_t v_i_906_, lean_object* v_b_907_){
_start:
{
uint8_t v___x_909_; 
v___x_909_ = lean_usize_dec_lt(v_i_906_, v_sz_905_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; 
v___x_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_910_, 0, v_b_907_);
return v___x_910_;
}
else
{
uint8_t v___x_911_; lean_object* v_a_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
lean_dec_ref(v_b_907_);
v___x_911_ = 0;
v_a_912_ = lean_array_uget_borrowed(v_as_904_, v_i_906_);
lean_inc(v_a_912_);
v___x_913_ = l_Lean_Message_toString(v_a_912_, v___x_911_);
v___x_914_ = l_IO_eprintln___at___00main_spec__6(v___x_913_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v___x_915_; size_t v___x_916_; size_t v___x_917_; 
lean_dec_ref_known(v___x_914_, 1);
v___x_915_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_916_ = ((size_t)1ULL);
v___x_917_ = lean_usize_add(v_i_906_, v___x_916_);
v_i_906_ = v___x_917_;
v_b_907_ = v___x_915_;
goto _start;
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
v_a_919_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_914_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_914_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_919_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___boxed(lean_object* v_as_927_, lean_object* v_sz_928_, lean_object* v_i_929_, lean_object* v_b_930_, lean_object* v___y_931_){
_start:
{
size_t v_sz_boxed_932_; size_t v_i_boxed_933_; lean_object* v_res_934_; 
v_sz_boxed_932_ = lean_unbox_usize(v_sz_928_);
lean_dec(v_sz_928_);
v_i_boxed_933_ = lean_unbox_usize(v_i_929_);
lean_dec(v_i_929_);
v_res_934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27(v_as_927_, v_sz_boxed_932_, v_i_boxed_933_, v_b_930_);
lean_dec_ref(v_as_927_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(lean_object* v_as_935_, size_t v_sz_936_, size_t v_i_937_, lean_object* v_b_938_){
_start:
{
uint8_t v___x_940_; 
v___x_940_ = lean_usize_dec_lt(v_i_937_, v_sz_936_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; 
v___x_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_941_, 0, v_b_938_);
return v___x_941_;
}
else
{
uint8_t v___x_942_; lean_object* v_a_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
lean_dec_ref(v_b_938_);
v___x_942_ = 0;
v_a_943_ = lean_array_uget_borrowed(v_as_935_, v_i_937_);
lean_inc(v_a_943_);
v___x_944_ = l_Lean_Message_toString(v_a_943_, v___x_942_);
v___x_945_ = l_IO_eprintln___at___00main_spec__6(v___x_944_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v___x_946_; size_t v___x_947_; size_t v___x_948_; lean_object* v___x_949_; 
lean_dec_ref_known(v___x_945_, 1);
v___x_946_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_947_ = ((size_t)1ULL);
v___x_948_ = lean_usize_add(v_i_937_, v___x_947_);
v___x_949_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27(v_as_935_, v_sz_936_, v___x_948_, v___x_946_);
return v___x_949_;
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
v_a_950_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_945_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_945_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13___boxed(lean_object* v_as_958_, lean_object* v_sz_959_, lean_object* v_i_960_, lean_object* v_b_961_, lean_object* v___y_962_){
_start:
{
size_t v_sz_boxed_963_; size_t v_i_boxed_964_; lean_object* v_res_965_; 
v_sz_boxed_963_ = lean_unbox_usize(v_sz_959_);
lean_dec(v_sz_959_);
v_i_boxed_964_ = lean_unbox_usize(v_i_960_);
lean_dec(v_i_960_);
v_res_965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_as_958_, v_sz_boxed_963_, v_i_boxed_964_, v_b_961_);
lean_dec_ref(v_as_958_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(lean_object* v_init_966_, lean_object* v_n_967_, lean_object* v_b_968_){
_start:
{
if (lean_obj_tag(v_n_967_) == 0)
{
lean_object* v_cs_970_; lean_object* v___x_971_; lean_object* v___x_972_; size_t v_sz_973_; size_t v___x_974_; lean_object* v___x_975_; 
v_cs_970_ = lean_ctor_get(v_n_967_, 0);
v___x_971_ = lean_box(0);
v___x_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
lean_ctor_set(v___x_972_, 1, v_b_968_);
v_sz_973_ = lean_array_size(v_cs_970_);
v___x_974_ = ((size_t)0ULL);
v___x_975_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12(v_init_966_, v_cs_970_, v_sz_973_, v___x_974_, v___x_972_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_990_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_990_ == 0)
{
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_990_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_990_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v_fst_980_; 
v_fst_980_ = lean_ctor_get(v_a_976_, 0);
if (lean_obj_tag(v_fst_980_) == 0)
{
lean_object* v_snd_981_; lean_object* v___x_982_; lean_object* v___x_984_; 
v_snd_981_ = lean_ctor_get(v_a_976_, 1);
lean_inc(v_snd_981_);
lean_dec(v_a_976_);
v___x_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_982_, 0, v_snd_981_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_982_);
v___x_984_ = v___x_978_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_982_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
else
{
lean_object* v_val_986_; lean_object* v___x_988_; 
lean_inc_ref(v_fst_980_);
lean_dec(v_a_976_);
v_val_986_ = lean_ctor_get(v_fst_980_, 0);
lean_inc(v_val_986_);
lean_dec_ref_known(v_fst_980_, 1);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v_val_986_);
v___x_988_ = v___x_978_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_val_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
v_a_991_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_975_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_975_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
else
{
lean_object* v_vs_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; size_t v_sz_1002_; size_t v___x_1003_; lean_object* v___x_1004_; 
v_vs_999_ = lean_ctor_get(v_n_967_, 0);
v___x_1000_ = lean_box(0);
v___x_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v_b_968_);
v_sz_1002_ = lean_array_size(v_vs_999_);
v___x_1003_ = ((size_t)0ULL);
v___x_1004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_vs_999_, v_sz_1002_, v___x_1003_, v___x_1001_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1019_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1007_ = v___x_1004_;
v_isShared_1008_ = v_isSharedCheck_1019_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_1004_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1019_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v_fst_1009_; 
v_fst_1009_ = lean_ctor_get(v_a_1005_, 0);
if (lean_obj_tag(v_fst_1009_) == 0)
{
lean_object* v_snd_1010_; lean_object* v___x_1011_; lean_object* v___x_1013_; 
v_snd_1010_ = lean_ctor_get(v_a_1005_, 1);
lean_inc(v_snd_1010_);
lean_dec(v_a_1005_);
v___x_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1011_, 0, v_snd_1010_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 0, v___x_1011_);
v___x_1013_ = v___x_1007_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
else
{
lean_object* v_val_1015_; lean_object* v___x_1017_; 
lean_inc_ref(v_fst_1009_);
lean_dec(v_a_1005_);
v_val_1015_ = lean_ctor_get(v_fst_1009_, 0);
lean_inc(v_val_1015_);
lean_dec_ref_known(v_fst_1009_, 1);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 0, v_val_1015_);
v___x_1017_ = v___x_1007_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_val_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
v_a_1020_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_1004_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1004_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12(lean_object* v_init_1028_, lean_object* v_as_1029_, size_t v_sz_1030_, size_t v_i_1031_, lean_object* v_b_1032_){
_start:
{
uint8_t v___x_1034_; 
v___x_1034_ = lean_usize_dec_lt(v_i_1031_, v_sz_1030_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; 
v___x_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1035_, 0, v_b_1032_);
return v___x_1035_;
}
else
{
lean_object* v_snd_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1070_; 
v_snd_1036_ = lean_ctor_get(v_b_1032_, 1);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_b_1032_);
if (v_isSharedCheck_1070_ == 0)
{
lean_object* v_unused_1071_; 
v_unused_1071_ = lean_ctor_get(v_b_1032_, 0);
lean_dec(v_unused_1071_);
v___x_1038_ = v_b_1032_;
v_isShared_1039_ = v_isSharedCheck_1070_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_snd_1036_);
lean_dec(v_b_1032_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1070_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; lean_object* v_a_1041_; lean_object* v___x_1042_; 
v___x_1040_ = lean_box(0);
v_a_1041_ = lean_array_uget_borrowed(v_as_1029_, v_i_1031_);
lean_inc(v_snd_1036_);
v___x_1042_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_1028_, v_a_1041_, v_snd_1036_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1061_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1045_ = v___x_1042_;
v_isShared_1046_ = v_isSharedCheck_1061_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1042_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1061_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
if (lean_obj_tag(v_a_1043_) == 0)
{
lean_object* v___x_1047_; lean_object* v___x_1049_; 
v___x_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1047_, 0, v_a_1043_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 0, v___x_1047_);
v___x_1049_ = v___x_1038_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_snd_1036_);
v___x_1049_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1051_; 
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 0, v___x_1049_);
v___x_1051_ = v___x_1045_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; 
lean_del_object(v___x_1045_);
lean_dec(v_snd_1036_);
v_a_1054_ = lean_ctor_get(v_a_1043_, 0);
lean_inc(v_a_1054_);
lean_dec_ref_known(v_a_1043_, 1);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 1, v_a_1054_);
lean_ctor_set(v___x_1038_, 0, v___x_1040_);
v___x_1056_ = v___x_1038_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_a_1054_);
v___x_1056_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
size_t v___x_1057_; size_t v___x_1058_; 
v___x_1057_ = ((size_t)1ULL);
v___x_1058_ = lean_usize_add(v_i_1031_, v___x_1057_);
v_i_1031_ = v___x_1058_;
v_b_1032_ = v___x_1056_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_del_object(v___x_1038_);
lean_dec(v_snd_1036_);
v_a_1062_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1042_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1042_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12___boxed(lean_object* v_init_1072_, lean_object* v_as_1073_, lean_object* v_sz_1074_, lean_object* v_i_1075_, lean_object* v_b_1076_, lean_object* v___y_1077_){
_start:
{
size_t v_sz_boxed_1078_; size_t v_i_boxed_1079_; lean_object* v_res_1080_; 
v_sz_boxed_1078_ = lean_unbox_usize(v_sz_1074_);
lean_dec(v_sz_1074_);
v_i_boxed_1079_ = lean_unbox_usize(v_i_1075_);
lean_dec(v_i_1075_);
v_res_1080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__12(v_init_1072_, v_as_1073_, v_sz_boxed_1078_, v_i_boxed_1079_, v_b_1076_);
lean_dec_ref(v_as_1073_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10___boxed(lean_object* v_init_1081_, lean_object* v_n_1082_, lean_object* v_b_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_1081_, v_n_1082_, v_b_1083_);
lean_dec_ref(v_n_1082_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15(lean_object* v_as_1089_, size_t v_sz_1090_, size_t v_i_1091_, lean_object* v_b_1092_){
_start:
{
uint8_t v___x_1094_; 
v___x_1094_ = lean_usize_dec_lt(v_i_1091_, v_sz_1090_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; 
v___x_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1095_, 0, v_b_1092_);
return v___x_1095_;
}
else
{
uint8_t v___x_1096_; lean_object* v_a_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_dec_ref(v_b_1092_);
v___x_1096_ = 0;
v_a_1097_ = lean_array_uget_borrowed(v_as_1089_, v_i_1091_);
lean_inc(v_a_1097_);
v___x_1098_ = l_Lean_Message_toString(v_a_1097_, v___x_1096_);
v___x_1099_ = l_IO_eprintln___at___00main_spec__6(v___x_1098_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v___x_1100_; size_t v___x_1101_; size_t v___x_1102_; 
lean_dec_ref_known(v___x_1099_, 1);
v___x_1100_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_1101_ = ((size_t)1ULL);
v___x_1102_ = lean_usize_add(v_i_1091_, v___x_1101_);
v_i_1091_ = v___x_1102_;
v_b_1092_ = v___x_1100_;
goto _start;
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
v_a_1104_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1099_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1099_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___boxed(lean_object* v_as_1112_, lean_object* v_sz_1113_, lean_object* v_i_1114_, lean_object* v_b_1115_, lean_object* v___y_1116_){
_start:
{
size_t v_sz_boxed_1117_; size_t v_i_boxed_1118_; lean_object* v_res_1119_; 
v_sz_boxed_1117_ = lean_unbox_usize(v_sz_1113_);
lean_dec(v_sz_1113_);
v_i_boxed_1118_ = lean_unbox_usize(v_i_1114_);
lean_dec(v_i_1114_);
v_res_1119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15(v_as_1112_, v_sz_boxed_1117_, v_i_boxed_1118_, v_b_1115_);
lean_dec_ref(v_as_1112_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(lean_object* v_as_1120_, size_t v_sz_1121_, size_t v_i_1122_, lean_object* v_b_1123_){
_start:
{
uint8_t v___x_1125_; 
v___x_1125_ = lean_usize_dec_lt(v_i_1122_, v_sz_1121_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1126_, 0, v_b_1123_);
return v___x_1126_;
}
else
{
uint8_t v___x_1127_; lean_object* v_a_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
lean_dec_ref(v_b_1123_);
v___x_1127_ = 0;
v_a_1128_ = lean_array_uget_borrowed(v_as_1120_, v_i_1122_);
lean_inc(v_a_1128_);
v___x_1129_ = l_Lean_Message_toString(v_a_1128_, v___x_1127_);
v___x_1130_ = l_IO_eprintln___at___00main_spec__6(v___x_1129_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v___x_1131_; size_t v___x_1132_; size_t v___x_1133_; lean_object* v___x_1134_; 
lean_dec_ref_known(v___x_1130_, 1);
v___x_1131_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_1132_ = ((size_t)1ULL);
v___x_1133_ = lean_usize_add(v_i_1122_, v___x_1132_);
v___x_1134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15(v_as_1120_, v_sz_1121_, v___x_1133_, v___x_1131_);
return v___x_1134_;
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
v_a_1135_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1130_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1130_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11___boxed(lean_object* v_as_1143_, lean_object* v_sz_1144_, lean_object* v_i_1145_, lean_object* v_b_1146_, lean_object* v___y_1147_){
_start:
{
size_t v_sz_boxed_1148_; size_t v_i_boxed_1149_; lean_object* v_res_1150_; 
v_sz_boxed_1148_ = lean_unbox_usize(v_sz_1144_);
lean_dec(v_sz_1144_);
v_i_boxed_1149_ = lean_unbox_usize(v_i_1145_);
lean_dec(v_i_1145_);
v_res_1150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_as_1143_, v_sz_boxed_1148_, v_i_boxed_1149_, v_b_1146_);
lean_dec_ref(v_as_1143_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7(lean_object* v_t_1151_, lean_object* v_init_1152_){
_start:
{
lean_object* v_root_1154_; lean_object* v_tail_1155_; lean_object* v___x_1156_; 
v_root_1154_ = lean_ctor_get(v_t_1151_, 0);
v_tail_1155_ = lean_ctor_get(v_t_1151_, 1);
v___x_1156_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_1152_, v_root_1154_, v_init_1152_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1193_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1159_ = v___x_1156_;
v_isShared_1160_ = v_isSharedCheck_1193_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1156_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1193_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
if (lean_obj_tag(v_a_1157_) == 0)
{
lean_object* v_a_1161_; lean_object* v___x_1163_; 
v_a_1161_ = lean_ctor_get(v_a_1157_, 0);
lean_inc(v_a_1161_);
lean_dec_ref_known(v_a_1157_, 1);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v_a_1161_);
v___x_1163_ = v___x_1159_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1161_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
else
{
lean_object* v_a_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; size_t v_sz_1168_; size_t v___x_1169_; lean_object* v___x_1170_; 
lean_del_object(v___x_1159_);
v_a_1165_ = lean_ctor_get(v_a_1157_, 0);
lean_inc(v_a_1165_);
lean_dec_ref_known(v_a_1157_, 1);
v___x_1166_ = lean_box(0);
v___x_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
lean_ctor_set(v___x_1167_, 1, v_a_1165_);
v_sz_1168_ = lean_array_size(v_tail_1155_);
v___x_1169_ = ((size_t)0ULL);
v___x_1170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_tail_1155_, v_sz_1168_, v___x_1169_, v___x_1167_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1184_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1173_ = v___x_1170_;
v_isShared_1174_ = v_isSharedCheck_1184_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1170_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1184_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v_fst_1175_; 
v_fst_1175_ = lean_ctor_get(v_a_1171_, 0);
if (lean_obj_tag(v_fst_1175_) == 0)
{
lean_object* v_snd_1176_; lean_object* v___x_1178_; 
v_snd_1176_ = lean_ctor_get(v_a_1171_, 1);
lean_inc(v_snd_1176_);
lean_dec(v_a_1171_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v_snd_1176_);
v___x_1178_ = v___x_1173_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_snd_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
else
{
lean_object* v_val_1180_; lean_object* v___x_1182_; 
lean_inc_ref(v_fst_1175_);
lean_dec(v_a_1171_);
v_val_1180_ = lean_ctor_get(v_fst_1175_, 0);
lean_inc(v_val_1180_);
lean_dec_ref_known(v_fst_1175_, 1);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v_val_1180_);
v___x_1182_ = v___x_1173_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_val_1180_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
v_a_1185_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1170_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1170_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
v_a_1194_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1156_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1156_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7___boxed(lean_object* v_t_1202_, lean_object* v_init_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_t_1202_, v_init_1203_);
lean_dec_ref(v_t_1202_);
return v_res_1205_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0(uint8_t v_suppressElabErrors_1213_, lean_object* v_x_1214_){
_start:
{
if (lean_obj_tag(v_x_1214_) == 1)
{
lean_object* v_pre_1215_; 
v_pre_1215_ = lean_ctor_get(v_x_1214_, 0);
switch(lean_obj_tag(v_pre_1215_))
{
case 1:
{
lean_object* v_pre_1216_; 
v_pre_1216_ = lean_ctor_get(v_pre_1215_, 0);
switch(lean_obj_tag(v_pre_1216_))
{
case 0:
{
lean_object* v_str_1217_; lean_object* v_str_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; 
v_str_1217_ = lean_ctor_get(v_x_1214_, 1);
v_str_1218_ = lean_ctor_get(v_pre_1215_, 1);
v___x_1219_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__0));
v___x_1220_ = lean_string_dec_eq(v_str_1218_, v___x_1219_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; uint8_t v___x_1222_; 
v___x_1221_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__1));
v___x_1222_ = lean_string_dec_eq(v_str_1218_, v___x_1221_);
if (v___x_1222_ == 0)
{
return v___x_1222_;
}
else
{
lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__2));
v___x_1224_ = lean_string_dec_eq(v_str_1217_, v___x_1223_);
if (v___x_1224_ == 0)
{
return v___x_1224_;
}
else
{
return v_suppressElabErrors_1213_;
}
}
}
else
{
lean_object* v___x_1225_; uint8_t v___x_1226_; 
v___x_1225_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__3));
v___x_1226_ = lean_string_dec_eq(v_str_1217_, v___x_1225_);
if (v___x_1226_ == 0)
{
return v___x_1226_;
}
else
{
return v_suppressElabErrors_1213_;
}
}
}
case 1:
{
lean_object* v_pre_1227_; 
v_pre_1227_ = lean_ctor_get(v_pre_1216_, 0);
if (lean_obj_tag(v_pre_1227_) == 0)
{
lean_object* v_str_1228_; lean_object* v_str_1229_; lean_object* v_str_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v_str_1228_ = lean_ctor_get(v_x_1214_, 1);
v_str_1229_ = lean_ctor_get(v_pre_1215_, 1);
v_str_1230_ = lean_ctor_get(v_pre_1216_, 1);
v___x_1231_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__4));
v___x_1232_ = lean_string_dec_eq(v_str_1230_, v___x_1231_);
if (v___x_1232_ == 0)
{
return v___x_1232_;
}
else
{
lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__5));
v___x_1234_ = lean_string_dec_eq(v_str_1229_, v___x_1233_);
if (v___x_1234_ == 0)
{
return v___x_1234_;
}
else
{
lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1235_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__6));
v___x_1236_ = lean_string_dec_eq(v_str_1228_, v___x_1235_);
if (v___x_1236_ == 0)
{
return v___x_1236_;
}
else
{
return v_suppressElabErrors_1213_;
}
}
}
}
else
{
uint8_t v___x_1237_; 
v___x_1237_ = 0;
return v___x_1237_;
}
}
default: 
{
uint8_t v___x_1238_; 
v___x_1238_ = 0;
return v___x_1238_;
}
}
}
case 0:
{
lean_object* v_str_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; 
v_str_1239_ = lean_ctor_get(v_x_1214_, 1);
v___x_1240_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_1241_ = lean_string_dec_eq(v_str_1239_, v___x_1240_);
if (v___x_1241_ == 0)
{
return v___x_1241_;
}
else
{
return v_suppressElabErrors_1213_;
}
}
default: 
{
uint8_t v___x_1242_; 
v___x_1242_ = 0;
return v___x_1242_;
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
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___boxed(lean_object* v_suppressElabErrors_1244_, lean_object* v_x_1245_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1246_; uint8_t v_res_1247_; lean_object* v_r_1248_; 
v_suppressElabErrors_boxed_1246_ = lean_unbox(v_suppressElabErrors_1244_);
v_res_1247_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0(v_suppressElabErrors_boxed_1246_, v_x_1245_);
lean_dec(v_x_1245_);
v_r_1248_ = lean_box(v_res_1247_);
return v_r_1248_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(lean_object* v_opts_1249_, lean_object* v_opt_1250_){
_start:
{
lean_object* v_name_1251_; lean_object* v_defValue_1252_; lean_object* v_map_1253_; lean_object* v___x_1254_; 
v_name_1251_ = lean_ctor_get(v_opt_1250_, 0);
v_defValue_1252_ = lean_ctor_get(v_opt_1250_, 1);
v_map_1253_ = lean_ctor_get(v_opts_1249_, 0);
v___x_1254_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1253_, v_name_1251_);
if (lean_obj_tag(v___x_1254_) == 0)
{
uint8_t v___x_1255_; 
v___x_1255_ = lean_unbox(v_defValue_1252_);
return v___x_1255_;
}
else
{
lean_object* v_val_1256_; 
v_val_1256_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_val_1256_);
lean_dec_ref_known(v___x_1254_, 1);
if (lean_obj_tag(v_val_1256_) == 1)
{
uint8_t v_v_1257_; 
v_v_1257_ = lean_ctor_get_uint8(v_val_1256_, 0);
lean_dec_ref_known(v_val_1256_, 0);
return v_v_1257_;
}
else
{
uint8_t v___x_1258_; 
lean_dec(v_val_1256_);
v___x_1258_ = lean_unbox(v_defValue_1252_);
return v___x_1258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___boxed(lean_object* v_opts_1259_, lean_object* v_opt_1260_){
_start:
{
uint8_t v_res_1261_; lean_object* v_r_1262_; 
v_res_1261_ = l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(v_opts_1259_, v_opt_1260_);
lean_dec_ref(v_opt_1260_);
lean_dec_ref(v_opts_1259_);
v_r_1262_ = lean_box(v_res_1261_);
return v_r_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44(lean_object* v_ref_1264_, lean_object* v_msgData_1265_, uint8_t v_severity_1266_, uint8_t v_isSilent_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v___y_1272_; uint8_t v___y_1273_; lean_object* v___y_1274_; uint8_t v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v_toCold_1279_; lean_object* v___y_1280_; lean_object* v___y_1309_; lean_object* v___y_1310_; uint8_t v___y_1311_; uint8_t v___y_1312_; uint8_t v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; uint8_t v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; uint8_t v___y_1340_; uint8_t v___y_1341_; lean_object* v___y_1342_; uint8_t v___y_1346_; uint8_t v___y_1347_; uint8_t v___x_1357_; uint8_t v___y_1359_; uint8_t v___x_1365_; 
v___x_1357_ = 2;
v___x_1365_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1266_, v___x_1357_);
if (v___x_1365_ == 0)
{
v___y_1359_ = v___x_1365_;
goto v___jp_1358_;
}
else
{
uint8_t v___x_1366_; 
lean_inc_ref(v_msgData_1265_);
v___x_1366_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1265_);
if (v___x_1366_ == 0)
{
v___y_1359_ = v___x_1366_;
goto v___jp_1358_;
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
lean_dec_ref(v_msgData_1265_);
v___x_1367_ = lean_box(0);
v___x_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
return v___x_1368_;
}
}
v___jp_1271_:
{
lean_object* v_currNamespace_1281_; lean_object* v_openDecls_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v_env_1287_; lean_object* v_nextMacroScope_1288_; lean_object* v_ngen_1289_; lean_object* v_auxDeclNGen_1290_; lean_object* v_traceState_1291_; lean_object* v_cache_1292_; lean_object* v_recordedDeps_1293_; lean_object* v_messages_1294_; lean_object* v_infoState_1295_; lean_object* v_snapshotTasks_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1307_; 
v_currNamespace_1281_ = lean_ctor_get(v_toCold_1279_, 4);
v_openDecls_1282_ = lean_ctor_get(v_toCold_1279_, 5);
lean_inc(v_openDecls_1282_);
lean_inc(v_currNamespace_1281_);
v___x_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1283_, 0, v_currNamespace_1281_);
lean_ctor_set(v___x_1283_, 1, v_openDecls_1282_);
v___x_1284_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
lean_ctor_set(v___x_1284_, 1, v___y_1272_);
lean_inc_ref(v___y_1278_);
lean_inc_ref(v___y_1274_);
v___x_1285_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1285_, 0, v___y_1274_);
lean_ctor_set(v___x_1285_, 1, v___y_1277_);
lean_ctor_set(v___x_1285_, 2, v___y_1276_);
lean_ctor_set(v___x_1285_, 3, v___y_1278_);
lean_ctor_set(v___x_1285_, 4, v___x_1284_);
lean_ctor_set_uint8(v___x_1285_, sizeof(void*)*5, v___y_1273_);
lean_ctor_set_uint8(v___x_1285_, sizeof(void*)*5 + 1, v___y_1275_);
lean_ctor_set_uint8(v___x_1285_, sizeof(void*)*5 + 2, v_isSilent_1267_);
v___x_1286_ = lean_st_ref_take(v___y_1280_);
v_env_1287_ = lean_ctor_get(v___x_1286_, 0);
v_nextMacroScope_1288_ = lean_ctor_get(v___x_1286_, 1);
v_ngen_1289_ = lean_ctor_get(v___x_1286_, 2);
v_auxDeclNGen_1290_ = lean_ctor_get(v___x_1286_, 3);
v_traceState_1291_ = lean_ctor_get(v___x_1286_, 4);
v_cache_1292_ = lean_ctor_get(v___x_1286_, 5);
v_recordedDeps_1293_ = lean_ctor_get(v___x_1286_, 6);
v_messages_1294_ = lean_ctor_get(v___x_1286_, 7);
v_infoState_1295_ = lean_ctor_get(v___x_1286_, 8);
v_snapshotTasks_1296_ = lean_ctor_get(v___x_1286_, 9);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1298_ = v___x_1286_;
v_isShared_1299_ = v_isSharedCheck_1307_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_snapshotTasks_1296_);
lean_inc(v_infoState_1295_);
lean_inc(v_messages_1294_);
lean_inc(v_recordedDeps_1293_);
lean_inc(v_cache_1292_);
lean_inc(v_traceState_1291_);
lean_inc(v_auxDeclNGen_1290_);
lean_inc(v_ngen_1289_);
lean_inc(v_nextMacroScope_1288_);
lean_inc(v_env_1287_);
lean_dec(v___x_1286_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1307_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1300_ = lean_box(0);
v___x_1301_ = l_Lean_MessageLog_add(v___x_1285_, v_messages_1294_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 7, v___x_1301_);
v___x_1303_ = v___x_1298_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_env_1287_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v_nextMacroScope_1288_);
lean_ctor_set(v_reuseFailAlloc_1306_, 2, v_ngen_1289_);
lean_ctor_set(v_reuseFailAlloc_1306_, 3, v_auxDeclNGen_1290_);
lean_ctor_set(v_reuseFailAlloc_1306_, 4, v_traceState_1291_);
lean_ctor_set(v_reuseFailAlloc_1306_, 5, v_cache_1292_);
lean_ctor_set(v_reuseFailAlloc_1306_, 6, v_recordedDeps_1293_);
lean_ctor_set(v_reuseFailAlloc_1306_, 7, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1306_, 8, v_infoState_1295_);
lean_ctor_set(v_reuseFailAlloc_1306_, 9, v_snapshotTasks_1296_);
v___x_1303_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = lean_st_ref_put(v___y_1280_, v___x_1303_);
v___x_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1300_);
return v___x_1305_;
}
}
}
v___jp_1308_:
{
lean_object* v_fileName_1317_; lean_object* v_fileMap_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1334_; 
v_fileName_1317_ = lean_ctor_get(v___y_1315_, 0);
v_fileMap_1318_ = lean_ctor_get(v___y_1315_, 1);
v___x_1319_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1265_);
v___x_1320_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v___x_1319_, v___y_1268_, v___y_1269_);
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1323_ = v___x_1320_;
v_isShared_1324_ = v_isSharedCheck_1334_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1334_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
lean_inc_ref_n(v_fileMap_1318_, 2);
v___x_1325_ = l_Lean_FileMap_toPosition(v_fileMap_1318_, v___y_1314_);
lean_dec(v___y_1314_);
v___x_1326_ = l_Lean_FileMap_toPosition(v_fileMap_1318_, v___y_1316_);
lean_dec(v___y_1316_);
v___x_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
v___x_1328_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___closed__0));
if (v___y_1312_ == 0)
{
lean_del_object(v___x_1323_);
lean_dec_ref(v___y_1310_);
v___y_1272_ = v_a_1321_;
v___y_1273_ = v___y_1311_;
v___y_1274_ = v_fileName_1317_;
v___y_1275_ = v___y_1313_;
v___y_1276_ = v___x_1327_;
v___y_1277_ = v___x_1325_;
v___y_1278_ = v___x_1328_;
v_toCold_1279_ = v___y_1309_;
v___y_1280_ = v___y_1269_;
goto v___jp_1271_;
}
else
{
uint8_t v___x_1329_; 
lean_inc(v_a_1321_);
v___x_1329_ = l_Lean_MessageData_hasTag(v___y_1310_, v_a_1321_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; lean_object* v___x_1332_; 
lean_dec_ref_known(v___x_1327_, 1);
lean_dec_ref(v___x_1325_);
lean_dec(v_a_1321_);
v___x_1330_ = lean_box(0);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1330_);
v___x_1332_ = v___x_1323_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
else
{
lean_del_object(v___x_1323_);
v___y_1272_ = v_a_1321_;
v___y_1273_ = v___y_1311_;
v___y_1274_ = v_fileName_1317_;
v___y_1275_ = v___y_1313_;
v___y_1276_ = v___x_1327_;
v___y_1277_ = v___x_1325_;
v___y_1278_ = v___x_1328_;
v_toCold_1279_ = v___y_1309_;
v___y_1280_ = v___y_1269_;
goto v___jp_1271_;
}
}
}
}
v___jp_1335_:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Lean_Syntax_getTailPos_x3f(v___y_1339_, v___y_1340_);
lean_dec(v___y_1339_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_inc(v___y_1342_);
v___y_1309_ = v___y_1337_;
v___y_1310_ = v___y_1338_;
v___y_1311_ = v___y_1340_;
v___y_1312_ = v___y_1336_;
v___y_1313_ = v___y_1341_;
v___y_1314_ = v___y_1342_;
v___y_1315_ = v___y_1337_;
v___y_1316_ = v___y_1342_;
goto v___jp_1308_;
}
else
{
lean_object* v_val_1344_; 
v_val_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_val_1344_);
lean_dec_ref_known(v___x_1343_, 1);
v___y_1309_ = v___y_1337_;
v___y_1310_ = v___y_1338_;
v___y_1311_ = v___y_1340_;
v___y_1312_ = v___y_1336_;
v___y_1313_ = v___y_1341_;
v___y_1314_ = v___y_1342_;
v___y_1315_ = v___y_1337_;
v___y_1316_ = v_val_1344_;
goto v___jp_1308_;
}
}
v___jp_1345_:
{
lean_object* v_toCold_1348_; lean_object* v_ref_1349_; uint8_t v_suppressElabErrors_1350_; lean_object* v___x_1351_; lean_object* v___f_1352_; lean_object* v_ref_1353_; lean_object* v___x_1354_; 
v_toCold_1348_ = lean_ctor_get(v___y_1268_, 0);
v_ref_1349_ = lean_ctor_get(v___y_1268_, 2);
v_suppressElabErrors_1350_ = lean_ctor_get_uint8(v___y_1268_, sizeof(void*)*3 + 2);
v___x_1351_ = lean_box(v_suppressElabErrors_1350_);
v___f_1352_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1352_, 0, v___x_1351_);
v_ref_1353_ = l_Lean_replaceRef(v_ref_1264_, v_ref_1349_);
v___x_1354_ = l_Lean_Syntax_getPos_x3f(v_ref_1353_, v___y_1346_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_unsigned_to_nat(0u);
v___y_1336_ = v_suppressElabErrors_1350_;
v___y_1337_ = v_toCold_1348_;
v___y_1338_ = v___f_1352_;
v___y_1339_ = v_ref_1353_;
v___y_1340_ = v___y_1346_;
v___y_1341_ = v___y_1347_;
v___y_1342_ = v___x_1355_;
goto v___jp_1335_;
}
else
{
lean_object* v_val_1356_; 
v_val_1356_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_val_1356_);
lean_dec_ref_known(v___x_1354_, 1);
v___y_1336_ = v_suppressElabErrors_1350_;
v___y_1337_ = v_toCold_1348_;
v___y_1338_ = v___f_1352_;
v___y_1339_ = v_ref_1353_;
v___y_1340_ = v___y_1346_;
v___y_1341_ = v___y_1347_;
v___y_1342_ = v_val_1356_;
goto v___jp_1335_;
}
}
v___jp_1358_:
{
uint8_t v___x_1360_; uint8_t v___x_1361_; 
v___x_1360_ = 1;
v___x_1361_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1266_, v___x_1360_);
if (v___x_1361_ == 0)
{
v___y_1346_ = v___y_1359_;
v___y_1347_ = v_severity_1266_;
goto v___jp_1345_;
}
else
{
lean_object* v___x_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v___x_1362_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1268_);
v___x_1363_ = l_Lean_warningAsError;
v___x_1364_ = l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(v___x_1362_, v___x_1363_);
lean_dec_ref(v___x_1362_);
if (v___x_1364_ == 0)
{
v___y_1346_ = v___y_1359_;
v___y_1347_ = v_severity_1266_;
goto v___jp_1345_;
}
else
{
v___y_1346_ = v___y_1359_;
v___y_1347_ = v___x_1357_;
goto v___jp_1345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___boxed(lean_object* v_ref_1369_, lean_object* v_msgData_1370_, lean_object* v_severity_1371_, lean_object* v_isSilent_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
uint8_t v_severity_boxed_1376_; uint8_t v_isSilent_boxed_1377_; lean_object* v_res_1378_; 
v_severity_boxed_1376_ = lean_unbox(v_severity_1371_);
v_isSilent_boxed_1377_ = lean_unbox(v_isSilent_1372_);
v_res_1378_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44(v_ref_1369_, v_msgData_1370_, v_severity_boxed_1376_, v_isSilent_boxed_1377_, v___y_1373_, v___y_1374_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec(v_ref_1369_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30(lean_object* v_msgData_1379_, uint8_t v_severity_1380_, uint8_t v_isSilent_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_ref_1385_; lean_object* v___x_1386_; 
v_ref_1385_ = lean_ctor_get(v___y_1382_, 2);
v___x_1386_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44(v_ref_1385_, v_msgData_1379_, v_severity_1380_, v_isSilent_1381_, v___y_1382_, v___y_1383_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30___boxed(lean_object* v_msgData_1387_, lean_object* v_severity_1388_, lean_object* v_isSilent_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
uint8_t v_severity_boxed_1393_; uint8_t v_isSilent_boxed_1394_; lean_object* v_res_1395_; 
v_severity_boxed_1393_ = lean_unbox(v_severity_1388_);
v_isSilent_boxed_1394_ = lean_unbox(v_isSilent_1389_);
v_res_1395_ = l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30(v_msgData_1387_, v_severity_boxed_1393_, v_isSilent_boxed_1394_, v___y_1390_, v___y_1391_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13(lean_object* v_msgData_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
uint8_t v___x_1400_; uint8_t v___x_1401_; lean_object* v___x_1402_; 
v___x_1400_ = 2;
v___x_1401_ = 0;
v___x_1402_ = l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30(v_msgData_1396_, v___x_1400_, v___x_1401_, v___y_1397_, v___y_1398_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13___boxed(lean_object* v_msgData_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_logError___at___00main_spec__13(v_msgData_1403_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(lean_object* v_opts_1408_, lean_object* v_opt_1409_){
_start:
{
lean_object* v_name_1410_; lean_object* v_map_1411_; lean_object* v___x_1412_; 
v_name_1410_ = lean_ctor_get(v_opt_1409_, 0);
v_map_1411_ = lean_ctor_get(v_opts_1408_, 0);
v___x_1412_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1411_, v_name_1410_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v___x_1413_; 
v___x_1413_ = lean_box(0);
return v___x_1413_;
}
else
{
lean_object* v_val_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1423_; 
v_val_1414_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1416_ = v___x_1412_;
v_isShared_1417_ = v_isSharedCheck_1423_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_val_1414_);
lean_dec(v___x_1412_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1423_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
if (lean_obj_tag(v_val_1414_) == 0)
{
lean_object* v_v_1418_; lean_object* v___x_1420_; 
v_v_1418_ = lean_ctor_get(v_val_1414_, 0);
lean_inc_ref(v_v_1418_);
lean_dec_ref_known(v_val_1414_, 1);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v_v_1418_);
v___x_1420_ = v___x_1416_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_v_1418_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
else
{
lean_object* v___x_1422_; 
lean_del_object(v___x_1416_);
lean_dec(v_val_1414_);
v___x_1422_ = lean_box(0);
return v___x_1422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___boxed(lean_object* v_opts_1424_, lean_object* v_opt_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(v_opts_1424_, v_opt_1425_);
lean_dec_ref(v_opt_1425_);
lean_dec_ref(v_opts_1424_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22(lean_object* v_x_1427_, lean_object* v_x_1428_){
_start:
{
if (lean_obj_tag(v_x_1428_) == 0)
{
return v_x_1427_;
}
else
{
lean_object* v_key_1429_; lean_object* v_value_1430_; lean_object* v_tail_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v_key_1429_ = lean_ctor_get(v_x_1428_, 0);
v_value_1430_ = lean_ctor_get(v_x_1428_, 1);
v_tail_1431_ = lean_ctor_get(v_x_1428_, 2);
lean_inc(v_value_1430_);
lean_inc(v_key_1429_);
v___x_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1432_, 0, v_key_1429_);
lean_ctor_set(v___x_1432_, 1, v_value_1430_);
v___x_1433_ = lean_array_push(v_x_1427_, v___x_1432_);
v_x_1427_ = v___x_1433_;
v_x_1428_ = v_tail_1431_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22___boxed(lean_object* v_x_1435_, lean_object* v_x_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22(v_x_1435_, v_x_1436_);
lean_dec(v_x_1436_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23(lean_object* v_as_1438_, size_t v_i_1439_, size_t v_stop_1440_, lean_object* v_b_1441_){
_start:
{
uint8_t v___x_1442_; 
v___x_1442_ = lean_usize_dec_eq(v_i_1439_, v_stop_1440_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; lean_object* v___x_1444_; size_t v___x_1445_; size_t v___x_1446_; 
v___x_1443_ = lean_array_uget_borrowed(v_as_1438_, v_i_1439_);
v___x_1444_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22(v_b_1441_, v___x_1443_);
v___x_1445_ = ((size_t)1ULL);
v___x_1446_ = lean_usize_add(v_i_1439_, v___x_1445_);
v_i_1439_ = v___x_1446_;
v_b_1441_ = v___x_1444_;
goto _start;
}
else
{
return v_b_1441_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23___boxed(lean_object* v_as_1448_, lean_object* v_i_1449_, lean_object* v_stop_1450_, lean_object* v_b_1451_){
_start:
{
size_t v_i_boxed_1452_; size_t v_stop_boxed_1453_; lean_object* v_res_1454_; 
v_i_boxed_1452_ = lean_unbox_usize(v_i_1449_);
lean_dec(v_i_1449_);
v_stop_boxed_1453_ = lean_unbox_usize(v_stop_1450_);
lean_dec(v_stop_1450_);
v_res_1454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23(v_as_1448_, v_i_boxed_1452_, v_stop_boxed_1453_, v_b_1451_);
lean_dec_ref(v_as_1448_);
return v_res_1454_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(lean_object* v_x_1455_, lean_object* v_x_1456_){
_start:
{
lean_object* v_fst_1457_; lean_object* v_fst_1458_; lean_object* v_fst_1459_; lean_object* v_fst_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; 
v_fst_1457_ = lean_ctor_get(v_x_1455_, 0);
v_fst_1458_ = lean_ctor_get(v_x_1456_, 0);
v_fst_1459_ = lean_ctor_get(v_fst_1457_, 0);
v_fst_1460_ = lean_ctor_get(v_fst_1458_, 0);
v___x_1461_ = lean_unsigned_to_nat(1u);
v___x_1462_ = lean_nat_add(v_fst_1459_, v___x_1461_);
v___x_1463_ = lean_nat_dec_le(v___x_1462_, v_fst_1460_);
lean_dec(v___x_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0___boxed(lean_object* v_x_1464_, lean_object* v_x_1465_){
_start:
{
uint8_t v_res_1466_; lean_object* v_r_1467_; 
v_res_1466_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v_x_1464_, v_x_1465_);
lean_dec_ref(v_x_1465_);
lean_dec_ref(v_x_1464_);
v_r_1467_ = lean_box(v_res_1466_);
return v_r_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(lean_object* v_hi_1468_, lean_object* v_pivot_1469_, lean_object* v_as_1470_, lean_object* v_i_1471_, lean_object* v_k_1472_){
_start:
{
uint8_t v___x_1473_; 
v___x_1473_ = lean_nat_dec_lt(v_k_1472_, v_hi_1468_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
lean_dec(v_k_1472_);
v___x_1474_ = lean_array_fswap(v_as_1470_, v_i_1471_, v_hi_1468_);
v___x_1475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1475_, 0, v_i_1471_);
lean_ctor_set(v___x_1475_, 1, v___x_1474_);
return v___x_1475_;
}
else
{
lean_object* v___x_1476_; lean_object* v_fst_1477_; lean_object* v_fst_1478_; lean_object* v_fst_1479_; lean_object* v_fst_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; uint8_t v___x_1483_; 
v___x_1476_ = lean_array_fget_borrowed(v_as_1470_, v_k_1472_);
v_fst_1477_ = lean_ctor_get(v___x_1476_, 0);
v_fst_1478_ = lean_ctor_get(v_pivot_1469_, 0);
v_fst_1479_ = lean_ctor_get(v_fst_1477_, 0);
v_fst_1480_ = lean_ctor_get(v_fst_1478_, 0);
v___x_1481_ = lean_unsigned_to_nat(1u);
v___x_1482_ = lean_nat_add(v_fst_1479_, v___x_1481_);
v___x_1483_ = lean_nat_dec_le(v___x_1482_, v_fst_1480_);
lean_dec(v___x_1482_);
if (v___x_1483_ == 0)
{
lean_object* v___x_1484_; 
v___x_1484_ = lean_nat_add(v_k_1472_, v___x_1481_);
lean_dec(v_k_1472_);
v_k_1472_ = v___x_1484_;
goto _start;
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1486_ = lean_array_fswap(v_as_1470_, v_i_1471_, v_k_1472_);
v___x_1487_ = lean_nat_add(v_i_1471_, v___x_1481_);
lean_dec(v_i_1471_);
v___x_1488_ = lean_nat_add(v_k_1472_, v___x_1481_);
lean_dec(v_k_1472_);
v_as_1470_ = v___x_1486_;
v_i_1471_ = v___x_1487_;
v_k_1472_ = v___x_1488_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg___boxed(lean_object* v_hi_1490_, lean_object* v_pivot_1491_, lean_object* v_as_1492_, lean_object* v_i_1493_, lean_object* v_k_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(v_hi_1490_, v_pivot_1491_, v_as_1492_, v_i_1493_, v_k_1494_);
lean_dec_ref(v_pivot_1491_);
lean_dec(v_hi_1490_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(lean_object* v_n_1496_, lean_object* v_as_1497_, lean_object* v_lo_1498_, lean_object* v_hi_1499_){
_start:
{
lean_object* v___y_1501_; uint8_t v___x_1511_; 
v___x_1511_ = lean_nat_dec_lt(v_lo_1498_, v_hi_1499_);
if (v___x_1511_ == 0)
{
lean_dec(v_lo_1498_);
return v_as_1497_;
}
else
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v_mid_1514_; lean_object* v___y_1516_; lean_object* v___y_1522_; lean_object* v___x_1527_; lean_object* v___x_1528_; uint8_t v___x_1529_; 
v___x_1512_ = lean_nat_add(v_lo_1498_, v_hi_1499_);
v___x_1513_ = lean_unsigned_to_nat(1u);
v_mid_1514_ = lean_nat_shiftr(v___x_1512_, v___x_1513_);
lean_dec(v___x_1512_);
v___x_1527_ = lean_array_fget_borrowed(v_as_1497_, v_mid_1514_);
v___x_1528_ = lean_array_fget_borrowed(v_as_1497_, v_lo_1498_);
v___x_1529_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v___x_1527_, v___x_1528_);
if (v___x_1529_ == 0)
{
v___y_1522_ = v_as_1497_;
goto v___jp_1521_;
}
else
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_array_fswap(v_as_1497_, v_lo_1498_, v_mid_1514_);
v___y_1522_ = v___x_1530_;
goto v___jp_1521_;
}
v___jp_1515_:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; 
v___x_1517_ = lean_array_fget_borrowed(v___y_1516_, v_mid_1514_);
v___x_1518_ = lean_array_fget_borrowed(v___y_1516_, v_hi_1499_);
v___x_1519_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v___x_1517_, v___x_1518_);
if (v___x_1519_ == 0)
{
lean_dec(v_mid_1514_);
v___y_1501_ = v___y_1516_;
goto v___jp_1500_;
}
else
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_array_fswap(v___y_1516_, v_mid_1514_, v_hi_1499_);
lean_dec(v_mid_1514_);
v___y_1501_ = v___x_1520_;
goto v___jp_1500_;
}
}
v___jp_1521_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; 
v___x_1523_ = lean_array_fget_borrowed(v___y_1522_, v_hi_1499_);
v___x_1524_ = lean_array_fget_borrowed(v___y_1522_, v_lo_1498_);
v___x_1525_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___lam__0(v___x_1523_, v___x_1524_);
if (v___x_1525_ == 0)
{
v___y_1516_ = v___y_1522_;
goto v___jp_1515_;
}
else
{
lean_object* v___x_1526_; 
v___x_1526_ = lean_array_fswap(v___y_1522_, v_lo_1498_, v_hi_1499_);
v___y_1516_ = v___x_1526_;
goto v___jp_1515_;
}
}
}
v___jp_1500_:
{
lean_object* v_pivot_1502_; lean_object* v___x_1503_; lean_object* v_fst_1504_; lean_object* v_snd_1505_; uint8_t v___x_1506_; 
v_pivot_1502_ = lean_array_fget(v___y_1501_, v_hi_1499_);
lean_inc_n(v_lo_1498_, 2);
v___x_1503_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(v_hi_1499_, v_pivot_1502_, v___y_1501_, v_lo_1498_, v_lo_1498_);
lean_dec(v_pivot_1502_);
v_fst_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_fst_1504_);
v_snd_1505_ = lean_ctor_get(v___x_1503_, 1);
lean_inc(v_snd_1505_);
lean_dec_ref(v___x_1503_);
v___x_1506_ = lean_nat_dec_le(v_hi_1499_, v_fst_1504_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1507_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v_n_1496_, v_snd_1505_, v_lo_1498_, v_fst_1504_);
v___x_1508_ = lean_unsigned_to_nat(1u);
v___x_1509_ = lean_nat_add(v_fst_1504_, v___x_1508_);
lean_dec(v_fst_1504_);
v_as_1497_ = v___x_1507_;
v_lo_1498_ = v___x_1509_;
goto _start;
}
else
{
lean_dec(v_fst_1504_);
lean_dec(v_lo_1498_);
return v_snd_1505_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg___boxed(lean_object* v_n_1531_, lean_object* v_as_1532_, lean_object* v_lo_1533_, lean_object* v_hi_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v_n_1531_, v_as_1532_, v_lo_1533_, v_hi_1534_);
lean_dec(v_hi_1534_);
lean_dec(v_n_1531_);
return v_res_1535_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0(uint8_t v_suppressElabErrors_1536_, uint8_t v___x_1537_, lean_object* v___x_1538_, lean_object* v_x_1539_){
_start:
{
if (lean_obj_tag(v_x_1539_) == 1)
{
lean_object* v_pre_1540_; 
v_pre_1540_ = lean_ctor_get(v_x_1539_, 0);
switch(lean_obj_tag(v_pre_1540_))
{
case 1:
{
lean_object* v_pre_1541_; 
v_pre_1541_ = lean_ctor_get(v_pre_1540_, 0);
switch(lean_obj_tag(v_pre_1541_))
{
case 0:
{
lean_object* v_str_1542_; lean_object* v_str_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; 
v_str_1542_ = lean_ctor_get(v_x_1539_, 1);
v_str_1543_ = lean_ctor_get(v_pre_1540_, 1);
v___x_1544_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__0));
v___x_1545_ = lean_string_dec_eq(v_str_1543_, v___x_1544_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; uint8_t v___x_1547_; 
v___x_1546_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__1));
v___x_1547_ = lean_string_dec_eq(v_str_1543_, v___x_1546_);
if (v___x_1547_ == 0)
{
return v___x_1547_;
}
else
{
lean_object* v___x_1548_; uint8_t v___x_1549_; 
v___x_1548_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__2));
v___x_1549_ = lean_string_dec_eq(v_str_1542_, v___x_1548_);
if (v___x_1549_ == 0)
{
return v___x_1549_;
}
else
{
return v_suppressElabErrors_1536_;
}
}
}
else
{
lean_object* v___x_1550_; uint8_t v___x_1551_; 
v___x_1550_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__3));
v___x_1551_ = lean_string_dec_eq(v_str_1542_, v___x_1550_);
if (v___x_1551_ == 0)
{
return v___x_1551_;
}
else
{
return v_suppressElabErrors_1536_;
}
}
}
case 1:
{
lean_object* v_pre_1552_; 
v_pre_1552_ = lean_ctor_get(v_pre_1541_, 0);
if (lean_obj_tag(v_pre_1552_) == 0)
{
lean_object* v_str_1553_; lean_object* v_str_1554_; lean_object* v_str_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v_str_1553_ = lean_ctor_get(v_x_1539_, 1);
v_str_1554_ = lean_ctor_get(v_pre_1540_, 1);
v_str_1555_ = lean_ctor_get(v_pre_1541_, 1);
v___x_1556_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__4));
v___x_1557_ = lean_string_dec_eq(v_str_1555_, v___x_1556_);
if (v___x_1557_ == 0)
{
return v___x_1557_;
}
else
{
lean_object* v___x_1558_; uint8_t v___x_1559_; 
v___x_1558_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__5));
v___x_1559_ = lean_string_dec_eq(v_str_1554_, v___x_1558_);
if (v___x_1559_ == 0)
{
return v___x_1559_;
}
else
{
lean_object* v___x_1560_; uint8_t v___x_1561_; 
v___x_1560_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___lam__0___closed__6));
v___x_1561_ = lean_string_dec_eq(v_str_1553_, v___x_1560_);
if (v___x_1561_ == 0)
{
return v___x_1561_;
}
else
{
return v_suppressElabErrors_1536_;
}
}
}
}
else
{
return v___x_1537_;
}
}
default: 
{
return v___x_1537_;
}
}
}
case 0:
{
lean_object* v_str_1562_; uint8_t v___x_1563_; 
v_str_1562_ = lean_ctor_get(v_x_1539_, 1);
v___x_1563_ = lean_string_dec_eq(v_str_1562_, v___x_1538_);
if (v___x_1563_ == 0)
{
return v___x_1563_;
}
else
{
return v_suppressElabErrors_1536_;
}
}
default: 
{
return v___x_1537_;
}
}
}
else
{
return v___x_1537_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0___boxed(lean_object* v_suppressElabErrors_1564_, lean_object* v___x_1565_, lean_object* v___x_1566_, lean_object* v_x_1567_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1568_; uint8_t v___x_38705__boxed_1569_; uint8_t v_res_1570_; lean_object* v_r_1571_; 
v_suppressElabErrors_boxed_1568_ = lean_unbox(v_suppressElabErrors_1564_);
v___x_38705__boxed_1569_ = lean_unbox(v___x_1565_);
v_res_1570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0(v_suppressElabErrors_boxed_1568_, v___x_38705__boxed_1569_, v___x_1566_, v_x_1567_);
lean_dec(v_x_1567_);
lean_dec_ref(v___x_1566_);
v_r_1571_ = lean_box(v_res_1570_);
return v_r_1571_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0(void){
_start:
{
lean_object* v___x_1572_; double v___x_1573_; 
v___x_1572_ = lean_unsigned_to_nat(0u);
v___x_1573_ = lean_float_of_nat(v___x_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(uint8_t v___x_1574_, lean_object* v_as_1575_, size_t v_sz_1576_, size_t v_i_1577_, lean_object* v_b_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v_a_1583_; uint8_t v___x_1587_; 
v___x_1587_ = lean_usize_dec_lt(v_i_1577_, v_sz_1576_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; 
v___x_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1588_, 0, v_b_1578_);
return v___x_1588_;
}
else
{
lean_object* v_a_1589_; lean_object* v_fst_1590_; lean_object* v_snd_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1670_; 
v_a_1589_ = lean_array_uget(v_as_1575_, v_i_1577_);
v_fst_1590_ = lean_ctor_get(v_a_1589_, 0);
v_snd_1591_ = lean_ctor_get(v_a_1589_, 1);
v_isSharedCheck_1670_ = !lean_is_exclusive(v_a_1589_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1593_ = v_a_1589_;
v_isShared_1594_ = v_isSharedCheck_1670_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_snd_1591_);
lean_inc(v_fst_1590_);
lean_dec(v_a_1589_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1670_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v_fst_1595_; lean_object* v_snd_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1669_; 
v_fst_1595_ = lean_ctor_get(v_fst_1590_, 0);
v_snd_1596_ = lean_ctor_get(v_fst_1590_, 1);
v_isSharedCheck_1669_ = !lean_is_exclusive(v_fst_1590_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1598_ = v_fst_1590_;
v_isShared_1599_ = v_isSharedCheck_1669_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_snd_1596_);
lean_inc(v_fst_1595_);
lean_dec(v_fst_1590_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1669_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; double v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v_toCold_1605_; uint8_t v_suppressElabErrors_1606_; lean_object* v_fileName_1607_; lean_object* v_fileMap_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1615_; 
v___x_1600_ = lean_box(0);
v___x_1601_ = lean_box(0);
v___x_1602_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___closed__0);
v___x_1603_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__30_spec__44___closed__0));
v___x_1604_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1604_, 0, v___x_1600_);
lean_ctor_set(v___x_1604_, 1, v___x_1601_);
lean_ctor_set(v___x_1604_, 2, v___x_1603_);
lean_ctor_set_float(v___x_1604_, sizeof(void*)*3, v___x_1602_);
lean_ctor_set_float(v___x_1604_, sizeof(void*)*3 + 8, v___x_1602_);
lean_ctor_set_uint8(v___x_1604_, sizeof(void*)*3 + 16, v___x_1587_);
v_toCold_1605_ = lean_ctor_get(v___y_1579_, 0);
v_suppressElabErrors_1606_ = lean_ctor_get_uint8(v___y_1579_, sizeof(void*)*3 + 2);
v_fileName_1607_ = lean_ctor_get(v_toCold_1605_, 0);
v_fileMap_1608_ = lean_ctor_get(v_toCold_1605_, 1);
v___x_1609_ = lean_box(0);
v___x_1610_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_1611_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_1612_ = l_Lean_MessageData_nil;
v___x_1613_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1604_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
lean_ctor_set(v___x_1613_, 2, v_snd_1591_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set_tag(v___x_1598_, 8);
lean_ctor_set(v___x_1598_, 1, v___x_1613_);
lean_ctor_set(v___x_1598_, 0, v___x_1611_);
v___x_1615_ = v___x_1598_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v___x_1613_);
v___x_1615_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
uint8_t v___x_1616_; lean_object* v___x_1617_; lean_object* v___y_1619_; lean_object* v___y_1620_; 
v___x_1616_ = 0;
lean_inc_ref(v_fileMap_1608_);
lean_inc_ref(v_fileName_1607_);
v___x_1617_ = l_Lean_Elab_mkMessageCore(v_fileName_1607_, v_fileMap_1608_, v___x_1615_, v___x_1616_, v_fst_1595_, v_snd_1596_);
lean_dec(v_snd_1596_);
lean_dec(v_fst_1595_);
if (v_suppressElabErrors_1606_ == 0)
{
v___y_1619_ = v___y_1579_;
v___y_1620_ = v___y_1580_;
goto v___jp_1618_;
}
else
{
lean_object* v_data_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___f_1666_; uint8_t v___x_1667_; 
v_data_1663_ = lean_ctor_get(v___x_1617_, 4);
v___x_1664_ = lean_box(v_suppressElabErrors_1606_);
v___x_1665_ = lean_box(v___x_1574_);
v___f_1666_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1666_, 0, v___x_1664_);
lean_closure_set(v___f_1666_, 1, v___x_1665_);
lean_closure_set(v___f_1666_, 2, v___x_1610_);
lean_inc(v_data_1663_);
v___x_1667_ = l_Lean_MessageData_hasTag(v___f_1666_, v_data_1663_);
if (v___x_1667_ == 0)
{
lean_dec_ref(v___x_1617_);
lean_del_object(v___x_1593_);
v_a_1583_ = v___x_1609_;
goto v___jp_1582_;
}
else
{
v___y_1619_ = v___y_1579_;
v___y_1620_ = v___y_1580_;
goto v___jp_1618_;
}
}
v___jp_1618_:
{
lean_object* v_toCold_1621_; lean_object* v_fileName_1622_; lean_object* v_pos_1623_; lean_object* v_endPos_1624_; uint8_t v_keepFullRange_1625_; uint8_t v_severity_1626_; uint8_t v_isSilent_1627_; lean_object* v_caption_1628_; lean_object* v_data_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1662_; 
v_toCold_1621_ = lean_ctor_get(v___y_1619_, 0);
v_fileName_1622_ = lean_ctor_get(v___x_1617_, 0);
v_pos_1623_ = lean_ctor_get(v___x_1617_, 1);
v_endPos_1624_ = lean_ctor_get(v___x_1617_, 2);
v_keepFullRange_1625_ = lean_ctor_get_uint8(v___x_1617_, sizeof(void*)*5);
v_severity_1626_ = lean_ctor_get_uint8(v___x_1617_, sizeof(void*)*5 + 1);
v_isSilent_1627_ = lean_ctor_get_uint8(v___x_1617_, sizeof(void*)*5 + 2);
v_caption_1628_ = lean_ctor_get(v___x_1617_, 3);
v_data_1629_ = lean_ctor_get(v___x_1617_, 4);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1631_ = v___x_1617_;
v_isShared_1632_ = v_isSharedCheck_1662_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_data_1629_);
lean_inc(v_caption_1628_);
lean_inc(v_endPos_1624_);
lean_inc(v_pos_1623_);
lean_inc(v_fileName_1622_);
lean_dec(v___x_1617_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1662_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v_currNamespace_1633_; lean_object* v_openDecls_1634_; lean_object* v___x_1636_; 
v_currNamespace_1633_ = lean_ctor_get(v_toCold_1621_, 4);
v_openDecls_1634_ = lean_ctor_get(v_toCold_1621_, 5);
lean_inc(v_openDecls_1634_);
lean_inc(v_currNamespace_1633_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 1, v_openDecls_1634_);
lean_ctor_set(v___x_1593_, 0, v_currNamespace_1633_);
v___x_1636_ = v___x_1593_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_currNamespace_1633_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_openDecls_1634_);
v___x_1636_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v___x_1637_; lean_object* v___x_1639_; 
v___x_1637_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
lean_ctor_set(v___x_1637_, 1, v_data_1629_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 4, v___x_1637_);
v___x_1639_ = v___x_1631_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_fileName_1622_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_pos_1623_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v_endPos_1624_);
lean_ctor_set(v_reuseFailAlloc_1660_, 3, v_caption_1628_);
lean_ctor_set(v_reuseFailAlloc_1660_, 4, v___x_1637_);
lean_ctor_set_uint8(v_reuseFailAlloc_1660_, sizeof(void*)*5, v_keepFullRange_1625_);
lean_ctor_set_uint8(v_reuseFailAlloc_1660_, sizeof(void*)*5 + 1, v_severity_1626_);
lean_ctor_set_uint8(v_reuseFailAlloc_1660_, sizeof(void*)*5 + 2, v_isSilent_1627_);
v___x_1639_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
lean_object* v___x_1640_; lean_object* v_env_1641_; lean_object* v_nextMacroScope_1642_; lean_object* v_ngen_1643_; lean_object* v_auxDeclNGen_1644_; lean_object* v_traceState_1645_; lean_object* v_cache_1646_; lean_object* v_recordedDeps_1647_; lean_object* v_messages_1648_; lean_object* v_infoState_1649_; lean_object* v_snapshotTasks_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1659_; 
v___x_1640_ = lean_st_ref_take(v___y_1620_);
v_env_1641_ = lean_ctor_get(v___x_1640_, 0);
v_nextMacroScope_1642_ = lean_ctor_get(v___x_1640_, 1);
v_ngen_1643_ = lean_ctor_get(v___x_1640_, 2);
v_auxDeclNGen_1644_ = lean_ctor_get(v___x_1640_, 3);
v_traceState_1645_ = lean_ctor_get(v___x_1640_, 4);
v_cache_1646_ = lean_ctor_get(v___x_1640_, 5);
v_recordedDeps_1647_ = lean_ctor_get(v___x_1640_, 6);
v_messages_1648_ = lean_ctor_get(v___x_1640_, 7);
v_infoState_1649_ = lean_ctor_get(v___x_1640_, 8);
v_snapshotTasks_1650_ = lean_ctor_get(v___x_1640_, 9);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1652_ = v___x_1640_;
v_isShared_1653_ = v_isSharedCheck_1659_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_snapshotTasks_1650_);
lean_inc(v_infoState_1649_);
lean_inc(v_messages_1648_);
lean_inc(v_recordedDeps_1647_);
lean_inc(v_cache_1646_);
lean_inc(v_traceState_1645_);
lean_inc(v_auxDeclNGen_1644_);
lean_inc(v_ngen_1643_);
lean_inc(v_nextMacroScope_1642_);
lean_inc(v_env_1641_);
lean_dec(v___x_1640_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1659_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1654_; lean_object* v___x_1656_; 
v___x_1654_ = l_Lean_MessageLog_add(v___x_1639_, v_messages_1648_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 7, v___x_1654_);
v___x_1656_ = v___x_1652_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_env_1641_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v_nextMacroScope_1642_);
lean_ctor_set(v_reuseFailAlloc_1658_, 2, v_ngen_1643_);
lean_ctor_set(v_reuseFailAlloc_1658_, 3, v_auxDeclNGen_1644_);
lean_ctor_set(v_reuseFailAlloc_1658_, 4, v_traceState_1645_);
lean_ctor_set(v_reuseFailAlloc_1658_, 5, v_cache_1646_);
lean_ctor_set(v_reuseFailAlloc_1658_, 6, v_recordedDeps_1647_);
lean_ctor_set(v_reuseFailAlloc_1658_, 7, v___x_1654_);
lean_ctor_set(v_reuseFailAlloc_1658_, 8, v_infoState_1649_);
lean_ctor_set(v_reuseFailAlloc_1658_, 9, v_snapshotTasks_1650_);
v___x_1656_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
lean_object* v___x_1657_; 
v___x_1657_ = lean_st_ref_put(v___y_1620_, v___x_1656_);
v_a_1583_ = v___x_1609_;
goto v___jp_1582_;
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
v___jp_1582_:
{
size_t v___x_1584_; size_t v___x_1585_; 
v___x_1584_ = ((size_t)1ULL);
v___x_1585_ = lean_usize_add(v_i_1577_, v___x_1584_);
v_i_1577_ = v___x_1585_;
v_b_1578_ = v_a_1583_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___boxed(lean_object* v___x_1671_, lean_object* v_as_1672_, lean_object* v_sz_1673_, lean_object* v_i_1674_, lean_object* v_b_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
uint8_t v___x_38770__boxed_1679_; size_t v_sz_boxed_1680_; size_t v_i_boxed_1681_; lean_object* v_res_1682_; 
v___x_38770__boxed_1679_ = lean_unbox(v___x_1671_);
v_sz_boxed_1680_ = lean_unbox_usize(v_sz_1673_);
lean_dec(v_sz_1673_);
v_i_boxed_1681_ = lean_unbox_usize(v_i_1674_);
lean_dec(v_i_1674_);
v_res_1682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(v___x_38770__boxed_1679_, v_as_1672_, v_sz_boxed_1680_, v_i_boxed_1681_, v_b_1675_, v___y_1676_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec_ref(v_as_1672_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(lean_object* v_a_1683_, lean_object* v_fallback_1684_, lean_object* v_x_1685_){
_start:
{
if (lean_obj_tag(v_x_1685_) == 0)
{
lean_inc(v_fallback_1684_);
return v_fallback_1684_;
}
else
{
lean_object* v_key_1686_; lean_object* v_value_1687_; lean_object* v_tail_1688_; lean_object* v_fst_1689_; lean_object* v_snd_1690_; lean_object* v_fst_1691_; lean_object* v_snd_1692_; uint8_t v_decide_1693_; 
v_key_1686_ = lean_ctor_get(v_x_1685_, 0);
v_value_1687_ = lean_ctor_get(v_x_1685_, 1);
v_tail_1688_ = lean_ctor_get(v_x_1685_, 2);
v_fst_1689_ = lean_ctor_get(v_key_1686_, 0);
v_snd_1690_ = lean_ctor_get(v_key_1686_, 1);
v_fst_1691_ = lean_ctor_get(v_a_1683_, 0);
v_snd_1692_ = lean_ctor_get(v_a_1683_, 1);
v_decide_1693_ = lean_nat_dec_eq(v_fst_1689_, v_fst_1691_);
if (v_decide_1693_ == 0)
{
v_x_1685_ = v_tail_1688_;
goto _start;
}
else
{
uint8_t v_decide_1695_; 
v_decide_1695_ = lean_nat_dec_eq(v_snd_1690_, v_snd_1692_);
if (v_decide_1695_ == 0)
{
v_x_1685_ = v_tail_1688_;
goto _start;
}
else
{
lean_inc(v_value_1687_);
return v_value_1687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg___boxed(lean_object* v_a_1697_, lean_object* v_fallback_1698_, lean_object* v_x_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(v_a_1697_, v_fallback_1698_, v_x_1699_);
lean_dec(v_x_1699_);
lean_dec(v_fallback_1698_);
lean_dec_ref(v_a_1697_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(lean_object* v_m_1701_, lean_object* v_a_1702_, lean_object* v_fallback_1703_){
_start:
{
lean_object* v_buckets_1704_; lean_object* v_fst_1705_; lean_object* v_snd_1706_; lean_object* v___x_1707_; uint64_t v___x_1708_; uint64_t v___x_1709_; uint64_t v___x_1710_; uint64_t v___x_1711_; uint64_t v___x_1712_; uint64_t v_fold_1713_; uint64_t v___x_1714_; uint64_t v___x_1715_; uint64_t v___x_1716_; size_t v___x_1717_; size_t v___x_1718_; size_t v___x_1719_; size_t v___x_1720_; size_t v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v_buckets_1704_ = lean_ctor_get(v_m_1701_, 1);
v_fst_1705_ = lean_ctor_get(v_a_1702_, 0);
v_snd_1706_ = lean_ctor_get(v_a_1702_, 1);
v___x_1707_ = lean_array_get_size(v_buckets_1704_);
v___x_1708_ = l_String_instHashableRaw_hash(v_fst_1705_);
v___x_1709_ = l_String_instHashableRaw_hash(v_snd_1706_);
v___x_1710_ = lean_uint64_mix_hash(v___x_1708_, v___x_1709_);
v___x_1711_ = 32ULL;
v___x_1712_ = lean_uint64_shift_right(v___x_1710_, v___x_1711_);
v_fold_1713_ = lean_uint64_xor(v___x_1710_, v___x_1712_);
v___x_1714_ = 16ULL;
v___x_1715_ = lean_uint64_shift_right(v_fold_1713_, v___x_1714_);
v___x_1716_ = lean_uint64_xor(v_fold_1713_, v___x_1715_);
v___x_1717_ = lean_uint64_to_usize(v___x_1716_);
v___x_1718_ = lean_usize_of_nat(v___x_1707_);
v___x_1719_ = ((size_t)1ULL);
v___x_1720_ = lean_usize_sub(v___x_1718_, v___x_1719_);
v___x_1721_ = lean_usize_land(v___x_1717_, v___x_1720_);
v___x_1722_ = lean_array_uget_borrowed(v_buckets_1704_, v___x_1721_);
v___x_1723_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(v_a_1702_, v_fallback_1703_, v___x_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg___boxed(lean_object* v_m_1724_, lean_object* v_a_1725_, lean_object* v_fallback_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_m_1724_, v_a_1725_, v_fallback_1726_);
lean_dec(v_fallback_1726_);
lean_dec_ref(v_a_1725_);
lean_dec_ref(v_m_1724_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44___redArg(lean_object* v_x_1728_, lean_object* v_x_1729_){
_start:
{
if (lean_obj_tag(v_x_1729_) == 0)
{
return v_x_1728_;
}
else
{
lean_object* v_key_1730_; lean_object* v_value_1731_; lean_object* v_tail_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1759_; 
v_key_1730_ = lean_ctor_get(v_x_1729_, 0);
v_value_1731_ = lean_ctor_get(v_x_1729_, 1);
v_tail_1732_ = lean_ctor_get(v_x_1729_, 2);
v_isSharedCheck_1759_ = !lean_is_exclusive(v_x_1729_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1734_ = v_x_1729_;
v_isShared_1735_ = v_isSharedCheck_1759_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_tail_1732_);
lean_inc(v_value_1731_);
lean_inc(v_key_1730_);
lean_dec(v_x_1729_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1759_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v_fst_1736_; lean_object* v_snd_1737_; lean_object* v___x_1738_; uint64_t v___x_1739_; uint64_t v___x_1740_; uint64_t v___x_1741_; uint64_t v___x_1742_; uint64_t v___x_1743_; uint64_t v_fold_1744_; uint64_t v___x_1745_; uint64_t v___x_1746_; uint64_t v___x_1747_; size_t v___x_1748_; size_t v___x_1749_; size_t v___x_1750_; size_t v___x_1751_; size_t v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1755_; 
v_fst_1736_ = lean_ctor_get(v_key_1730_, 0);
v_snd_1737_ = lean_ctor_get(v_key_1730_, 1);
v___x_1738_ = lean_array_get_size(v_x_1728_);
v___x_1739_ = l_String_instHashableRaw_hash(v_fst_1736_);
v___x_1740_ = l_String_instHashableRaw_hash(v_snd_1737_);
v___x_1741_ = lean_uint64_mix_hash(v___x_1739_, v___x_1740_);
v___x_1742_ = 32ULL;
v___x_1743_ = lean_uint64_shift_right(v___x_1741_, v___x_1742_);
v_fold_1744_ = lean_uint64_xor(v___x_1741_, v___x_1743_);
v___x_1745_ = 16ULL;
v___x_1746_ = lean_uint64_shift_right(v_fold_1744_, v___x_1745_);
v___x_1747_ = lean_uint64_xor(v_fold_1744_, v___x_1746_);
v___x_1748_ = lean_uint64_to_usize(v___x_1747_);
v___x_1749_ = lean_usize_of_nat(v___x_1738_);
v___x_1750_ = ((size_t)1ULL);
v___x_1751_ = lean_usize_sub(v___x_1749_, v___x_1750_);
v___x_1752_ = lean_usize_land(v___x_1748_, v___x_1751_);
v___x_1753_ = lean_array_uget_borrowed(v_x_1728_, v___x_1752_);
lean_inc(v___x_1753_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 2, v___x_1753_);
v___x_1755_ = v___x_1734_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_key_1730_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_value_1731_);
lean_ctor_set(v_reuseFailAlloc_1758_, 2, v___x_1753_);
v___x_1755_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
lean_object* v___x_1756_; 
v___x_1756_ = lean_array_uset(v_x_1728_, v___x_1752_, v___x_1755_);
v_x_1728_ = v___x_1756_;
v_x_1729_ = v_tail_1732_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35___redArg(lean_object* v_i_1760_, lean_object* v_source_1761_, lean_object* v_target_1762_){
_start:
{
lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1763_ = lean_array_get_size(v_source_1761_);
v___x_1764_ = lean_nat_dec_lt(v_i_1760_, v___x_1763_);
if (v___x_1764_ == 0)
{
lean_dec_ref(v_source_1761_);
lean_dec(v_i_1760_);
return v_target_1762_;
}
else
{
lean_object* v_es_1765_; lean_object* v___x_1766_; lean_object* v_source_1767_; lean_object* v_target_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v_es_1765_ = lean_array_fget(v_source_1761_, v_i_1760_);
v___x_1766_ = lean_box(0);
v_source_1767_ = lean_array_fset(v_source_1761_, v_i_1760_, v___x_1766_);
v_target_1768_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44___redArg(v_target_1762_, v_es_1765_);
v___x_1769_ = lean_unsigned_to_nat(1u);
v___x_1770_ = lean_nat_add(v_i_1760_, v___x_1769_);
lean_dec(v_i_1760_);
v_i_1760_ = v___x_1770_;
v_source_1761_ = v_source_1767_;
v_target_1762_ = v_target_1768_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24___redArg(lean_object* v_data_1772_){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v_nbuckets_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1773_ = lean_array_get_size(v_data_1772_);
v___x_1774_ = lean_unsigned_to_nat(2u);
v_nbuckets_1775_ = lean_nat_mul(v___x_1773_, v___x_1774_);
v___x_1776_ = lean_unsigned_to_nat(0u);
v___x_1777_ = lean_box(0);
v___x_1778_ = lean_mk_array(v_nbuckets_1775_, v___x_1777_);
v___x_1779_ = lean_array_propagate_mark(v_data_1772_, v___x_1778_);
v___x_1780_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35___redArg(v___x_1776_, v_data_1772_, v___x_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(lean_object* v_a_1781_, lean_object* v_b_1782_, lean_object* v_x_1783_){
_start:
{
if (lean_obj_tag(v_x_1783_) == 0)
{
lean_dec(v_b_1782_);
lean_dec_ref(v_a_1781_);
return v_x_1783_;
}
else
{
lean_object* v_key_1784_; lean_object* v_value_1785_; lean_object* v_tail_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1802_; 
v_key_1784_ = lean_ctor_get(v_x_1783_, 0);
v_value_1785_ = lean_ctor_get(v_x_1783_, 1);
v_tail_1786_ = lean_ctor_get(v_x_1783_, 2);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_x_1783_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1788_ = v_x_1783_;
v_isShared_1789_ = v_isSharedCheck_1802_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_tail_1786_);
lean_inc(v_value_1785_);
lean_inc(v_key_1784_);
lean_dec(v_x_1783_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1802_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v_fst_1795_; lean_object* v_snd_1796_; lean_object* v_fst_1797_; lean_object* v_snd_1798_; uint8_t v_decide_1799_; 
v_fst_1795_ = lean_ctor_get(v_key_1784_, 0);
v_snd_1796_ = lean_ctor_get(v_key_1784_, 1);
v_fst_1797_ = lean_ctor_get(v_a_1781_, 0);
v_snd_1798_ = lean_ctor_get(v_a_1781_, 1);
v_decide_1799_ = lean_nat_dec_eq(v_fst_1795_, v_fst_1797_);
if (v_decide_1799_ == 0)
{
goto v___jp_1790_;
}
else
{
uint8_t v_decide_1800_; 
v_decide_1800_ = lean_nat_dec_eq(v_snd_1796_, v_snd_1798_);
if (v_decide_1800_ == 0)
{
goto v___jp_1790_;
}
else
{
lean_object* v___x_1801_; 
lean_del_object(v___x_1788_);
lean_dec(v_value_1785_);
lean_dec(v_key_1784_);
v___x_1801_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1801_, 0, v_a_1781_);
lean_ctor_set(v___x_1801_, 1, v_b_1782_);
lean_ctor_set(v___x_1801_, 2, v_tail_1786_);
return v___x_1801_;
}
}
v___jp_1790_:
{
lean_object* v___x_1791_; lean_object* v___x_1793_; 
v___x_1791_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(v_a_1781_, v_b_1782_, v_tail_1786_);
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 2, v___x_1791_);
v___x_1793_ = v___x_1788_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_key_1784_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v_value_1785_);
lean_ctor_set(v_reuseFailAlloc_1794_, 2, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(lean_object* v_a_1803_, lean_object* v_x_1804_){
_start:
{
if (lean_obj_tag(v_x_1804_) == 0)
{
uint8_t v___x_1805_; 
v___x_1805_ = 0;
return v___x_1805_;
}
else
{
lean_object* v_key_1806_; lean_object* v_tail_1807_; lean_object* v_fst_1808_; lean_object* v_snd_1809_; lean_object* v_fst_1810_; lean_object* v_snd_1811_; uint8_t v_decide_1812_; 
v_key_1806_ = lean_ctor_get(v_x_1804_, 0);
v_tail_1807_ = lean_ctor_get(v_x_1804_, 2);
v_fst_1808_ = lean_ctor_get(v_key_1806_, 0);
v_snd_1809_ = lean_ctor_get(v_key_1806_, 1);
v_fst_1810_ = lean_ctor_get(v_a_1803_, 0);
v_snd_1811_ = lean_ctor_get(v_a_1803_, 1);
v_decide_1812_ = lean_nat_dec_eq(v_fst_1808_, v_fst_1810_);
if (v_decide_1812_ == 0)
{
v_x_1804_ = v_tail_1807_;
goto _start;
}
else
{
uint8_t v_decide_1814_; 
v_decide_1814_ = lean_nat_dec_eq(v_snd_1809_, v_snd_1811_);
if (v_decide_1814_ == 0)
{
v_x_1804_ = v_tail_1807_;
goto _start;
}
else
{
return v_decide_1814_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg___boxed(lean_object* v_a_1816_, lean_object* v_x_1817_){
_start:
{
uint8_t v_res_1818_; lean_object* v_r_1819_; 
v_res_1818_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(v_a_1816_, v_x_1817_);
lean_dec(v_x_1817_);
lean_dec_ref(v_a_1816_);
v_r_1819_ = lean_box(v_res_1818_);
return v_r_1819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(lean_object* v_m_1820_, lean_object* v_a_1821_, lean_object* v_b_1822_){
_start:
{
lean_object* v_size_1823_; lean_object* v_buckets_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1871_; 
v_size_1823_ = lean_ctor_get(v_m_1820_, 0);
v_buckets_1824_ = lean_ctor_get(v_m_1820_, 1);
v_isSharedCheck_1871_ = !lean_is_exclusive(v_m_1820_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1826_ = v_m_1820_;
v_isShared_1827_ = v_isSharedCheck_1871_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_buckets_1824_);
lean_inc(v_size_1823_);
lean_dec(v_m_1820_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1871_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v_fst_1828_; lean_object* v_snd_1829_; lean_object* v___x_1830_; uint64_t v___x_1831_; uint64_t v___x_1832_; uint64_t v___x_1833_; uint64_t v___x_1834_; uint64_t v___x_1835_; uint64_t v_fold_1836_; uint64_t v___x_1837_; uint64_t v___x_1838_; uint64_t v___x_1839_; size_t v___x_1840_; size_t v___x_1841_; size_t v___x_1842_; size_t v___x_1843_; size_t v___x_1844_; lean_object* v_bkt_1845_; uint8_t v___x_1846_; 
v_fst_1828_ = lean_ctor_get(v_a_1821_, 0);
v_snd_1829_ = lean_ctor_get(v_a_1821_, 1);
v___x_1830_ = lean_array_get_size(v_buckets_1824_);
v___x_1831_ = l_String_instHashableRaw_hash(v_fst_1828_);
v___x_1832_ = l_String_instHashableRaw_hash(v_snd_1829_);
v___x_1833_ = lean_uint64_mix_hash(v___x_1831_, v___x_1832_);
v___x_1834_ = 32ULL;
v___x_1835_ = lean_uint64_shift_right(v___x_1833_, v___x_1834_);
v_fold_1836_ = lean_uint64_xor(v___x_1833_, v___x_1835_);
v___x_1837_ = 16ULL;
v___x_1838_ = lean_uint64_shift_right(v_fold_1836_, v___x_1837_);
v___x_1839_ = lean_uint64_xor(v_fold_1836_, v___x_1838_);
v___x_1840_ = lean_uint64_to_usize(v___x_1839_);
v___x_1841_ = lean_usize_of_nat(v___x_1830_);
v___x_1842_ = ((size_t)1ULL);
v___x_1843_ = lean_usize_sub(v___x_1841_, v___x_1842_);
v___x_1844_ = lean_usize_land(v___x_1840_, v___x_1843_);
v_bkt_1845_ = lean_array_uget_borrowed(v_buckets_1824_, v___x_1844_);
v___x_1846_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(v_a_1821_, v_bkt_1845_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; lean_object* v_size_x27_1848_; lean_object* v___x_1849_; lean_object* v_buckets_x27_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; 
v___x_1847_ = lean_unsigned_to_nat(1u);
v_size_x27_1848_ = lean_nat_add(v_size_1823_, v___x_1847_);
lean_dec(v_size_1823_);
lean_inc(v_bkt_1845_);
v___x_1849_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1849_, 0, v_a_1821_);
lean_ctor_set(v___x_1849_, 1, v_b_1822_);
lean_ctor_set(v___x_1849_, 2, v_bkt_1845_);
v_buckets_x27_1850_ = lean_array_uset(v_buckets_1824_, v___x_1844_, v___x_1849_);
v___x_1851_ = lean_unsigned_to_nat(4u);
v___x_1852_ = lean_nat_mul(v_size_x27_1848_, v___x_1851_);
v___x_1853_ = lean_unsigned_to_nat(3u);
v___x_1854_ = lean_nat_div(v___x_1852_, v___x_1853_);
lean_dec(v___x_1852_);
v___x_1855_ = lean_array_get_size(v_buckets_x27_1850_);
v___x_1856_ = lean_nat_dec_le(v___x_1854_, v___x_1855_);
lean_dec(v___x_1854_);
if (v___x_1856_ == 0)
{
lean_object* v_val_1857_; lean_object* v___x_1859_; 
v_val_1857_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24___redArg(v_buckets_x27_1850_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 1, v_val_1857_);
lean_ctor_set(v___x_1826_, 0, v_size_x27_1848_);
v___x_1859_ = v___x_1826_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_size_x27_1848_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v_val_1857_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
else
{
lean_object* v___x_1862_; 
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 1, v_buckets_x27_1850_);
lean_ctor_set(v___x_1826_, 0, v_size_x27_1848_);
v___x_1862_ = v___x_1826_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_size_x27_1848_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v_buckets_x27_1850_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
else
{
lean_object* v___x_1864_; lean_object* v_buckets_x27_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1869_; 
lean_inc(v_bkt_1845_);
v___x_1864_ = lean_box(0);
v_buckets_x27_1865_ = lean_array_uset(v_buckets_1824_, v___x_1844_, v___x_1864_);
v___x_1866_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(v_a_1821_, v_b_1822_, v_bkt_1845_);
v___x_1867_ = lean_array_uset(v_buckets_x27_1865_, v___x_1844_, v___x_1866_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 1, v___x_1867_);
v___x_1869_ = v___x_1826_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_size_1823_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(uint8_t v___x_1874_, lean_object* v_as_1875_, size_t v_sz_1876_, size_t v_i_1877_, lean_object* v_b_1878_, lean_object* v___y_1879_){
_start:
{
uint8_t v___x_1881_; 
v___x_1881_ = lean_usize_dec_lt(v_i_1877_, v_sz_1876_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1882_; 
v___x_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1882_, 0, v_b_1878_);
return v___x_1882_;
}
else
{
lean_object* v_snd_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1920_; 
v_snd_1883_ = lean_ctor_get(v_b_1878_, 1);
v_isSharedCheck_1920_ = !lean_is_exclusive(v_b_1878_);
if (v_isSharedCheck_1920_ == 0)
{
lean_object* v_unused_1921_; 
v_unused_1921_ = lean_ctor_get(v_b_1878_, 0);
lean_dec(v_unused_1921_);
v___x_1885_ = v_b_1878_;
v_isShared_1886_ = v_isSharedCheck_1920_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_snd_1883_);
lean_dec(v_b_1878_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1920_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v_ref_1887_; lean_object* v_a_1888_; lean_object* v_ref_1889_; lean_object* v_msg_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1919_; 
v_ref_1887_ = lean_ctor_get(v___y_1879_, 2);
v_a_1888_ = lean_array_uget(v_as_1875_, v_i_1877_);
v_ref_1889_ = lean_ctor_get(v_a_1888_, 0);
v_msg_1890_ = lean_ctor_get(v_a_1888_, 1);
v_isSharedCheck_1919_ = !lean_is_exclusive(v_a_1888_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1892_ = v_a_1888_;
v_isShared_1893_ = v_isSharedCheck_1919_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_msg_1890_);
lean_inc(v_ref_1889_);
lean_dec(v_a_1888_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1919_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1894_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v_ref_1911_; lean_object* v___y_1913_; lean_object* v___x_1916_; 
v___x_1894_ = lean_box(0);
v_ref_1911_ = l_Lean_replaceRef(v_ref_1889_, v_ref_1887_);
lean_dec(v_ref_1889_);
v___x_1916_ = l_Lean_Syntax_getPos_x3f(v_ref_1911_, v___x_1874_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v___x_1917_; 
v___x_1917_ = lean_unsigned_to_nat(0u);
v___y_1913_ = v___x_1917_;
goto v___jp_1912_;
}
else
{
lean_object* v_val_1918_; 
v_val_1918_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_val_1918_);
lean_dec_ref_known(v___x_1916_, 1);
v___y_1913_ = v_val_1918_;
goto v___jp_1912_;
}
v___jp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 1, v___y_1897_);
lean_ctor_set(v___x_1885_, 0, v___y_1896_);
v___x_1899_ = v___x_1885_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___y_1896_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v___y_1897_);
v___x_1899_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v_pos2traces_1903_; lean_object* v___x_1905_; 
v___x_1900_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1901_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1883_, v___x_1899_, v___x_1900_);
v___x_1902_ = lean_array_push(v___x_1901_, v_msg_1890_);
v_pos2traces_1903_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_1883_, v___x_1899_, v___x_1902_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 1, v_pos2traces_1903_);
lean_ctor_set(v___x_1892_, 0, v___x_1894_);
v___x_1905_ = v___x_1892_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1894_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v_pos2traces_1903_);
v___x_1905_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
size_t v___x_1906_; size_t v___x_1907_; 
v___x_1906_ = ((size_t)1ULL);
v___x_1907_ = lean_usize_add(v_i_1877_, v___x_1906_);
v_i_1877_ = v___x_1907_;
v_b_1878_ = v___x_1905_;
goto _start;
}
}
}
v___jp_1912_:
{
lean_object* v___x_1914_; 
v___x_1914_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1911_, v___x_1874_);
lean_dec(v_ref_1911_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_inc(v___y_1913_);
v___y_1896_ = v___y_1913_;
v___y_1897_ = v___y_1913_;
goto v___jp_1895_;
}
else
{
lean_object* v_val_1915_; 
v_val_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_val_1915_);
lean_dec_ref_known(v___x_1914_, 1);
v___y_1896_ = v___y_1913_;
v___y_1897_ = v_val_1915_;
goto v___jp_1895_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___boxed(lean_object* v___x_1922_, lean_object* v_as_1923_, lean_object* v_sz_1924_, lean_object* v_i_1925_, lean_object* v_b_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
uint8_t v___x_39216__boxed_1929_; size_t v_sz_boxed_1930_; size_t v_i_boxed_1931_; lean_object* v_res_1932_; 
v___x_39216__boxed_1929_ = lean_unbox(v___x_1922_);
v_sz_boxed_1930_ = lean_unbox_usize(v_sz_1924_);
lean_dec(v_sz_1924_);
v_i_boxed_1931_ = lean_unbox_usize(v_i_1925_);
lean_dec(v_i_1925_);
v_res_1932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(v___x_39216__boxed_1929_, v_as_1923_, v_sz_boxed_1930_, v_i_boxed_1931_, v_b_1926_, v___y_1927_);
lean_dec_ref(v___y_1927_);
lean_dec_ref(v_as_1923_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40(uint8_t v___x_1933_, lean_object* v_as_1934_, size_t v_sz_1935_, size_t v_i_1936_, lean_object* v_b_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
uint8_t v___x_1941_; 
v___x_1941_ = lean_usize_dec_lt(v_i_1936_, v_sz_1935_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; 
v___x_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1942_, 0, v_b_1937_);
return v___x_1942_;
}
else
{
lean_object* v_snd_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1980_; 
v_snd_1943_ = lean_ctor_get(v_b_1937_, 1);
v_isSharedCheck_1980_ = !lean_is_exclusive(v_b_1937_);
if (v_isSharedCheck_1980_ == 0)
{
lean_object* v_unused_1981_; 
v_unused_1981_ = lean_ctor_get(v_b_1937_, 0);
lean_dec(v_unused_1981_);
v___x_1945_ = v_b_1937_;
v_isShared_1946_ = v_isSharedCheck_1980_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_snd_1943_);
lean_dec(v_b_1937_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1980_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v_ref_1947_; lean_object* v_a_1948_; lean_object* v_ref_1949_; lean_object* v_msg_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1979_; 
v_ref_1947_ = lean_ctor_get(v___y_1938_, 2);
v_a_1948_ = lean_array_uget(v_as_1934_, v_i_1936_);
v_ref_1949_ = lean_ctor_get(v_a_1948_, 0);
v_msg_1950_ = lean_ctor_get(v_a_1948_, 1);
v_isSharedCheck_1979_ = !lean_is_exclusive(v_a_1948_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1952_ = v_a_1948_;
v_isShared_1953_ = v_isSharedCheck_1979_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_msg_1950_);
lean_inc(v_ref_1949_);
lean_dec(v_a_1948_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1979_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1954_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v_ref_1971_; lean_object* v___y_1973_; lean_object* v___x_1976_; 
v___x_1954_ = lean_box(0);
v_ref_1971_ = l_Lean_replaceRef(v_ref_1949_, v_ref_1947_);
lean_dec(v_ref_1949_);
v___x_1976_ = l_Lean_Syntax_getPos_x3f(v_ref_1971_, v___x_1933_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v___x_1977_; 
v___x_1977_ = lean_unsigned_to_nat(0u);
v___y_1973_ = v___x_1977_;
goto v___jp_1972_;
}
else
{
lean_object* v_val_1978_; 
v_val_1978_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_val_1978_);
lean_dec_ref_known(v___x_1976_, 1);
v___y_1973_ = v_val_1978_;
goto v___jp_1972_;
}
v___jp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 1, v___y_1957_);
lean_ctor_set(v___x_1945_, 0, v___y_1956_);
v___x_1959_ = v___x_1945_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___y_1956_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v___y_1957_);
v___x_1959_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v_pos2traces_1963_; lean_object* v___x_1965_; 
v___x_1960_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1961_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1943_, v___x_1959_, v___x_1960_);
v___x_1962_ = lean_array_push(v___x_1961_, v_msg_1950_);
v_pos2traces_1963_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_1943_, v___x_1959_, v___x_1962_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 1, v_pos2traces_1963_);
lean_ctor_set(v___x_1952_, 0, v___x_1954_);
v___x_1965_ = v___x_1952_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1954_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v_pos2traces_1963_);
v___x_1965_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
size_t v___x_1966_; size_t v___x_1967_; lean_object* v___x_1968_; 
v___x_1966_ = ((size_t)1ULL);
v___x_1967_ = lean_usize_add(v_i_1936_, v___x_1966_);
v___x_1968_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(v___x_1933_, v_as_1934_, v_sz_1935_, v___x_1967_, v___x_1965_, v___y_1938_);
return v___x_1968_;
}
}
}
v___jp_1972_:
{
lean_object* v___x_1974_; 
v___x_1974_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1971_, v___x_1933_);
lean_dec(v_ref_1971_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_inc(v___y_1973_);
v___y_1956_ = v___y_1973_;
v___y_1957_ = v___y_1973_;
goto v___jp_1955_;
}
else
{
lean_object* v_val_1975_; 
v_val_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_val_1975_);
lean_dec_ref_known(v___x_1974_, 1);
v___y_1956_ = v___y_1973_;
v___y_1957_ = v_val_1975_;
goto v___jp_1955_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40___boxed(lean_object* v___x_1982_, lean_object* v_as_1983_, lean_object* v_sz_1984_, lean_object* v_i_1985_, lean_object* v_b_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
uint8_t v___x_39297__boxed_1990_; size_t v_sz_boxed_1991_; size_t v_i_boxed_1992_; lean_object* v_res_1993_; 
v___x_39297__boxed_1990_ = lean_unbox(v___x_1982_);
v_sz_boxed_1991_ = lean_unbox_usize(v_sz_1984_);
lean_dec(v_sz_1984_);
v_i_boxed_1992_ = lean_unbox_usize(v_i_1985_);
lean_dec(v_i_1985_);
v_res_1993_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40(v___x_39297__boxed_1990_, v_as_1983_, v_sz_boxed_1991_, v_i_boxed_1992_, v_b_1986_, v___y_1987_, v___y_1988_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec_ref(v_as_1983_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(lean_object* v_init_1994_, uint8_t v___x_1995_, lean_object* v_n_1996_, lean_object* v_b_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
if (lean_obj_tag(v_n_1996_) == 0)
{
lean_object* v_cs_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; size_t v_sz_2004_; size_t v___x_2005_; lean_object* v___x_2006_; 
v_cs_2001_ = lean_ctor_get(v_n_1996_, 0);
v___x_2002_ = lean_box(0);
v___x_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2002_);
lean_ctor_set(v___x_2003_, 1, v_b_1997_);
v_sz_2004_ = lean_array_size(v_cs_2001_);
v___x_2005_ = ((size_t)0ULL);
v___x_2006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39(v_init_1994_, v___x_1995_, v_cs_2001_, v_sz_2004_, v___x_2005_, v___x_2003_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2021_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2009_ = v___x_2006_;
v_isShared_2010_ = v_isSharedCheck_2021_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_2006_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2021_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v_fst_2011_; 
v_fst_2011_ = lean_ctor_get(v_a_2007_, 0);
if (lean_obj_tag(v_fst_2011_) == 0)
{
lean_object* v_snd_2012_; lean_object* v___x_2013_; lean_object* v___x_2015_; 
v_snd_2012_ = lean_ctor_get(v_a_2007_, 1);
lean_inc(v_snd_2012_);
lean_dec(v_a_2007_);
v___x_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2013_, 0, v_snd_2012_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 0, v___x_2013_);
v___x_2015_ = v___x_2009_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2013_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
else
{
lean_object* v_val_2017_; lean_object* v___x_2019_; 
lean_inc_ref(v_fst_2011_);
lean_dec(v_a_2007_);
v_val_2017_ = lean_ctor_get(v_fst_2011_, 0);
lean_inc(v_val_2017_);
lean_dec_ref_known(v_fst_2011_, 1);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 0, v_val_2017_);
v___x_2019_ = v___x_2009_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_val_2017_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
v_a_2022_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_2006_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2006_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
else
{
lean_object* v_vs_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; size_t v_sz_2033_; size_t v___x_2034_; lean_object* v___x_2035_; 
v_vs_2030_ = lean_ctor_get(v_n_1996_, 0);
v___x_2031_ = lean_box(0);
v___x_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
lean_ctor_set(v___x_2032_, 1, v_b_1997_);
v_sz_2033_ = lean_array_size(v_vs_2030_);
v___x_2034_ = ((size_t)0ULL);
v___x_2035_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40(v___x_1995_, v_vs_2030_, v_sz_2033_, v___x_2034_, v___x_2032_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2050_; 
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2038_ = v___x_2035_;
v_isShared_2039_ = v_isSharedCheck_2050_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2035_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2050_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v_fst_2040_; 
v_fst_2040_ = lean_ctor_get(v_a_2036_, 0);
if (lean_obj_tag(v_fst_2040_) == 0)
{
lean_object* v_snd_2041_; lean_object* v___x_2042_; lean_object* v___x_2044_; 
v_snd_2041_ = lean_ctor_get(v_a_2036_, 1);
lean_inc(v_snd_2041_);
lean_dec(v_a_2036_);
v___x_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2042_, 0, v_snd_2041_);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 0, v___x_2042_);
v___x_2044_ = v___x_2038_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
else
{
lean_object* v_val_2046_; lean_object* v___x_2048_; 
lean_inc_ref(v_fst_2040_);
lean_dec(v_a_2036_);
v_val_2046_ = lean_ctor_get(v_fst_2040_, 0);
lean_inc(v_val_2046_);
lean_dec_ref_known(v_fst_2040_, 1);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 0, v_val_2046_);
v___x_2048_ = v___x_2038_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_val_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
v_a_2051_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2035_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2035_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39(lean_object* v_init_2059_, uint8_t v___x_2060_, lean_object* v_as_2061_, size_t v_sz_2062_, size_t v_i_2063_, lean_object* v_b_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
uint8_t v___x_2068_; 
v___x_2068_ = lean_usize_dec_lt(v_i_2063_, v_sz_2062_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2069_; 
v___x_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2069_, 0, v_b_2064_);
return v___x_2069_;
}
else
{
lean_object* v_snd_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2104_; 
v_snd_2070_ = lean_ctor_get(v_b_2064_, 1);
v_isSharedCheck_2104_ = !lean_is_exclusive(v_b_2064_);
if (v_isSharedCheck_2104_ == 0)
{
lean_object* v_unused_2105_; 
v_unused_2105_ = lean_ctor_get(v_b_2064_, 0);
lean_dec(v_unused_2105_);
v___x_2072_ = v_b_2064_;
v_isShared_2073_ = v_isSharedCheck_2104_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_snd_2070_);
lean_dec(v_b_2064_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2104_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2074_; lean_object* v_a_2075_; lean_object* v___x_2076_; 
v___x_2074_ = lean_box(0);
v_a_2075_ = lean_array_uget_borrowed(v_as_2061_, v_i_2063_);
lean_inc(v_snd_2070_);
v___x_2076_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(v_init_2059_, v___x_2060_, v_a_2075_, v_snd_2070_, v___y_2065_, v___y_2066_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2095_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2079_ = v___x_2076_;
v_isShared_2080_ = v_isSharedCheck_2095_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2076_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2095_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
if (lean_obj_tag(v_a_2077_) == 0)
{
lean_object* v___x_2081_; lean_object* v___x_2083_; 
v___x_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2081_, 0, v_a_2077_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 0, v___x_2081_);
v___x_2083_ = v___x_2072_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2081_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_snd_2070_);
v___x_2083_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
lean_object* v___x_2085_; 
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 0, v___x_2083_);
v___x_2085_ = v___x_2079_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; 
lean_del_object(v___x_2079_);
lean_dec(v_snd_2070_);
v_a_2088_ = lean_ctor_get(v_a_2077_, 0);
lean_inc(v_a_2088_);
lean_dec_ref_known(v_a_2077_, 1);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 1, v_a_2088_);
lean_ctor_set(v___x_2072_, 0, v___x_2074_);
v___x_2090_ = v___x_2072_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2074_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v_a_2088_);
v___x_2090_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
size_t v___x_2091_; size_t v___x_2092_; 
v___x_2091_ = ((size_t)1ULL);
v___x_2092_ = lean_usize_add(v_i_2063_, v___x_2091_);
v_i_2063_ = v___x_2092_;
v_b_2064_ = v___x_2090_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_del_object(v___x_2072_);
lean_dec(v_snd_2070_);
v_a_2096_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2076_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2076_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39___boxed(lean_object* v_init_2106_, lean_object* v___x_2107_, lean_object* v_as_2108_, lean_object* v_sz_2109_, lean_object* v_i_2110_, lean_object* v_b_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
uint8_t v___x_39378__boxed_2115_; size_t v_sz_boxed_2116_; size_t v_i_boxed_2117_; lean_object* v_res_2118_; 
v___x_39378__boxed_2115_ = lean_unbox(v___x_2107_);
v_sz_boxed_2116_ = lean_unbox_usize(v_sz_2109_);
lean_dec(v_sz_2109_);
v_i_boxed_2117_ = lean_unbox_usize(v_i_2110_);
lean_dec(v_i_2110_);
v_res_2118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__39(v_init_2106_, v___x_39378__boxed_2115_, v_as_2108_, v_sz_boxed_2116_, v_i_boxed_2117_, v_b_2111_, v___y_2112_, v___y_2113_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec_ref(v_as_2108_);
lean_dec_ref(v_init_2106_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27___boxed(lean_object* v_init_2119_, lean_object* v___x_2120_, lean_object* v_n_2121_, lean_object* v_b_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
uint8_t v___x_39398__boxed_2126_; lean_object* v_res_2127_; 
v___x_39398__boxed_2126_ = lean_unbox(v___x_2120_);
v_res_2127_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(v_init_2119_, v___x_39398__boxed_2126_, v_n_2121_, v_b_2122_, v___y_2123_, v___y_2124_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec_ref(v_n_2121_);
lean_dec_ref(v_init_2119_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(uint8_t v___x_2128_, lean_object* v_as_2129_, size_t v_sz_2130_, size_t v_i_2131_, lean_object* v_b_2132_, lean_object* v___y_2133_){
_start:
{
uint8_t v___x_2135_; 
v___x_2135_ = lean_usize_dec_lt(v_i_2131_, v_sz_2130_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; 
v___x_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2136_, 0, v_b_2132_);
return v___x_2136_;
}
else
{
lean_object* v_snd_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2174_; 
v_snd_2137_ = lean_ctor_get(v_b_2132_, 1);
v_isSharedCheck_2174_ = !lean_is_exclusive(v_b_2132_);
if (v_isSharedCheck_2174_ == 0)
{
lean_object* v_unused_2175_; 
v_unused_2175_ = lean_ctor_get(v_b_2132_, 0);
lean_dec(v_unused_2175_);
v___x_2139_ = v_b_2132_;
v_isShared_2140_ = v_isSharedCheck_2174_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_snd_2137_);
lean_dec(v_b_2132_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2174_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v_ref_2141_; lean_object* v_a_2142_; lean_object* v_ref_2143_; lean_object* v_msg_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2173_; 
v_ref_2141_ = lean_ctor_get(v___y_2133_, 2);
v_a_2142_ = lean_array_uget(v_as_2129_, v_i_2131_);
v_ref_2143_ = lean_ctor_get(v_a_2142_, 0);
v_msg_2144_ = lean_ctor_get(v_a_2142_, 1);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_a_2142_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2146_ = v_a_2142_;
v_isShared_2147_ = v_isSharedCheck_2173_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_msg_2144_);
lean_inc(v_ref_2143_);
lean_dec(v_a_2142_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2173_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2148_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v_ref_2165_; lean_object* v___y_2167_; lean_object* v___x_2170_; 
v___x_2148_ = lean_box(0);
v_ref_2165_ = l_Lean_replaceRef(v_ref_2143_, v_ref_2141_);
lean_dec(v_ref_2143_);
v___x_2170_ = l_Lean_Syntax_getPos_x3f(v_ref_2165_, v___x_2128_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v___x_2171_; 
v___x_2171_ = lean_unsigned_to_nat(0u);
v___y_2167_ = v___x_2171_;
goto v___jp_2166_;
}
else
{
lean_object* v_val_2172_; 
v_val_2172_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_val_2172_);
lean_dec_ref_known(v___x_2170_, 1);
v___y_2167_ = v_val_2172_;
goto v___jp_2166_;
}
v___jp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 1, v___y_2151_);
lean_ctor_set(v___x_2139_, 0, v___y_2150_);
v___x_2153_ = v___x_2139_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___y_2150_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v___y_2151_);
v___x_2153_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v_pos2traces_2157_; lean_object* v___x_2159_; 
v___x_2154_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_2155_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_2137_, v___x_2153_, v___x_2154_);
v___x_2156_ = lean_array_push(v___x_2155_, v_msg_2144_);
v_pos2traces_2157_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_2137_, v___x_2153_, v___x_2156_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 1, v_pos2traces_2157_);
lean_ctor_set(v___x_2146_, 0, v___x_2148_);
v___x_2159_ = v___x_2146_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_pos2traces_2157_);
v___x_2159_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
size_t v___x_2160_; size_t v___x_2161_; 
v___x_2160_ = ((size_t)1ULL);
v___x_2161_ = lean_usize_add(v_i_2131_, v___x_2160_);
v_i_2131_ = v___x_2161_;
v_b_2132_ = v___x_2159_;
goto _start;
}
}
}
v___jp_2166_:
{
lean_object* v___x_2168_; 
v___x_2168_ = l_Lean_Syntax_getTailPos_x3f(v_ref_2165_, v___x_2128_);
lean_dec(v_ref_2165_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_inc(v___y_2167_);
v___y_2150_ = v___y_2167_;
v___y_2151_ = v___y_2167_;
goto v___jp_2149_;
}
else
{
lean_object* v_val_2169_; 
v_val_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_val_2169_);
lean_dec_ref_known(v___x_2168_, 1);
v___y_2150_ = v___y_2167_;
v___y_2151_ = v_val_2169_;
goto v___jp_2149_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg___boxed(lean_object* v___x_2176_, lean_object* v_as_2177_, lean_object* v_sz_2178_, lean_object* v_i_2179_, lean_object* v_b_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
uint8_t v___x_39581__boxed_2183_; size_t v_sz_boxed_2184_; size_t v_i_boxed_2185_; lean_object* v_res_2186_; 
v___x_39581__boxed_2183_ = lean_unbox(v___x_2176_);
v_sz_boxed_2184_ = lean_unbox_usize(v_sz_2178_);
lean_dec(v_sz_2178_);
v_i_boxed_2185_ = lean_unbox_usize(v_i_2179_);
lean_dec(v_i_2179_);
v_res_2186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(v___x_39581__boxed_2183_, v_as_2177_, v_sz_boxed_2184_, v_i_boxed_2185_, v_b_2180_, v___y_2181_);
lean_dec_ref(v___y_2181_);
lean_dec_ref(v_as_2177_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28(uint8_t v___x_2187_, lean_object* v_as_2188_, size_t v_sz_2189_, size_t v_i_2190_, lean_object* v_b_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
uint8_t v___x_2195_; 
v___x_2195_ = lean_usize_dec_lt(v_i_2190_, v_sz_2189_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; 
v___x_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2196_, 0, v_b_2191_);
return v___x_2196_;
}
else
{
lean_object* v_snd_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2234_; 
v_snd_2197_ = lean_ctor_get(v_b_2191_, 1);
v_isSharedCheck_2234_ = !lean_is_exclusive(v_b_2191_);
if (v_isSharedCheck_2234_ == 0)
{
lean_object* v_unused_2235_; 
v_unused_2235_ = lean_ctor_get(v_b_2191_, 0);
lean_dec(v_unused_2235_);
v___x_2199_ = v_b_2191_;
v_isShared_2200_ = v_isSharedCheck_2234_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_snd_2197_);
lean_dec(v_b_2191_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2234_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v_ref_2201_; lean_object* v_a_2202_; lean_object* v_ref_2203_; lean_object* v_msg_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2233_; 
v_ref_2201_ = lean_ctor_get(v___y_2192_, 2);
v_a_2202_ = lean_array_uget(v_as_2188_, v_i_2190_);
v_ref_2203_ = lean_ctor_get(v_a_2202_, 0);
v_msg_2204_ = lean_ctor_get(v_a_2202_, 1);
v_isSharedCheck_2233_ = !lean_is_exclusive(v_a_2202_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2206_ = v_a_2202_;
v_isShared_2207_ = v_isSharedCheck_2233_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_msg_2204_);
lean_inc(v_ref_2203_);
lean_dec(v_a_2202_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2233_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2208_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v_ref_2225_; lean_object* v___y_2227_; lean_object* v___x_2230_; 
v___x_2208_ = lean_box(0);
v_ref_2225_ = l_Lean_replaceRef(v_ref_2203_, v_ref_2201_);
lean_dec(v_ref_2203_);
v___x_2230_ = l_Lean_Syntax_getPos_x3f(v_ref_2225_, v___x_2187_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v___x_2231_; 
v___x_2231_ = lean_unsigned_to_nat(0u);
v___y_2227_ = v___x_2231_;
goto v___jp_2226_;
}
else
{
lean_object* v_val_2232_; 
v_val_2232_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_val_2232_);
lean_dec_ref_known(v___x_2230_, 1);
v___y_2227_ = v_val_2232_;
goto v___jp_2226_;
}
v___jp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 1, v___y_2211_);
lean_ctor_set(v___x_2199_, 0, v___y_2210_);
v___x_2213_ = v___x_2199_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___y_2210_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v___y_2211_);
v___x_2213_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v_pos2traces_2217_; lean_object* v___x_2219_; 
v___x_2214_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_2215_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_2197_, v___x_2213_, v___x_2214_);
v___x_2216_ = lean_array_push(v___x_2215_, v_msg_2204_);
v_pos2traces_2217_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_snd_2197_, v___x_2213_, v___x_2216_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 1, v_pos2traces_2217_);
lean_ctor_set(v___x_2206_, 0, v___x_2208_);
v___x_2219_ = v___x_2206_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2208_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_pos2traces_2217_);
v___x_2219_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
size_t v___x_2220_; size_t v___x_2221_; lean_object* v___x_2222_; 
v___x_2220_ = ((size_t)1ULL);
v___x_2221_ = lean_usize_add(v_i_2190_, v___x_2220_);
v___x_2222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(v___x_2187_, v_as_2188_, v_sz_2189_, v___x_2221_, v___x_2219_, v___y_2192_);
return v___x_2222_;
}
}
}
v___jp_2226_:
{
lean_object* v___x_2228_; 
v___x_2228_ = l_Lean_Syntax_getTailPos_x3f(v_ref_2225_, v___x_2187_);
lean_dec(v_ref_2225_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_inc(v___y_2227_);
v___y_2210_ = v___y_2227_;
v___y_2211_ = v___y_2227_;
goto v___jp_2209_;
}
else
{
lean_object* v_val_2229_; 
v_val_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_val_2229_);
lean_dec_ref_known(v___x_2228_, 1);
v___y_2210_ = v___y_2227_;
v___y_2211_ = v_val_2229_;
goto v___jp_2209_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28___boxed(lean_object* v___x_2236_, lean_object* v_as_2237_, lean_object* v_sz_2238_, lean_object* v_i_2239_, lean_object* v_b_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
uint8_t v___x_39661__boxed_2244_; size_t v_sz_boxed_2245_; size_t v_i_boxed_2246_; lean_object* v_res_2247_; 
v___x_39661__boxed_2244_ = lean_unbox(v___x_2236_);
v_sz_boxed_2245_ = lean_unbox_usize(v_sz_2238_);
lean_dec(v_sz_2238_);
v_i_boxed_2246_ = lean_unbox_usize(v_i_2239_);
lean_dec(v_i_2239_);
v_res_2247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28(v___x_39661__boxed_2244_, v_as_2237_, v_sz_boxed_2245_, v_i_boxed_2246_, v_b_2240_, v___y_2241_, v___y_2242_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec_ref(v_as_2237_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(uint8_t v___x_2248_, lean_object* v_t_2249_, lean_object* v_init_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v_root_2254_; lean_object* v_tail_2255_; lean_object* v___x_2256_; 
v_root_2254_ = lean_ctor_get(v_t_2249_, 0);
v_tail_2255_ = lean_ctor_get(v_t_2249_, 1);
lean_inc_ref(v_init_2250_);
v___x_2256_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27(v_init_2250_, v___x_2248_, v_root_2254_, v_init_2250_, v___y_2251_, v___y_2252_);
lean_dec_ref(v_init_2250_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2293_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2259_ = v___x_2256_;
v_isShared_2260_ = v_isSharedCheck_2293_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2293_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
if (lean_obj_tag(v_a_2257_) == 0)
{
lean_object* v_a_2261_; lean_object* v___x_2263_; 
v_a_2261_ = lean_ctor_get(v_a_2257_, 0);
lean_inc(v_a_2261_);
lean_dec_ref_known(v_a_2257_, 1);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v_a_2261_);
v___x_2263_ = v___x_2259_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2261_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; size_t v_sz_2268_; size_t v___x_2269_; lean_object* v___x_2270_; 
lean_del_object(v___x_2259_);
v_a_2265_ = lean_ctor_get(v_a_2257_, 0);
lean_inc(v_a_2265_);
lean_dec_ref_known(v_a_2257_, 1);
v___x_2266_ = lean_box(0);
v___x_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
lean_ctor_set(v___x_2267_, 1, v_a_2265_);
v_sz_2268_ = lean_array_size(v_tail_2255_);
v___x_2269_ = ((size_t)0ULL);
v___x_2270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28(v___x_2248_, v_tail_2255_, v_sz_2268_, v___x_2269_, v___x_2267_, v___y_2251_, v___y_2252_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2284_; 
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2273_ = v___x_2270_;
v_isShared_2274_ = v_isSharedCheck_2284_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2270_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2284_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v_fst_2275_; 
v_fst_2275_ = lean_ctor_get(v_a_2271_, 0);
if (lean_obj_tag(v_fst_2275_) == 0)
{
lean_object* v_snd_2276_; lean_object* v___x_2278_; 
v_snd_2276_ = lean_ctor_get(v_a_2271_, 1);
lean_inc(v_snd_2276_);
lean_dec(v_a_2271_);
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 0, v_snd_2276_);
v___x_2278_ = v___x_2273_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_snd_2276_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
else
{
lean_object* v_val_2280_; lean_object* v___x_2282_; 
lean_inc_ref(v_fst_2275_);
lean_dec(v_a_2271_);
v_val_2280_ = lean_ctor_get(v_fst_2275_, 0);
lean_inc(v_val_2280_);
lean_dec_ref_known(v_fst_2275_, 1);
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 0, v_val_2280_);
v___x_2282_ = v___x_2273_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_val_2280_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
v_a_2285_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2270_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2270_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2285_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
}
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
v_a_2294_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2256_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2256_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___boxed(lean_object* v___x_2302_, lean_object* v_t_2303_, lean_object* v_init_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
uint8_t v___x_39742__boxed_2308_; lean_object* v_res_2309_; 
v___x_39742__boxed_2308_ = lean_unbox(v___x_2302_);
v_res_2309_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(v___x_39742__boxed_2308_, v_t_2303_, v_init_2304_, v___y_2305_, v___y_2306_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec_ref(v_t_2303_);
return v_res_2309_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0(void){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2310_ = lean_unsigned_to_nat(32u);
v___x_2311_ = lean_mk_empty_array_with_capacity(v___x_2310_);
v___x_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
return v___x_2312_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1(void){
_start:
{
size_t v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2313_ = ((size_t)5ULL);
v___x_2314_ = lean_unsigned_to_nat(0u);
v___x_2315_ = lean_unsigned_to_nat(32u);
v___x_2316_ = lean_mk_empty_array_with_capacity(v___x_2315_);
v___x_2317_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__0);
v___x_2318_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
lean_ctor_set(v___x_2318_, 1, v___x_2316_);
lean_ctor_set(v___x_2318_, 2, v___x_2314_);
lean_ctor_set(v___x_2318_, 3, v___x_2314_);
lean_ctor_set_usize(v___x_2318_, 4, v___x_2313_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(lean_object* v___y_2319_){
_start:
{
lean_object* v___x_2321_; lean_object* v_traceState_2322_; lean_object* v_traces_2323_; lean_object* v___x_2324_; lean_object* v_traceState_2325_; lean_object* v_env_2326_; lean_object* v_nextMacroScope_2327_; lean_object* v_ngen_2328_; lean_object* v_auxDeclNGen_2329_; lean_object* v_cache_2330_; lean_object* v_recordedDeps_2331_; lean_object* v_messages_2332_; lean_object* v_infoState_2333_; lean_object* v_snapshotTasks_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2353_; 
v___x_2321_ = lean_st_ref_get(v___y_2319_);
v_traceState_2322_ = lean_ctor_get(v___x_2321_, 4);
lean_inc_ref(v_traceState_2322_);
lean_dec(v___x_2321_);
v_traces_2323_ = lean_ctor_get(v_traceState_2322_, 0);
lean_inc_ref(v_traces_2323_);
lean_dec_ref(v_traceState_2322_);
v___x_2324_ = lean_st_ref_take(v___y_2319_);
v_traceState_2325_ = lean_ctor_get(v___x_2324_, 4);
v_env_2326_ = lean_ctor_get(v___x_2324_, 0);
v_nextMacroScope_2327_ = lean_ctor_get(v___x_2324_, 1);
v_ngen_2328_ = lean_ctor_get(v___x_2324_, 2);
v_auxDeclNGen_2329_ = lean_ctor_get(v___x_2324_, 3);
v_cache_2330_ = lean_ctor_get(v___x_2324_, 5);
v_recordedDeps_2331_ = lean_ctor_get(v___x_2324_, 6);
v_messages_2332_ = lean_ctor_get(v___x_2324_, 7);
v_infoState_2333_ = lean_ctor_get(v___x_2324_, 8);
v_snapshotTasks_2334_ = lean_ctor_get(v___x_2324_, 9);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2336_ = v___x_2324_;
v_isShared_2337_ = v_isSharedCheck_2353_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_snapshotTasks_2334_);
lean_inc(v_infoState_2333_);
lean_inc(v_messages_2332_);
lean_inc(v_recordedDeps_2331_);
lean_inc(v_cache_2330_);
lean_inc(v_traceState_2325_);
lean_inc(v_auxDeclNGen_2329_);
lean_inc(v_ngen_2328_);
lean_inc(v_nextMacroScope_2327_);
lean_inc(v_env_2326_);
lean_dec(v___x_2324_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2353_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
uint64_t v_tid_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2351_; 
v_tid_2338_ = lean_ctor_get_uint64(v_traceState_2325_, sizeof(void*)*1);
v_isSharedCheck_2351_ = !lean_is_exclusive(v_traceState_2325_);
if (v_isSharedCheck_2351_ == 0)
{
lean_object* v_unused_2352_; 
v_unused_2352_ = lean_ctor_get(v_traceState_2325_, 0);
lean_dec(v_unused_2352_);
v___x_2340_ = v_traceState_2325_;
v_isShared_2341_ = v_isSharedCheck_2351_;
goto v_resetjp_2339_;
}
else
{
lean_dec(v_traceState_2325_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2351_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2342_; lean_object* v___x_2344_; 
v___x_2342_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 0, v___x_2342_);
v___x_2344_ = v___x_2340_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2342_);
lean_ctor_set_uint64(v_reuseFailAlloc_2350_, sizeof(void*)*1, v_tid_2338_);
v___x_2344_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
lean_object* v___x_2346_; 
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 4, v___x_2344_);
v___x_2346_ = v___x_2336_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_env_2326_);
lean_ctor_set(v_reuseFailAlloc_2349_, 1, v_nextMacroScope_2327_);
lean_ctor_set(v_reuseFailAlloc_2349_, 2, v_ngen_2328_);
lean_ctor_set(v_reuseFailAlloc_2349_, 3, v_auxDeclNGen_2329_);
lean_ctor_set(v_reuseFailAlloc_2349_, 4, v___x_2344_);
lean_ctor_set(v_reuseFailAlloc_2349_, 5, v_cache_2330_);
lean_ctor_set(v_reuseFailAlloc_2349_, 6, v_recordedDeps_2331_);
lean_ctor_set(v_reuseFailAlloc_2349_, 7, v_messages_2332_);
lean_ctor_set(v_reuseFailAlloc_2349_, 8, v_infoState_2333_);
lean_ctor_set(v_reuseFailAlloc_2349_, 9, v_snapshotTasks_2334_);
v___x_2346_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2347_ = lean_st_ref_put(v___y_2319_, v___x_2346_);
v___x_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2348_, 0, v_traces_2323_);
return v___x_2348_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___boxed(lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___y_2354_);
lean_dec(v___y_2354_);
return v_res_2356_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0(void){
_start:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2357_ = lean_box(0);
v___x_2358_ = lean_unsigned_to_nat(16u);
v___x_2359_ = lean_mk_array(v___x_2358_, v___x_2357_);
return v___x_2359_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1(void){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v_pos2traces_2362_; 
v___x_2360_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0, &l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0);
v___x_2361_ = lean_unsigned_to_nat(0u);
v_pos2traces_2362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_2362_, 0, v___x_2361_);
lean_ctor_set(v_pos2traces_2362_, 1, v___x_2360_);
return v_pos2traces_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9(lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v_toCold_2369_; lean_object* v_options_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
v_toCold_2369_ = lean_ctor_get(v___y_2363_, 0);
v_options_2370_ = lean_ctor_get(v_toCold_2369_, 2);
v___x_2371_ = l_Lean_trace_profiler_output;
v___x_2372_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(v_options_2370_, v___x_2371_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v___x_2373_; uint8_t v___x_2374_; 
v___x_2373_ = l_Lean_trace_profiler_serve;
v___x_2374_ = l_Lean_Option_get___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(v_options_2370_, v___x_2373_);
if (v___x_2374_ == 0)
{
lean_object* v___x_2375_; lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2438_; 
v___x_2375_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___y_2364_);
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2378_ = v___x_2375_;
v_isShared_2379_ = v_isSharedCheck_2438_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2375_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2438_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
uint8_t v___x_2380_; 
v___x_2380_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_2376_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; lean_object* v_pos2traces_2382_; lean_object* v___x_2383_; 
lean_del_object(v___x_2378_);
v___x_2381_ = lean_unsigned_to_nat(0u);
v_pos2traces_2382_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1, &l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1);
v___x_2383_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(v___x_2380_, v_a_2376_, v_pos2traces_2382_, v___y_2363_, v___y_2364_);
lean_dec(v_a_2376_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_a_2384_; lean_object* v___y_2386_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2412_; lean_object* v_size_2418_; lean_object* v_buckets_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; uint8_t v___x_2422_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_a_2384_);
lean_dec_ref_known(v___x_2383_, 1);
v_size_2418_ = lean_ctor_get(v_a_2384_, 0);
lean_inc(v_size_2418_);
v_buckets_2419_ = lean_ctor_get(v_a_2384_, 1);
lean_inc_ref(v_buckets_2419_);
lean_dec(v_a_2384_);
v___x_2420_ = lean_mk_empty_array_with_capacity(v_size_2418_);
lean_dec(v_size_2418_);
v___x_2421_ = lean_array_get_size(v_buckets_2419_);
v___x_2422_ = lean_nat_dec_lt(v___x_2381_, v___x_2421_);
if (v___x_2422_ == 0)
{
lean_dec_ref(v_buckets_2419_);
v___y_2412_ = v___x_2420_;
goto v___jp_2411_;
}
else
{
size_t v___x_2423_; size_t v___x_2424_; lean_object* v___x_2425_; 
v___x_2423_ = ((size_t)0ULL);
v___x_2424_ = lean_usize_of_nat(v___x_2421_);
v___x_2425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__23(v_buckets_2419_, v___x_2423_, v___x_2424_, v___x_2420_);
lean_dec_ref(v_buckets_2419_);
v___y_2412_ = v___x_2425_;
goto v___jp_2411_;
}
v___jp_2385_:
{
lean_object* v___x_2387_; size_t v_sz_2388_; size_t v___x_2389_; lean_object* v___x_2390_; 
v___x_2387_ = lean_box(0);
v_sz_2388_ = lean_array_size(v___y_2386_);
v___x_2389_ = ((size_t)0ULL);
v___x_2390_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(v___x_2374_, v___y_2386_, v_sz_2388_, v___x_2389_, v___x_2387_, v___y_2363_, v___y_2364_);
lean_dec_ref(v___y_2386_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2397_ == 0)
{
lean_object* v_unused_2398_; 
v_unused_2398_ = lean_ctor_get(v___x_2390_, 0);
lean_dec(v_unused_2398_);
v___x_2392_ = v___x_2390_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_dec(v___x_2390_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 0, v___x_2387_);
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2387_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
else
{
return v___x_2390_;
}
}
v___jp_2399_:
{
lean_object* v___x_2404_; 
v___x_2404_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v___y_2401_, v___y_2402_, v___y_2400_, v___y_2403_);
lean_dec(v___y_2403_);
lean_dec(v___y_2401_);
v___y_2386_ = v___x_2404_;
goto v___jp_2385_;
}
v___jp_2405_:
{
uint8_t v___x_2410_; 
v___x_2410_ = lean_nat_dec_le(v___y_2409_, v___y_2406_);
if (v___x_2410_ == 0)
{
lean_dec(v___y_2406_);
lean_inc(v___y_2409_);
v___y_2400_ = v___y_2409_;
v___y_2401_ = v___y_2407_;
v___y_2402_ = v___y_2408_;
v___y_2403_ = v___y_2409_;
goto v___jp_2399_;
}
else
{
v___y_2400_ = v___y_2409_;
v___y_2401_ = v___y_2407_;
v___y_2402_ = v___y_2408_;
v___y_2403_ = v___y_2406_;
goto v___jp_2399_;
}
}
v___jp_2411_:
{
lean_object* v___x_2413_; uint8_t v___x_2414_; 
v___x_2413_ = lean_array_get_size(v___y_2412_);
v___x_2414_ = lean_nat_dec_eq(v___x_2413_, v___x_2381_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; lean_object* v___x_2416_; uint8_t v___x_2417_; 
v___x_2415_ = lean_unsigned_to_nat(1u);
v___x_2416_ = lean_nat_sub(v___x_2413_, v___x_2415_);
v___x_2417_ = lean_nat_dec_le(v___x_2381_, v___x_2416_);
if (v___x_2417_ == 0)
{
lean_inc(v___x_2416_);
v___y_2406_ = v___x_2416_;
v___y_2407_ = v___x_2413_;
v___y_2408_ = v___y_2412_;
v___y_2409_ = v___x_2416_;
goto v___jp_2405_;
}
else
{
v___y_2406_ = v___x_2416_;
v___y_2407_ = v___x_2413_;
v___y_2408_ = v___y_2412_;
v___y_2409_ = v___x_2381_;
goto v___jp_2405_;
}
}
else
{
v___y_2386_ = v___y_2412_;
goto v___jp_2385_;
}
}
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
v_a_2426_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2383_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2383_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
else
{
lean_object* v___x_2434_; lean_object* v___x_2436_; 
lean_dec(v_a_2376_);
v___x_2434_ = lean_box(0);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 0, v___x_2434_);
v___x_2436_ = v___x_2378_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2434_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
else
{
goto v___jp_2366_;
}
}
else
{
lean_dec_ref_known(v___x_2372_, 1);
goto v___jp_2366_;
}
v___jp_2366_:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2367_ = lean_box(0);
v___x_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
return v___x_2368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9___boxed(lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2439_, v___y_2440_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(lean_object* v_as_2443_, size_t v_sz_2444_, size_t v_i_2445_, lean_object* v_b_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
uint8_t v___x_2450_; 
v___x_2450_ = lean_usize_dec_lt(v_i_2445_, v_sz_2444_);
if (v___x_2450_ == 0)
{
lean_object* v___x_2451_; 
v___x_2451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2451_, 0, v_b_2446_);
return v___x_2451_;
}
else
{
lean_object* v___x_2452_; lean_object* v_a_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2452_ = lean_box(0);
v_a_2453_ = lean_array_uget_borrowed(v_as_2443_, v_i_2445_);
v___x_2454_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2447_);
lean_inc(v_a_2453_);
v___x_2455_ = l_Lean_Compiler_LCNF_resumeCompilation(v_a_2453_, v___x_2454_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v___x_2456_; 
lean_dec_ref_known(v___x_2455_, 1);
v___x_2456_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2456_) == 0)
{
size_t v___x_2457_; size_t v___x_2458_; 
lean_dec_ref_known(v___x_2456_, 1);
v___x_2457_ = ((size_t)1ULL);
v___x_2458_ = lean_usize_add(v_i_2445_, v___x_2457_);
v_i_2445_ = v___x_2458_;
v_b_2446_ = v___x_2452_;
goto _start;
}
else
{
return v___x_2456_;
}
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2461_; 
v_a_2460_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2460_);
lean_dec_ref_known(v___x_2455_, 1);
v___x_2461_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2468_ == 0)
{
lean_object* v_unused_2469_; 
v_unused_2469_ = lean_ctor_get(v___x_2461_, 0);
lean_dec(v_unused_2469_);
v___x_2463_ = v___x_2461_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_dec(v___x_2461_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
lean_ctor_set_tag(v___x_2463_, 1);
lean_ctor_set(v___x_2463_, 0, v_a_2460_);
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2460_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
else
{
lean_dec(v_a_2460_);
return v___x_2461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10___boxed(lean_object* v_as_2470_, lean_object* v_sz_2471_, lean_object* v_i_2472_, lean_object* v_b_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
size_t v_sz_boxed_2477_; size_t v_i_boxed_2478_; lean_object* v_res_2479_; 
v_sz_boxed_2477_ = lean_unbox_usize(v_sz_2471_);
lean_dec(v_sz_2471_);
v_i_boxed_2478_ = lean_unbox_usize(v_i_2472_);
lean_dec(v_i_2472_);
v_res_2479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(v_as_2470_, v_sz_boxed_2477_, v_i_boxed_2478_, v_b_2473_, v___y_2474_, v___y_2475_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec_ref(v_as_2470_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(lean_object* v_as_2480_, size_t v_sz_2481_, size_t v_i_2482_, lean_object* v_b_2483_, lean_object* v___y_2484_){
_start:
{
uint8_t v___x_2486_; 
v___x_2486_ = lean_usize_dec_lt(v_i_2482_, v_sz_2481_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; 
v___x_2487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2487_, 0, v_b_2483_);
return v___x_2487_;
}
else
{
uint8_t v___x_2488_; lean_object* v_a_2489_; lean_object* v___x_2490_; lean_object* v_ref_2491_; lean_object* v___x_2492_; 
lean_dec_ref(v_b_2483_);
v___x_2488_ = 0;
v_a_2489_ = lean_array_uget_borrowed(v_as_2480_, v_i_2482_);
lean_inc(v_a_2489_);
v___x_2490_ = l_Lean_Message_toString(v_a_2489_, v___x_2488_);
v_ref_2491_ = lean_ctor_get(v___y_2484_, 2);
v___x_2492_ = l_IO_eprintln___at___00main_spec__6(v___x_2490_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v___x_2493_; size_t v___x_2494_; size_t v___x_2495_; 
lean_dec_ref_known(v___x_2492_, 1);
v___x_2493_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_2494_ = ((size_t)1ULL);
v___x_2495_ = lean_usize_add(v_i_2482_, v___x_2494_);
v_i_2482_ = v___x_2495_;
v_b_2483_ = v___x_2493_;
goto _start;
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2508_; 
v_a_2497_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2499_ = v___x_2492_;
v_isShared_2500_ = v_isSharedCheck_2508_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2492_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2508_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2506_; 
v___x_2501_ = lean_io_error_to_string(v_a_2497_);
v___x_2502_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2501_);
v___x_2503_ = l_Lean_MessageData_ofFormat(v___x_2502_);
lean_inc(v_ref_2491_);
v___x_2504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2504_, 0, v_ref_2491_);
lean_ctor_set(v___x_2504_, 1, v___x_2503_);
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 0, v___x_2504_);
v___x_2506_ = v___x_2499_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v___x_2504_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg___boxed(lean_object* v_as_2509_, lean_object* v_sz_2510_, lean_object* v_i_2511_, lean_object* v_b_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
size_t v_sz_boxed_2515_; size_t v_i_boxed_2516_; lean_object* v_res_2517_; 
v_sz_boxed_2515_ = lean_unbox_usize(v_sz_2510_);
lean_dec(v_sz_2510_);
v_i_boxed_2516_ = lean_unbox_usize(v_i_2511_);
lean_dec(v_i_2511_);
v_res_2517_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(v_as_2509_, v_sz_boxed_2515_, v_i_boxed_2516_, v_b_2512_, v___y_2513_);
lean_dec_ref(v___y_2513_);
lean_dec_ref(v_as_2509_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38(lean_object* v_as_2518_, size_t v_sz_2519_, size_t v_i_2520_, lean_object* v_b_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
uint8_t v___x_2525_; 
v___x_2525_ = lean_usize_dec_lt(v_i_2520_, v_sz_2519_);
if (v___x_2525_ == 0)
{
lean_object* v___x_2526_; 
v___x_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2526_, 0, v_b_2521_);
return v___x_2526_;
}
else
{
uint8_t v___x_2527_; lean_object* v_a_2528_; lean_object* v___x_2529_; lean_object* v_ref_2530_; lean_object* v___x_2531_; 
lean_dec_ref(v_b_2521_);
v___x_2527_ = 0;
v_a_2528_ = lean_array_uget_borrowed(v_as_2518_, v_i_2520_);
lean_inc(v_a_2528_);
v___x_2529_ = l_Lean_Message_toString(v_a_2528_, v___x_2527_);
v_ref_2530_ = lean_ctor_get(v___y_2522_, 2);
v___x_2531_ = l_IO_eprintln___at___00main_spec__6(v___x_2529_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v___x_2532_; size_t v___x_2533_; size_t v___x_2534_; lean_object* v___x_2535_; 
lean_dec_ref_known(v___x_2531_, 1);
v___x_2532_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__27___closed__0));
v___x_2533_ = ((size_t)1ULL);
v___x_2534_ = lean_usize_add(v_i_2520_, v___x_2533_);
v___x_2535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(v_as_2518_, v_sz_2519_, v___x_2534_, v___x_2532_, v___y_2522_);
return v___x_2535_;
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2547_; 
v_a_2536_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2538_ = v___x_2531_;
v_isShared_2539_ = v_isSharedCheck_2547_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2531_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2547_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2545_; 
v___x_2540_ = lean_io_error_to_string(v_a_2536_);
v___x_2541_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
v___x_2542_ = l_Lean_MessageData_ofFormat(v___x_2541_);
lean_inc(v_ref_2530_);
v___x_2543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2543_, 0, v_ref_2530_);
lean_ctor_set(v___x_2543_, 1, v___x_2542_);
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 0, v___x_2543_);
v___x_2545_ = v___x_2538_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v___x_2543_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38___boxed(lean_object* v_as_2548_, lean_object* v_sz_2549_, lean_object* v_i_2550_, lean_object* v_b_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
size_t v_sz_boxed_2555_; size_t v_i_boxed_2556_; lean_object* v_res_2557_; 
v_sz_boxed_2555_ = lean_unbox_usize(v_sz_2549_);
lean_dec(v_sz_2549_);
v_i_boxed_2556_ = lean_unbox_usize(v_i_2550_);
lean_dec(v_i_2550_);
v_res_2557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38(v_as_2548_, v_sz_boxed_2555_, v_i_boxed_2556_, v_b_2551_, v___y_2552_, v___y_2553_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec_ref(v_as_2548_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(lean_object* v_init_2558_, lean_object* v_n_2559_, lean_object* v_b_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
if (lean_obj_tag(v_n_2559_) == 0)
{
lean_object* v_cs_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; size_t v_sz_2567_; size_t v___x_2568_; lean_object* v___x_2569_; 
v_cs_2564_ = lean_ctor_get(v_n_2559_, 0);
v___x_2565_ = lean_box(0);
v___x_2566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2565_);
lean_ctor_set(v___x_2566_, 1, v_b_2560_);
v_sz_2567_ = lean_array_size(v_cs_2564_);
v___x_2568_ = ((size_t)0ULL);
v___x_2569_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37(v_init_2558_, v_cs_2564_, v_sz_2567_, v___x_2568_, v___x_2566_, v___y_2561_, v___y_2562_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2584_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2572_ = v___x_2569_;
v_isShared_2573_ = v_isSharedCheck_2584_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2569_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2584_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v_fst_2574_; 
v_fst_2574_ = lean_ctor_get(v_a_2570_, 0);
if (lean_obj_tag(v_fst_2574_) == 0)
{
lean_object* v_snd_2575_; lean_object* v___x_2576_; lean_object* v___x_2578_; 
v_snd_2575_ = lean_ctor_get(v_a_2570_, 1);
lean_inc(v_snd_2575_);
lean_dec(v_a_2570_);
v___x_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2576_, 0, v_snd_2575_);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 0, v___x_2576_);
v___x_2578_ = v___x_2572_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
else
{
lean_object* v_val_2580_; lean_object* v___x_2582_; 
lean_inc_ref(v_fst_2574_);
lean_dec(v_a_2570_);
v_val_2580_ = lean_ctor_get(v_fst_2574_, 0);
lean_inc(v_val_2580_);
lean_dec_ref_known(v_fst_2574_, 1);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 0, v_val_2580_);
v___x_2582_ = v___x_2572_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_val_2580_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
v_a_2585_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2569_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2569_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
else
{
lean_object* v_vs_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; size_t v_sz_2596_; size_t v___x_2597_; lean_object* v___x_2598_; 
v_vs_2593_ = lean_ctor_get(v_n_2559_, 0);
v___x_2594_ = lean_box(0);
v___x_2595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
lean_ctor_set(v___x_2595_, 1, v_b_2560_);
v_sz_2596_ = lean_array_size(v_vs_2593_);
v___x_2597_ = ((size_t)0ULL);
v___x_2598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38(v_vs_2593_, v_sz_2596_, v___x_2597_, v___x_2595_, v___y_2561_, v___y_2562_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2613_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2601_ = v___x_2598_;
v_isShared_2602_ = v_isSharedCheck_2613_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2598_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2613_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v_fst_2603_; 
v_fst_2603_ = lean_ctor_get(v_a_2599_, 0);
if (lean_obj_tag(v_fst_2603_) == 0)
{
lean_object* v_snd_2604_; lean_object* v___x_2605_; lean_object* v___x_2607_; 
v_snd_2604_ = lean_ctor_get(v_a_2599_, 1);
lean_inc(v_snd_2604_);
lean_dec(v_a_2599_);
v___x_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2605_, 0, v_snd_2604_);
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 0, v___x_2605_);
v___x_2607_ = v___x_2601_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2605_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
else
{
lean_object* v_val_2609_; lean_object* v___x_2611_; 
lean_inc_ref(v_fst_2603_);
lean_dec(v_a_2599_);
v_val_2609_ = lean_ctor_get(v_fst_2603_, 0);
lean_inc(v_val_2609_);
lean_dec_ref_known(v_fst_2603_, 1);
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 0, v_val_2609_);
v___x_2611_ = v___x_2601_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_val_2609_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
v_a_2614_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2598_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2598_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37(lean_object* v_init_2622_, lean_object* v_as_2623_, size_t v_sz_2624_, size_t v_i_2625_, lean_object* v_b_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
uint8_t v___x_2630_; 
v___x_2630_ = lean_usize_dec_lt(v_i_2625_, v_sz_2624_);
if (v___x_2630_ == 0)
{
lean_object* v___x_2631_; 
v___x_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2631_, 0, v_b_2626_);
return v___x_2631_;
}
else
{
lean_object* v_snd_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2666_; 
v_snd_2632_ = lean_ctor_get(v_b_2626_, 1);
v_isSharedCheck_2666_ = !lean_is_exclusive(v_b_2626_);
if (v_isSharedCheck_2666_ == 0)
{
lean_object* v_unused_2667_; 
v_unused_2667_ = lean_ctor_get(v_b_2626_, 0);
lean_dec(v_unused_2667_);
v___x_2634_ = v_b_2626_;
v_isShared_2635_ = v_isSharedCheck_2666_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_snd_2632_);
lean_dec(v_b_2626_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2666_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2636_; lean_object* v_a_2637_; lean_object* v___x_2638_; 
v___x_2636_ = lean_box(0);
v_a_2637_ = lean_array_uget_borrowed(v_as_2623_, v_i_2625_);
lean_inc(v_snd_2632_);
v___x_2638_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(v_init_2622_, v_a_2637_, v_snd_2632_, v___y_2627_, v___y_2628_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2657_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2641_ = v___x_2638_;
v_isShared_2642_ = v_isSharedCheck_2657_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2638_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2657_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
if (lean_obj_tag(v_a_2639_) == 0)
{
lean_object* v___x_2643_; lean_object* v___x_2645_; 
v___x_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2643_, 0, v_a_2639_);
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 0, v___x_2643_);
v___x_2645_ = v___x_2634_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2643_);
lean_ctor_set(v_reuseFailAlloc_2649_, 1, v_snd_2632_);
v___x_2645_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
lean_object* v___x_2647_; 
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
}
else
{
lean_object* v_a_2650_; lean_object* v___x_2652_; 
lean_del_object(v___x_2641_);
lean_dec(v_snd_2632_);
v_a_2650_ = lean_ctor_get(v_a_2639_, 0);
lean_inc(v_a_2650_);
lean_dec_ref_known(v_a_2639_, 1);
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 1, v_a_2650_);
lean_ctor_set(v___x_2634_, 0, v___x_2636_);
v___x_2652_ = v___x_2634_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___x_2636_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v_a_2650_);
v___x_2652_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
size_t v___x_2653_; size_t v___x_2654_; 
v___x_2653_ = ((size_t)1ULL);
v___x_2654_ = lean_usize_add(v_i_2625_, v___x_2653_);
v_i_2625_ = v___x_2654_;
v_b_2626_ = v___x_2652_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
lean_del_object(v___x_2634_);
lean_dec(v_snd_2632_);
v_a_2658_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2660_ = v___x_2638_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2638_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
if (v_isShared_2661_ == 0)
{
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2658_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37___boxed(lean_object* v_init_2668_, lean_object* v_as_2669_, lean_object* v_sz_2670_, lean_object* v_i_2671_, lean_object* v_b_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_){
_start:
{
size_t v_sz_boxed_2676_; size_t v_i_boxed_2677_; lean_object* v_res_2678_; 
v_sz_boxed_2676_ = lean_unbox_usize(v_sz_2670_);
lean_dec(v_sz_2670_);
v_i_boxed_2677_ = lean_unbox_usize(v_i_2671_);
lean_dec(v_i_2671_);
v_res_2678_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__37(v_init_2668_, v_as_2669_, v_sz_boxed_2676_, v_i_boxed_2677_, v_b_2672_, v___y_2673_, v___y_2674_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec_ref(v_as_2669_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26___boxed(lean_object* v_init_2679_, lean_object* v_n_2680_, lean_object* v_b_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(v_init_2679_, v_n_2680_, v_b_2681_, v___y_2682_, v___y_2683_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec_ref(v_n_2680_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(lean_object* v_as_2686_, size_t v_sz_2687_, size_t v_i_2688_, lean_object* v_b_2689_, lean_object* v___y_2690_){
_start:
{
uint8_t v___x_2692_; 
v___x_2692_ = lean_usize_dec_lt(v_i_2688_, v_sz_2687_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2693_; 
v___x_2693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2693_, 0, v_b_2689_);
return v___x_2693_;
}
else
{
uint8_t v___x_2694_; lean_object* v_a_2695_; lean_object* v___x_2696_; lean_object* v_ref_2697_; lean_object* v___x_2698_; 
lean_dec_ref(v_b_2689_);
v___x_2694_ = 0;
v_a_2695_ = lean_array_uget_borrowed(v_as_2686_, v_i_2688_);
lean_inc(v_a_2695_);
v___x_2696_ = l_Lean_Message_toString(v_a_2695_, v___x_2694_);
v_ref_2697_ = lean_ctor_get(v___y_2690_, 2);
v___x_2698_ = l_IO_eprintln___at___00main_spec__6(v___x_2696_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v___x_2699_; size_t v___x_2700_; size_t v___x_2701_; 
lean_dec_ref_known(v___x_2698_, 1);
v___x_2699_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_2700_ = ((size_t)1ULL);
v___x_2701_ = lean_usize_add(v_i_2688_, v___x_2700_);
v_i_2688_ = v___x_2701_;
v_b_2689_ = v___x_2699_;
goto _start;
}
else
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2714_; 
v_a_2703_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2705_ = v___x_2698_;
v_isShared_2706_ = v_isSharedCheck_2714_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2698_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2714_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2712_; 
v___x_2707_ = lean_io_error_to_string(v_a_2703_);
v___x_2708_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
v___x_2709_ = l_Lean_MessageData_ofFormat(v___x_2708_);
lean_inc(v_ref_2697_);
v___x_2710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2710_, 0, v_ref_2697_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 0, v___x_2710_);
v___x_2712_ = v___x_2705_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2710_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg___boxed(lean_object* v_as_2715_, lean_object* v_sz_2716_, lean_object* v_i_2717_, lean_object* v_b_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
size_t v_sz_boxed_2721_; size_t v_i_boxed_2722_; lean_object* v_res_2723_; 
v_sz_boxed_2721_ = lean_unbox_usize(v_sz_2716_);
lean_dec(v_sz_2716_);
v_i_boxed_2722_ = lean_unbox_usize(v_i_2717_);
lean_dec(v_i_2717_);
v_res_2723_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(v_as_2715_, v_sz_boxed_2721_, v_i_boxed_2722_, v_b_2718_, v___y_2719_);
lean_dec_ref(v___y_2719_);
lean_dec_ref(v_as_2715_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27(lean_object* v_as_2724_, size_t v_sz_2725_, size_t v_i_2726_, lean_object* v_b_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
uint8_t v___x_2731_; 
v___x_2731_ = lean_usize_dec_lt(v_i_2726_, v_sz_2725_);
if (v___x_2731_ == 0)
{
lean_object* v___x_2732_; 
v___x_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2732_, 0, v_b_2727_);
return v___x_2732_;
}
else
{
uint8_t v___x_2733_; lean_object* v_a_2734_; lean_object* v___x_2735_; lean_object* v_ref_2736_; lean_object* v___x_2737_; 
lean_dec_ref(v_b_2727_);
v___x_2733_ = 0;
v_a_2734_ = lean_array_uget_borrowed(v_as_2724_, v_i_2726_);
lean_inc(v_a_2734_);
v___x_2735_ = l_Lean_Message_toString(v_a_2734_, v___x_2733_);
v_ref_2736_ = lean_ctor_get(v___y_2728_, 2);
v___x_2737_ = l_IO_eprintln___at___00main_spec__6(v___x_2735_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v___x_2738_; size_t v___x_2739_; size_t v___x_2740_; lean_object* v___x_2741_; 
lean_dec_ref_known(v___x_2737_, 1);
v___x_2738_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_2739_ = ((size_t)1ULL);
v___x_2740_ = lean_usize_add(v_i_2726_, v___x_2739_);
v___x_2741_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(v_as_2724_, v_sz_2725_, v___x_2740_, v___x_2738_, v___y_2728_);
return v___x_2741_;
}
else
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2753_; 
v_a_2742_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2744_ = v___x_2737_;
v_isShared_2745_ = v_isSharedCheck_2753_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2737_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2753_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2751_; 
v___x_2746_ = lean_io_error_to_string(v_a_2742_);
v___x_2747_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2746_);
v___x_2748_ = l_Lean_MessageData_ofFormat(v___x_2747_);
lean_inc(v_ref_2736_);
v___x_2749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2749_, 0, v_ref_2736_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 0, v___x_2749_);
v___x_2751_ = v___x_2744_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v___x_2749_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27___boxed(lean_object* v_as_2754_, lean_object* v_sz_2755_, lean_object* v_i_2756_, lean_object* v_b_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
size_t v_sz_boxed_2761_; size_t v_i_boxed_2762_; lean_object* v_res_2763_; 
v_sz_boxed_2761_ = lean_unbox_usize(v_sz_2755_);
lean_dec(v_sz_2755_);
v_i_boxed_2762_ = lean_unbox_usize(v_i_2756_);
lean_dec(v_i_2756_);
v_res_2763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27(v_as_2754_, v_sz_boxed_2761_, v_i_boxed_2762_, v_b_2757_, v___y_2758_, v___y_2759_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec_ref(v_as_2754_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__11(lean_object* v_t_2764_, lean_object* v_init_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v_root_2769_; lean_object* v_tail_2770_; lean_object* v___x_2771_; 
v_root_2769_ = lean_ctor_get(v_t_2764_, 0);
v_tail_2770_ = lean_ctor_get(v_t_2764_, 1);
v___x_2771_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(v_init_2765_, v_root_2769_, v_init_2765_, v___y_2766_, v___y_2767_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2808_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2774_ = v___x_2771_;
v_isShared_2775_ = v_isSharedCheck_2808_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2771_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2808_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
if (lean_obj_tag(v_a_2772_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2778_; 
v_a_2776_ = lean_ctor_get(v_a_2772_, 0);
lean_inc(v_a_2776_);
lean_dec_ref_known(v_a_2772_, 1);
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 0, v_a_2776_);
v___x_2778_ = v___x_2774_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_a_2776_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
else
{
lean_object* v_a_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; size_t v_sz_2783_; size_t v___x_2784_; lean_object* v___x_2785_; 
lean_del_object(v___x_2774_);
v_a_2780_ = lean_ctor_get(v_a_2772_, 0);
lean_inc(v_a_2780_);
lean_dec_ref_known(v_a_2772_, 1);
v___x_2781_ = lean_box(0);
v___x_2782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2781_);
lean_ctor_set(v___x_2782_, 1, v_a_2780_);
v_sz_2783_ = lean_array_size(v_tail_2770_);
v___x_2784_ = ((size_t)0ULL);
v___x_2785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27(v_tail_2770_, v_sz_2783_, v___x_2784_, v___x_2782_, v___y_2766_, v___y_2767_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2799_; 
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2788_ = v___x_2785_;
v_isShared_2789_ = v_isSharedCheck_2799_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2785_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2799_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v_fst_2790_; 
v_fst_2790_ = lean_ctor_get(v_a_2786_, 0);
if (lean_obj_tag(v_fst_2790_) == 0)
{
lean_object* v_snd_2791_; lean_object* v___x_2793_; 
v_snd_2791_ = lean_ctor_get(v_a_2786_, 1);
lean_inc(v_snd_2791_);
lean_dec(v_a_2786_);
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 0, v_snd_2791_);
v___x_2793_ = v___x_2788_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_snd_2791_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
else
{
lean_object* v_val_2795_; lean_object* v___x_2797_; 
lean_inc_ref(v_fst_2790_);
lean_dec(v_a_2786_);
v_val_2795_ = lean_ctor_get(v_fst_2790_, 0);
lean_inc(v_val_2795_);
lean_dec_ref_known(v_fst_2790_, 1);
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 0, v_val_2795_);
v___x_2797_ = v___x_2788_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_val_2795_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
v_a_2800_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2785_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2785_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
}
}
else
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
v_a_2809_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2771_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2771_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__11___boxed(lean_object* v_t_2817_, lean_object* v_init_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_Lean_PersistentArray_forIn___at___00main_spec__11(v_t_2817_, v_init_2818_, v___y_2819_, v___y_2820_);
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec_ref(v_t_2817_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(lean_object* v_as_2823_, size_t v_sz_2824_, size_t v_i_2825_, lean_object* v_b_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
uint8_t v___x_2830_; 
v___x_2830_ = lean_usize_dec_lt(v_i_2825_, v_sz_2824_);
if (v___x_2830_ == 0)
{
lean_object* v___x_2831_; 
v___x_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2831_, 0, v_b_2826_);
return v___x_2831_;
}
else
{
lean_object* v_a_2832_; lean_object* v_declNames_2833_; lean_object* v___x_2834_; size_t v_sz_2835_; size_t v___x_2836_; lean_object* v___x_2837_; 
v_a_2832_ = lean_array_uget_borrowed(v_as_2823_, v_i_2825_);
v_declNames_2833_ = lean_ctor_get(v_a_2832_, 0);
v___x_2834_ = lean_box(0);
v_sz_2835_ = lean_array_size(v_declNames_2833_);
v___x_2836_ = ((size_t)0ULL);
v___x_2837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(v_declNames_2833_, v_sz_2835_, v___x_2836_, v___x_2834_, v___y_2827_, v___y_2828_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v___x_2838_; 
lean_dec_ref_known(v___x_2837_, 1);
v___x_2838_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v___y_2828_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v_unreported_2840_; lean_object* v___x_2841_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_a_2839_);
lean_dec_ref_known(v___x_2838_, 1);
v_unreported_2840_ = lean_ctor_get(v_a_2839_, 1);
lean_inc_ref(v_unreported_2840_);
lean_dec(v_a_2839_);
v___x_2841_ = l_Lean_PersistentArray_forIn___at___00main_spec__11(v_unreported_2840_, v___x_2834_, v___y_2827_, v___y_2828_);
lean_dec_ref(v_unreported_2840_);
if (lean_obj_tag(v___x_2841_) == 0)
{
size_t v___x_2842_; size_t v___x_2843_; 
lean_dec_ref_known(v___x_2841_, 1);
v___x_2842_ = ((size_t)1ULL);
v___x_2843_ = lean_usize_add(v_i_2825_, v___x_2842_);
v_i_2825_ = v___x_2843_;
v_b_2826_ = v___x_2834_;
goto _start;
}
else
{
return v___x_2841_;
}
}
else
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
v_a_2845_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2838_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2838_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
else
{
return v___x_2837_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___boxed(lean_object* v_as_2853_, lean_object* v_sz_2854_, lean_object* v_i_2855_, lean_object* v_b_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_){
_start:
{
size_t v_sz_boxed_2860_; size_t v_i_boxed_2861_; lean_object* v_res_2862_; 
v_sz_boxed_2860_ = lean_unbox_usize(v_sz_2854_);
lean_dec(v_sz_2854_);
v_i_boxed_2861_ = lean_unbox_usize(v_i_2855_);
lean_dec(v_i_2855_);
v_res_2862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(v_as_2853_, v_sz_boxed_2860_, v_i_boxed_2861_, v_b_2856_, v___y_2857_, v___y_2858_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
lean_dec_ref(v_as_2853_);
return v_res_2862_;
}
}
static lean_object* _init_l_main___closed__1(void){
_start:
{
lean_object* v___x_2864_; 
v___x_2864_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg();
return v___x_2864_;
}
}
static lean_object* _init_l_main___closed__2(void){
_start:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2865_ = l_Lean_instInhabitedClassState_default;
v___x_2866_ = lean_box(0);
v___x_2867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2866_);
lean_ctor_set(v___x_2867_, 1, v___x_2865_);
return v___x_2867_;
}
}
static lean_object* _init_l_main___closed__3(void){
_start:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2868_ = l_Lean_Meta_Match_Extension_instInhabitedState;
v___x_2869_ = lean_box(0);
v___x_2870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2869_);
lean_ctor_set(v___x_2870_, 1, v___x_2868_);
return v___x_2870_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_2871_; 
v___x_2871_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_2871_;
}
}
static lean_object* _init_l_main___closed__5(void){
_start:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2872_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2873_ = lean_box(0);
v___x_2874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2873_);
lean_ctor_set(v___x_2874_, 1, v___x_2872_);
return v___x_2874_;
}
}
static lean_object* _init_l_main___closed__6(void){
_start:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2875_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_2876_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2875_);
return v___x_2876_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
lean_object* v___x_2877_; 
v___x_2877_ = l_Array_instInhabited___redArg();
return v___x_2877_;
}
}
static lean_object* _init_l_main___closed__17(void){
_start:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2890_ = ((lean_object*)(l_main___closed__16));
v___x_2891_ = lean_unsigned_to_nat(27u);
v___x_2892_ = lean_unsigned_to_nat(160u);
v___x_2893_ = ((lean_object*)(l_main___closed__15));
v___x_2894_ = ((lean_object*)(l_main___closed__14));
v___x_2895_ = l_mkPanicMessageWithDecl(v___x_2894_, v___x_2893_, v___x_2892_, v___x_2891_, v___x_2890_);
return v___x_2895_;
}
}
static lean_object* _init_l_main___closed__19(void){
_start:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2897_ = ((lean_object*)(l_main___closed__16));
v___x_2898_ = lean_unsigned_to_nat(51u);
v___x_2899_ = lean_unsigned_to_nat(133u);
v___x_2900_ = ((lean_object*)(l_main___closed__15));
v___x_2901_ = ((lean_object*)(l_main___closed__14));
v___x_2902_ = l_mkPanicMessageWithDecl(v___x_2901_, v___x_2900_, v___x_2899_, v___x_2898_, v___x_2897_);
return v___x_2902_;
}
}
static lean_object* _init_l_main___closed__20(void){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2903_ = lean_unsigned_to_nat(1u);
v___x_2904_ = l_Lean_firstFrontendMacroScope;
v___x_2905_ = lean_nat_add(v___x_2904_, v___x_2903_);
return v___x_2905_;
}
}
static lean_object* _init_l_main___closed__24(void){
_start:
{
lean_object* v___x_2912_; uint64_t v___x_2913_; lean_object* v___x_2914_; 
v___x_2912_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
v___x_2913_ = 0ULL;
v___x_2914_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2914_, 0, v___x_2912_);
lean_ctor_set_uint64(v___x_2914_, sizeof(void*)*1, v___x_2913_);
return v___x_2914_;
}
}
static lean_object* _init_l_main___closed__25(void){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2915_;
}
}
static lean_object* _init_l_main___closed__26(void){
_start:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = lean_obj_once(&l_main___closed__25, &l_main___closed__25_once, _init_l_main___closed__25);
v___x_2917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2916_);
return v___x_2917_;
}
}
static lean_object* _init_l_main___closed__27(void){
_start:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2918_ = lean_obj_once(&l_main___closed__26, &l_main___closed__26_once, _init_l_main___closed__26);
v___x_2919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
lean_ctor_set(v___x_2919_, 1, v___x_2918_);
return v___x_2919_;
}
}
static lean_object* _init_l_main___closed__29(void){
_start:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2922_ = lean_unsigned_to_nat(0u);
v___x_2923_ = l_Lean_Options_empty;
v___x_2924_ = ((lean_object*)(l_main___closed__28));
v___x_2925_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2924_);
lean_ctor_set(v___x_2925_, 1, v___x_2923_);
lean_ctor_set(v___x_2925_, 2, v___x_2924_);
lean_ctor_set(v___x_2925_, 3, v___x_2922_);
lean_ctor_set(v___x_2925_, 4, v___x_2922_);
lean_ctor_set(v___x_2925_, 5, v___x_2922_);
return v___x_2925_;
}
}
static lean_object* _init_l_main___closed__30(void){
_start:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2926_ = l_Lean_NameSet_empty;
v___x_2927_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
v___x_2928_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2927_);
lean_ctor_set(v___x_2928_, 1, v___x_2927_);
lean_ctor_set(v___x_2928_, 2, v___x_2926_);
return v___x_2928_;
}
}
static lean_object* _init_l_main___closed__31(void){
_start:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; uint8_t v___x_2931_; lean_object* v___x_2932_; 
v___x_2929_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___closed__1);
v___x_2930_ = lean_obj_once(&l_main___closed__26, &l_main___closed__26_once, _init_l_main___closed__26);
v___x_2931_ = 1;
v___x_2932_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2932_, 0, v___x_2930_);
lean_ctor_set(v___x_2932_, 1, v___x_2930_);
lean_ctor_set(v___x_2932_, 2, v___x_2929_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3, v___x_2931_);
return v___x_2932_;
}
}
static uint8_t _init_l_main___closed__35(void){
_start:
{
uint8_t v___x_2937_; uint8_t v___x_2938_; uint8_t v___x_2939_; 
v___x_2937_ = 2;
v___x_2938_ = 0;
v___x_2939_ = l_Lean_instOrdOLeanLevel_ord(v___x_2938_, v___x_2937_);
return v___x_2939_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_2940_; lean_object* v___x_2941_; 
v___x_2940_ = 1;
v___x_2941_ = lean_box_uint32(v___x_2940_);
return v___x_2941_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_2942_; lean_object* v___x_2943_; 
v___x_2942_ = 0;
v___x_2943_ = lean_box_uint32(v___x_2942_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_2944_){
_start:
{
if (lean_obj_tag(v_args_2944_) == 1)
{
lean_object* v_tail_2969_; 
v_tail_2969_ = lean_ctor_get(v_args_2944_, 1);
lean_inc(v_tail_2969_);
if (lean_obj_tag(v_tail_2969_) == 1)
{
lean_object* v_tail_2970_; 
v_tail_2970_ = lean_ctor_get(v_tail_2969_, 1);
lean_inc(v_tail_2970_);
if (lean_obj_tag(v_tail_2970_) == 1)
{
lean_object* v_head_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_3651_; 
v_head_2971_ = lean_ctor_get(v_args_2944_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v_args_2944_);
if (v_isSharedCheck_3651_ == 0)
{
lean_object* v_unused_3652_; 
v_unused_3652_ = lean_ctor_get(v_args_2944_, 1);
lean_dec(v_unused_3652_);
v___x_2973_ = v_args_2944_;
v_isShared_2974_ = v_isSharedCheck_3651_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_head_2971_);
lean_dec(v_args_2944_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_3651_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v_head_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_3649_; 
v_head_2975_ = lean_ctor_get(v_tail_2969_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v_tail_2969_);
if (v_isSharedCheck_3649_ == 0)
{
lean_object* v_unused_3650_; 
v_unused_3650_ = lean_ctor_get(v_tail_2969_, 1);
lean_dec(v_unused_3650_);
v___x_2977_ = v_tail_2969_;
v_isShared_2978_ = v_isSharedCheck_3649_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_head_2975_);
lean_dec(v_tail_2969_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_3649_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v_head_2979_; lean_object* v_tail_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_3648_; 
v_head_2979_ = lean_ctor_get(v_tail_2970_, 0);
v_tail_2980_ = lean_ctor_get(v_tail_2970_, 1);
v_isSharedCheck_3648_ = !lean_is_exclusive(v_tail_2970_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_2982_ = v_tail_2970_;
v_isShared_2983_ = v_isSharedCheck_3648_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_tail_2980_);
lean_inc(v_head_2979_);
lean_dec(v_tail_2970_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_3648_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2984_ = lean_obj_once(&l_main___closed__1, &l_main___closed__1_once, _init_l_main___closed__1);
v___x_2985_ = lean_box(0);
v___x_2986_ = lean_obj_once(&l_main___closed__2, &l_main___closed__2_once, _init_l_main___closed__2);
v___x_2987_ = lean_obj_once(&l_main___closed__3, &l_main___closed__3_once, _init_l_main___closed__3);
v___x_2988_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2989_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2990_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_2991_ = lean_box(1);
v___x_2992_ = ((lean_object*)(l_main___closed__8));
v___x_2993_ = l_Lean_ModuleSetup_load(v_head_2971_);
lean_dec(v_head_2971_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v_name_2995_; lean_object* v_package_x3f_2996_; lean_object* v_importArts_2997_; lean_object* v_options_2998_; lean_object* v___f_2999_; uint8_t v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3004_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_a_2994_);
lean_dec_ref_known(v___x_2993_, 1);
v_name_2995_ = lean_ctor_get(v_a_2994_, 0);
lean_inc(v_name_2995_);
v_package_x3f_2996_ = lean_ctor_get(v_a_2994_, 1);
lean_inc(v_package_x3f_2996_);
v_importArts_2997_ = lean_ctor_get(v_a_2994_, 3);
lean_inc(v_importArts_2997_);
v_options_2998_ = lean_ctor_get(v_a_2994_, 6);
lean_inc(v_options_2998_);
lean_dec(v_a_2994_);
v___f_2999_ = lean_alloc_closure((void*)(l_main___lam__0), 2, 1);
lean_closure_set(v___f_2999_, 0, v_package_x3f_2996_);
v___x_3000_ = 0;
v___x_3001_ = l_Lean_LeanOptions_toOptions(v_options_2998_);
v___x_3002_ = lean_box(v___x_3000_);
if (v_isShared_2983_ == 0)
{
lean_ctor_set_tag(v___x_2982_, 0);
lean_ctor_set(v___x_2982_, 1, v___x_3001_);
lean_ctor_set(v___x_2982_, 0, v___x_3002_);
v___x_3004_ = v___x_2982_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3002_);
lean_ctor_set(v_reuseFailAlloc_3639_, 1, v___x_3001_);
v___x_3004_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
lean_object* v___x_3005_; 
v___x_3005_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_tail_2980_, v___x_3004_);
lean_dec(v_tail_2980_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; lean_object* v_fst_3007_; lean_object* v_snd_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3630_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_a_3006_);
lean_dec_ref_known(v___x_3005_, 1);
v_fst_3007_ = lean_ctor_get(v_a_3006_, 0);
v_snd_3008_ = lean_ctor_get(v_a_3006_, 1);
v_isSharedCheck_3630_ = !lean_is_exclusive(v_a_3006_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3010_ = v_a_3006_;
v_isShared_3011_ = v_isSharedCheck_3630_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_snd_3008_);
lean_inc(v_fst_3007_);
lean_dec(v_a_3006_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3630_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3012_; uint8_t v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; uint8_t v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; uint8_t v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v_nextMacroScope_3191_; lean_object* v_ngen_3192_; lean_object* v_auxDeclNGen_3193_; lean_object* v_traceState_3194_; lean_object* v_recordedDeps_3195_; lean_object* v_messages_3196_; lean_object* v_infoState_3197_; lean_object* v_snapshotTasks_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; uint8_t v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; uint16_t v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v_fileName_3247_; lean_object* v_fileMap_3248_; lean_object* v_currNamespace_3249_; lean_object* v_openDecls_3250_; lean_object* v_initHeartbeats_3251_; lean_object* v_maxHeartbeats_3252_; lean_object* v_quotContext_3253_; lean_object* v_currMacroScope_3254_; lean_object* v_cancelTk_x3f_3255_; lean_object* v_inheritedTraceOptions_3256_; lean_object* v_currRecDepth_3257_; lean_object* v_ref_3258_; uint8_t v_suppressElabErrors_3259_; uint8_t v_isRecordingDeps_3260_; lean_object* v___y_3261_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; uint8_t v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; uint8_t v___y_3294_; uint16_t v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___x_3345_; 
v___x_3012_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_3013_ = 1;
v___x_3014_ = l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(v_snd_3008_, v___x_3012_, v___x_3013_);
v___x_3015_ = l_Lean_maxHeartbeats;
v___x_3016_ = lean_unsigned_to_nat(0u);
v___x_3017_ = l_Lean_Option_set___at___00main_spec__3(v___x_3014_, v___x_3015_, v___x_3016_);
v___x_3345_ = lean_init_search_path();
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; uint8_t v___x_3351_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; uint8_t v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3522_; lean_object* v___y_3523_; uint8_t v___y_3594_; uint8_t v___x_3621_; 
lean_dec_ref_known(v___x_3345_, 1);
v___x_3346_ = ((lean_object*)(l_main___closed__18));
lean_inc(v_name_2995_);
v___x_3347_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3347_, 0, v_name_2995_);
lean_ctor_set_uint8(v___x_3347_, sizeof(void*)*1, v___x_3013_);
lean_ctor_set_uint8(v___x_3347_, sizeof(void*)*1 + 1, v___x_3013_);
lean_ctor_set_uint8(v___x_3347_, sizeof(void*)*1 + 2, v___x_3000_);
v___x_3348_ = lean_unsigned_to_nat(1u);
v___x_3349_ = lean_mk_empty_array_with_capacity(v___x_3348_);
v___x_3350_ = lean_array_push(v___x_3349_, v___x_3347_);
v___x_3351_ = 0;
v___x_3621_ = lean_uint8_once(&l_main___closed__35, &l_main___closed__35_once, _init_l_main___closed__35);
if (v___x_3621_ == 0)
{
v___y_3594_ = v___x_3013_;
goto v___jp_3593_;
}
else
{
v___y_3594_ = v___x_3000_;
goto v___jp_3593_;
}
v___jp_3352_:
{
lean_object* v___x_3357_; lean_object* v_moduleData_3358_; lean_object* v___x_3359_; uint8_t v___x_3360_; 
v___x_3357_ = l_Lean_Environment_header(v___y_3356_);
v_moduleData_3358_ = lean_ctor_get(v___x_3357_, 7);
lean_inc_ref(v_moduleData_3358_);
lean_dec_ref(v___x_3357_);
v___x_3359_ = lean_array_get_size(v_moduleData_3358_);
v___x_3360_ = lean_nat_dec_lt(v___y_3354_, v___x_3359_);
if (v___x_3360_ == 0)
{
lean_object* v___x_3361_; lean_object* v___x_3362_; 
lean_dec_ref(v_moduleData_3358_);
lean_dec_ref(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec_ref(v___x_3017_);
lean_del_object(v___x_3010_);
lean_dec(v_fst_3007_);
lean_dec(v_name_2995_);
lean_dec(v_head_2979_);
lean_del_object(v___x_2977_);
lean_dec(v_head_2975_);
v___x_3361_ = lean_obj_once(&l_main___closed__19, &l_main___closed__19_once, _init_l_main___closed__19);
v___x_3362_ = l_panic___at___00main_spec__5(v___x_3361_);
return v___x_3362_;
}
else
{
lean_object* v_base_3363_; lean_object* v_private_3364_; lean_object* v_header_3365_; lean_object* v_serverBaseExts_3366_; lean_object* v_checked_3367_; lean_object* v_asyncConstsMap_3368_; lean_object* v_asyncCtx_x3f_3369_; lean_object* v_importRealizationCtx_x3f_3370_; lean_object* v_localRealizationCtxMap_3371_; lean_object* v_allRealizations_3372_; uint8_t v_isExporting_3373_; uint8_t v_isRecordingDeps_3374_; lean_object* v_synthCacheRaw_x3f_3375_; lean_object* v_declChangeLog_3376_; lean_object* v_recordingConstGen_3377_; lean_object* v_constAddedGens_3378_; lean_object* v_constGen_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3462_; 
v_base_3363_ = lean_ctor_get(v___y_3356_, 0);
lean_inc_ref(v_base_3363_);
v_private_3364_ = lean_ctor_get(v_base_3363_, 0);
lean_inc(v_private_3364_);
v_header_3365_ = lean_ctor_get(v_private_3364_, 7);
lean_inc_ref(v_header_3365_);
v_serverBaseExts_3366_ = lean_ctor_get(v___y_3356_, 1);
v_checked_3367_ = lean_ctor_get(v___y_3356_, 2);
v_asyncConstsMap_3368_ = lean_ctor_get(v___y_3356_, 3);
v_asyncCtx_x3f_3369_ = lean_ctor_get(v___y_3356_, 4);
v_importRealizationCtx_x3f_3370_ = lean_ctor_get(v___y_3356_, 5);
v_localRealizationCtxMap_3371_ = lean_ctor_get(v___y_3356_, 6);
v_allRealizations_3372_ = lean_ctor_get(v___y_3356_, 7);
v_isExporting_3373_ = lean_ctor_get_uint8(v___y_3356_, sizeof(void*)*13);
v_isRecordingDeps_3374_ = lean_ctor_get_uint8(v___y_3356_, sizeof(void*)*13 + 1);
v_synthCacheRaw_x3f_3375_ = lean_ctor_get(v___y_3356_, 8);
v_declChangeLog_3376_ = lean_ctor_get(v___y_3356_, 9);
v_recordingConstGen_3377_ = lean_ctor_get(v___y_3356_, 10);
v_constAddedGens_3378_ = lean_ctor_get(v___y_3356_, 11);
v_constGen_3379_ = lean_ctor_get(v___y_3356_, 12);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___y_3356_);
if (v_isSharedCheck_3462_ == 0)
{
lean_object* v_unused_3463_; 
v_unused_3463_ = lean_ctor_get(v___y_3356_, 0);
lean_dec(v_unused_3463_);
v___x_3381_ = v___y_3356_;
v_isShared_3382_ = v_isSharedCheck_3462_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_constGen_3379_);
lean_inc(v_constAddedGens_3378_);
lean_inc(v_recordingConstGen_3377_);
lean_inc(v_declChangeLog_3376_);
lean_inc(v_synthCacheRaw_x3f_3375_);
lean_inc(v_allRealizations_3372_);
lean_inc(v_localRealizationCtxMap_3371_);
lean_inc(v_importRealizationCtx_x3f_3370_);
lean_inc(v_asyncCtx_x3f_3369_);
lean_inc(v_asyncConstsMap_3368_);
lean_inc(v_checked_3367_);
lean_inc(v_serverBaseExts_3366_);
lean_dec(v___y_3356_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3462_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v_public_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3460_; 
v_public_3383_ = lean_ctor_get(v_base_3363_, 1);
v_isSharedCheck_3460_ = !lean_is_exclusive(v_base_3363_);
if (v_isSharedCheck_3460_ == 0)
{
lean_object* v_unused_3461_; 
v_unused_3461_ = lean_ctor_get(v_base_3363_, 0);
lean_dec(v_unused_3461_);
v___x_3385_ = v_base_3363_;
v_isShared_3386_ = v_isSharedCheck_3460_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_public_3383_);
lean_dec(v_base_3363_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3460_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v_constants_3387_; uint8_t v_quotInit_3388_; lean_object* v_diagnostics_3389_; lean_object* v_const2ModIdx_3390_; lean_object* v_extensions_3391_; lean_object* v_irBaseExts_3392_; lean_object* v_extGens_3393_; lean_object* v_trackedGen_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3458_; 
v_constants_3387_ = lean_ctor_get(v_private_3364_, 0);
v_quotInit_3388_ = lean_ctor_get_uint8(v_private_3364_, sizeof(void*)*8);
v_diagnostics_3389_ = lean_ctor_get(v_private_3364_, 1);
v_const2ModIdx_3390_ = lean_ctor_get(v_private_3364_, 2);
v_extensions_3391_ = lean_ctor_get(v_private_3364_, 3);
v_irBaseExts_3392_ = lean_ctor_get(v_private_3364_, 4);
v_extGens_3393_ = lean_ctor_get(v_private_3364_, 5);
v_trackedGen_3394_ = lean_ctor_get(v_private_3364_, 6);
v_isSharedCheck_3458_ = !lean_is_exclusive(v_private_3364_);
if (v_isSharedCheck_3458_ == 0)
{
lean_object* v_unused_3459_; 
v_unused_3459_ = lean_ctor_get(v_private_3364_, 7);
lean_dec(v_unused_3459_);
v___x_3396_ = v_private_3364_;
v_isShared_3397_ = v_isSharedCheck_3458_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_trackedGen_3394_);
lean_inc(v_extGens_3393_);
lean_inc(v_irBaseExts_3392_);
lean_inc(v_extensions_3391_);
lean_inc(v_const2ModIdx_3390_);
lean_inc(v_diagnostics_3389_);
lean_inc(v_constants_3387_);
lean_dec(v_private_3364_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3458_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
uint32_t v_trustLevel_3398_; lean_object* v_mainModule_3399_; uint8_t v_isModule_3400_; lean_object* v_regions_3401_; lean_object* v_modules_3402_; lean_object* v_moduleNames_3403_; lean_object* v_moduleName2Idx_3404_; lean_object* v_importAllModules_3405_; lean_object* v_moduleData_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3456_; 
v_trustLevel_3398_ = lean_ctor_get_uint32(v_header_3365_, sizeof(void*)*8);
v_mainModule_3399_ = lean_ctor_get(v_header_3365_, 0);
v_isModule_3400_ = lean_ctor_get_uint8(v_header_3365_, sizeof(void*)*8 + 4);
v_regions_3401_ = lean_ctor_get(v_header_3365_, 2);
v_modules_3402_ = lean_ctor_get(v_header_3365_, 3);
v_moduleNames_3403_ = lean_ctor_get(v_header_3365_, 4);
v_moduleName2Idx_3404_ = lean_ctor_get(v_header_3365_, 5);
v_importAllModules_3405_ = lean_ctor_get(v_header_3365_, 6);
v_moduleData_3406_ = lean_ctor_get(v_header_3365_, 7);
v_isSharedCheck_3456_ = !lean_is_exclusive(v_header_3365_);
if (v_isSharedCheck_3456_ == 0)
{
lean_object* v_unused_3457_; 
v_unused_3457_ = lean_ctor_get(v_header_3365_, 1);
lean_dec(v_unused_3457_);
v___x_3408_ = v_header_3365_;
v_isShared_3409_ = v_isSharedCheck_3456_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_moduleData_3406_);
lean_inc(v_importAllModules_3405_);
lean_inc(v_moduleName2Idx_3404_);
lean_inc(v_moduleNames_3403_);
lean_inc(v_modules_3402_);
lean_inc(v_regions_3401_);
lean_inc(v_mainModule_3399_);
lean_dec(v_header_3365_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3456_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3410_; lean_object* v_imports_3411_; lean_object* v___x_3413_; 
v___x_3410_ = lean_array_fget(v_moduleData_3358_, v___y_3354_);
lean_dec_ref(v_moduleData_3358_);
v_imports_3411_ = lean_ctor_get(v___x_3410_, 0);
lean_inc_ref(v_imports_3411_);
lean_dec(v___x_3410_);
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 1, v_imports_3411_);
v___x_3413_ = v___x_3408_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 8, 5);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_mainModule_3399_);
lean_ctor_set(v_reuseFailAlloc_3455_, 1, v_imports_3411_);
lean_ctor_set(v_reuseFailAlloc_3455_, 2, v_regions_3401_);
lean_ctor_set(v_reuseFailAlloc_3455_, 3, v_modules_3402_);
lean_ctor_set(v_reuseFailAlloc_3455_, 4, v_moduleNames_3403_);
lean_ctor_set(v_reuseFailAlloc_3455_, 5, v_moduleName2Idx_3404_);
lean_ctor_set(v_reuseFailAlloc_3455_, 6, v_importAllModules_3405_);
lean_ctor_set(v_reuseFailAlloc_3455_, 7, v_moduleData_3406_);
lean_ctor_set_uint32(v_reuseFailAlloc_3455_, sizeof(void*)*8, v_trustLevel_3398_);
lean_ctor_set_uint8(v_reuseFailAlloc_3455_, sizeof(void*)*8 + 4, v_isModule_3400_);
v___x_3413_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
lean_object* v___x_3415_; 
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 7, v___x_3413_);
v___x_3415_ = v___x_3396_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_constants_3387_);
lean_ctor_set(v_reuseFailAlloc_3454_, 1, v_diagnostics_3389_);
lean_ctor_set(v_reuseFailAlloc_3454_, 2, v_const2ModIdx_3390_);
lean_ctor_set(v_reuseFailAlloc_3454_, 3, v_extensions_3391_);
lean_ctor_set(v_reuseFailAlloc_3454_, 4, v_irBaseExts_3392_);
lean_ctor_set(v_reuseFailAlloc_3454_, 5, v_extGens_3393_);
lean_ctor_set(v_reuseFailAlloc_3454_, 6, v_trackedGen_3394_);
lean_ctor_set(v_reuseFailAlloc_3454_, 7, v___x_3413_);
lean_ctor_set_uint8(v_reuseFailAlloc_3454_, sizeof(void*)*8, v_quotInit_3388_);
v___x_3415_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
lean_object* v___x_3417_; 
if (v_isShared_3386_ == 0)
{
lean_ctor_set(v___x_3385_, 0, v___x_3415_);
v___x_3417_ = v___x_3385_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3415_);
lean_ctor_set(v_reuseFailAlloc_3453_, 1, v_public_3383_);
v___x_3417_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
lean_object* v___x_3419_; 
if (v_isShared_3382_ == 0)
{
lean_ctor_set(v___x_3381_, 0, v___x_3417_);
v___x_3419_ = v___x_3381_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v___x_3417_);
lean_ctor_set(v_reuseFailAlloc_3452_, 1, v_serverBaseExts_3366_);
lean_ctor_set(v_reuseFailAlloc_3452_, 2, v_checked_3367_);
lean_ctor_set(v_reuseFailAlloc_3452_, 3, v_asyncConstsMap_3368_);
lean_ctor_set(v_reuseFailAlloc_3452_, 4, v_asyncCtx_x3f_3369_);
lean_ctor_set(v_reuseFailAlloc_3452_, 5, v_importRealizationCtx_x3f_3370_);
lean_ctor_set(v_reuseFailAlloc_3452_, 6, v_localRealizationCtxMap_3371_);
lean_ctor_set(v_reuseFailAlloc_3452_, 7, v_allRealizations_3372_);
lean_ctor_set(v_reuseFailAlloc_3452_, 8, v_synthCacheRaw_x3f_3375_);
lean_ctor_set(v_reuseFailAlloc_3452_, 9, v_declChangeLog_3376_);
lean_ctor_set(v_reuseFailAlloc_3452_, 10, v_recordingConstGen_3377_);
lean_ctor_set(v_reuseFailAlloc_3452_, 11, v_constAddedGens_3378_);
lean_ctor_set(v_reuseFailAlloc_3452_, 12, v_constGen_3379_);
lean_ctor_set_uint8(v_reuseFailAlloc_3452_, sizeof(void*)*13, v_isExporting_3373_);
lean_ctor_set_uint8(v_reuseFailAlloc_3452_, sizeof(void*)*13 + 1, v_isRecordingDeps_3374_);
v___x_3419_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; uint16_t v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v_env_3446_; uint8_t v___x_3447_; uint16_t v___x_3448_; uint16_t v___x_3449_; uint16_t v___x_3450_; uint8_t v___x_3451_; 
v___x_3420_ = l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
v___x_3421_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2992_, v___x_3420_, v___x_3419_, v___y_3354_, v___x_3351_);
lean_dec(v___y_3354_);
v___x_3422_ = l_Lean_instInhabitedFileMap_default;
v___x_3423_ = lean_unsigned_to_nat(1000u);
v___x_3424_ = l_Lean_Core_getMaxHeartbeats(v___x_3017_);
v___x_3425_ = l_Lean_firstFrontendMacroScope;
v___x_3426_ = lean_box(0);
v___x_3427_ = lean_box(0);
v___x_3428_ = l_Lean_OptionFlags_ofOptions(v___x_3017_);
v___x_3429_ = lean_obj_once(&l_main___closed__20, &l_main___closed__20_once, _init_l_main___closed__20);
v___x_3430_ = ((lean_object*)(l_main___closed__23));
lean_inc_n(v___y_3355_, 3);
v___x_3431_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3431_, 0, v___y_3355_);
lean_ctor_set(v___x_3431_, 1, v___x_3348_);
lean_ctor_set(v___x_3431_, 2, v___x_2985_);
v___x_3432_ = lean_obj_once(&l_main___closed__24, &l_main___closed__24_once, _init_l_main___closed__24);
v___x_3433_ = lean_obj_once(&l_main___closed__27, &l_main___closed__27_once, _init_l_main___closed__27);
v___x_3434_ = ((lean_object*)(l_main___closed__28));
v___x_3435_ = l_Lean_Options_empty;
v___x_3436_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_3437_ = lean_obj_once(&l_main___closed__30, &l_main___closed__30_once, _init_l_main___closed__30);
v___x_3438_ = lean_obj_once(&l_main___closed__31, &l_main___closed__31_once, _init_l_main___closed__31);
lean_inc_ref(v___x_3431_);
v___x_3439_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3419_);
lean_ctor_set(v___x_3439_, 1, v___x_3429_);
lean_ctor_set(v___x_3439_, 2, v___x_3430_);
lean_ctor_set(v___x_3439_, 3, v___x_3431_);
lean_ctor_set(v___x_3439_, 4, v___x_3432_);
lean_ctor_set(v___x_3439_, 5, v___x_3433_);
lean_ctor_set(v___x_3439_, 6, v___x_3436_);
lean_ctor_set(v___x_3439_, 7, v___x_3437_);
lean_ctor_set(v___x_3439_, 8, v___x_3438_);
lean_ctor_set(v___x_3439_, 9, v___x_3434_);
v___x_3440_ = lean_st_mk_ref(v___x_3439_);
v___x_3441_ = l_Lean_inheritedTraceOptions;
v___x_3442_ = lean_st_ref_get(v___x_3441_);
lean_inc(v___x_3442_);
lean_inc(v___x_3424_);
lean_inc_ref(v___x_3017_);
lean_inc(v_head_2975_);
v___x_3443_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3443_, 0, v_head_2975_);
lean_ctor_set(v___x_3443_, 1, v___x_3422_);
lean_ctor_set(v___x_3443_, 2, v___x_3017_);
lean_ctor_set(v___x_3443_, 3, v___x_3423_);
lean_ctor_set(v___x_3443_, 4, v___y_3355_);
lean_ctor_set(v___x_3443_, 5, v___x_2985_);
lean_ctor_set(v___x_3443_, 6, v___x_3016_);
lean_ctor_set(v___x_3443_, 7, v___x_3424_);
lean_ctor_set(v___x_3443_, 8, v___y_3355_);
lean_ctor_set(v___x_3443_, 9, v___x_3425_);
lean_ctor_set(v___x_3443_, 10, v___x_3426_);
lean_ctor_set(v___x_3443_, 11, v___x_3442_);
v___x_3444_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3444_, 0, v___x_3443_);
lean_ctor_set(v___x_3444_, 1, v___x_3016_);
lean_ctor_set(v___x_3444_, 2, v___x_3427_);
lean_ctor_set_uint16(v___x_3444_, sizeof(void*)*3, v___x_3428_);
lean_ctor_set_uint8(v___x_3444_, sizeof(void*)*3 + 2, v___x_3000_);
lean_ctor_set_uint8(v___x_3444_, sizeof(void*)*3 + 3, v___x_3000_);
v___x_3445_ = lean_st_ref_get(v___x_3440_);
v_env_3446_ = lean_ctor_get(v___x_3445_, 0);
lean_inc_ref(v_env_3446_);
lean_dec(v___x_3445_);
v___x_3447_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3446_);
lean_dec_ref(v_env_3446_);
v___x_3448_ = 512;
v___x_3449_ = lean_uint16_land(v___x_3428_, v___x_3448_);
v___x_3450_ = 0;
v___x_3451_ = lean_uint16_dec_eq(v___x_3449_, v___x_3450_);
if (v___x_3451_ == 0)
{
if (v___x_3447_ == 0)
{
lean_dec(v___x_3442_);
lean_dec(v___x_3424_);
v___y_3284_ = v___x_3427_;
v___y_3285_ = v___x_3435_;
v___y_3286_ = v___x_3422_;
v___y_3287_ = v___x_3360_;
v___y_3288_ = v___y_3353_;
v___y_3289_ = v___x_2985_;
v___y_3290_ = v___x_3433_;
v___y_3291_ = v___x_3425_;
v___y_3292_ = v___x_3426_;
v___y_3293_ = v___x_3431_;
v___y_3294_ = v___x_3360_;
v___y_3295_ = v___x_3428_;
v___y_3296_ = v___x_3421_;
v___y_3297_ = v___x_3436_;
v___y_3298_ = v___x_3444_;
v___y_3299_ = v___x_3432_;
v___y_3300_ = v___y_3355_;
v___y_3301_ = v___x_3429_;
v___y_3302_ = v___x_3438_;
v___y_3303_ = v___x_3430_;
v___y_3304_ = v___x_3435_;
v___y_3305_ = v___x_3440_;
v___y_3306_ = v___x_3437_;
v___y_3307_ = v___x_3420_;
v___y_3308_ = v___x_3434_;
v___y_3309_ = v___x_3433_;
goto v___jp_3283_;
}
else
{
lean_dec_ref_known(v___x_3444_, 3);
lean_inc(v_head_2975_);
lean_inc(v___x_3440_);
lean_inc_n(v___y_3355_, 2);
v___y_3223_ = v___x_3427_;
v___y_3224_ = v___x_3435_;
v___y_3225_ = v___x_3422_;
v___y_3226_ = v___y_3353_;
v___y_3227_ = v___x_3360_;
v___y_3228_ = v___x_2985_;
v___y_3229_ = v___x_3426_;
v___y_3230_ = v___x_3425_;
v___y_3231_ = v___x_3433_;
v___y_3232_ = v___x_3431_;
v___y_3233_ = v___x_3428_;
v___y_3234_ = v___x_3421_;
v___y_3235_ = v___x_3436_;
v___y_3236_ = v___x_3432_;
v___y_3237_ = v___y_3355_;
v___y_3238_ = v___x_3429_;
v___y_3239_ = v___x_3438_;
v___y_3240_ = v___x_3430_;
v___y_3241_ = v___x_3435_;
v___y_3242_ = v___x_3440_;
v___y_3243_ = v___x_3420_;
v___y_3244_ = v___x_3437_;
v___y_3245_ = v___x_3434_;
v___y_3246_ = v___x_3433_;
v_fileName_3247_ = v_head_2975_;
v_fileMap_3248_ = v___x_3422_;
v_currNamespace_3249_ = v___y_3355_;
v_openDecls_3250_ = v___x_2985_;
v_initHeartbeats_3251_ = v___x_3016_;
v_maxHeartbeats_3252_ = v___x_3424_;
v_quotContext_3253_ = v___y_3355_;
v_currMacroScope_3254_ = v___x_3425_;
v_cancelTk_x3f_3255_ = v___x_3426_;
v_inheritedTraceOptions_3256_ = v___x_3442_;
v_currRecDepth_3257_ = v___x_3016_;
v_ref_3258_ = v___x_3427_;
v_suppressElabErrors_3259_ = v___x_3000_;
v_isRecordingDeps_3260_ = v___x_3000_;
v___y_3261_ = v___x_3440_;
goto v___jp_3222_;
}
}
else
{
if (v___x_3447_ == 0)
{
lean_dec_ref_known(v___x_3444_, 3);
lean_inc(v_head_2975_);
lean_inc(v___x_3440_);
lean_inc_n(v___y_3355_, 2);
v___y_3223_ = v___x_3427_;
v___y_3224_ = v___x_3435_;
v___y_3225_ = v___x_3422_;
v___y_3226_ = v___y_3353_;
v___y_3227_ = v___x_3360_;
v___y_3228_ = v___x_2985_;
v___y_3229_ = v___x_3426_;
v___y_3230_ = v___x_3425_;
v___y_3231_ = v___x_3433_;
v___y_3232_ = v___x_3431_;
v___y_3233_ = v___x_3428_;
v___y_3234_ = v___x_3421_;
v___y_3235_ = v___x_3436_;
v___y_3236_ = v___x_3432_;
v___y_3237_ = v___y_3355_;
v___y_3238_ = v___x_3429_;
v___y_3239_ = v___x_3438_;
v___y_3240_ = v___x_3430_;
v___y_3241_ = v___x_3435_;
v___y_3242_ = v___x_3440_;
v___y_3243_ = v___x_3420_;
v___y_3244_ = v___x_3437_;
v___y_3245_ = v___x_3434_;
v___y_3246_ = v___x_3433_;
v_fileName_3247_ = v_head_2975_;
v_fileMap_3248_ = v___x_3422_;
v_currNamespace_3249_ = v___y_3355_;
v_openDecls_3250_ = v___x_2985_;
v_initHeartbeats_3251_ = v___x_3016_;
v_maxHeartbeats_3252_ = v___x_3424_;
v_quotContext_3253_ = v___y_3355_;
v_currMacroScope_3254_ = v___x_3425_;
v_cancelTk_x3f_3255_ = v___x_3426_;
v_inheritedTraceOptions_3256_ = v___x_3442_;
v_currRecDepth_3257_ = v___x_3016_;
v_ref_3258_ = v___x_3427_;
v_suppressElabErrors_3259_ = v___x_3000_;
v_isRecordingDeps_3260_ = v___x_3000_;
v___y_3261_ = v___x_3440_;
goto v___jp_3222_;
}
else
{
lean_dec(v___x_3442_);
lean_dec(v___x_3424_);
v___y_3284_ = v___x_3427_;
v___y_3285_ = v___x_3435_;
v___y_3286_ = v___x_3422_;
v___y_3287_ = v___x_3360_;
v___y_3288_ = v___y_3353_;
v___y_3289_ = v___x_2985_;
v___y_3290_ = v___x_3433_;
v___y_3291_ = v___x_3425_;
v___y_3292_ = v___x_3426_;
v___y_3293_ = v___x_3431_;
v___y_3294_ = v___x_3000_;
v___y_3295_ = v___x_3428_;
v___y_3296_ = v___x_3421_;
v___y_3297_ = v___x_3436_;
v___y_3298_ = v___x_3444_;
v___y_3299_ = v___x_3432_;
v___y_3300_ = v___y_3355_;
v___y_3301_ = v___x_3429_;
v___y_3302_ = v___x_3438_;
v___y_3303_ = v___x_3430_;
v___y_3304_ = v___x_3435_;
v___y_3305_ = v___x_3440_;
v___y_3306_ = v___x_3437_;
v___y_3307_ = v___x_3420_;
v___y_3308_ = v___x_3434_;
v___y_3309_ = v___x_3433_;
goto v___jp_3283_;
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
v___jp_3464_:
{
lean_object* v___x_3474_; 
if (v_isShared_2974_ == 0)
{
lean_ctor_set_tag(v___x_2973_, 0);
lean_ctor_set(v___x_2973_, 1, v___y_3472_);
lean_ctor_set(v___x_2973_, 0, v___y_3471_);
v___x_3474_ = v___x_2973_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v___y_3471_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v___y_3472_);
v___x_3474_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
lean_object* v___f_3475_; lean_object* v___x_3476_; 
v___f_3475_ = lean_alloc_closure((void*)(l_main___lam__3___boxed), 2, 1);
lean_closure_set(v___f_3475_, 0, v___x_3474_);
v___x_3476_ = lean_box(0);
if (v___y_3468_ == 0)
{
lean_object* v___x_3477_; 
lean_inc(v___y_3470_);
lean_inc_ref(v___y_3466_);
v___x_3477_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v___y_3466_, v___y_3467_, v___f_3475_, v___x_3476_, v___y_3470_, v___x_3013_);
v___y_3353_ = v___y_3465_;
v___y_3354_ = v___y_3469_;
v___y_3355_ = v___y_3470_;
v___y_3356_ = v___x_3477_;
goto v___jp_3352_;
}
else
{
lean_object* v___x_3478_; lean_object* v___x_3479_; 
lean_inc_ref_n(v___y_3466_, 2);
v___x_3478_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite___redArg(v___y_3466_, v___y_3467_);
lean_dec_ref(v___y_3467_);
lean_inc(v___y_3470_);
v___x_3479_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v___y_3466_, v___x_3478_, v___f_3475_, v___x_3476_, v___y_3470_, v___x_3013_);
v___y_3353_ = v___y_3465_;
v___y_3354_ = v___y_3469_;
v___y_3355_ = v___y_3470_;
v___y_3356_ = v___x_3479_;
goto v___jp_3352_;
}
}
}
v___jp_3481_:
{
lean_object* v___x_3486_; lean_object* v_toEnvExtension_3487_; lean_object* v_asyncMode_3488_; uint8_t v_logWrites_3489_; lean_object* v___x_3490_; lean_object* v_importedEntries_3491_; lean_object* v_state_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; uint8_t v___x_3495_; 
v___x_3486_ = l_Lean_IR_declMapExt;
v_toEnvExtension_3487_ = lean_ctor_get(v___x_3486_, 0);
v_asyncMode_3488_ = lean_ctor_get(v_toEnvExtension_3487_, 2);
v_logWrites_3489_ = lean_ctor_get_uint8(v_toEnvExtension_3487_, sizeof(void*)*6);
lean_inc(v___y_3484_);
lean_inc_ref(v___y_3485_);
v___x_3490_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2989_, v_toEnvExtension_3487_, v___y_3485_, v_asyncMode_3488_, v___y_3484_, v___x_3000_);
v_importedEntries_3491_ = lean_ctor_get(v___x_3490_, 0);
lean_inc_ref(v_importedEntries_3491_);
v_state_3492_ = lean_ctor_get(v___x_3490_, 1);
lean_inc(v_state_3492_);
lean_dec(v___x_3490_);
v___x_3493_ = lean_array_get_borrowed(v___x_2990_, v_importedEntries_3491_, v___y_3483_);
v___x_3494_ = lean_array_get_size(v___x_3493_);
v___x_3495_ = lean_nat_dec_lt(v___x_3016_, v___x_3494_);
if (v___x_3495_ == 0)
{
v___y_3465_ = v___y_3482_;
v___y_3466_ = v_toEnvExtension_3487_;
v___y_3467_ = v___y_3485_;
v___y_3468_ = v_logWrites_3489_;
v___y_3469_ = v___y_3483_;
v___y_3470_ = v___y_3484_;
v___y_3471_ = v_importedEntries_3491_;
v___y_3472_ = v_state_3492_;
goto v___jp_3464_;
}
else
{
size_t v___x_3496_; size_t v___x_3497_; lean_object* v___x_3498_; 
v___x_3496_ = ((size_t)0ULL);
v___x_3497_ = lean_usize_of_nat(v___x_3494_);
lean_inc_ref(v___y_3485_);
v___x_3498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3485_, v___x_3493_, v___x_3496_, v___x_3497_, v_state_3492_);
v___y_3465_ = v___y_3482_;
v___y_3466_ = v_toEnvExtension_3487_;
v___y_3467_ = v___y_3485_;
v___y_3468_ = v_logWrites_3489_;
v___y_3469_ = v___y_3483_;
v___y_3470_ = v___y_3484_;
v___y_3471_ = v_importedEntries_3491_;
v___y_3472_ = v___x_3498_;
goto v___jp_3464_;
}
}
v___jp_3499_:
{
uint8_t v___x_3506_; 
v___x_3506_ = lean_nat_dec_lt(v___x_3016_, v___y_3501_);
if (v___x_3506_ == 0)
{
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3501_);
v___y_3482_ = v___y_3500_;
v___y_3483_ = v___y_3502_;
v___y_3484_ = v___y_3504_;
v___y_3485_ = v___y_3505_;
goto v___jp_3481_;
}
else
{
size_t v___x_3507_; size_t v___x_3508_; lean_object* v___x_3509_; 
v___x_3507_ = ((size_t)0ULL);
v___x_3508_ = lean_usize_of_nat(v___y_3501_);
lean_dec(v___y_3501_);
v___x_3509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3503_, v___x_3507_, v___x_3508_, v___y_3505_);
lean_dec_ref(v___y_3503_);
v___y_3482_ = v___y_3500_;
v___y_3483_ = v___y_3502_;
v___y_3484_ = v___y_3504_;
v___y_3485_ = v___x_3509_;
goto v___jp_3481_;
}
}
v___jp_3510_:
{
lean_object* v___x_3516_; uint8_t v___x_3517_; 
v___x_3516_ = lean_array_get_size(v___y_3515_);
v___x_3517_ = lean_nat_dec_lt(v___x_3016_, v___x_3516_);
if (v___x_3517_ == 0)
{
v___y_3500_ = v___y_3511_;
v___y_3501_ = v___x_3516_;
v___y_3502_ = v___y_3513_;
v___y_3503_ = v___y_3515_;
v___y_3504_ = v___y_3514_;
v___y_3505_ = v___y_3512_;
goto v___jp_3499_;
}
else
{
size_t v___x_3518_; size_t v___x_3519_; lean_object* v___x_3520_; 
v___x_3518_ = ((size_t)0ULL);
v___x_3519_ = lean_usize_of_nat(v___x_3516_);
v___x_3520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3515_, v___x_3518_, v___x_3519_, v___y_3512_);
v___y_3500_ = v___y_3511_;
v___y_3501_ = v___x_3516_;
v___y_3502_ = v___y_3513_;
v___y_3503_ = v___y_3515_;
v___y_3504_ = v___y_3514_;
v___y_3505_ = v___x_3520_;
goto v___jp_3499_;
}
}
v___jp_3521_:
{
lean_object* v___x_3524_; lean_object* v_ext_3525_; lean_object* v___x_3526_; 
v___x_3524_ = l_Lean_Compiler_CSimp_ext;
v_ext_3525_ = lean_ctor_get(v___x_3524_, 1);
lean_inc_ref(v_ext_3525_);
lean_inc(v___y_3522_);
v___x_3526_ = l_main___elam__0___redArg(v___y_3522_, v___x_3000_, v___x_2984_, v_ext_3525_, v___y_3523_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_a_3527_; lean_object* v___x_3528_; lean_object* v_ext_3529_; lean_object* v___x_3530_; 
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_a_3527_);
lean_dec_ref_known(v___x_3526_, 1);
v___x_3528_ = l_Lean_Meta_instanceExtension;
v_ext_3529_ = lean_ctor_get(v___x_3528_, 1);
lean_inc_ref(v_ext_3529_);
lean_inc(v___y_3522_);
v___x_3530_ = l_main___elam__0___redArg(v___y_3522_, v___x_3000_, v___x_2984_, v_ext_3529_, v_a_3527_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3531_);
lean_dec_ref_known(v___x_3530_, 1);
v___x_3532_ = l_Lean_classExtension;
lean_inc(v___y_3522_);
v___x_3533_ = l_main___elam__0___redArg(v___y_3522_, v___x_3000_, v___x_2986_, v___x_3532_, v_a_3531_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v_a_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
lean_inc(v_a_3534_);
lean_dec_ref_known(v___x_3533_, 1);
v___x_3535_ = l_Lean_Meta_Match_Extension_extension;
lean_inc(v___y_3522_);
v___x_3536_ = l_main___elam__0___redArg(v___y_3522_, v___x_3000_, v___x_2987_, v___x_3535_, v_a_3534_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3560_; 
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3539_ = v___x_3536_;
v_isShared_3540_ = v_isSharedCheck_3560_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3536_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3560_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3541_; 
v___x_3541_ = l_Lean_Environment_getModuleIdx_x3f(v_a_3537_, v_name_2995_);
if (lean_obj_tag(v___x_3541_) == 1)
{
lean_object* v_val_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; uint8_t v___x_3547_; 
lean_del_object(v___x_3539_);
v_val_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_val_3542_);
lean_dec_ref_known(v___x_3541_, 1);
v___x_3543_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_3544_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2988_, v___x_3543_, v_a_3537_, v_val_3542_, v___x_3351_);
v___x_3545_ = lean_array_get_size(v___x_3544_);
v___x_3546_ = ((lean_object*)(l_main___closed__32));
v___x_3547_ = lean_nat_dec_lt(v___x_3016_, v___x_3545_);
if (v___x_3547_ == 0)
{
lean_dec_ref(v___x_3544_);
lean_inc(v___y_3522_);
v___y_3511_ = v___y_3522_;
v___y_3512_ = v_a_3537_;
v___y_3513_ = v_val_3542_;
v___y_3514_ = v___y_3522_;
v___y_3515_ = v___x_3546_;
goto v___jp_3510_;
}
else
{
size_t v___x_3548_; size_t v___x_3549_; lean_object* v___x_3550_; 
v___x_3548_ = ((size_t)0ULL);
v___x_3549_ = lean_usize_of_nat(v___x_3545_);
lean_inc(v_a_3537_);
v___x_3550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_3537_, v___x_3544_, v___x_3548_, v___x_3549_, v___x_3546_);
lean_dec_ref(v___x_3544_);
lean_inc(v___y_3522_);
v___y_3511_ = v___y_3522_;
v___y_3512_ = v_a_3537_;
v___y_3513_ = v_val_3542_;
v___y_3514_ = v___y_3522_;
v___y_3515_ = v___x_3550_;
goto v___jp_3510_;
}
}
else
{
lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3558_; 
lean_dec(v___x_3541_);
lean_dec(v_a_3537_);
lean_dec(v___y_3522_);
lean_dec_ref(v___x_3017_);
lean_del_object(v___x_3010_);
lean_dec(v_fst_3007_);
lean_dec(v_head_2979_);
lean_del_object(v___x_2977_);
lean_dec(v_head_2975_);
lean_del_object(v___x_2973_);
v___x_3551_ = ((lean_object*)(l_main___closed__33));
v___x_3552_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2995_, v___x_3013_);
v___x_3553_ = lean_string_append(v___x_3551_, v___x_3552_);
lean_dec_ref(v___x_3552_);
v___x_3554_ = ((lean_object*)(l_main___closed__34));
v___x_3555_ = lean_string_append(v___x_3553_, v___x_3554_);
v___x_3556_ = lean_mk_io_user_error(v___x_3555_);
if (v_isShared_3540_ == 0)
{
lean_ctor_set_tag(v___x_3539_, 1);
lean_ctor_set(v___x_3539_, 0, v___x_3556_);
v___x_3558_ = v___x_3539_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3556_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
else
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
lean_dec(v___y_3522_);
lean_dec_ref(v___x_3017_);
lean_del_object(v___x_3010_);
lean_dec(v_fst_3007_);
lean_dec(v_name_2995_);
lean_dec(v_head_2979_);
lean_del_object(v___x_2977_);
lean_dec(v_head_2975_);
lean_del_object(v___x_2973_);
v_a_3561_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3563_ = v___x_3536_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3536_);
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
else
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_dec(v___y_3522_);
lean_dec_ref(v___x_3017_);
lean_del_object(v___x_3010_);
lean_dec(v_fst_3007_);
lean_dec(v_name_2995_);
lean_dec(v_head_2979_);
lean_del_object(v___x_2977_);
lean_dec(v_head_2975_);
lean_del_object(v___x_2973_);
v_a_3569_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3533_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3533_);
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
lean_dec(v___y_3522_);
lean_dec_ref(v___x_3017_);
lean_del_object(v___x_3010_);
lean_dec(v_fst_3007_);
lean_dec(v_name_2995_);
lean_dec(v_head_2979_);
lean_del_object(v___x_2977_);
lean_dec(v_head_2975_);
lean_del_object(v___x_2973_);
v_a_3577_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3530_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3530_);
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
else
{
lean_object* v_a_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3592_; 
lean_dec(v___y_3522_);
lean_dec_ref(v___x_3017_);
lean_del_object(v___x_3010_);
lean_dec(v_fst_3007_);
lean_dec(v_name_2995_);
lean_dec(v_head_2979_);
lean_del_object(v___x_2977_);
lean_dec(v_head_2975_);
lean_del_object(v___x_2973_);
v_a_3585_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3587_ = v___x_3526_;
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_a_3585_);
lean_dec(v___x_3526_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3590_; 
if (v_isShared_3588_ == 0)
{
v___x_3590_ = v___x_3587_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3585_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
}
v___jp_3593_:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___f_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3595_ = l_Lean_instInhabitedImportState_default;
v___x_3596_ = lean_box(v___x_3351_);
v___x_3597_ = lean_box(v___y_3594_);
v___x_3598_ = lean_box(v___x_3013_);
v___x_3599_ = lean_box(v___x_3000_);
lean_inc_ref(v___x_3017_);
lean_inc(v_name_2995_);
v___f_3600_ = lean_alloc_closure((void*)(l_main___lam__1___boxed), 10, 9);
lean_closure_set(v___f_3600_, 0, v___x_3595_);
lean_closure_set(v___f_3600_, 1, v___x_3350_);
lean_closure_set(v___f_3600_, 2, v___x_3596_);
lean_closure_set(v___f_3600_, 3, v_importArts_2997_);
lean_closure_set(v___f_3600_, 4, v___x_3597_);
lean_closure_set(v___f_3600_, 5, v___x_3598_);
lean_closure_set(v___f_3600_, 6, v_name_2995_);
lean_closure_set(v___f_3600_, 7, v___x_3017_);
lean_closure_set(v___f_3600_, 8, v___x_3599_);
v___x_3601_ = lean_alloc_closure((void*)(l_Lean_withImporting___boxed), 3, 2);
lean_closure_set(v___x_3601_, 0, lean_box(0));
lean_closure_set(v___x_3601_, 1, v___f_3600_);
v___x_3602_ = lean_box(0);
v___x_3603_ = l_Lean_profileitIOUnsafe___redArg(v___x_3346_, v___x_3017_, v___x_3601_, v___x_3602_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v_a_3604_; lean_object* v___x_3605_; lean_object* v_toEnvExtension_3606_; lean_object* v_asyncMode_3607_; uint8_t v_logWrites_3608_; lean_object* v___x_3609_; 
v_a_3604_ = lean_ctor_get(v___x_3603_, 0);
lean_inc(v_a_3604_);
lean_dec_ref_known(v___x_3603_, 1);
v___x_3605_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_3606_ = lean_ctor_get(v___x_3605_, 0);
v_asyncMode_3607_ = lean_ctor_get(v_toEnvExtension_3606_, 2);
v_logWrites_3608_ = lean_ctor_get_uint8(v_toEnvExtension_3606_, sizeof(void*)*6);
lean_inc(v_name_2995_);
v___x_3609_ = l_Lean_Environment_setMainModule(v_a_3604_, v_name_2995_);
if (v_logWrites_3608_ == 0)
{
lean_object* v___x_3610_; 
lean_inc_ref(v_toEnvExtension_3606_);
v___x_3610_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_3606_, v___x_3609_, v___f_2999_, v_asyncMode_3607_, v___x_3602_, v___x_3013_);
v___y_3522_ = v___x_3602_;
v___y_3523_ = v___x_3610_;
goto v___jp_3521_;
}
else
{
lean_object* v___x_3611_; lean_object* v___x_3612_; 
lean_inc_ref_n(v_toEnvExtension_3606_, 2);
v___x_3611_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite___redArg(v_toEnvExtension_3606_, v___x_3609_);
lean_dec_ref(v___x_3609_);
v___x_3612_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_3606_, v___x_3611_, v___f_2999_, v_asyncMode_3607_, v___x_3602_, v___x_3013_);
v___y_3522_ = v___x_3602_;
v___y_3523_ = v___x_3612_;
goto v___jp_3521_;
}
}
else
{
lean_object* v_a_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3620_; 
lean_dec_ref(v___x_3017_);
lean_del_object(v___x_3010_);
lean_dec(v_fst_3007_);
lean_dec_ref(v___f_2999_);
lean_dec(v_name_2995_);
lean_dec(v_head_2979_);
lean_del_object(v___x_2977_);
lean_dec(v_head_2975_);
lean_del_object(v___x_2973_);
v_a_3613_ = lean_ctor_get(v___x_3603_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3615_ = v___x_3603_;
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_a_3613_);
lean_dec(v___x_3603_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3618_; 
if (v_isShared_3616_ == 0)
{
v___x_3618_ = v___x_3615_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3613_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
}
}
}
else
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3629_; 
lean_dec_ref(v___x_3017_);
lean_del_object(v___x_3010_);
lean_dec(v_fst_3007_);
lean_dec_ref(v___f_2999_);
lean_dec(v_importArts_2997_);
lean_dec(v_name_2995_);
lean_dec(v_head_2979_);
lean_del_object(v___x_2977_);
lean_dec(v_head_2975_);
lean_del_object(v___x_2973_);
v_a_3622_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3624_ = v___x_3345_;
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v___x_3345_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3627_; 
if (v_isShared_3625_ == 0)
{
v___x_3627_ = v___x_3624_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_a_3622_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
}
v___jp_3018_:
{
lean_object* v___x_3040_; lean_object* v_messages_3041_; lean_object* v_env_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3167_; 
v___x_3040_ = lean_st_ref_get(v___y_3034_);
lean_dec(v___y_3034_);
v_messages_3041_ = lean_ctor_get(v___x_3040_, 7);
v_env_3042_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3167_ == 0)
{
lean_object* v_unused_3168_; lean_object* v_unused_3169_; lean_object* v_unused_3170_; lean_object* v_unused_3171_; lean_object* v_unused_3172_; lean_object* v_unused_3173_; lean_object* v_unused_3174_; lean_object* v_unused_3175_; 
v_unused_3168_ = lean_ctor_get(v___x_3040_, 9);
lean_dec(v_unused_3168_);
v_unused_3169_ = lean_ctor_get(v___x_3040_, 8);
lean_dec(v_unused_3169_);
v_unused_3170_ = lean_ctor_get(v___x_3040_, 6);
lean_dec(v_unused_3170_);
v_unused_3171_ = lean_ctor_get(v___x_3040_, 5);
lean_dec(v_unused_3171_);
v_unused_3172_ = lean_ctor_get(v___x_3040_, 4);
lean_dec(v_unused_3172_);
v_unused_3173_ = lean_ctor_get(v___x_3040_, 3);
lean_dec(v_unused_3173_);
v_unused_3174_ = lean_ctor_get(v___x_3040_, 2);
lean_dec(v_unused_3174_);
v_unused_3175_ = lean_ctor_get(v___x_3040_, 1);
lean_dec(v_unused_3175_);
v___x_3044_ = v___x_3040_;
v_isShared_3045_ = v_isSharedCheck_3167_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_messages_3041_);
lean_inc(v_env_3042_);
lean_dec(v___x_3040_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3167_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v_unreported_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v_unreported_3046_ = lean_ctor_get(v_messages_3041_, 1);
v___x_3047_ = lean_box(0);
v___x_3048_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_unreported_3046_, v___x_3047_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3157_; 
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3157_ == 0)
{
lean_object* v_unused_3158_; 
v_unused_3158_ = lean_ctor_get(v___x_3048_, 0);
lean_dec(v_unused_3158_);
v___x_3050_ = v___x_3048_;
v_isShared_3051_ = v_isSharedCheck_3157_;
goto v_resetjp_3049_;
}
else
{
lean_dec(v___x_3048_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3157_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
uint8_t v___x_3052_; 
v___x_3052_ = l_Lean_MessageLog_hasErrors(v_messages_3041_);
lean_dec_ref(v_messages_3041_);
if (v___x_3052_ == 0)
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
lean_del_object(v___x_3050_);
v___x_3053_ = ((lean_object*)(l_main___closed__9));
lean_inc(v_head_2975_);
v___x_3054_ = l_System_FilePath_addExtension(v_head_2975_, v___x_3053_);
lean_inc_ref(v_env_3042_);
v___x_3055_ = l___private_LeanIR_0__mkIRSigData(v_env_3042_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v_a_3056_; lean_object* v___x_3057_; 
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
lean_inc(v_a_3056_);
lean_dec_ref_known(v___x_3055_, 1);
lean_inc_ref(v_env_3042_);
v___x_3057_ = l___private_LeanIR_0__mkIRData(v_env_3042_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v_a_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3063_; 
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
lean_inc(v_a_3058_);
lean_dec_ref_known(v___x_3057_, 1);
v___x_3059_ = l_Lean_Environment_mainModule(v_env_3042_);
v___x_3060_ = ((lean_object*)(l_main___closed__11));
v___x_3061_ = l_Lean_Name_append(v___x_3059_, v___x_3060_);
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 1, v_a_3056_);
lean_ctor_set(v___x_3010_, 0, v___x_3054_);
v___x_3063_ = v___x_3010_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v___x_3054_);
lean_ctor_set(v_reuseFailAlloc_3136_, 1, v_a_3056_);
v___x_3063_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
lean_object* v___x_3065_; 
lean_inc(v_head_2975_);
if (v_isShared_2978_ == 0)
{
lean_ctor_set_tag(v___x_2977_, 0);
lean_ctor_set(v___x_2977_, 1, v_a_3058_);
v___x_3065_ = v___x_2977_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_head_2975_);
lean_ctor_set(v_reuseFailAlloc_3135_, 1, v_a_3058_);
v___x_3065_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3066_ = lean_unsigned_to_nat(2u);
v___x_3067_ = lean_mk_empty_array_with_capacity(v___x_3066_);
v___x_3068_ = lean_array_push(v___x_3067_, v___x_3063_);
v___x_3069_ = lean_array_push(v___x_3068_, v___x_3065_);
v___x_3070_ = l_Lean_saveModuleDataParts(v___x_3061_, v___x_3069_);
lean_dec_ref(v___x_3069_);
lean_dec(v___x_3061_);
if (lean_obj_tag(v___x_3070_) == 0)
{
uint8_t v___x_3071_; lean_object* v___x_3072_; 
lean_dec_ref_known(v___x_3070_, 1);
v___x_3071_ = 1;
v___x_3072_ = lean_io_prim_handle_mk(v_head_2979_, v___x_3071_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v_a_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; uint16_t v___x_3076_; lean_object* v___x_3078_; 
lean_dec(v_head_2979_);
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
lean_inc(v_a_3073_);
lean_dec_ref_known(v___x_3072_, 1);
v___x_3074_ = ((lean_object*)(l_main___closed__12));
v___x_3075_ = l_Lean_Core_getMaxHeartbeats(v___y_3032_);
v___x_3076_ = l_Lean_OptionFlags_ofOptions(v___y_3032_);
lean_inc_ref(v___y_3037_);
lean_inc_ref(v___y_3029_);
lean_inc_ref(v___y_3035_);
lean_inc_ref(v___y_3030_);
lean_inc_ref(v___y_3039_);
lean_inc_ref(v___y_3033_);
lean_inc_ref(v___y_3031_);
lean_inc(v___y_3038_);
lean_inc_ref(v_env_3042_);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 9, v___y_3037_);
lean_ctor_set(v___x_3044_, 8, v___y_3029_);
lean_ctor_set(v___x_3044_, 7, v___y_3035_);
lean_ctor_set(v___x_3044_, 6, v___y_3030_);
lean_ctor_set(v___x_3044_, 5, v___y_3039_);
lean_ctor_set(v___x_3044_, 4, v___y_3033_);
lean_ctor_set(v___x_3044_, 3, v___y_3028_);
lean_ctor_set(v___x_3044_, 2, v___y_3031_);
lean_ctor_set(v___x_3044_, 1, v___y_3038_);
v___x_3078_ = v___x_3044_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_env_3042_);
lean_ctor_set(v_reuseFailAlloc_3104_, 1, v___y_3038_);
lean_ctor_set(v_reuseFailAlloc_3104_, 2, v___y_3031_);
lean_ctor_set(v_reuseFailAlloc_3104_, 3, v___y_3028_);
lean_ctor_set(v_reuseFailAlloc_3104_, 4, v___y_3033_);
lean_ctor_set(v_reuseFailAlloc_3104_, 5, v___y_3039_);
lean_ctor_set(v_reuseFailAlloc_3104_, 6, v___y_3030_);
lean_ctor_set(v_reuseFailAlloc_3104_, 7, v___y_3035_);
lean_ctor_set(v_reuseFailAlloc_3104_, 8, v___y_3029_);
lean_ctor_set(v_reuseFailAlloc_3104_, 9, v___y_3037_);
v___x_3078_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___f_3083_; lean_object* v___x_3084_; 
v___x_3079_ = lean_box(v___x_3076_);
v___x_3080_ = lean_box(v___y_3023_);
v___x_3081_ = lean_box(v___x_3000_);
v___x_3082_ = lean_box(v___x_3052_);
lean_inc_ref(v___y_3027_);
lean_inc_ref(v___y_3020_);
v___f_3083_ = lean_alloc_closure((void*)(l_main___lam__2___boxed), 19, 18);
lean_closure_set(v___f_3083_, 0, v___x_3078_);
lean_closure_set(v___f_3083_, 1, v___y_3020_);
lean_closure_set(v___f_3083_, 2, v___x_3079_);
lean_closure_set(v___f_3083_, 3, v_name_2995_);
lean_closure_set(v___f_3083_, 4, v_a_3073_);
lean_closure_set(v___f_3083_, 5, v___x_3080_);
lean_closure_set(v___f_3083_, 6, v___y_3027_);
lean_closure_set(v___f_3083_, 7, v_head_2975_);
lean_closure_set(v___f_3083_, 8, v___y_3021_);
lean_closure_set(v___f_3083_, 9, v___y_3022_);
lean_closure_set(v___f_3083_, 10, v___y_3024_);
lean_closure_set(v___f_3083_, 11, v___x_3075_);
lean_closure_set(v___f_3083_, 12, v___y_3026_);
lean_closure_set(v___f_3083_, 13, v___y_3025_);
lean_closure_set(v___f_3083_, 14, v___x_3016_);
lean_closure_set(v___f_3083_, 15, v___y_3019_);
lean_closure_set(v___f_3083_, 16, v___x_3081_);
lean_closure_set(v___f_3083_, 17, v___x_3082_);
v___x_3084_ = l_Lean_profileitIOUnsafe___redArg(v___x_3074_, v___x_3017_, v___f_3083_, v___y_3036_);
lean_dec_ref(v___x_3017_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v___x_3085_; uint8_t v___x_3086_; 
lean_dec_ref_known(v___x_3084_, 1);
v___x_3085_ = lean_display_cumulative_profiling_times();
v___x_3086_ = lean_unbox(v_fst_3007_);
lean_dec(v_fst_3007_);
if (v___x_3086_ == 0)
{
lean_dec_ref(v_env_3042_);
goto v___jp_2966_;
}
else
{
lean_object* v___x_3087_; 
v___x_3087_ = l_Lean_Environment_displayStats(v_env_3042_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_dec_ref_known(v___x_3087_, 1);
goto v___jp_2966_;
}
else
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3095_; 
v_a_3088_ = lean_ctor_get(v___x_3087_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3090_ = v___x_3087_;
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3087_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3093_; 
if (v_isShared_3091_ == 0)
{
v___x_3093_ = v___x_3090_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_a_3088_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
}
else
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
lean_dec_ref(v_env_3042_);
lean_dec(v_fst_3007_);
v_a_3096_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_3084_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3084_);
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
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
lean_dec_ref_known(v___x_3072_, 1);
lean_del_object(v___x_3044_);
lean_dec_ref(v_env_3042_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3019_);
lean_dec_ref(v___x_3017_);
lean_dec(v_fst_3007_);
lean_dec(v_name_2995_);
lean_dec(v_head_2975_);
v___x_3105_ = ((lean_object*)(l_main___closed__13));
v___x_3106_ = lean_string_append(v___x_3105_, v_head_2979_);
lean_dec(v_head_2979_);
v___x_3107_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__1));
v___x_3108_ = lean_string_append(v___x_3106_, v___x_3107_);
v___x_3109_ = l_IO_eprintln___at___00main_spec__6(v___x_3108_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3117_; 
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3117_ == 0)
{
lean_object* v_unused_3118_; 
v_unused_3118_ = lean_ctor_get(v___x_3109_, 0);
lean_dec(v_unused_3118_);
v___x_3111_ = v___x_3109_;
v_isShared_3112_ = v_isSharedCheck_3117_;
goto v_resetjp_3110_;
}
else
{
lean_dec(v___x_3109_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3117_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3113_; lean_object* v___x_3115_; 
v___x_3113_ = l_main___boxed__const__1;
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 0, v___x_3113_);
v___x_3115_ = v___x_3111_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3113_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
v_a_3119_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3109_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3109_);
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
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
lean_del_object(v___x_3044_);
lean_dec_ref(v_env_3042_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3019_);
lean_dec_ref(v___x_3017_);
lean_dec(v_fst_3007_);
lean_dec(v_name_2995_);
lean_dec(v_head_2979_);
lean_dec(v_head_2975_);
v_a_3127_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v___x_3070_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3070_);
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
}
else
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
lean_dec(v_a_3056_);
lean_dec_ref(v___x_3054_);
lean_del_object(v___x_3044_);
lean_dec_ref(v_env_3042_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3019_);
lean_dec_ref(v___x_3017_);
lean_del_object(v___x_3010_);
lean_dec(v_fst_3007_);
lean_dec(v_name_2995_);
lean_dec(v_head_2979_);
lean_del_object(v___x_2977_);
lean_dec(v_head_2975_);
v_a_3137_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3057_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3057_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3137_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
else
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
lean_dec_ref(v___x_3054_);
lean_del_object(v___x_3044_);
lean_dec_ref(v_env_3042_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3019_);
lean_dec_ref(v___x_3017_);
lean_del_object(v___x_3010_);
lean_dec(v_fst_3007_);
lean_dec(v_name_2995_);
lean_dec(v_head_2979_);
lean_del_object(v___x_2977_);
lean_dec(v_head_2975_);
v_a_3145_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v___x_3055_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3055_);
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
lean_object* v___x_3153_; lean_object* v___x_3155_; 
lean_del_object(v___x_3044_);
lean_dec_ref(v_env_3042_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3019_);
lean_dec_ref(v___x_3017_);
lean_del_object(v___x_3010_);
lean_dec(v_fst_3007_);
lean_dec(v_name_2995_);
lean_dec(v_head_2979_);
lean_del_object(v___x_2977_);
lean_dec(v_head_2975_);
v___x_3153_ = l_main___boxed__const__1;
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 0, v___x_3153_);
v___x_3155_ = v___x_3050_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v___x_3153_);
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
else
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
lean_del_object(v___x_3044_);
lean_dec_ref(v_env_3042_);
lean_dec_ref(v_messages_3041_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3019_);
lean_dec_ref(v___x_3017_);
lean_del_object(v___x_3010_);
lean_dec(v_fst_3007_);
lean_dec(v_name_2995_);
lean_dec(v_head_2979_);
lean_del_object(v___x_2977_);
lean_dec(v_head_2975_);
v_a_3159_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3161_ = v___x_3048_;
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3048_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3164_; 
if (v_isShared_3162_ == 0)
{
v___x_3164_ = v___x_3161_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_a_3159_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
}
}
v___jp_3176_:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; size_t v_sz_3213_; size_t v___x_3214_; lean_object* v___x_3215_; 
lean_inc_ref(v___y_3208_);
v___x_3210_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3210_, 0, v___y_3209_);
lean_ctor_set(v___x_3210_, 1, v_nextMacroScope_3191_);
lean_ctor_set(v___x_3210_, 2, v_ngen_3192_);
lean_ctor_set(v___x_3210_, 3, v_auxDeclNGen_3193_);
lean_ctor_set(v___x_3210_, 4, v_traceState_3194_);
lean_ctor_set(v___x_3210_, 5, v___y_3208_);
lean_ctor_set(v___x_3210_, 6, v_recordedDeps_3195_);
lean_ctor_set(v___x_3210_, 7, v_messages_3196_);
lean_ctor_set(v___x_3210_, 8, v_infoState_3197_);
lean_ctor_set(v___x_3210_, 9, v_snapshotTasks_3198_);
v___x_3211_ = lean_st_ref_put(v___y_3189_, v___x_3210_);
v___x_3212_ = lean_box(0);
v_sz_3213_ = lean_array_size(v___y_3187_);
v___x_3214_ = ((size_t)0ULL);
v___x_3215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(v___y_3187_, v_sz_3213_, v___x_3214_, v___x_3212_, v___y_3202_, v___y_3189_);
lean_dec_ref(v___y_3187_);
if (lean_obj_tag(v___x_3215_) == 0)
{
lean_dec_ref_known(v___x_3215_, 1);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3189_);
v___y_3019_ = v___y_3177_;
v___y_3020_ = v___y_3178_;
v___y_3021_ = v___y_3179_;
v___y_3022_ = v___y_3181_;
v___y_3023_ = v___y_3180_;
v___y_3024_ = v___y_3182_;
v___y_3025_ = v___y_3185_;
v___y_3026_ = v___y_3184_;
v___y_3027_ = v___y_3183_;
v___y_3028_ = v___y_3186_;
v___y_3029_ = v___y_3201_;
v___y_3030_ = v___y_3188_;
v___y_3031_ = v___y_3203_;
v___y_3032_ = v___y_3204_;
v___y_3033_ = v___y_3190_;
v___y_3034_ = v___y_3205_;
v___y_3035_ = v___y_3206_;
v___y_3036_ = v___y_3199_;
v___y_3037_ = v___y_3207_;
v___y_3038_ = v___y_3200_;
v___y_3039_ = v___y_3208_;
goto v___jp_3018_;
}
else
{
lean_object* v_a_3216_; uint8_t v___x_3217_; 
v_a_3216_ = lean_ctor_get(v___x_3215_, 0);
lean_inc(v_a_3216_);
lean_dec_ref_known(v___x_3215_, 1);
v___x_3217_ = l_Lean_Exception_isInterrupt(v_a_3216_);
if (v___x_3217_ == 0)
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3218_ = l_Lean_Exception_toMessageData(v_a_3216_);
v___x_3219_ = l_Lean_logError___at___00main_spec__13(v___x_3218_, v___y_3202_, v___y_3189_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3202_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_dec_ref_known(v___x_3219_, 1);
v___y_3019_ = v___y_3177_;
v___y_3020_ = v___y_3178_;
v___y_3021_ = v___y_3179_;
v___y_3022_ = v___y_3181_;
v___y_3023_ = v___y_3180_;
v___y_3024_ = v___y_3182_;
v___y_3025_ = v___y_3185_;
v___y_3026_ = v___y_3184_;
v___y_3027_ = v___y_3183_;
v___y_3028_ = v___y_3186_;
v___y_3029_ = v___y_3201_;
v___y_3030_ = v___y_3188_;
v___y_3031_ = v___y_3203_;
v___y_3032_ = v___y_3204_;
v___y_3033_ = v___y_3190_;
v___y_3034_ = v___y_3205_;
v___y_3035_ = v___y_3206_;
v___y_3036_ = v___y_3199_;
v___y_3037_ = v___y_3207_;
v___y_3038_ = v___y_3200_;
v___y_3039_ = v___y_3208_;
goto v___jp_3018_;
}
else
{
lean_object* v___x_3220_; lean_object* v___x_3221_; 
lean_dec_ref_known(v___x_3219_, 1);
lean_dec(v___y_3205_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3177_);
lean_dec_ref(v___x_3017_);
lean_del_object(v___x_3010_);
lean_dec(v_fst_3007_);
lean_dec(v_name_2995_);
lean_dec(v_head_2979_);
lean_del_object(v___x_2977_);
lean_dec(v_head_2975_);
v___x_3220_ = lean_obj_once(&l_main___closed__17, &l_main___closed__17_once, _init_l_main___closed__17);
v___x_3221_ = l_panic___at___00main_spec__5(v___x_3220_);
return v___x_3221_;
}
}
else
{
lean_dec(v_a_3216_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3189_);
v___y_3019_ = v___y_3177_;
v___y_3020_ = v___y_3178_;
v___y_3021_ = v___y_3179_;
v___y_3022_ = v___y_3181_;
v___y_3023_ = v___y_3180_;
v___y_3024_ = v___y_3182_;
v___y_3025_ = v___y_3185_;
v___y_3026_ = v___y_3184_;
v___y_3027_ = v___y_3183_;
v___y_3028_ = v___y_3186_;
v___y_3029_ = v___y_3201_;
v___y_3030_ = v___y_3188_;
v___y_3031_ = v___y_3203_;
v___y_3032_ = v___y_3204_;
v___y_3033_ = v___y_3190_;
v___y_3034_ = v___y_3205_;
v___y_3035_ = v___y_3206_;
v___y_3036_ = v___y_3199_;
v___y_3037_ = v___y_3207_;
v___y_3038_ = v___y_3200_;
v___y_3039_ = v___y_3208_;
goto v___jp_3018_;
}
}
}
v___jp_3222_:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v_env_3267_; lean_object* v_nextMacroScope_3268_; lean_object* v_ngen_3269_; lean_object* v_auxDeclNGen_3270_; lean_object* v_traceState_3271_; lean_object* v_recordedDeps_3272_; lean_object* v_messages_3273_; lean_object* v_infoState_3274_; lean_object* v_snapshotTasks_3275_; lean_object* v___x_3276_; uint8_t v___x_3277_; 
v___x_3262_ = l_Lean_maxRecDepth;
v___x_3263_ = l_Lean_Option_get___at___00main_spec__8(v___x_3017_, v___x_3262_);
lean_inc_ref(v___x_3017_);
v___x_3264_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3264_, 0, v_fileName_3247_);
lean_ctor_set(v___x_3264_, 1, v_fileMap_3248_);
lean_ctor_set(v___x_3264_, 2, v___x_3017_);
lean_ctor_set(v___x_3264_, 3, v___x_3263_);
lean_ctor_set(v___x_3264_, 4, v_currNamespace_3249_);
lean_ctor_set(v___x_3264_, 5, v_openDecls_3250_);
lean_ctor_set(v___x_3264_, 6, v_initHeartbeats_3251_);
lean_ctor_set(v___x_3264_, 7, v_maxHeartbeats_3252_);
lean_ctor_set(v___x_3264_, 8, v_quotContext_3253_);
lean_ctor_set(v___x_3264_, 9, v_currMacroScope_3254_);
lean_ctor_set(v___x_3264_, 10, v_cancelTk_x3f_3255_);
lean_ctor_set(v___x_3264_, 11, v_inheritedTraceOptions_3256_);
v___x_3265_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3265_, 0, v___x_3264_);
lean_ctor_set(v___x_3265_, 1, v_currRecDepth_3257_);
lean_ctor_set(v___x_3265_, 2, v_ref_3258_);
lean_ctor_set_uint16(v___x_3265_, sizeof(void*)*3, v___y_3233_);
lean_ctor_set_uint8(v___x_3265_, sizeof(void*)*3 + 2, v_suppressElabErrors_3259_);
lean_ctor_set_uint8(v___x_3265_, sizeof(void*)*3 + 3, v_isRecordingDeps_3260_);
v___x_3266_ = lean_st_ref_take(v___y_3261_);
v_env_3267_ = lean_ctor_get(v___x_3266_, 0);
lean_inc_ref(v_env_3267_);
v_nextMacroScope_3268_ = lean_ctor_get(v___x_3266_, 1);
lean_inc(v_nextMacroScope_3268_);
v_ngen_3269_ = lean_ctor_get(v___x_3266_, 2);
lean_inc_ref(v_ngen_3269_);
v_auxDeclNGen_3270_ = lean_ctor_get(v___x_3266_, 3);
lean_inc_ref(v_auxDeclNGen_3270_);
v_traceState_3271_ = lean_ctor_get(v___x_3266_, 4);
lean_inc_ref(v_traceState_3271_);
v_recordedDeps_3272_ = lean_ctor_get(v___x_3266_, 6);
lean_inc_ref(v_recordedDeps_3272_);
v_messages_3273_ = lean_ctor_get(v___x_3266_, 7);
lean_inc_ref(v_messages_3273_);
v_infoState_3274_ = lean_ctor_get(v___x_3266_, 8);
lean_inc_ref(v_infoState_3274_);
v_snapshotTasks_3275_ = lean_ctor_get(v___x_3266_, 9);
lean_inc_ref(v_snapshotTasks_3275_);
lean_dec(v___x_3266_);
v___x_3276_ = lean_array_get_size(v___y_3234_);
v___x_3277_ = lean_nat_dec_lt(v___x_3016_, v___x_3276_);
if (v___x_3277_ == 0)
{
lean_object* v___x_3278_; 
lean_inc_ref(v___y_3243_);
v___x_3278_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3243_, v_env_3267_, v___x_2991_);
v___y_3177_ = v___y_3223_;
v___y_3178_ = v___y_3224_;
v___y_3179_ = v___y_3225_;
v___y_3180_ = v___y_3227_;
v___y_3181_ = v___y_3226_;
v___y_3182_ = v___y_3228_;
v___y_3183_ = v___y_3231_;
v___y_3184_ = v___y_3230_;
v___y_3185_ = v___y_3229_;
v___y_3186_ = v___y_3232_;
v___y_3187_ = v___y_3234_;
v___y_3188_ = v___y_3235_;
v___y_3189_ = v___y_3261_;
v___y_3190_ = v___y_3236_;
v_nextMacroScope_3191_ = v_nextMacroScope_3268_;
v_ngen_3192_ = v_ngen_3269_;
v_auxDeclNGen_3193_ = v_auxDeclNGen_3270_;
v_traceState_3194_ = v_traceState_3271_;
v_recordedDeps_3195_ = v_recordedDeps_3272_;
v_messages_3196_ = v_messages_3273_;
v_infoState_3197_ = v_infoState_3274_;
v_snapshotTasks_3198_ = v_snapshotTasks_3275_;
v___y_3199_ = v___y_3237_;
v___y_3200_ = v___y_3238_;
v___y_3201_ = v___y_3239_;
v___y_3202_ = v___x_3265_;
v___y_3203_ = v___y_3240_;
v___y_3204_ = v___y_3241_;
v___y_3205_ = v___y_3242_;
v___y_3206_ = v___y_3244_;
v___y_3207_ = v___y_3245_;
v___y_3208_ = v___y_3246_;
v___y_3209_ = v___x_3278_;
goto v___jp_3176_;
}
else
{
size_t v___x_3279_; size_t v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3279_ = ((size_t)0ULL);
v___x_3280_ = lean_usize_of_nat(v___x_3276_);
v___x_3281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v___y_3234_, v___x_3279_, v___x_3280_, v___x_2991_);
lean_inc_ref(v___y_3243_);
v___x_3282_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3243_, v_env_3267_, v___x_3281_);
v___y_3177_ = v___y_3223_;
v___y_3178_ = v___y_3224_;
v___y_3179_ = v___y_3225_;
v___y_3180_ = v___y_3227_;
v___y_3181_ = v___y_3226_;
v___y_3182_ = v___y_3228_;
v___y_3183_ = v___y_3231_;
v___y_3184_ = v___y_3230_;
v___y_3185_ = v___y_3229_;
v___y_3186_ = v___y_3232_;
v___y_3187_ = v___y_3234_;
v___y_3188_ = v___y_3235_;
v___y_3189_ = v___y_3261_;
v___y_3190_ = v___y_3236_;
v_nextMacroScope_3191_ = v_nextMacroScope_3268_;
v_ngen_3192_ = v_ngen_3269_;
v_auxDeclNGen_3193_ = v_auxDeclNGen_3270_;
v_traceState_3194_ = v_traceState_3271_;
v_recordedDeps_3195_ = v_recordedDeps_3272_;
v_messages_3196_ = v_messages_3273_;
v_infoState_3197_ = v_infoState_3274_;
v_snapshotTasks_3198_ = v_snapshotTasks_3275_;
v___y_3199_ = v___y_3237_;
v___y_3200_ = v___y_3238_;
v___y_3201_ = v___y_3239_;
v___y_3202_ = v___x_3265_;
v___y_3203_ = v___y_3240_;
v___y_3204_ = v___y_3241_;
v___y_3205_ = v___y_3242_;
v___y_3206_ = v___y_3244_;
v___y_3207_ = v___y_3245_;
v___y_3208_ = v___y_3246_;
v___y_3209_ = v___x_3282_;
goto v___jp_3176_;
}
}
v___jp_3283_:
{
lean_object* v___x_3310_; lean_object* v_env_3311_; lean_object* v_nextMacroScope_3312_; lean_object* v_ngen_3313_; lean_object* v_auxDeclNGen_3314_; lean_object* v_traceState_3315_; lean_object* v_recordedDeps_3316_; lean_object* v_messages_3317_; lean_object* v_infoState_3318_; lean_object* v_snapshotTasks_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3343_; 
v___x_3310_ = lean_st_ref_take(v___y_3305_);
v_env_3311_ = lean_ctor_get(v___x_3310_, 0);
v_nextMacroScope_3312_ = lean_ctor_get(v___x_3310_, 1);
v_ngen_3313_ = lean_ctor_get(v___x_3310_, 2);
v_auxDeclNGen_3314_ = lean_ctor_get(v___x_3310_, 3);
v_traceState_3315_ = lean_ctor_get(v___x_3310_, 4);
v_recordedDeps_3316_ = lean_ctor_get(v___x_3310_, 6);
v_messages_3317_ = lean_ctor_get(v___x_3310_, 7);
v_infoState_3318_ = lean_ctor_get(v___x_3310_, 8);
v_snapshotTasks_3319_ = lean_ctor_get(v___x_3310_, 9);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3343_ == 0)
{
lean_object* v_unused_3344_; 
v_unused_3344_ = lean_ctor_get(v___x_3310_, 5);
lean_dec(v_unused_3344_);
v___x_3321_ = v___x_3310_;
v_isShared_3322_ = v_isSharedCheck_3343_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_snapshotTasks_3319_);
lean_inc(v_infoState_3318_);
lean_inc(v_messages_3317_);
lean_inc(v_recordedDeps_3316_);
lean_inc(v_traceState_3315_);
lean_inc(v_auxDeclNGen_3314_);
lean_inc(v_ngen_3313_);
lean_inc(v_nextMacroScope_3312_);
lean_inc(v_env_3311_);
lean_dec(v___x_3310_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3343_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3323_; lean_object* v___x_3325_; 
v___x_3323_ = l_Lean_Kernel_enableDiag(v_env_3311_, v___y_3294_);
lean_inc_ref(v___y_3309_);
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 5, v___y_3309_);
lean_ctor_set(v___x_3321_, 0, v___x_3323_);
v___x_3325_ = v___x_3321_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v___x_3323_);
lean_ctor_set(v_reuseFailAlloc_3342_, 1, v_nextMacroScope_3312_);
lean_ctor_set(v_reuseFailAlloc_3342_, 2, v_ngen_3313_);
lean_ctor_set(v_reuseFailAlloc_3342_, 3, v_auxDeclNGen_3314_);
lean_ctor_set(v_reuseFailAlloc_3342_, 4, v_traceState_3315_);
lean_ctor_set(v_reuseFailAlloc_3342_, 5, v___y_3309_);
lean_ctor_set(v_reuseFailAlloc_3342_, 6, v_recordedDeps_3316_);
lean_ctor_set(v_reuseFailAlloc_3342_, 7, v_messages_3317_);
lean_ctor_set(v_reuseFailAlloc_3342_, 8, v_infoState_3318_);
lean_ctor_set(v_reuseFailAlloc_3342_, 9, v_snapshotTasks_3319_);
v___x_3325_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
lean_object* v___x_3326_; lean_object* v_toCold_3327_; lean_object* v_currRecDepth_3328_; lean_object* v_ref_3329_; uint8_t v_suppressElabErrors_3330_; uint8_t v_isRecordingDeps_3331_; lean_object* v_fileName_3332_; lean_object* v_fileMap_3333_; lean_object* v_currNamespace_3334_; lean_object* v_openDecls_3335_; lean_object* v_initHeartbeats_3336_; lean_object* v_maxHeartbeats_3337_; lean_object* v_quotContext_3338_; lean_object* v_currMacroScope_3339_; lean_object* v_cancelTk_x3f_3340_; lean_object* v_inheritedTraceOptions_3341_; 
v___x_3326_ = lean_st_ref_put(v___y_3305_, v___x_3325_);
v_toCold_3327_ = lean_ctor_get(v___y_3298_, 0);
lean_inc_ref(v_toCold_3327_);
v_currRecDepth_3328_ = lean_ctor_get(v___y_3298_, 1);
lean_inc(v_currRecDepth_3328_);
v_ref_3329_ = lean_ctor_get(v___y_3298_, 2);
lean_inc(v_ref_3329_);
v_suppressElabErrors_3330_ = lean_ctor_get_uint8(v___y_3298_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3331_ = lean_ctor_get_uint8(v___y_3298_, sizeof(void*)*3 + 3);
lean_dec_ref(v___y_3298_);
v_fileName_3332_ = lean_ctor_get(v_toCold_3327_, 0);
lean_inc_ref(v_fileName_3332_);
v_fileMap_3333_ = lean_ctor_get(v_toCold_3327_, 1);
lean_inc_ref(v_fileMap_3333_);
v_currNamespace_3334_ = lean_ctor_get(v_toCold_3327_, 4);
lean_inc(v_currNamespace_3334_);
v_openDecls_3335_ = lean_ctor_get(v_toCold_3327_, 5);
lean_inc(v_openDecls_3335_);
v_initHeartbeats_3336_ = lean_ctor_get(v_toCold_3327_, 6);
lean_inc(v_initHeartbeats_3336_);
v_maxHeartbeats_3337_ = lean_ctor_get(v_toCold_3327_, 7);
lean_inc(v_maxHeartbeats_3337_);
v_quotContext_3338_ = lean_ctor_get(v_toCold_3327_, 8);
lean_inc(v_quotContext_3338_);
v_currMacroScope_3339_ = lean_ctor_get(v_toCold_3327_, 9);
lean_inc(v_currMacroScope_3339_);
v_cancelTk_x3f_3340_ = lean_ctor_get(v_toCold_3327_, 10);
lean_inc(v_cancelTk_x3f_3340_);
v_inheritedTraceOptions_3341_ = lean_ctor_get(v_toCold_3327_, 11);
lean_inc_ref(v_inheritedTraceOptions_3341_);
lean_dec_ref(v_toCold_3327_);
lean_inc(v___y_3305_);
v___y_3223_ = v___y_3284_;
v___y_3224_ = v___y_3285_;
v___y_3225_ = v___y_3286_;
v___y_3226_ = v___y_3288_;
v___y_3227_ = v___y_3287_;
v___y_3228_ = v___y_3289_;
v___y_3229_ = v___y_3292_;
v___y_3230_ = v___y_3291_;
v___y_3231_ = v___y_3290_;
v___y_3232_ = v___y_3293_;
v___y_3233_ = v___y_3295_;
v___y_3234_ = v___y_3296_;
v___y_3235_ = v___y_3297_;
v___y_3236_ = v___y_3299_;
v___y_3237_ = v___y_3300_;
v___y_3238_ = v___y_3301_;
v___y_3239_ = v___y_3302_;
v___y_3240_ = v___y_3303_;
v___y_3241_ = v___y_3304_;
v___y_3242_ = v___y_3305_;
v___y_3243_ = v___y_3307_;
v___y_3244_ = v___y_3306_;
v___y_3245_ = v___y_3308_;
v___y_3246_ = v___y_3309_;
v_fileName_3247_ = v_fileName_3332_;
v_fileMap_3248_ = v_fileMap_3333_;
v_currNamespace_3249_ = v_currNamespace_3334_;
v_openDecls_3250_ = v_openDecls_3335_;
v_initHeartbeats_3251_ = v_initHeartbeats_3336_;
v_maxHeartbeats_3252_ = v_maxHeartbeats_3337_;
v_quotContext_3253_ = v_quotContext_3338_;
v_currMacroScope_3254_ = v_currMacroScope_3339_;
v_cancelTk_x3f_3255_ = v_cancelTk_x3f_3340_;
v_inheritedTraceOptions_3256_ = v_inheritedTraceOptions_3341_;
v_currRecDepth_3257_ = v_currRecDepth_3328_;
v_ref_3258_ = v_ref_3329_;
v_suppressElabErrors_3259_ = v_suppressElabErrors_3330_;
v_isRecordingDeps_3260_ = v_isRecordingDeps_3331_;
v___y_3261_ = v___y_3305_;
goto v___jp_3222_;
}
}
}
}
}
else
{
lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3638_; 
lean_dec_ref(v___f_2999_);
lean_dec(v_importArts_2997_);
lean_dec(v_name_2995_);
lean_dec(v_head_2979_);
lean_del_object(v___x_2977_);
lean_dec(v_head_2975_);
lean_del_object(v___x_2973_);
v_a_3631_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3633_ = v___x_3005_;
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3005_);
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
}
else
{
lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3647_; 
lean_del_object(v___x_2982_);
lean_dec(v_tail_2980_);
lean_dec(v_head_2979_);
lean_del_object(v___x_2977_);
lean_dec(v_head_2975_);
lean_del_object(v___x_2973_);
v_a_3640_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3642_ = v___x_2993_;
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_2993_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3645_; 
if (v_isShared_3643_ == 0)
{
v___x_3645_ = v___x_3642_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_a_3640_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
}
}
}
}
}
else
{
lean_dec(v_tail_2970_);
lean_dec_ref_known(v_tail_2969_, 2);
lean_dec_ref_known(v_args_2944_, 2);
goto v___jp_2946_;
}
}
else
{
lean_dec(v_tail_2969_);
lean_dec_ref_known(v_args_2944_, 2);
goto v___jp_2946_;
}
}
else
{
lean_dec(v_args_2944_);
goto v___jp_2946_;
}
v___jp_2946_:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2947_ = ((lean_object*)(l_main___closed__0));
v___x_2948_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_2947_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2956_; 
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2956_ == 0)
{
lean_object* v_unused_2957_; 
v_unused_2957_ = lean_ctor_get(v___x_2948_, 0);
lean_dec(v_unused_2957_);
v___x_2950_ = v___x_2948_;
v_isShared_2951_ = v_isSharedCheck_2956_;
goto v_resetjp_2949_;
}
else
{
lean_dec(v___x_2948_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2956_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2952_; lean_object* v___x_2954_; 
v___x_2952_ = l_main___boxed__const__1;
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 0, v___x_2952_);
v___x_2954_ = v___x_2950_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v___x_2952_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
else
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2965_; 
v_a_2958_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2960_ = v___x_2948_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2948_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2963_; 
if (v_isShared_2961_ == 0)
{
v___x_2963_ = v___x_2960_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2958_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
}
v___jp_2966_:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2967_ = l_main___boxed__const__2;
v___x_2968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2967_);
return v___x_2968_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_3653_, lean_object* v_a_3654_){
_start:
{
lean_object* v_res_3655_; 
v_res_3655_ = _lean_main(v_args_3653_);
return v_res_3655_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object* v_as_3656_, lean_object* v_as_x27_3657_, lean_object* v_b_3658_, lean_object* v_a_3659_){
_start:
{
lean_object* v___x_3661_; 
v___x_3661_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_3657_, v_b_3658_);
return v___x_3661_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object* v_as_3662_, lean_object* v_as_x27_3663_, lean_object* v_b_3664_, lean_object* v_a_3665_, lean_object* v___y_3666_){
_start:
{
lean_object* v_res_3667_; 
v_res_3667_ = l_List_forIn_x27_loop___at___00main_spec__1(v_as_3662_, v_as_x27_3663_, v_b_3664_, v_a_3665_);
lean_dec(v_as_x27_3663_);
lean_dec(v_as_3662_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16(lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
lean_object* v___x_3671_; 
v___x_3671_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v___y_3669_);
return v___x_3671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___boxed(lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_){
_start:
{
lean_object* v_res_3675_; 
v_res_3675_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16(v___y_3672_, v___y_3673_);
lean_dec(v___y_3673_);
lean_dec_ref(v___y_3672_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17(lean_object* v_00_u03b2_3676_, lean_object* v_m_3677_, lean_object* v_a_3678_, lean_object* v_fallback_3679_){
_start:
{
lean_object* v___x_3680_; 
v___x_3680_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_m_3677_, v_a_3678_, v_fallback_3679_);
return v___x_3680_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___boxed(lean_object* v_00_u03b2_3681_, lean_object* v_m_3682_, lean_object* v_a_3683_, lean_object* v_fallback_3684_){
_start:
{
lean_object* v_res_3685_; 
v_res_3685_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17(v_00_u03b2_3681_, v_m_3682_, v_a_3683_, v_fallback_3684_);
lean_dec(v_fallback_3684_);
lean_dec_ref(v_a_3683_);
lean_dec_ref(v_m_3682_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18(lean_object* v_00_u03b2_3686_, lean_object* v_m_3687_, lean_object* v_a_3688_, lean_object* v_b_3689_){
_start:
{
lean_object* v___x_3690_; 
v___x_3690_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___redArg(v_m_3687_, v_a_3688_, v_b_3689_);
return v___x_3690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21(lean_object* v_n_3691_, lean_object* v_as_3692_, lean_object* v_lo_3693_, lean_object* v_hi_3694_, lean_object* v_w_3695_, lean_object* v_hlo_3696_, lean_object* v_hhi_3697_){
_start:
{
lean_object* v___x_3698_; 
v___x_3698_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___redArg(v_n_3691_, v_as_3692_, v_lo_3693_, v_hi_3694_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___boxed(lean_object* v_n_3699_, lean_object* v_as_3700_, lean_object* v_lo_3701_, lean_object* v_hi_3702_, lean_object* v_w_3703_, lean_object* v_hlo_3704_, lean_object* v_hhi_3705_){
_start:
{
lean_object* v_res_3706_; 
v_res_3706_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21(v_n_3699_, v_as_3700_, v_lo_3701_, v_hi_3702_, v_w_3703_, v_hlo_3704_, v_hhi_3705_);
lean_dec(v_hi_3702_);
lean_dec(v_n_3699_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21(lean_object* v_00_u03b2_3707_, lean_object* v_a_3708_, lean_object* v_fallback_3709_, lean_object* v_x_3710_){
_start:
{
lean_object* v___x_3711_; 
v___x_3711_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___redArg(v_a_3708_, v_fallback_3709_, v_x_3710_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3712_, lean_object* v_a_3713_, lean_object* v_fallback_3714_, lean_object* v_x_3715_){
_start:
{
lean_object* v_res_3716_; 
v_res_3716_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__21(v_00_u03b2_3712_, v_a_3713_, v_fallback_3714_, v_x_3715_);
lean_dec(v_x_3715_);
lean_dec(v_fallback_3714_);
lean_dec_ref(v_a_3713_);
return v_res_3716_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23(lean_object* v_00_u03b2_3717_, lean_object* v_a_3718_, lean_object* v_x_3719_){
_start:
{
uint8_t v___x_3720_; 
v___x_3720_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___redArg(v_a_3718_, v_x_3719_);
return v___x_3720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23___boxed(lean_object* v_00_u03b2_3721_, lean_object* v_a_3722_, lean_object* v_x_3723_){
_start:
{
uint8_t v_res_3724_; lean_object* v_r_3725_; 
v_res_3724_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__23(v_00_u03b2_3721_, v_a_3722_, v_x_3723_);
lean_dec(v_x_3723_);
lean_dec_ref(v_a_3722_);
v_r_3725_ = lean_box(v_res_3724_);
return v_r_3725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24(lean_object* v_00_u03b2_3726_, lean_object* v_data_3727_){
_start:
{
lean_object* v___x_3728_; 
v___x_3728_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24___redArg(v_data_3727_);
return v___x_3728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25(lean_object* v_00_u03b2_3729_, lean_object* v_a_3730_, lean_object* v_b_3731_, lean_object* v_x_3732_){
_start:
{
lean_object* v___x_3733_; 
v___x_3733_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__25___redArg(v_a_3730_, v_b_3731_, v_x_3732_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31(lean_object* v_n_3734_, lean_object* v_lo_3735_, lean_object* v_hi_3736_, lean_object* v_hhi_3737_, lean_object* v_pivot_3738_, lean_object* v_as_3739_, lean_object* v_i_3740_, lean_object* v_k_3741_, lean_object* v_ilo_3742_, lean_object* v_ik_3743_, lean_object* v_w_3744_){
_start:
{
lean_object* v___x_3745_; 
v___x_3745_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___redArg(v_hi_3736_, v_pivot_3738_, v_as_3739_, v_i_3740_, v_k_3741_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31___boxed(lean_object* v_n_3746_, lean_object* v_lo_3747_, lean_object* v_hi_3748_, lean_object* v_hhi_3749_, lean_object* v_pivot_3750_, lean_object* v_as_3751_, lean_object* v_i_3752_, lean_object* v_k_3753_, lean_object* v_ilo_3754_, lean_object* v_ik_3755_, lean_object* v_w_3756_){
_start:
{
lean_object* v_res_3757_; 
v_res_3757_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21_spec__31(v_n_3746_, v_lo_3747_, v_hi_3748_, v_hhi_3749_, v_pivot_3750_, v_as_3751_, v_i_3752_, v_k_3753_, v_ilo_3754_, v_ik_3755_, v_w_3756_);
lean_dec_ref(v_pivot_3750_);
lean_dec(v_hi_3748_);
lean_dec(v_lo_3747_);
lean_dec(v_n_3746_);
return v_res_3757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40(lean_object* v_as_3758_, size_t v_sz_3759_, size_t v_i_3760_, lean_object* v_b_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_){
_start:
{
lean_object* v___x_3765_; 
v___x_3765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___redArg(v_as_3758_, v_sz_3759_, v_i_3760_, v_b_3761_, v___y_3762_);
return v___x_3765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40___boxed(lean_object* v_as_3766_, lean_object* v_sz_3767_, lean_object* v_i_3768_, lean_object* v_b_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_){
_start:
{
size_t v_sz_boxed_3773_; size_t v_i_boxed_3774_; lean_object* v_res_3775_; 
v_sz_boxed_3773_ = lean_unbox_usize(v_sz_3767_);
lean_dec(v_sz_3767_);
v_i_boxed_3774_ = lean_unbox_usize(v_i_3768_);
lean_dec(v_i_3768_);
v_res_3775_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__27_spec__40(v_as_3766_, v_sz_boxed_3773_, v_i_boxed_3774_, v_b_3769_, v___y_3770_, v___y_3771_);
lean_dec(v___y_3771_);
lean_dec_ref(v___y_3770_);
lean_dec_ref(v_as_3766_);
return v_res_3775_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35(lean_object* v_00_u03b2_3776_, lean_object* v_i_3777_, lean_object* v_source_3778_, lean_object* v_target_3779_){
_start:
{
lean_object* v___x_3780_; 
v___x_3780_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35___redArg(v_i_3777_, v_source_3778_, v_target_3779_);
return v___x_3780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42(uint8_t v___x_3781_, lean_object* v_as_3782_, size_t v_sz_3783_, size_t v_i_3784_, lean_object* v_b_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_){
_start:
{
lean_object* v___x_3789_; 
v___x_3789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___redArg(v___x_3781_, v_as_3782_, v_sz_3783_, v_i_3784_, v_b_3785_, v___y_3786_);
return v___x_3789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42___boxed(lean_object* v___x_3790_, lean_object* v_as_3791_, lean_object* v_sz_3792_, lean_object* v_i_3793_, lean_object* v_b_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_){
_start:
{
uint8_t v___x_42265__boxed_3798_; size_t v_sz_boxed_3799_; size_t v_i_boxed_3800_; lean_object* v_res_3801_; 
v___x_42265__boxed_3798_ = lean_unbox(v___x_3790_);
v_sz_boxed_3799_ = lean_unbox_usize(v_sz_3792_);
lean_dec(v_sz_3792_);
v_i_boxed_3800_ = lean_unbox_usize(v_i_3793_);
lean_dec(v_i_3793_);
v_res_3801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__28_spec__42(v___x_42265__boxed_3798_, v_as_3791_, v_sz_boxed_3799_, v_i_boxed_3800_, v_b_3794_, v___y_3795_, v___y_3796_);
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
lean_dec_ref(v_as_3791_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51(lean_object* v_as_3802_, size_t v_sz_3803_, size_t v_i_3804_, lean_object* v_b_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_){
_start:
{
lean_object* v___x_3809_; 
v___x_3809_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___redArg(v_as_3802_, v_sz_3803_, v_i_3804_, v_b_3805_, v___y_3806_);
return v___x_3809_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51___boxed(lean_object* v_as_3810_, lean_object* v_sz_3811_, lean_object* v_i_3812_, lean_object* v_b_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_){
_start:
{
size_t v_sz_boxed_3817_; size_t v_i_boxed_3818_; lean_object* v_res_3819_; 
v_sz_boxed_3817_ = lean_unbox_usize(v_sz_3811_);
lean_dec(v_sz_3811_);
v_i_boxed_3818_ = lean_unbox_usize(v_i_3812_);
lean_dec(v_i_3812_);
v_res_3819_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__38_spec__51(v_as_3810_, v_sz_boxed_3817_, v_i_boxed_3818_, v_b_3813_, v___y_3814_, v___y_3815_);
lean_dec(v___y_3815_);
lean_dec_ref(v___y_3814_);
lean_dec_ref(v_as_3810_);
return v_res_3819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44(lean_object* v_00_u03b2_3820_, lean_object* v_x_3821_, lean_object* v_x_3822_){
_start:
{
lean_object* v___x_3823_; 
v___x_3823_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__24_spec__35_spec__44___redArg(v_x_3821_, v_x_3822_);
return v___x_3823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49(uint8_t v___x_3824_, lean_object* v_as_3825_, size_t v_sz_3826_, size_t v_i_3827_, lean_object* v_b_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
lean_object* v___x_3832_; 
v___x_3832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___redArg(v___x_3824_, v_as_3825_, v_sz_3826_, v_i_3827_, v_b_3828_, v___y_3829_);
return v___x_3832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49___boxed(lean_object* v___x_3833_, lean_object* v_as_3834_, lean_object* v_sz_3835_, lean_object* v_i_3836_, lean_object* v_b_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_){
_start:
{
uint8_t v___x_42296__boxed_3841_; size_t v_sz_boxed_3842_; size_t v_i_boxed_3843_; lean_object* v_res_3844_; 
v___x_42296__boxed_3841_ = lean_unbox(v___x_3833_);
v_sz_boxed_3842_ = lean_unbox_usize(v_sz_3835_);
lean_dec(v_sz_3835_);
v_i_boxed_3843_ = lean_unbox_usize(v_i_3836_);
lean_dec(v_i_3836_);
v_res_3844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19_spec__27_spec__40_spec__49(v___x_42296__boxed_3841_, v_as_3834_, v_sz_boxed_3842_, v_i_boxed_3843_, v_b_3837_, v___y_3838_, v___y_3839_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec_ref(v_as_3834_);
return v_res_3844_;
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
