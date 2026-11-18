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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instOrdOLeanLevel_ord(uint8_t, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Compiler_LCNF_resumeCompilation(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_output;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_serve;
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_lintComputable_spec__2_spec__3_spec__4_spec__5(lean_object*, lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
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
lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_lintComputable_spec__2_spec__3_spec__4(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__26___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__26___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__26___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__26(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__29(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20_spec__30___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20_spec__30___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16_spec__20___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__22___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__22___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__24___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23_spec__34_spec__43___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23_spec__34___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__27_spec__41___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__27_spec__41___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__27_spec__41___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__27_spec__41___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__27_spec__41___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__27(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__39_spec__48___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__39_spec__48___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__39(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__39___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__38(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___closed__0;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0;
static lean_once_cell_t l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1;
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__37_spec__50___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__37_spec__50___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__37(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__36(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__39___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__39___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16_spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__22___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__24(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20_spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__39(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__39___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23_spec__34(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__27_spec__41(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__27_spec__41___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__37_spec__50(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__37_spec__50___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23_spec__34_spec__43(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__39_spec__48(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__39_spec__48___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_35012__boxed_343_; lean_object* v_res_344_; 
v___x_35012__boxed_343_ = lean_unbox(v___x_338_);
v_res_344_ = l_main___elam__0___redArg(v___x_337_, v___x_35012__boxed_343_, v_inst_339_, v_ext_340_, v_env_341_);
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
uint8_t v___x_35092__boxed_364_; lean_object* v_res_365_; 
v___x_35092__boxed_364_ = lean_unbox(v___x_356_);
v_res_365_ = l_main___elam__0(v___x_355_, v___x_35092__boxed_364_, v_00_u03b1_357_, v_00_u03b2_358_, v_00_u03c3_359_, v_inst_360_, v_ext_361_, v_env_362_);
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
lean_object* v___x_370_; lean_object* v___x_20094__overap_371_; lean_object* v___x_372_; 
v___x_370_ = lean_obj_once(&l_panic___at___00main_spec__5___closed__0, &l_panic___at___00main_spec__5___closed__0_once, _init_l_panic___at___00main_spec__5___closed__0);
v___x_20094__overap_371_ = lean_panic_fn_borrowed(v___x_370_, v_msg_368_);
v___x_372_ = lean_apply_1(v___x_20094__overap_371_, lean_box(0));
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
uint8_t v___x_35260__boxed_514_; uint8_t v___y_35261__boxed_515_; uint8_t v___x_35262__boxed_516_; uint8_t v___x_35264__boxed_517_; lean_object* v_res_518_; 
v___x_35260__boxed_514_ = lean_unbox(v___x_506_);
v___y_35261__boxed_515_ = lean_unbox(v___y_508_);
v___x_35262__boxed_516_ = lean_unbox(v___x_509_);
v___x_35264__boxed_517_ = lean_unbox(v___x_512_);
v_res_518_ = l_main___lam__1(v___x_504_, v___x_505_, v___x_35260__boxed_514_, v_importArts_507_, v___y_35261__boxed_515_, v___x_35262__boxed_516_, v_name_510_, v___x_511_, v___x_35264__boxed_517_);
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
uint16_t v___x_35333__boxed_646_; uint8_t v___x_35335__boxed_647_; uint8_t v___x_35346__boxed_648_; uint8_t v___x_35347__boxed_649_; uint8_t v___x_35348__boxed_650_; lean_object* v_res_651_; 
v___x_35333__boxed_646_ = lean_unbox(v___x_628_);
v___x_35335__boxed_647_ = lean_unbox(v___x_631_);
v___x_35346__boxed_648_ = lean_unbox(v___x_642_);
v___x_35347__boxed_649_ = lean_unbox(v___x_643_);
v___x_35348__boxed_650_ = lean_unbox(v___x_644_);
v_res_651_ = l_main___lam__2(v___x_626_, v___x_627_, v___x_35333__boxed_646_, v_name_629_, v_a_630_, v___x_35335__boxed_647_, v___x_632_, v_head_633_, v___x_634_, v___x_635_, v___x_636_, v___x_637_, v___x_638_, v___x_639_, v___x_640_, v___x_641_, v___x_35346__boxed_648_, v___x_35347__boxed_649_, v___x_35348__boxed_650_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__26(lean_object* v_as_910_, size_t v_sz_911_, size_t v_i_912_, lean_object* v_b_913_){
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
v___x_921_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__26___closed__0));
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__26___boxed(lean_object* v_as_933_, lean_object* v_sz_934_, lean_object* v_i_935_, lean_object* v_b_936_, lean_object* v___y_937_){
_start:
{
size_t v_sz_boxed_938_; size_t v_i_boxed_939_; lean_object* v_res_940_; 
v_sz_boxed_938_ = lean_unbox_usize(v_sz_934_);
lean_dec(v_sz_934_);
v_i_boxed_939_ = lean_unbox_usize(v_i_935_);
lean_dec(v_i_935_);
v_res_940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__26(v_as_933_, v_sz_boxed_938_, v_i_boxed_939_, v_b_936_);
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
v___x_952_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__26___closed__0));
v___x_953_ = ((size_t)1ULL);
v___x_954_ = lean_usize_add(v_i_943_, v___x_953_);
v___x_955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__26(v_as_941_, v_sz_942_, v___x_954_, v___x_952_);
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
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__29(lean_object* v_msgData_1212_, uint8_t v_severity_1213_, uint8_t v_isSilent_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_ref_1218_; lean_object* v___x_1219_; 
v_ref_1218_ = lean_ctor_get(v___y_1215_, 2);
v___x_1219_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_lintComputable_spec__2_spec__3_spec__4(v_ref_1218_, v_msgData_1212_, v_severity_1213_, v_isSilent_1214_, v___y_1215_, v___y_1216_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__29___boxed(lean_object* v_msgData_1220_, lean_object* v_severity_1221_, lean_object* v_isSilent_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
uint8_t v_severity_boxed_1226_; uint8_t v_isSilent_boxed_1227_; lean_object* v_res_1228_; 
v_severity_boxed_1226_ = lean_unbox(v_severity_1221_);
v_isSilent_boxed_1227_ = lean_unbox(v_isSilent_1222_);
v_res_1228_ = l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__29(v_msgData_1220_, v_severity_boxed_1226_, v_isSilent_boxed_1227_, v___y_1223_, v___y_1224_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13(lean_object* v_msgData_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
uint8_t v___x_1233_; uint8_t v___x_1234_; lean_object* v___x_1235_; 
v___x_1233_ = 2;
v___x_1234_ = 0;
v___x_1235_ = l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__29(v_msgData_1229_, v___x_1233_, v___x_1234_, v___y_1230_, v___y_1231_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13___boxed(lean_object* v_msgData_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_logError___at___00main_spec__13(v_msgData_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
return v_res_1240_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___redArg___lam__0(lean_object* v_x_1241_, lean_object* v_x_1242_){
_start:
{
lean_object* v_fst_1243_; lean_object* v_fst_1244_; lean_object* v_fst_1245_; lean_object* v_fst_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v_fst_1243_ = lean_ctor_get(v_x_1241_, 0);
v_fst_1244_ = lean_ctor_get(v_x_1242_, 0);
v_fst_1245_ = lean_ctor_get(v_fst_1243_, 0);
v_fst_1246_ = lean_ctor_get(v_fst_1244_, 0);
v___x_1247_ = lean_unsigned_to_nat(1u);
v___x_1248_ = lean_nat_add(v_fst_1245_, v___x_1247_);
v___x_1249_ = lean_nat_dec_le(v___x_1248_, v_fst_1246_);
lean_dec(v___x_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___redArg___lam__0___boxed(lean_object* v_x_1250_, lean_object* v_x_1251_){
_start:
{
uint8_t v_res_1252_; lean_object* v_r_1253_; 
v_res_1252_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___redArg___lam__0(v_x_1250_, v_x_1251_);
lean_dec_ref(v_x_1251_);
lean_dec_ref(v_x_1250_);
v_r_1253_ = lean_box(v_res_1252_);
return v_r_1253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20_spec__30___redArg(lean_object* v_hi_1254_, lean_object* v_pivot_1255_, lean_object* v_as_1256_, lean_object* v_i_1257_, lean_object* v_k_1258_){
_start:
{
uint8_t v___x_1259_; 
v___x_1259_ = lean_nat_dec_lt(v_k_1258_, v_hi_1254_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
lean_dec(v_k_1258_);
v___x_1260_ = lean_array_fswap(v_as_1256_, v_i_1257_, v_hi_1254_);
v___x_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1261_, 0, v_i_1257_);
lean_ctor_set(v___x_1261_, 1, v___x_1260_);
return v___x_1261_;
}
else
{
lean_object* v___x_1262_; lean_object* v_fst_1263_; lean_object* v_fst_1264_; lean_object* v_fst_1265_; lean_object* v_fst_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; 
v___x_1262_ = lean_array_fget_borrowed(v_as_1256_, v_k_1258_);
v_fst_1263_ = lean_ctor_get(v___x_1262_, 0);
v_fst_1264_ = lean_ctor_get(v_pivot_1255_, 0);
v_fst_1265_ = lean_ctor_get(v_fst_1263_, 0);
v_fst_1266_ = lean_ctor_get(v_fst_1264_, 0);
v___x_1267_ = lean_unsigned_to_nat(1u);
v___x_1268_ = lean_nat_add(v_fst_1265_, v___x_1267_);
v___x_1269_ = lean_nat_dec_le(v___x_1268_, v_fst_1266_);
lean_dec(v___x_1268_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; 
v___x_1270_ = lean_nat_add(v_k_1258_, v___x_1267_);
lean_dec(v_k_1258_);
v_k_1258_ = v___x_1270_;
goto _start;
}
else
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1272_ = lean_array_fswap(v_as_1256_, v_i_1257_, v_k_1258_);
v___x_1273_ = lean_nat_add(v_i_1257_, v___x_1267_);
lean_dec(v_i_1257_);
v___x_1274_ = lean_nat_add(v_k_1258_, v___x_1267_);
lean_dec(v_k_1258_);
v_as_1256_ = v___x_1272_;
v_i_1257_ = v___x_1273_;
v_k_1258_ = v___x_1274_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20_spec__30___redArg___boxed(lean_object* v_hi_1276_, lean_object* v_pivot_1277_, lean_object* v_as_1278_, lean_object* v_i_1279_, lean_object* v_k_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20_spec__30___redArg(v_hi_1276_, v_pivot_1277_, v_as_1278_, v_i_1279_, v_k_1280_);
lean_dec_ref(v_pivot_1277_);
lean_dec(v_hi_1276_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___redArg(lean_object* v_n_1282_, lean_object* v_as_1283_, lean_object* v_lo_1284_, lean_object* v_hi_1285_){
_start:
{
lean_object* v___y_1287_; uint8_t v___x_1297_; 
v___x_1297_ = lean_nat_dec_lt(v_lo_1284_, v_hi_1285_);
if (v___x_1297_ == 0)
{
lean_dec(v_lo_1284_);
return v_as_1283_;
}
else
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v_mid_1300_; lean_object* v___y_1302_; lean_object* v___y_1308_; lean_object* v___x_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1298_ = lean_nat_add(v_lo_1284_, v_hi_1285_);
v___x_1299_ = lean_unsigned_to_nat(1u);
v_mid_1300_ = lean_nat_shiftr(v___x_1298_, v___x_1299_);
lean_dec(v___x_1298_);
v___x_1313_ = lean_array_fget_borrowed(v_as_1283_, v_mid_1300_);
v___x_1314_ = lean_array_fget_borrowed(v_as_1283_, v_lo_1284_);
v___x_1315_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___redArg___lam__0(v___x_1313_, v___x_1314_);
if (v___x_1315_ == 0)
{
v___y_1308_ = v_as_1283_;
goto v___jp_1307_;
}
else
{
lean_object* v___x_1316_; 
v___x_1316_ = lean_array_fswap(v_as_1283_, v_lo_1284_, v_mid_1300_);
v___y_1308_ = v___x_1316_;
goto v___jp_1307_;
}
v___jp_1301_:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
v___x_1303_ = lean_array_fget_borrowed(v___y_1302_, v_mid_1300_);
v___x_1304_ = lean_array_fget_borrowed(v___y_1302_, v_hi_1285_);
v___x_1305_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___redArg___lam__0(v___x_1303_, v___x_1304_);
if (v___x_1305_ == 0)
{
lean_dec(v_mid_1300_);
v___y_1287_ = v___y_1302_;
goto v___jp_1286_;
}
else
{
lean_object* v___x_1306_; 
v___x_1306_ = lean_array_fswap(v___y_1302_, v_mid_1300_, v_hi_1285_);
lean_dec(v_mid_1300_);
v___y_1287_ = v___x_1306_;
goto v___jp_1286_;
}
}
v___jp_1307_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
v___x_1309_ = lean_array_fget_borrowed(v___y_1308_, v_hi_1285_);
v___x_1310_ = lean_array_fget_borrowed(v___y_1308_, v_lo_1284_);
v___x_1311_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___redArg___lam__0(v___x_1309_, v___x_1310_);
if (v___x_1311_ == 0)
{
v___y_1302_ = v___y_1308_;
goto v___jp_1301_;
}
else
{
lean_object* v___x_1312_; 
v___x_1312_ = lean_array_fswap(v___y_1308_, v_lo_1284_, v_hi_1285_);
v___y_1302_ = v___x_1312_;
goto v___jp_1301_;
}
}
}
v___jp_1286_:
{
lean_object* v_pivot_1288_; lean_object* v___x_1289_; lean_object* v_fst_1290_; lean_object* v_snd_1291_; uint8_t v___x_1292_; 
v_pivot_1288_ = lean_array_fget(v___y_1287_, v_hi_1285_);
lean_inc_n(v_lo_1284_, 2);
v___x_1289_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20_spec__30___redArg(v_hi_1285_, v_pivot_1288_, v___y_1287_, v_lo_1284_, v_lo_1284_);
lean_dec(v_pivot_1288_);
v_fst_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_fst_1290_);
v_snd_1291_ = lean_ctor_get(v___x_1289_, 1);
lean_inc(v_snd_1291_);
lean_dec_ref(v___x_1289_);
v___x_1292_ = lean_nat_dec_le(v_hi_1285_, v_fst_1290_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1293_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___redArg(v_n_1282_, v_snd_1291_, v_lo_1284_, v_fst_1290_);
v___x_1294_ = lean_unsigned_to_nat(1u);
v___x_1295_ = lean_nat_add(v_fst_1290_, v___x_1294_);
lean_dec(v_fst_1290_);
v_as_1283_ = v___x_1293_;
v_lo_1284_ = v___x_1295_;
goto _start;
}
else
{
lean_dec(v_fst_1290_);
lean_dec(v_lo_1284_);
return v_snd_1291_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___redArg___boxed(lean_object* v_n_1317_, lean_object* v_as_1318_, lean_object* v_lo_1319_, lean_object* v_hi_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___redArg(v_n_1317_, v_as_1318_, v_lo_1319_, v_hi_1320_);
lean_dec(v_hi_1320_);
lean_dec(v_n_1317_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(lean_object* v_opts_1322_, lean_object* v_opt_1323_){
_start:
{
lean_object* v_name_1324_; lean_object* v_map_1325_; lean_object* v___x_1326_; 
v_name_1324_ = lean_ctor_get(v_opt_1323_, 0);
v_map_1325_ = lean_ctor_get(v_opts_1322_, 0);
v___x_1326_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1325_, v_name_1324_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_box(0);
return v___x_1327_;
}
else
{
lean_object* v_val_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1337_; 
v_val_1328_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1330_ = v___x_1326_;
v_isShared_1331_ = v_isSharedCheck_1337_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_val_1328_);
lean_dec(v___x_1326_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1337_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
if (lean_obj_tag(v_val_1328_) == 0)
{
lean_object* v_v_1332_; lean_object* v___x_1334_; 
v_v_1332_ = lean_ctor_get(v_val_1328_, 0);
lean_inc_ref(v_v_1332_);
lean_dec_ref_known(v_val_1328_, 1);
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 0, v_v_1332_);
v___x_1334_ = v___x_1330_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_v_1332_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
else
{
lean_object* v___x_1336_; 
lean_del_object(v___x_1330_);
lean_dec(v_val_1328_);
v___x_1336_ = lean_box(0);
return v___x_1336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14___boxed(lean_object* v_opts_1338_, lean_object* v_opt_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(v_opts_1338_, v_opt_1339_);
lean_dec_ref(v_opt_1339_);
lean_dec_ref(v_opts_1338_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16_spec__20___redArg(lean_object* v_a_1341_, lean_object* v_fallback_1342_, lean_object* v_x_1343_){
_start:
{
if (lean_obj_tag(v_x_1343_) == 0)
{
lean_inc(v_fallback_1342_);
return v_fallback_1342_;
}
else
{
lean_object* v_key_1344_; lean_object* v_value_1345_; lean_object* v_tail_1346_; lean_object* v_fst_1347_; lean_object* v_snd_1348_; lean_object* v_fst_1349_; lean_object* v_snd_1350_; uint8_t v_decide_1351_; 
v_key_1344_ = lean_ctor_get(v_x_1343_, 0);
v_value_1345_ = lean_ctor_get(v_x_1343_, 1);
v_tail_1346_ = lean_ctor_get(v_x_1343_, 2);
v_fst_1347_ = lean_ctor_get(v_key_1344_, 0);
v_snd_1348_ = lean_ctor_get(v_key_1344_, 1);
v_fst_1349_ = lean_ctor_get(v_a_1341_, 0);
v_snd_1350_ = lean_ctor_get(v_a_1341_, 1);
v_decide_1351_ = lean_nat_dec_eq(v_fst_1347_, v_fst_1349_);
if (v_decide_1351_ == 0)
{
v_x_1343_ = v_tail_1346_;
goto _start;
}
else
{
uint8_t v_decide_1353_; 
v_decide_1353_ = lean_nat_dec_eq(v_snd_1348_, v_snd_1350_);
if (v_decide_1353_ == 0)
{
v_x_1343_ = v_tail_1346_;
goto _start;
}
else
{
lean_inc(v_value_1345_);
return v_value_1345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16_spec__20___redArg___boxed(lean_object* v_a_1355_, lean_object* v_fallback_1356_, lean_object* v_x_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16_spec__20___redArg(v_a_1355_, v_fallback_1356_, v_x_1357_);
lean_dec(v_x_1357_);
lean_dec(v_fallback_1356_);
lean_dec_ref(v_a_1355_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(lean_object* v_m_1359_, lean_object* v_a_1360_, lean_object* v_fallback_1361_){
_start:
{
lean_object* v_buckets_1362_; lean_object* v_fst_1363_; lean_object* v_snd_1364_; lean_object* v___x_1365_; uint64_t v___x_1366_; uint64_t v___x_1367_; uint64_t v___x_1368_; uint64_t v___x_1369_; uint64_t v___x_1370_; uint64_t v_fold_1371_; uint64_t v___x_1372_; uint64_t v___x_1373_; uint64_t v___x_1374_; size_t v___x_1375_; size_t v___x_1376_; size_t v___x_1377_; size_t v___x_1378_; size_t v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v_buckets_1362_ = lean_ctor_get(v_m_1359_, 1);
v_fst_1363_ = lean_ctor_get(v_a_1360_, 0);
v_snd_1364_ = lean_ctor_get(v_a_1360_, 1);
v___x_1365_ = lean_array_get_size(v_buckets_1362_);
v___x_1366_ = l_String_instHashableRaw_hash(v_fst_1363_);
v___x_1367_ = l_String_instHashableRaw_hash(v_snd_1364_);
v___x_1368_ = lean_uint64_mix_hash(v___x_1366_, v___x_1367_);
v___x_1369_ = 32ULL;
v___x_1370_ = lean_uint64_shift_right(v___x_1368_, v___x_1369_);
v_fold_1371_ = lean_uint64_xor(v___x_1368_, v___x_1370_);
v___x_1372_ = 16ULL;
v___x_1373_ = lean_uint64_shift_right(v_fold_1371_, v___x_1372_);
v___x_1374_ = lean_uint64_xor(v_fold_1371_, v___x_1373_);
v___x_1375_ = lean_uint64_to_usize(v___x_1374_);
v___x_1376_ = lean_usize_of_nat(v___x_1365_);
v___x_1377_ = ((size_t)1ULL);
v___x_1378_ = lean_usize_sub(v___x_1376_, v___x_1377_);
v___x_1379_ = lean_usize_land(v___x_1375_, v___x_1378_);
v___x_1380_ = lean_array_uget_borrowed(v_buckets_1362_, v___x_1379_);
v___x_1381_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16_spec__20___redArg(v_a_1360_, v_fallback_1361_, v___x_1380_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg___boxed(lean_object* v_m_1382_, lean_object* v_a_1383_, lean_object* v_fallback_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v_m_1382_, v_a_1383_, v_fallback_1384_);
lean_dec(v_fallback_1384_);
lean_dec_ref(v_a_1383_);
lean_dec_ref(v_m_1382_);
return v_res_1385_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__22___redArg(lean_object* v_a_1386_, lean_object* v_x_1387_){
_start:
{
if (lean_obj_tag(v_x_1387_) == 0)
{
uint8_t v___x_1388_; 
v___x_1388_ = 0;
return v___x_1388_;
}
else
{
lean_object* v_key_1389_; lean_object* v_tail_1390_; lean_object* v_fst_1391_; lean_object* v_snd_1392_; lean_object* v_fst_1393_; lean_object* v_snd_1394_; uint8_t v_decide_1395_; 
v_key_1389_ = lean_ctor_get(v_x_1387_, 0);
v_tail_1390_ = lean_ctor_get(v_x_1387_, 2);
v_fst_1391_ = lean_ctor_get(v_key_1389_, 0);
v_snd_1392_ = lean_ctor_get(v_key_1389_, 1);
v_fst_1393_ = lean_ctor_get(v_a_1386_, 0);
v_snd_1394_ = lean_ctor_get(v_a_1386_, 1);
v_decide_1395_ = lean_nat_dec_eq(v_fst_1391_, v_fst_1393_);
if (v_decide_1395_ == 0)
{
v_x_1387_ = v_tail_1390_;
goto _start;
}
else
{
uint8_t v_decide_1397_; 
v_decide_1397_ = lean_nat_dec_eq(v_snd_1392_, v_snd_1394_);
if (v_decide_1397_ == 0)
{
v_x_1387_ = v_tail_1390_;
goto _start;
}
else
{
return v_decide_1397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__22___redArg___boxed(lean_object* v_a_1399_, lean_object* v_x_1400_){
_start:
{
uint8_t v_res_1401_; lean_object* v_r_1402_; 
v_res_1401_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__22___redArg(v_a_1399_, v_x_1400_);
lean_dec(v_x_1400_);
lean_dec_ref(v_a_1399_);
v_r_1402_ = lean_box(v_res_1401_);
return v_r_1402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__24___redArg(lean_object* v_a_1403_, lean_object* v_b_1404_, lean_object* v_x_1405_){
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
v___x_1413_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__24___redArg(v_a_1403_, v_b_1404_, v_tail_1408_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23_spec__34_spec__43___redArg(lean_object* v_x_1425_, lean_object* v_x_1426_){
_start:
{
if (lean_obj_tag(v_x_1426_) == 0)
{
return v_x_1425_;
}
else
{
lean_object* v_key_1427_; lean_object* v_value_1428_; lean_object* v_tail_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1456_; 
v_key_1427_ = lean_ctor_get(v_x_1426_, 0);
v_value_1428_ = lean_ctor_get(v_x_1426_, 1);
v_tail_1429_ = lean_ctor_get(v_x_1426_, 2);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_x_1426_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1431_ = v_x_1426_;
v_isShared_1432_ = v_isSharedCheck_1456_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_tail_1429_);
lean_inc(v_value_1428_);
lean_inc(v_key_1427_);
lean_dec(v_x_1426_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1456_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v_fst_1433_; lean_object* v_snd_1434_; lean_object* v___x_1435_; uint64_t v___x_1436_; uint64_t v___x_1437_; uint64_t v___x_1438_; uint64_t v___x_1439_; uint64_t v___x_1440_; uint64_t v_fold_1441_; uint64_t v___x_1442_; uint64_t v___x_1443_; uint64_t v___x_1444_; size_t v___x_1445_; size_t v___x_1446_; size_t v___x_1447_; size_t v___x_1448_; size_t v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1452_; 
v_fst_1433_ = lean_ctor_get(v_key_1427_, 0);
v_snd_1434_ = lean_ctor_get(v_key_1427_, 1);
v___x_1435_ = lean_array_get_size(v_x_1425_);
v___x_1436_ = l_String_instHashableRaw_hash(v_fst_1433_);
v___x_1437_ = l_String_instHashableRaw_hash(v_snd_1434_);
v___x_1438_ = lean_uint64_mix_hash(v___x_1436_, v___x_1437_);
v___x_1439_ = 32ULL;
v___x_1440_ = lean_uint64_shift_right(v___x_1438_, v___x_1439_);
v_fold_1441_ = lean_uint64_xor(v___x_1438_, v___x_1440_);
v___x_1442_ = 16ULL;
v___x_1443_ = lean_uint64_shift_right(v_fold_1441_, v___x_1442_);
v___x_1444_ = lean_uint64_xor(v_fold_1441_, v___x_1443_);
v___x_1445_ = lean_uint64_to_usize(v___x_1444_);
v___x_1446_ = lean_usize_of_nat(v___x_1435_);
v___x_1447_ = ((size_t)1ULL);
v___x_1448_ = lean_usize_sub(v___x_1446_, v___x_1447_);
v___x_1449_ = lean_usize_land(v___x_1445_, v___x_1448_);
v___x_1450_ = lean_array_uget_borrowed(v_x_1425_, v___x_1449_);
lean_inc(v___x_1450_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 2, v___x_1450_);
v___x_1452_ = v___x_1431_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_key_1427_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_value_1428_);
lean_ctor_set(v_reuseFailAlloc_1455_, 2, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
lean_object* v___x_1453_; 
v___x_1453_ = lean_array_uset(v_x_1425_, v___x_1449_, v___x_1452_);
v_x_1425_ = v___x_1453_;
v_x_1426_ = v_tail_1429_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23_spec__34___redArg(lean_object* v_i_1457_, lean_object* v_source_1458_, lean_object* v_target_1459_){
_start:
{
lean_object* v___x_1460_; uint8_t v___x_1461_; 
v___x_1460_ = lean_array_get_size(v_source_1458_);
v___x_1461_ = lean_nat_dec_lt(v_i_1457_, v___x_1460_);
if (v___x_1461_ == 0)
{
lean_dec_ref(v_source_1458_);
lean_dec(v_i_1457_);
return v_target_1459_;
}
else
{
lean_object* v_es_1462_; lean_object* v___x_1463_; lean_object* v_source_1464_; lean_object* v_target_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v_es_1462_ = lean_array_fget(v_source_1458_, v_i_1457_);
v___x_1463_ = lean_box(0);
v_source_1464_ = lean_array_fset(v_source_1458_, v_i_1457_, v___x_1463_);
v_target_1465_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23_spec__34_spec__43___redArg(v_target_1459_, v_es_1462_);
v___x_1466_ = lean_unsigned_to_nat(1u);
v___x_1467_ = lean_nat_add(v_i_1457_, v___x_1466_);
lean_dec(v_i_1457_);
v_i_1457_ = v___x_1467_;
v_source_1458_ = v_source_1464_;
v_target_1459_ = v_target_1465_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23___redArg(lean_object* v_data_1469_){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v_nbuckets_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1470_ = lean_array_get_size(v_data_1469_);
v___x_1471_ = lean_unsigned_to_nat(2u);
v_nbuckets_1472_ = lean_nat_mul(v___x_1470_, v___x_1471_);
v___x_1473_ = lean_unsigned_to_nat(0u);
v___x_1474_ = lean_box(0);
v___x_1475_ = lean_mk_array(v_nbuckets_1472_, v___x_1474_);
v___x_1476_ = lean_array_propagate_mark(v_data_1469_, v___x_1475_);
v___x_1477_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23_spec__34___redArg(v___x_1473_, v_data_1469_, v___x_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(lean_object* v_m_1478_, lean_object* v_a_1479_, lean_object* v_b_1480_){
_start:
{
lean_object* v_size_1481_; lean_object* v_buckets_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1529_; 
v_size_1481_ = lean_ctor_get(v_m_1478_, 0);
v_buckets_1482_ = lean_ctor_get(v_m_1478_, 1);
v_isSharedCheck_1529_ = !lean_is_exclusive(v_m_1478_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1484_ = v_m_1478_;
v_isShared_1485_ = v_isSharedCheck_1529_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_buckets_1482_);
lean_inc(v_size_1481_);
lean_dec(v_m_1478_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1529_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v_fst_1486_; lean_object* v_snd_1487_; lean_object* v___x_1488_; uint64_t v___x_1489_; uint64_t v___x_1490_; uint64_t v___x_1491_; uint64_t v___x_1492_; uint64_t v___x_1493_; uint64_t v_fold_1494_; uint64_t v___x_1495_; uint64_t v___x_1496_; uint64_t v___x_1497_; size_t v___x_1498_; size_t v___x_1499_; size_t v___x_1500_; size_t v___x_1501_; size_t v___x_1502_; lean_object* v_bkt_1503_; uint8_t v___x_1504_; 
v_fst_1486_ = lean_ctor_get(v_a_1479_, 0);
v_snd_1487_ = lean_ctor_get(v_a_1479_, 1);
v___x_1488_ = lean_array_get_size(v_buckets_1482_);
v___x_1489_ = l_String_instHashableRaw_hash(v_fst_1486_);
v___x_1490_ = l_String_instHashableRaw_hash(v_snd_1487_);
v___x_1491_ = lean_uint64_mix_hash(v___x_1489_, v___x_1490_);
v___x_1492_ = 32ULL;
v___x_1493_ = lean_uint64_shift_right(v___x_1491_, v___x_1492_);
v_fold_1494_ = lean_uint64_xor(v___x_1491_, v___x_1493_);
v___x_1495_ = 16ULL;
v___x_1496_ = lean_uint64_shift_right(v_fold_1494_, v___x_1495_);
v___x_1497_ = lean_uint64_xor(v_fold_1494_, v___x_1496_);
v___x_1498_ = lean_uint64_to_usize(v___x_1497_);
v___x_1499_ = lean_usize_of_nat(v___x_1488_);
v___x_1500_ = ((size_t)1ULL);
v___x_1501_ = lean_usize_sub(v___x_1499_, v___x_1500_);
v___x_1502_ = lean_usize_land(v___x_1498_, v___x_1501_);
v_bkt_1503_ = lean_array_uget_borrowed(v_buckets_1482_, v___x_1502_);
v___x_1504_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__22___redArg(v_a_1479_, v_bkt_1503_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; lean_object* v_size_x27_1506_; lean_object* v___x_1507_; lean_object* v_buckets_x27_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; uint8_t v___x_1514_; 
v___x_1505_ = lean_unsigned_to_nat(1u);
v_size_x27_1506_ = lean_nat_add(v_size_1481_, v___x_1505_);
lean_dec(v_size_1481_);
lean_inc(v_bkt_1503_);
v___x_1507_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1507_, 0, v_a_1479_);
lean_ctor_set(v___x_1507_, 1, v_b_1480_);
lean_ctor_set(v___x_1507_, 2, v_bkt_1503_);
v_buckets_x27_1508_ = lean_array_uset(v_buckets_1482_, v___x_1502_, v___x_1507_);
v___x_1509_ = lean_unsigned_to_nat(4u);
v___x_1510_ = lean_nat_mul(v_size_x27_1506_, v___x_1509_);
v___x_1511_ = lean_unsigned_to_nat(3u);
v___x_1512_ = lean_nat_div(v___x_1510_, v___x_1511_);
lean_dec(v___x_1510_);
v___x_1513_ = lean_array_get_size(v_buckets_x27_1508_);
v___x_1514_ = lean_nat_dec_le(v___x_1512_, v___x_1513_);
lean_dec(v___x_1512_);
if (v___x_1514_ == 0)
{
lean_object* v_val_1515_; lean_object* v___x_1517_; 
v_val_1515_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23___redArg(v_buckets_x27_1508_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 1, v_val_1515_);
lean_ctor_set(v___x_1484_, 0, v_size_x27_1506_);
v___x_1517_ = v___x_1484_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_size_x27_1506_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_val_1515_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
else
{
lean_object* v___x_1520_; 
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 1, v_buckets_x27_1508_);
lean_ctor_set(v___x_1484_, 0, v_size_x27_1506_);
v___x_1520_ = v___x_1484_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_size_x27_1506_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v_buckets_x27_1508_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
else
{
lean_object* v___x_1522_; lean_object* v_buckets_x27_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1527_; 
lean_inc(v_bkt_1503_);
v___x_1522_ = lean_box(0);
v_buckets_x27_1523_ = lean_array_uset(v_buckets_1482_, v___x_1502_, v___x_1522_);
v___x_1524_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__24___redArg(v_a_1479_, v_b_1480_, v_bkt_1503_);
v___x_1525_ = lean_array_uset(v_buckets_x27_1523_, v___x_1502_, v___x_1524_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 1, v___x_1525_);
v___x_1527_ = v___x_1484_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_size_1481_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v___x_1525_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__27_spec__41___redArg(uint8_t v___x_1532_, lean_object* v_as_1533_, size_t v_sz_1534_, size_t v_i_1535_, lean_object* v_b_1536_, lean_object* v___y_1537_){
_start:
{
uint8_t v___x_1539_; 
v___x_1539_ = lean_usize_dec_lt(v_i_1535_, v_sz_1534_);
if (v___x_1539_ == 0)
{
lean_object* v___x_1540_; 
v___x_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1540_, 0, v_b_1536_);
return v___x_1540_;
}
else
{
lean_object* v_snd_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1578_; 
v_snd_1541_ = lean_ctor_get(v_b_1536_, 1);
v_isSharedCheck_1578_ = !lean_is_exclusive(v_b_1536_);
if (v_isSharedCheck_1578_ == 0)
{
lean_object* v_unused_1579_; 
v_unused_1579_ = lean_ctor_get(v_b_1536_, 0);
lean_dec(v_unused_1579_);
v___x_1543_ = v_b_1536_;
v_isShared_1544_ = v_isSharedCheck_1578_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_snd_1541_);
lean_dec(v_b_1536_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1578_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v_ref_1545_; lean_object* v_a_1546_; lean_object* v_ref_1547_; lean_object* v_msg_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1577_; 
v_ref_1545_ = lean_ctor_get(v___y_1537_, 2);
v_a_1546_ = lean_array_uget(v_as_1533_, v_i_1535_);
v_ref_1547_ = lean_ctor_get(v_a_1546_, 0);
v_msg_1548_ = lean_ctor_get(v_a_1546_, 1);
v_isSharedCheck_1577_ = !lean_is_exclusive(v_a_1546_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1550_ = v_a_1546_;
v_isShared_1551_ = v_isSharedCheck_1577_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_msg_1548_);
lean_inc(v_ref_1547_);
lean_dec(v_a_1546_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1577_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1552_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v_ref_1569_; lean_object* v___y_1571_; lean_object* v___x_1574_; 
v___x_1552_ = lean_box(0);
v_ref_1569_ = l_Lean_replaceRef(v_ref_1547_, v_ref_1545_);
lean_dec(v_ref_1547_);
v___x_1574_ = l_Lean_Syntax_getPos_x3f(v_ref_1569_, v___x_1532_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v___x_1575_; 
v___x_1575_ = lean_unsigned_to_nat(0u);
v___y_1571_ = v___x_1575_;
goto v___jp_1570_;
}
else
{
lean_object* v_val_1576_; 
v_val_1576_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_val_1576_);
lean_dec_ref_known(v___x_1574_, 1);
v___y_1571_ = v_val_1576_;
goto v___jp_1570_;
}
v___jp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 1, v___y_1555_);
lean_ctor_set(v___x_1543_, 0, v___y_1554_);
v___x_1557_ = v___x_1543_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___y_1554_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v___y_1555_);
v___x_1557_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v_pos2traces_1561_; lean_object* v___x_1563_; 
v___x_1558_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__27_spec__41___redArg___closed__0));
v___x_1559_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v_snd_1541_, v___x_1557_, v___x_1558_);
v___x_1560_ = lean_array_push(v___x_1559_, v_msg_1548_);
v_pos2traces_1561_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1541_, v___x_1557_, v___x_1560_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 1, v_pos2traces_1561_);
lean_ctor_set(v___x_1550_, 0, v___x_1552_);
v___x_1563_ = v___x_1550_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1552_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_pos2traces_1561_);
v___x_1563_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
size_t v___x_1564_; size_t v___x_1565_; 
v___x_1564_ = ((size_t)1ULL);
v___x_1565_ = lean_usize_add(v_i_1535_, v___x_1564_);
v_i_1535_ = v___x_1565_;
v_b_1536_ = v___x_1563_;
goto _start;
}
}
}
v___jp_1570_:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1569_, v___x_1532_);
lean_dec(v_ref_1569_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_inc(v___y_1571_);
v___y_1554_ = v___y_1571_;
v___y_1555_ = v___y_1571_;
goto v___jp_1553_;
}
else
{
lean_object* v_val_1573_; 
v_val_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_val_1573_);
lean_dec_ref_known(v___x_1572_, 1);
v___y_1554_ = v___y_1571_;
v___y_1555_ = v_val_1573_;
goto v___jp_1553_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__27_spec__41___redArg___boxed(lean_object* v___x_1580_, lean_object* v_as_1581_, lean_object* v_sz_1582_, lean_object* v_i_1583_, lean_object* v_b_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
uint8_t v___x_36739__boxed_1587_; size_t v_sz_boxed_1588_; size_t v_i_boxed_1589_; lean_object* v_res_1590_; 
v___x_36739__boxed_1587_ = lean_unbox(v___x_1580_);
v_sz_boxed_1588_ = lean_unbox_usize(v_sz_1582_);
lean_dec(v_sz_1582_);
v_i_boxed_1589_ = lean_unbox_usize(v_i_1583_);
lean_dec(v_i_1583_);
v_res_1590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__27_spec__41___redArg(v___x_36739__boxed_1587_, v_as_1581_, v_sz_boxed_1588_, v_i_boxed_1589_, v_b_1584_, v___y_1585_);
lean_dec_ref(v___y_1585_);
lean_dec_ref(v_as_1581_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__27(uint8_t v___x_1591_, lean_object* v_as_1592_, size_t v_sz_1593_, size_t v_i_1594_, lean_object* v_b_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
uint8_t v___x_1599_; 
v___x_1599_ = lean_usize_dec_lt(v_i_1594_, v_sz_1593_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; 
v___x_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1600_, 0, v_b_1595_);
return v___x_1600_;
}
else
{
lean_object* v_snd_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1638_; 
v_snd_1601_ = lean_ctor_get(v_b_1595_, 1);
v_isSharedCheck_1638_ = !lean_is_exclusive(v_b_1595_);
if (v_isSharedCheck_1638_ == 0)
{
lean_object* v_unused_1639_; 
v_unused_1639_ = lean_ctor_get(v_b_1595_, 0);
lean_dec(v_unused_1639_);
v___x_1603_ = v_b_1595_;
v_isShared_1604_ = v_isSharedCheck_1638_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_snd_1601_);
lean_dec(v_b_1595_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1638_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v_ref_1605_; lean_object* v_a_1606_; lean_object* v_ref_1607_; lean_object* v_msg_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1637_; 
v_ref_1605_ = lean_ctor_get(v___y_1596_, 2);
v_a_1606_ = lean_array_uget(v_as_1592_, v_i_1594_);
v_ref_1607_ = lean_ctor_get(v_a_1606_, 0);
v_msg_1608_ = lean_ctor_get(v_a_1606_, 1);
v_isSharedCheck_1637_ = !lean_is_exclusive(v_a_1606_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1610_ = v_a_1606_;
v_isShared_1611_ = v_isSharedCheck_1637_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_msg_1608_);
lean_inc(v_ref_1607_);
lean_dec(v_a_1606_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1637_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1612_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v_ref_1629_; lean_object* v___y_1631_; lean_object* v___x_1634_; 
v___x_1612_ = lean_box(0);
v_ref_1629_ = l_Lean_replaceRef(v_ref_1607_, v_ref_1605_);
lean_dec(v_ref_1607_);
v___x_1634_ = l_Lean_Syntax_getPos_x3f(v_ref_1629_, v___x_1591_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v___x_1635_; 
v___x_1635_ = lean_unsigned_to_nat(0u);
v___y_1631_ = v___x_1635_;
goto v___jp_1630_;
}
else
{
lean_object* v_val_1636_; 
v_val_1636_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_val_1636_);
lean_dec_ref_known(v___x_1634_, 1);
v___y_1631_ = v_val_1636_;
goto v___jp_1630_;
}
v___jp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 1, v___y_1615_);
lean_ctor_set(v___x_1603_, 0, v___y_1614_);
v___x_1617_ = v___x_1603_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___y_1614_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v___y_1615_);
v___x_1617_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v_pos2traces_1621_; lean_object* v___x_1623_; 
v___x_1618_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__27_spec__41___redArg___closed__0));
v___x_1619_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v_snd_1601_, v___x_1617_, v___x_1618_);
v___x_1620_ = lean_array_push(v___x_1619_, v_msg_1608_);
v_pos2traces_1621_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1601_, v___x_1617_, v___x_1620_);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 1, v_pos2traces_1621_);
lean_ctor_set(v___x_1610_, 0, v___x_1612_);
v___x_1623_ = v___x_1610_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1612_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_pos2traces_1621_);
v___x_1623_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
size_t v___x_1624_; size_t v___x_1625_; lean_object* v___x_1626_; 
v___x_1624_ = ((size_t)1ULL);
v___x_1625_ = lean_usize_add(v_i_1594_, v___x_1624_);
v___x_1626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__27_spec__41___redArg(v___x_1591_, v_as_1592_, v_sz_1593_, v___x_1625_, v___x_1623_, v___y_1596_);
return v___x_1626_;
}
}
}
v___jp_1630_:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1629_, v___x_1591_);
lean_dec(v_ref_1629_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_inc(v___y_1631_);
v___y_1614_ = v___y_1631_;
v___y_1615_ = v___y_1631_;
goto v___jp_1613_;
}
else
{
lean_object* v_val_1633_; 
v_val_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_val_1633_);
lean_dec_ref_known(v___x_1632_, 1);
v___y_1614_ = v___y_1631_;
v___y_1615_ = v_val_1633_;
goto v___jp_1613_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__27___boxed(lean_object* v___x_1640_, lean_object* v_as_1641_, lean_object* v_sz_1642_, lean_object* v_i_1643_, lean_object* v_b_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
uint8_t v___x_36820__boxed_1648_; size_t v_sz_boxed_1649_; size_t v_i_boxed_1650_; lean_object* v_res_1651_; 
v___x_36820__boxed_1648_ = lean_unbox(v___x_1640_);
v_sz_boxed_1649_ = lean_unbox_usize(v_sz_1642_);
lean_dec(v_sz_1642_);
v_i_boxed_1650_ = lean_unbox_usize(v_i_1643_);
lean_dec(v_i_1643_);
v_res_1651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__27(v___x_36820__boxed_1648_, v_as_1641_, v_sz_boxed_1649_, v_i_boxed_1650_, v_b_1644_, v___y_1645_, v___y_1646_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec_ref(v_as_1641_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__39_spec__48___redArg(uint8_t v___x_1652_, lean_object* v_as_1653_, size_t v_sz_1654_, size_t v_i_1655_, lean_object* v_b_1656_, lean_object* v___y_1657_){
_start:
{
uint8_t v___x_1659_; 
v___x_1659_ = lean_usize_dec_lt(v_i_1655_, v_sz_1654_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; 
v___x_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1660_, 0, v_b_1656_);
return v___x_1660_;
}
else
{
lean_object* v_snd_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1698_; 
v_snd_1661_ = lean_ctor_get(v_b_1656_, 1);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_b_1656_);
if (v_isSharedCheck_1698_ == 0)
{
lean_object* v_unused_1699_; 
v_unused_1699_ = lean_ctor_get(v_b_1656_, 0);
lean_dec(v_unused_1699_);
v___x_1663_ = v_b_1656_;
v_isShared_1664_ = v_isSharedCheck_1698_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_snd_1661_);
lean_dec(v_b_1656_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1698_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v_ref_1665_; lean_object* v_a_1666_; lean_object* v_ref_1667_; lean_object* v_msg_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1697_; 
v_ref_1665_ = lean_ctor_get(v___y_1657_, 2);
v_a_1666_ = lean_array_uget(v_as_1653_, v_i_1655_);
v_ref_1667_ = lean_ctor_get(v_a_1666_, 0);
v_msg_1668_ = lean_ctor_get(v_a_1666_, 1);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_a_1666_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1670_ = v_a_1666_;
v_isShared_1671_ = v_isSharedCheck_1697_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_msg_1668_);
lean_inc(v_ref_1667_);
lean_dec(v_a_1666_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1697_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v_ref_1689_; lean_object* v___y_1691_; lean_object* v___x_1694_; 
v___x_1672_ = lean_box(0);
v_ref_1689_ = l_Lean_replaceRef(v_ref_1667_, v_ref_1665_);
lean_dec(v_ref_1667_);
v___x_1694_ = l_Lean_Syntax_getPos_x3f(v_ref_1689_, v___x_1652_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v___x_1695_; 
v___x_1695_ = lean_unsigned_to_nat(0u);
v___y_1691_ = v___x_1695_;
goto v___jp_1690_;
}
else
{
lean_object* v_val_1696_; 
v_val_1696_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_val_1696_);
lean_dec_ref_known(v___x_1694_, 1);
v___y_1691_ = v_val_1696_;
goto v___jp_1690_;
}
v___jp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 1, v___y_1675_);
lean_ctor_set(v___x_1663_, 0, v___y_1674_);
v___x_1677_ = v___x_1663_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___y_1674_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v___y_1675_);
v___x_1677_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v_pos2traces_1681_; lean_object* v___x_1683_; 
v___x_1678_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__27_spec__41___redArg___closed__0));
v___x_1679_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v_snd_1661_, v___x_1677_, v___x_1678_);
v___x_1680_ = lean_array_push(v___x_1679_, v_msg_1668_);
v_pos2traces_1681_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1661_, v___x_1677_, v___x_1680_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 1, v_pos2traces_1681_);
lean_ctor_set(v___x_1670_, 0, v___x_1672_);
v___x_1683_ = v___x_1670_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1672_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_pos2traces_1681_);
v___x_1683_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
size_t v___x_1684_; size_t v___x_1685_; 
v___x_1684_ = ((size_t)1ULL);
v___x_1685_ = lean_usize_add(v_i_1655_, v___x_1684_);
v_i_1655_ = v___x_1685_;
v_b_1656_ = v___x_1683_;
goto _start;
}
}
}
v___jp_1690_:
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1689_, v___x_1652_);
lean_dec(v_ref_1689_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_inc(v___y_1691_);
v___y_1674_ = v___y_1691_;
v___y_1675_ = v___y_1691_;
goto v___jp_1673_;
}
else
{
lean_object* v_val_1693_; 
v_val_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_val_1693_);
lean_dec_ref_known(v___x_1692_, 1);
v___y_1674_ = v___y_1691_;
v___y_1675_ = v_val_1693_;
goto v___jp_1673_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__39_spec__48___redArg___boxed(lean_object* v___x_1700_, lean_object* v_as_1701_, lean_object* v_sz_1702_, lean_object* v_i_1703_, lean_object* v_b_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
uint8_t v___x_36903__boxed_1707_; size_t v_sz_boxed_1708_; size_t v_i_boxed_1709_; lean_object* v_res_1710_; 
v___x_36903__boxed_1707_ = lean_unbox(v___x_1700_);
v_sz_boxed_1708_ = lean_unbox_usize(v_sz_1702_);
lean_dec(v_sz_1702_);
v_i_boxed_1709_ = lean_unbox_usize(v_i_1703_);
lean_dec(v_i_1703_);
v_res_1710_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__39_spec__48___redArg(v___x_36903__boxed_1707_, v_as_1701_, v_sz_boxed_1708_, v_i_boxed_1709_, v_b_1704_, v___y_1705_);
lean_dec_ref(v___y_1705_);
lean_dec_ref(v_as_1701_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__39(uint8_t v___x_1711_, lean_object* v_as_1712_, size_t v_sz_1713_, size_t v_i_1714_, lean_object* v_b_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
uint8_t v___x_1719_; 
v___x_1719_ = lean_usize_dec_lt(v_i_1714_, v_sz_1713_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; 
v___x_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1720_, 0, v_b_1715_);
return v___x_1720_;
}
else
{
lean_object* v_snd_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1758_; 
v_snd_1721_ = lean_ctor_get(v_b_1715_, 1);
v_isSharedCheck_1758_ = !lean_is_exclusive(v_b_1715_);
if (v_isSharedCheck_1758_ == 0)
{
lean_object* v_unused_1759_; 
v_unused_1759_ = lean_ctor_get(v_b_1715_, 0);
lean_dec(v_unused_1759_);
v___x_1723_ = v_b_1715_;
v_isShared_1724_ = v_isSharedCheck_1758_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_snd_1721_);
lean_dec(v_b_1715_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1758_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v_ref_1725_; lean_object* v_a_1726_; lean_object* v_ref_1727_; lean_object* v_msg_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1757_; 
v_ref_1725_ = lean_ctor_get(v___y_1716_, 2);
v_a_1726_ = lean_array_uget(v_as_1712_, v_i_1714_);
v_ref_1727_ = lean_ctor_get(v_a_1726_, 0);
v_msg_1728_ = lean_ctor_get(v_a_1726_, 1);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_a_1726_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1730_ = v_a_1726_;
v_isShared_1731_ = v_isSharedCheck_1757_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_msg_1728_);
lean_inc(v_ref_1727_);
lean_dec(v_a_1726_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1757_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1732_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v_ref_1749_; lean_object* v___y_1751_; lean_object* v___x_1754_; 
v___x_1732_ = lean_box(0);
v_ref_1749_ = l_Lean_replaceRef(v_ref_1727_, v_ref_1725_);
lean_dec(v_ref_1727_);
v___x_1754_ = l_Lean_Syntax_getPos_x3f(v_ref_1749_, v___x_1711_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v___x_1755_; 
v___x_1755_ = lean_unsigned_to_nat(0u);
v___y_1751_ = v___x_1755_;
goto v___jp_1750_;
}
else
{
lean_object* v_val_1756_; 
v_val_1756_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_val_1756_);
lean_dec_ref_known(v___x_1754_, 1);
v___y_1751_ = v_val_1756_;
goto v___jp_1750_;
}
v___jp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 1, v___y_1735_);
lean_ctor_set(v___x_1723_, 0, v___y_1734_);
v___x_1737_ = v___x_1723_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___y_1734_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v___y_1735_);
v___x_1737_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v_pos2traces_1741_; lean_object* v___x_1743_; 
v___x_1738_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__27_spec__41___redArg___closed__0));
v___x_1739_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v_snd_1721_, v___x_1737_, v___x_1738_);
v___x_1740_ = lean_array_push(v___x_1739_, v_msg_1728_);
v_pos2traces_1741_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_snd_1721_, v___x_1737_, v___x_1740_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 1, v_pos2traces_1741_);
lean_ctor_set(v___x_1730_, 0, v___x_1732_);
v___x_1743_ = v___x_1730_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1732_);
lean_ctor_set(v_reuseFailAlloc_1747_, 1, v_pos2traces_1741_);
v___x_1743_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
size_t v___x_1744_; size_t v___x_1745_; lean_object* v___x_1746_; 
v___x_1744_ = ((size_t)1ULL);
v___x_1745_ = lean_usize_add(v_i_1714_, v___x_1744_);
v___x_1746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__39_spec__48___redArg(v___x_1711_, v_as_1712_, v_sz_1713_, v___x_1745_, v___x_1743_, v___y_1716_);
return v___x_1746_;
}
}
}
v___jp_1750_:
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1749_, v___x_1711_);
lean_dec(v_ref_1749_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_inc(v___y_1751_);
v___y_1734_ = v___y_1751_;
v___y_1735_ = v___y_1751_;
goto v___jp_1733_;
}
else
{
lean_object* v_val_1753_; 
v_val_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_val_1753_);
lean_dec_ref_known(v___x_1752_, 1);
v___y_1734_ = v___y_1751_;
v___y_1735_ = v_val_1753_;
goto v___jp_1733_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__39___boxed(lean_object* v___x_1760_, lean_object* v_as_1761_, lean_object* v_sz_1762_, lean_object* v_i_1763_, lean_object* v_b_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
uint8_t v___x_36983__boxed_1768_; size_t v_sz_boxed_1769_; size_t v_i_boxed_1770_; lean_object* v_res_1771_; 
v___x_36983__boxed_1768_ = lean_unbox(v___x_1760_);
v_sz_boxed_1769_ = lean_unbox_usize(v_sz_1762_);
lean_dec(v_sz_1762_);
v_i_boxed_1770_ = lean_unbox_usize(v_i_1763_);
lean_dec(v_i_1763_);
v_res_1771_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__39(v___x_36983__boxed_1768_, v_as_1761_, v_sz_boxed_1769_, v_i_boxed_1770_, v_b_1764_, v___y_1765_, v___y_1766_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec_ref(v_as_1761_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26(lean_object* v_init_1772_, uint8_t v___x_1773_, lean_object* v_n_1774_, lean_object* v_b_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
if (lean_obj_tag(v_n_1774_) == 0)
{
lean_object* v_cs_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; size_t v_sz_1782_; size_t v___x_1783_; lean_object* v___x_1784_; 
v_cs_1779_ = lean_ctor_get(v_n_1774_, 0);
v___x_1780_ = lean_box(0);
v___x_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
lean_ctor_set(v___x_1781_, 1, v_b_1775_);
v_sz_1782_ = lean_array_size(v_cs_1779_);
v___x_1783_ = ((size_t)0ULL);
v___x_1784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__38(v_init_1772_, v___x_1773_, v_cs_1779_, v_sz_1782_, v___x_1783_, v___x_1781_, v___y_1776_, v___y_1777_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1799_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1787_ = v___x_1784_;
v_isShared_1788_ = v_isSharedCheck_1799_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1784_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1799_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v_fst_1789_; 
v_fst_1789_ = lean_ctor_get(v_a_1785_, 0);
if (lean_obj_tag(v_fst_1789_) == 0)
{
lean_object* v_snd_1790_; lean_object* v___x_1791_; lean_object* v___x_1793_; 
v_snd_1790_ = lean_ctor_get(v_a_1785_, 1);
lean_inc(v_snd_1790_);
lean_dec(v_a_1785_);
v___x_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1791_, 0, v_snd_1790_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 0, v___x_1791_);
v___x_1793_ = v___x_1787_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
else
{
lean_object* v_val_1795_; lean_object* v___x_1797_; 
lean_inc_ref(v_fst_1789_);
lean_dec(v_a_1785_);
v_val_1795_ = lean_ctor_get(v_fst_1789_, 0);
lean_inc(v_val_1795_);
lean_dec_ref_known(v_fst_1789_, 1);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 0, v_val_1795_);
v___x_1797_ = v___x_1787_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_val_1795_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
v_a_1800_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1784_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1784_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
else
{
lean_object* v_vs_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; size_t v_sz_1811_; size_t v___x_1812_; lean_object* v___x_1813_; 
v_vs_1808_ = lean_ctor_get(v_n_1774_, 0);
v___x_1809_ = lean_box(0);
v___x_1810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
lean_ctor_set(v___x_1810_, 1, v_b_1775_);
v_sz_1811_ = lean_array_size(v_vs_1808_);
v___x_1812_ = ((size_t)0ULL);
v___x_1813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__39(v___x_1773_, v_vs_1808_, v_sz_1811_, v___x_1812_, v___x_1810_, v___y_1776_, v___y_1777_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1828_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1816_ = v___x_1813_;
v_isShared_1817_ = v_isSharedCheck_1828_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1813_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1828_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v_fst_1818_; 
v_fst_1818_ = lean_ctor_get(v_a_1814_, 0);
if (lean_obj_tag(v_fst_1818_) == 0)
{
lean_object* v_snd_1819_; lean_object* v___x_1820_; lean_object* v___x_1822_; 
v_snd_1819_ = lean_ctor_get(v_a_1814_, 1);
lean_inc(v_snd_1819_);
lean_dec(v_a_1814_);
v___x_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1820_, 0, v_snd_1819_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v___x_1820_);
v___x_1822_ = v___x_1816_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
else
{
lean_object* v_val_1824_; lean_object* v___x_1826_; 
lean_inc_ref(v_fst_1818_);
lean_dec(v_a_1814_);
v_val_1824_ = lean_ctor_get(v_fst_1818_, 0);
lean_inc(v_val_1824_);
lean_dec_ref_known(v_fst_1818_, 1);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v_val_1824_);
v___x_1826_ = v___x_1816_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_val_1824_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
else
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
v_a_1829_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v___x_1813_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1813_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__38(lean_object* v_init_1837_, uint8_t v___x_1838_, lean_object* v_as_1839_, size_t v_sz_1840_, size_t v_i_1841_, lean_object* v_b_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
uint8_t v___x_1846_; 
v___x_1846_ = lean_usize_dec_lt(v_i_1841_, v_sz_1840_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; 
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_b_1842_);
return v___x_1847_;
}
else
{
lean_object* v_snd_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1882_; 
v_snd_1848_ = lean_ctor_get(v_b_1842_, 1);
v_isSharedCheck_1882_ = !lean_is_exclusive(v_b_1842_);
if (v_isSharedCheck_1882_ == 0)
{
lean_object* v_unused_1883_; 
v_unused_1883_ = lean_ctor_get(v_b_1842_, 0);
lean_dec(v_unused_1883_);
v___x_1850_ = v_b_1842_;
v_isShared_1851_ = v_isSharedCheck_1882_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_snd_1848_);
lean_dec(v_b_1842_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1882_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1852_; lean_object* v_a_1853_; lean_object* v___x_1854_; 
v___x_1852_ = lean_box(0);
v_a_1853_ = lean_array_uget_borrowed(v_as_1839_, v_i_1841_);
lean_inc(v_snd_1848_);
v___x_1854_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26(v_init_1837_, v___x_1838_, v_a_1853_, v_snd_1848_, v___y_1843_, v___y_1844_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1873_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1857_ = v___x_1854_;
v_isShared_1858_ = v_isSharedCheck_1873_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1854_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1873_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
if (lean_obj_tag(v_a_1855_) == 0)
{
lean_object* v___x_1859_; lean_object* v___x_1861_; 
v___x_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1859_, 0, v_a_1855_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1859_);
v___x_1861_ = v___x_1850_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1859_);
lean_ctor_set(v_reuseFailAlloc_1865_, 1, v_snd_1848_);
v___x_1861_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1863_; 
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 0, v___x_1861_);
v___x_1863_ = v___x_1857_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; 
lean_del_object(v___x_1857_);
lean_dec(v_snd_1848_);
v_a_1866_ = lean_ctor_get(v_a_1855_, 0);
lean_inc(v_a_1866_);
lean_dec_ref_known(v_a_1855_, 1);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 1, v_a_1866_);
lean_ctor_set(v___x_1850_, 0, v___x_1852_);
v___x_1868_ = v___x_1850_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1852_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_a_1866_);
v___x_1868_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
size_t v___x_1869_; size_t v___x_1870_; 
v___x_1869_ = ((size_t)1ULL);
v___x_1870_ = lean_usize_add(v_i_1841_, v___x_1869_);
v_i_1841_ = v___x_1870_;
v_b_1842_ = v___x_1868_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_del_object(v___x_1850_);
lean_dec(v_snd_1848_);
v_a_1874_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1854_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1854_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__38___boxed(lean_object* v_init_1884_, lean_object* v___x_1885_, lean_object* v_as_1886_, lean_object* v_sz_1887_, lean_object* v_i_1888_, lean_object* v_b_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
uint8_t v___x_37064__boxed_1893_; size_t v_sz_boxed_1894_; size_t v_i_boxed_1895_; lean_object* v_res_1896_; 
v___x_37064__boxed_1893_ = lean_unbox(v___x_1885_);
v_sz_boxed_1894_ = lean_unbox_usize(v_sz_1887_);
lean_dec(v_sz_1887_);
v_i_boxed_1895_ = lean_unbox_usize(v_i_1888_);
lean_dec(v_i_1888_);
v_res_1896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__38(v_init_1884_, v___x_37064__boxed_1893_, v_as_1886_, v_sz_boxed_1894_, v_i_boxed_1895_, v_b_1889_, v___y_1890_, v___y_1891_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec_ref(v_as_1886_);
lean_dec_ref(v_init_1884_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26___boxed(lean_object* v_init_1897_, lean_object* v___x_1898_, lean_object* v_n_1899_, lean_object* v_b_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
uint8_t v___x_37084__boxed_1904_; lean_object* v_res_1905_; 
v___x_37084__boxed_1904_ = lean_unbox(v___x_1898_);
v_res_1905_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26(v_init_1897_, v___x_37084__boxed_1904_, v_n_1899_, v_b_1900_, v___y_1901_, v___y_1902_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec_ref(v_n_1899_);
lean_dec_ref(v_init_1897_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18(uint8_t v___x_1906_, lean_object* v_t_1907_, lean_object* v_init_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v_root_1912_; lean_object* v_tail_1913_; lean_object* v___x_1914_; 
v_root_1912_ = lean_ctor_get(v_t_1907_, 0);
v_tail_1913_ = lean_ctor_get(v_t_1907_, 1);
lean_inc_ref(v_init_1908_);
v___x_1914_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26(v_init_1908_, v___x_1906_, v_root_1912_, v_init_1908_, v___y_1909_, v___y_1910_);
lean_dec_ref(v_init_1908_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1951_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1917_ = v___x_1914_;
v_isShared_1918_ = v_isSharedCheck_1951_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1914_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1951_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
if (lean_obj_tag(v_a_1915_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1921_; 
v_a_1919_ = lean_ctor_get(v_a_1915_, 0);
lean_inc(v_a_1919_);
lean_dec_ref_known(v_a_1915_, 1);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 0, v_a_1919_);
v___x_1921_ = v___x_1917_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1919_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
else
{
lean_object* v_a_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; size_t v_sz_1926_; size_t v___x_1927_; lean_object* v___x_1928_; 
lean_del_object(v___x_1917_);
v_a_1923_ = lean_ctor_get(v_a_1915_, 0);
lean_inc(v_a_1923_);
lean_dec_ref_known(v_a_1915_, 1);
v___x_1924_ = lean_box(0);
v___x_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
lean_ctor_set(v___x_1925_, 1, v_a_1923_);
v_sz_1926_ = lean_array_size(v_tail_1913_);
v___x_1927_ = ((size_t)0ULL);
v___x_1928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__27(v___x_1906_, v_tail_1913_, v_sz_1926_, v___x_1927_, v___x_1925_, v___y_1909_, v___y_1910_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1942_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1931_ = v___x_1928_;
v_isShared_1932_ = v_isSharedCheck_1942_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1928_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1942_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v_fst_1933_; 
v_fst_1933_ = lean_ctor_get(v_a_1929_, 0);
if (lean_obj_tag(v_fst_1933_) == 0)
{
lean_object* v_snd_1934_; lean_object* v___x_1936_; 
v_snd_1934_ = lean_ctor_get(v_a_1929_, 1);
lean_inc(v_snd_1934_);
lean_dec(v_a_1929_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v_snd_1934_);
v___x_1936_ = v___x_1931_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_snd_1934_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
else
{
lean_object* v_val_1938_; lean_object* v___x_1940_; 
lean_inc_ref(v_fst_1933_);
lean_dec(v_a_1929_);
v_val_1938_ = lean_ctor_get(v_fst_1933_, 0);
lean_inc(v_val_1938_);
lean_dec_ref_known(v_fst_1933_, 1);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v_val_1938_);
v___x_1940_ = v___x_1931_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_val_1938_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
v_a_1943_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1928_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1928_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
v_a_1952_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1914_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1914_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18___boxed(lean_object* v___x_1960_, lean_object* v_t_1961_, lean_object* v_init_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
uint8_t v___x_37265__boxed_1966_; lean_object* v_res_1967_; 
v___x_37265__boxed_1966_ = lean_unbox(v___x_1960_);
v_res_1967_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18(v___x_37265__boxed_1966_, v_t_1961_, v_init_1962_, v___y_1963_, v___y_1964_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec_ref(v_t_1961_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21(lean_object* v_x_1968_, lean_object* v_x_1969_){
_start:
{
if (lean_obj_tag(v_x_1969_) == 0)
{
return v_x_1968_;
}
else
{
lean_object* v_key_1970_; lean_object* v_value_1971_; lean_object* v_tail_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v_key_1970_ = lean_ctor_get(v_x_1969_, 0);
v_value_1971_ = lean_ctor_get(v_x_1969_, 1);
v_tail_1972_ = lean_ctor_get(v_x_1969_, 2);
lean_inc(v_value_1971_);
lean_inc(v_key_1970_);
v___x_1973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1973_, 0, v_key_1970_);
lean_ctor_set(v___x_1973_, 1, v_value_1971_);
v___x_1974_ = lean_array_push(v_x_1968_, v___x_1973_);
v_x_1968_ = v___x_1974_;
v_x_1969_ = v_tail_1972_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21___boxed(lean_object* v_x_1976_, lean_object* v_x_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21(v_x_1976_, v_x_1977_);
lean_dec(v_x_1977_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22(lean_object* v_as_1979_, size_t v_i_1980_, size_t v_stop_1981_, lean_object* v_b_1982_){
_start:
{
uint8_t v___x_1983_; 
v___x_1983_ = lean_usize_dec_eq(v_i_1980_, v_stop_1981_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; lean_object* v___x_1985_; size_t v___x_1986_; size_t v___x_1987_; 
v___x_1984_ = lean_array_uget_borrowed(v_as_1979_, v_i_1980_);
v___x_1985_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__21(v_b_1982_, v___x_1984_);
v___x_1986_ = ((size_t)1ULL);
v___x_1987_ = lean_usize_add(v_i_1980_, v___x_1986_);
v_i_1980_ = v___x_1987_;
v_b_1982_ = v___x_1985_;
goto _start;
}
else
{
return v_b_1982_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22___boxed(lean_object* v_as_1989_, lean_object* v_i_1990_, lean_object* v_stop_1991_, lean_object* v_b_1992_){
_start:
{
size_t v_i_boxed_1993_; size_t v_stop_boxed_1994_; lean_object* v_res_1995_; 
v_i_boxed_1993_ = lean_unbox_usize(v_i_1990_);
lean_dec(v_i_1990_);
v_stop_boxed_1994_ = lean_unbox_usize(v_stop_1991_);
lean_dec(v_stop_1991_);
v_res_1995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22(v_as_1989_, v_i_boxed_1993_, v_stop_boxed_1994_, v_b_1992_);
lean_dec_ref(v_as_1989_);
return v_res_1995_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0(uint8_t v_suppressElabErrors_2003_, uint8_t v___x_2004_, lean_object* v___x_2005_, lean_object* v_x_2006_){
_start:
{
if (lean_obj_tag(v_x_2006_) == 1)
{
lean_object* v_pre_2007_; 
v_pre_2007_ = lean_ctor_get(v_x_2006_, 0);
switch(lean_obj_tag(v_pre_2007_))
{
case 1:
{
lean_object* v_pre_2008_; 
v_pre_2008_ = lean_ctor_get(v_pre_2007_, 0);
switch(lean_obj_tag(v_pre_2008_))
{
case 0:
{
lean_object* v_str_2009_; lean_object* v_str_2010_; lean_object* v___x_2011_; uint8_t v___x_2012_; 
v_str_2009_ = lean_ctor_get(v_x_2006_, 1);
v_str_2010_ = lean_ctor_get(v_pre_2007_, 1);
v___x_2011_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__0));
v___x_2012_ = lean_string_dec_eq(v_str_2010_, v___x_2011_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; uint8_t v___x_2014_; 
v___x_2013_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__1));
v___x_2014_ = lean_string_dec_eq(v_str_2010_, v___x_2013_);
if (v___x_2014_ == 0)
{
return v___x_2014_;
}
else
{
lean_object* v___x_2015_; uint8_t v___x_2016_; 
v___x_2015_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__2));
v___x_2016_ = lean_string_dec_eq(v_str_2009_, v___x_2015_);
if (v___x_2016_ == 0)
{
return v___x_2016_;
}
else
{
return v_suppressElabErrors_2003_;
}
}
}
else
{
lean_object* v___x_2017_; uint8_t v___x_2018_; 
v___x_2017_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__3));
v___x_2018_ = lean_string_dec_eq(v_str_2009_, v___x_2017_);
if (v___x_2018_ == 0)
{
return v___x_2018_;
}
else
{
return v_suppressElabErrors_2003_;
}
}
}
case 1:
{
lean_object* v_pre_2019_; 
v_pre_2019_ = lean_ctor_get(v_pre_2008_, 0);
if (lean_obj_tag(v_pre_2019_) == 0)
{
lean_object* v_str_2020_; lean_object* v_str_2021_; lean_object* v_str_2022_; lean_object* v___x_2023_; uint8_t v___x_2024_; 
v_str_2020_ = lean_ctor_get(v_x_2006_, 1);
v_str_2021_ = lean_ctor_get(v_pre_2007_, 1);
v_str_2022_ = lean_ctor_get(v_pre_2008_, 1);
v___x_2023_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__4));
v___x_2024_ = lean_string_dec_eq(v_str_2022_, v___x_2023_);
if (v___x_2024_ == 0)
{
return v___x_2024_;
}
else
{
lean_object* v___x_2025_; uint8_t v___x_2026_; 
v___x_2025_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__5));
v___x_2026_ = lean_string_dec_eq(v_str_2021_, v___x_2025_);
if (v___x_2026_ == 0)
{
return v___x_2026_;
}
else
{
lean_object* v___x_2027_; uint8_t v___x_2028_; 
v___x_2027_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___closed__6));
v___x_2028_ = lean_string_dec_eq(v_str_2020_, v___x_2027_);
if (v___x_2028_ == 0)
{
return v___x_2028_;
}
else
{
return v_suppressElabErrors_2003_;
}
}
}
}
else
{
return v___x_2004_;
}
}
default: 
{
return v___x_2004_;
}
}
}
case 0:
{
lean_object* v_str_2029_; uint8_t v___x_2030_; 
v_str_2029_ = lean_ctor_get(v_x_2006_, 1);
v___x_2030_ = lean_string_dec_eq(v_str_2029_, v___x_2005_);
if (v___x_2030_ == 0)
{
return v___x_2030_;
}
else
{
return v_suppressElabErrors_2003_;
}
}
default: 
{
return v___x_2004_;
}
}
}
else
{
return v___x_2004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___boxed(lean_object* v_suppressElabErrors_2031_, lean_object* v___x_2032_, lean_object* v___x_2033_, lean_object* v_x_2034_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2035_; uint8_t v___x_37407__boxed_2036_; uint8_t v_res_2037_; lean_object* v_r_2038_; 
v_suppressElabErrors_boxed_2035_ = lean_unbox(v_suppressElabErrors_2031_);
v___x_37407__boxed_2036_ = lean_unbox(v___x_2032_);
v_res_2037_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0(v_suppressElabErrors_boxed_2035_, v___x_37407__boxed_2036_, v___x_2033_, v_x_2034_);
lean_dec(v_x_2034_);
lean_dec_ref(v___x_2033_);
v_r_2038_ = lean_box(v_res_2037_);
return v_r_2038_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___closed__0(void){
_start:
{
lean_object* v___x_2039_; double v___x_2040_; 
v___x_2039_ = lean_unsigned_to_nat(0u);
v___x_2040_ = lean_float_of_nat(v___x_2039_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(uint8_t v___x_2042_, lean_object* v_as_2043_, size_t v_sz_2044_, size_t v_i_2045_, lean_object* v_b_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v_a_2051_; uint8_t v___x_2055_; 
v___x_2055_ = lean_usize_dec_lt(v_i_2045_, v_sz_2044_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; 
v___x_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2056_, 0, v_b_2046_);
return v___x_2056_;
}
else
{
lean_object* v_a_2057_; lean_object* v_fst_2058_; lean_object* v_snd_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2138_; 
v_a_2057_ = lean_array_uget(v_as_2043_, v_i_2045_);
v_fst_2058_ = lean_ctor_get(v_a_2057_, 0);
v_snd_2059_ = lean_ctor_get(v_a_2057_, 1);
v_isSharedCheck_2138_ = !lean_is_exclusive(v_a_2057_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2061_ = v_a_2057_;
v_isShared_2062_ = v_isSharedCheck_2138_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_snd_2059_);
lean_inc(v_fst_2058_);
lean_dec(v_a_2057_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2138_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v_fst_2063_; lean_object* v_snd_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2137_; 
v_fst_2063_ = lean_ctor_get(v_fst_2058_, 0);
v_snd_2064_ = lean_ctor_get(v_fst_2058_, 1);
v_isSharedCheck_2137_ = !lean_is_exclusive(v_fst_2058_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2066_ = v_fst_2058_;
v_isShared_2067_ = v_isSharedCheck_2137_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_snd_2064_);
lean_inc(v_fst_2063_);
lean_dec(v_fst_2058_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2137_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; double v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v_toCold_2073_; uint8_t v_suppressElabErrors_2074_; lean_object* v_fileName_2075_; lean_object* v_fileMap_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2083_; 
v___x_2068_ = lean_box(0);
v___x_2069_ = lean_box(0);
v___x_2070_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___closed__0);
v___x_2071_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___closed__1));
v___x_2072_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2072_, 0, v___x_2068_);
lean_ctor_set(v___x_2072_, 1, v___x_2069_);
lean_ctor_set(v___x_2072_, 2, v___x_2071_);
lean_ctor_set_float(v___x_2072_, sizeof(void*)*3, v___x_2070_);
lean_ctor_set_float(v___x_2072_, sizeof(void*)*3 + 8, v___x_2070_);
lean_ctor_set_uint8(v___x_2072_, sizeof(void*)*3 + 16, v___x_2055_);
v_toCold_2073_ = lean_ctor_get(v___y_2047_, 0);
v_suppressElabErrors_2074_ = lean_ctor_get_uint8(v___y_2047_, sizeof(void*)*3 + 2);
v_fileName_2075_ = lean_ctor_get(v_toCold_2073_, 0);
v_fileMap_2076_ = lean_ctor_get(v_toCold_2073_, 1);
v___x_2077_ = lean_box(0);
v___x_2078_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_2079_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_2080_ = l_Lean_MessageData_nil;
v___x_2081_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2072_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
lean_ctor_set(v___x_2081_, 2, v_snd_2059_);
if (v_isShared_2067_ == 0)
{
lean_ctor_set_tag(v___x_2066_, 8);
lean_ctor_set(v___x_2066_, 1, v___x_2081_);
lean_ctor_set(v___x_2066_, 0, v___x_2079_);
v___x_2083_ = v___x_2066_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2079_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
uint8_t v___x_2084_; lean_object* v___x_2085_; lean_object* v___y_2087_; lean_object* v___y_2088_; 
v___x_2084_ = 0;
lean_inc_ref(v_fileMap_2076_);
lean_inc_ref(v_fileName_2075_);
v___x_2085_ = l_Lean_Elab_mkMessageCore(v_fileName_2075_, v_fileMap_2076_, v___x_2083_, v___x_2084_, v_fst_2063_, v_snd_2064_);
lean_dec(v_snd_2064_);
lean_dec(v_fst_2063_);
if (v_suppressElabErrors_2074_ == 0)
{
v___y_2087_ = v___y_2047_;
v___y_2088_ = v___y_2048_;
goto v___jp_2086_;
}
else
{
lean_object* v_data_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___f_2134_; uint8_t v___x_2135_; 
v_data_2131_ = lean_ctor_get(v___x_2085_, 4);
v___x_2132_ = lean_box(v_suppressElabErrors_2074_);
v___x_2133_ = lean_box(v___x_2042_);
v___f_2134_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2134_, 0, v___x_2132_);
lean_closure_set(v___f_2134_, 1, v___x_2133_);
lean_closure_set(v___f_2134_, 2, v___x_2078_);
lean_inc(v_data_2131_);
v___x_2135_ = l_Lean_MessageData_hasTag(v___f_2134_, v_data_2131_);
if (v___x_2135_ == 0)
{
lean_dec_ref(v___x_2085_);
lean_del_object(v___x_2061_);
v_a_2051_ = v___x_2077_;
goto v___jp_2050_;
}
else
{
v___y_2087_ = v___y_2047_;
v___y_2088_ = v___y_2048_;
goto v___jp_2086_;
}
}
v___jp_2086_:
{
lean_object* v_toCold_2089_; lean_object* v_fileName_2090_; lean_object* v_pos_2091_; lean_object* v_endPos_2092_; uint8_t v_keepFullRange_2093_; uint8_t v_severity_2094_; uint8_t v_isSilent_2095_; lean_object* v_caption_2096_; lean_object* v_data_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2130_; 
v_toCold_2089_ = lean_ctor_get(v___y_2087_, 0);
v_fileName_2090_ = lean_ctor_get(v___x_2085_, 0);
v_pos_2091_ = lean_ctor_get(v___x_2085_, 1);
v_endPos_2092_ = lean_ctor_get(v___x_2085_, 2);
v_keepFullRange_2093_ = lean_ctor_get_uint8(v___x_2085_, sizeof(void*)*5);
v_severity_2094_ = lean_ctor_get_uint8(v___x_2085_, sizeof(void*)*5 + 1);
v_isSilent_2095_ = lean_ctor_get_uint8(v___x_2085_, sizeof(void*)*5 + 2);
v_caption_2096_ = lean_ctor_get(v___x_2085_, 3);
v_data_2097_ = lean_ctor_get(v___x_2085_, 4);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2099_ = v___x_2085_;
v_isShared_2100_ = v_isSharedCheck_2130_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_data_2097_);
lean_inc(v_caption_2096_);
lean_inc(v_endPos_2092_);
lean_inc(v_pos_2091_);
lean_inc(v_fileName_2090_);
lean_dec(v___x_2085_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2130_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v_currNamespace_2101_; lean_object* v_openDecls_2102_; lean_object* v___x_2104_; 
v_currNamespace_2101_ = lean_ctor_get(v_toCold_2089_, 4);
v_openDecls_2102_ = lean_ctor_get(v_toCold_2089_, 5);
lean_inc(v_openDecls_2102_);
lean_inc(v_currNamespace_2101_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 1, v_openDecls_2102_);
lean_ctor_set(v___x_2061_, 0, v_currNamespace_2101_);
v___x_2104_ = v___x_2061_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_currNamespace_2101_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_openDecls_2102_);
v___x_2104_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
lean_object* v___x_2105_; lean_object* v___x_2107_; 
v___x_2105_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
lean_ctor_set(v___x_2105_, 1, v_data_2097_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 4, v___x_2105_);
v___x_2107_ = v___x_2099_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_fileName_2090_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v_pos_2091_);
lean_ctor_set(v_reuseFailAlloc_2128_, 2, v_endPos_2092_);
lean_ctor_set(v_reuseFailAlloc_2128_, 3, v_caption_2096_);
lean_ctor_set(v_reuseFailAlloc_2128_, 4, v___x_2105_);
lean_ctor_set_uint8(v_reuseFailAlloc_2128_, sizeof(void*)*5, v_keepFullRange_2093_);
lean_ctor_set_uint8(v_reuseFailAlloc_2128_, sizeof(void*)*5 + 1, v_severity_2094_);
lean_ctor_set_uint8(v_reuseFailAlloc_2128_, sizeof(void*)*5 + 2, v_isSilent_2095_);
v___x_2107_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v___x_2108_; lean_object* v_env_2109_; lean_object* v_nextMacroScope_2110_; lean_object* v_ngen_2111_; lean_object* v_auxDeclNGen_2112_; lean_object* v_traceState_2113_; lean_object* v_cache_2114_; lean_object* v_recordedDeps_2115_; lean_object* v_messages_2116_; lean_object* v_infoState_2117_; lean_object* v_snapshotTasks_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2127_; 
v___x_2108_ = lean_st_ref_take(v___y_2088_);
v_env_2109_ = lean_ctor_get(v___x_2108_, 0);
v_nextMacroScope_2110_ = lean_ctor_get(v___x_2108_, 1);
v_ngen_2111_ = lean_ctor_get(v___x_2108_, 2);
v_auxDeclNGen_2112_ = lean_ctor_get(v___x_2108_, 3);
v_traceState_2113_ = lean_ctor_get(v___x_2108_, 4);
v_cache_2114_ = lean_ctor_get(v___x_2108_, 5);
v_recordedDeps_2115_ = lean_ctor_get(v___x_2108_, 6);
v_messages_2116_ = lean_ctor_get(v___x_2108_, 7);
v_infoState_2117_ = lean_ctor_get(v___x_2108_, 8);
v_snapshotTasks_2118_ = lean_ctor_get(v___x_2108_, 9);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2120_ = v___x_2108_;
v_isShared_2121_ = v_isSharedCheck_2127_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_snapshotTasks_2118_);
lean_inc(v_infoState_2117_);
lean_inc(v_messages_2116_);
lean_inc(v_recordedDeps_2115_);
lean_inc(v_cache_2114_);
lean_inc(v_traceState_2113_);
lean_inc(v_auxDeclNGen_2112_);
lean_inc(v_ngen_2111_);
lean_inc(v_nextMacroScope_2110_);
lean_inc(v_env_2109_);
lean_dec(v___x_2108_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2127_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2122_; lean_object* v___x_2124_; 
v___x_2122_ = l_Lean_MessageLog_add(v___x_2107_, v_messages_2116_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 7, v___x_2122_);
v___x_2124_ = v___x_2120_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_env_2109_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v_nextMacroScope_2110_);
lean_ctor_set(v_reuseFailAlloc_2126_, 2, v_ngen_2111_);
lean_ctor_set(v_reuseFailAlloc_2126_, 3, v_auxDeclNGen_2112_);
lean_ctor_set(v_reuseFailAlloc_2126_, 4, v_traceState_2113_);
lean_ctor_set(v_reuseFailAlloc_2126_, 5, v_cache_2114_);
lean_ctor_set(v_reuseFailAlloc_2126_, 6, v_recordedDeps_2115_);
lean_ctor_set(v_reuseFailAlloc_2126_, 7, v___x_2122_);
lean_ctor_set(v_reuseFailAlloc_2126_, 8, v_infoState_2117_);
lean_ctor_set(v_reuseFailAlloc_2126_, 9, v_snapshotTasks_2118_);
v___x_2124_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
lean_object* v___x_2125_; 
v___x_2125_ = lean_st_ref_put(v___y_2088_, v___x_2124_);
v_a_2051_ = v___x_2077_;
goto v___jp_2050_;
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
v___jp_2050_:
{
size_t v___x_2052_; size_t v___x_2053_; 
v___x_2052_ = ((size_t)1ULL);
v___x_2053_ = lean_usize_add(v_i_2045_, v___x_2052_);
v_i_2045_ = v___x_2053_;
v_b_2046_ = v_a_2051_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19___boxed(lean_object* v___x_2139_, lean_object* v_as_2140_, lean_object* v_sz_2141_, lean_object* v_i_2142_, lean_object* v_b_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
uint8_t v___x_37480__boxed_2147_; size_t v_sz_boxed_2148_; size_t v_i_boxed_2149_; lean_object* v_res_2150_; 
v___x_37480__boxed_2147_ = lean_unbox(v___x_2139_);
v_sz_boxed_2148_ = lean_unbox_usize(v_sz_2141_);
lean_dec(v_sz_2141_);
v_i_boxed_2149_ = lean_unbox_usize(v_i_2142_);
lean_dec(v_i_2142_);
v_res_2150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(v___x_37480__boxed_2147_, v_as_2140_, v_sz_boxed_2148_, v_i_boxed_2149_, v_b_2143_, v___y_2144_, v___y_2145_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
lean_dec_ref(v_as_2140_);
return v_res_2150_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg___closed__0(void){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2151_ = lean_unsigned_to_nat(32u);
v___x_2152_ = lean_mk_empty_array_with_capacity(v___x_2151_);
v___x_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
return v___x_2153_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg___closed__1(void){
_start:
{
size_t v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2154_ = ((size_t)5ULL);
v___x_2155_ = lean_unsigned_to_nat(0u);
v___x_2156_ = lean_unsigned_to_nat(32u);
v___x_2157_ = lean_mk_empty_array_with_capacity(v___x_2156_);
v___x_2158_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg___closed__0);
v___x_2159_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
lean_ctor_set(v___x_2159_, 1, v___x_2157_);
lean_ctor_set(v___x_2159_, 2, v___x_2155_);
lean_ctor_set(v___x_2159_, 3, v___x_2155_);
lean_ctor_set_usize(v___x_2159_, 4, v___x_2154_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg(lean_object* v___y_2160_){
_start:
{
lean_object* v___x_2162_; lean_object* v_traceState_2163_; lean_object* v_traces_2164_; lean_object* v___x_2165_; lean_object* v_traceState_2166_; lean_object* v_env_2167_; lean_object* v_nextMacroScope_2168_; lean_object* v_ngen_2169_; lean_object* v_auxDeclNGen_2170_; lean_object* v_cache_2171_; lean_object* v_recordedDeps_2172_; lean_object* v_messages_2173_; lean_object* v_infoState_2174_; lean_object* v_snapshotTasks_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2194_; 
v___x_2162_ = lean_st_ref_get(v___y_2160_);
v_traceState_2163_ = lean_ctor_get(v___x_2162_, 4);
lean_inc_ref(v_traceState_2163_);
lean_dec(v___x_2162_);
v_traces_2164_ = lean_ctor_get(v_traceState_2163_, 0);
lean_inc_ref(v_traces_2164_);
lean_dec_ref(v_traceState_2163_);
v___x_2165_ = lean_st_ref_take(v___y_2160_);
v_traceState_2166_ = lean_ctor_get(v___x_2165_, 4);
v_env_2167_ = lean_ctor_get(v___x_2165_, 0);
v_nextMacroScope_2168_ = lean_ctor_get(v___x_2165_, 1);
v_ngen_2169_ = lean_ctor_get(v___x_2165_, 2);
v_auxDeclNGen_2170_ = lean_ctor_get(v___x_2165_, 3);
v_cache_2171_ = lean_ctor_get(v___x_2165_, 5);
v_recordedDeps_2172_ = lean_ctor_get(v___x_2165_, 6);
v_messages_2173_ = lean_ctor_get(v___x_2165_, 7);
v_infoState_2174_ = lean_ctor_get(v___x_2165_, 8);
v_snapshotTasks_2175_ = lean_ctor_get(v___x_2165_, 9);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2177_ = v___x_2165_;
v_isShared_2178_ = v_isSharedCheck_2194_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_snapshotTasks_2175_);
lean_inc(v_infoState_2174_);
lean_inc(v_messages_2173_);
lean_inc(v_recordedDeps_2172_);
lean_inc(v_cache_2171_);
lean_inc(v_traceState_2166_);
lean_inc(v_auxDeclNGen_2170_);
lean_inc(v_ngen_2169_);
lean_inc(v_nextMacroScope_2168_);
lean_inc(v_env_2167_);
lean_dec(v___x_2165_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2194_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
uint64_t v_tid_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2192_; 
v_tid_2179_ = lean_ctor_get_uint64(v_traceState_2166_, sizeof(void*)*1);
v_isSharedCheck_2192_ = !lean_is_exclusive(v_traceState_2166_);
if (v_isSharedCheck_2192_ == 0)
{
lean_object* v_unused_2193_; 
v_unused_2193_ = lean_ctor_get(v_traceState_2166_, 0);
lean_dec(v_unused_2193_);
v___x_2181_ = v_traceState_2166_;
v_isShared_2182_ = v_isSharedCheck_2192_;
goto v_resetjp_2180_;
}
else
{
lean_dec(v_traceState_2166_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2192_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2183_; lean_object* v___x_2185_; 
v___x_2183_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg___closed__1);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 0, v___x_2183_);
v___x_2185_ = v___x_2181_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2183_);
lean_ctor_set_uint64(v_reuseFailAlloc_2191_, sizeof(void*)*1, v_tid_2179_);
v___x_2185_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
lean_object* v___x_2187_; 
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 4, v___x_2185_);
v___x_2187_ = v___x_2177_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_env_2167_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v_nextMacroScope_2168_);
lean_ctor_set(v_reuseFailAlloc_2190_, 2, v_ngen_2169_);
lean_ctor_set(v_reuseFailAlloc_2190_, 3, v_auxDeclNGen_2170_);
lean_ctor_set(v_reuseFailAlloc_2190_, 4, v___x_2185_);
lean_ctor_set(v_reuseFailAlloc_2190_, 5, v_cache_2171_);
lean_ctor_set(v_reuseFailAlloc_2190_, 6, v_recordedDeps_2172_);
lean_ctor_set(v_reuseFailAlloc_2190_, 7, v_messages_2173_);
lean_ctor_set(v_reuseFailAlloc_2190_, 8, v_infoState_2174_);
lean_ctor_set(v_reuseFailAlloc_2190_, 9, v_snapshotTasks_2175_);
v___x_2187_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = lean_st_ref_put(v___y_2160_, v___x_2187_);
v___x_2189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2189_, 0, v_traces_2164_);
return v___x_2189_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg___boxed(lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg(v___y_2195_);
lean_dec(v___y_2195_);
return v_res_2197_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2198_ = lean_box(0);
v___x_2199_ = lean_unsigned_to_nat(16u);
v___x_2200_ = lean_mk_array(v___x_2199_, v___x_2198_);
return v___x_2200_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1(void){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v_pos2traces_2203_; 
v___x_2201_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0, &l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__0);
v___x_2202_ = lean_unsigned_to_nat(0u);
v_pos2traces_2203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_2203_, 0, v___x_2202_);
lean_ctor_set(v_pos2traces_2203_, 1, v___x_2201_);
return v_pos2traces_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9(lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v_toCold_2210_; lean_object* v_options_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v_toCold_2210_ = lean_ctor_get(v___y_2204_, 0);
v_options_2211_ = lean_ctor_get(v_toCold_2210_, 2);
v___x_2212_ = l_Lean_trace_profiler_output;
v___x_2213_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__14(v_options_2211_, v___x_2212_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v___x_2214_; uint8_t v___x_2215_; 
v___x_2214_ = l_Lean_trace_profiler_serve;
v___x_2215_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_lintComputable_spec__2_spec__3_spec__4_spec__5(v_options_2211_, v___x_2214_);
if (v___x_2215_ == 0)
{
lean_object* v___x_2216_; lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2279_; 
v___x_2216_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg(v___y_2205_);
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2219_ = v___x_2216_;
v_isShared_2220_ = v_isSharedCheck_2279_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2216_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2279_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
uint8_t v___x_2221_; 
v___x_2221_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_2217_);
if (v___x_2221_ == 0)
{
lean_object* v___x_2222_; lean_object* v_pos2traces_2223_; lean_object* v___x_2224_; 
lean_del_object(v___x_2219_);
v___x_2222_ = lean_unsigned_to_nat(0u);
v_pos2traces_2223_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1, &l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__9___closed__1);
v___x_2224_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18(v___x_2221_, v_a_2217_, v_pos2traces_2223_, v___y_2204_, v___y_2205_);
lean_dec(v_a_2217_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; lean_object* v___y_2227_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2253_; lean_object* v_size_2259_; lean_object* v_buckets_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; uint8_t v___x_2263_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2225_);
lean_dec_ref_known(v___x_2224_, 1);
v_size_2259_ = lean_ctor_get(v_a_2225_, 0);
lean_inc(v_size_2259_);
v_buckets_2260_ = lean_ctor_get(v_a_2225_, 1);
lean_inc_ref(v_buckets_2260_);
lean_dec(v_a_2225_);
v___x_2261_ = lean_mk_empty_array_with_capacity(v_size_2259_);
lean_dec(v_size_2259_);
v___x_2262_ = lean_array_get_size(v_buckets_2260_);
v___x_2263_ = lean_nat_dec_lt(v___x_2222_, v___x_2262_);
if (v___x_2263_ == 0)
{
lean_dec_ref(v_buckets_2260_);
v___y_2253_ = v___x_2261_;
goto v___jp_2252_;
}
else
{
size_t v___x_2264_; size_t v___x_2265_; lean_object* v___x_2266_; 
v___x_2264_ = ((size_t)0ULL);
v___x_2265_ = lean_usize_of_nat(v___x_2262_);
v___x_2266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__22(v_buckets_2260_, v___x_2264_, v___x_2265_, v___x_2261_);
lean_dec_ref(v_buckets_2260_);
v___y_2253_ = v___x_2266_;
goto v___jp_2252_;
}
v___jp_2226_:
{
lean_object* v___x_2228_; size_t v_sz_2229_; size_t v___x_2230_; lean_object* v___x_2231_; 
v___x_2228_ = lean_box(0);
v_sz_2229_ = lean_array_size(v___y_2227_);
v___x_2230_ = ((size_t)0ULL);
v___x_2231_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__19(v___x_2215_, v___y_2227_, v_sz_2229_, v___x_2230_, v___x_2228_, v___y_2204_, v___y_2205_);
lean_dec_ref(v___y_2227_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2238_ == 0)
{
lean_object* v_unused_2239_; 
v_unused_2239_ = lean_ctor_get(v___x_2231_, 0);
lean_dec(v_unused_2239_);
v___x_2233_ = v___x_2231_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_dec(v___x_2231_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 0, v___x_2228_);
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2228_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
else
{
return v___x_2231_;
}
}
v___jp_2240_:
{
lean_object* v___x_2245_; 
v___x_2245_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___redArg(v___y_2241_, v___y_2243_, v___y_2242_, v___y_2244_);
lean_dec(v___y_2244_);
lean_dec(v___y_2241_);
v___y_2227_ = v___x_2245_;
goto v___jp_2226_;
}
v___jp_2246_:
{
uint8_t v___x_2251_; 
v___x_2251_ = lean_nat_dec_le(v___y_2250_, v___y_2248_);
if (v___x_2251_ == 0)
{
lean_dec(v___y_2248_);
lean_inc(v___y_2250_);
v___y_2241_ = v___y_2247_;
v___y_2242_ = v___y_2250_;
v___y_2243_ = v___y_2249_;
v___y_2244_ = v___y_2250_;
goto v___jp_2240_;
}
else
{
v___y_2241_ = v___y_2247_;
v___y_2242_ = v___y_2250_;
v___y_2243_ = v___y_2249_;
v___y_2244_ = v___y_2248_;
goto v___jp_2240_;
}
}
v___jp_2252_:
{
lean_object* v___x_2254_; uint8_t v___x_2255_; 
v___x_2254_ = lean_array_get_size(v___y_2253_);
v___x_2255_ = lean_nat_dec_eq(v___x_2254_, v___x_2222_);
if (v___x_2255_ == 0)
{
lean_object* v___x_2256_; lean_object* v___x_2257_; uint8_t v___x_2258_; 
v___x_2256_ = lean_unsigned_to_nat(1u);
v___x_2257_ = lean_nat_sub(v___x_2254_, v___x_2256_);
v___x_2258_ = lean_nat_dec_le(v___x_2222_, v___x_2257_);
if (v___x_2258_ == 0)
{
lean_inc(v___x_2257_);
v___y_2247_ = v___x_2254_;
v___y_2248_ = v___x_2257_;
v___y_2249_ = v___y_2253_;
v___y_2250_ = v___x_2257_;
goto v___jp_2246_;
}
else
{
v___y_2247_ = v___x_2254_;
v___y_2248_ = v___x_2257_;
v___y_2249_ = v___y_2253_;
v___y_2250_ = v___x_2222_;
goto v___jp_2246_;
}
}
else
{
v___y_2227_ = v___y_2253_;
goto v___jp_2226_;
}
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
v_a_2267_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2224_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2224_);
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
else
{
lean_object* v___x_2275_; lean_object* v___x_2277_; 
lean_dec(v_a_2217_);
v___x_2275_ = lean_box(0);
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 0, v___x_2275_);
v___x_2277_ = v___x_2219_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v___x_2275_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
else
{
goto v___jp_2207_;
}
}
else
{
lean_dec_ref_known(v___x_2213_, 1);
goto v___jp_2207_;
}
v___jp_2207_:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = lean_box(0);
v___x_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
return v___x_2209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__9___boxed(lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(lean_object* v_as_2284_, size_t v_sz_2285_, size_t v_i_2286_, lean_object* v_b_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
uint8_t v___x_2291_; 
v___x_2291_ = lean_usize_dec_lt(v_i_2286_, v_sz_2285_);
if (v___x_2291_ == 0)
{
lean_object* v___x_2292_; 
v___x_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2292_, 0, v_b_2287_);
return v___x_2292_;
}
else
{
lean_object* v___x_2293_; lean_object* v_a_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2293_ = lean_box(0);
v_a_2294_ = lean_array_uget_borrowed(v_as_2284_, v_i_2286_);
v___x_2295_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2288_);
lean_inc(v_a_2294_);
v___x_2296_ = l_Lean_Compiler_LCNF_resumeCompilation(v_a_2294_, v___x_2295_, v___y_2288_, v___y_2289_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v___x_2297_; 
lean_dec_ref_known(v___x_2296_, 1);
v___x_2297_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2288_, v___y_2289_);
if (lean_obj_tag(v___x_2297_) == 0)
{
size_t v___x_2298_; size_t v___x_2299_; 
lean_dec_ref_known(v___x_2297_, 1);
v___x_2298_ = ((size_t)1ULL);
v___x_2299_ = lean_usize_add(v_i_2286_, v___x_2298_);
v_i_2286_ = v___x_2299_;
v_b_2287_ = v___x_2293_;
goto _start;
}
else
{
return v___x_2297_;
}
}
else
{
lean_object* v_a_2301_; lean_object* v___x_2302_; 
v_a_2301_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_a_2301_);
lean_dec_ref_known(v___x_2296_, 1);
v___x_2302_ = l_Lean_addTraceAsMessages___at___00main_spec__9(v___y_2288_, v___y_2289_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2309_ == 0)
{
lean_object* v_unused_2310_; 
v_unused_2310_ = lean_ctor_get(v___x_2302_, 0);
lean_dec(v_unused_2310_);
v___x_2304_ = v___x_2302_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_dec(v___x_2302_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
lean_ctor_set_tag(v___x_2304_, 1);
lean_ctor_set(v___x_2304_, 0, v_a_2301_);
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2301_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
else
{
lean_dec(v_a_2301_);
return v___x_2302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10___boxed(lean_object* v_as_2311_, lean_object* v_sz_2312_, lean_object* v_i_2313_, lean_object* v_b_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
size_t v_sz_boxed_2318_; size_t v_i_boxed_2319_; lean_object* v_res_2320_; 
v_sz_boxed_2318_ = lean_unbox_usize(v_sz_2312_);
lean_dec(v_sz_2312_);
v_i_boxed_2319_ = lean_unbox_usize(v_i_2313_);
lean_dec(v_i_2313_);
v_res_2320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(v_as_2311_, v_sz_boxed_2318_, v_i_boxed_2319_, v_b_2314_, v___y_2315_, v___y_2316_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec_ref(v_as_2311_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__37_spec__50___redArg(lean_object* v_as_2321_, size_t v_sz_2322_, size_t v_i_2323_, lean_object* v_b_2324_, lean_object* v___y_2325_){
_start:
{
uint8_t v___x_2327_; 
v___x_2327_ = lean_usize_dec_lt(v_i_2323_, v_sz_2322_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2328_; 
v___x_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2328_, 0, v_b_2324_);
return v___x_2328_;
}
else
{
uint8_t v___x_2329_; lean_object* v_a_2330_; lean_object* v___x_2331_; lean_object* v_ref_2332_; lean_object* v___x_2333_; 
lean_dec_ref(v_b_2324_);
v___x_2329_ = 0;
v_a_2330_ = lean_array_uget_borrowed(v_as_2321_, v_i_2323_);
lean_inc(v_a_2330_);
v___x_2331_ = l_Lean_Message_toString(v_a_2330_, v___x_2329_);
v_ref_2332_ = lean_ctor_get(v___y_2325_, 2);
v___x_2333_ = l_IO_eprintln___at___00main_spec__6(v___x_2331_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v___x_2334_; size_t v___x_2335_; size_t v___x_2336_; 
lean_dec_ref_known(v___x_2333_, 1);
v___x_2334_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__26___closed__0));
v___x_2335_ = ((size_t)1ULL);
v___x_2336_ = lean_usize_add(v_i_2323_, v___x_2335_);
v_i_2323_ = v___x_2336_;
v_b_2324_ = v___x_2334_;
goto _start;
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2349_; 
v_a_2338_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2340_ = v___x_2333_;
v_isShared_2341_ = v_isSharedCheck_2349_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2333_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2349_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2347_; 
v___x_2342_ = lean_io_error_to_string(v_a_2338_);
v___x_2343_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
v___x_2344_ = l_Lean_MessageData_ofFormat(v___x_2343_);
lean_inc(v_ref_2332_);
v___x_2345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2345_, 0, v_ref_2332_);
lean_ctor_set(v___x_2345_, 1, v___x_2344_);
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 0, v___x_2345_);
v___x_2347_ = v___x_2340_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__37_spec__50___redArg___boxed(lean_object* v_as_2350_, lean_object* v_sz_2351_, lean_object* v_i_2352_, lean_object* v_b_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
size_t v_sz_boxed_2356_; size_t v_i_boxed_2357_; lean_object* v_res_2358_; 
v_sz_boxed_2356_ = lean_unbox_usize(v_sz_2351_);
lean_dec(v_sz_2351_);
v_i_boxed_2357_ = lean_unbox_usize(v_i_2352_);
lean_dec(v_i_2352_);
v_res_2358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__37_spec__50___redArg(v_as_2350_, v_sz_boxed_2356_, v_i_boxed_2357_, v_b_2353_, v___y_2354_);
lean_dec_ref(v___y_2354_);
lean_dec_ref(v_as_2350_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__37(lean_object* v_as_2359_, size_t v_sz_2360_, size_t v_i_2361_, lean_object* v_b_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
uint8_t v___x_2366_; 
v___x_2366_ = lean_usize_dec_lt(v_i_2361_, v_sz_2360_);
if (v___x_2366_ == 0)
{
lean_object* v___x_2367_; 
v___x_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2367_, 0, v_b_2362_);
return v___x_2367_;
}
else
{
uint8_t v___x_2368_; lean_object* v_a_2369_; lean_object* v___x_2370_; lean_object* v_ref_2371_; lean_object* v___x_2372_; 
lean_dec_ref(v_b_2362_);
v___x_2368_ = 0;
v_a_2369_ = lean_array_uget_borrowed(v_as_2359_, v_i_2361_);
lean_inc(v_a_2369_);
v___x_2370_ = l_Lean_Message_toString(v_a_2369_, v___x_2368_);
v_ref_2371_ = lean_ctor_get(v___y_2363_, 2);
v___x_2372_ = l_IO_eprintln___at___00main_spec__6(v___x_2370_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v___x_2373_; size_t v___x_2374_; size_t v___x_2375_; lean_object* v___x_2376_; 
lean_dec_ref_known(v___x_2372_, 1);
v___x_2373_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13_spec__26___closed__0));
v___x_2374_ = ((size_t)1ULL);
v___x_2375_ = lean_usize_add(v_i_2361_, v___x_2374_);
v___x_2376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__37_spec__50___redArg(v_as_2359_, v_sz_2360_, v___x_2375_, v___x_2373_, v___y_2363_);
return v___x_2376_;
}
else
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2388_; 
v_a_2377_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2379_ = v___x_2372_;
v_isShared_2380_ = v_isSharedCheck_2388_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2372_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2388_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2386_; 
v___x_2381_ = lean_io_error_to_string(v_a_2377_);
v___x_2382_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2381_);
v___x_2383_ = l_Lean_MessageData_ofFormat(v___x_2382_);
lean_inc(v_ref_2371_);
v___x_2384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2384_, 0, v_ref_2371_);
lean_ctor_set(v___x_2384_, 1, v___x_2383_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v___x_2384_);
v___x_2386_ = v___x_2379_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2384_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__37___boxed(lean_object* v_as_2389_, lean_object* v_sz_2390_, lean_object* v_i_2391_, lean_object* v_b_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
size_t v_sz_boxed_2396_; size_t v_i_boxed_2397_; lean_object* v_res_2398_; 
v_sz_boxed_2396_ = lean_unbox_usize(v_sz_2390_);
lean_dec(v_sz_2390_);
v_i_boxed_2397_ = lean_unbox_usize(v_i_2391_);
lean_dec(v_i_2391_);
v_res_2398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__37(v_as_2389_, v_sz_boxed_2396_, v_i_boxed_2397_, v_b_2392_, v___y_2393_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec_ref(v_as_2389_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25(lean_object* v_init_2399_, lean_object* v_n_2400_, lean_object* v_b_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
if (lean_obj_tag(v_n_2400_) == 0)
{
lean_object* v_cs_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; size_t v_sz_2408_; size_t v___x_2409_; lean_object* v___x_2410_; 
v_cs_2405_ = lean_ctor_get(v_n_2400_, 0);
v___x_2406_ = lean_box(0);
v___x_2407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
lean_ctor_set(v___x_2407_, 1, v_b_2401_);
v_sz_2408_ = lean_array_size(v_cs_2405_);
v___x_2409_ = ((size_t)0ULL);
v___x_2410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__36(v_init_2399_, v_cs_2405_, v_sz_2408_, v___x_2409_, v___x_2407_, v___y_2402_, v___y_2403_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2425_; 
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2413_ = v___x_2410_;
v_isShared_2414_ = v_isSharedCheck_2425_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2410_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2425_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v_fst_2415_; 
v_fst_2415_ = lean_ctor_get(v_a_2411_, 0);
if (lean_obj_tag(v_fst_2415_) == 0)
{
lean_object* v_snd_2416_; lean_object* v___x_2417_; lean_object* v___x_2419_; 
v_snd_2416_ = lean_ctor_get(v_a_2411_, 1);
lean_inc(v_snd_2416_);
lean_dec(v_a_2411_);
v___x_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2417_, 0, v_snd_2416_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 0, v___x_2417_);
v___x_2419_ = v___x_2413_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2417_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
else
{
lean_object* v_val_2421_; lean_object* v___x_2423_; 
lean_inc_ref(v_fst_2415_);
lean_dec(v_a_2411_);
v_val_2421_ = lean_ctor_get(v_fst_2415_, 0);
lean_inc(v_val_2421_);
lean_dec_ref_known(v_fst_2415_, 1);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 0, v_val_2421_);
v___x_2423_ = v___x_2413_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_val_2421_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
v_a_2426_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2410_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2410_);
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
lean_object* v_vs_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; size_t v_sz_2437_; size_t v___x_2438_; lean_object* v___x_2439_; 
v_vs_2434_ = lean_ctor_get(v_n_2400_, 0);
v___x_2435_ = lean_box(0);
v___x_2436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
lean_ctor_set(v___x_2436_, 1, v_b_2401_);
v_sz_2437_ = lean_array_size(v_vs_2434_);
v___x_2438_ = ((size_t)0ULL);
v___x_2439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__37(v_vs_2434_, v_sz_2437_, v___x_2438_, v___x_2436_, v___y_2402_, v___y_2403_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2454_; 
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2442_ = v___x_2439_;
v_isShared_2443_ = v_isSharedCheck_2454_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2439_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2454_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v_fst_2444_; 
v_fst_2444_ = lean_ctor_get(v_a_2440_, 0);
if (lean_obj_tag(v_fst_2444_) == 0)
{
lean_object* v_snd_2445_; lean_object* v___x_2446_; lean_object* v___x_2448_; 
v_snd_2445_ = lean_ctor_get(v_a_2440_, 1);
lean_inc(v_snd_2445_);
lean_dec(v_a_2440_);
v___x_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2446_, 0, v_snd_2445_);
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 0, v___x_2446_);
v___x_2448_ = v___x_2442_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2446_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
else
{
lean_object* v_val_2450_; lean_object* v___x_2452_; 
lean_inc_ref(v_fst_2444_);
lean_dec(v_a_2440_);
v_val_2450_ = lean_ctor_get(v_fst_2444_, 0);
lean_inc(v_val_2450_);
lean_dec_ref_known(v_fst_2444_, 1);
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 0, v_val_2450_);
v___x_2452_ = v___x_2442_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_val_2450_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
else
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
v_a_2455_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2457_ = v___x_2439_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2439_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2455_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__36(lean_object* v_init_2463_, lean_object* v_as_2464_, size_t v_sz_2465_, size_t v_i_2466_, lean_object* v_b_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
uint8_t v___x_2471_; 
v___x_2471_ = lean_usize_dec_lt(v_i_2466_, v_sz_2465_);
if (v___x_2471_ == 0)
{
lean_object* v___x_2472_; 
v___x_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2472_, 0, v_b_2467_);
return v___x_2472_;
}
else
{
lean_object* v_snd_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2507_; 
v_snd_2473_ = lean_ctor_get(v_b_2467_, 1);
v_isSharedCheck_2507_ = !lean_is_exclusive(v_b_2467_);
if (v_isSharedCheck_2507_ == 0)
{
lean_object* v_unused_2508_; 
v_unused_2508_ = lean_ctor_get(v_b_2467_, 0);
lean_dec(v_unused_2508_);
v___x_2475_ = v_b_2467_;
v_isShared_2476_ = v_isSharedCheck_2507_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_snd_2473_);
lean_dec(v_b_2467_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2507_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2477_; lean_object* v_a_2478_; lean_object* v___x_2479_; 
v___x_2477_ = lean_box(0);
v_a_2478_ = lean_array_uget_borrowed(v_as_2464_, v_i_2466_);
lean_inc(v_snd_2473_);
v___x_2479_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25(v_init_2463_, v_a_2478_, v_snd_2473_, v___y_2468_, v___y_2469_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2498_; 
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2482_ = v___x_2479_;
v_isShared_2483_ = v_isSharedCheck_2498_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2479_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2498_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
if (lean_obj_tag(v_a_2480_) == 0)
{
lean_object* v___x_2484_; lean_object* v___x_2486_; 
v___x_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2484_, 0, v_a_2480_);
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 0, v___x_2484_);
v___x_2486_ = v___x_2475_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2484_);
lean_ctor_set(v_reuseFailAlloc_2490_, 1, v_snd_2473_);
v___x_2486_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
lean_object* v___x_2488_; 
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 0, v___x_2486_);
v___x_2488_ = v___x_2482_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2486_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; 
lean_del_object(v___x_2482_);
lean_dec(v_snd_2473_);
v_a_2491_ = lean_ctor_get(v_a_2480_, 0);
lean_inc(v_a_2491_);
lean_dec_ref_known(v_a_2480_, 1);
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 1, v_a_2491_);
lean_ctor_set(v___x_2475_, 0, v___x_2477_);
v___x_2493_ = v___x_2475_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v___x_2477_);
lean_ctor_set(v_reuseFailAlloc_2497_, 1, v_a_2491_);
v___x_2493_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
size_t v___x_2494_; size_t v___x_2495_; 
v___x_2494_ = ((size_t)1ULL);
v___x_2495_ = lean_usize_add(v_i_2466_, v___x_2494_);
v_i_2466_ = v___x_2495_;
v_b_2467_ = v___x_2493_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
lean_del_object(v___x_2475_);
lean_dec(v_snd_2473_);
v_a_2499_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2479_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2479_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2499_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__36___boxed(lean_object* v_init_2509_, lean_object* v_as_2510_, lean_object* v_sz_2511_, lean_object* v_i_2512_, lean_object* v_b_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
size_t v_sz_boxed_2517_; size_t v_i_boxed_2518_; lean_object* v_res_2519_; 
v_sz_boxed_2517_ = lean_unbox_usize(v_sz_2511_);
lean_dec(v_sz_2511_);
v_i_boxed_2518_ = lean_unbox_usize(v_i_2512_);
lean_dec(v_i_2512_);
v_res_2519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__36(v_init_2509_, v_as_2510_, v_sz_boxed_2517_, v_i_boxed_2518_, v_b_2513_, v___y_2514_, v___y_2515_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec_ref(v_as_2510_);
return v_res_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25___boxed(lean_object* v_init_2520_, lean_object* v_n_2521_, lean_object* v_b_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25(v_init_2520_, v_n_2521_, v_b_2522_, v___y_2523_, v___y_2524_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec_ref(v_n_2521_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__39___redArg(lean_object* v_as_2527_, size_t v_sz_2528_, size_t v_i_2529_, lean_object* v_b_2530_, lean_object* v___y_2531_){
_start:
{
uint8_t v___x_2533_; 
v___x_2533_ = lean_usize_dec_lt(v_i_2529_, v_sz_2528_);
if (v___x_2533_ == 0)
{
lean_object* v___x_2534_; 
v___x_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2534_, 0, v_b_2530_);
return v___x_2534_;
}
else
{
uint8_t v___x_2535_; lean_object* v_a_2536_; lean_object* v___x_2537_; lean_object* v_ref_2538_; lean_object* v___x_2539_; 
lean_dec_ref(v_b_2530_);
v___x_2535_ = 0;
v_a_2536_ = lean_array_uget_borrowed(v_as_2527_, v_i_2529_);
lean_inc(v_a_2536_);
v___x_2537_ = l_Lean_Message_toString(v_a_2536_, v___x_2535_);
v_ref_2538_ = lean_ctor_get(v___y_2531_, 2);
v___x_2539_ = l_IO_eprintln___at___00main_spec__6(v___x_2537_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v___x_2540_; size_t v___x_2541_; size_t v___x_2542_; 
lean_dec_ref_known(v___x_2539_, 1);
v___x_2540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_2541_ = ((size_t)1ULL);
v___x_2542_ = lean_usize_add(v_i_2529_, v___x_2541_);
v_i_2529_ = v___x_2542_;
v_b_2530_ = v___x_2540_;
goto _start;
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2555_; 
v_a_2544_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2546_ = v___x_2539_;
v_isShared_2547_ = v_isSharedCheck_2555_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2539_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2555_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2553_; 
v___x_2548_ = lean_io_error_to_string(v_a_2544_);
v___x_2549_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2548_);
v___x_2550_ = l_Lean_MessageData_ofFormat(v___x_2549_);
lean_inc(v_ref_2538_);
v___x_2551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2551_, 0, v_ref_2538_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 0, v___x_2551_);
v___x_2553_ = v___x_2546_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2551_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__39___redArg___boxed(lean_object* v_as_2556_, lean_object* v_sz_2557_, lean_object* v_i_2558_, lean_object* v_b_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
size_t v_sz_boxed_2562_; size_t v_i_boxed_2563_; lean_object* v_res_2564_; 
v_sz_boxed_2562_ = lean_unbox_usize(v_sz_2557_);
lean_dec(v_sz_2557_);
v_i_boxed_2563_ = lean_unbox_usize(v_i_2558_);
lean_dec(v_i_2558_);
v_res_2564_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__39___redArg(v_as_2556_, v_sz_boxed_2562_, v_i_boxed_2563_, v_b_2559_, v___y_2560_);
lean_dec_ref(v___y_2560_);
lean_dec_ref(v_as_2556_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(lean_object* v_as_2565_, size_t v_sz_2566_, size_t v_i_2567_, lean_object* v_b_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
uint8_t v___x_2572_; 
v___x_2572_ = lean_usize_dec_lt(v_i_2567_, v_sz_2566_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; 
v___x_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2573_, 0, v_b_2568_);
return v___x_2573_;
}
else
{
uint8_t v___x_2574_; lean_object* v_a_2575_; lean_object* v___x_2576_; lean_object* v_ref_2577_; lean_object* v___x_2578_; 
lean_dec_ref(v_b_2568_);
v___x_2574_ = 0;
v_a_2575_ = lean_array_uget_borrowed(v_as_2565_, v_i_2567_);
lean_inc(v_a_2575_);
v___x_2576_ = l_Lean_Message_toString(v_a_2575_, v___x_2574_);
v_ref_2577_ = lean_ctor_get(v___y_2569_, 2);
v___x_2578_ = l_IO_eprintln___at___00main_spec__6(v___x_2576_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v___x_2579_; size_t v___x_2580_; size_t v___x_2581_; lean_object* v___x_2582_; 
lean_dec_ref_known(v___x_2578_, 1);
v___x_2579_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__15___closed__0));
v___x_2580_ = ((size_t)1ULL);
v___x_2581_ = lean_usize_add(v_i_2567_, v___x_2580_);
v___x_2582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__39___redArg(v_as_2565_, v_sz_2566_, v___x_2581_, v___x_2579_, v___y_2569_);
return v___x_2582_;
}
else
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2594_; 
v_a_2583_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2585_ = v___x_2578_;
v_isShared_2586_ = v_isSharedCheck_2594_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2578_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2594_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2592_; 
v___x_2587_ = lean_io_error_to_string(v_a_2583_);
v___x_2588_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
v___x_2589_ = l_Lean_MessageData_ofFormat(v___x_2588_);
lean_inc(v_ref_2577_);
v___x_2590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2590_, 0, v_ref_2577_);
lean_ctor_set(v___x_2590_, 1, v___x_2589_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v___x_2590_);
v___x_2592_ = v___x_2585_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v___x_2590_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26___boxed(lean_object* v_as_2595_, lean_object* v_sz_2596_, lean_object* v_i_2597_, lean_object* v_b_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
size_t v_sz_boxed_2602_; size_t v_i_boxed_2603_; lean_object* v_res_2604_; 
v_sz_boxed_2602_ = lean_unbox_usize(v_sz_2596_);
lean_dec(v_sz_2596_);
v_i_boxed_2603_ = lean_unbox_usize(v_i_2597_);
lean_dec(v_i_2597_);
v_res_2604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(v_as_2595_, v_sz_boxed_2602_, v_i_boxed_2603_, v_b_2598_, v___y_2599_, v___y_2600_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec_ref(v_as_2595_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__11(lean_object* v_t_2605_, lean_object* v_init_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v_root_2610_; lean_object* v_tail_2611_; lean_object* v___x_2612_; 
v_root_2610_ = lean_ctor_get(v_t_2605_, 0);
v_tail_2611_ = lean_ctor_get(v_t_2605_, 1);
v___x_2612_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25(v_init_2606_, v_root_2610_, v_init_2606_, v___y_2607_, v___y_2608_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2649_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2615_ = v___x_2612_;
v_isShared_2616_ = v_isSharedCheck_2649_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2612_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2649_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
if (lean_obj_tag(v_a_2613_) == 0)
{
lean_object* v_a_2617_; lean_object* v___x_2619_; 
v_a_2617_ = lean_ctor_get(v_a_2613_, 0);
lean_inc(v_a_2617_);
lean_dec_ref_known(v_a_2613_, 1);
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v_a_2617_);
v___x_2619_ = v___x_2615_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2617_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; size_t v_sz_2624_; size_t v___x_2625_; lean_object* v___x_2626_; 
lean_del_object(v___x_2615_);
v_a_2621_ = lean_ctor_get(v_a_2613_, 0);
lean_inc(v_a_2621_);
lean_dec_ref_known(v_a_2613_, 1);
v___x_2622_ = lean_box(0);
v___x_2623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
lean_ctor_set(v___x_2623_, 1, v_a_2621_);
v_sz_2624_ = lean_array_size(v_tail_2611_);
v___x_2625_ = ((size_t)0ULL);
v___x_2626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26(v_tail_2611_, v_sz_2624_, v___x_2625_, v___x_2623_, v___y_2607_, v___y_2608_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2640_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2629_ = v___x_2626_;
v_isShared_2630_ = v_isSharedCheck_2640_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2626_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2640_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v_fst_2631_; 
v_fst_2631_ = lean_ctor_get(v_a_2627_, 0);
if (lean_obj_tag(v_fst_2631_) == 0)
{
lean_object* v_snd_2632_; lean_object* v___x_2634_; 
v_snd_2632_ = lean_ctor_get(v_a_2627_, 1);
lean_inc(v_snd_2632_);
lean_dec(v_a_2627_);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v_snd_2632_);
v___x_2634_ = v___x_2629_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_snd_2632_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
else
{
lean_object* v_val_2636_; lean_object* v___x_2638_; 
lean_inc_ref(v_fst_2631_);
lean_dec(v_a_2627_);
v_val_2636_ = lean_ctor_get(v_fst_2631_, 0);
lean_inc(v_val_2636_);
lean_dec_ref_known(v_fst_2631_, 1);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v_val_2636_);
v___x_2638_ = v___x_2629_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_val_2636_);
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
else
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
v_a_2641_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2626_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2626_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
}
}
else
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
v_a_2650_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2612_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2612_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__11___boxed(lean_object* v_t_2658_, lean_object* v_init_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l_Lean_PersistentArray_forIn___at___00main_spec__11(v_t_2658_, v_init_2659_, v___y_2660_, v___y_2661_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec_ref(v_t_2658_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(lean_object* v_as_2664_, size_t v_sz_2665_, size_t v_i_2666_, lean_object* v_b_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
uint8_t v___x_2671_; 
v___x_2671_ = lean_usize_dec_lt(v_i_2666_, v_sz_2665_);
if (v___x_2671_ == 0)
{
lean_object* v___x_2672_; 
v___x_2672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2672_, 0, v_b_2667_);
return v___x_2672_;
}
else
{
lean_object* v_a_2673_; lean_object* v_declNames_2674_; lean_object* v___x_2675_; size_t v_sz_2676_; size_t v___x_2677_; lean_object* v___x_2678_; 
v_a_2673_ = lean_array_uget_borrowed(v_as_2664_, v_i_2666_);
v_declNames_2674_ = lean_ctor_get(v_a_2673_, 0);
v___x_2675_ = lean_box(0);
v_sz_2676_ = lean_array_size(v_declNames_2674_);
v___x_2677_ = ((size_t)0ULL);
v___x_2678_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__10(v_declNames_2674_, v_sz_2676_, v___x_2677_, v___x_2675_, v___y_2668_, v___y_2669_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v___x_2679_; 
lean_dec_ref_known(v___x_2678_, 1);
v___x_2679_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v___y_2669_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; lean_object* v_unreported_2681_; lean_object* v___x_2682_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v___x_2679_, 1);
v_unreported_2681_ = lean_ctor_get(v_a_2680_, 1);
lean_inc_ref(v_unreported_2681_);
lean_dec(v_a_2680_);
v___x_2682_ = l_Lean_PersistentArray_forIn___at___00main_spec__11(v_unreported_2681_, v___x_2675_, v___y_2668_, v___y_2669_);
lean_dec_ref(v_unreported_2681_);
if (lean_obj_tag(v___x_2682_) == 0)
{
size_t v___x_2683_; size_t v___x_2684_; 
lean_dec_ref_known(v___x_2682_, 1);
v___x_2683_ = ((size_t)1ULL);
v___x_2684_ = lean_usize_add(v_i_2666_, v___x_2683_);
v_i_2666_ = v___x_2684_;
v_b_2667_ = v___x_2675_;
goto _start;
}
else
{
return v___x_2682_;
}
}
else
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
v_a_2686_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2679_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2679_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
else
{
return v___x_2678_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___boxed(lean_object* v_as_2694_, lean_object* v_sz_2695_, lean_object* v_i_2696_, lean_object* v_b_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
size_t v_sz_boxed_2701_; size_t v_i_boxed_2702_; lean_object* v_res_2703_; 
v_sz_boxed_2701_ = lean_unbox_usize(v_sz_2695_);
lean_dec(v_sz_2695_);
v_i_boxed_2702_ = lean_unbox_usize(v_i_2696_);
lean_dec(v_i_2696_);
v_res_2703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(v_as_2694_, v_sz_boxed_2701_, v_i_boxed_2702_, v_b_2697_, v___y_2698_, v___y_2699_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec_ref(v_as_2694_);
return v_res_2703_;
}
}
static lean_object* _init_l_main___closed__1(void){
_start:
{
lean_object* v___x_2705_; 
v___x_2705_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___redArg();
return v___x_2705_;
}
}
static lean_object* _init_l_main___closed__2(void){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2706_ = l_Lean_instInhabitedClassState_default;
v___x_2707_ = lean_box(0);
v___x_2708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
lean_ctor_set(v___x_2708_, 1, v___x_2706_);
return v___x_2708_;
}
}
static lean_object* _init_l_main___closed__3(void){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2709_ = l_Lean_Meta_Match_Extension_instInhabitedState;
v___x_2710_ = lean_box(0);
v___x_2711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2710_);
lean_ctor_set(v___x_2711_, 1, v___x_2709_);
return v___x_2711_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_2712_; 
v___x_2712_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_2712_;
}
}
static lean_object* _init_l_main___closed__5(void){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2713_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2714_ = lean_box(0);
v___x_2715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2714_);
lean_ctor_set(v___x_2715_, 1, v___x_2713_);
return v___x_2715_;
}
}
static lean_object* _init_l_main___closed__6(void){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2716_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_2717_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2716_);
return v___x_2717_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l_Array_instInhabited___redArg();
return v___x_2718_;
}
}
static lean_object* _init_l_main___closed__17(void){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2731_ = ((lean_object*)(l_main___closed__16));
v___x_2732_ = lean_unsigned_to_nat(27u);
v___x_2733_ = lean_unsigned_to_nat(160u);
v___x_2734_ = ((lean_object*)(l_main___closed__15));
v___x_2735_ = ((lean_object*)(l_main___closed__14));
v___x_2736_ = l_mkPanicMessageWithDecl(v___x_2735_, v___x_2734_, v___x_2733_, v___x_2732_, v___x_2731_);
return v___x_2736_;
}
}
static lean_object* _init_l_main___closed__19(void){
_start:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2738_ = ((lean_object*)(l_main___closed__16));
v___x_2739_ = lean_unsigned_to_nat(51u);
v___x_2740_ = lean_unsigned_to_nat(133u);
v___x_2741_ = ((lean_object*)(l_main___closed__15));
v___x_2742_ = ((lean_object*)(l_main___closed__14));
v___x_2743_ = l_mkPanicMessageWithDecl(v___x_2742_, v___x_2741_, v___x_2740_, v___x_2739_, v___x_2738_);
return v___x_2743_;
}
}
static lean_object* _init_l_main___closed__20(void){
_start:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2744_ = lean_unsigned_to_nat(1u);
v___x_2745_ = l_Lean_firstFrontendMacroScope;
v___x_2746_ = lean_nat_add(v___x_2745_, v___x_2744_);
return v___x_2746_;
}
}
static lean_object* _init_l_main___closed__24(void){
_start:
{
lean_object* v___x_2753_; uint64_t v___x_2754_; lean_object* v___x_2755_; 
v___x_2753_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg___closed__1);
v___x_2754_ = 0ULL;
v___x_2755_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2755_, 0, v___x_2753_);
lean_ctor_set_uint64(v___x_2755_, sizeof(void*)*1, v___x_2754_);
return v___x_2755_;
}
}
static lean_object* _init_l_main___closed__25(void){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2756_;
}
}
static lean_object* _init_l_main___closed__26(void){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2757_ = lean_obj_once(&l_main___closed__25, &l_main___closed__25_once, _init_l_main___closed__25);
v___x_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2757_);
return v___x_2758_;
}
}
static lean_object* _init_l_main___closed__27(void){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = lean_obj_once(&l_main___closed__26, &l_main___closed__26_once, _init_l_main___closed__26);
v___x_2760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2759_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
return v___x_2760_;
}
}
static lean_object* _init_l_main___closed__29(void){
_start:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2763_ = lean_unsigned_to_nat(0u);
v___x_2764_ = l_Lean_Options_empty;
v___x_2765_ = ((lean_object*)(l_main___closed__28));
v___x_2766_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2765_);
lean_ctor_set(v___x_2766_, 1, v___x_2764_);
lean_ctor_set(v___x_2766_, 2, v___x_2765_);
lean_ctor_set(v___x_2766_, 3, v___x_2763_);
lean_ctor_set(v___x_2766_, 4, v___x_2763_);
lean_ctor_set(v___x_2766_, 5, v___x_2763_);
lean_ctor_set(v___x_2766_, 6, v___x_2765_);
lean_ctor_set(v___x_2766_, 7, v___x_2765_);
return v___x_2766_;
}
}
static lean_object* _init_l_main___closed__30(void){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2767_ = l_Lean_NameSet_empty;
v___x_2768_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg___closed__1);
v___x_2769_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2768_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
lean_ctor_set(v___x_2769_, 2, v___x_2767_);
return v___x_2769_;
}
}
static lean_object* _init_l_main___closed__31(void){
_start:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; uint8_t v___x_2772_; lean_object* v___x_2773_; 
v___x_2770_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg___closed__1);
v___x_2771_ = lean_obj_once(&l_main___closed__26, &l_main___closed__26_once, _init_l_main___closed__26);
v___x_2772_ = 1;
v___x_2773_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2773_, 0, v___x_2771_);
lean_ctor_set(v___x_2773_, 1, v___x_2771_);
lean_ctor_set(v___x_2773_, 2, v___x_2770_);
lean_ctor_set_uint8(v___x_2773_, sizeof(void*)*3, v___x_2772_);
return v___x_2773_;
}
}
static uint8_t _init_l_main___closed__35(void){
_start:
{
uint8_t v___x_2778_; uint8_t v___x_2779_; uint8_t v___x_2780_; 
v___x_2778_ = 2;
v___x_2779_ = 0;
v___x_2780_ = l_Lean_instOrdOLeanLevel_ord(v___x_2779_, v___x_2778_);
return v___x_2780_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_2781_; lean_object* v___x_2782_; 
v___x_2781_ = 1;
v___x_2782_ = lean_box_uint32(v___x_2781_);
return v___x_2782_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_2783_; lean_object* v___x_2784_; 
v___x_2783_ = 0;
v___x_2784_ = lean_box_uint32(v___x_2783_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_2785_){
_start:
{
if (lean_obj_tag(v_args_2785_) == 1)
{
lean_object* v_tail_2810_; 
v_tail_2810_ = lean_ctor_get(v_args_2785_, 1);
lean_inc(v_tail_2810_);
if (lean_obj_tag(v_tail_2810_) == 1)
{
lean_object* v_tail_2811_; 
v_tail_2811_ = lean_ctor_get(v_tail_2810_, 1);
lean_inc(v_tail_2811_);
if (lean_obj_tag(v_tail_2811_) == 1)
{
lean_object* v_head_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_3500_; 
v_head_2812_ = lean_ctor_get(v_args_2785_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v_args_2785_);
if (v_isSharedCheck_3500_ == 0)
{
lean_object* v_unused_3501_; 
v_unused_3501_ = lean_ctor_get(v_args_2785_, 1);
lean_dec(v_unused_3501_);
v___x_2814_ = v_args_2785_;
v_isShared_2815_ = v_isSharedCheck_3500_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_head_2812_);
lean_dec(v_args_2785_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_3500_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v_head_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_3498_; 
v_head_2816_ = lean_ctor_get(v_tail_2810_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v_tail_2810_);
if (v_isSharedCheck_3498_ == 0)
{
lean_object* v_unused_3499_; 
v_unused_3499_ = lean_ctor_get(v_tail_2810_, 1);
lean_dec(v_unused_3499_);
v___x_2818_ = v_tail_2810_;
v_isShared_2819_ = v_isSharedCheck_3498_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_head_2816_);
lean_dec(v_tail_2810_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_3498_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v_head_2820_; lean_object* v_tail_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_3497_; 
v_head_2820_ = lean_ctor_get(v_tail_2811_, 0);
v_tail_2821_ = lean_ctor_get(v_tail_2811_, 1);
v_isSharedCheck_3497_ = !lean_is_exclusive(v_tail_2811_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_2823_ = v_tail_2811_;
v_isShared_2824_ = v_isSharedCheck_3497_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_tail_2821_);
lean_inc(v_head_2820_);
lean_dec(v_tail_2811_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_3497_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2825_ = lean_obj_once(&l_main___closed__1, &l_main___closed__1_once, _init_l_main___closed__1);
v___x_2826_ = lean_box(0);
v___x_2827_ = lean_obj_once(&l_main___closed__2, &l_main___closed__2_once, _init_l_main___closed__2);
v___x_2828_ = lean_obj_once(&l_main___closed__3, &l_main___closed__3_once, _init_l_main___closed__3);
v___x_2829_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2830_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2831_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_2832_ = lean_box(1);
v___x_2833_ = ((lean_object*)(l_main___closed__8));
v___x_2834_ = l_Lean_ModuleSetup_load(v_head_2812_);
lean_dec(v_head_2812_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; lean_object* v_name_2836_; lean_object* v_package_x3f_2837_; lean_object* v_importArts_2838_; lean_object* v_options_2839_; lean_object* v___f_2840_; uint8_t v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2845_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_a_2835_);
lean_dec_ref_known(v___x_2834_, 1);
v_name_2836_ = lean_ctor_get(v_a_2835_, 0);
lean_inc(v_name_2836_);
v_package_x3f_2837_ = lean_ctor_get(v_a_2835_, 1);
lean_inc(v_package_x3f_2837_);
v_importArts_2838_ = lean_ctor_get(v_a_2835_, 3);
lean_inc(v_importArts_2838_);
v_options_2839_ = lean_ctor_get(v_a_2835_, 6);
lean_inc(v_options_2839_);
lean_dec(v_a_2835_);
v___f_2840_ = lean_alloc_closure((void*)(l_main___lam__0), 2, 1);
lean_closure_set(v___f_2840_, 0, v_package_x3f_2837_);
v___x_2841_ = 0;
v___x_2842_ = l_Lean_LeanOptions_toOptions(v_options_2839_);
v___x_2843_ = lean_box(v___x_2841_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set_tag(v___x_2823_, 0);
lean_ctor_set(v___x_2823_, 1, v___x_2842_);
lean_ctor_set(v___x_2823_, 0, v___x_2843_);
v___x_2845_ = v___x_2823_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_2843_);
lean_ctor_set(v_reuseFailAlloc_3488_, 1, v___x_2842_);
v___x_2845_ = v_reuseFailAlloc_3488_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
lean_object* v___x_2846_; 
v___x_2846_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_tail_2821_, v___x_2845_);
lean_dec(v_tail_2821_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v_fst_2848_; lean_object* v_snd_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_3479_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2846_, 1);
v_fst_2848_ = lean_ctor_get(v_a_2847_, 0);
v_snd_2849_ = lean_ctor_get(v_a_2847_, 1);
v_isSharedCheck_3479_ = !lean_is_exclusive(v_a_2847_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_2851_ = v_a_2847_;
v_isShared_2852_ = v_isSharedCheck_3479_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_snd_2849_);
lean_inc(v_fst_2848_);
lean_dec(v_a_2847_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_3479_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2853_; uint8_t v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; uint8_t v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; uint8_t v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; uint8_t v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; uint8_t v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v_nextMacroScope_3043_; lean_object* v_ngen_3044_; lean_object* v_auxDeclNGen_3045_; lean_object* v_traceState_3046_; lean_object* v_recordedDeps_3047_; lean_object* v_messages_3048_; lean_object* v_infoState_3049_; lean_object* v_snapshotTasks_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; uint8_t v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; uint8_t v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; uint16_t v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v_fileName_3092_; lean_object* v_fileMap_3093_; lean_object* v_currNamespace_3094_; lean_object* v_openDecls_3095_; lean_object* v_initHeartbeats_3096_; lean_object* v_maxHeartbeats_3097_; lean_object* v_quotContext_3098_; lean_object* v_currMacroScope_3099_; lean_object* v_cancelTk_x3f_3100_; lean_object* v_inheritedTraceOptions_3101_; lean_object* v_currRecDepth_3102_; lean_object* v_ref_3103_; uint8_t v_suppressElabErrors_3104_; uint8_t v_checkDeprecated_3105_; uint8_t v_isRecordingDeps_3106_; lean_object* v___y_3107_; uint8_t v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; uint8_t v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; uint8_t v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; uint16_t v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___x_3193_; 
v___x_2853_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_2854_ = 1;
v___x_2855_ = l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(v_snd_2849_, v___x_2853_, v___x_2854_);
v___x_2856_ = l_Lean_maxHeartbeats;
v___x_2857_ = lean_unsigned_to_nat(0u);
v___x_2858_ = l_Lean_Option_set___at___00main_spec__3(v___x_2855_, v___x_2856_, v___x_2857_);
v___x_3193_ = lean_init_search_path();
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; uint8_t v___x_3199_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; uint8_t v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3371_; lean_object* v___y_3372_; uint8_t v___y_3443_; uint8_t v___x_3470_; 
lean_dec_ref_known(v___x_3193_, 1);
v___x_3194_ = ((lean_object*)(l_main___closed__18));
lean_inc(v_name_2836_);
v___x_3195_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3195_, 0, v_name_2836_);
lean_ctor_set_uint8(v___x_3195_, sizeof(void*)*1, v___x_2854_);
lean_ctor_set_uint8(v___x_3195_, sizeof(void*)*1 + 1, v___x_2854_);
lean_ctor_set_uint8(v___x_3195_, sizeof(void*)*1 + 2, v___x_2841_);
v___x_3196_ = lean_unsigned_to_nat(1u);
v___x_3197_ = lean_mk_empty_array_with_capacity(v___x_3196_);
v___x_3198_ = lean_array_push(v___x_3197_, v___x_3195_);
v___x_3199_ = 0;
v___x_3470_ = lean_uint8_once(&l_main___closed__35, &l_main___closed__35_once, _init_l_main___closed__35);
if (v___x_3470_ == 0)
{
v___y_3443_ = v___x_2854_;
goto v___jp_3442_;
}
else
{
v___y_3443_ = v___x_2841_;
goto v___jp_3442_;
}
v___jp_3200_:
{
lean_object* v___x_3205_; lean_object* v_moduleData_3206_; lean_object* v___x_3207_; uint8_t v___x_3208_; 
v___x_3205_ = l_Lean_Environment_header(v___y_3204_);
v_moduleData_3206_ = lean_ctor_get(v___x_3205_, 7);
lean_inc_ref(v_moduleData_3206_);
lean_dec_ref(v___x_3205_);
v___x_3207_ = lean_array_get_size(v_moduleData_3206_);
v___x_3208_ = lean_nat_dec_lt(v___y_3203_, v___x_3207_);
if (v___x_3208_ == 0)
{
lean_object* v___x_3209_; lean_object* v___x_3210_; 
lean_dec_ref(v_moduleData_3206_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v___x_2858_);
lean_del_object(v___x_2851_);
lean_dec(v_fst_2848_);
lean_dec(v_name_2836_);
lean_dec(v_head_2820_);
lean_del_object(v___x_2818_);
lean_dec(v_head_2816_);
v___x_3209_ = lean_obj_once(&l_main___closed__19, &l_main___closed__19_once, _init_l_main___closed__19);
v___x_3210_ = l_panic___at___00main_spec__5(v___x_3209_);
return v___x_3210_;
}
else
{
lean_object* v_base_3211_; lean_object* v_private_3212_; lean_object* v_header_3213_; lean_object* v_serverBaseExts_3214_; lean_object* v_checked_3215_; lean_object* v_asyncConstsMap_3216_; lean_object* v_asyncCtx_x3f_3217_; lean_object* v_importRealizationCtx_x3f_3218_; lean_object* v_localRealizationCtxMap_3219_; lean_object* v_allRealizations_3220_; uint8_t v_isExporting_3221_; uint8_t v_isRecordingDeps_3222_; lean_object* v_synthCacheRaw_x3f_3223_; lean_object* v_declChangeLog_3224_; lean_object* v_recordingConstGen_3225_; lean_object* v_constAddedGens_3226_; lean_object* v_constGen_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3311_; 
v_base_3211_ = lean_ctor_get(v___y_3204_, 0);
lean_inc_ref(v_base_3211_);
v_private_3212_ = lean_ctor_get(v_base_3211_, 0);
lean_inc(v_private_3212_);
v_header_3213_ = lean_ctor_get(v_private_3212_, 7);
lean_inc_ref(v_header_3213_);
v_serverBaseExts_3214_ = lean_ctor_get(v___y_3204_, 1);
v_checked_3215_ = lean_ctor_get(v___y_3204_, 2);
v_asyncConstsMap_3216_ = lean_ctor_get(v___y_3204_, 3);
v_asyncCtx_x3f_3217_ = lean_ctor_get(v___y_3204_, 4);
v_importRealizationCtx_x3f_3218_ = lean_ctor_get(v___y_3204_, 5);
v_localRealizationCtxMap_3219_ = lean_ctor_get(v___y_3204_, 6);
v_allRealizations_3220_ = lean_ctor_get(v___y_3204_, 7);
v_isExporting_3221_ = lean_ctor_get_uint8(v___y_3204_, sizeof(void*)*13);
v_isRecordingDeps_3222_ = lean_ctor_get_uint8(v___y_3204_, sizeof(void*)*13 + 1);
v_synthCacheRaw_x3f_3223_ = lean_ctor_get(v___y_3204_, 8);
v_declChangeLog_3224_ = lean_ctor_get(v___y_3204_, 9);
v_recordingConstGen_3225_ = lean_ctor_get(v___y_3204_, 10);
v_constAddedGens_3226_ = lean_ctor_get(v___y_3204_, 11);
v_constGen_3227_ = lean_ctor_get(v___y_3204_, 12);
v_isSharedCheck_3311_ = !lean_is_exclusive(v___y_3204_);
if (v_isSharedCheck_3311_ == 0)
{
lean_object* v_unused_3312_; 
v_unused_3312_ = lean_ctor_get(v___y_3204_, 0);
lean_dec(v_unused_3312_);
v___x_3229_ = v___y_3204_;
v_isShared_3230_ = v_isSharedCheck_3311_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_constGen_3227_);
lean_inc(v_constAddedGens_3226_);
lean_inc(v_recordingConstGen_3225_);
lean_inc(v_declChangeLog_3224_);
lean_inc(v_synthCacheRaw_x3f_3223_);
lean_inc(v_allRealizations_3220_);
lean_inc(v_localRealizationCtxMap_3219_);
lean_inc(v_importRealizationCtx_x3f_3218_);
lean_inc(v_asyncCtx_x3f_3217_);
lean_inc(v_asyncConstsMap_3216_);
lean_inc(v_checked_3215_);
lean_inc(v_serverBaseExts_3214_);
lean_dec(v___y_3204_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3311_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v_public_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3309_; 
v_public_3231_ = lean_ctor_get(v_base_3211_, 1);
v_isSharedCheck_3309_ = !lean_is_exclusive(v_base_3211_);
if (v_isSharedCheck_3309_ == 0)
{
lean_object* v_unused_3310_; 
v_unused_3310_ = lean_ctor_get(v_base_3211_, 0);
lean_dec(v_unused_3310_);
v___x_3233_ = v_base_3211_;
v_isShared_3234_ = v_isSharedCheck_3309_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_public_3231_);
lean_dec(v_base_3211_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3309_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v_constants_3235_; uint8_t v_quotInit_3236_; lean_object* v_diagnostics_3237_; lean_object* v_importedExtraConsts_3238_; lean_object* v_extensions_3239_; lean_object* v_irBaseExts_3240_; lean_object* v_extGens_3241_; lean_object* v_trackedGen_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3307_; 
v_constants_3235_ = lean_ctor_get(v_private_3212_, 0);
v_quotInit_3236_ = lean_ctor_get_uint8(v_private_3212_, sizeof(void*)*8);
v_diagnostics_3237_ = lean_ctor_get(v_private_3212_, 1);
v_importedExtraConsts_3238_ = lean_ctor_get(v_private_3212_, 2);
v_extensions_3239_ = lean_ctor_get(v_private_3212_, 3);
v_irBaseExts_3240_ = lean_ctor_get(v_private_3212_, 4);
v_extGens_3241_ = lean_ctor_get(v_private_3212_, 5);
v_trackedGen_3242_ = lean_ctor_get(v_private_3212_, 6);
v_isSharedCheck_3307_ = !lean_is_exclusive(v_private_3212_);
if (v_isSharedCheck_3307_ == 0)
{
lean_object* v_unused_3308_; 
v_unused_3308_ = lean_ctor_get(v_private_3212_, 7);
lean_dec(v_unused_3308_);
v___x_3244_ = v_private_3212_;
v_isShared_3245_ = v_isSharedCheck_3307_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_trackedGen_3242_);
lean_inc(v_extGens_3241_);
lean_inc(v_irBaseExts_3240_);
lean_inc(v_extensions_3239_);
lean_inc(v_importedExtraConsts_3238_);
lean_inc(v_diagnostics_3237_);
lean_inc(v_constants_3235_);
lean_dec(v_private_3212_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3307_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
uint32_t v_trustLevel_3246_; lean_object* v_mainModule_3247_; uint8_t v_isModule_3248_; lean_object* v_regions_3249_; lean_object* v_modules_3250_; lean_object* v_moduleNames_3251_; lean_object* v_moduleName2Idx_3252_; lean_object* v_importAllModules_3253_; lean_object* v_moduleData_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3305_; 
v_trustLevel_3246_ = lean_ctor_get_uint32(v_header_3213_, sizeof(void*)*8);
v_mainModule_3247_ = lean_ctor_get(v_header_3213_, 0);
v_isModule_3248_ = lean_ctor_get_uint8(v_header_3213_, sizeof(void*)*8 + 4);
v_regions_3249_ = lean_ctor_get(v_header_3213_, 2);
v_modules_3250_ = lean_ctor_get(v_header_3213_, 3);
v_moduleNames_3251_ = lean_ctor_get(v_header_3213_, 4);
v_moduleName2Idx_3252_ = lean_ctor_get(v_header_3213_, 5);
v_importAllModules_3253_ = lean_ctor_get(v_header_3213_, 6);
v_moduleData_3254_ = lean_ctor_get(v_header_3213_, 7);
v_isSharedCheck_3305_ = !lean_is_exclusive(v_header_3213_);
if (v_isSharedCheck_3305_ == 0)
{
lean_object* v_unused_3306_; 
v_unused_3306_ = lean_ctor_get(v_header_3213_, 1);
lean_dec(v_unused_3306_);
v___x_3256_ = v_header_3213_;
v_isShared_3257_ = v_isSharedCheck_3305_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_moduleData_3254_);
lean_inc(v_importAllModules_3253_);
lean_inc(v_moduleName2Idx_3252_);
lean_inc(v_moduleNames_3251_);
lean_inc(v_modules_3250_);
lean_inc(v_regions_3249_);
lean_inc(v_mainModule_3247_);
lean_dec(v_header_3213_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3305_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3258_; lean_object* v_imports_3259_; lean_object* v___x_3261_; 
v___x_3258_ = lean_array_fget(v_moduleData_3206_, v___y_3203_);
lean_dec_ref(v_moduleData_3206_);
v_imports_3259_ = lean_ctor_get(v___x_3258_, 0);
lean_inc_ref(v_imports_3259_);
lean_dec(v___x_3258_);
if (v_isShared_3257_ == 0)
{
lean_ctor_set(v___x_3256_, 1, v_imports_3259_);
v___x_3261_ = v___x_3256_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 8, 5);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_mainModule_3247_);
lean_ctor_set(v_reuseFailAlloc_3304_, 1, v_imports_3259_);
lean_ctor_set(v_reuseFailAlloc_3304_, 2, v_regions_3249_);
lean_ctor_set(v_reuseFailAlloc_3304_, 3, v_modules_3250_);
lean_ctor_set(v_reuseFailAlloc_3304_, 4, v_moduleNames_3251_);
lean_ctor_set(v_reuseFailAlloc_3304_, 5, v_moduleName2Idx_3252_);
lean_ctor_set(v_reuseFailAlloc_3304_, 6, v_importAllModules_3253_);
lean_ctor_set(v_reuseFailAlloc_3304_, 7, v_moduleData_3254_);
lean_ctor_set_uint32(v_reuseFailAlloc_3304_, sizeof(void*)*8, v_trustLevel_3246_);
lean_ctor_set_uint8(v_reuseFailAlloc_3304_, sizeof(void*)*8 + 4, v_isModule_3248_);
v___x_3261_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
lean_object* v___x_3263_; 
if (v_isShared_3245_ == 0)
{
lean_ctor_set(v___x_3244_, 7, v___x_3261_);
v___x_3263_ = v___x_3244_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_constants_3235_);
lean_ctor_set(v_reuseFailAlloc_3303_, 1, v_diagnostics_3237_);
lean_ctor_set(v_reuseFailAlloc_3303_, 2, v_importedExtraConsts_3238_);
lean_ctor_set(v_reuseFailAlloc_3303_, 3, v_extensions_3239_);
lean_ctor_set(v_reuseFailAlloc_3303_, 4, v_irBaseExts_3240_);
lean_ctor_set(v_reuseFailAlloc_3303_, 5, v_extGens_3241_);
lean_ctor_set(v_reuseFailAlloc_3303_, 6, v_trackedGen_3242_);
lean_ctor_set(v_reuseFailAlloc_3303_, 7, v___x_3261_);
lean_ctor_set_uint8(v_reuseFailAlloc_3303_, sizeof(void*)*8, v_quotInit_3236_);
v___x_3263_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
lean_object* v___x_3265_; 
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 0, v___x_3263_);
v___x_3265_ = v___x_3233_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v___x_3263_);
lean_ctor_set(v_reuseFailAlloc_3302_, 1, v_public_3231_);
v___x_3265_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
lean_object* v___x_3267_; 
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 0, v___x_3265_);
v___x_3267_ = v___x_3229_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3265_);
lean_ctor_set(v_reuseFailAlloc_3301_, 1, v_serverBaseExts_3214_);
lean_ctor_set(v_reuseFailAlloc_3301_, 2, v_checked_3215_);
lean_ctor_set(v_reuseFailAlloc_3301_, 3, v_asyncConstsMap_3216_);
lean_ctor_set(v_reuseFailAlloc_3301_, 4, v_asyncCtx_x3f_3217_);
lean_ctor_set(v_reuseFailAlloc_3301_, 5, v_importRealizationCtx_x3f_3218_);
lean_ctor_set(v_reuseFailAlloc_3301_, 6, v_localRealizationCtxMap_3219_);
lean_ctor_set(v_reuseFailAlloc_3301_, 7, v_allRealizations_3220_);
lean_ctor_set(v_reuseFailAlloc_3301_, 8, v_synthCacheRaw_x3f_3223_);
lean_ctor_set(v_reuseFailAlloc_3301_, 9, v_declChangeLog_3224_);
lean_ctor_set(v_reuseFailAlloc_3301_, 10, v_recordingConstGen_3225_);
lean_ctor_set(v_reuseFailAlloc_3301_, 11, v_constAddedGens_3226_);
lean_ctor_set(v_reuseFailAlloc_3301_, 12, v_constGen_3227_);
lean_ctor_set_uint8(v_reuseFailAlloc_3301_, sizeof(void*)*13, v_isExporting_3221_);
lean_ctor_set_uint8(v_reuseFailAlloc_3301_, sizeof(void*)*13 + 1, v_isRecordingDeps_3222_);
v___x_3267_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; uint16_t v___x_3276_; uint8_t v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v_env_3295_; uint8_t v___x_3296_; uint16_t v___x_3297_; uint16_t v___x_3298_; uint16_t v___x_3299_; uint8_t v___x_3300_; 
v___x_3268_ = l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
v___x_3269_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2833_, v___x_3268_, v___x_3267_, v___y_3203_, v___x_3199_);
lean_dec(v___y_3203_);
v___x_3270_ = l_Lean_instInhabitedFileMap_default;
v___x_3271_ = lean_unsigned_to_nat(1000u);
v___x_3272_ = l_Lean_Core_getMaxHeartbeats(v___x_2858_);
v___x_3273_ = l_Lean_firstFrontendMacroScope;
v___x_3274_ = lean_box(0);
v___x_3275_ = lean_box(0);
v___x_3276_ = l_Lean_OptionFlags_ofOptions(v___x_2858_);
v___x_3277_ = 0;
v___x_3278_ = lean_obj_once(&l_main___closed__20, &l_main___closed__20_once, _init_l_main___closed__20);
v___x_3279_ = ((lean_object*)(l_main___closed__23));
lean_inc_n(v___y_3202_, 3);
v___x_3280_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3280_, 0, v___y_3202_);
lean_ctor_set(v___x_3280_, 1, v___x_3196_);
lean_ctor_set(v___x_3280_, 2, v___x_2826_);
v___x_3281_ = lean_obj_once(&l_main___closed__24, &l_main___closed__24_once, _init_l_main___closed__24);
v___x_3282_ = lean_obj_once(&l_main___closed__27, &l_main___closed__27_once, _init_l_main___closed__27);
v___x_3283_ = ((lean_object*)(l_main___closed__28));
v___x_3284_ = l_Lean_Options_empty;
v___x_3285_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_3286_ = lean_obj_once(&l_main___closed__30, &l_main___closed__30_once, _init_l_main___closed__30);
v___x_3287_ = lean_obj_once(&l_main___closed__31, &l_main___closed__31_once, _init_l_main___closed__31);
lean_inc_ref(v___x_3280_);
v___x_3288_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3267_);
lean_ctor_set(v___x_3288_, 1, v___x_3278_);
lean_ctor_set(v___x_3288_, 2, v___x_3279_);
lean_ctor_set(v___x_3288_, 3, v___x_3280_);
lean_ctor_set(v___x_3288_, 4, v___x_3281_);
lean_ctor_set(v___x_3288_, 5, v___x_3282_);
lean_ctor_set(v___x_3288_, 6, v___x_3285_);
lean_ctor_set(v___x_3288_, 7, v___x_3286_);
lean_ctor_set(v___x_3288_, 8, v___x_3287_);
lean_ctor_set(v___x_3288_, 9, v___x_3283_);
v___x_3289_ = lean_st_mk_ref(v___x_3288_);
v___x_3290_ = l_Lean_inheritedTraceOptions;
v___x_3291_ = lean_st_ref_get(v___x_3290_);
lean_inc(v___x_3291_);
lean_inc(v___x_3272_);
lean_inc_ref(v___x_2858_);
lean_inc(v_head_2816_);
v___x_3292_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3292_, 0, v_head_2816_);
lean_ctor_set(v___x_3292_, 1, v___x_3270_);
lean_ctor_set(v___x_3292_, 2, v___x_2858_);
lean_ctor_set(v___x_3292_, 3, v___x_3271_);
lean_ctor_set(v___x_3292_, 4, v___y_3202_);
lean_ctor_set(v___x_3292_, 5, v___x_2826_);
lean_ctor_set(v___x_3292_, 6, v___x_2857_);
lean_ctor_set(v___x_3292_, 7, v___x_3272_);
lean_ctor_set(v___x_3292_, 8, v___y_3202_);
lean_ctor_set(v___x_3292_, 9, v___x_3273_);
lean_ctor_set(v___x_3292_, 10, v___x_3274_);
lean_ctor_set(v___x_3292_, 11, v___x_3291_);
v___x_3293_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3293_, 0, v___x_3292_);
lean_ctor_set(v___x_3293_, 1, v___x_2857_);
lean_ctor_set(v___x_3293_, 2, v___x_3275_);
lean_ctor_set_uint16(v___x_3293_, sizeof(void*)*3, v___x_3276_);
lean_ctor_set_uint8(v___x_3293_, sizeof(void*)*3 + 2, v___x_2841_);
lean_ctor_set_uint8(v___x_3293_, sizeof(void*)*3 + 3, v___x_3277_);
lean_ctor_set_uint8(v___x_3293_, sizeof(void*)*3 + 4, v___x_2841_);
v___x_3294_ = lean_st_ref_get(v___x_3289_);
v_env_3295_ = lean_ctor_get(v___x_3294_, 0);
lean_inc_ref(v_env_3295_);
lean_dec(v___x_3294_);
v___x_3296_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3295_);
lean_dec_ref(v_env_3295_);
v___x_3297_ = 512;
v___x_3298_ = lean_uint16_land(v___x_3276_, v___x_3297_);
v___x_3299_ = 0;
v___x_3300_ = lean_uint16_dec_eq(v___x_3298_, v___x_3299_);
if (v___x_3300_ == 0)
{
if (v___x_3296_ == 0)
{
lean_dec(v___x_3291_);
lean_dec(v___x_3272_);
v___y_3130_ = v___x_3208_;
v___y_3131_ = v___x_3270_;
v___y_3132_ = v___y_3201_;
v___y_3133_ = v___x_3275_;
v___y_3134_ = v___x_2826_;
v___y_3135_ = v___x_3274_;
v___y_3136_ = v___x_3282_;
v___y_3137_ = v___x_3277_;
v___y_3138_ = v___x_3284_;
v___y_3139_ = v___x_3273_;
v___y_3140_ = v___x_3280_;
v___y_3141_ = v___x_3287_;
v___y_3142_ = v___x_3293_;
v___y_3143_ = v___x_3289_;
v___y_3144_ = v___x_3208_;
v___y_3145_ = v___x_3268_;
v___y_3146_ = v___x_3284_;
v___y_3147_ = v___x_3276_;
v___y_3148_ = v___x_3269_;
v___y_3149_ = v___y_3202_;
v___y_3150_ = v___x_3278_;
v___y_3151_ = v___x_3281_;
v___y_3152_ = v___x_3282_;
v___y_3153_ = v___x_3285_;
v___y_3154_ = v___x_3283_;
v___y_3155_ = v___x_3286_;
v___y_3156_ = v___x_3279_;
goto v___jp_3129_;
}
else
{
lean_dec_ref_known(v___x_3293_, 3);
lean_inc(v_head_2816_);
lean_inc_n(v___y_3202_, 2);
lean_inc(v___x_3289_);
v___y_3067_ = v___x_3208_;
v___y_3068_ = v___x_3275_;
v___y_3069_ = v___y_3201_;
v___y_3070_ = v___x_3270_;
v___y_3071_ = v___x_2826_;
v___y_3072_ = v___x_3274_;
v___y_3073_ = v___x_3282_;
v___y_3074_ = v___x_3277_;
v___y_3075_ = v___x_3284_;
v___y_3076_ = v___x_3273_;
v___y_3077_ = v___x_3280_;
v___y_3078_ = v___x_3287_;
v___y_3079_ = v___x_3289_;
v___y_3080_ = v___x_3268_;
v___y_3081_ = v___x_3284_;
v___y_3082_ = v___x_3276_;
v___y_3083_ = v___x_3269_;
v___y_3084_ = v___y_3202_;
v___y_3085_ = v___x_3278_;
v___y_3086_ = v___x_3282_;
v___y_3087_ = v___x_3281_;
v___y_3088_ = v___x_3285_;
v___y_3089_ = v___x_3283_;
v___y_3090_ = v___x_3286_;
v___y_3091_ = v___x_3279_;
v_fileName_3092_ = v_head_2816_;
v_fileMap_3093_ = v___x_3270_;
v_currNamespace_3094_ = v___y_3202_;
v_openDecls_3095_ = v___x_2826_;
v_initHeartbeats_3096_ = v___x_2857_;
v_maxHeartbeats_3097_ = v___x_3272_;
v_quotContext_3098_ = v___y_3202_;
v_currMacroScope_3099_ = v___x_3273_;
v_cancelTk_x3f_3100_ = v___x_3274_;
v_inheritedTraceOptions_3101_ = v___x_3291_;
v_currRecDepth_3102_ = v___x_2857_;
v_ref_3103_ = v___x_3275_;
v_suppressElabErrors_3104_ = v___x_2841_;
v_checkDeprecated_3105_ = v___x_3277_;
v_isRecordingDeps_3106_ = v___x_2841_;
v___y_3107_ = v___x_3289_;
goto v___jp_3066_;
}
}
else
{
if (v___x_3296_ == 0)
{
lean_dec_ref_known(v___x_3293_, 3);
lean_inc(v_head_2816_);
lean_inc_n(v___y_3202_, 2);
lean_inc(v___x_3289_);
v___y_3067_ = v___x_3208_;
v___y_3068_ = v___x_3275_;
v___y_3069_ = v___y_3201_;
v___y_3070_ = v___x_3270_;
v___y_3071_ = v___x_2826_;
v___y_3072_ = v___x_3274_;
v___y_3073_ = v___x_3282_;
v___y_3074_ = v___x_3277_;
v___y_3075_ = v___x_3284_;
v___y_3076_ = v___x_3273_;
v___y_3077_ = v___x_3280_;
v___y_3078_ = v___x_3287_;
v___y_3079_ = v___x_3289_;
v___y_3080_ = v___x_3268_;
v___y_3081_ = v___x_3284_;
v___y_3082_ = v___x_3276_;
v___y_3083_ = v___x_3269_;
v___y_3084_ = v___y_3202_;
v___y_3085_ = v___x_3278_;
v___y_3086_ = v___x_3282_;
v___y_3087_ = v___x_3281_;
v___y_3088_ = v___x_3285_;
v___y_3089_ = v___x_3283_;
v___y_3090_ = v___x_3286_;
v___y_3091_ = v___x_3279_;
v_fileName_3092_ = v_head_2816_;
v_fileMap_3093_ = v___x_3270_;
v_currNamespace_3094_ = v___y_3202_;
v_openDecls_3095_ = v___x_2826_;
v_initHeartbeats_3096_ = v___x_2857_;
v_maxHeartbeats_3097_ = v___x_3272_;
v_quotContext_3098_ = v___y_3202_;
v_currMacroScope_3099_ = v___x_3273_;
v_cancelTk_x3f_3100_ = v___x_3274_;
v_inheritedTraceOptions_3101_ = v___x_3291_;
v_currRecDepth_3102_ = v___x_2857_;
v_ref_3103_ = v___x_3275_;
v_suppressElabErrors_3104_ = v___x_2841_;
v_checkDeprecated_3105_ = v___x_3277_;
v_isRecordingDeps_3106_ = v___x_2841_;
v___y_3107_ = v___x_3289_;
goto v___jp_3066_;
}
else
{
lean_dec(v___x_3291_);
lean_dec(v___x_3272_);
v___y_3130_ = v___x_3208_;
v___y_3131_ = v___x_3270_;
v___y_3132_ = v___y_3201_;
v___y_3133_ = v___x_3275_;
v___y_3134_ = v___x_2826_;
v___y_3135_ = v___x_3274_;
v___y_3136_ = v___x_3282_;
v___y_3137_ = v___x_3277_;
v___y_3138_ = v___x_3284_;
v___y_3139_ = v___x_3273_;
v___y_3140_ = v___x_3280_;
v___y_3141_ = v___x_3287_;
v___y_3142_ = v___x_3293_;
v___y_3143_ = v___x_3289_;
v___y_3144_ = v___x_2841_;
v___y_3145_ = v___x_3268_;
v___y_3146_ = v___x_3284_;
v___y_3147_ = v___x_3276_;
v___y_3148_ = v___x_3269_;
v___y_3149_ = v___y_3202_;
v___y_3150_ = v___x_3278_;
v___y_3151_ = v___x_3281_;
v___y_3152_ = v___x_3282_;
v___y_3153_ = v___x_3285_;
v___y_3154_ = v___x_3283_;
v___y_3155_ = v___x_3286_;
v___y_3156_ = v___x_3279_;
goto v___jp_3129_;
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
v___jp_3313_:
{
lean_object* v___x_3323_; 
if (v_isShared_2815_ == 0)
{
lean_ctor_set_tag(v___x_2814_, 0);
lean_ctor_set(v___x_2814_, 1, v___y_3321_);
lean_ctor_set(v___x_2814_, 0, v___y_3320_);
v___x_3323_ = v___x_2814_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v___y_3320_);
lean_ctor_set(v_reuseFailAlloc_3329_, 1, v___y_3321_);
v___x_3323_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
lean_object* v___f_3324_; lean_object* v___x_3325_; 
v___f_3324_ = lean_alloc_closure((void*)(l_main___lam__3___boxed), 2, 1);
lean_closure_set(v___f_3324_, 0, v___x_3323_);
v___x_3325_ = lean_box(0);
if (v___y_3317_ == 0)
{
lean_object* v___x_3326_; 
lean_inc(v___y_3315_);
lean_inc_ref(v___y_3319_);
v___x_3326_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v___y_3319_, v___y_3316_, v___f_3324_, v___x_3325_, v___y_3315_, v___x_2854_);
v___y_3201_ = v___y_3314_;
v___y_3202_ = v___y_3315_;
v___y_3203_ = v___y_3318_;
v___y_3204_ = v___x_3326_;
goto v___jp_3200_;
}
else
{
lean_object* v___x_3327_; lean_object* v___x_3328_; 
lean_inc_ref_n(v___y_3319_, 2);
v___x_3327_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite___redArg(v___y_3319_, v___y_3316_);
lean_dec_ref(v___y_3316_);
lean_inc(v___y_3315_);
v___x_3328_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v___y_3319_, v___x_3327_, v___f_3324_, v___x_3325_, v___y_3315_, v___x_2854_);
v___y_3201_ = v___y_3314_;
v___y_3202_ = v___y_3315_;
v___y_3203_ = v___y_3318_;
v___y_3204_ = v___x_3328_;
goto v___jp_3200_;
}
}
}
v___jp_3330_:
{
lean_object* v___x_3335_; lean_object* v_toEnvExtension_3336_; lean_object* v_asyncMode_3337_; uint8_t v_logWrites_3338_; lean_object* v___x_3339_; lean_object* v_importedEntries_3340_; lean_object* v_state_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; uint8_t v___x_3344_; 
v___x_3335_ = l_Lean_IR_declMapExt;
v_toEnvExtension_3336_ = lean_ctor_get(v___x_3335_, 0);
v_asyncMode_3337_ = lean_ctor_get(v_toEnvExtension_3336_, 2);
v_logWrites_3338_ = lean_ctor_get_uint8(v_toEnvExtension_3336_, sizeof(void*)*6);
lean_inc(v___y_3332_);
lean_inc_ref(v___y_3334_);
v___x_3339_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2830_, v_toEnvExtension_3336_, v___y_3334_, v_asyncMode_3337_, v___y_3332_, v___x_2841_);
v_importedEntries_3340_ = lean_ctor_get(v___x_3339_, 0);
lean_inc_ref(v_importedEntries_3340_);
v_state_3341_ = lean_ctor_get(v___x_3339_, 1);
lean_inc(v_state_3341_);
lean_dec(v___x_3339_);
v___x_3342_ = lean_array_get_borrowed(v___x_2831_, v_importedEntries_3340_, v___y_3333_);
v___x_3343_ = lean_array_get_size(v___x_3342_);
v___x_3344_ = lean_nat_dec_lt(v___x_2857_, v___x_3343_);
if (v___x_3344_ == 0)
{
v___y_3314_ = v___y_3331_;
v___y_3315_ = v___y_3332_;
v___y_3316_ = v___y_3334_;
v___y_3317_ = v_logWrites_3338_;
v___y_3318_ = v___y_3333_;
v___y_3319_ = v_toEnvExtension_3336_;
v___y_3320_ = v_importedEntries_3340_;
v___y_3321_ = v_state_3341_;
goto v___jp_3313_;
}
else
{
size_t v___x_3345_; size_t v___x_3346_; lean_object* v___x_3347_; 
v___x_3345_ = ((size_t)0ULL);
v___x_3346_ = lean_usize_of_nat(v___x_3343_);
lean_inc_ref(v___y_3334_);
v___x_3347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3334_, v___x_3342_, v___x_3345_, v___x_3346_, v_state_3341_);
v___y_3314_ = v___y_3331_;
v___y_3315_ = v___y_3332_;
v___y_3316_ = v___y_3334_;
v___y_3317_ = v_logWrites_3338_;
v___y_3318_ = v___y_3333_;
v___y_3319_ = v_toEnvExtension_3336_;
v___y_3320_ = v_importedEntries_3340_;
v___y_3321_ = v___x_3347_;
goto v___jp_3313_;
}
}
v___jp_3348_:
{
uint8_t v___x_3355_; 
v___x_3355_ = lean_nat_dec_lt(v___x_2857_, v___y_3351_);
if (v___x_3355_ == 0)
{
lean_dec_ref(v___y_3352_);
lean_dec(v___y_3351_);
v___y_3331_ = v___y_3349_;
v___y_3332_ = v___y_3350_;
v___y_3333_ = v___y_3353_;
v___y_3334_ = v___y_3354_;
goto v___jp_3330_;
}
else
{
size_t v___x_3356_; size_t v___x_3357_; lean_object* v___x_3358_; 
v___x_3356_ = ((size_t)0ULL);
v___x_3357_ = lean_usize_of_nat(v___y_3351_);
lean_dec(v___y_3351_);
v___x_3358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3352_, v___x_3356_, v___x_3357_, v___y_3354_);
lean_dec_ref(v___y_3352_);
v___y_3331_ = v___y_3349_;
v___y_3332_ = v___y_3350_;
v___y_3333_ = v___y_3353_;
v___y_3334_ = v___x_3358_;
goto v___jp_3330_;
}
}
v___jp_3359_:
{
lean_object* v___x_3365_; uint8_t v___x_3366_; 
v___x_3365_ = lean_array_get_size(v___y_3364_);
v___x_3366_ = lean_nat_dec_lt(v___x_2857_, v___x_3365_);
if (v___x_3366_ == 0)
{
v___y_3349_ = v___y_3360_;
v___y_3350_ = v___y_3361_;
v___y_3351_ = v___x_3365_;
v___y_3352_ = v___y_3364_;
v___y_3353_ = v___y_3363_;
v___y_3354_ = v___y_3362_;
goto v___jp_3348_;
}
else
{
size_t v___x_3367_; size_t v___x_3368_; lean_object* v___x_3369_; 
v___x_3367_ = ((size_t)0ULL);
v___x_3368_ = lean_usize_of_nat(v___x_3365_);
v___x_3369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3364_, v___x_3367_, v___x_3368_, v___y_3362_);
v___y_3349_ = v___y_3360_;
v___y_3350_ = v___y_3361_;
v___y_3351_ = v___x_3365_;
v___y_3352_ = v___y_3364_;
v___y_3353_ = v___y_3363_;
v___y_3354_ = v___x_3369_;
goto v___jp_3348_;
}
}
v___jp_3370_:
{
lean_object* v___x_3373_; lean_object* v_ext_3374_; lean_object* v___x_3375_; 
v___x_3373_ = l_Lean_Compiler_CSimp_ext;
v_ext_3374_ = lean_ctor_get(v___x_3373_, 1);
lean_inc_ref(v_ext_3374_);
lean_inc(v___y_3371_);
v___x_3375_ = l_main___elam__0___redArg(v___y_3371_, v___x_2841_, v___x_2825_, v_ext_3374_, v___y_3372_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v_a_3376_; lean_object* v___x_3377_; lean_object* v_ext_3378_; lean_object* v___x_3379_; 
v_a_3376_ = lean_ctor_get(v___x_3375_, 0);
lean_inc(v_a_3376_);
lean_dec_ref_known(v___x_3375_, 1);
v___x_3377_ = l_Lean_Meta_instanceExtension;
v_ext_3378_ = lean_ctor_get(v___x_3377_, 1);
lean_inc_ref(v_ext_3378_);
lean_inc(v___y_3371_);
v___x_3379_ = l_main___elam__0___redArg(v___y_3371_, v___x_2841_, v___x_2825_, v_ext_3378_, v_a_3376_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_object* v_a_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
v_a_3380_ = lean_ctor_get(v___x_3379_, 0);
lean_inc(v_a_3380_);
lean_dec_ref_known(v___x_3379_, 1);
v___x_3381_ = l_Lean_classExtension;
lean_inc(v___y_3371_);
v___x_3382_ = l_main___elam__0___redArg(v___y_3371_, v___x_2841_, v___x_2827_, v___x_3381_, v_a_3380_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc(v_a_3383_);
lean_dec_ref_known(v___x_3382_, 1);
v___x_3384_ = l_Lean_Meta_Match_Extension_extension;
lean_inc(v___y_3371_);
v___x_3385_ = l_main___elam__0___redArg(v___y_3371_, v___x_2841_, v___x_2828_, v___x_3384_, v_a_3383_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3409_; 
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3388_ = v___x_3385_;
v_isShared_3389_ = v_isSharedCheck_3409_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v___x_3385_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3409_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3390_; 
v___x_3390_ = l_Lean_Environment_getModuleIdx_x3f(v_a_3386_, v_name_2836_);
if (lean_obj_tag(v___x_3390_) == 1)
{
lean_object* v_val_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; uint8_t v___x_3396_; 
lean_del_object(v___x_3388_);
v_val_3391_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_val_3391_);
lean_dec_ref_known(v___x_3390_, 1);
v___x_3392_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_3393_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2829_, v___x_3392_, v_a_3386_, v_val_3391_, v___x_3199_);
v___x_3394_ = lean_array_get_size(v___x_3393_);
v___x_3395_ = ((lean_object*)(l_main___closed__32));
v___x_3396_ = lean_nat_dec_lt(v___x_2857_, v___x_3394_);
if (v___x_3396_ == 0)
{
lean_dec_ref(v___x_3393_);
lean_inc(v___y_3371_);
v___y_3360_ = v___y_3371_;
v___y_3361_ = v___y_3371_;
v___y_3362_ = v_a_3386_;
v___y_3363_ = v_val_3391_;
v___y_3364_ = v___x_3395_;
goto v___jp_3359_;
}
else
{
size_t v___x_3397_; size_t v___x_3398_; lean_object* v___x_3399_; 
v___x_3397_ = ((size_t)0ULL);
v___x_3398_ = lean_usize_of_nat(v___x_3394_);
lean_inc(v_a_3386_);
v___x_3399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_3386_, v___x_3393_, v___x_3397_, v___x_3398_, v___x_3395_);
lean_dec_ref(v___x_3393_);
lean_inc(v___y_3371_);
v___y_3360_ = v___y_3371_;
v___y_3361_ = v___y_3371_;
v___y_3362_ = v_a_3386_;
v___y_3363_ = v_val_3391_;
v___y_3364_ = v___x_3399_;
goto v___jp_3359_;
}
}
else
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3407_; 
lean_dec(v___x_3390_);
lean_dec(v_a_3386_);
lean_dec(v___y_3371_);
lean_dec_ref(v___x_2858_);
lean_del_object(v___x_2851_);
lean_dec(v_fst_2848_);
lean_dec(v_head_2820_);
lean_del_object(v___x_2818_);
lean_dec(v_head_2816_);
lean_del_object(v___x_2814_);
v___x_3400_ = ((lean_object*)(l_main___closed__33));
v___x_3401_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2836_, v___x_2854_);
v___x_3402_ = lean_string_append(v___x_3400_, v___x_3401_);
lean_dec_ref(v___x_3401_);
v___x_3403_ = ((lean_object*)(l_main___closed__34));
v___x_3404_ = lean_string_append(v___x_3402_, v___x_3403_);
v___x_3405_ = lean_mk_io_user_error(v___x_3404_);
if (v_isShared_3389_ == 0)
{
lean_ctor_set_tag(v___x_3388_, 1);
lean_ctor_set(v___x_3388_, 0, v___x_3405_);
v___x_3407_ = v___x_3388_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v___x_3405_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
else
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
lean_dec(v___y_3371_);
lean_dec_ref(v___x_2858_);
lean_del_object(v___x_2851_);
lean_dec(v_fst_2848_);
lean_dec(v_name_2836_);
lean_dec(v_head_2820_);
lean_del_object(v___x_2818_);
lean_dec(v_head_2816_);
lean_del_object(v___x_2814_);
v_a_3410_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___x_3385_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3385_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3410_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
else
{
lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3425_; 
lean_dec(v___y_3371_);
lean_dec_ref(v___x_2858_);
lean_del_object(v___x_2851_);
lean_dec(v_fst_2848_);
lean_dec(v_name_2836_);
lean_dec(v_head_2820_);
lean_del_object(v___x_2818_);
lean_dec(v_head_2816_);
lean_del_object(v___x_2814_);
v_a_3418_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3420_ = v___x_3382_;
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3382_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3423_; 
if (v_isShared_3421_ == 0)
{
v___x_3423_ = v___x_3420_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3418_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
}
else
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3433_; 
lean_dec(v___y_3371_);
lean_dec_ref(v___x_2858_);
lean_del_object(v___x_2851_);
lean_dec(v_fst_2848_);
lean_dec(v_name_2836_);
lean_dec(v_head_2820_);
lean_del_object(v___x_2818_);
lean_dec(v_head_2816_);
lean_del_object(v___x_2814_);
v_a_3426_ = lean_ctor_get(v___x_3379_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3379_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3428_ = v___x_3379_;
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___x_3379_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3431_; 
if (v_isShared_3429_ == 0)
{
v___x_3431_ = v___x_3428_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_a_3426_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
lean_dec(v___y_3371_);
lean_dec_ref(v___x_2858_);
lean_del_object(v___x_2851_);
lean_dec(v_fst_2848_);
lean_dec(v_name_2836_);
lean_dec(v_head_2820_);
lean_del_object(v___x_2818_);
lean_dec(v_head_2816_);
lean_del_object(v___x_2814_);
v_a_3434_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3375_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3375_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
v___jp_3442_:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___f_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
v___x_3444_ = l_Lean_instInhabitedImportState_default;
v___x_3445_ = lean_box(v___x_3199_);
v___x_3446_ = lean_box(v___y_3443_);
v___x_3447_ = lean_box(v___x_2854_);
v___x_3448_ = lean_box(v___x_2841_);
lean_inc_ref(v___x_2858_);
lean_inc(v_name_2836_);
v___f_3449_ = lean_alloc_closure((void*)(l_main___lam__1___boxed), 10, 9);
lean_closure_set(v___f_3449_, 0, v___x_3444_);
lean_closure_set(v___f_3449_, 1, v___x_3198_);
lean_closure_set(v___f_3449_, 2, v___x_3445_);
lean_closure_set(v___f_3449_, 3, v_importArts_2838_);
lean_closure_set(v___f_3449_, 4, v___x_3446_);
lean_closure_set(v___f_3449_, 5, v___x_3447_);
lean_closure_set(v___f_3449_, 6, v_name_2836_);
lean_closure_set(v___f_3449_, 7, v___x_2858_);
lean_closure_set(v___f_3449_, 8, v___x_3448_);
v___x_3450_ = lean_alloc_closure((void*)(l_Lean_withImporting___boxed), 3, 2);
lean_closure_set(v___x_3450_, 0, lean_box(0));
lean_closure_set(v___x_3450_, 1, v___f_3449_);
v___x_3451_ = lean_box(0);
v___x_3452_ = l_Lean_profileitIOUnsafe___redArg(v___x_3194_, v___x_2858_, v___x_3450_, v___x_3451_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v_a_3453_; lean_object* v___x_3454_; lean_object* v_toEnvExtension_3455_; lean_object* v_asyncMode_3456_; uint8_t v_logWrites_3457_; lean_object* v___x_3458_; 
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_a_3453_);
lean_dec_ref_known(v___x_3452_, 1);
v___x_3454_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_3455_ = lean_ctor_get(v___x_3454_, 0);
v_asyncMode_3456_ = lean_ctor_get(v_toEnvExtension_3455_, 2);
v_logWrites_3457_ = lean_ctor_get_uint8(v_toEnvExtension_3455_, sizeof(void*)*6);
lean_inc(v_name_2836_);
v___x_3458_ = l_Lean_Environment_setMainModule(v_a_3453_, v_name_2836_);
if (v_logWrites_3457_ == 0)
{
lean_object* v___x_3459_; 
lean_inc_ref(v_toEnvExtension_3455_);
v___x_3459_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_3455_, v___x_3458_, v___f_2840_, v_asyncMode_3456_, v___x_3451_, v___x_2854_);
v___y_3371_ = v___x_3451_;
v___y_3372_ = v___x_3459_;
goto v___jp_3370_;
}
else
{
lean_object* v___x_3460_; lean_object* v___x_3461_; 
lean_inc_ref_n(v_toEnvExtension_3455_, 2);
v___x_3460_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite___redArg(v_toEnvExtension_3455_, v___x_3458_);
lean_dec_ref(v___x_3458_);
v___x_3461_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore___redArg(v_toEnvExtension_3455_, v___x_3460_, v___f_2840_, v_asyncMode_3456_, v___x_3451_, v___x_2854_);
v___y_3371_ = v___x_3451_;
v___y_3372_ = v___x_3461_;
goto v___jp_3370_;
}
}
else
{
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3469_; 
lean_dec_ref(v___x_2858_);
lean_del_object(v___x_2851_);
lean_dec(v_fst_2848_);
lean_dec_ref(v___f_2840_);
lean_dec(v_name_2836_);
lean_dec(v_head_2820_);
lean_del_object(v___x_2818_);
lean_dec(v_head_2816_);
lean_del_object(v___x_2814_);
v_a_3462_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3464_ = v___x_3452_;
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3452_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3467_; 
if (v_isShared_3465_ == 0)
{
v___x_3467_ = v___x_3464_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_a_3462_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
}
}
else
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
lean_dec_ref(v___x_2858_);
lean_del_object(v___x_2851_);
lean_dec(v_fst_2848_);
lean_dec_ref(v___f_2840_);
lean_dec(v_importArts_2838_);
lean_dec(v_name_2836_);
lean_dec(v_head_2820_);
lean_del_object(v___x_2818_);
lean_dec(v_head_2816_);
lean_del_object(v___x_2814_);
v_a_3471_ = lean_ctor_get(v___x_3193_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3193_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3193_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3471_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
v___jp_2859_:
{
lean_object* v___x_2882_; lean_object* v_messages_2883_; lean_object* v_env_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_3010_; 
v___x_2882_ = lean_st_ref_get(v___y_2876_);
lean_dec(v___y_2876_);
v_messages_2883_ = lean_ctor_get(v___x_2882_, 7);
v_env_2884_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_3010_ == 0)
{
lean_object* v_unused_3011_; lean_object* v_unused_3012_; lean_object* v_unused_3013_; lean_object* v_unused_3014_; lean_object* v_unused_3015_; lean_object* v_unused_3016_; lean_object* v_unused_3017_; lean_object* v_unused_3018_; 
v_unused_3011_ = lean_ctor_get(v___x_2882_, 9);
lean_dec(v_unused_3011_);
v_unused_3012_ = lean_ctor_get(v___x_2882_, 8);
lean_dec(v_unused_3012_);
v_unused_3013_ = lean_ctor_get(v___x_2882_, 6);
lean_dec(v_unused_3013_);
v_unused_3014_ = lean_ctor_get(v___x_2882_, 5);
lean_dec(v_unused_3014_);
v_unused_3015_ = lean_ctor_get(v___x_2882_, 4);
lean_dec(v_unused_3015_);
v_unused_3016_ = lean_ctor_get(v___x_2882_, 3);
lean_dec(v_unused_3016_);
v_unused_3017_ = lean_ctor_get(v___x_2882_, 2);
lean_dec(v_unused_3017_);
v_unused_3018_ = lean_ctor_get(v___x_2882_, 1);
lean_dec(v_unused_3018_);
v___x_2886_ = v___x_2882_;
v_isShared_2887_ = v_isSharedCheck_3010_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_messages_2883_);
lean_inc(v_env_2884_);
lean_dec(v___x_2882_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_3010_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v_unreported_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v_unreported_2888_ = lean_ctor_get(v_messages_2883_, 1);
v___x_2889_ = lean_box(0);
v___x_2890_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_unreported_2888_, v___x_2889_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_3000_; 
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_3000_ == 0)
{
lean_object* v_unused_3001_; 
v_unused_3001_ = lean_ctor_get(v___x_2890_, 0);
lean_dec(v_unused_3001_);
v___x_2892_ = v___x_2890_;
v_isShared_2893_ = v_isSharedCheck_3000_;
goto v_resetjp_2891_;
}
else
{
lean_dec(v___x_2890_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_3000_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
uint8_t v___x_2894_; 
v___x_2894_ = l_Lean_MessageLog_hasErrors(v_messages_2883_);
lean_dec_ref(v_messages_2883_);
if (v___x_2894_ == 0)
{
lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
lean_del_object(v___x_2892_);
v___x_2895_ = ((lean_object*)(l_main___closed__9));
lean_inc(v_head_2816_);
v___x_2896_ = l_System_FilePath_addExtension(v_head_2816_, v___x_2895_);
lean_inc_ref(v_env_2884_);
v___x_2897_ = l___private_LeanIR_0__mkIRSigData(v_env_2884_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v___x_2899_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_a_2898_);
lean_dec_ref_known(v___x_2897_, 1);
lean_inc_ref(v_env_2884_);
v___x_2899_ = l___private_LeanIR_0__mkIRData(v_env_2884_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2905_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
lean_inc(v_a_2900_);
lean_dec_ref_known(v___x_2899_, 1);
v___x_2901_ = l_Lean_Environment_mainModule(v_env_2884_);
v___x_2902_ = ((lean_object*)(l_main___closed__11));
v___x_2903_ = l_Lean_Name_append(v___x_2901_, v___x_2902_);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 1, v_a_2898_);
lean_ctor_set(v___x_2851_, 0, v___x_2896_);
v___x_2905_ = v___x_2851_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2896_);
lean_ctor_set(v_reuseFailAlloc_2979_, 1, v_a_2898_);
v___x_2905_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
lean_object* v___x_2907_; 
lean_inc(v_head_2816_);
if (v_isShared_2819_ == 0)
{
lean_ctor_set_tag(v___x_2818_, 0);
lean_ctor_set(v___x_2818_, 1, v_a_2900_);
v___x_2907_ = v___x_2818_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_head_2816_);
lean_ctor_set(v_reuseFailAlloc_2978_, 1, v_a_2900_);
v___x_2907_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2908_ = lean_unsigned_to_nat(2u);
v___x_2909_ = lean_mk_empty_array_with_capacity(v___x_2908_);
v___x_2910_ = lean_array_push(v___x_2909_, v___x_2905_);
v___x_2911_ = lean_array_push(v___x_2910_, v___x_2907_);
v___x_2912_ = l_Lean_saveModuleDataParts(v___x_2903_, v___x_2911_);
lean_dec(v___x_2903_);
if (lean_obj_tag(v___x_2912_) == 0)
{
uint8_t v___x_2913_; lean_object* v___x_2914_; 
lean_dec_ref_known(v___x_2912_, 1);
v___x_2913_ = 1;
v___x_2914_ = lean_io_prim_handle_mk(v_head_2820_, v___x_2913_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; uint16_t v___x_2918_; lean_object* v___x_2920_; 
lean_dec(v_head_2820_);
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
lean_dec_ref_known(v___x_2914_, 1);
v___x_2916_ = ((lean_object*)(l_main___closed__12));
v___x_2917_ = l_Lean_Core_getMaxHeartbeats(v___y_2878_);
v___x_2918_ = l_Lean_OptionFlags_ofOptions(v___y_2878_);
lean_inc_ref(v___y_2879_);
lean_inc_ref(v___y_2872_);
lean_inc_ref(v___y_2880_);
lean_inc_ref(v___y_2877_);
lean_inc_ref(v___y_2874_);
lean_inc_ref(v___y_2875_);
lean_inc_ref(v___y_2881_);
lean_inc(v___y_2873_);
lean_inc_ref(v_env_2884_);
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 9, v___y_2879_);
lean_ctor_set(v___x_2886_, 8, v___y_2872_);
lean_ctor_set(v___x_2886_, 7, v___y_2880_);
lean_ctor_set(v___x_2886_, 6, v___y_2877_);
lean_ctor_set(v___x_2886_, 5, v___y_2874_);
lean_ctor_set(v___x_2886_, 4, v___y_2875_);
lean_ctor_set(v___x_2886_, 3, v___y_2870_);
lean_ctor_set(v___x_2886_, 2, v___y_2881_);
lean_ctor_set(v___x_2886_, 1, v___y_2873_);
v___x_2920_ = v___x_2886_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_env_2884_);
lean_ctor_set(v_reuseFailAlloc_2947_, 1, v___y_2873_);
lean_ctor_set(v_reuseFailAlloc_2947_, 2, v___y_2881_);
lean_ctor_set(v_reuseFailAlloc_2947_, 3, v___y_2870_);
lean_ctor_set(v_reuseFailAlloc_2947_, 4, v___y_2875_);
lean_ctor_set(v_reuseFailAlloc_2947_, 5, v___y_2874_);
lean_ctor_set(v_reuseFailAlloc_2947_, 6, v___y_2877_);
lean_ctor_set(v_reuseFailAlloc_2947_, 7, v___y_2880_);
lean_ctor_set(v_reuseFailAlloc_2947_, 8, v___y_2872_);
lean_ctor_set(v_reuseFailAlloc_2947_, 9, v___y_2879_);
v___x_2920_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___f_2926_; lean_object* v___x_2927_; 
v___x_2921_ = lean_box(v___x_2918_);
v___x_2922_ = lean_box(v___y_2860_);
v___x_2923_ = lean_box(v___x_2841_);
v___x_2924_ = lean_box(v___y_2867_);
v___x_2925_ = lean_box(v___x_2894_);
lean_inc_ref(v___y_2866_);
lean_inc_ref(v___y_2868_);
v___f_2926_ = lean_alloc_closure((void*)(l_main___lam__2___boxed), 20, 19);
lean_closure_set(v___f_2926_, 0, v___x_2920_);
lean_closure_set(v___f_2926_, 1, v___y_2868_);
lean_closure_set(v___f_2926_, 2, v___x_2921_);
lean_closure_set(v___f_2926_, 3, v_name_2836_);
lean_closure_set(v___f_2926_, 4, v_a_2915_);
lean_closure_set(v___f_2926_, 5, v___x_2922_);
lean_closure_set(v___f_2926_, 6, v___y_2866_);
lean_closure_set(v___f_2926_, 7, v_head_2816_);
lean_closure_set(v___f_2926_, 8, v___y_2863_);
lean_closure_set(v___f_2926_, 9, v___y_2862_);
lean_closure_set(v___f_2926_, 10, v___y_2864_);
lean_closure_set(v___f_2926_, 11, v___x_2917_);
lean_closure_set(v___f_2926_, 12, v___y_2869_);
lean_closure_set(v___f_2926_, 13, v___y_2865_);
lean_closure_set(v___f_2926_, 14, v___x_2857_);
lean_closure_set(v___f_2926_, 15, v___y_2861_);
lean_closure_set(v___f_2926_, 16, v___x_2923_);
lean_closure_set(v___f_2926_, 17, v___x_2924_);
lean_closure_set(v___f_2926_, 18, v___x_2925_);
v___x_2927_ = l_Lean_profileitIOUnsafe___redArg(v___x_2916_, v___x_2858_, v___f_2926_, v___y_2871_);
lean_dec_ref(v___x_2858_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v___x_2928_; uint8_t v___x_2929_; 
lean_dec_ref_known(v___x_2927_, 1);
v___x_2928_ = lean_display_cumulative_profiling_times();
v___x_2929_ = lean_unbox(v_fst_2848_);
lean_dec(v_fst_2848_);
if (v___x_2929_ == 0)
{
lean_dec_ref(v_env_2884_);
goto v___jp_2807_;
}
else
{
lean_object* v___x_2930_; 
v___x_2930_ = l_Lean_Environment_displayStats(v_env_2884_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_dec_ref_known(v___x_2930_, 1);
goto v___jp_2807_;
}
else
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2930_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2930_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_a_2931_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
}
}
else
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
lean_dec_ref(v_env_2884_);
lean_dec(v_fst_2848_);
v_a_2939_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2941_ = v___x_2927_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___x_2927_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2939_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
}
else
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
lean_dec_ref_known(v___x_2914_, 1);
lean_del_object(v___x_2886_);
lean_dec_ref(v_env_2884_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec_ref(v___x_2858_);
lean_dec(v_fst_2848_);
lean_dec(v_name_2836_);
lean_dec(v_head_2816_);
v___x_2948_ = ((lean_object*)(l_main___closed__13));
v___x_2949_ = lean_string_append(v___x_2948_, v_head_2820_);
lean_dec(v_head_2820_);
v___x_2950_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__1));
v___x_2951_ = lean_string_append(v___x_2949_, v___x_2950_);
v___x_2952_ = l_IO_eprintln___at___00main_spec__6(v___x_2951_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2960_; 
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2960_ == 0)
{
lean_object* v_unused_2961_; 
v_unused_2961_ = lean_ctor_get(v___x_2952_, 0);
lean_dec(v_unused_2961_);
v___x_2954_ = v___x_2952_;
v_isShared_2955_ = v_isSharedCheck_2960_;
goto v_resetjp_2953_;
}
else
{
lean_dec(v___x_2952_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2960_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2956_; lean_object* v___x_2958_; 
v___x_2956_ = l_main___boxed__const__1;
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 0, v___x_2956_);
v___x_2958_ = v___x_2954_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v___x_2956_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
else
{
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2969_; 
v_a_2962_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2964_ = v___x_2952_;
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2952_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2967_; 
if (v_isShared_2965_ == 0)
{
v___x_2967_ = v___x_2964_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_a_2962_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
}
else
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
lean_del_object(v___x_2886_);
lean_dec_ref(v_env_2884_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec_ref(v___x_2858_);
lean_dec(v_fst_2848_);
lean_dec(v_name_2836_);
lean_dec(v_head_2820_);
lean_dec(v_head_2816_);
v_a_2970_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2912_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2912_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
}
}
else
{
lean_object* v_a_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2987_; 
lean_dec(v_a_2898_);
lean_dec_ref(v___x_2896_);
lean_del_object(v___x_2886_);
lean_dec_ref(v_env_2884_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec_ref(v___x_2858_);
lean_del_object(v___x_2851_);
lean_dec(v_fst_2848_);
lean_dec(v_name_2836_);
lean_dec(v_head_2820_);
lean_del_object(v___x_2818_);
lean_dec(v_head_2816_);
v_a_2980_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2982_ = v___x_2899_;
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_a_2980_);
lean_dec(v___x_2899_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2985_; 
if (v_isShared_2983_ == 0)
{
v___x_2985_ = v___x_2982_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_a_2980_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
}
else
{
lean_object* v_a_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_2995_; 
lean_dec_ref(v___x_2896_);
lean_del_object(v___x_2886_);
lean_dec_ref(v_env_2884_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec_ref(v___x_2858_);
lean_del_object(v___x_2851_);
lean_dec(v_fst_2848_);
lean_dec(v_name_2836_);
lean_dec(v_head_2820_);
lean_del_object(v___x_2818_);
lean_dec(v_head_2816_);
v_a_2988_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2990_ = v___x_2897_;
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_a_2988_);
lean_dec(v___x_2897_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2993_; 
if (v_isShared_2991_ == 0)
{
v___x_2993_ = v___x_2990_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_a_2988_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
}
else
{
lean_object* v___x_2996_; lean_object* v___x_2998_; 
lean_del_object(v___x_2886_);
lean_dec_ref(v_env_2884_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec_ref(v___x_2858_);
lean_del_object(v___x_2851_);
lean_dec(v_fst_2848_);
lean_dec(v_name_2836_);
lean_dec(v_head_2820_);
lean_del_object(v___x_2818_);
lean_dec(v_head_2816_);
v___x_2996_ = l_main___boxed__const__1;
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 0, v___x_2996_);
v___x_2998_ = v___x_2892_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2996_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
else
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3009_; 
lean_del_object(v___x_2886_);
lean_dec_ref(v_env_2884_);
lean_dec_ref(v_messages_2883_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec_ref(v___x_2858_);
lean_del_object(v___x_2851_);
lean_dec(v_fst_2848_);
lean_dec(v_name_2836_);
lean_dec(v_head_2820_);
lean_del_object(v___x_2818_);
lean_dec(v_head_2816_);
v_a_3002_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3004_ = v___x_2890_;
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_2890_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3007_; 
if (v_isShared_3005_ == 0)
{
v___x_3007_ = v___x_3004_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_a_3002_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
}
v___jp_3019_:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; size_t v_sz_3057_; size_t v___x_3058_; lean_object* v___x_3059_; 
lean_inc_ref(v___y_3038_);
v___x_3054_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3054_, 0, v___y_3053_);
lean_ctor_set(v___x_3054_, 1, v_nextMacroScope_3043_);
lean_ctor_set(v___x_3054_, 2, v_ngen_3044_);
lean_ctor_set(v___x_3054_, 3, v_auxDeclNGen_3045_);
lean_ctor_set(v___x_3054_, 4, v_traceState_3046_);
lean_ctor_set(v___x_3054_, 5, v___y_3038_);
lean_ctor_set(v___x_3054_, 6, v_recordedDeps_3047_);
lean_ctor_set(v___x_3054_, 7, v_messages_3048_);
lean_ctor_set(v___x_3054_, 8, v_infoState_3049_);
lean_ctor_set(v___x_3054_, 9, v_snapshotTasks_3050_);
v___x_3055_ = lean_st_ref_put(v___y_3040_, v___x_3054_);
v___x_3056_ = lean_box(0);
v_sz_3057_ = lean_array_size(v___y_3034_);
v___x_3058_ = ((size_t)0ULL);
v___x_3059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(v___y_3034_, v_sz_3057_, v___x_3058_, v___x_3056_, v___y_3036_, v___y_3040_);
lean_dec_ref(v___y_3034_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_dec_ref_known(v___x_3059_, 1);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3036_);
v___y_2860_ = v___y_3020_;
v___y_2861_ = v___y_3023_;
v___y_2862_ = v___y_3022_;
v___y_2863_ = v___y_3021_;
v___y_2864_ = v___y_3024_;
v___y_2865_ = v___y_3025_;
v___y_2866_ = v___y_3026_;
v___y_2867_ = v___y_3027_;
v___y_2868_ = v___y_3028_;
v___y_2869_ = v___y_3029_;
v___y_2870_ = v___y_3030_;
v___y_2871_ = v___y_3035_;
v___y_2872_ = v___y_3031_;
v___y_2873_ = v___y_3037_;
v___y_2874_ = v___y_3038_;
v___y_2875_ = v___y_3039_;
v___y_2876_ = v___y_3032_;
v___y_2877_ = v___y_3041_;
v___y_2878_ = v___y_3033_;
v___y_2879_ = v___y_3042_;
v___y_2880_ = v___y_3051_;
v___y_2881_ = v___y_3052_;
goto v___jp_2859_;
}
else
{
lean_object* v_a_3060_; uint8_t v___x_3061_; 
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_a_3060_);
lean_dec_ref_known(v___x_3059_, 1);
v___x_3061_ = l_Lean_Exception_isInterrupt(v_a_3060_);
if (v___x_3061_ == 0)
{
lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3062_ = l_Lean_Exception_toMessageData(v_a_3060_);
v___x_3063_ = l_Lean_logError___at___00main_spec__13(v___x_3062_, v___y_3036_, v___y_3040_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3036_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_dec_ref_known(v___x_3063_, 1);
v___y_2860_ = v___y_3020_;
v___y_2861_ = v___y_3023_;
v___y_2862_ = v___y_3022_;
v___y_2863_ = v___y_3021_;
v___y_2864_ = v___y_3024_;
v___y_2865_ = v___y_3025_;
v___y_2866_ = v___y_3026_;
v___y_2867_ = v___y_3027_;
v___y_2868_ = v___y_3028_;
v___y_2869_ = v___y_3029_;
v___y_2870_ = v___y_3030_;
v___y_2871_ = v___y_3035_;
v___y_2872_ = v___y_3031_;
v___y_2873_ = v___y_3037_;
v___y_2874_ = v___y_3038_;
v___y_2875_ = v___y_3039_;
v___y_2876_ = v___y_3032_;
v___y_2877_ = v___y_3041_;
v___y_2878_ = v___y_3033_;
v___y_2879_ = v___y_3042_;
v___y_2880_ = v___y_3051_;
v___y_2881_ = v___y_3052_;
goto v___jp_2859_;
}
else
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
lean_dec_ref_known(v___x_3063_, 1);
lean_dec(v___y_3035_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3030_);
lean_dec(v___y_3029_);
lean_dec(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec(v___y_3023_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec_ref(v___x_2858_);
lean_del_object(v___x_2851_);
lean_dec(v_fst_2848_);
lean_dec(v_name_2836_);
lean_dec(v_head_2820_);
lean_del_object(v___x_2818_);
lean_dec(v_head_2816_);
v___x_3064_ = lean_obj_once(&l_main___closed__17, &l_main___closed__17_once, _init_l_main___closed__17);
v___x_3065_ = l_panic___at___00main_spec__5(v___x_3064_);
return v___x_3065_;
}
}
else
{
lean_dec(v_a_3060_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3036_);
v___y_2860_ = v___y_3020_;
v___y_2861_ = v___y_3023_;
v___y_2862_ = v___y_3022_;
v___y_2863_ = v___y_3021_;
v___y_2864_ = v___y_3024_;
v___y_2865_ = v___y_3025_;
v___y_2866_ = v___y_3026_;
v___y_2867_ = v___y_3027_;
v___y_2868_ = v___y_3028_;
v___y_2869_ = v___y_3029_;
v___y_2870_ = v___y_3030_;
v___y_2871_ = v___y_3035_;
v___y_2872_ = v___y_3031_;
v___y_2873_ = v___y_3037_;
v___y_2874_ = v___y_3038_;
v___y_2875_ = v___y_3039_;
v___y_2876_ = v___y_3032_;
v___y_2877_ = v___y_3041_;
v___y_2878_ = v___y_3033_;
v___y_2879_ = v___y_3042_;
v___y_2880_ = v___y_3051_;
v___y_2881_ = v___y_3052_;
goto v___jp_2859_;
}
}
}
v___jp_3066_:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v_env_3113_; lean_object* v_nextMacroScope_3114_; lean_object* v_ngen_3115_; lean_object* v_auxDeclNGen_3116_; lean_object* v_traceState_3117_; lean_object* v_recordedDeps_3118_; lean_object* v_messages_3119_; lean_object* v_infoState_3120_; lean_object* v_snapshotTasks_3121_; lean_object* v___x_3122_; uint8_t v___x_3123_; 
v___x_3108_ = l_Lean_maxRecDepth;
v___x_3109_ = l_Lean_Option_get___at___00main_spec__8(v___x_2858_, v___x_3108_);
lean_inc_ref(v___x_2858_);
v___x_3110_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3110_, 0, v_fileName_3092_);
lean_ctor_set(v___x_3110_, 1, v_fileMap_3093_);
lean_ctor_set(v___x_3110_, 2, v___x_2858_);
lean_ctor_set(v___x_3110_, 3, v___x_3109_);
lean_ctor_set(v___x_3110_, 4, v_currNamespace_3094_);
lean_ctor_set(v___x_3110_, 5, v_openDecls_3095_);
lean_ctor_set(v___x_3110_, 6, v_initHeartbeats_3096_);
lean_ctor_set(v___x_3110_, 7, v_maxHeartbeats_3097_);
lean_ctor_set(v___x_3110_, 8, v_quotContext_3098_);
lean_ctor_set(v___x_3110_, 9, v_currMacroScope_3099_);
lean_ctor_set(v___x_3110_, 10, v_cancelTk_x3f_3100_);
lean_ctor_set(v___x_3110_, 11, v_inheritedTraceOptions_3101_);
v___x_3111_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3111_, 0, v___x_3110_);
lean_ctor_set(v___x_3111_, 1, v_currRecDepth_3102_);
lean_ctor_set(v___x_3111_, 2, v_ref_3103_);
lean_ctor_set_uint16(v___x_3111_, sizeof(void*)*3, v___y_3082_);
lean_ctor_set_uint8(v___x_3111_, sizeof(void*)*3 + 2, v_suppressElabErrors_3104_);
lean_ctor_set_uint8(v___x_3111_, sizeof(void*)*3 + 3, v_checkDeprecated_3105_);
lean_ctor_set_uint8(v___x_3111_, sizeof(void*)*3 + 4, v_isRecordingDeps_3106_);
v___x_3112_ = lean_st_ref_take(v___y_3107_);
v_env_3113_ = lean_ctor_get(v___x_3112_, 0);
lean_inc_ref(v_env_3113_);
v_nextMacroScope_3114_ = lean_ctor_get(v___x_3112_, 1);
lean_inc(v_nextMacroScope_3114_);
v_ngen_3115_ = lean_ctor_get(v___x_3112_, 2);
lean_inc_ref(v_ngen_3115_);
v_auxDeclNGen_3116_ = lean_ctor_get(v___x_3112_, 3);
lean_inc_ref(v_auxDeclNGen_3116_);
v_traceState_3117_ = lean_ctor_get(v___x_3112_, 4);
lean_inc_ref(v_traceState_3117_);
v_recordedDeps_3118_ = lean_ctor_get(v___x_3112_, 6);
lean_inc_ref(v_recordedDeps_3118_);
v_messages_3119_ = lean_ctor_get(v___x_3112_, 7);
lean_inc_ref(v_messages_3119_);
v_infoState_3120_ = lean_ctor_get(v___x_3112_, 8);
lean_inc_ref(v_infoState_3120_);
v_snapshotTasks_3121_ = lean_ctor_get(v___x_3112_, 9);
lean_inc_ref(v_snapshotTasks_3121_);
lean_dec(v___x_3112_);
v___x_3122_ = lean_array_get_size(v___y_3083_);
v___x_3123_ = lean_nat_dec_lt(v___x_2857_, v___x_3122_);
if (v___x_3123_ == 0)
{
lean_object* v___x_3124_; 
lean_inc_ref(v___y_3080_);
v___x_3124_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3080_, v_env_3113_, v___x_2832_);
v___y_3020_ = v___y_3067_;
v___y_3021_ = v___y_3070_;
v___y_3022_ = v___y_3069_;
v___y_3023_ = v___y_3068_;
v___y_3024_ = v___y_3071_;
v___y_3025_ = v___y_3072_;
v___y_3026_ = v___y_3073_;
v___y_3027_ = v___y_3074_;
v___y_3028_ = v___y_3075_;
v___y_3029_ = v___y_3076_;
v___y_3030_ = v___y_3077_;
v___y_3031_ = v___y_3078_;
v___y_3032_ = v___y_3079_;
v___y_3033_ = v___y_3081_;
v___y_3034_ = v___y_3083_;
v___y_3035_ = v___y_3084_;
v___y_3036_ = v___x_3111_;
v___y_3037_ = v___y_3085_;
v___y_3038_ = v___y_3086_;
v___y_3039_ = v___y_3087_;
v___y_3040_ = v___y_3107_;
v___y_3041_ = v___y_3088_;
v___y_3042_ = v___y_3089_;
v_nextMacroScope_3043_ = v_nextMacroScope_3114_;
v_ngen_3044_ = v_ngen_3115_;
v_auxDeclNGen_3045_ = v_auxDeclNGen_3116_;
v_traceState_3046_ = v_traceState_3117_;
v_recordedDeps_3047_ = v_recordedDeps_3118_;
v_messages_3048_ = v_messages_3119_;
v_infoState_3049_ = v_infoState_3120_;
v_snapshotTasks_3050_ = v_snapshotTasks_3121_;
v___y_3051_ = v___y_3090_;
v___y_3052_ = v___y_3091_;
v___y_3053_ = v___x_3124_;
goto v___jp_3019_;
}
else
{
size_t v___x_3125_; size_t v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3125_ = ((size_t)0ULL);
v___x_3126_ = lean_usize_of_nat(v___x_3122_);
v___x_3127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v___y_3083_, v___x_3125_, v___x_3126_, v___x_2832_);
lean_inc_ref(v___y_3080_);
v___x_3128_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3080_, v_env_3113_, v___x_3127_);
v___y_3020_ = v___y_3067_;
v___y_3021_ = v___y_3070_;
v___y_3022_ = v___y_3069_;
v___y_3023_ = v___y_3068_;
v___y_3024_ = v___y_3071_;
v___y_3025_ = v___y_3072_;
v___y_3026_ = v___y_3073_;
v___y_3027_ = v___y_3074_;
v___y_3028_ = v___y_3075_;
v___y_3029_ = v___y_3076_;
v___y_3030_ = v___y_3077_;
v___y_3031_ = v___y_3078_;
v___y_3032_ = v___y_3079_;
v___y_3033_ = v___y_3081_;
v___y_3034_ = v___y_3083_;
v___y_3035_ = v___y_3084_;
v___y_3036_ = v___x_3111_;
v___y_3037_ = v___y_3085_;
v___y_3038_ = v___y_3086_;
v___y_3039_ = v___y_3087_;
v___y_3040_ = v___y_3107_;
v___y_3041_ = v___y_3088_;
v___y_3042_ = v___y_3089_;
v_nextMacroScope_3043_ = v_nextMacroScope_3114_;
v_ngen_3044_ = v_ngen_3115_;
v_auxDeclNGen_3045_ = v_auxDeclNGen_3116_;
v_traceState_3046_ = v_traceState_3117_;
v_recordedDeps_3047_ = v_recordedDeps_3118_;
v_messages_3048_ = v_messages_3119_;
v_infoState_3049_ = v_infoState_3120_;
v_snapshotTasks_3050_ = v_snapshotTasks_3121_;
v___y_3051_ = v___y_3090_;
v___y_3052_ = v___y_3091_;
v___y_3053_ = v___x_3128_;
goto v___jp_3019_;
}
}
v___jp_3129_:
{
lean_object* v___x_3157_; lean_object* v_env_3158_; lean_object* v_nextMacroScope_3159_; lean_object* v_ngen_3160_; lean_object* v_auxDeclNGen_3161_; lean_object* v_traceState_3162_; lean_object* v_recordedDeps_3163_; lean_object* v_messages_3164_; lean_object* v_infoState_3165_; lean_object* v_snapshotTasks_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3191_; 
v___x_3157_ = lean_st_ref_take(v___y_3143_);
v_env_3158_ = lean_ctor_get(v___x_3157_, 0);
v_nextMacroScope_3159_ = lean_ctor_get(v___x_3157_, 1);
v_ngen_3160_ = lean_ctor_get(v___x_3157_, 2);
v_auxDeclNGen_3161_ = lean_ctor_get(v___x_3157_, 3);
v_traceState_3162_ = lean_ctor_get(v___x_3157_, 4);
v_recordedDeps_3163_ = lean_ctor_get(v___x_3157_, 6);
v_messages_3164_ = lean_ctor_get(v___x_3157_, 7);
v_infoState_3165_ = lean_ctor_get(v___x_3157_, 8);
v_snapshotTasks_3166_ = lean_ctor_get(v___x_3157_, 9);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3191_ == 0)
{
lean_object* v_unused_3192_; 
v_unused_3192_ = lean_ctor_get(v___x_3157_, 5);
lean_dec(v_unused_3192_);
v___x_3168_ = v___x_3157_;
v_isShared_3169_ = v_isSharedCheck_3191_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_snapshotTasks_3166_);
lean_inc(v_infoState_3165_);
lean_inc(v_messages_3164_);
lean_inc(v_recordedDeps_3163_);
lean_inc(v_traceState_3162_);
lean_inc(v_auxDeclNGen_3161_);
lean_inc(v_ngen_3160_);
lean_inc(v_nextMacroScope_3159_);
lean_inc(v_env_3158_);
lean_dec(v___x_3157_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3191_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3170_; lean_object* v___x_3172_; 
v___x_3170_ = l_Lean_Kernel_enableDiag(v_env_3158_, v___y_3144_);
lean_inc_ref(v___y_3152_);
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 5, v___y_3152_);
lean_ctor_set(v___x_3168_, 0, v___x_3170_);
v___x_3172_ = v___x_3168_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3170_);
lean_ctor_set(v_reuseFailAlloc_3190_, 1, v_nextMacroScope_3159_);
lean_ctor_set(v_reuseFailAlloc_3190_, 2, v_ngen_3160_);
lean_ctor_set(v_reuseFailAlloc_3190_, 3, v_auxDeclNGen_3161_);
lean_ctor_set(v_reuseFailAlloc_3190_, 4, v_traceState_3162_);
lean_ctor_set(v_reuseFailAlloc_3190_, 5, v___y_3152_);
lean_ctor_set(v_reuseFailAlloc_3190_, 6, v_recordedDeps_3163_);
lean_ctor_set(v_reuseFailAlloc_3190_, 7, v_messages_3164_);
lean_ctor_set(v_reuseFailAlloc_3190_, 8, v_infoState_3165_);
lean_ctor_set(v_reuseFailAlloc_3190_, 9, v_snapshotTasks_3166_);
v___x_3172_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
lean_object* v___x_3173_; lean_object* v_toCold_3174_; lean_object* v_currRecDepth_3175_; lean_object* v_ref_3176_; uint8_t v_suppressElabErrors_3177_; uint8_t v_checkDeprecated_3178_; uint8_t v_isRecordingDeps_3179_; lean_object* v_fileName_3180_; lean_object* v_fileMap_3181_; lean_object* v_currNamespace_3182_; lean_object* v_openDecls_3183_; lean_object* v_initHeartbeats_3184_; lean_object* v_maxHeartbeats_3185_; lean_object* v_quotContext_3186_; lean_object* v_currMacroScope_3187_; lean_object* v_cancelTk_x3f_3188_; lean_object* v_inheritedTraceOptions_3189_; 
v___x_3173_ = lean_st_ref_put(v___y_3143_, v___x_3172_);
v_toCold_3174_ = lean_ctor_get(v___y_3142_, 0);
lean_inc_ref(v_toCold_3174_);
v_currRecDepth_3175_ = lean_ctor_get(v___y_3142_, 1);
lean_inc(v_currRecDepth_3175_);
v_ref_3176_ = lean_ctor_get(v___y_3142_, 2);
lean_inc(v_ref_3176_);
v_suppressElabErrors_3177_ = lean_ctor_get_uint8(v___y_3142_, sizeof(void*)*3 + 2);
v_checkDeprecated_3178_ = lean_ctor_get_uint8(v___y_3142_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3179_ = lean_ctor_get_uint8(v___y_3142_, sizeof(void*)*3 + 4);
lean_dec_ref(v___y_3142_);
v_fileName_3180_ = lean_ctor_get(v_toCold_3174_, 0);
lean_inc_ref(v_fileName_3180_);
v_fileMap_3181_ = lean_ctor_get(v_toCold_3174_, 1);
lean_inc_ref(v_fileMap_3181_);
v_currNamespace_3182_ = lean_ctor_get(v_toCold_3174_, 4);
lean_inc(v_currNamespace_3182_);
v_openDecls_3183_ = lean_ctor_get(v_toCold_3174_, 5);
lean_inc(v_openDecls_3183_);
v_initHeartbeats_3184_ = lean_ctor_get(v_toCold_3174_, 6);
lean_inc(v_initHeartbeats_3184_);
v_maxHeartbeats_3185_ = lean_ctor_get(v_toCold_3174_, 7);
lean_inc(v_maxHeartbeats_3185_);
v_quotContext_3186_ = lean_ctor_get(v_toCold_3174_, 8);
lean_inc(v_quotContext_3186_);
v_currMacroScope_3187_ = lean_ctor_get(v_toCold_3174_, 9);
lean_inc(v_currMacroScope_3187_);
v_cancelTk_x3f_3188_ = lean_ctor_get(v_toCold_3174_, 10);
lean_inc(v_cancelTk_x3f_3188_);
v_inheritedTraceOptions_3189_ = lean_ctor_get(v_toCold_3174_, 11);
lean_inc_ref(v_inheritedTraceOptions_3189_);
lean_dec_ref(v_toCold_3174_);
lean_inc(v___y_3143_);
v___y_3067_ = v___y_3130_;
v___y_3068_ = v___y_3133_;
v___y_3069_ = v___y_3132_;
v___y_3070_ = v___y_3131_;
v___y_3071_ = v___y_3134_;
v___y_3072_ = v___y_3135_;
v___y_3073_ = v___y_3136_;
v___y_3074_ = v___y_3137_;
v___y_3075_ = v___y_3138_;
v___y_3076_ = v___y_3139_;
v___y_3077_ = v___y_3140_;
v___y_3078_ = v___y_3141_;
v___y_3079_ = v___y_3143_;
v___y_3080_ = v___y_3145_;
v___y_3081_ = v___y_3146_;
v___y_3082_ = v___y_3147_;
v___y_3083_ = v___y_3148_;
v___y_3084_ = v___y_3149_;
v___y_3085_ = v___y_3150_;
v___y_3086_ = v___y_3152_;
v___y_3087_ = v___y_3151_;
v___y_3088_ = v___y_3153_;
v___y_3089_ = v___y_3154_;
v___y_3090_ = v___y_3155_;
v___y_3091_ = v___y_3156_;
v_fileName_3092_ = v_fileName_3180_;
v_fileMap_3093_ = v_fileMap_3181_;
v_currNamespace_3094_ = v_currNamespace_3182_;
v_openDecls_3095_ = v_openDecls_3183_;
v_initHeartbeats_3096_ = v_initHeartbeats_3184_;
v_maxHeartbeats_3097_ = v_maxHeartbeats_3185_;
v_quotContext_3098_ = v_quotContext_3186_;
v_currMacroScope_3099_ = v_currMacroScope_3187_;
v_cancelTk_x3f_3100_ = v_cancelTk_x3f_3188_;
v_inheritedTraceOptions_3101_ = v_inheritedTraceOptions_3189_;
v_currRecDepth_3102_ = v_currRecDepth_3175_;
v_ref_3103_ = v_ref_3176_;
v_suppressElabErrors_3104_ = v_suppressElabErrors_3177_;
v_checkDeprecated_3105_ = v_checkDeprecated_3178_;
v_isRecordingDeps_3106_ = v_isRecordingDeps_3179_;
v___y_3107_ = v___y_3143_;
goto v___jp_3066_;
}
}
}
}
}
else
{
lean_object* v_a_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3487_; 
lean_dec_ref(v___f_2840_);
lean_dec(v_importArts_2838_);
lean_dec(v_name_2836_);
lean_dec(v_head_2820_);
lean_del_object(v___x_2818_);
lean_dec(v_head_2816_);
lean_del_object(v___x_2814_);
v_a_3480_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3482_ = v___x_2846_;
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_a_3480_);
lean_dec(v___x_2846_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3485_; 
if (v_isShared_3483_ == 0)
{
v___x_3485_ = v___x_3482_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_a_3480_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
}
}
else
{
lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3496_; 
lean_del_object(v___x_2823_);
lean_dec(v_tail_2821_);
lean_dec(v_head_2820_);
lean_del_object(v___x_2818_);
lean_dec(v_head_2816_);
lean_del_object(v___x_2814_);
v_a_3489_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3491_ = v___x_2834_;
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_dec(v___x_2834_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3494_; 
if (v_isShared_3492_ == 0)
{
v___x_3494_ = v___x_3491_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3489_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_tail_2810_, 2);
lean_dec(v_tail_2811_);
lean_dec_ref_known(v_args_2785_, 2);
goto v___jp_2787_;
}
}
else
{
lean_dec(v_tail_2810_);
lean_dec_ref_known(v_args_2785_, 2);
goto v___jp_2787_;
}
}
else
{
lean_dec(v_args_2785_);
goto v___jp_2787_;
}
v___jp_2787_:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = ((lean_object*)(l_main___closed__0));
v___x_2789_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_2788_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2797_; 
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2797_ == 0)
{
lean_object* v_unused_2798_; 
v_unused_2798_ = lean_ctor_get(v___x_2789_, 0);
lean_dec(v_unused_2798_);
v___x_2791_ = v___x_2789_;
v_isShared_2792_ = v_isSharedCheck_2797_;
goto v_resetjp_2790_;
}
else
{
lean_dec(v___x_2789_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2797_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2793_; lean_object* v___x_2795_; 
v___x_2793_ = l_main___boxed__const__1;
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 0, v___x_2793_);
v___x_2795_ = v___x_2791_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v___x_2793_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
else
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
v_a_2799_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2789_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2789_);
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
v___jp_2807_:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2808_ = l_main___boxed__const__2;
v___x_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2808_);
return v___x_2809_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_3502_, lean_object* v_a_3503_){
_start:
{
lean_object* v_res_3504_; 
v_res_3504_ = _lean_main(v_args_3502_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object* v_as_3505_, lean_object* v_as_x27_3506_, lean_object* v_b_3507_, lean_object* v_a_3508_){
_start:
{
lean_object* v___x_3510_; 
v___x_3510_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_3506_, v_b_3507_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object* v_as_3511_, lean_object* v_as_x27_3512_, lean_object* v_b_3513_, lean_object* v_a_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v_res_3516_; 
v_res_3516_ = l_List_forIn_x27_loop___at___00main_spec__1(v_as_3511_, v_as_x27_3512_, v_b_3513_, v_a_3514_);
lean_dec(v_as_x27_3512_);
lean_dec(v_as_3511_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(lean_object* v___y_3517_, lean_object* v___y_3518_){
_start:
{
lean_object* v___x_3520_; 
v___x_3520_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___redArg(v___y_3518_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15___boxed(lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
lean_object* v_res_3524_; 
v_res_3524_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__15(v___y_3521_, v___y_3522_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3521_);
return v_res_3524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16(lean_object* v_00_u03b2_3525_, lean_object* v_m_3526_, lean_object* v_a_3527_, lean_object* v_fallback_3528_){
_start:
{
lean_object* v___x_3529_; 
v___x_3529_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___redArg(v_m_3526_, v_a_3527_, v_fallback_3528_);
return v___x_3529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16___boxed(lean_object* v_00_u03b2_3530_, lean_object* v_m_3531_, lean_object* v_a_3532_, lean_object* v_fallback_3533_){
_start:
{
lean_object* v_res_3534_; 
v_res_3534_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16(v_00_u03b2_3530_, v_m_3531_, v_a_3532_, v_fallback_3533_);
lean_dec(v_fallback_3533_);
lean_dec_ref(v_a_3532_);
lean_dec_ref(v_m_3531_);
return v_res_3534_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17(lean_object* v_00_u03b2_3535_, lean_object* v_m_3536_, lean_object* v_a_3537_, lean_object* v_b_3538_){
_start:
{
lean_object* v___x_3539_; 
v___x_3539_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17___redArg(v_m_3536_, v_a_3537_, v_b_3538_);
return v___x_3539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(lean_object* v_n_3540_, lean_object* v_as_3541_, lean_object* v_lo_3542_, lean_object* v_hi_3543_, lean_object* v_w_3544_, lean_object* v_hlo_3545_, lean_object* v_hhi_3546_){
_start:
{
lean_object* v___x_3547_; 
v___x_3547_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___redArg(v_n_3540_, v_as_3541_, v_lo_3542_, v_hi_3543_);
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20___boxed(lean_object* v_n_3548_, lean_object* v_as_3549_, lean_object* v_lo_3550_, lean_object* v_hi_3551_, lean_object* v_w_3552_, lean_object* v_hlo_3553_, lean_object* v_hhi_3554_){
_start:
{
lean_object* v_res_3555_; 
v_res_3555_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20(v_n_3548_, v_as_3549_, v_lo_3550_, v_hi_3551_, v_w_3552_, v_hlo_3553_, v_hhi_3554_);
lean_dec(v_hi_3551_);
lean_dec(v_n_3548_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16_spec__20(lean_object* v_00_u03b2_3556_, lean_object* v_a_3557_, lean_object* v_fallback_3558_, lean_object* v_x_3559_){
_start:
{
lean_object* v___x_3560_; 
v___x_3560_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16_spec__20___redArg(v_a_3557_, v_fallback_3558_, v_x_3559_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16_spec__20___boxed(lean_object* v_00_u03b2_3561_, lean_object* v_a_3562_, lean_object* v_fallback_3563_, lean_object* v_x_3564_){
_start:
{
lean_object* v_res_3565_; 
v_res_3565_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__16_spec__20(v_00_u03b2_3561_, v_a_3562_, v_fallback_3563_, v_x_3564_);
lean_dec(v_x_3564_);
lean_dec(v_fallback_3563_);
lean_dec_ref(v_a_3562_);
return v_res_3565_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__22(lean_object* v_00_u03b2_3566_, lean_object* v_a_3567_, lean_object* v_x_3568_){
_start:
{
uint8_t v___x_3569_; 
v___x_3569_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__22___redArg(v_a_3567_, v_x_3568_);
return v___x_3569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__22___boxed(lean_object* v_00_u03b2_3570_, lean_object* v_a_3571_, lean_object* v_x_3572_){
_start:
{
uint8_t v_res_3573_; lean_object* v_r_3574_; 
v_res_3573_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__22(v_00_u03b2_3570_, v_a_3571_, v_x_3572_);
lean_dec(v_x_3572_);
lean_dec_ref(v_a_3571_);
v_r_3574_ = lean_box(v_res_3573_);
return v_r_3574_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23(lean_object* v_00_u03b2_3575_, lean_object* v_data_3576_){
_start:
{
lean_object* v___x_3577_; 
v___x_3577_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23___redArg(v_data_3576_);
return v___x_3577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__24(lean_object* v_00_u03b2_3578_, lean_object* v_a_3579_, lean_object* v_b_3580_, lean_object* v_x_3581_){
_start:
{
lean_object* v___x_3582_; 
v___x_3582_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__24___redArg(v_a_3579_, v_b_3580_, v_x_3581_);
return v___x_3582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20_spec__30(lean_object* v_n_3583_, lean_object* v_lo_3584_, lean_object* v_hi_3585_, lean_object* v_hhi_3586_, lean_object* v_pivot_3587_, lean_object* v_as_3588_, lean_object* v_i_3589_, lean_object* v_k_3590_, lean_object* v_ilo_3591_, lean_object* v_ik_3592_, lean_object* v_w_3593_){
_start:
{
lean_object* v___x_3594_; 
v___x_3594_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20_spec__30___redArg(v_hi_3585_, v_pivot_3587_, v_as_3588_, v_i_3589_, v_k_3590_);
return v___x_3594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20_spec__30___boxed(lean_object* v_n_3595_, lean_object* v_lo_3596_, lean_object* v_hi_3597_, lean_object* v_hhi_3598_, lean_object* v_pivot_3599_, lean_object* v_as_3600_, lean_object* v_i_3601_, lean_object* v_k_3602_, lean_object* v_ilo_3603_, lean_object* v_ik_3604_, lean_object* v_w_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__20_spec__30(v_n_3595_, v_lo_3596_, v_hi_3597_, v_hhi_3598_, v_pivot_3599_, v_as_3600_, v_i_3601_, v_k_3602_, v_ilo_3603_, v_ik_3604_, v_w_3605_);
lean_dec_ref(v_pivot_3599_);
lean_dec(v_hi_3597_);
lean_dec(v_lo_3596_);
lean_dec(v_n_3595_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__39(lean_object* v_as_3607_, size_t v_sz_3608_, size_t v_i_3609_, lean_object* v_b_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_){
_start:
{
lean_object* v___x_3614_; 
v___x_3614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__39___redArg(v_as_3607_, v_sz_3608_, v_i_3609_, v_b_3610_, v___y_3611_);
return v___x_3614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__39___boxed(lean_object* v_as_3615_, lean_object* v_sz_3616_, lean_object* v_i_3617_, lean_object* v_b_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_){
_start:
{
size_t v_sz_boxed_3622_; size_t v_i_boxed_3623_; lean_object* v_res_3624_; 
v_sz_boxed_3622_ = lean_unbox_usize(v_sz_3616_);
lean_dec(v_sz_3616_);
v_i_boxed_3623_ = lean_unbox_usize(v_i_3617_);
lean_dec(v_i_3617_);
v_res_3624_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__26_spec__39(v_as_3615_, v_sz_boxed_3622_, v_i_boxed_3623_, v_b_3618_, v___y_3619_, v___y_3620_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec_ref(v_as_3615_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23_spec__34(lean_object* v_00_u03b2_3625_, lean_object* v_i_3626_, lean_object* v_source_3627_, lean_object* v_target_3628_){
_start:
{
lean_object* v___x_3629_; 
v___x_3629_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23_spec__34___redArg(v_i_3626_, v_source_3627_, v_target_3628_);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__27_spec__41(uint8_t v___x_3630_, lean_object* v_as_3631_, size_t v_sz_3632_, size_t v_i_3633_, lean_object* v_b_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
lean_object* v___x_3638_; 
v___x_3638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__27_spec__41___redArg(v___x_3630_, v_as_3631_, v_sz_3632_, v_i_3633_, v_b_3634_, v___y_3635_);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__27_spec__41___boxed(lean_object* v___x_3639_, lean_object* v_as_3640_, lean_object* v_sz_3641_, lean_object* v_i_3642_, lean_object* v_b_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_){
_start:
{
uint8_t v___x_40064__boxed_3647_; size_t v_sz_boxed_3648_; size_t v_i_boxed_3649_; lean_object* v_res_3650_; 
v___x_40064__boxed_3647_ = lean_unbox(v___x_3639_);
v_sz_boxed_3648_ = lean_unbox_usize(v_sz_3641_);
lean_dec(v_sz_3641_);
v_i_boxed_3649_ = lean_unbox_usize(v_i_3642_);
lean_dec(v_i_3642_);
v_res_3650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__27_spec__41(v___x_40064__boxed_3647_, v_as_3640_, v_sz_boxed_3648_, v_i_boxed_3649_, v_b_3643_, v___y_3644_, v___y_3645_);
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
lean_dec_ref(v_as_3640_);
return v_res_3650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__37_spec__50(lean_object* v_as_3651_, size_t v_sz_3652_, size_t v_i_3653_, lean_object* v_b_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_){
_start:
{
lean_object* v___x_3658_; 
v___x_3658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__37_spec__50___redArg(v_as_3651_, v_sz_3652_, v_i_3653_, v_b_3654_, v___y_3655_);
return v___x_3658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__37_spec__50___boxed(lean_object* v_as_3659_, lean_object* v_sz_3660_, lean_object* v_i_3661_, lean_object* v_b_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_){
_start:
{
size_t v_sz_boxed_3666_; size_t v_i_boxed_3667_; lean_object* v_res_3668_; 
v_sz_boxed_3666_ = lean_unbox_usize(v_sz_3660_);
lean_dec(v_sz_3660_);
v_i_boxed_3667_ = lean_unbox_usize(v_i_3661_);
lean_dec(v_i_3661_);
v_res_3668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__11_spec__25_spec__37_spec__50(v_as_3659_, v_sz_boxed_3666_, v_i_boxed_3667_, v_b_3662_, v___y_3663_, v___y_3664_);
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
lean_dec_ref(v_as_3659_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23_spec__34_spec__43(lean_object* v_00_u03b2_3669_, lean_object* v_x_3670_, lean_object* v_x_3671_){
_start:
{
lean_object* v___x_3672_; 
v___x_3672_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__17_spec__23_spec__34_spec__43___redArg(v_x_3670_, v_x_3671_);
return v___x_3672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__39_spec__48(uint8_t v___x_3673_, lean_object* v_as_3674_, size_t v_sz_3675_, size_t v_i_3676_, lean_object* v_b_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_){
_start:
{
lean_object* v___x_3681_; 
v___x_3681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__39_spec__48___redArg(v___x_3673_, v_as_3674_, v_sz_3675_, v_i_3676_, v_b_3677_, v___y_3678_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__39_spec__48___boxed(lean_object* v___x_3682_, lean_object* v_as_3683_, lean_object* v_sz_3684_, lean_object* v_i_3685_, lean_object* v_b_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_){
_start:
{
uint8_t v___x_40095__boxed_3690_; size_t v_sz_boxed_3691_; size_t v_i_boxed_3692_; lean_object* v_res_3693_; 
v___x_40095__boxed_3690_ = lean_unbox(v___x_3682_);
v_sz_boxed_3691_ = lean_unbox_usize(v_sz_3684_);
lean_dec(v_sz_3684_);
v_i_boxed_3692_ = lean_unbox_usize(v_i_3685_);
lean_dec(v_i_3685_);
v_res_3693_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__9_spec__18_spec__26_spec__39_spec__48(v___x_40095__boxed_3690_, v_as_3683_, v_sz_boxed_3691_, v_i_boxed_3692_, v_b_3686_, v___y_3687_, v___y_3688_);
lean_dec(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec_ref(v_as_3683_);
return v_res_3693_;
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
