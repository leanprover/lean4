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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_importModulesCore(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*);
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
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_instDecidableEqOLeanLevel(uint8_t, uint8_t);
lean_object* l_Lean_finalizeImport(lean_object*, lean_object*, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecls();
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_toName(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_setOption(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_IO_println___at___00Lean_Environment_displayStats_spec__1(lean_object*);
lean_object* l_Lean_ModuleSetup_load(lean_object*);
lean_object* l_Lean_LeanOptions_toOptions(lean_object*);
lean_object* l_Lean_getBuildDir();
lean_object* l_Lean_initSearchPath(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedClassState_default;
extern lean_object* l_Lean_Meta_Match_Extension_instInhabitedState;
extern lean_object* l_Lean_Compiler_compiler_inLeanIR;
lean_object* l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_maxHeartbeats;
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_saveModuleData(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* lean_io_get_num_heartbeats();
extern lean_object* l_Lean_diagnostics;
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Compiler_LCNF_emitC(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_io_prim_handle_write(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
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
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedError;
lean_object* l_instInhabitedEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_firstFrontendMacroScope;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanIR_0__setConfigOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "invalid trailing argument `"};
static const lean_object* l___private_LeanIR_0__setConfigOption___closed__0 = (const lean_object*)&l___private_LeanIR_0__setConfigOption___closed__0_value;
static const lean_string_object l___private_LeanIR_0__setConfigOption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "`, expected argument of the form `-Dopt=val`"};
static const lean_object* l___private_LeanIR_0__setConfigOption___closed__1 = (const lean_object*)&l___private_LeanIR_0__setConfigOption___closed__1_value;
static const lean_string_object l___private_LeanIR_0__setConfigOption___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-D"};
static const lean_object* l___private_LeanIR_0__setConfigOption___closed__2 = (const lean_object*)&l___private_LeanIR_0__setConfigOption___closed__2_value;
static lean_once_cell_t l___private_LeanIR_0__setConfigOption___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanIR_0__setConfigOption___closed__3;
static const lean_string_object l___private_LeanIR_0__setConfigOption___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unknown option '"};
static const lean_object* l___private_LeanIR_0__setConfigOption___closed__4 = (const lean_object*)&l___private_LeanIR_0__setConfigOption___closed__4_value;
static const lean_string_object l___private_LeanIR_0__setConfigOption___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_LeanIR_0__setConfigOption___closed__5 = (const lean_object*)&l___private_LeanIR_0__setConfigOption___closed__5_value;
static const lean_string_object l___private_LeanIR_0__setConfigOption___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "invalid -D parameter, argument must contain '='"};
static const lean_object* l___private_LeanIR_0__setConfigOption___closed__6 = (const lean_object*)&l___private_LeanIR_0__setConfigOption___closed__6_value;
static const lean_ctor_object l___private_LeanIR_0__setConfigOption___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanIR_0__setConfigOption___closed__6_value)}};
static const lean_object* l___private_LeanIR_0__setConfigOption___closed__7 = (const lean_object*)&l___private_LeanIR_0__setConfigOption___closed__7_value;
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_main___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_main___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_main___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l_main___lam__1___closed__0 = (const lean_object*)&l_main___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_main___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
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
static const lean_string_object l_main___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ir"};
static const lean_object* l_main___closed__11 = (const lean_object*)&l_main___closed__11_value;
static const lean_ctor_object l_main___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__11_value),LEAN_SCALAR_PTR_LITERAL(157, 0, 67, 166, 172, 92, 38, 85)}};
static const lean_object* l_main___closed__12 = (const lean_object*)&l_main___closed__12_value;
static const lean_string_object l_main___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "C code generation"};
static const lean_object* l_main___closed__13 = (const lean_object*)&l_main___closed__13_value;
static lean_once_cell_t l_main___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__14;
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
static lean_once_cell_t l_main___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__30;
static lean_once_cell_t l_main___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__31;
static const lean_array_object l_main___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___closed__32 = (const lean_object*)&l_main___closed__32_value;
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1(lean_object* v_a_1_, lean_object* v_as_2_, size_t v_i_3_, size_t v_stop_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_usize_dec_eq(v_i_3_, v_stop_4_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_6_ = lean_array_uget_borrowed(v_as_2_, v_i_3_);
v___x_7_ = lean_name_eq(v_a_1_, v___x_6_);
if (v___x_7_ == 0)
{
size_t v___x_8_; size_t v___x_9_; 
v___x_8_ = ((size_t)1ULL);
v___x_9_ = lean_usize_add(v_i_3_, v___x_8_);
v_i_3_ = v___x_9_;
goto _start;
}
else
{
return v___x_7_;
}
}
else
{
uint8_t v___x_11_; 
v___x_11_ = 0;
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1___boxed(lean_object* v_a_12_, lean_object* v_as_13_, lean_object* v_i_14_, lean_object* v_stop_15_){
_start:
{
size_t v_i_boxed_16_; size_t v_stop_boxed_17_; uint8_t v_res_18_; lean_object* v_r_19_; 
v_i_boxed_16_ = lean_unbox_usize(v_i_14_);
lean_dec(v_i_14_);
v_stop_boxed_17_ = lean_unbox_usize(v_stop_15_);
lean_dec(v_stop_15_);
v_res_18_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1(v_a_12_, v_as_13_, v_i_boxed_16_, v_stop_boxed_17_);
lean_dec_ref(v_as_13_);
lean_dec(v_a_12_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1(lean_object* v_as_20_, lean_object* v_a_21_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_22_ = lean_unsigned_to_nat(0u);
v___x_23_ = lean_array_get_size(v_as_20_);
v___x_24_ = lean_nat_dec_lt(v___x_22_, v___x_23_);
if (v___x_24_ == 0)
{
return v___x_24_;
}
else
{
if (v___x_24_ == 0)
{
return v___x_24_;
}
else
{
size_t v___x_25_; size_t v___x_26_; uint8_t v___x_27_; 
v___x_25_ = ((size_t)0ULL);
v___x_26_ = lean_usize_of_nat(v___x_23_);
v___x_27_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1(v_a_21_, v_as_20_, v___x_25_, v___x_26_);
return v___x_27_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1___boxed(lean_object* v_as_28_, lean_object* v_a_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1(v_as_28_, v_a_29_);
lean_dec(v_a_29_);
lean_dec_ref(v_as_28_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(lean_object* v_irExtNames_32_, lean_object* v_as_33_, size_t v_i_34_, size_t v_stop_35_, lean_object* v_b_36_){
_start:
{
lean_object* v___y_38_; uint8_t v___x_42_; 
v___x_42_ = lean_usize_dec_eq(v_i_34_, v_stop_35_);
if (v___x_42_ == 0)
{
lean_object* v___x_43_; lean_object* v_fst_44_; uint8_t v___x_45_; 
v___x_43_ = lean_array_uget_borrowed(v_as_33_, v_i_34_);
v_fst_44_ = lean_ctor_get(v___x_43_, 0);
v___x_45_ = l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1(v_irExtNames_32_, v_fst_44_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; 
lean_inc(v___x_43_);
v___x_46_ = lean_array_push(v_b_36_, v___x_43_);
v___y_38_ = v___x_46_;
goto v___jp_37_;
}
else
{
v___y_38_ = v_b_36_;
goto v___jp_37_;
}
}
else
{
return v_b_36_;
}
v___jp_37_:
{
size_t v___x_39_; size_t v___x_40_; 
v___x_39_ = ((size_t)1ULL);
v___x_40_ = lean_usize_add(v_i_34_, v___x_39_);
v_i_34_ = v___x_40_;
v_b_36_ = v___y_38_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2___boxed(lean_object* v_irExtNames_47_, lean_object* v_as_48_, lean_object* v_i_49_, lean_object* v_stop_50_, lean_object* v_b_51_){
_start:
{
size_t v_i_boxed_52_; size_t v_stop_boxed_53_; lean_object* v_res_54_; 
v_i_boxed_52_ = lean_unbox_usize(v_i_49_);
lean_dec(v_i_49_);
v_stop_boxed_53_ = lean_unbox_usize(v_stop_50_);
lean_dec(v_stop_50_);
v_res_54_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(v_irExtNames_47_, v_as_48_, v_i_boxed_52_, v_stop_boxed_53_, v_b_51_);
lean_dec_ref(v_as_48_);
lean_dec_ref(v_irExtNames_47_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0(size_t v_sz_55_, size_t v_i_56_, lean_object* v_bs_57_){
_start:
{
uint8_t v___x_58_; 
v___x_58_ = lean_usize_dec_lt(v_i_56_, v_sz_55_);
if (v___x_58_ == 0)
{
return v_bs_57_;
}
else
{
lean_object* v_v_59_; lean_object* v_fst_60_; lean_object* v___x_61_; lean_object* v_bs_x27_62_; size_t v___x_63_; size_t v___x_64_; lean_object* v___x_65_; 
v_v_59_ = lean_array_uget_borrowed(v_bs_57_, v_i_56_);
v_fst_60_ = lean_ctor_get(v_v_59_, 0);
lean_inc(v_fst_60_);
v___x_61_ = lean_unsigned_to_nat(0u);
v_bs_x27_62_ = lean_array_uset(v_bs_57_, v_i_56_, v___x_61_);
v___x_63_ = ((size_t)1ULL);
v___x_64_ = lean_usize_add(v_i_56_, v___x_63_);
v___x_65_ = lean_array_uset(v_bs_x27_62_, v_i_56_, v_fst_60_);
v_i_56_ = v___x_64_;
v_bs_57_ = v___x_65_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0___boxed(lean_object* v_sz_67_, lean_object* v_i_68_, lean_object* v_bs_69_){
_start:
{
size_t v_sz_boxed_70_; size_t v_i_boxed_71_; lean_object* v_res_72_; 
v_sz_boxed_70_ = lean_unbox_usize(v_sz_67_);
lean_dec(v_sz_67_);
v_i_boxed_71_ = lean_unbox_usize(v_i_68_);
lean_dec(v_i_68_);
v_res_72_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0(v_sz_boxed_70_, v_i_boxed_71_, v_bs_69_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__mkIRData(lean_object* v_env_77_){
_start:
{
lean_object* v_irEntries_79_; uint8_t v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
lean_inc_ref_n(v_env_77_, 2);
v_irEntries_79_ = lean_ir_export_entries(v_env_77_);
v___x_80_ = 2;
v___x_81_ = lean_box(0);
v___x_82_ = l_Lean_mkModuleData(v_env_77_, v___x_80_, v___x_81_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v_a_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_113_; 
v_a_83_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_113_ == 0)
{
v___x_85_ = v___x_82_;
v_isShared_86_ = v_isSharedCheck_113_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_a_83_);
lean_dec(v___x_82_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_113_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___y_88_; lean_object* v_entries_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v_entries_100_ = lean_ctor_get(v_a_83_, 4);
lean_inc_ref(v_entries_100_);
lean_dec(v_a_83_);
v___x_101_ = lean_unsigned_to_nat(0u);
v___x_102_ = lean_array_get_size(v_entries_100_);
v___x_103_ = ((lean_object*)(l___private_LeanIR_0__mkIRData___closed__1));
v___x_104_ = lean_nat_dec_lt(v___x_101_, v___x_102_);
if (v___x_104_ == 0)
{
lean_dec_ref(v_entries_100_);
v___y_88_ = v___x_103_;
goto v___jp_87_;
}
else
{
size_t v_sz_105_; size_t v___x_106_; lean_object* v_irExtNames_107_; uint8_t v___x_108_; 
v_sz_105_ = lean_array_size(v_irEntries_79_);
v___x_106_ = ((size_t)0ULL);
lean_inc_ref(v_irEntries_79_);
v_irExtNames_107_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0(v_sz_105_, v___x_106_, v_irEntries_79_);
v___x_108_ = lean_nat_dec_le(v___x_102_, v___x_102_);
if (v___x_108_ == 0)
{
if (v___x_104_ == 0)
{
lean_dec_ref(v_irExtNames_107_);
lean_dec_ref(v_entries_100_);
v___y_88_ = v___x_103_;
goto v___jp_87_;
}
else
{
size_t v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_usize_of_nat(v___x_102_);
v___x_110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(v_irExtNames_107_, v_entries_100_, v___x_106_, v___x_109_, v___x_103_);
lean_dec_ref(v_entries_100_);
lean_dec_ref(v_irExtNames_107_);
v___y_88_ = v___x_110_;
goto v___jp_87_;
}
}
else
{
size_t v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_usize_of_nat(v___x_102_);
v___x_112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(v_irExtNames_107_, v_entries_100_, v___x_106_, v___x_111_, v___x_103_);
lean_dec_ref(v_entries_100_);
lean_dec_ref(v_irExtNames_107_);
v___y_88_ = v___x_112_;
goto v___jp_87_;
}
}
v___jp_87_:
{
lean_object* v___x_89_; uint8_t v_isModule_90_; lean_object* v_imports_91_; lean_object* v___x_92_; uint8_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_89_ = l_Lean_Environment_header(v_env_77_);
v_isModule_90_ = lean_ctor_get_uint8(v___x_89_, sizeof(void*)*7 + 4);
v_imports_91_ = lean_ctor_get(v___x_89_, 1);
lean_inc_ref(v_imports_91_);
lean_dec_ref(v___x_89_);
v___x_92_ = ((lean_object*)(l___private_LeanIR_0__mkIRData___closed__0));
v___x_93_ = 1;
v___x_94_ = lean_get_ir_extra_const_names(v_env_77_, v___x_80_, v___x_93_);
v___x_95_ = l_Array_append___redArg(v_irEntries_79_, v___y_88_);
lean_dec_ref(v___y_88_);
v___x_96_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_96_, 0, v_imports_91_);
lean_ctor_set(v___x_96_, 1, v___x_92_);
lean_ctor_set(v___x_96_, 2, v___x_92_);
lean_ctor_set(v___x_96_, 3, v___x_94_);
lean_ctor_set(v___x_96_, 4, v___x_95_);
lean_ctor_set_uint8(v___x_96_, sizeof(void*)*5, v_isModule_90_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_96_);
v___x_98_ = v___x_85_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
else
{
lean_dec_ref(v_irEntries_79_);
lean_dec_ref(v_env_77_);
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__mkIRData___boxed(lean_object* v_env_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l___private_LeanIR_0__mkIRData(v_env_114_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(lean_object* v_arg_117_, lean_object* v___x_118_, lean_object* v_arg_119_, lean_object* v_a_120_, lean_object* v_b_121_){
_start:
{
lean_object* v_startInclusive_122_; lean_object* v_endExclusive_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v_startInclusive_122_ = lean_ctor_get(v_arg_117_, 1);
v_endExclusive_123_ = lean_ctor_get(v_arg_117_, 2);
v___x_124_ = lean_nat_sub(v_endExclusive_123_, v_startInclusive_122_);
v___x_125_ = lean_nat_dec_eq(v_a_120_, v___x_124_);
lean_dec(v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; uint32_t v___x_127_; uint32_t v___x_128_; uint8_t v___x_129_; 
v___x_126_ = lean_nat_add(v___x_118_, v_a_120_);
v___x_127_ = lean_string_utf8_get_fast(v_arg_119_, v___x_126_);
v___x_128_ = 61;
v___x_129_ = lean_uint32_dec_eq(v___x_127_, v___x_128_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
lean_dec(v_a_120_);
v___x_130_ = lean_box(0);
v___x_131_ = lean_string_utf8_next_fast(v_arg_119_, v___x_126_);
lean_dec(v___x_126_);
v___x_132_ = lean_nat_sub(v___x_131_, v___x_118_);
v_a_120_ = v___x_132_;
v_b_121_ = v___x_130_;
goto _start;
}
else
{
lean_object* v___x_134_; 
lean_dec(v___x_126_);
v___x_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_134_, 0, v_a_120_);
return v___x_134_;
}
}
else
{
lean_dec(v_a_120_);
lean_inc(v_b_121_);
return v_b_121_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___boxed(lean_object* v_arg_135_, lean_object* v___x_136_, lean_object* v_arg_137_, lean_object* v_a_138_, lean_object* v_b_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(v_arg_135_, v___x_136_, v_arg_137_, v_a_138_, v_b_139_);
lean_dec(v_b_139_);
lean_dec_ref(v_arg_137_);
lean_dec(v___x_136_);
lean_dec_ref(v_arg_135_);
return v_res_140_;
}
}
static lean_object* _init_l___private_LeanIR_0__setConfigOption___closed__3(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__2));
v___x_145_ = lean_string_utf8_byte_size(v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption(lean_object* v_opts_151_, lean_object* v_arg_152_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_161_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__2));
v___x_162_ = lean_string_utf8_byte_size(v_arg_152_);
v___x_163_ = lean_obj_once(&l___private_LeanIR_0__setConfigOption___closed__3, &l___private_LeanIR_0__setConfigOption___closed__3_once, _init_l___private_LeanIR_0__setConfigOption___closed__3);
v___x_164_ = lean_nat_dec_le(v___x_163_, v___x_162_);
if (v___x_164_ == 0)
{
lean_dec_ref(v_opts_151_);
goto v___jp_154_;
}
else
{
lean_object* v_searcher_165_; uint8_t v___x_166_; 
v_searcher_165_ = lean_unsigned_to_nat(0u);
v___x_166_ = lean_string_memcmp(v_arg_152_, v___x_161_, v_searcher_165_, v_searcher_165_, v___x_163_);
if (v___x_166_ == 0)
{
lean_dec_ref(v_opts_151_);
goto v___jp_154_;
}
else
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___y_171_; lean_object* v_arg_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_167_ = lean_unsigned_to_nat(2u);
lean_inc_ref_n(v_arg_152_, 2);
v___x_168_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_168_, 0, v_arg_152_);
lean_ctor_set(v___x_168_, 1, v_searcher_165_);
lean_ctor_set(v___x_168_, 2, v___x_162_);
v___x_169_ = l_String_Slice_Pos_nextn(v___x_168_, v_searcher_165_, v___x_167_);
lean_dec_ref(v___x_168_);
lean_inc(v___x_169_);
v_arg_209_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_arg_209_, 0, v_arg_152_);
lean_ctor_set(v_arg_209_, 1, v___x_169_);
lean_ctor_set(v_arg_209_, 2, v___x_162_);
v___x_210_ = lean_box(0);
v___x_211_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(v_arg_209_, v___x_169_, v_arg_152_, v_searcher_165_, v___x_210_);
lean_dec_ref(v_arg_209_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v___x_212_; 
v___x_212_ = lean_nat_sub(v___x_162_, v___x_169_);
v___y_171_ = v___x_212_;
goto v___jp_170_;
}
else
{
lean_object* v_val_213_; 
v_val_213_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_val_213_);
lean_dec_ref(v___x_211_);
v___y_171_ = v_val_213_;
goto v___jp_170_;
}
v___jp_170_:
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = lean_nat_sub(v___x_162_, v___x_169_);
v___x_173_ = lean_nat_dec_eq(v___y_171_, v___x_172_);
lean_dec(v___x_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; 
v___x_174_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_198_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_198_ == 0)
{
v___x_177_ = v___x_174_;
v_isShared_178_ = v_isSharedCheck_198_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_174_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_198_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v_name_181_; lean_object* v___x_182_; 
v___x_179_ = lean_nat_add(v___x_169_, v___y_171_);
lean_dec(v___y_171_);
lean_inc(v___x_179_);
lean_inc(v___x_169_);
lean_inc_ref(v_arg_152_);
v___x_180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_180_, 0, v_arg_152_);
lean_ctor_set(v___x_180_, 1, v___x_169_);
lean_ctor_set(v___x_180_, 2, v___x_179_);
v_name_181_ = l_String_Slice_toName(v___x_180_);
lean_dec_ref(v___x_180_);
v___x_182_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_175_, v_name_181_);
lean_dec(v_a_175_);
if (lean_obj_tag(v___x_182_) == 1)
{
lean_object* v_val_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v_val_187_; lean_object* v___x_188_; 
lean_del_object(v___x_177_);
v_val_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_val_183_);
lean_dec_ref(v___x_182_);
v___x_184_ = lean_string_utf8_next_fast(v_arg_152_, v___x_179_);
lean_dec(v___x_179_);
v___x_185_ = lean_nat_sub(v___x_184_, v___x_169_);
v___x_186_ = lean_nat_add(v___x_169_, v___x_185_);
lean_dec(v___x_185_);
lean_dec(v___x_169_);
v_val_187_ = lean_string_utf8_extract(v_arg_152_, v___x_186_, v___x_162_);
lean_dec(v___x_186_);
lean_dec_ref(v_arg_152_);
v___x_188_ = l_Lean_Language_Lean_setOption(v_opts_151_, v_val_183_, v_name_181_, v_val_187_);
return v___x_188_;
}
else
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_196_; 
lean_dec(v___x_182_);
lean_dec(v___x_179_);
lean_dec(v___x_169_);
lean_dec_ref(v_arg_152_);
lean_dec_ref(v_opts_151_);
v___x_189_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__4));
v___x_190_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_181_, v___x_166_);
v___x_191_ = lean_string_append(v___x_189_, v___x_190_);
lean_dec_ref(v___x_190_);
v___x_192_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__5));
v___x_193_ = lean_string_append(v___x_191_, v___x_192_);
v___x_194_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
if (v_isShared_178_ == 0)
{
lean_ctor_set_tag(v___x_177_, 1);
lean_ctor_set(v___x_177_, 0, v___x_194_);
v___x_196_ = v___x_177_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
lean_dec(v___y_171_);
lean_dec(v___x_169_);
lean_dec_ref(v_arg_152_);
lean_dec_ref(v_opts_151_);
v_a_199_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_174_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_174_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
else
{
lean_object* v___x_207_; lean_object* v___x_208_; 
lean_dec(v___y_171_);
lean_dec(v___x_169_);
lean_dec_ref(v_arg_152_);
lean_dec_ref(v_opts_151_);
v___x_207_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__7));
v___x_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
return v___x_208_;
}
}
}
}
v___jp_154_:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_155_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__0));
v___x_156_ = lean_string_append(v___x_155_, v_arg_152_);
lean_dec_ref(v_arg_152_);
v___x_157_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__1));
v___x_158_ = lean_string_append(v___x_156_, v___x_157_);
v___x_159_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
v___x_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption___boxed(lean_object* v_opts_214_, lean_object* v_arg_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l___private_LeanIR_0__setConfigOption(v_opts_214_, v_arg_215_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0(lean_object* v_arg_218_, lean_object* v___x_219_, lean_object* v_arg_220_, lean_object* v_inst_221_, lean_object* v_R_222_, lean_object* v_a_223_, lean_object* v_b_224_, lean_object* v_c_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(v_arg_218_, v___x_219_, v_arg_220_, v_a_223_, v_b_224_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___boxed(lean_object* v_arg_227_, lean_object* v___x_228_, lean_object* v_arg_229_, lean_object* v_inst_230_, lean_object* v_R_231_, lean_object* v_a_232_, lean_object* v_b_233_, lean_object* v_c_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0(v_arg_227_, v___x_228_, v_arg_229_, v_inst_230_, v_R_231_, v_a_232_, v_b_233_, v_c_234_);
lean_dec(v_b_233_);
lean_dec_ref(v_arg_229_);
lean_dec(v___x_228_);
lean_dec_ref(v_arg_227_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg(lean_object* v___x_236_, lean_object* v_inst_237_, lean_object* v_ext_238_, lean_object* v_env_239_){
_start:
{
lean_object* v_toEnvExtension_241_; lean_object* v_addImportedFn_242_; lean_object* v_asyncMode_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v_importedEntries_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_274_; 
v_toEnvExtension_241_ = lean_ctor_get(v_ext_238_, 0);
lean_inc_ref(v_toEnvExtension_241_);
v_addImportedFn_242_ = lean_ctor_get(v_ext_238_, 2);
lean_inc_ref(v_addImportedFn_242_);
lean_dec_ref(v_ext_238_);
v_asyncMode_243_ = lean_ctor_get(v_toEnvExtension_241_, 2);
v___x_244_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v_inst_237_);
lean_inc_ref(v_env_239_);
v___x_245_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_244_, v_toEnvExtension_241_, v_env_239_, v_asyncMode_243_, v___x_236_);
lean_dec_ref(v___x_244_);
v_importedEntries_246_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_274_ == 0)
{
lean_object* v_unused_275_; 
v_unused_275_ = lean_ctor_get(v___x_245_, 1);
lean_dec(v_unused_275_);
v___x_248_ = v___x_245_;
v_isShared_249_ = v_isSharedCheck_274_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_importedEntries_246_);
lean_dec(v___x_245_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_274_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_250_ = l_Lean_Options_empty;
lean_inc_ref(v_env_239_);
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v_env_239_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
lean_inc_ref(v_importedEntries_246_);
v___x_252_ = lean_apply_3(v_addImportedFn_242_, v_importedEntries_246_, v___x_251_, lean_box(0));
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_265_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_265_ == 0)
{
v___x_255_ = v___x_252_;
v_isShared_256_ = v_isSharedCheck_265_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_252_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_265_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 1, v_a_253_);
v___x_258_ = v___x_248_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_importedEntries_246_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v_a_253_);
v___x_258_ = v_reuseFailAlloc_264_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_259_ = lean_box(0);
v___x_260_ = l_Lean_EnvExtension_setState___redArg(v_toEnvExtension_241_, v_env_239_, v___x_258_, v___x_259_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 0, v___x_260_);
v___x_262_ = v___x_255_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
else
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
lean_del_object(v___x_248_);
lean_dec_ref(v_importedEntries_246_);
lean_dec_ref(v_toEnvExtension_241_);
lean_dec_ref(v_env_239_);
v_a_266_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_273_ == 0)
{
v___x_268_ = v___x_252_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_252_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_266_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg___boxed(lean_object* v___x_276_, lean_object* v_inst_277_, lean_object* v_ext_278_, lean_object* v_env_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_main___elam__0___redArg(v___x_276_, v_inst_277_, v_ext_278_, v_env_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0(lean_object* v___x_282_, lean_object* v_00_u03b1_283_, lean_object* v_00_u03b2_284_, lean_object* v_00_u03c3_285_, lean_object* v_inst_286_, lean_object* v_ext_287_, lean_object* v_env_288_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_main___elam__0___redArg(v___x_282_, v_inst_286_, v_ext_287_, v_env_288_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___boxed(lean_object* v___x_291_, lean_object* v_00_u03b1_292_, lean_object* v_00_u03b2_293_, lean_object* v_00_u03c3_294_, lean_object* v_inst_295_, lean_object* v_ext_296_, lean_object* v_env_297_, lean_object* v___y_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_main___elam__0(v___x_291_, v_00_u03b1_292_, v_00_u03b2_293_, v_00_u03c3_294_, v_inst_295_, v_ext_296_, v_env_297_);
return v_res_299_;
}
}
static lean_object* _init_l_panic___at___00main_spec__5___closed__0(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = l_instInhabitedError;
v___x_301_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_301_, 0, lean_box(0));
lean_closure_set(v___x_301_, 1, lean_box(0));
lean_closure_set(v___x_301_, 2, v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5(lean_object* v_msg_302_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_20091__overap_305_; lean_object* v___x_306_; 
v___x_304_ = lean_obj_once(&l_panic___at___00main_spec__5___closed__0, &l_panic___at___00main_spec__5___closed__0_once, _init_l_panic___at___00main_spec__5___closed__0);
v___x_20091__overap_305_ = lean_panic_fn_borrowed(v___x_304_, v_msg_302_);
v___x_306_ = lean_apply_1(v___x_20091__overap_305_, lean_box(0));
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5___boxed(lean_object* v_msg_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_panic___at___00main_spec__5(v_msg_307_);
return v_res_309_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00main_spec__8(lean_object* v_opts_310_, lean_object* v_opt_311_){
_start:
{
lean_object* v_name_312_; lean_object* v_defValue_313_; lean_object* v_map_314_; lean_object* v___x_315_; 
v_name_312_ = lean_ctor_get(v_opt_311_, 0);
v_defValue_313_ = lean_ctor_get(v_opt_311_, 1);
v_map_314_ = lean_ctor_get(v_opts_310_, 0);
v___x_315_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_314_, v_name_312_);
if (lean_obj_tag(v___x_315_) == 0)
{
uint8_t v___x_316_; 
v___x_316_ = lean_unbox(v_defValue_313_);
return v___x_316_;
}
else
{
lean_object* v_val_317_; 
v_val_317_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_val_317_);
lean_dec_ref(v___x_315_);
if (lean_obj_tag(v_val_317_) == 1)
{
uint8_t v_v_318_; 
v_v_318_ = lean_ctor_get_uint8(v_val_317_, 0);
lean_dec_ref(v_val_317_);
return v_v_318_;
}
else
{
uint8_t v___x_319_; 
lean_dec(v_val_317_);
v___x_319_ = lean_unbox(v_defValue_313_);
return v___x_319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8___boxed(lean_object* v_opts_320_, lean_object* v_opt_321_){
_start:
{
uint8_t v_res_322_; lean_object* v_r_323_; 
v_res_322_ = l_Lean_Option_get___at___00main_spec__8(v_opts_320_, v_opt_321_);
lean_dec_ref(v_opt_321_);
lean_dec_ref(v_opts_320_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__9(lean_object* v_opts_324_, lean_object* v_opt_325_){
_start:
{
lean_object* v_name_326_; lean_object* v_defValue_327_; lean_object* v_map_328_; lean_object* v___x_329_; 
v_name_326_ = lean_ctor_get(v_opt_325_, 0);
v_defValue_327_ = lean_ctor_get(v_opt_325_, 1);
v_map_328_ = lean_ctor_get(v_opts_324_, 0);
v___x_329_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_328_, v_name_326_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_inc(v_defValue_327_);
return v_defValue_327_;
}
else
{
lean_object* v_val_330_; 
v_val_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_val_330_);
lean_dec_ref(v___x_329_);
if (lean_obj_tag(v_val_330_) == 3)
{
lean_object* v_v_331_; 
v_v_331_ = lean_ctor_get(v_val_330_, 0);
lean_inc(v_v_331_);
lean_dec_ref(v_val_330_);
return v_v_331_;
}
else
{
lean_dec(v_val_330_);
lean_inc(v_defValue_327_);
return v_defValue_327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__9___boxed(lean_object* v_opts_332_, lean_object* v_opt_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Option_get___at___00main_spec__9(v_opts_332_, v_opt_333_);
lean_dec_ref(v_opt_333_);
lean_dec_ref(v_opts_332_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(lean_object* v___x_335_, lean_object* v_a_336_, lean_object* v_x_337_){
_start:
{
if (lean_obj_tag(v_x_337_) == 0)
{
lean_dec(v_a_336_);
return v_x_337_;
}
else
{
lean_object* v_key_338_; lean_object* v_value_339_; lean_object* v_tail_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_387_; 
v_key_338_ = lean_ctor_get(v_x_337_, 0);
v_value_339_ = lean_ctor_get(v_x_337_, 1);
v_tail_340_ = lean_ctor_get(v_x_337_, 2);
v_isSharedCheck_387_ = !lean_is_exclusive(v_x_337_);
if (v_isSharedCheck_387_ == 0)
{
v___x_342_ = v_x_337_;
v_isShared_343_ = v_isSharedCheck_387_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_tail_340_);
lean_inc(v_value_339_);
lean_inc(v_key_338_);
lean_dec(v_x_337_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_387_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
uint8_t v___x_344_; 
v___x_344_ = lean_name_eq(v_key_338_, v_a_336_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; lean_object* v___x_347_; 
v___x_345_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v___x_335_, v_a_336_, v_tail_340_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 2, v___x_345_);
v___x_347_ = v___x_342_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_key_338_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_value_339_);
lean_ctor_set(v_reuseFailAlloc_348_, 2, v___x_345_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
else
{
lean_object* v_toEffectiveImport_349_; lean_object* v_toImport_350_; lean_object* v_parts_351_; lean_object* v_irData_x3f_352_; uint8_t v_needsIRTrans_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_385_; 
lean_dec(v_key_338_);
v_toEffectiveImport_349_ = lean_ctor_get(v_value_339_, 0);
lean_inc_ref(v_toEffectiveImport_349_);
v_toImport_350_ = lean_ctor_get(v_toEffectiveImport_349_, 0);
lean_inc_ref(v_toImport_350_);
v_parts_351_ = lean_ctor_get(v_value_339_, 1);
v_irData_x3f_352_ = lean_ctor_get(v_value_339_, 2);
v_needsIRTrans_353_ = lean_ctor_get_uint8(v_value_339_, sizeof(void*)*3);
v_isSharedCheck_385_ = !lean_is_exclusive(v_value_339_);
if (v_isSharedCheck_385_ == 0)
{
lean_object* v_unused_386_; 
v_unused_386_ = lean_ctor_get(v_value_339_, 0);
lean_dec(v_unused_386_);
v___x_355_ = v_value_339_;
v_isShared_356_ = v_isSharedCheck_385_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_irData_x3f_352_);
lean_inc(v_parts_351_);
lean_dec(v_value_339_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_385_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
uint8_t v_hasData_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_383_; 
v_hasData_357_ = lean_ctor_get_uint8(v_toEffectiveImport_349_, sizeof(void*)*1 + 1);
v_isSharedCheck_383_ = !lean_is_exclusive(v_toEffectiveImport_349_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; 
v_unused_384_ = lean_ctor_get(v_toEffectiveImport_349_, 0);
lean_dec(v_unused_384_);
v___x_359_ = v_toEffectiveImport_349_;
v_isShared_360_ = v_isSharedCheck_383_;
goto v_resetjp_358_;
}
else
{
lean_dec(v_toEffectiveImport_349_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_383_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v_module_361_; uint8_t v___x_362_; 
v_module_361_ = lean_ctor_get(v_toImport_350_, 0);
v___x_362_ = lean_name_eq(v_module_361_, v___x_335_);
if (v___x_362_ == 0)
{
uint8_t v___x_363_; lean_object* v___x_365_; 
v___x_363_ = 2;
if (v_isShared_360_ == 0)
{
v___x_365_ = v___x_359_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_toImport_350_);
lean_ctor_set_uint8(v_reuseFailAlloc_372_, sizeof(void*)*1 + 1, v_hasData_357_);
v___x_365_ = v_reuseFailAlloc_372_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_367_; 
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*1, v___x_363_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 0, v___x_365_);
v___x_367_ = v___x_355_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_365_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_parts_351_);
lean_ctor_set(v_reuseFailAlloc_371_, 2, v_irData_x3f_352_);
lean_ctor_set_uint8(v_reuseFailAlloc_371_, sizeof(void*)*3, v_needsIRTrans_353_);
v___x_367_ = v_reuseFailAlloc_371_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_369_; 
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 1, v___x_367_);
lean_ctor_set(v___x_342_, 0, v_a_336_);
v___x_369_ = v___x_342_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_336_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_370_, 2, v_tail_340_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
else
{
uint8_t v___x_373_; lean_object* v___x_375_; 
v___x_373_ = 0;
if (v_isShared_360_ == 0)
{
v___x_375_ = v___x_359_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_toImport_350_);
lean_ctor_set_uint8(v_reuseFailAlloc_382_, sizeof(void*)*1 + 1, v_hasData_357_);
v___x_375_ = v_reuseFailAlloc_382_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_377_; 
lean_ctor_set_uint8(v___x_375_, sizeof(void*)*1, v___x_373_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 0, v___x_375_);
v___x_377_ = v___x_355_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_parts_351_);
lean_ctor_set(v_reuseFailAlloc_381_, 2, v_irData_x3f_352_);
lean_ctor_set_uint8(v_reuseFailAlloc_381_, sizeof(void*)*3, v_needsIRTrans_353_);
v___x_377_ = v_reuseFailAlloc_381_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_379_; 
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 1, v___x_377_);
lean_ctor_set(v___x_342_, 0, v_a_336_);
v___x_379_ = v___x_342_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_336_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v___x_377_);
lean_ctor_set(v_reuseFailAlloc_380_, 2, v_tail_340_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5___boxed(lean_object* v___x_388_, lean_object* v_a_389_, lean_object* v_x_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v___x_388_, v_a_389_, v_x_390_);
lean_dec(v___x_388_);
return v_res_391_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0(void){
_start:
{
lean_object* v___x_392_; uint64_t v___x_393_; 
v___x_392_ = lean_unsigned_to_nat(1723u);
v___x_393_ = lean_uint64_of_nat(v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(lean_object* v___x_394_, lean_object* v_m_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_size_397_; lean_object* v_buckets_398_; lean_object* v___x_399_; uint64_t v___y_401_; 
v_size_397_ = lean_ctor_get(v_m_395_, 0);
v_buckets_398_ = lean_ctor_get(v_m_395_, 1);
v___x_399_ = lean_array_get_size(v_buckets_398_);
if (lean_obj_tag(v_a_396_) == 0)
{
uint64_t v___x_428_; 
v___x_428_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0);
v___y_401_ = v___x_428_;
goto v___jp_400_;
}
else
{
uint64_t v_hash_429_; 
v_hash_429_ = lean_ctor_get_uint64(v_a_396_, sizeof(void*)*2);
v___y_401_ = v_hash_429_;
goto v___jp_400_;
}
v___jp_400_:
{
uint64_t v___x_402_; uint64_t v___x_403_; uint64_t v_fold_404_; uint64_t v___x_405_; uint64_t v___x_406_; uint64_t v___x_407_; size_t v___x_408_; size_t v___x_409_; size_t v___x_410_; size_t v___x_411_; size_t v___x_412_; lean_object* v_bucket_413_; uint8_t v___x_414_; 
v___x_402_ = 32ULL;
v___x_403_ = lean_uint64_shift_right(v___y_401_, v___x_402_);
v_fold_404_ = lean_uint64_xor(v___y_401_, v___x_403_);
v___x_405_ = 16ULL;
v___x_406_ = lean_uint64_shift_right(v_fold_404_, v___x_405_);
v___x_407_ = lean_uint64_xor(v_fold_404_, v___x_406_);
v___x_408_ = lean_uint64_to_usize(v___x_407_);
v___x_409_ = lean_usize_of_nat(v___x_399_);
v___x_410_ = ((size_t)1ULL);
v___x_411_ = lean_usize_sub(v___x_409_, v___x_410_);
v___x_412_ = lean_usize_land(v___x_408_, v___x_411_);
v_bucket_413_ = lean_array_uget_borrowed(v_buckets_398_, v___x_412_);
v___x_414_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_a_396_, v_bucket_413_);
if (v___x_414_ == 0)
{
lean_dec(v_a_396_);
return v_m_395_;
}
else
{
lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_425_; 
lean_inc(v_bucket_413_);
lean_inc_ref(v_buckets_398_);
lean_inc(v_size_397_);
v_isSharedCheck_425_ = !lean_is_exclusive(v_m_395_);
if (v_isSharedCheck_425_ == 0)
{
lean_object* v_unused_426_; lean_object* v_unused_427_; 
v_unused_426_ = lean_ctor_get(v_m_395_, 1);
lean_dec(v_unused_426_);
v_unused_427_ = lean_ctor_get(v_m_395_, 0);
lean_dec(v_unused_427_);
v___x_416_ = v_m_395_;
v_isShared_417_ = v_isSharedCheck_425_;
goto v_resetjp_415_;
}
else
{
lean_dec(v_m_395_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_425_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v_buckets_419_; lean_object* v_bucket_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_418_ = lean_box(0);
v_buckets_419_ = lean_array_uset(v_buckets_398_, v___x_412_, v___x_418_);
v_bucket_420_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v___x_394_, v_a_396_, v_bucket_413_);
v___x_421_ = lean_array_uset(v_buckets_419_, v___x_412_, v_bucket_420_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 1, v___x_421_);
v___x_423_ = v___x_416_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_size_397_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___boxed(lean_object* v___x_430_, lean_object* v_m_431_, lean_object* v_a_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(v___x_430_, v_m_431_, v_a_432_);
lean_dec(v___x_430_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_main___lam__0(lean_object* v___x_434_, lean_object* v___x_435_, uint8_t v___x_436_, lean_object* v___x_437_, uint8_t v___y_438_, lean_object* v_name_439_, lean_object* v___x_440_, uint8_t v___x_441_, uint8_t v___x_442_){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_st_mk_ref(v___x_434_);
v___x_445_ = l_Lean_importModulesCore(v___x_435_, v___x_436_, v___x_437_, v___y_438_, v___x_444_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v___x_446_; lean_object* v_moduleNameMap_447_; lean_object* v_moduleNames_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_461_; 
lean_dec_ref(v___x_445_);
v___x_446_ = lean_st_ref_get(v___x_444_);
lean_dec(v___x_444_);
v_moduleNameMap_447_ = lean_ctor_get(v___x_446_, 0);
v_moduleNames_448_ = lean_ctor_get(v___x_446_, 1);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_461_ == 0)
{
v___x_450_ = v___x_446_;
v_isShared_451_ = v_isSharedCheck_461_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_moduleNames_448_);
lean_inc(v_moduleNameMap_447_);
lean_dec(v___x_446_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_461_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v___x_454_; 
lean_inc(v_name_439_);
v___x_452_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(v_name_439_, v_moduleNameMap_447_, v_name_439_);
lean_dec(v_name_439_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_452_);
v___x_454_ = v___x_450_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_452_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v_moduleNames_448_);
v___x_454_ = v_reuseFailAlloc_460_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
uint32_t v___x_455_; uint8_t v___x_456_; uint8_t v___x_457_; 
v___x_455_ = 0;
v___x_456_ = 0;
v___x_457_ = l_Lean_instDecidableEqOLeanLevel(v___x_456_, v___x_436_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_finalizeImport(v___x_454_, v___x_435_, v___x_440_, v___x_455_, v___x_441_, v___x_442_, v___x_456_, v___x_441_);
lean_dec_ref(v___x_454_);
return v___x_458_;
}
else
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_finalizeImport(v___x_454_, v___x_435_, v___x_440_, v___x_455_, v___x_441_, v___x_442_, v___x_456_, v___x_442_);
lean_dec_ref(v___x_454_);
return v___x_459_;
}
}
}
}
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
lean_dec(v___x_444_);
lean_dec_ref(v___x_440_);
lean_dec(v_name_439_);
lean_dec_ref(v___x_435_);
v_a_462_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_445_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_445_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__0___boxed(lean_object* v___x_470_, lean_object* v___x_471_, lean_object* v___x_472_, lean_object* v___x_473_, lean_object* v___y_474_, lean_object* v_name_475_, lean_object* v___x_476_, lean_object* v___x_477_, lean_object* v___x_478_, lean_object* v___y_479_){
_start:
{
uint8_t v___x_36246__boxed_480_; uint8_t v___y_36248__boxed_481_; uint8_t v___x_36250__boxed_482_; uint8_t v___x_36251__boxed_483_; lean_object* v_res_484_; 
v___x_36246__boxed_480_ = lean_unbox(v___x_472_);
v___y_36248__boxed_481_ = lean_unbox(v___y_474_);
v___x_36250__boxed_482_ = lean_unbox(v___x_477_);
v___x_36251__boxed_483_ = lean_unbox(v___x_478_);
v_res_484_ = l_main___lam__0(v___x_470_, v___x_471_, v___x_36246__boxed_480_, v___x_473_, v___y_36248__boxed_481_, v_name_475_, v___x_476_, v___x_36250__boxed_482_, v___x_36251__boxed_483_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_main___lam__1(lean_object* v___x_486_, lean_object* v___x_487_, lean_object* v___x_488_, lean_object* v_name_489_, lean_object* v_a_490_, lean_object* v___x_491_, lean_object* v_head_492_, lean_object* v___x_493_, lean_object* v___x_494_, lean_object* v___x_495_, lean_object* v___x_496_, lean_object* v___x_497_, lean_object* v___x_498_, lean_object* v___x_499_, lean_object* v___x_500_, uint8_t v___x_501_, uint8_t v___x_502_){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v_env_508_; lean_object* v___x_509_; uint8_t v___x_510_; lean_object* v_fileName_512_; lean_object* v_fileMap_513_; lean_object* v_currRecDepth_514_; lean_object* v_ref_515_; lean_object* v_currNamespace_516_; lean_object* v_openDecls_517_; lean_object* v_initHeartbeats_518_; lean_object* v_maxHeartbeats_519_; lean_object* v_quotContext_520_; lean_object* v_currMacroScope_521_; lean_object* v_cancelTk_x3f_522_; uint8_t v_suppressElabErrors_523_; lean_object* v_inheritedTraceOptions_524_; lean_object* v___y_525_; uint8_t v___y_554_; uint8_t v___x_574_; 
v___x_504_ = lean_io_get_num_heartbeats();
v___x_505_ = lean_st_mk_ref(v___x_486_);
v___x_506_ = lean_st_ref_get(v___x_487_);
v___x_507_ = lean_st_ref_get(v___x_505_);
v_env_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc_ref(v_env_508_);
lean_dec(v___x_507_);
v___x_509_ = l_Lean_diagnostics;
v___x_510_ = l_Lean_Option_get___at___00main_spec__8(v___x_488_, v___x_509_);
v___x_574_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_508_);
lean_dec_ref(v_env_508_);
if (v___x_574_ == 0)
{
if (v___x_510_ == 0)
{
v___y_554_ = v___x_502_;
goto v___jp_553_;
}
else
{
v___y_554_ = v___x_574_;
goto v___jp_553_;
}
}
else
{
v___y_554_ = v___x_510_;
goto v___jp_553_;
}
v___jp_511_:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_526_ = l_Lean_maxRecDepth;
v___x_527_ = l_Lean_Option_get___at___00main_spec__9(v___x_488_, v___x_526_);
v___x_528_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_528_, 0, v_fileName_512_);
lean_ctor_set(v___x_528_, 1, v_fileMap_513_);
lean_ctor_set(v___x_528_, 2, v___x_488_);
lean_ctor_set(v___x_528_, 3, v_currRecDepth_514_);
lean_ctor_set(v___x_528_, 4, v___x_527_);
lean_ctor_set(v___x_528_, 5, v_ref_515_);
lean_ctor_set(v___x_528_, 6, v_currNamespace_516_);
lean_ctor_set(v___x_528_, 7, v_openDecls_517_);
lean_ctor_set(v___x_528_, 8, v_initHeartbeats_518_);
lean_ctor_set(v___x_528_, 9, v_maxHeartbeats_519_);
lean_ctor_set(v___x_528_, 10, v_quotContext_520_);
lean_ctor_set(v___x_528_, 11, v_currMacroScope_521_);
lean_ctor_set(v___x_528_, 12, v_cancelTk_x3f_522_);
lean_ctor_set(v___x_528_, 13, v_inheritedTraceOptions_524_);
lean_ctor_set_uint8(v___x_528_, sizeof(void*)*14, v___x_510_);
lean_ctor_set_uint8(v___x_528_, sizeof(void*)*14 + 1, v_suppressElabErrors_523_);
v___x_529_ = l_Lean_Compiler_LCNF_emitC(v_name_489_, v___x_528_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___x_528_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_a_530_);
lean_dec_ref(v___x_529_);
v___x_531_ = lean_st_ref_get(v___x_505_);
lean_dec(v___x_505_);
lean_dec(v___x_531_);
v___x_532_ = lean_string_to_utf8(v_a_530_);
lean_dec(v_a_530_);
v___x_533_ = lean_io_prim_handle_write(v_a_490_, v___x_532_);
lean_dec_ref(v___x_532_);
return v___x_533_;
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_552_; 
lean_dec(v___x_505_);
v_a_534_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_552_ == 0)
{
v___x_536_ = v___x_529_;
v_isShared_537_ = v_isSharedCheck_552_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_529_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_552_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
if (lean_obj_tag(v_a_534_) == 0)
{
lean_object* v_msg_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_542_; 
v_msg_538_ = lean_ctor_get(v_a_534_, 1);
lean_inc_ref(v_msg_538_);
lean_dec_ref(v_a_534_);
v___x_539_ = l_Lean_MessageData_toString(v_msg_538_);
v___x_540_ = lean_mk_io_user_error(v___x_539_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_540_);
v___x_542_ = v___x_536_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
else
{
lean_object* v_id_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_550_; 
v_id_544_ = lean_ctor_get(v_a_534_, 0);
lean_inc(v_id_544_);
lean_dec_ref(v_a_534_);
v___x_545_ = ((lean_object*)(l_main___lam__1___closed__0));
v___x_546_ = l_Nat_reprFast(v_id_544_);
v___x_547_ = lean_string_append(v___x_545_, v___x_546_);
lean_dec_ref(v___x_546_);
v___x_548_ = lean_mk_io_user_error(v___x_547_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_548_);
v___x_550_ = v___x_536_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
v___jp_553_:
{
if (v___y_554_ == 0)
{
lean_object* v___x_555_; lean_object* v_env_556_; lean_object* v_nextMacroScope_557_; lean_object* v_ngen_558_; lean_object* v_auxDeclNGen_559_; lean_object* v_traceState_560_; lean_object* v_messages_561_; lean_object* v_infoState_562_; lean_object* v_snapshotTasks_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_572_; 
v___x_555_ = lean_st_ref_take(v___x_505_);
v_env_556_ = lean_ctor_get(v___x_555_, 0);
v_nextMacroScope_557_ = lean_ctor_get(v___x_555_, 1);
v_ngen_558_ = lean_ctor_get(v___x_555_, 2);
v_auxDeclNGen_559_ = lean_ctor_get(v___x_555_, 3);
v_traceState_560_ = lean_ctor_get(v___x_555_, 4);
v_messages_561_ = lean_ctor_get(v___x_555_, 6);
v_infoState_562_ = lean_ctor_get(v___x_555_, 7);
v_snapshotTasks_563_ = lean_ctor_get(v___x_555_, 8);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_572_ == 0)
{
lean_object* v_unused_573_; 
v_unused_573_ = lean_ctor_get(v___x_555_, 5);
lean_dec(v_unused_573_);
v___x_565_ = v___x_555_;
v_isShared_566_ = v_isSharedCheck_572_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_snapshotTasks_563_);
lean_inc(v_infoState_562_);
lean_inc(v_messages_561_);
lean_inc(v_traceState_560_);
lean_inc(v_auxDeclNGen_559_);
lean_inc(v_ngen_558_);
lean_inc(v_nextMacroScope_557_);
lean_inc(v_env_556_);
lean_dec(v___x_555_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_572_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v___x_569_; 
v___x_567_ = l_Lean_Kernel_enableDiag(v_env_556_, v___x_510_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 5, v___x_491_);
lean_ctor_set(v___x_565_, 0, v___x_567_);
v___x_569_ = v___x_565_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_567_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_nextMacroScope_557_);
lean_ctor_set(v_reuseFailAlloc_571_, 2, v_ngen_558_);
lean_ctor_set(v_reuseFailAlloc_571_, 3, v_auxDeclNGen_559_);
lean_ctor_set(v_reuseFailAlloc_571_, 4, v_traceState_560_);
lean_ctor_set(v_reuseFailAlloc_571_, 5, v___x_491_);
lean_ctor_set(v_reuseFailAlloc_571_, 6, v_messages_561_);
lean_ctor_set(v_reuseFailAlloc_571_, 7, v_infoState_562_);
lean_ctor_set(v_reuseFailAlloc_571_, 8, v_snapshotTasks_563_);
v___x_569_ = v_reuseFailAlloc_571_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_570_; 
v___x_570_ = lean_st_ref_set(v___x_505_, v___x_569_);
lean_inc(v___x_505_);
lean_inc(v___x_496_);
v_fileName_512_ = v_head_492_;
v_fileMap_513_ = v___x_493_;
v_currRecDepth_514_ = v___x_494_;
v_ref_515_ = v___x_495_;
v_currNamespace_516_ = v___x_496_;
v_openDecls_517_ = v___x_497_;
v_initHeartbeats_518_ = v___x_504_;
v_maxHeartbeats_519_ = v___x_498_;
v_quotContext_520_ = v___x_496_;
v_currMacroScope_521_ = v___x_499_;
v_cancelTk_x3f_522_ = v___x_500_;
v_suppressElabErrors_523_ = v___x_501_;
v_inheritedTraceOptions_524_ = v___x_506_;
v___y_525_ = v___x_505_;
goto v___jp_511_;
}
}
}
else
{
lean_dec_ref(v___x_491_);
lean_inc(v___x_505_);
lean_inc(v___x_496_);
v_fileName_512_ = v_head_492_;
v_fileMap_513_ = v___x_493_;
v_currRecDepth_514_ = v___x_494_;
v_ref_515_ = v___x_495_;
v_currNamespace_516_ = v___x_496_;
v_openDecls_517_ = v___x_497_;
v_initHeartbeats_518_ = v___x_504_;
v_maxHeartbeats_519_ = v___x_498_;
v_quotContext_520_ = v___x_496_;
v_currMacroScope_521_ = v___x_499_;
v_cancelTk_x3f_522_ = v___x_500_;
v_suppressElabErrors_523_ = v___x_501_;
v_inheritedTraceOptions_524_ = v___x_506_;
v___y_525_ = v___x_505_;
goto v___jp_511_;
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__1___boxed(lean_object** _args){
lean_object* v___x_575_ = _args[0];
lean_object* v___x_576_ = _args[1];
lean_object* v___x_577_ = _args[2];
lean_object* v_name_578_ = _args[3];
lean_object* v_a_579_ = _args[4];
lean_object* v___x_580_ = _args[5];
lean_object* v_head_581_ = _args[6];
lean_object* v___x_582_ = _args[7];
lean_object* v___x_583_ = _args[8];
lean_object* v___x_584_ = _args[9];
lean_object* v___x_585_ = _args[10];
lean_object* v___x_586_ = _args[11];
lean_object* v___x_587_ = _args[12];
lean_object* v___x_588_ = _args[13];
lean_object* v___x_589_ = _args[14];
lean_object* v___x_590_ = _args[15];
lean_object* v___x_591_ = _args[16];
lean_object* v___y_592_ = _args[17];
_start:
{
uint8_t v___x_36336__boxed_593_; uint8_t v___x_36337__boxed_594_; lean_object* v_res_595_; 
v___x_36336__boxed_593_ = lean_unbox(v___x_590_);
v___x_36337__boxed_594_ = lean_unbox(v___x_591_);
v_res_595_ = l_main___lam__1(v___x_575_, v___x_576_, v___x_577_, v_name_578_, v_a_579_, v___x_580_, v_head_581_, v___x_582_, v___x_583_, v___x_584_, v___x_585_, v___x_586_, v___x_587_, v___x_588_, v___x_589_, v___x_36336__boxed_593_, v___x_36337__boxed_594_);
lean_dec(v_a_579_);
lean_dec(v___x_576_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(lean_object* v_s_596_){
_start:
{
lean_object* v___x_598_; lean_object* v_putStr_599_; lean_object* v___x_600_; 
v___x_598_ = lean_get_stderr();
v_putStr_599_ = lean_ctor_get(v___x_598_, 4);
lean_inc_ref(v_putStr_599_);
lean_dec_ref(v___x_598_);
v___x_600_ = lean_apply_2(v_putStr_599_, v_s_596_, lean_box(0));
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8___boxed(lean_object* v_s_601_, lean_object* v_a_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v_s_601_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6(lean_object* v_s_604_){
_start:
{
uint32_t v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_606_ = 10;
v___x_607_ = lean_string_push(v_s_604_, v___x_606_);
v___x_608_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v___x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6___boxed(lean_object* v_s_609_, lean_object* v_a_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_IO_eprintln___at___00main_spec__6(v_s_609_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(lean_object* v_o_615_, lean_object* v_k_616_, lean_object* v_v_617_){
_start:
{
lean_object* v_map_618_; uint8_t v_hasTrace_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_633_; 
v_map_618_ = lean_ctor_get(v_o_615_, 0);
v_hasTrace_619_ = lean_ctor_get_uint8(v_o_615_, sizeof(void*)*1);
v_isSharedCheck_633_ = !lean_is_exclusive(v_o_615_);
if (v_isSharedCheck_633_ == 0)
{
v___x_621_ = v_o_615_;
v_isShared_622_ = v_isSharedCheck_633_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_map_618_);
lean_dec(v_o_615_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_633_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_623_, 0, v_v_617_);
lean_inc(v_k_616_);
v___x_624_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_616_, v___x_623_, v_map_618_);
if (v_hasTrace_619_ == 0)
{
lean_object* v___x_625_; uint8_t v___x_626_; lean_object* v___x_628_; 
v___x_625_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_626_ = l_Lean_Name_isPrefixOf(v___x_625_, v_k_616_);
lean_dec(v_k_616_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_624_);
v___x_628_ = v___x_621_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_624_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_ctor_set_uint8(v___x_628_, sizeof(void*)*1, v___x_626_);
return v___x_628_;
}
}
else
{
lean_object* v___x_631_; 
lean_dec(v_k_616_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_624_);
v___x_631_ = v___x_621_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_624_);
lean_ctor_set_uint8(v_reuseFailAlloc_632_, sizeof(void*)*1, v_hasTrace_619_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00main_spec__3(lean_object* v_opts_634_, lean_object* v_opt_635_, lean_object* v_val_636_){
_start:
{
lean_object* v_name_637_; lean_object* v___x_638_; 
v_name_637_ = lean_ctor_get(v_opt_635_, 0);
lean_inc(v_name_637_);
lean_dec_ref(v_opt_635_);
v___x_638_ = l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(v_opts_634_, v_name_637_, v_val_636_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object* v___y_640_, lean_object* v_as_641_, size_t v_i_642_, size_t v_stop_643_, lean_object* v_b_644_){
_start:
{
lean_object* v___y_646_; uint8_t v___x_650_; 
v___x_650_ = lean_usize_dec_eq(v_i_642_, v_stop_643_);
if (v___x_650_ == 0)
{
lean_object* v_fst_651_; lean_object* v_snd_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___y_656_; 
v_fst_651_ = lean_ctor_get(v_b_644_, 0);
v_snd_652_ = lean_ctor_get(v_b_644_, 1);
v___x_653_ = lean_array_uget_borrowed(v_as_641_, v_i_642_);
v___x_654_ = l_Lean_IR_Decl_name(v___x_653_);
if (lean_obj_tag(v___x_654_) == 1)
{
lean_object* v_pre_669_; lean_object* v_str_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v_pre_669_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_pre_669_);
v_str_670_ = lean_ctor_get(v___x_654_, 1);
lean_inc_ref(v_str_670_);
v___x_671_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___closed__0));
v___x_672_ = lean_string_dec_eq(v_str_670_, v___x_671_);
lean_dec_ref(v_str_670_);
if (v___x_672_ == 0)
{
lean_dec(v_pre_669_);
lean_inc_ref(v___x_654_);
v___y_656_ = v___x_654_;
goto v___jp_655_;
}
else
{
v___y_656_ = v_pre_669_;
goto v___jp_655_;
}
}
else
{
lean_inc(v___x_654_);
v___y_656_ = v___x_654_;
goto v___jp_655_;
}
v___jp_655_:
{
uint8_t v___x_657_; 
lean_inc_ref(v___y_640_);
v___x_657_ = l_Lean_isExtern(v___y_640_, v___y_656_);
if (v___x_657_ == 0)
{
lean_dec(v___x_654_);
v___y_646_ = v_b_644_;
goto v___jp_645_;
}
else
{
lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_666_; 
lean_inc(v_snd_652_);
lean_inc(v_fst_651_);
v_isSharedCheck_666_ = !lean_is_exclusive(v_b_644_);
if (v_isSharedCheck_666_ == 0)
{
lean_object* v_unused_667_; lean_object* v_unused_668_; 
v_unused_667_ = lean_ctor_get(v_b_644_, 1);
lean_dec(v_unused_667_);
v_unused_668_ = lean_ctor_get(v_b_644_, 0);
lean_dec(v_unused_668_);
v___x_659_ = v_b_644_;
v_isShared_660_ = v_isSharedCheck_666_;
goto v_resetjp_658_;
}
else
{
lean_dec(v_b_644_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_666_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_664_; 
lean_inc_n(v___x_653_, 2);
v___x_661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_653_);
lean_ctor_set(v___x_661_, 1, v_fst_651_);
v___x_662_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_652_, v___x_654_, v___x_653_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v___x_662_);
lean_ctor_set(v___x_659_, 0, v___x_661_);
v___x_664_ = v___x_659_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v___x_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
v___y_646_ = v___x_664_;
goto v___jp_645_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_640_);
return v_b_644_;
}
v___jp_645_:
{
size_t v___x_647_; size_t v___x_648_; 
v___x_647_ = ((size_t)1ULL);
v___x_648_ = lean_usize_add(v_i_642_, v___x_647_);
v_i_642_ = v___x_648_;
v_b_644_ = v___y_646_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object* v___y_673_, lean_object* v_as_674_, lean_object* v_i_675_, lean_object* v_stop_676_, lean_object* v_b_677_){
_start:
{
size_t v_i_boxed_678_; size_t v_stop_boxed_679_; lean_object* v_res_680_; 
v_i_boxed_678_ = lean_unbox_usize(v_i_675_);
lean_dec(v_i_675_);
v_stop_boxed_679_ = lean_unbox_usize(v_stop_676_);
lean_dec(v_stop_676_);
v_res_680_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_673_, v_as_674_, v_i_boxed_678_, v_stop_boxed_679_, v_b_677_);
lean_dec_ref(v_as_674_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg(lean_object* v_as_x27_682_, lean_object* v_b_683_){
_start:
{
if (lean_obj_tag(v_as_x27_682_) == 0)
{
lean_object* v___x_685_; 
v___x_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_685_, 0, v_b_683_);
return v___x_685_;
}
else
{
lean_object* v_head_686_; lean_object* v_tail_687_; lean_object* v_fst_688_; lean_object* v_snd_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_714_; 
v_head_686_ = lean_ctor_get(v_as_x27_682_, 0);
v_tail_687_ = lean_ctor_get(v_as_x27_682_, 1);
v_fst_688_ = lean_ctor_get(v_b_683_, 0);
v_snd_689_ = lean_ctor_get(v_b_683_, 1);
v_isSharedCheck_714_ = !lean_is_exclusive(v_b_683_);
if (v_isSharedCheck_714_ == 0)
{
v___x_691_ = v_b_683_;
v_isShared_692_ = v_isSharedCheck_714_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_snd_689_);
lean_inc(v_fst_688_);
lean_dec(v_b_683_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_714_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_693_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0));
v___x_694_ = lean_string_dec_eq(v_head_686_, v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; 
lean_inc(v_head_686_);
v___x_695_ = l___private_LeanIR_0__setConfigOption(v_snd_689_, v_head_686_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v___x_698_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
lean_dec_ref(v___x_695_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 1, v_a_696_);
v___x_698_ = v___x_691_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_fst_688_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_a_696_);
v___x_698_ = v_reuseFailAlloc_700_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
v_as_x27_682_ = v_tail_687_;
v_b_683_ = v___x_698_;
goto _start;
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_del_object(v___x_691_);
lean_dec(v_fst_688_);
v_a_701_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_695_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_695_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
else
{
lean_object* v___x_709_; lean_object* v___x_711_; 
lean_dec(v_fst_688_);
v___x_709_ = lean_box(v___x_694_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_709_);
v___x_711_ = v___x_691_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v_snd_689_);
v___x_711_ = v_reuseFailAlloc_713_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
v_as_x27_682_ = v_tail_687_;
v_b_683_ = v___x_711_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(lean_object* v_as_x27_715_, lean_object* v_b_716_, lean_object* v___y_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_715_, v_b_716_);
lean_dec(v_as_x27_715_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object* v_as_719_, size_t v_i_720_, size_t v_stop_721_, lean_object* v_b_722_){
_start:
{
uint8_t v___x_723_; 
v___x_723_ = lean_usize_dec_eq(v_i_720_, v_stop_721_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; lean_object* v_toEnvExtension_725_; lean_object* v_asyncMode_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; size_t v___x_730_; size_t v___x_731_; 
v___x_724_ = l_Lean_Compiler_LCNF_impureSigExt;
v_toEnvExtension_725_ = lean_ctor_get(v___x_724_, 0);
v_asyncMode_726_ = lean_ctor_get(v_toEnvExtension_725_, 2);
v___x_727_ = lean_box(0);
v___x_728_ = lean_array_uget_borrowed(v_as_719_, v_i_720_);
lean_inc(v___x_728_);
v___x_729_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_724_, v_b_722_, v___x_728_, v_asyncMode_726_, v___x_727_);
v___x_730_ = ((size_t)1ULL);
v___x_731_ = lean_usize_add(v_i_720_, v___x_730_);
v_i_720_ = v___x_731_;
v_b_722_ = v___x_729_;
goto _start;
}
else
{
return v_b_722_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object* v_as_733_, lean_object* v_i_734_, lean_object* v_stop_735_, lean_object* v_b_736_){
_start:
{
size_t v_i_boxed_737_; size_t v_stop_boxed_738_; lean_object* v_res_739_; 
v_i_boxed_737_ = lean_unbox_usize(v_i_734_);
lean_dec(v_i_734_);
v_stop_boxed_738_ = lean_unbox_usize(v_stop_735_);
lean_dec(v_stop_735_);
v_res_739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_as_733_, v_i_boxed_737_, v_stop_boxed_738_, v_b_736_);
lean_dec_ref(v_as_733_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(lean_object* v_as_743_, size_t v_sz_744_, size_t v_i_745_, lean_object* v_b_746_, lean_object* v___y_747_){
_start:
{
uint8_t v___x_749_; 
v___x_749_ = lean_usize_dec_lt(v_i_745_, v_sz_744_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; 
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v_b_746_);
return v___x_750_;
}
else
{
uint8_t v___x_751_; lean_object* v_a_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec_ref(v_b_746_);
v___x_751_ = 0;
v_a_752_ = lean_array_uget_borrowed(v_as_743_, v_i_745_);
lean_inc(v_a_752_);
v___x_753_ = l_Lean_Message_toString(v_a_752_, v___x_751_);
v___x_754_ = l_IO_eprintln___at___00main_spec__6(v___x_753_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v___x_755_; size_t v___x_756_; size_t v___x_757_; 
lean_dec_ref(v___x_754_);
v___x_755_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_756_ = ((size_t)1ULL);
v___x_757_ = lean_usize_add(v_i_745_, v___x_756_);
v_i_745_ = v___x_757_;
v_b_746_ = v___x_755_;
goto _start;
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_771_; 
v_a_759_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_771_ == 0)
{
v___x_761_ = v___x_754_;
v_isShared_762_ = v_isSharedCheck_771_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_754_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_771_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v_ref_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_769_; 
v_ref_763_ = lean_ctor_get(v___y_747_, 5);
v___x_764_ = lean_io_error_to_string(v_a_759_);
v___x_765_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
v___x_766_ = l_Lean_MessageData_ofFormat(v___x_765_);
lean_inc(v_ref_763_);
v___x_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_767_, 0, v_ref_763_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v___x_767_);
v___x_769_ = v___x_761_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___boxed(lean_object* v_as_772_, lean_object* v_sz_773_, lean_object* v_i_774_, lean_object* v_b_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
size_t v_sz_boxed_778_; size_t v_i_boxed_779_; lean_object* v_res_780_; 
v_sz_boxed_778_ = lean_unbox_usize(v_sz_773_);
lean_dec(v_sz_773_);
v_i_boxed_779_ = lean_unbox_usize(v_i_774_);
lean_dec(v_i_774_);
v_res_780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_772_, v_sz_boxed_778_, v_i_boxed_779_, v_b_775_, v___y_776_);
lean_dec_ref(v___y_776_);
lean_dec_ref(v_as_772_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(lean_object* v_as_781_, size_t v_sz_782_, size_t v_i_783_, lean_object* v_b_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
uint8_t v___x_788_; 
v___x_788_ = lean_usize_dec_lt(v_i_783_, v_sz_782_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; 
v___x_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_789_, 0, v_b_784_);
return v___x_789_;
}
else
{
uint8_t v___x_790_; lean_object* v_a_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
lean_dec_ref(v_b_784_);
v___x_790_ = 0;
v_a_791_ = lean_array_uget_borrowed(v_as_781_, v_i_783_);
lean_inc(v_a_791_);
v___x_792_ = l_Lean_Message_toString(v_a_791_, v___x_790_);
v___x_793_ = l_IO_eprintln___at___00main_spec__6(v___x_792_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v___x_794_; size_t v___x_795_; size_t v___x_796_; lean_object* v___x_797_; 
lean_dec_ref(v___x_793_);
v___x_794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_795_ = ((size_t)1ULL);
v___x_796_ = lean_usize_add(v_i_783_, v___x_795_);
v___x_797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_781_, v_sz_782_, v___x_796_, v___x_794_, v___y_785_);
return v___x_797_;
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
v_ref_802_ = lean_ctor_get(v___y_785_, 5);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27___boxed(lean_object* v_as_811_, lean_object* v_sz_812_, lean_object* v_i_813_, lean_object* v_b_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
size_t v_sz_boxed_818_; size_t v_i_boxed_819_; lean_object* v_res_820_; 
v_sz_boxed_818_ = lean_unbox_usize(v_sz_812_);
lean_dec(v_sz_812_);
v_i_boxed_819_ = lean_unbox_usize(v_i_813_);
lean_dec(v_i_813_);
v_res_820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(v_as_811_, v_sz_boxed_818_, v_i_boxed_819_, v_b_814_, v___y_815_, v___y_816_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec_ref(v_as_811_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(lean_object* v_as_824_, size_t v_sz_825_, size_t v_i_826_, lean_object* v_b_827_, lean_object* v___y_828_){
_start:
{
uint8_t v___x_830_; 
v___x_830_ = lean_usize_dec_lt(v_i_826_, v_sz_825_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; 
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v_b_827_);
return v___x_831_;
}
else
{
uint8_t v___x_832_; lean_object* v_a_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
lean_dec_ref(v_b_827_);
v___x_832_ = 0;
v_a_833_ = lean_array_uget_borrowed(v_as_824_, v_i_826_);
lean_inc(v_a_833_);
v___x_834_ = l_Lean_Message_toString(v_a_833_, v___x_832_);
v___x_835_ = l_IO_eprintln___at___00main_spec__6(v___x_834_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v___x_836_; size_t v___x_837_; size_t v___x_838_; 
lean_dec_ref(v___x_835_);
v___x_836_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_837_ = ((size_t)1ULL);
v___x_838_ = lean_usize_add(v_i_826_, v___x_837_);
v_i_826_ = v___x_838_;
v_b_827_ = v___x_836_;
goto _start;
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_852_; 
v_a_840_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_852_ == 0)
{
v___x_842_ = v___x_835_;
v_isShared_843_ = v_isSharedCheck_852_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_835_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_852_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v_ref_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
v_ref_844_ = lean_ctor_get(v___y_828_, 5);
v___x_845_ = lean_io_error_to_string(v_a_840_);
v___x_846_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
v___x_847_ = l_Lean_MessageData_ofFormat(v___x_846_);
lean_inc(v_ref_844_);
v___x_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_848_, 0, v_ref_844_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_848_);
v___x_850_ = v___x_842_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___boxed(lean_object* v_as_853_, lean_object* v_sz_854_, lean_object* v_i_855_, lean_object* v_b_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
size_t v_sz_boxed_859_; size_t v_i_boxed_860_; lean_object* v_res_861_; 
v_sz_boxed_859_ = lean_unbox_usize(v_sz_854_);
lean_dec(v_sz_854_);
v_i_boxed_860_ = lean_unbox_usize(v_i_855_);
lean_dec(v_i_855_);
v_res_861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_853_, v_sz_boxed_859_, v_i_boxed_860_, v_b_856_, v___y_857_);
lean_dec_ref(v___y_857_);
lean_dec_ref(v_as_853_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(lean_object* v_as_862_, size_t v_sz_863_, size_t v_i_864_, lean_object* v_b_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
uint8_t v___x_869_; 
v___x_869_ = lean_usize_dec_lt(v_i_864_, v_sz_863_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; 
v___x_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_870_, 0, v_b_865_);
return v___x_870_;
}
else
{
uint8_t v___x_871_; lean_object* v_a_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
lean_dec_ref(v_b_865_);
v___x_871_ = 0;
v_a_872_ = lean_array_uget_borrowed(v_as_862_, v_i_864_);
lean_inc(v_a_872_);
v___x_873_ = l_Lean_Message_toString(v_a_872_, v___x_871_);
v___x_874_ = l_IO_eprintln___at___00main_spec__6(v___x_873_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v___x_875_; size_t v___x_876_; size_t v___x_877_; lean_object* v___x_878_; 
lean_dec_ref(v___x_874_);
v___x_875_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_876_ = ((size_t)1ULL);
v___x_877_ = lean_usize_add(v_i_864_, v___x_876_);
v___x_878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_862_, v_sz_863_, v___x_877_, v___x_875_, v___y_866_);
return v___x_878_;
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
v_ref_883_ = lean_ctor_get(v___y_866_, 5);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38___boxed(lean_object* v_as_892_, lean_object* v_sz_893_, lean_object* v_i_894_, lean_object* v_b_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
size_t v_sz_boxed_899_; size_t v_i_boxed_900_; lean_object* v_res_901_; 
v_sz_boxed_899_ = lean_unbox_usize(v_sz_893_);
lean_dec(v_sz_893_);
v_i_boxed_900_ = lean_unbox_usize(v_i_894_);
lean_dec(v_i_894_);
v_res_901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(v_as_892_, v_sz_boxed_899_, v_i_boxed_900_, v_b_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec_ref(v_as_892_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(lean_object* v_init_902_, lean_object* v_n_903_, lean_object* v_b_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
if (lean_obj_tag(v_n_903_) == 0)
{
lean_object* v_cs_908_; lean_object* v___x_909_; lean_object* v___x_910_; size_t v_sz_911_; size_t v___x_912_; lean_object* v___x_913_; 
v_cs_908_ = lean_ctor_get(v_n_903_, 0);
v___x_909_ = lean_box(0);
v___x_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
lean_ctor_set(v___x_910_, 1, v_b_904_);
v_sz_911_ = lean_array_size(v_cs_908_);
v___x_912_ = ((size_t)0ULL);
v___x_913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_init_902_, v_cs_908_, v_sz_911_, v___x_912_, v___x_910_, v___y_905_, v___y_906_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_928_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_928_ == 0)
{
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_928_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_928_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v_fst_918_; 
v_fst_918_ = lean_ctor_get(v_a_914_, 0);
if (lean_obj_tag(v_fst_918_) == 0)
{
lean_object* v_snd_919_; lean_object* v___x_920_; lean_object* v___x_922_; 
v_snd_919_ = lean_ctor_get(v_a_914_, 1);
lean_inc(v_snd_919_);
lean_dec(v_a_914_);
v___x_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_920_, 0, v_snd_919_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_920_);
v___x_922_ = v___x_916_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
else
{
lean_object* v_val_924_; lean_object* v___x_926_; 
lean_inc_ref(v_fst_918_);
lean_dec(v_a_914_);
v_val_924_ = lean_ctor_get(v_fst_918_, 0);
lean_inc(v_val_924_);
lean_dec_ref(v_fst_918_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v_val_924_);
v___x_926_ = v___x_916_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_val_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
v_a_929_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_913_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_913_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
else
{
lean_object* v_vs_937_; lean_object* v___x_938_; lean_object* v___x_939_; size_t v_sz_940_; size_t v___x_941_; lean_object* v___x_942_; 
v_vs_937_ = lean_ctor_get(v_n_903_, 0);
v___x_938_ = lean_box(0);
v___x_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v_b_904_);
v_sz_940_ = lean_array_size(v_vs_937_);
v___x_941_ = ((size_t)0ULL);
v___x_942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(v_vs_937_, v_sz_940_, v___x_941_, v___x_939_, v___y_905_, v___y_906_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_957_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_957_ == 0)
{
v___x_945_ = v___x_942_;
v_isShared_946_ = v_isSharedCheck_957_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_942_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_957_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v_fst_947_; 
v_fst_947_ = lean_ctor_get(v_a_943_, 0);
if (lean_obj_tag(v_fst_947_) == 0)
{
lean_object* v_snd_948_; lean_object* v___x_949_; lean_object* v___x_951_; 
v_snd_948_ = lean_ctor_get(v_a_943_, 1);
lean_inc(v_snd_948_);
lean_dec(v_a_943_);
v___x_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_949_, 0, v_snd_948_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v___x_949_);
v___x_951_ = v___x_945_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
else
{
lean_object* v_val_953_; lean_object* v___x_955_; 
lean_inc_ref(v_fst_947_);
lean_dec(v_a_943_);
v_val_953_ = lean_ctor_get(v_fst_947_, 0);
lean_inc(v_val_953_);
lean_dec_ref(v_fst_947_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v_val_953_);
v___x_955_ = v___x_945_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_val_953_);
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
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
v_a_958_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_942_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_942_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(lean_object* v_init_966_, lean_object* v_as_967_, size_t v_sz_968_, size_t v_i_969_, lean_object* v_b_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
uint8_t v___x_974_; 
v___x_974_ = lean_usize_dec_lt(v_i_969_, v_sz_968_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; 
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v_b_970_);
return v___x_975_;
}
else
{
lean_object* v_snd_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1010_; 
v_snd_976_ = lean_ctor_get(v_b_970_, 1);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_b_970_);
if (v_isSharedCheck_1010_ == 0)
{
lean_object* v_unused_1011_; 
v_unused_1011_ = lean_ctor_get(v_b_970_, 0);
lean_dec(v_unused_1011_);
v___x_978_ = v_b_970_;
v_isShared_979_ = v_isSharedCheck_1010_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_snd_976_);
lean_dec(v_b_970_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1010_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v_a_980_; lean_object* v___x_981_; 
v_a_980_ = lean_array_uget_borrowed(v_as_967_, v_i_969_);
lean_inc(v_snd_976_);
v___x_981_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_966_, v_a_980_, v_snd_976_, v___y_971_, v___y_972_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_1001_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_984_ = v___x_981_;
v_isShared_985_ = v_isSharedCheck_1001_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_981_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_1001_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
if (lean_obj_tag(v_a_982_) == 0)
{
lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_986_, 0, v_a_982_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_986_);
v___x_988_ = v___x_978_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_snd_976_);
v___x_988_ = v_reuseFailAlloc_992_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_990_; 
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
}
else
{
lean_object* v_a_993_; lean_object* v___x_994_; lean_object* v___x_996_; 
lean_del_object(v___x_984_);
lean_dec(v_snd_976_);
v_a_993_ = lean_ctor_get(v_a_982_, 0);
lean_inc(v_a_993_);
lean_dec_ref(v_a_982_);
v___x_994_ = lean_box(0);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 1, v_a_993_);
lean_ctor_set(v___x_978_, 0, v___x_994_);
v___x_996_ = v___x_978_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_a_993_);
v___x_996_ = v_reuseFailAlloc_1000_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
size_t v___x_997_; size_t v___x_998_; 
v___x_997_ = ((size_t)1ULL);
v___x_998_ = lean_usize_add(v_i_969_, v___x_997_);
v_i_969_ = v___x_998_;
v_b_970_ = v___x_996_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_del_object(v___x_978_);
lean_dec(v_snd_976_);
v_a_1002_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_981_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_981_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37___boxed(lean_object* v_init_1012_, lean_object* v_as_1013_, lean_object* v_sz_1014_, lean_object* v_i_1015_, lean_object* v_b_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
size_t v_sz_boxed_1020_; size_t v_i_boxed_1021_; lean_object* v_res_1022_; 
v_sz_boxed_1020_ = lean_unbox_usize(v_sz_1014_);
lean_dec(v_sz_1014_);
v_i_boxed_1021_ = lean_unbox_usize(v_i_1015_);
lean_dec(v_i_1015_);
v_res_1022_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_init_1012_, v_as_1013_, v_sz_boxed_1020_, v_i_boxed_1021_, v_b_1016_, v___y_1017_, v___y_1018_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec_ref(v_as_1013_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26___boxed(lean_object* v_init_1023_, lean_object* v_n_1024_, lean_object* v_b_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1023_, v_n_1024_, v_b_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec_ref(v_n_1024_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12(lean_object* v_t_1030_, lean_object* v_init_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_root_1035_; lean_object* v_tail_1036_; lean_object* v___x_1037_; 
v_root_1035_ = lean_ctor_get(v_t_1030_, 0);
v_tail_1036_ = lean_ctor_get(v_t_1030_, 1);
v___x_1037_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1031_, v_root_1035_, v_init_1031_, v___y_1032_, v___y_1033_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1074_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1040_ = v___x_1037_;
v_isShared_1041_ = v_isSharedCheck_1074_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1037_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1074_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
if (lean_obj_tag(v_a_1038_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1044_; 
v_a_1042_ = lean_ctor_get(v_a_1038_, 0);
lean_inc(v_a_1042_);
lean_dec_ref(v_a_1038_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v_a_1042_);
v___x_1044_ = v___x_1040_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; size_t v_sz_1049_; size_t v___x_1050_; lean_object* v___x_1051_; 
lean_del_object(v___x_1040_);
v_a_1046_ = lean_ctor_get(v_a_1038_, 0);
lean_inc(v_a_1046_);
lean_dec_ref(v_a_1038_);
v___x_1047_ = lean_box(0);
v___x_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
lean_ctor_set(v___x_1048_, 1, v_a_1046_);
v_sz_1049_ = lean_array_size(v_tail_1036_);
v___x_1050_ = ((size_t)0ULL);
v___x_1051_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(v_tail_1036_, v_sz_1049_, v___x_1050_, v___x_1048_, v___y_1032_, v___y_1033_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1065_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1054_ = v___x_1051_;
v_isShared_1055_ = v_isSharedCheck_1065_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1065_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v_fst_1056_; 
v_fst_1056_ = lean_ctor_get(v_a_1052_, 0);
if (lean_obj_tag(v_fst_1056_) == 0)
{
lean_object* v_snd_1057_; lean_object* v___x_1059_; 
v_snd_1057_ = lean_ctor_get(v_a_1052_, 1);
lean_inc(v_snd_1057_);
lean_dec(v_a_1052_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v_snd_1057_);
v___x_1059_ = v___x_1054_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_snd_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
else
{
lean_object* v_val_1061_; lean_object* v___x_1063_; 
lean_inc_ref(v_fst_1056_);
lean_dec(v_a_1052_);
v_val_1061_ = lean_ctor_get(v_fst_1056_, 0);
lean_inc(v_val_1061_);
lean_dec_ref(v_fst_1056_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v_val_1061_);
v___x_1063_ = v___x_1054_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_val_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
v_a_1066_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1051_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1051_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
v_a_1075_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1037_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1037_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12___boxed(lean_object* v_t_1083_, lean_object* v_init_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(v_t_1083_, v_init_1084_, v___y_1085_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec_ref(v_t_1083_);
return v_res_1088_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(uint8_t v___x_1096_, uint8_t v_suppressElabErrors_1097_, lean_object* v___x_1098_, lean_object* v_x_1099_){
_start:
{
if (lean_obj_tag(v_x_1099_) == 1)
{
lean_object* v_pre_1100_; 
v_pre_1100_ = lean_ctor_get(v_x_1099_, 0);
switch(lean_obj_tag(v_pre_1100_))
{
case 1:
{
lean_object* v_pre_1101_; 
v_pre_1101_ = lean_ctor_get(v_pre_1100_, 0);
switch(lean_obj_tag(v_pre_1101_))
{
case 0:
{
lean_object* v_str_1102_; lean_object* v_str_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v_str_1102_ = lean_ctor_get(v_x_1099_, 1);
v_str_1103_ = lean_ctor_get(v_pre_1100_, 1);
v___x_1104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0));
v___x_1105_ = lean_string_dec_eq(v_str_1103_, v___x_1104_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1));
v___x_1107_ = lean_string_dec_eq(v_str_1103_, v___x_1106_);
if (v___x_1107_ == 0)
{
return v___x_1096_;
}
else
{
lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1108_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2));
v___x_1109_ = lean_string_dec_eq(v_str_1102_, v___x_1108_);
if (v___x_1109_ == 0)
{
return v___x_1096_;
}
else
{
return v_suppressElabErrors_1097_;
}
}
}
else
{
lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1110_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3));
v___x_1111_ = lean_string_dec_eq(v_str_1102_, v___x_1110_);
if (v___x_1111_ == 0)
{
return v___x_1096_;
}
else
{
return v_suppressElabErrors_1097_;
}
}
}
case 1:
{
lean_object* v_pre_1112_; 
v_pre_1112_ = lean_ctor_get(v_pre_1101_, 0);
if (lean_obj_tag(v_pre_1112_) == 0)
{
lean_object* v_str_1113_; lean_object* v_str_1114_; lean_object* v_str_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
v_str_1113_ = lean_ctor_get(v_x_1099_, 1);
v_str_1114_ = lean_ctor_get(v_pre_1100_, 1);
v_str_1115_ = lean_ctor_get(v_pre_1101_, 1);
v___x_1116_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4));
v___x_1117_ = lean_string_dec_eq(v_str_1115_, v___x_1116_);
if (v___x_1117_ == 0)
{
return v___x_1096_;
}
else
{
lean_object* v___x_1118_; uint8_t v___x_1119_; 
v___x_1118_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5));
v___x_1119_ = lean_string_dec_eq(v_str_1114_, v___x_1118_);
if (v___x_1119_ == 0)
{
return v___x_1096_;
}
else
{
lean_object* v___x_1120_; uint8_t v___x_1121_; 
v___x_1120_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6));
v___x_1121_ = lean_string_dec_eq(v_str_1113_, v___x_1120_);
if (v___x_1121_ == 0)
{
return v___x_1096_;
}
else
{
return v_suppressElabErrors_1097_;
}
}
}
}
else
{
return v___x_1096_;
}
}
default: 
{
return v___x_1096_;
}
}
}
case 0:
{
lean_object* v_str_1122_; uint8_t v___x_1123_; 
v_str_1122_ = lean_ctor_get(v_x_1099_, 1);
v___x_1123_ = lean_string_dec_eq(v_str_1122_, v___x_1098_);
if (v___x_1123_ == 0)
{
return v___x_1096_;
}
else
{
return v_suppressElabErrors_1097_;
}
}
default: 
{
return v___x_1096_;
}
}
}
else
{
return v___x_1096_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed(lean_object* v___x_1124_, lean_object* v_suppressElabErrors_1125_, lean_object* v___x_1126_, lean_object* v_x_1127_){
_start:
{
uint8_t v___x_37203__boxed_1128_; uint8_t v_suppressElabErrors_boxed_1129_; uint8_t v_res_1130_; lean_object* v_r_1131_; 
v___x_37203__boxed_1128_ = lean_unbox(v___x_1124_);
v_suppressElabErrors_boxed_1129_ = lean_unbox(v_suppressElabErrors_1125_);
v_res_1130_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(v___x_37203__boxed_1128_, v_suppressElabErrors_boxed_1129_, v___x_1126_, v_x_1127_);
lean_dec(v_x_1127_);
lean_dec_ref(v___x_1126_);
v_r_1131_ = lean_box(v_res_1130_);
return v_r_1131_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0(void){
_start:
{
lean_object* v___x_1132_; double v___x_1133_; 
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = lean_float_of_nat(v___x_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(uint8_t v___x_1135_, lean_object* v_as_1136_, size_t v_sz_1137_, size_t v_i_1138_, lean_object* v_b_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_a_1144_; uint8_t v___x_1148_; 
v___x_1148_ = lean_usize_dec_lt(v_i_1138_, v_sz_1137_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1149_, 0, v_b_1139_);
return v___x_1149_;
}
else
{
lean_object* v_a_1150_; lean_object* v_fst_1151_; lean_object* v_snd_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1228_; 
v_a_1150_ = lean_array_uget(v_as_1136_, v_i_1138_);
v_fst_1151_ = lean_ctor_get(v_a_1150_, 0);
v_snd_1152_ = lean_ctor_get(v_a_1150_, 1);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_a_1150_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1154_ = v_a_1150_;
v_isShared_1155_ = v_isSharedCheck_1228_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_snd_1152_);
lean_inc(v_fst_1151_);
lean_dec(v_a_1150_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1228_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v_fst_1156_; lean_object* v_snd_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1227_; 
v_fst_1156_ = lean_ctor_get(v_fst_1151_, 0);
v_snd_1157_ = lean_ctor_get(v_fst_1151_, 1);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_fst_1151_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1159_ = v_fst_1151_;
v_isShared_1160_ = v_isSharedCheck_1227_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_snd_1157_);
lean_inc(v_fst_1156_);
lean_dec(v_fst_1151_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1227_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; double v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v_fileName_1166_; lean_object* v_fileMap_1167_; uint8_t v_suppressElabErrors_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1175_; 
v___x_1161_ = lean_box(0);
v___x_1162_ = lean_box(0);
v___x_1163_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0);
v___x_1164_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1));
v___x_1165_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1165_, 0, v___x_1161_);
lean_ctor_set(v___x_1165_, 1, v___x_1162_);
lean_ctor_set(v___x_1165_, 2, v___x_1164_);
lean_ctor_set_float(v___x_1165_, sizeof(void*)*3, v___x_1163_);
lean_ctor_set_float(v___x_1165_, sizeof(void*)*3 + 8, v___x_1163_);
lean_ctor_set_uint8(v___x_1165_, sizeof(void*)*3 + 16, v___x_1148_);
v_fileName_1166_ = lean_ctor_get(v___y_1140_, 0);
v_fileMap_1167_ = lean_ctor_get(v___y_1140_, 1);
v_suppressElabErrors_1168_ = lean_ctor_get_uint8(v___y_1140_, sizeof(void*)*14 + 1);
v___x_1169_ = lean_box(0);
v___x_1170_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_1171_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_1172_ = l_Lean_MessageData_nil;
v___x_1173_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1165_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
lean_ctor_set(v___x_1173_, 2, v_snd_1152_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set_tag(v___x_1159_, 8);
lean_ctor_set(v___x_1159_, 1, v___x_1173_);
lean_ctor_set(v___x_1159_, 0, v___x_1171_);
v___x_1175_ = v___x_1159_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v___x_1173_);
v___x_1175_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
uint8_t v___x_1176_; lean_object* v___x_1177_; lean_object* v___y_1179_; lean_object* v___y_1180_; 
v___x_1176_ = 0;
lean_inc_ref(v_fileMap_1167_);
lean_inc_ref(v_fileName_1166_);
v___x_1177_ = l_Lean_Elab_mkMessageCore(v_fileName_1166_, v_fileMap_1167_, v___x_1175_, v___x_1176_, v_fst_1156_, v_snd_1157_);
lean_dec(v_snd_1157_);
lean_dec(v_fst_1156_);
if (v_suppressElabErrors_1168_ == 0)
{
v___y_1179_ = v___y_1140_;
v___y_1180_ = v___y_1141_;
goto v___jp_1178_;
}
else
{
lean_object* v_data_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___f_1224_; uint8_t v___x_1225_; 
v_data_1221_ = lean_ctor_get(v___x_1177_, 4);
lean_inc(v_data_1221_);
v___x_1222_ = lean_box(v___x_1135_);
v___x_1223_ = lean_box(v_suppressElabErrors_1168_);
v___f_1224_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1224_, 0, v___x_1222_);
lean_closure_set(v___f_1224_, 1, v___x_1223_);
lean_closure_set(v___f_1224_, 2, v___x_1170_);
v___x_1225_ = l_Lean_MessageData_hasTag(v___f_1224_, v_data_1221_);
if (v___x_1225_ == 0)
{
lean_dec_ref(v___x_1177_);
lean_del_object(v___x_1154_);
v_a_1144_ = v___x_1169_;
goto v___jp_1143_;
}
else
{
v___y_1179_ = v___y_1140_;
v___y_1180_ = v___y_1141_;
goto v___jp_1178_;
}
}
v___jp_1178_:
{
lean_object* v___x_1181_; lean_object* v_fileName_1182_; lean_object* v_pos_1183_; lean_object* v_endPos_1184_; uint8_t v_keepFullRange_1185_; uint8_t v_severity_1186_; uint8_t v_isSilent_1187_; lean_object* v_caption_1188_; lean_object* v_data_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1220_; 
v___x_1181_ = lean_st_ref_take(v___y_1180_);
v_fileName_1182_ = lean_ctor_get(v___x_1177_, 0);
v_pos_1183_ = lean_ctor_get(v___x_1177_, 1);
v_endPos_1184_ = lean_ctor_get(v___x_1177_, 2);
v_keepFullRange_1185_ = lean_ctor_get_uint8(v___x_1177_, sizeof(void*)*5);
v_severity_1186_ = lean_ctor_get_uint8(v___x_1177_, sizeof(void*)*5 + 1);
v_isSilent_1187_ = lean_ctor_get_uint8(v___x_1177_, sizeof(void*)*5 + 2);
v_caption_1188_ = lean_ctor_get(v___x_1177_, 3);
v_data_1189_ = lean_ctor_get(v___x_1177_, 4);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1191_ = v___x_1177_;
v_isShared_1192_ = v_isSharedCheck_1220_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_data_1189_);
lean_inc(v_caption_1188_);
lean_inc(v_endPos_1184_);
lean_inc(v_pos_1183_);
lean_inc(v_fileName_1182_);
lean_dec(v___x_1177_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1220_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v_currNamespace_1193_; lean_object* v_openDecls_1194_; lean_object* v_env_1195_; lean_object* v_nextMacroScope_1196_; lean_object* v_ngen_1197_; lean_object* v_auxDeclNGen_1198_; lean_object* v_traceState_1199_; lean_object* v_cache_1200_; lean_object* v_messages_1201_; lean_object* v_infoState_1202_; lean_object* v_snapshotTasks_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1219_; 
v_currNamespace_1193_ = lean_ctor_get(v___y_1179_, 6);
v_openDecls_1194_ = lean_ctor_get(v___y_1179_, 7);
v_env_1195_ = lean_ctor_get(v___x_1181_, 0);
v_nextMacroScope_1196_ = lean_ctor_get(v___x_1181_, 1);
v_ngen_1197_ = lean_ctor_get(v___x_1181_, 2);
v_auxDeclNGen_1198_ = lean_ctor_get(v___x_1181_, 3);
v_traceState_1199_ = lean_ctor_get(v___x_1181_, 4);
v_cache_1200_ = lean_ctor_get(v___x_1181_, 5);
v_messages_1201_ = lean_ctor_get(v___x_1181_, 6);
v_infoState_1202_ = lean_ctor_get(v___x_1181_, 7);
v_snapshotTasks_1203_ = lean_ctor_get(v___x_1181_, 8);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1205_ = v___x_1181_;
v_isShared_1206_ = v_isSharedCheck_1219_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_snapshotTasks_1203_);
lean_inc(v_infoState_1202_);
lean_inc(v_messages_1201_);
lean_inc(v_cache_1200_);
lean_inc(v_traceState_1199_);
lean_inc(v_auxDeclNGen_1198_);
lean_inc(v_ngen_1197_);
lean_inc(v_nextMacroScope_1196_);
lean_inc(v_env_1195_);
lean_dec(v___x_1181_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1219_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
lean_inc(v_openDecls_1194_);
lean_inc(v_currNamespace_1193_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 1, v_openDecls_1194_);
lean_ctor_set(v___x_1154_, 0, v_currNamespace_1193_);
v___x_1208_ = v___x_1154_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_currNamespace_1193_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v_openDecls_1194_);
v___x_1208_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1209_; lean_object* v___x_1211_; 
v___x_1209_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v_data_1189_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 4, v___x_1209_);
v___x_1211_ = v___x_1191_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_fileName_1182_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_pos_1183_);
lean_ctor_set(v_reuseFailAlloc_1217_, 2, v_endPos_1184_);
lean_ctor_set(v_reuseFailAlloc_1217_, 3, v_caption_1188_);
lean_ctor_set(v_reuseFailAlloc_1217_, 4, v___x_1209_);
lean_ctor_set_uint8(v_reuseFailAlloc_1217_, sizeof(void*)*5, v_keepFullRange_1185_);
lean_ctor_set_uint8(v_reuseFailAlloc_1217_, sizeof(void*)*5 + 1, v_severity_1186_);
lean_ctor_set_uint8(v_reuseFailAlloc_1217_, sizeof(void*)*5 + 2, v_isSilent_1187_);
v___x_1211_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1212_ = l_Lean_MessageLog_add(v___x_1211_, v_messages_1201_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 6, v___x_1212_);
v___x_1214_ = v___x_1205_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_env_1195_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_nextMacroScope_1196_);
lean_ctor_set(v_reuseFailAlloc_1216_, 2, v_ngen_1197_);
lean_ctor_set(v_reuseFailAlloc_1216_, 3, v_auxDeclNGen_1198_);
lean_ctor_set(v_reuseFailAlloc_1216_, 4, v_traceState_1199_);
lean_ctor_set(v_reuseFailAlloc_1216_, 5, v_cache_1200_);
lean_ctor_set(v_reuseFailAlloc_1216_, 6, v___x_1212_);
lean_ctor_set(v_reuseFailAlloc_1216_, 7, v_infoState_1202_);
lean_ctor_set(v_reuseFailAlloc_1216_, 8, v_snapshotTasks_1203_);
v___x_1214_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_st_ref_set(v___y_1180_, v___x_1214_);
v_a_1144_ = v___x_1169_;
goto v___jp_1143_;
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
v___jp_1143_:
{
size_t v___x_1145_; size_t v___x_1146_; 
v___x_1145_ = ((size_t)1ULL);
v___x_1146_ = lean_usize_add(v_i_1138_, v___x_1145_);
v_i_1138_ = v___x_1146_;
v_b_1139_ = v_a_1144_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___boxed(lean_object* v___x_1229_, lean_object* v_as_1230_, lean_object* v_sz_1231_, lean_object* v_i_1232_, lean_object* v_b_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
uint8_t v___x_37276__boxed_1237_; size_t v_sz_boxed_1238_; size_t v_i_boxed_1239_; lean_object* v_res_1240_; 
v___x_37276__boxed_1237_ = lean_unbox(v___x_1229_);
v_sz_boxed_1238_ = lean_unbox_usize(v_sz_1231_);
lean_dec(v_sz_1231_);
v_i_boxed_1239_ = lean_unbox_usize(v_i_1232_);
lean_dec(v_i_1232_);
v_res_1240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_37276__boxed_1237_, v_as_1230_, v_sz_boxed_1238_, v_i_boxed_1239_, v_b_1233_, v___y_1234_, v___y_1235_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec_ref(v_as_1230_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(lean_object* v_opts_1241_, lean_object* v_opt_1242_){
_start:
{
lean_object* v_name_1243_; lean_object* v_map_1244_; lean_object* v___x_1245_; 
v_name_1243_ = lean_ctor_get(v_opt_1242_, 0);
v_map_1244_ = lean_ctor_get(v_opts_1241_, 0);
v___x_1245_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1244_, v_name_1243_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v___x_1246_; 
v___x_1246_ = lean_box(0);
return v___x_1246_;
}
else
{
lean_object* v_val_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1256_; 
v_val_1247_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1249_ = v___x_1245_;
v_isShared_1250_ = v_isSharedCheck_1256_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_val_1247_);
lean_dec(v___x_1245_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1256_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
if (lean_obj_tag(v_val_1247_) == 0)
{
lean_object* v_v_1251_; lean_object* v___x_1253_; 
v_v_1251_ = lean_ctor_get(v_val_1247_, 0);
lean_inc_ref(v_v_1251_);
lean_dec_ref(v_val_1247_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v_v_1251_);
v___x_1253_ = v___x_1249_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_v_1251_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
else
{
lean_object* v___x_1255_; 
lean_del_object(v___x_1249_);
lean_dec(v_val_1247_);
v___x_1255_ = lean_box(0);
return v___x_1255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15___boxed(lean_object* v_opts_1257_, lean_object* v_opt_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(v_opts_1257_, v_opt_1258_);
lean_dec_ref(v_opt_1258_);
lean_dec_ref(v_opts_1257_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(lean_object* v_a_1260_, lean_object* v_fallback_1261_, lean_object* v_x_1262_){
_start:
{
if (lean_obj_tag(v_x_1262_) == 0)
{
lean_inc(v_fallback_1261_);
return v_fallback_1261_;
}
else
{
lean_object* v_key_1263_; lean_object* v_value_1264_; lean_object* v_tail_1265_; uint8_t v___y_1267_; lean_object* v_fst_1269_; lean_object* v_snd_1270_; lean_object* v_fst_1271_; lean_object* v_snd_1272_; uint8_t v___x_1273_; 
v_key_1263_ = lean_ctor_get(v_x_1262_, 0);
v_value_1264_ = lean_ctor_get(v_x_1262_, 1);
v_tail_1265_ = lean_ctor_get(v_x_1262_, 2);
v_fst_1269_ = lean_ctor_get(v_key_1263_, 0);
v_snd_1270_ = lean_ctor_get(v_key_1263_, 1);
v_fst_1271_ = lean_ctor_get(v_a_1260_, 0);
v_snd_1272_ = lean_ctor_get(v_a_1260_, 1);
v___x_1273_ = lean_nat_dec_eq(v_fst_1269_, v_fst_1271_);
if (v___x_1273_ == 0)
{
v___y_1267_ = v___x_1273_;
goto v___jp_1266_;
}
else
{
uint8_t v___x_1274_; 
v___x_1274_ = lean_nat_dec_eq(v_snd_1270_, v_snd_1272_);
v___y_1267_ = v___x_1274_;
goto v___jp_1266_;
}
v___jp_1266_:
{
if (v___y_1267_ == 0)
{
v_x_1262_ = v_tail_1265_;
goto _start;
}
else
{
lean_inc(v_value_1264_);
return v_value_1264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg___boxed(lean_object* v_a_1275_, lean_object* v_fallback_1276_, lean_object* v_x_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_1275_, v_fallback_1276_, v_x_1277_);
lean_dec(v_x_1277_);
lean_dec(v_fallback_1276_);
lean_dec_ref(v_a_1275_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(lean_object* v_m_1279_, lean_object* v_a_1280_, lean_object* v_fallback_1281_){
_start:
{
lean_object* v_buckets_1282_; lean_object* v_fst_1283_; lean_object* v_snd_1284_; lean_object* v___x_1285_; uint64_t v___x_1286_; uint64_t v___x_1287_; uint64_t v___x_1288_; uint64_t v___x_1289_; uint64_t v___x_1290_; uint64_t v_fold_1291_; uint64_t v___x_1292_; uint64_t v___x_1293_; uint64_t v___x_1294_; size_t v___x_1295_; size_t v___x_1296_; size_t v___x_1297_; size_t v___x_1298_; size_t v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v_buckets_1282_ = lean_ctor_get(v_m_1279_, 1);
v_fst_1283_ = lean_ctor_get(v_a_1280_, 0);
v_snd_1284_ = lean_ctor_get(v_a_1280_, 1);
v___x_1285_ = lean_array_get_size(v_buckets_1282_);
v___x_1286_ = l_String_instHashableRaw_hash(v_fst_1283_);
v___x_1287_ = l_String_instHashableRaw_hash(v_snd_1284_);
v___x_1288_ = lean_uint64_mix_hash(v___x_1286_, v___x_1287_);
v___x_1289_ = 32ULL;
v___x_1290_ = lean_uint64_shift_right(v___x_1288_, v___x_1289_);
v_fold_1291_ = lean_uint64_xor(v___x_1288_, v___x_1290_);
v___x_1292_ = 16ULL;
v___x_1293_ = lean_uint64_shift_right(v_fold_1291_, v___x_1292_);
v___x_1294_ = lean_uint64_xor(v_fold_1291_, v___x_1293_);
v___x_1295_ = lean_uint64_to_usize(v___x_1294_);
v___x_1296_ = lean_usize_of_nat(v___x_1285_);
v___x_1297_ = ((size_t)1ULL);
v___x_1298_ = lean_usize_sub(v___x_1296_, v___x_1297_);
v___x_1299_ = lean_usize_land(v___x_1295_, v___x_1298_);
v___x_1300_ = lean_array_uget_borrowed(v_buckets_1282_, v___x_1299_);
v___x_1301_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_1280_, v_fallback_1281_, v___x_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg___boxed(lean_object* v_m_1302_, lean_object* v_a_1303_, lean_object* v_fallback_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_1302_, v_a_1303_, v_fallback_1304_);
lean_dec(v_fallback_1304_);
lean_dec_ref(v_a_1303_);
lean_dec_ref(v_m_1302_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(lean_object* v_x_1306_, lean_object* v_x_1307_){
_start:
{
if (lean_obj_tag(v_x_1307_) == 0)
{
return v_x_1306_;
}
else
{
lean_object* v_key_1308_; lean_object* v_value_1309_; lean_object* v_tail_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1337_; 
v_key_1308_ = lean_ctor_get(v_x_1307_, 0);
v_value_1309_ = lean_ctor_get(v_x_1307_, 1);
v_tail_1310_ = lean_ctor_get(v_x_1307_, 2);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_x_1307_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1312_ = v_x_1307_;
v_isShared_1313_ = v_isSharedCheck_1337_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_tail_1310_);
lean_inc(v_value_1309_);
lean_inc(v_key_1308_);
lean_dec(v_x_1307_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1337_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v_fst_1314_; lean_object* v_snd_1315_; lean_object* v___x_1316_; uint64_t v___x_1317_; uint64_t v___x_1318_; uint64_t v___x_1319_; uint64_t v___x_1320_; uint64_t v___x_1321_; uint64_t v_fold_1322_; uint64_t v___x_1323_; uint64_t v___x_1324_; uint64_t v___x_1325_; size_t v___x_1326_; size_t v___x_1327_; size_t v___x_1328_; size_t v___x_1329_; size_t v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1333_; 
v_fst_1314_ = lean_ctor_get(v_key_1308_, 0);
v_snd_1315_ = lean_ctor_get(v_key_1308_, 1);
v___x_1316_ = lean_array_get_size(v_x_1306_);
v___x_1317_ = l_String_instHashableRaw_hash(v_fst_1314_);
v___x_1318_ = l_String_instHashableRaw_hash(v_snd_1315_);
v___x_1319_ = lean_uint64_mix_hash(v___x_1317_, v___x_1318_);
v___x_1320_ = 32ULL;
v___x_1321_ = lean_uint64_shift_right(v___x_1319_, v___x_1320_);
v_fold_1322_ = lean_uint64_xor(v___x_1319_, v___x_1321_);
v___x_1323_ = 16ULL;
v___x_1324_ = lean_uint64_shift_right(v_fold_1322_, v___x_1323_);
v___x_1325_ = lean_uint64_xor(v_fold_1322_, v___x_1324_);
v___x_1326_ = lean_uint64_to_usize(v___x_1325_);
v___x_1327_ = lean_usize_of_nat(v___x_1316_);
v___x_1328_ = ((size_t)1ULL);
v___x_1329_ = lean_usize_sub(v___x_1327_, v___x_1328_);
v___x_1330_ = lean_usize_land(v___x_1326_, v___x_1329_);
v___x_1331_ = lean_array_uget_borrowed(v_x_1306_, v___x_1330_);
lean_inc(v___x_1331_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 2, v___x_1331_);
v___x_1333_ = v___x_1312_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_key_1308_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_value_1309_);
lean_ctor_set(v_reuseFailAlloc_1336_, 2, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1334_; 
v___x_1334_ = lean_array_uset(v_x_1306_, v___x_1330_, v___x_1333_);
v_x_1306_ = v___x_1334_;
v_x_1307_ = v_tail_1310_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(lean_object* v_i_1338_, lean_object* v_source_1339_, lean_object* v_target_1340_){
_start:
{
lean_object* v___x_1341_; uint8_t v___x_1342_; 
v___x_1341_ = lean_array_get_size(v_source_1339_);
v___x_1342_ = lean_nat_dec_lt(v_i_1338_, v___x_1341_);
if (v___x_1342_ == 0)
{
lean_dec_ref(v_source_1339_);
lean_dec(v_i_1338_);
return v_target_1340_;
}
else
{
lean_object* v_es_1343_; lean_object* v___x_1344_; lean_object* v_source_1345_; lean_object* v_target_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v_es_1343_ = lean_array_fget(v_source_1339_, v_i_1338_);
v___x_1344_ = lean_box(0);
v_source_1345_ = lean_array_fset(v_source_1339_, v_i_1338_, v___x_1344_);
v_target_1346_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_target_1340_, v_es_1343_);
v___x_1347_ = lean_unsigned_to_nat(1u);
v___x_1348_ = lean_nat_add(v_i_1338_, v___x_1347_);
lean_dec(v_i_1338_);
v_i_1338_ = v___x_1348_;
v_source_1339_ = v_source_1345_;
v_target_1340_ = v_target_1346_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(lean_object* v_data_1350_){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v_nbuckets_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1351_ = lean_array_get_size(v_data_1350_);
v___x_1352_ = lean_unsigned_to_nat(2u);
v_nbuckets_1353_ = lean_nat_mul(v___x_1351_, v___x_1352_);
v___x_1354_ = lean_unsigned_to_nat(0u);
v___x_1355_ = lean_box(0);
v___x_1356_ = lean_mk_array(v_nbuckets_1353_, v___x_1355_);
v___x_1357_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v___x_1354_, v_data_1350_, v___x_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(lean_object* v_a_1358_, lean_object* v_b_1359_, lean_object* v_x_1360_){
_start:
{
if (lean_obj_tag(v_x_1360_) == 0)
{
lean_dec(v_b_1359_);
lean_dec_ref(v_a_1358_);
return v_x_1360_;
}
else
{
lean_object* v_key_1361_; lean_object* v_value_1362_; lean_object* v_tail_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1382_; 
v_key_1361_ = lean_ctor_get(v_x_1360_, 0);
v_value_1362_ = lean_ctor_get(v_x_1360_, 1);
v_tail_1363_ = lean_ctor_get(v_x_1360_, 2);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_x_1360_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1365_ = v_x_1360_;
v_isShared_1366_ = v_isSharedCheck_1382_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_tail_1363_);
lean_inc(v_value_1362_);
lean_inc(v_key_1361_);
lean_dec(v_x_1360_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1382_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
uint8_t v___y_1368_; lean_object* v_fst_1376_; lean_object* v_snd_1377_; lean_object* v_fst_1378_; lean_object* v_snd_1379_; uint8_t v___x_1380_; 
v_fst_1376_ = lean_ctor_get(v_key_1361_, 0);
v_snd_1377_ = lean_ctor_get(v_key_1361_, 1);
v_fst_1378_ = lean_ctor_get(v_a_1358_, 0);
v_snd_1379_ = lean_ctor_get(v_a_1358_, 1);
v___x_1380_ = lean_nat_dec_eq(v_fst_1376_, v_fst_1378_);
if (v___x_1380_ == 0)
{
v___y_1368_ = v___x_1380_;
goto v___jp_1367_;
}
else
{
uint8_t v___x_1381_; 
v___x_1381_ = lean_nat_dec_eq(v_snd_1377_, v_snd_1379_);
v___y_1368_ = v___x_1381_;
goto v___jp_1367_;
}
v___jp_1367_:
{
if (v___y_1368_ == 0)
{
lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1369_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_1358_, v_b_1359_, v_tail_1363_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 2, v___x_1369_);
v___x_1371_ = v___x_1365_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_key_1361_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_value_1362_);
lean_ctor_set(v_reuseFailAlloc_1372_, 2, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
else
{
lean_object* v___x_1374_; 
lean_dec(v_value_1362_);
lean_dec(v_key_1361_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 1, v_b_1359_);
lean_ctor_set(v___x_1365_, 0, v_a_1358_);
v___x_1374_ = v___x_1365_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1358_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v_b_1359_);
lean_ctor_set(v_reuseFailAlloc_1375_, 2, v_tail_1363_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(lean_object* v_a_1383_, lean_object* v_x_1384_){
_start:
{
if (lean_obj_tag(v_x_1384_) == 0)
{
uint8_t v___x_1385_; 
v___x_1385_ = 0;
return v___x_1385_;
}
else
{
lean_object* v_key_1386_; lean_object* v_tail_1387_; uint8_t v___y_1389_; lean_object* v_fst_1391_; lean_object* v_snd_1392_; lean_object* v_fst_1393_; lean_object* v_snd_1394_; uint8_t v___x_1395_; 
v_key_1386_ = lean_ctor_get(v_x_1384_, 0);
v_tail_1387_ = lean_ctor_get(v_x_1384_, 2);
v_fst_1391_ = lean_ctor_get(v_key_1386_, 0);
v_snd_1392_ = lean_ctor_get(v_key_1386_, 1);
v_fst_1393_ = lean_ctor_get(v_a_1383_, 0);
v_snd_1394_ = lean_ctor_get(v_a_1383_, 1);
v___x_1395_ = lean_nat_dec_eq(v_fst_1391_, v_fst_1393_);
if (v___x_1395_ == 0)
{
v___y_1389_ = v___x_1395_;
goto v___jp_1388_;
}
else
{
uint8_t v___x_1396_; 
v___x_1396_ = lean_nat_dec_eq(v_snd_1392_, v_snd_1394_);
v___y_1389_ = v___x_1396_;
goto v___jp_1388_;
}
v___jp_1388_:
{
if (v___y_1389_ == 0)
{
v_x_1384_ = v_tail_1387_;
goto _start;
}
else
{
return v___y_1389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg___boxed(lean_object* v_a_1397_, lean_object* v_x_1398_){
_start:
{
uint8_t v_res_1399_; lean_object* v_r_1400_; 
v_res_1399_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_1397_, v_x_1398_);
lean_dec(v_x_1398_);
lean_dec_ref(v_a_1397_);
v_r_1400_ = lean_box(v_res_1399_);
return v_r_1400_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(lean_object* v_m_1401_, lean_object* v_a_1402_, lean_object* v_b_1403_){
_start:
{
lean_object* v_size_1404_; lean_object* v_buckets_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1452_; 
v_size_1404_ = lean_ctor_get(v_m_1401_, 0);
v_buckets_1405_ = lean_ctor_get(v_m_1401_, 1);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_m_1401_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1407_ = v_m_1401_;
v_isShared_1408_ = v_isSharedCheck_1452_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_buckets_1405_);
lean_inc(v_size_1404_);
lean_dec(v_m_1401_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1452_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v_fst_1409_; lean_object* v_snd_1410_; lean_object* v___x_1411_; uint64_t v___x_1412_; uint64_t v___x_1413_; uint64_t v___x_1414_; uint64_t v___x_1415_; uint64_t v___x_1416_; uint64_t v_fold_1417_; uint64_t v___x_1418_; uint64_t v___x_1419_; uint64_t v___x_1420_; size_t v___x_1421_; size_t v___x_1422_; size_t v___x_1423_; size_t v___x_1424_; size_t v___x_1425_; lean_object* v_bkt_1426_; uint8_t v___x_1427_; 
v_fst_1409_ = lean_ctor_get(v_a_1402_, 0);
v_snd_1410_ = lean_ctor_get(v_a_1402_, 1);
v___x_1411_ = lean_array_get_size(v_buckets_1405_);
v___x_1412_ = l_String_instHashableRaw_hash(v_fst_1409_);
v___x_1413_ = l_String_instHashableRaw_hash(v_snd_1410_);
v___x_1414_ = lean_uint64_mix_hash(v___x_1412_, v___x_1413_);
v___x_1415_ = 32ULL;
v___x_1416_ = lean_uint64_shift_right(v___x_1414_, v___x_1415_);
v_fold_1417_ = lean_uint64_xor(v___x_1414_, v___x_1416_);
v___x_1418_ = 16ULL;
v___x_1419_ = lean_uint64_shift_right(v_fold_1417_, v___x_1418_);
v___x_1420_ = lean_uint64_xor(v_fold_1417_, v___x_1419_);
v___x_1421_ = lean_uint64_to_usize(v___x_1420_);
v___x_1422_ = lean_usize_of_nat(v___x_1411_);
v___x_1423_ = ((size_t)1ULL);
v___x_1424_ = lean_usize_sub(v___x_1422_, v___x_1423_);
v___x_1425_ = lean_usize_land(v___x_1421_, v___x_1424_);
v_bkt_1426_ = lean_array_uget_borrowed(v_buckets_1405_, v___x_1425_);
v___x_1427_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_1402_, v_bkt_1426_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; lean_object* v_size_x27_1429_; lean_object* v___x_1430_; lean_object* v_buckets_x27_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___x_1428_ = lean_unsigned_to_nat(1u);
v_size_x27_1429_ = lean_nat_add(v_size_1404_, v___x_1428_);
lean_dec(v_size_1404_);
lean_inc(v_bkt_1426_);
v___x_1430_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1430_, 0, v_a_1402_);
lean_ctor_set(v___x_1430_, 1, v_b_1403_);
lean_ctor_set(v___x_1430_, 2, v_bkt_1426_);
v_buckets_x27_1431_ = lean_array_uset(v_buckets_1405_, v___x_1425_, v___x_1430_);
v___x_1432_ = lean_unsigned_to_nat(4u);
v___x_1433_ = lean_nat_mul(v_size_x27_1429_, v___x_1432_);
v___x_1434_ = lean_unsigned_to_nat(3u);
v___x_1435_ = lean_nat_div(v___x_1433_, v___x_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_array_get_size(v_buckets_x27_1431_);
v___x_1437_ = lean_nat_dec_le(v___x_1435_, v___x_1436_);
lean_dec(v___x_1435_);
if (v___x_1437_ == 0)
{
lean_object* v_val_1438_; lean_object* v___x_1440_; 
v_val_1438_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_buckets_x27_1431_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 1, v_val_1438_);
lean_ctor_set(v___x_1407_, 0, v_size_x27_1429_);
v___x_1440_ = v___x_1407_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_size_x27_1429_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_val_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
else
{
lean_object* v___x_1443_; 
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 1, v_buckets_x27_1431_);
lean_ctor_set(v___x_1407_, 0, v_size_x27_1429_);
v___x_1443_ = v___x_1407_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_size_x27_1429_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_buckets_x27_1431_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
else
{
lean_object* v___x_1445_; lean_object* v_buckets_x27_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
lean_inc(v_bkt_1426_);
v___x_1445_ = lean_box(0);
v_buckets_x27_1446_ = lean_array_uset(v_buckets_1405_, v___x_1425_, v___x_1445_);
v___x_1447_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_1402_, v_b_1403_, v_bkt_1426_);
v___x_1448_ = lean_array_uset(v_buckets_x27_1446_, v___x_1425_, v___x_1447_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 1, v___x_1448_);
v___x_1450_ = v___x_1407_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_size_1404_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v___x_1448_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(uint8_t v___x_1455_, lean_object* v_as_1456_, size_t v_sz_1457_, size_t v_i_1458_, lean_object* v_b_1459_, lean_object* v___y_1460_){
_start:
{
uint8_t v___x_1462_; 
v___x_1462_ = lean_usize_dec_lt(v_i_1458_, v_sz_1457_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; 
v___x_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1463_, 0, v_b_1459_);
return v___x_1463_;
}
else
{
lean_object* v_snd_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1501_; 
v_snd_1464_ = lean_ctor_get(v_b_1459_, 1);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_b_1459_);
if (v_isSharedCheck_1501_ == 0)
{
lean_object* v_unused_1502_; 
v_unused_1502_ = lean_ctor_get(v_b_1459_, 0);
lean_dec(v_unused_1502_);
v___x_1466_ = v_b_1459_;
v_isShared_1467_ = v_isSharedCheck_1501_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_snd_1464_);
lean_dec(v_b_1459_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1501_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v_ref_1468_; lean_object* v_a_1469_; lean_object* v_ref_1470_; lean_object* v_msg_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1500_; 
v_ref_1468_ = lean_ctor_get(v___y_1460_, 5);
v_a_1469_ = lean_array_uget(v_as_1456_, v_i_1458_);
v_ref_1470_ = lean_ctor_get(v_a_1469_, 0);
v_msg_1471_ = lean_ctor_get(v_a_1469_, 1);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_a_1469_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1473_ = v_a_1469_;
v_isShared_1474_ = v_isSharedCheck_1500_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_msg_1471_);
lean_inc(v_ref_1470_);
lean_dec(v_a_1469_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1500_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1475_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v_ref_1492_; lean_object* v___y_1494_; lean_object* v___x_1497_; 
v___x_1475_ = lean_box(0);
v_ref_1492_ = l_Lean_replaceRef(v_ref_1470_, v_ref_1468_);
lean_dec(v_ref_1470_);
v___x_1497_ = l_Lean_Syntax_getPos_x3f(v_ref_1492_, v___x_1455_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v___x_1498_; 
v___x_1498_ = lean_unsigned_to_nat(0u);
v___y_1494_ = v___x_1498_;
goto v___jp_1493_;
}
else
{
lean_object* v_val_1499_; 
v_val_1499_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_val_1499_);
lean_dec_ref(v___x_1497_);
v___y_1494_ = v_val_1499_;
goto v___jp_1493_;
}
v___jp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 1, v___y_1478_);
lean_ctor_set(v___x_1466_, 0, v___y_1477_);
v___x_1480_ = v___x_1466_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___y_1477_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v___y_1478_);
v___x_1480_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v_pos2traces_1484_; lean_object* v___x_1486_; 
v___x_1481_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1482_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1464_, v___x_1480_, v___x_1481_);
v___x_1483_ = lean_array_push(v___x_1482_, v_msg_1471_);
v_pos2traces_1484_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1464_, v___x_1480_, v___x_1483_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 1, v_pos2traces_1484_);
lean_ctor_set(v___x_1473_, 0, v___x_1475_);
v___x_1486_ = v___x_1473_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_pos2traces_1484_);
v___x_1486_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
size_t v___x_1487_; size_t v___x_1488_; 
v___x_1487_ = ((size_t)1ULL);
v___x_1488_ = lean_usize_add(v_i_1458_, v___x_1487_);
v_i_1458_ = v___x_1488_;
v_b_1459_ = v___x_1486_;
goto _start;
}
}
}
v___jp_1493_:
{
lean_object* v___x_1495_; 
v___x_1495_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1492_, v___x_1455_);
lean_dec(v_ref_1492_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_inc(v___y_1494_);
v___y_1477_ = v___y_1494_;
v___y_1478_ = v___y_1494_;
goto v___jp_1476_;
}
else
{
lean_object* v_val_1496_; 
v_val_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_val_1496_);
lean_dec_ref(v___x_1495_);
v___y_1477_ = v___y_1494_;
v___y_1478_ = v_val_1496_;
goto v___jp_1476_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___boxed(lean_object* v___x_1503_, lean_object* v_as_1504_, lean_object* v_sz_1505_, lean_object* v_i_1506_, lean_object* v_b_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
uint8_t v___x_37756__boxed_1510_; size_t v_sz_boxed_1511_; size_t v_i_boxed_1512_; lean_object* v_res_1513_; 
v___x_37756__boxed_1510_ = lean_unbox(v___x_1503_);
v_sz_boxed_1511_ = lean_unbox_usize(v_sz_1505_);
lean_dec(v_sz_1505_);
v_i_boxed_1512_ = lean_unbox_usize(v_i_1506_);
lean_dec(v_i_1506_);
v_res_1513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_37756__boxed_1510_, v_as_1504_, v_sz_boxed_1511_, v_i_boxed_1512_, v_b_1507_, v___y_1508_);
lean_dec_ref(v___y_1508_);
lean_dec_ref(v_as_1504_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(uint8_t v___x_1514_, lean_object* v_as_1515_, size_t v_sz_1516_, size_t v_i_1517_, lean_object* v_b_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
uint8_t v___x_1522_; 
v___x_1522_ = lean_usize_dec_lt(v_i_1517_, v_sz_1516_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; 
v___x_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1523_, 0, v_b_1518_);
return v___x_1523_;
}
else
{
lean_object* v_snd_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1561_; 
v_snd_1524_ = lean_ctor_get(v_b_1518_, 1);
v_isSharedCheck_1561_ = !lean_is_exclusive(v_b_1518_);
if (v_isSharedCheck_1561_ == 0)
{
lean_object* v_unused_1562_; 
v_unused_1562_ = lean_ctor_get(v_b_1518_, 0);
lean_dec(v_unused_1562_);
v___x_1526_ = v_b_1518_;
v_isShared_1527_ = v_isSharedCheck_1561_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_snd_1524_);
lean_dec(v_b_1518_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1561_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v_ref_1528_; lean_object* v_a_1529_; lean_object* v_ref_1530_; lean_object* v_msg_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1560_; 
v_ref_1528_ = lean_ctor_get(v___y_1519_, 5);
v_a_1529_ = lean_array_uget(v_as_1515_, v_i_1517_);
v_ref_1530_ = lean_ctor_get(v_a_1529_, 0);
v_msg_1531_ = lean_ctor_get(v_a_1529_, 1);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_a_1529_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1533_ = v_a_1529_;
v_isShared_1534_ = v_isSharedCheck_1560_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_msg_1531_);
lean_inc(v_ref_1530_);
lean_dec(v_a_1529_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1560_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1535_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v_ref_1552_; lean_object* v___y_1554_; lean_object* v___x_1557_; 
v___x_1535_ = lean_box(0);
v_ref_1552_ = l_Lean_replaceRef(v_ref_1530_, v_ref_1528_);
lean_dec(v_ref_1530_);
v___x_1557_ = l_Lean_Syntax_getPos_x3f(v_ref_1552_, v___x_1514_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v___x_1558_; 
v___x_1558_ = lean_unsigned_to_nat(0u);
v___y_1554_ = v___x_1558_;
goto v___jp_1553_;
}
else
{
lean_object* v_val_1559_; 
v_val_1559_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_val_1559_);
lean_dec_ref(v___x_1557_);
v___y_1554_ = v_val_1559_;
goto v___jp_1553_;
}
v___jp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 1, v___y_1538_);
lean_ctor_set(v___x_1526_, 0, v___y_1537_);
v___x_1540_ = v___x_1526_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___y_1537_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v___y_1538_);
v___x_1540_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v_pos2traces_1544_; lean_object* v___x_1546_; 
v___x_1541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1542_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1524_, v___x_1540_, v___x_1541_);
v___x_1543_ = lean_array_push(v___x_1542_, v_msg_1531_);
v_pos2traces_1544_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1524_, v___x_1540_, v___x_1543_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 1, v_pos2traces_1544_);
lean_ctor_set(v___x_1533_, 0, v___x_1535_);
v___x_1546_ = v___x_1533_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1535_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_pos2traces_1544_);
v___x_1546_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
size_t v___x_1547_; size_t v___x_1548_; lean_object* v___x_1549_; 
v___x_1547_ = ((size_t)1ULL);
v___x_1548_ = lean_usize_add(v_i_1517_, v___x_1547_);
v___x_1549_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_1514_, v_as_1515_, v_sz_1516_, v___x_1548_, v___x_1546_, v___y_1519_);
return v___x_1549_;
}
}
}
v___jp_1553_:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1552_, v___x_1514_);
lean_dec(v_ref_1552_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_inc(v___y_1554_);
v___y_1537_ = v___y_1554_;
v___y_1538_ = v___y_1554_;
goto v___jp_1536_;
}
else
{
lean_object* v_val_1556_; 
v_val_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_val_1556_);
lean_dec_ref(v___x_1555_);
v___y_1537_ = v___y_1554_;
v___y_1538_ = v_val_1556_;
goto v___jp_1536_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40___boxed(lean_object* v___x_1563_, lean_object* v_as_1564_, lean_object* v_sz_1565_, lean_object* v_i_1566_, lean_object* v_b_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
uint8_t v___x_37837__boxed_1571_; size_t v_sz_boxed_1572_; size_t v_i_boxed_1573_; lean_object* v_res_1574_; 
v___x_37837__boxed_1571_ = lean_unbox(v___x_1563_);
v_sz_boxed_1572_ = lean_unbox_usize(v_sz_1565_);
lean_dec(v_sz_1565_);
v_i_boxed_1573_ = lean_unbox_usize(v_i_1566_);
lean_dec(v_i_1566_);
v_res_1574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_37837__boxed_1571_, v_as_1564_, v_sz_boxed_1572_, v_i_boxed_1573_, v_b_1567_, v___y_1568_, v___y_1569_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec_ref(v_as_1564_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(lean_object* v_init_1575_, uint8_t v___x_1576_, lean_object* v_n_1577_, lean_object* v_b_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
if (lean_obj_tag(v_n_1577_) == 0)
{
lean_object* v_cs_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; size_t v_sz_1585_; size_t v___x_1586_; lean_object* v___x_1587_; 
v_cs_1582_ = lean_ctor_get(v_n_1577_, 0);
v___x_1583_ = lean_box(0);
v___x_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1583_);
lean_ctor_set(v___x_1584_, 1, v_b_1578_);
v_sz_1585_ = lean_array_size(v_cs_1582_);
v___x_1586_ = ((size_t)0ULL);
v___x_1587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_1575_, v___x_1576_, v_cs_1582_, v_sz_1585_, v___x_1586_, v___x_1584_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1602_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1590_ = v___x_1587_;
v_isShared_1591_ = v_isSharedCheck_1602_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1587_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1602_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v_fst_1592_; 
v_fst_1592_ = lean_ctor_get(v_a_1588_, 0);
if (lean_obj_tag(v_fst_1592_) == 0)
{
lean_object* v_snd_1593_; lean_object* v___x_1594_; lean_object* v___x_1596_; 
v_snd_1593_ = lean_ctor_get(v_a_1588_, 1);
lean_inc(v_snd_1593_);
lean_dec(v_a_1588_);
v___x_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1594_, 0, v_snd_1593_);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v___x_1594_);
v___x_1596_ = v___x_1590_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1594_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
else
{
lean_object* v_val_1598_; lean_object* v___x_1600_; 
lean_inc_ref(v_fst_1592_);
lean_dec(v_a_1588_);
v_val_1598_ = lean_ctor_get(v_fst_1592_, 0);
lean_inc(v_val_1598_);
lean_dec_ref(v_fst_1592_);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v_val_1598_);
v___x_1600_ = v___x_1590_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_val_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
v_a_1603_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1587_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1587_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
else
{
lean_object* v_vs_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; size_t v_sz_1614_; size_t v___x_1615_; lean_object* v___x_1616_; 
v_vs_1611_ = lean_ctor_get(v_n_1577_, 0);
v___x_1612_ = lean_box(0);
v___x_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
lean_ctor_set(v___x_1613_, 1, v_b_1578_);
v_sz_1614_ = lean_array_size(v_vs_1611_);
v___x_1615_ = ((size_t)0ULL);
v___x_1616_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_1576_, v_vs_1611_, v_sz_1614_, v___x_1615_, v___x_1613_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1631_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1619_ = v___x_1616_;
v_isShared_1620_ = v_isSharedCheck_1631_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1616_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1631_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v_fst_1621_; 
v_fst_1621_ = lean_ctor_get(v_a_1617_, 0);
if (lean_obj_tag(v_fst_1621_) == 0)
{
lean_object* v_snd_1622_; lean_object* v___x_1623_; lean_object* v___x_1625_; 
v_snd_1622_ = lean_ctor_get(v_a_1617_, 1);
lean_inc(v_snd_1622_);
lean_dec(v_a_1617_);
v___x_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1623_, 0, v_snd_1622_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 0, v___x_1623_);
v___x_1625_ = v___x_1619_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1623_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
else
{
lean_object* v_val_1627_; lean_object* v___x_1629_; 
lean_inc_ref(v_fst_1621_);
lean_dec(v_a_1617_);
v_val_1627_ = lean_ctor_get(v_fst_1621_, 0);
lean_inc(v_val_1627_);
lean_dec_ref(v_fst_1621_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 0, v_val_1627_);
v___x_1629_ = v___x_1619_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_val_1627_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
v_a_1632_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1616_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1616_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(lean_object* v_init_1640_, uint8_t v___x_1641_, lean_object* v_as_1642_, size_t v_sz_1643_, size_t v_i_1644_, lean_object* v_b_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
uint8_t v___x_1649_; 
v___x_1649_ = lean_usize_dec_lt(v_i_1644_, v_sz_1643_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; 
v___x_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1650_, 0, v_b_1645_);
return v___x_1650_;
}
else
{
lean_object* v_snd_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1685_; 
v_snd_1651_ = lean_ctor_get(v_b_1645_, 1);
v_isSharedCheck_1685_ = !lean_is_exclusive(v_b_1645_);
if (v_isSharedCheck_1685_ == 0)
{
lean_object* v_unused_1686_; 
v_unused_1686_ = lean_ctor_get(v_b_1645_, 0);
lean_dec(v_unused_1686_);
v___x_1653_ = v_b_1645_;
v_isShared_1654_ = v_isSharedCheck_1685_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_snd_1651_);
lean_dec(v_b_1645_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1685_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v_a_1655_; lean_object* v___x_1656_; 
v_a_1655_ = lean_array_uget_borrowed(v_as_1642_, v_i_1644_);
lean_inc(v_snd_1651_);
v___x_1656_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1640_, v___x_1641_, v_a_1655_, v_snd_1651_, v___y_1646_, v___y_1647_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1676_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1659_ = v___x_1656_;
v_isShared_1660_ = v_isSharedCheck_1676_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1656_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1676_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
if (lean_obj_tag(v_a_1657_) == 0)
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1661_, 0, v_a_1657_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 0, v___x_1661_);
v___x_1663_ = v___x_1653_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1661_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_snd_1651_);
v___x_1663_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v___x_1665_; 
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 0, v___x_1663_);
v___x_1665_ = v___x_1659_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1663_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1669_; lean_object* v___x_1671_; 
lean_del_object(v___x_1659_);
lean_dec(v_snd_1651_);
v_a_1668_ = lean_ctor_get(v_a_1657_, 0);
lean_inc(v_a_1668_);
lean_dec_ref(v_a_1657_);
v___x_1669_ = lean_box(0);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 1, v_a_1668_);
lean_ctor_set(v___x_1653_, 0, v___x_1669_);
v___x_1671_ = v___x_1653_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1669_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_a_1668_);
v___x_1671_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
size_t v___x_1672_; size_t v___x_1673_; 
v___x_1672_ = ((size_t)1ULL);
v___x_1673_ = lean_usize_add(v_i_1644_, v___x_1672_);
v_i_1644_ = v___x_1673_;
v_b_1645_ = v___x_1671_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
lean_del_object(v___x_1653_);
lean_dec(v_snd_1651_);
v_a_1677_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v___x_1656_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1656_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39___boxed(lean_object* v_init_1687_, lean_object* v___x_1688_, lean_object* v_as_1689_, lean_object* v_sz_1690_, lean_object* v_i_1691_, lean_object* v_b_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
uint8_t v___x_37918__boxed_1696_; size_t v_sz_boxed_1697_; size_t v_i_boxed_1698_; lean_object* v_res_1699_; 
v___x_37918__boxed_1696_ = lean_unbox(v___x_1688_);
v_sz_boxed_1697_ = lean_unbox_usize(v_sz_1690_);
lean_dec(v_sz_1690_);
v_i_boxed_1698_ = lean_unbox_usize(v_i_1691_);
lean_dec(v_i_1691_);
v_res_1699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_1687_, v___x_37918__boxed_1696_, v_as_1689_, v_sz_boxed_1697_, v_i_boxed_1698_, v_b_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec_ref(v_as_1689_);
lean_dec_ref(v_init_1687_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27___boxed(lean_object* v_init_1700_, lean_object* v___x_1701_, lean_object* v_n_1702_, lean_object* v_b_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
uint8_t v___x_37938__boxed_1707_; lean_object* v_res_1708_; 
v___x_37938__boxed_1707_ = lean_unbox(v___x_1701_);
v_res_1708_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1700_, v___x_37938__boxed_1707_, v_n_1702_, v_b_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec_ref(v_n_1702_);
lean_dec_ref(v_init_1700_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(uint8_t v___x_1709_, lean_object* v_as_1710_, size_t v_sz_1711_, size_t v_i_1712_, lean_object* v_b_1713_, lean_object* v___y_1714_){
_start:
{
uint8_t v___x_1716_; 
v___x_1716_ = lean_usize_dec_lt(v_i_1712_, v_sz_1711_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; 
v___x_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1717_, 0, v_b_1713_);
return v___x_1717_;
}
else
{
lean_object* v_snd_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1755_; 
v_snd_1718_ = lean_ctor_get(v_b_1713_, 1);
v_isSharedCheck_1755_ = !lean_is_exclusive(v_b_1713_);
if (v_isSharedCheck_1755_ == 0)
{
lean_object* v_unused_1756_; 
v_unused_1756_ = lean_ctor_get(v_b_1713_, 0);
lean_dec(v_unused_1756_);
v___x_1720_ = v_b_1713_;
v_isShared_1721_ = v_isSharedCheck_1755_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_snd_1718_);
lean_dec(v_b_1713_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1755_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v_ref_1722_; lean_object* v_a_1723_; lean_object* v_ref_1724_; lean_object* v_msg_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1754_; 
v_ref_1722_ = lean_ctor_get(v___y_1714_, 5);
v_a_1723_ = lean_array_uget(v_as_1710_, v_i_1712_);
v_ref_1724_ = lean_ctor_get(v_a_1723_, 0);
v_msg_1725_ = lean_ctor_get(v_a_1723_, 1);
v_isSharedCheck_1754_ = !lean_is_exclusive(v_a_1723_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1727_ = v_a_1723_;
v_isShared_1728_ = v_isSharedCheck_1754_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_msg_1725_);
lean_inc(v_ref_1724_);
lean_dec(v_a_1723_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1754_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1729_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v_ref_1746_; lean_object* v___y_1748_; lean_object* v___x_1751_; 
v___x_1729_ = lean_box(0);
v_ref_1746_ = l_Lean_replaceRef(v_ref_1724_, v_ref_1722_);
lean_dec(v_ref_1724_);
v___x_1751_ = l_Lean_Syntax_getPos_x3f(v_ref_1746_, v___x_1709_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v___x_1752_; 
v___x_1752_ = lean_unsigned_to_nat(0u);
v___y_1748_ = v___x_1752_;
goto v___jp_1747_;
}
else
{
lean_object* v_val_1753_; 
v_val_1753_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_val_1753_);
lean_dec_ref(v___x_1751_);
v___y_1748_ = v_val_1753_;
goto v___jp_1747_;
}
v___jp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 1, v___y_1732_);
lean_ctor_set(v___x_1720_, 0, v___y_1731_);
v___x_1734_ = v___x_1720_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___y_1731_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v___y_1732_);
v___x_1734_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v_pos2traces_1738_; lean_object* v___x_1740_; 
v___x_1735_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1736_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1718_, v___x_1734_, v___x_1735_);
v___x_1737_ = lean_array_push(v___x_1736_, v_msg_1725_);
v_pos2traces_1738_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1718_, v___x_1734_, v___x_1737_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 1, v_pos2traces_1738_);
lean_ctor_set(v___x_1727_, 0, v___x_1729_);
v___x_1740_ = v___x_1727_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1729_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_pos2traces_1738_);
v___x_1740_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
size_t v___x_1741_; size_t v___x_1742_; 
v___x_1741_ = ((size_t)1ULL);
v___x_1742_ = lean_usize_add(v_i_1712_, v___x_1741_);
v_i_1712_ = v___x_1742_;
v_b_1713_ = v___x_1740_;
goto _start;
}
}
}
v___jp_1747_:
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1746_, v___x_1709_);
lean_dec(v_ref_1746_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_inc(v___y_1748_);
v___y_1731_ = v___y_1748_;
v___y_1732_ = v___y_1748_;
goto v___jp_1730_;
}
else
{
lean_object* v_val_1750_; 
v_val_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_val_1750_);
lean_dec_ref(v___x_1749_);
v___y_1731_ = v___y_1748_;
v___y_1732_ = v_val_1750_;
goto v___jp_1730_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg___boxed(lean_object* v___x_1757_, lean_object* v_as_1758_, lean_object* v_sz_1759_, lean_object* v_i_1760_, lean_object* v_b_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
uint8_t v___x_38121__boxed_1764_; size_t v_sz_boxed_1765_; size_t v_i_boxed_1766_; lean_object* v_res_1767_; 
v___x_38121__boxed_1764_ = lean_unbox(v___x_1757_);
v_sz_boxed_1765_ = lean_unbox_usize(v_sz_1759_);
lean_dec(v_sz_1759_);
v_i_boxed_1766_ = lean_unbox_usize(v_i_1760_);
lean_dec(v_i_1760_);
v_res_1767_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_38121__boxed_1764_, v_as_1758_, v_sz_boxed_1765_, v_i_boxed_1766_, v_b_1761_, v___y_1762_);
lean_dec_ref(v___y_1762_);
lean_dec_ref(v_as_1758_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(uint8_t v___x_1768_, lean_object* v_as_1769_, size_t v_sz_1770_, size_t v_i_1771_, lean_object* v_b_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
uint8_t v___x_1776_; 
v___x_1776_ = lean_usize_dec_lt(v_i_1771_, v_sz_1770_);
if (v___x_1776_ == 0)
{
lean_object* v___x_1777_; 
v___x_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1777_, 0, v_b_1772_);
return v___x_1777_;
}
else
{
lean_object* v_snd_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1815_; 
v_snd_1778_ = lean_ctor_get(v_b_1772_, 1);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_b_1772_);
if (v_isSharedCheck_1815_ == 0)
{
lean_object* v_unused_1816_; 
v_unused_1816_ = lean_ctor_get(v_b_1772_, 0);
lean_dec(v_unused_1816_);
v___x_1780_ = v_b_1772_;
v_isShared_1781_ = v_isSharedCheck_1815_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_snd_1778_);
lean_dec(v_b_1772_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1815_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v_ref_1782_; lean_object* v_a_1783_; lean_object* v_ref_1784_; lean_object* v_msg_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1814_; 
v_ref_1782_ = lean_ctor_get(v___y_1773_, 5);
v_a_1783_ = lean_array_uget(v_as_1769_, v_i_1771_);
v_ref_1784_ = lean_ctor_get(v_a_1783_, 0);
v_msg_1785_ = lean_ctor_get(v_a_1783_, 1);
v_isSharedCheck_1814_ = !lean_is_exclusive(v_a_1783_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1787_ = v_a_1783_;
v_isShared_1788_ = v_isSharedCheck_1814_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_msg_1785_);
lean_inc(v_ref_1784_);
lean_dec(v_a_1783_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1814_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1789_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v_ref_1806_; lean_object* v___y_1808_; lean_object* v___x_1811_; 
v___x_1789_ = lean_box(0);
v_ref_1806_ = l_Lean_replaceRef(v_ref_1784_, v_ref_1782_);
lean_dec(v_ref_1784_);
v___x_1811_ = l_Lean_Syntax_getPos_x3f(v_ref_1806_, v___x_1768_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v___x_1812_; 
v___x_1812_ = lean_unsigned_to_nat(0u);
v___y_1808_ = v___x_1812_;
goto v___jp_1807_;
}
else
{
lean_object* v_val_1813_; 
v_val_1813_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_val_1813_);
lean_dec_ref(v___x_1811_);
v___y_1808_ = v_val_1813_;
goto v___jp_1807_;
}
v___jp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 1, v___y_1792_);
lean_ctor_set(v___x_1780_, 0, v___y_1791_);
v___x_1794_ = v___x_1780_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___y_1791_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v___y_1792_);
v___x_1794_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v_pos2traces_1798_; lean_object* v___x_1800_; 
v___x_1795_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1796_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1778_, v___x_1794_, v___x_1795_);
v___x_1797_ = lean_array_push(v___x_1796_, v_msg_1785_);
v_pos2traces_1798_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1778_, v___x_1794_, v___x_1797_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 1, v_pos2traces_1798_);
lean_ctor_set(v___x_1787_, 0, v___x_1789_);
v___x_1800_ = v___x_1787_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1789_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v_pos2traces_1798_);
v___x_1800_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
size_t v___x_1801_; size_t v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = ((size_t)1ULL);
v___x_1802_ = lean_usize_add(v_i_1771_, v___x_1801_);
v___x_1803_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_1768_, v_as_1769_, v_sz_1770_, v___x_1802_, v___x_1800_, v___y_1773_);
return v___x_1803_;
}
}
}
v___jp_1807_:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1806_, v___x_1768_);
lean_dec(v_ref_1806_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_inc(v___y_1808_);
v___y_1791_ = v___y_1808_;
v___y_1792_ = v___y_1808_;
goto v___jp_1790_;
}
else
{
lean_object* v_val_1810_; 
v_val_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_val_1810_);
lean_dec_ref(v___x_1809_);
v___y_1791_ = v___y_1808_;
v___y_1792_ = v_val_1810_;
goto v___jp_1790_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28___boxed(lean_object* v___x_1817_, lean_object* v_as_1818_, lean_object* v_sz_1819_, lean_object* v_i_1820_, lean_object* v_b_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
uint8_t v___x_38201__boxed_1825_; size_t v_sz_boxed_1826_; size_t v_i_boxed_1827_; lean_object* v_res_1828_; 
v___x_38201__boxed_1825_ = lean_unbox(v___x_1817_);
v_sz_boxed_1826_ = lean_unbox_usize(v_sz_1819_);
lean_dec(v_sz_1819_);
v_i_boxed_1827_ = lean_unbox_usize(v_i_1820_);
lean_dec(v_i_1820_);
v_res_1828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_38201__boxed_1825_, v_as_1818_, v_sz_boxed_1826_, v_i_boxed_1827_, v_b_1821_, v___y_1822_, v___y_1823_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec_ref(v_as_1818_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(uint8_t v___x_1829_, lean_object* v_t_1830_, lean_object* v_init_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_root_1835_; lean_object* v_tail_1836_; lean_object* v___x_1837_; 
v_root_1835_ = lean_ctor_get(v_t_1830_, 0);
v_tail_1836_ = lean_ctor_get(v_t_1830_, 1);
lean_inc_ref(v_init_1831_);
v___x_1837_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1831_, v___x_1829_, v_root_1835_, v_init_1831_, v___y_1832_, v___y_1833_);
lean_dec_ref(v_init_1831_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1874_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1840_ = v___x_1837_;
v_isShared_1841_ = v_isSharedCheck_1874_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1874_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
if (lean_obj_tag(v_a_1838_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1844_; 
v_a_1842_ = lean_ctor_get(v_a_1838_, 0);
lean_inc(v_a_1842_);
lean_dec_ref(v_a_1838_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v_a_1842_);
v___x_1844_ = v___x_1840_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
else
{
lean_object* v_a_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; size_t v_sz_1849_; size_t v___x_1850_; lean_object* v___x_1851_; 
lean_del_object(v___x_1840_);
v_a_1846_ = lean_ctor_get(v_a_1838_, 0);
lean_inc(v_a_1846_);
lean_dec_ref(v_a_1838_);
v___x_1847_ = lean_box(0);
v___x_1848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
lean_ctor_set(v___x_1848_, 1, v_a_1846_);
v_sz_1849_ = lean_array_size(v_tail_1836_);
v___x_1850_ = ((size_t)0ULL);
v___x_1851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_1829_, v_tail_1836_, v_sz_1849_, v___x_1850_, v___x_1848_, v___y_1832_, v___y_1833_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1865_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1854_ = v___x_1851_;
v_isShared_1855_ = v_isSharedCheck_1865_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1851_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1865_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v_fst_1856_; 
v_fst_1856_ = lean_ctor_get(v_a_1852_, 0);
if (lean_obj_tag(v_fst_1856_) == 0)
{
lean_object* v_snd_1857_; lean_object* v___x_1859_; 
v_snd_1857_ = lean_ctor_get(v_a_1852_, 1);
lean_inc(v_snd_1857_);
lean_dec(v_a_1852_);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v_snd_1857_);
v___x_1859_ = v___x_1854_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_snd_1857_);
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
lean_object* v_val_1861_; lean_object* v___x_1863_; 
lean_inc_ref(v_fst_1856_);
lean_dec(v_a_1852_);
v_val_1861_ = lean_ctor_get(v_fst_1856_, 0);
lean_inc(v_val_1861_);
lean_dec_ref(v_fst_1856_);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v_val_1861_);
v___x_1863_ = v___x_1854_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_val_1861_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
v_a_1866_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1851_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1851_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
}
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
v_a_1875_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1837_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1837_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19___boxed(lean_object* v___x_1883_, lean_object* v_t_1884_, lean_object* v_init_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
uint8_t v___x_38282__boxed_1889_; lean_object* v_res_1890_; 
v___x_38282__boxed_1889_ = lean_unbox(v___x_1883_);
v_res_1890_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_38282__boxed_1889_, v_t_1884_, v_init_1885_, v___y_1886_, v___y_1887_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec_ref(v_t_1884_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(lean_object* v_x_1891_, lean_object* v_x_1892_){
_start:
{
if (lean_obj_tag(v_x_1892_) == 0)
{
return v_x_1891_;
}
else
{
lean_object* v_key_1893_; lean_object* v_value_1894_; lean_object* v_tail_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v_key_1893_ = lean_ctor_get(v_x_1892_, 0);
v_value_1894_ = lean_ctor_get(v_x_1892_, 1);
v_tail_1895_ = lean_ctor_get(v_x_1892_, 2);
lean_inc(v_value_1894_);
lean_inc(v_key_1893_);
v___x_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1896_, 0, v_key_1893_);
lean_ctor_set(v___x_1896_, 1, v_value_1894_);
v___x_1897_ = lean_array_push(v_x_1891_, v___x_1896_);
v_x_1891_ = v___x_1897_;
v_x_1892_ = v_tail_1895_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22___boxed(lean_object* v_x_1899_, lean_object* v_x_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_x_1899_, v_x_1900_);
lean_dec(v_x_1900_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(lean_object* v_as_1902_, size_t v_i_1903_, size_t v_stop_1904_, lean_object* v_b_1905_){
_start:
{
uint8_t v___x_1906_; 
v___x_1906_ = lean_usize_dec_eq(v_i_1903_, v_stop_1904_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; lean_object* v___x_1908_; size_t v___x_1909_; size_t v___x_1910_; 
v___x_1907_ = lean_array_uget_borrowed(v_as_1902_, v_i_1903_);
v___x_1908_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_b_1905_, v___x_1907_);
v___x_1909_ = ((size_t)1ULL);
v___x_1910_ = lean_usize_add(v_i_1903_, v___x_1909_);
v_i_1903_ = v___x_1910_;
v_b_1905_ = v___x_1908_;
goto _start;
}
else
{
return v_b_1905_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23___boxed(lean_object* v_as_1912_, lean_object* v_i_1913_, lean_object* v_stop_1914_, lean_object* v_b_1915_){
_start:
{
size_t v_i_boxed_1916_; size_t v_stop_boxed_1917_; lean_object* v_res_1918_; 
v_i_boxed_1916_ = lean_unbox_usize(v_i_1913_);
lean_dec(v_i_1913_);
v_stop_boxed_1917_ = lean_unbox_usize(v_stop_1914_);
lean_dec(v_stop_1914_);
v_res_1918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_as_1912_, v_i_boxed_1916_, v_stop_boxed_1917_, v_b_1915_);
lean_dec_ref(v_as_1912_);
return v_res_1918_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0(void){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1919_ = lean_unsigned_to_nat(32u);
v___x_1920_ = lean_mk_empty_array_with_capacity(v___x_1919_);
v___x_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
return v___x_1921_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1(void){
_start:
{
size_t v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1922_ = ((size_t)5ULL);
v___x_1923_ = lean_unsigned_to_nat(0u);
v___x_1924_ = lean_unsigned_to_nat(32u);
v___x_1925_ = lean_mk_empty_array_with_capacity(v___x_1924_);
v___x_1926_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0);
v___x_1927_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
lean_ctor_set(v___x_1927_, 1, v___x_1925_);
lean_ctor_set(v___x_1927_, 2, v___x_1923_);
lean_ctor_set(v___x_1927_, 3, v___x_1923_);
lean_ctor_set_usize(v___x_1927_, 4, v___x_1922_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(lean_object* v___y_1928_){
_start:
{
lean_object* v___x_1930_; lean_object* v_traceState_1931_; lean_object* v_traces_1932_; lean_object* v___x_1933_; lean_object* v_traceState_1934_; lean_object* v_env_1935_; lean_object* v_nextMacroScope_1936_; lean_object* v_ngen_1937_; lean_object* v_auxDeclNGen_1938_; lean_object* v_cache_1939_; lean_object* v_messages_1940_; lean_object* v_infoState_1941_; lean_object* v_snapshotTasks_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1961_; 
v___x_1930_ = lean_st_ref_get(v___y_1928_);
v_traceState_1931_ = lean_ctor_get(v___x_1930_, 4);
lean_inc_ref(v_traceState_1931_);
lean_dec(v___x_1930_);
v_traces_1932_ = lean_ctor_get(v_traceState_1931_, 0);
lean_inc_ref(v_traces_1932_);
lean_dec_ref(v_traceState_1931_);
v___x_1933_ = lean_st_ref_take(v___y_1928_);
v_traceState_1934_ = lean_ctor_get(v___x_1933_, 4);
v_env_1935_ = lean_ctor_get(v___x_1933_, 0);
v_nextMacroScope_1936_ = lean_ctor_get(v___x_1933_, 1);
v_ngen_1937_ = lean_ctor_get(v___x_1933_, 2);
v_auxDeclNGen_1938_ = lean_ctor_get(v___x_1933_, 3);
v_cache_1939_ = lean_ctor_get(v___x_1933_, 5);
v_messages_1940_ = lean_ctor_get(v___x_1933_, 6);
v_infoState_1941_ = lean_ctor_get(v___x_1933_, 7);
v_snapshotTasks_1942_ = lean_ctor_get(v___x_1933_, 8);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1944_ = v___x_1933_;
v_isShared_1945_ = v_isSharedCheck_1961_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_snapshotTasks_1942_);
lean_inc(v_infoState_1941_);
lean_inc(v_messages_1940_);
lean_inc(v_cache_1939_);
lean_inc(v_traceState_1934_);
lean_inc(v_auxDeclNGen_1938_);
lean_inc(v_ngen_1937_);
lean_inc(v_nextMacroScope_1936_);
lean_inc(v_env_1935_);
lean_dec(v___x_1933_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1961_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
uint64_t v_tid_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1959_; 
v_tid_1946_ = lean_ctor_get_uint64(v_traceState_1934_, sizeof(void*)*1);
v_isSharedCheck_1959_ = !lean_is_exclusive(v_traceState_1934_);
if (v_isSharedCheck_1959_ == 0)
{
lean_object* v_unused_1960_; 
v_unused_1960_ = lean_ctor_get(v_traceState_1934_, 0);
lean_dec(v_unused_1960_);
v___x_1948_ = v_traceState_1934_;
v_isShared_1949_ = v_isSharedCheck_1959_;
goto v_resetjp_1947_;
}
else
{
lean_dec(v_traceState_1934_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1959_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1950_; lean_object* v___x_1952_; 
v___x_1950_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 0, v___x_1950_);
v___x_1952_ = v___x_1948_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1950_);
lean_ctor_set_uint64(v_reuseFailAlloc_1958_, sizeof(void*)*1, v_tid_1946_);
v___x_1952_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
lean_object* v___x_1954_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v___x_1952_);
v___x_1954_ = v___x_1944_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_env_1935_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v_nextMacroScope_1936_);
lean_ctor_set(v_reuseFailAlloc_1957_, 2, v_ngen_1937_);
lean_ctor_set(v_reuseFailAlloc_1957_, 3, v_auxDeclNGen_1938_);
lean_ctor_set(v_reuseFailAlloc_1957_, 4, v___x_1952_);
lean_ctor_set(v_reuseFailAlloc_1957_, 5, v_cache_1939_);
lean_ctor_set(v_reuseFailAlloc_1957_, 6, v_messages_1940_);
lean_ctor_set(v_reuseFailAlloc_1957_, 7, v_infoState_1941_);
lean_ctor_set(v_reuseFailAlloc_1957_, 8, v_snapshotTasks_1942_);
v___x_1954_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = lean_st_ref_set(v___y_1928_, v___x_1954_);
v___x_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1956_, 0, v_traces_1932_);
return v___x_1956_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___boxed(lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_1962_);
lean_dec(v___y_1962_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(lean_object* v_hi_1965_, lean_object* v_pivot_1966_, lean_object* v_as_1967_, lean_object* v_i_1968_, lean_object* v_k_1969_){
_start:
{
uint8_t v___x_1970_; 
v___x_1970_ = lean_nat_dec_lt(v_k_1969_, v_hi_1965_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
lean_dec(v_k_1969_);
v___x_1971_ = lean_array_fswap(v_as_1967_, v_i_1968_, v_hi_1965_);
v___x_1972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1972_, 0, v_i_1968_);
lean_ctor_set(v___x_1972_, 1, v___x_1971_);
return v___x_1972_;
}
else
{
lean_object* v___x_1973_; lean_object* v_fst_1974_; lean_object* v_fst_1975_; lean_object* v_fst_1976_; lean_object* v_fst_1977_; uint8_t v___x_1978_; 
v___x_1973_ = lean_array_fget_borrowed(v_as_1967_, v_k_1969_);
v_fst_1974_ = lean_ctor_get(v___x_1973_, 0);
v_fst_1975_ = lean_ctor_get(v_pivot_1966_, 0);
v_fst_1976_ = lean_ctor_get(v_fst_1974_, 0);
v_fst_1977_ = lean_ctor_get(v_fst_1975_, 0);
v___x_1978_ = lean_nat_dec_lt(v_fst_1976_, v_fst_1977_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = lean_unsigned_to_nat(1u);
v___x_1980_ = lean_nat_add(v_k_1969_, v___x_1979_);
lean_dec(v_k_1969_);
v_k_1969_ = v___x_1980_;
goto _start;
}
else
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1982_ = lean_array_fswap(v_as_1967_, v_i_1968_, v_k_1969_);
v___x_1983_ = lean_unsigned_to_nat(1u);
v___x_1984_ = lean_nat_add(v_i_1968_, v___x_1983_);
lean_dec(v_i_1968_);
v___x_1985_ = lean_nat_add(v_k_1969_, v___x_1983_);
lean_dec(v_k_1969_);
v_as_1967_ = v___x_1982_;
v_i_1968_ = v___x_1984_;
v_k_1969_ = v___x_1985_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg___boxed(lean_object* v_hi_1987_, lean_object* v_pivot_1988_, lean_object* v_as_1989_, lean_object* v_i_1990_, lean_object* v_k_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_1987_, v_pivot_1988_, v_as_1989_, v_i_1990_, v_k_1991_);
lean_dec_ref(v_pivot_1988_);
lean_dec(v_hi_1987_);
return v_res_1992_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(lean_object* v_x_1993_, lean_object* v_x_1994_){
_start:
{
lean_object* v_fst_1995_; lean_object* v_fst_1996_; lean_object* v_fst_1997_; lean_object* v_fst_1998_; uint8_t v___x_1999_; 
v_fst_1995_ = lean_ctor_get(v_x_1993_, 0);
v_fst_1996_ = lean_ctor_get(v_x_1994_, 0);
v_fst_1997_ = lean_ctor_get(v_fst_1995_, 0);
v_fst_1998_ = lean_ctor_get(v_fst_1996_, 0);
v___x_1999_ = lean_nat_dec_lt(v_fst_1997_, v_fst_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0___boxed(lean_object* v_x_2000_, lean_object* v_x_2001_){
_start:
{
uint8_t v_res_2002_; lean_object* v_r_2003_; 
v_res_2002_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v_x_2000_, v_x_2001_);
lean_dec_ref(v_x_2001_);
lean_dec_ref(v_x_2000_);
v_r_2003_ = lean_box(v_res_2002_);
return v_r_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(lean_object* v_n_2004_, lean_object* v_as_2005_, lean_object* v_lo_2006_, lean_object* v_hi_2007_){
_start:
{
lean_object* v___y_2009_; uint8_t v___x_2019_; 
v___x_2019_ = lean_nat_dec_lt(v_lo_2006_, v_hi_2007_);
if (v___x_2019_ == 0)
{
lean_dec(v_lo_2006_);
return v_as_2005_;
}
else
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v_mid_2022_; lean_object* v___y_2024_; lean_object* v___y_2030_; lean_object* v___x_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; 
v___x_2020_ = lean_nat_add(v_lo_2006_, v_hi_2007_);
v___x_2021_ = lean_unsigned_to_nat(1u);
v_mid_2022_ = lean_nat_shiftr(v___x_2020_, v___x_2021_);
lean_dec(v___x_2020_);
v___x_2035_ = lean_array_fget_borrowed(v_as_2005_, v_mid_2022_);
v___x_2036_ = lean_array_fget_borrowed(v_as_2005_, v_lo_2006_);
v___x_2037_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2035_, v___x_2036_);
if (v___x_2037_ == 0)
{
v___y_2030_ = v_as_2005_;
goto v___jp_2029_;
}
else
{
lean_object* v___x_2038_; 
v___x_2038_ = lean_array_fswap(v_as_2005_, v_lo_2006_, v_mid_2022_);
v___y_2030_ = v___x_2038_;
goto v___jp_2029_;
}
v___jp_2023_:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; 
v___x_2025_ = lean_array_fget_borrowed(v___y_2024_, v_mid_2022_);
v___x_2026_ = lean_array_fget_borrowed(v___y_2024_, v_hi_2007_);
v___x_2027_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2025_, v___x_2026_);
if (v___x_2027_ == 0)
{
lean_dec(v_mid_2022_);
v___y_2009_ = v___y_2024_;
goto v___jp_2008_;
}
else
{
lean_object* v___x_2028_; 
v___x_2028_ = lean_array_fswap(v___y_2024_, v_mid_2022_, v_hi_2007_);
lean_dec(v_mid_2022_);
v___y_2009_ = v___x_2028_;
goto v___jp_2008_;
}
}
v___jp_2029_:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; 
v___x_2031_ = lean_array_fget_borrowed(v___y_2030_, v_hi_2007_);
v___x_2032_ = lean_array_fget_borrowed(v___y_2030_, v_lo_2006_);
v___x_2033_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2031_, v___x_2032_);
if (v___x_2033_ == 0)
{
v___y_2024_ = v___y_2030_;
goto v___jp_2023_;
}
else
{
lean_object* v___x_2034_; 
v___x_2034_ = lean_array_fswap(v___y_2030_, v_lo_2006_, v_hi_2007_);
v___y_2024_ = v___x_2034_;
goto v___jp_2023_;
}
}
}
v___jp_2008_:
{
lean_object* v_pivot_2010_; lean_object* v___x_2011_; lean_object* v_fst_2012_; lean_object* v_snd_2013_; uint8_t v___x_2014_; 
v_pivot_2010_ = lean_array_fget(v___y_2009_, v_hi_2007_);
lean_inc_n(v_lo_2006_, 2);
v___x_2011_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_2007_, v_pivot_2010_, v___y_2009_, v_lo_2006_, v_lo_2006_);
lean_dec(v_pivot_2010_);
v_fst_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_fst_2012_);
v_snd_2013_ = lean_ctor_get(v___x_2011_, 1);
lean_inc(v_snd_2013_);
lean_dec_ref(v___x_2011_);
v___x_2014_ = lean_nat_dec_le(v_hi_2007_, v_fst_2012_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2015_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_2004_, v_snd_2013_, v_lo_2006_, v_fst_2012_);
v___x_2016_ = lean_unsigned_to_nat(1u);
v___x_2017_ = lean_nat_add(v_fst_2012_, v___x_2016_);
lean_dec(v_fst_2012_);
v_as_2005_ = v___x_2015_;
v_lo_2006_ = v___x_2017_;
goto _start;
}
else
{
lean_dec(v_fst_2012_);
lean_dec(v_lo_2006_);
return v_snd_2013_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___boxed(lean_object* v_n_2039_, lean_object* v_as_2040_, lean_object* v_lo_2041_, lean_object* v_hi_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_2039_, v_as_2040_, v_lo_2041_, v_hi_2042_);
lean_dec(v_hi_2042_);
lean_dec(v_n_2039_);
return v_res_2043_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2044_ = lean_box(0);
v___x_2045_ = lean_unsigned_to_nat(16u);
v___x_2046_ = lean_mk_array(v___x_2045_, v___x_2044_);
return v___x_2046_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1(void){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v_pos2traces_2049_; 
v___x_2047_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0);
v___x_2048_ = lean_unsigned_to_nat(0u);
v_pos2traces_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_2049_, 0, v___x_2048_);
lean_ctor_set(v_pos2traces_2049_, 1, v___x_2047_);
return v_pos2traces_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10(lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v_options_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v_options_2056_ = lean_ctor_get(v___y_2050_, 2);
v___x_2057_ = l_Lean_trace_profiler_output;
v___x_2058_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(v_options_2056_, v___x_2057_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v___x_2059_; uint8_t v___x_2060_; 
v___x_2059_ = l_Lean_trace_profiler_serve;
v___x_2060_ = l_Lean_Option_get___at___00main_spec__8(v_options_2056_, v___x_2059_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2061_; lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2128_; 
v___x_2061_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_2051_);
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2064_ = v___x_2061_;
v_isShared_2065_ = v_isSharedCheck_2128_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2061_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2128_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
uint8_t v___x_2066_; 
v___x_2066_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_2062_);
if (v___x_2066_ == 0)
{
lean_object* v___x_2067_; lean_object* v_pos2traces_2068_; lean_object* v___x_2069_; 
lean_del_object(v___x_2064_);
v___x_2067_ = lean_unsigned_to_nat(0u);
v_pos2traces_2068_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1);
v___x_2069_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_2066_, v_a_2062_, v_pos2traces_2068_, v___y_2050_, v___y_2051_);
lean_dec(v_a_2062_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; lean_object* v___y_2072_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2089_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v___y_2098_; lean_object* v_size_2104_; lean_object* v_buckets_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; uint8_t v___x_2108_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_a_2070_);
lean_dec_ref(v___x_2069_);
v_size_2104_ = lean_ctor_get(v_a_2070_, 0);
lean_inc(v_size_2104_);
v_buckets_2105_ = lean_ctor_get(v_a_2070_, 1);
lean_inc_ref(v_buckets_2105_);
lean_dec(v_a_2070_);
v___x_2106_ = lean_mk_empty_array_with_capacity(v_size_2104_);
lean_dec(v_size_2104_);
v___x_2107_ = lean_array_get_size(v_buckets_2105_);
v___x_2108_ = lean_nat_dec_lt(v___x_2067_, v___x_2107_);
if (v___x_2108_ == 0)
{
lean_dec_ref(v_buckets_2105_);
v___y_2098_ = v___x_2106_;
goto v___jp_2097_;
}
else
{
uint8_t v___x_2109_; 
v___x_2109_ = lean_nat_dec_le(v___x_2107_, v___x_2107_);
if (v___x_2109_ == 0)
{
if (v___x_2108_ == 0)
{
lean_dec_ref(v_buckets_2105_);
v___y_2098_ = v___x_2106_;
goto v___jp_2097_;
}
else
{
size_t v___x_2110_; size_t v___x_2111_; lean_object* v___x_2112_; 
v___x_2110_ = ((size_t)0ULL);
v___x_2111_ = lean_usize_of_nat(v___x_2107_);
v___x_2112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_buckets_2105_, v___x_2110_, v___x_2111_, v___x_2106_);
lean_dec_ref(v_buckets_2105_);
v___y_2098_ = v___x_2112_;
goto v___jp_2097_;
}
}
else
{
size_t v___x_2113_; size_t v___x_2114_; lean_object* v___x_2115_; 
v___x_2113_ = ((size_t)0ULL);
v___x_2114_ = lean_usize_of_nat(v___x_2107_);
v___x_2115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_buckets_2105_, v___x_2113_, v___x_2114_, v___x_2106_);
lean_dec_ref(v_buckets_2105_);
v___y_2098_ = v___x_2115_;
goto v___jp_2097_;
}
}
v___jp_2071_:
{
lean_object* v___x_2073_; size_t v_sz_2074_; size_t v___x_2075_; lean_object* v___x_2076_; 
v___x_2073_ = lean_box(0);
v_sz_2074_ = lean_array_size(v___y_2072_);
v___x_2075_ = ((size_t)0ULL);
v___x_2076_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_2060_, v___y_2072_, v_sz_2074_, v___x_2075_, v___x_2073_, v___y_2050_, v___y_2051_);
lean_dec_ref(v___y_2072_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2083_ == 0)
{
lean_object* v_unused_2084_; 
v_unused_2084_ = lean_ctor_get(v___x_2076_, 0);
lean_dec(v_unused_2084_);
v___x_2078_ = v___x_2076_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_dec(v___x_2076_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v___x_2073_);
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2073_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
else
{
return v___x_2076_;
}
}
v___jp_2085_:
{
lean_object* v___x_2090_; 
v___x_2090_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v___y_2087_, v___y_2088_, v___y_2086_, v___y_2089_);
lean_dec(v___y_2089_);
lean_dec(v___y_2087_);
v___y_2072_ = v___x_2090_;
goto v___jp_2071_;
}
v___jp_2091_:
{
uint8_t v___x_2096_; 
v___x_2096_ = lean_nat_dec_le(v___y_2095_, v___y_2093_);
if (v___x_2096_ == 0)
{
lean_dec(v___y_2093_);
lean_inc(v___y_2095_);
v___y_2086_ = v___y_2095_;
v___y_2087_ = v___y_2092_;
v___y_2088_ = v___y_2094_;
v___y_2089_ = v___y_2095_;
goto v___jp_2085_;
}
else
{
v___y_2086_ = v___y_2095_;
v___y_2087_ = v___y_2092_;
v___y_2088_ = v___y_2094_;
v___y_2089_ = v___y_2093_;
goto v___jp_2085_;
}
}
v___jp_2097_:
{
lean_object* v___x_2099_; uint8_t v___x_2100_; 
v___x_2099_ = lean_array_get_size(v___y_2098_);
v___x_2100_ = lean_nat_dec_eq(v___x_2099_, v___x_2067_);
if (v___x_2100_ == 0)
{
lean_object* v___x_2101_; lean_object* v___x_2102_; uint8_t v___x_2103_; 
v___x_2101_ = lean_unsigned_to_nat(1u);
v___x_2102_ = lean_nat_sub(v___x_2099_, v___x_2101_);
v___x_2103_ = lean_nat_dec_le(v___x_2067_, v___x_2102_);
if (v___x_2103_ == 0)
{
lean_inc(v___x_2102_);
v___y_2092_ = v___x_2099_;
v___y_2093_ = v___x_2102_;
v___y_2094_ = v___y_2098_;
v___y_2095_ = v___x_2102_;
goto v___jp_2091_;
}
else
{
v___y_2092_ = v___x_2099_;
v___y_2093_ = v___x_2102_;
v___y_2094_ = v___y_2098_;
v___y_2095_ = v___x_2067_;
goto v___jp_2091_;
}
}
else
{
v___y_2072_ = v___y_2098_;
goto v___jp_2071_;
}
}
}
else
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
v_a_2116_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___x_2069_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2069_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_a_2116_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
else
{
lean_object* v___x_2124_; lean_object* v___x_2126_; 
lean_dec(v_a_2062_);
v___x_2124_ = lean_box(0);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 0, v___x_2124_);
v___x_2126_ = v___x_2064_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
else
{
goto v___jp_2053_;
}
}
else
{
lean_dec_ref(v___x_2058_);
goto v___jp_2053_;
}
v___jp_2053_:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = lean_box(0);
v___x_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
return v___x_2055_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10___boxed(lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(lean_object* v_as_2133_, size_t v_sz_2134_, size_t v_i_2135_, lean_object* v_b_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
uint8_t v___x_2140_; 
v___x_2140_ = lean_usize_dec_lt(v_i_2135_, v_sz_2134_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; 
v___x_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2141_, 0, v_b_2136_);
return v___x_2141_;
}
else
{
lean_object* v_options_2142_; lean_object* v_a_2143_; lean_object* v___x_2144_; 
v_options_2142_ = lean_ctor_get(v___y_2137_, 2);
v_a_2143_ = lean_array_uget_borrowed(v_as_2133_, v_i_2135_);
lean_inc_ref(v_options_2142_);
lean_inc(v_a_2143_);
v___x_2144_ = l_Lean_Compiler_LCNF_resumeCompilation(v_a_2143_, v_options_2142_, v___y_2137_, v___y_2138_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v___x_2145_; 
lean_dec_ref(v___x_2144_);
v___x_2145_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2137_, v___y_2138_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v___x_2146_; size_t v___x_2147_; size_t v___x_2148_; 
lean_dec_ref(v___x_2145_);
v___x_2146_ = lean_box(0);
v___x_2147_ = ((size_t)1ULL);
v___x_2148_ = lean_usize_add(v_i_2135_, v___x_2147_);
v_i_2135_ = v___x_2148_;
v_b_2136_ = v___x_2146_;
goto _start;
}
else
{
return v___x_2145_;
}
}
else
{
lean_object* v_a_2150_; lean_object* v___x_2151_; 
v_a_2150_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2150_);
lean_dec_ref(v___x_2144_);
v___x_2151_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2137_, v___y_2138_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2158_ == 0)
{
lean_object* v_unused_2159_; 
v_unused_2159_ = lean_ctor_get(v___x_2151_, 0);
lean_dec(v_unused_2159_);
v___x_2153_ = v___x_2151_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_dec(v___x_2151_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
lean_ctor_set_tag(v___x_2153_, 1);
lean_ctor_set(v___x_2153_, 0, v_a_2150_);
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2150_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
else
{
lean_dec(v_a_2150_);
return v___x_2151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11___boxed(lean_object* v_as_2160_, lean_object* v_sz_2161_, lean_object* v_i_2162_, lean_object* v_b_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
size_t v_sz_boxed_2167_; size_t v_i_boxed_2168_; lean_object* v_res_2169_; 
v_sz_boxed_2167_ = lean_unbox_usize(v_sz_2161_);
lean_dec(v_sz_2161_);
v_i_boxed_2168_ = lean_unbox_usize(v_i_2162_);
lean_dec(v_i_2162_);
v_res_2169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_as_2160_, v_sz_boxed_2167_, v_i_boxed_2168_, v_b_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec_ref(v_as_2160_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(lean_object* v_as_2170_, size_t v_sz_2171_, size_t v_i_2172_, lean_object* v_b_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
uint8_t v___x_2177_; 
v___x_2177_ = lean_usize_dec_lt(v_i_2172_, v_sz_2171_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; 
v___x_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2178_, 0, v_b_2173_);
return v___x_2178_;
}
else
{
lean_object* v_a_2179_; lean_object* v_declNames_2180_; lean_object* v___x_2181_; size_t v_sz_2182_; size_t v___x_2183_; lean_object* v___x_2184_; 
v_a_2179_ = lean_array_uget_borrowed(v_as_2170_, v_i_2172_);
v_declNames_2180_ = lean_ctor_get(v_a_2179_, 0);
v___x_2181_ = lean_box(0);
v_sz_2182_ = lean_array_size(v_declNames_2180_);
v___x_2183_ = ((size_t)0ULL);
v___x_2184_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_declNames_2180_, v_sz_2182_, v___x_2183_, v___x_2181_, v___y_2174_, v___y_2175_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v___x_2185_; 
lean_dec_ref(v___x_2184_);
v___x_2185_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v___y_2175_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; lean_object* v_unreported_2187_; lean_object* v___x_2188_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2186_);
lean_dec_ref(v___x_2185_);
v_unreported_2187_ = lean_ctor_get(v_a_2186_, 1);
lean_inc_ref(v_unreported_2187_);
lean_dec(v_a_2186_);
v___x_2188_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(v_unreported_2187_, v___x_2181_, v___y_2174_, v___y_2175_);
lean_dec_ref(v_unreported_2187_);
if (lean_obj_tag(v___x_2188_) == 0)
{
size_t v___x_2189_; size_t v___x_2190_; 
lean_dec_ref(v___x_2188_);
v___x_2189_ = ((size_t)1ULL);
v___x_2190_ = lean_usize_add(v_i_2172_, v___x_2189_);
v_i_2172_ = v___x_2190_;
v_b_2173_ = v___x_2181_;
goto _start;
}
else
{
return v___x_2188_;
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
v_a_2192_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2185_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2185_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
else
{
return v___x_2184_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13___boxed(lean_object* v_as_2200_, lean_object* v_sz_2201_, lean_object* v_i_2202_, lean_object* v_b_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
size_t v_sz_boxed_2207_; size_t v_i_boxed_2208_; lean_object* v_res_2209_; 
v_sz_boxed_2207_ = lean_unbox_usize(v_sz_2201_);
lean_dec(v_sz_2201_);
v_i_boxed_2208_ = lean_unbox_usize(v_i_2202_);
lean_dec(v_i_2202_);
v_res_2209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v_as_2200_, v_sz_boxed_2207_, v_i_boxed_2208_, v_b_2203_, v___y_2204_, v___y_2205_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec_ref(v_as_2200_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object* v_as_2210_, size_t v_i_2211_, size_t v_stop_2212_, lean_object* v_b_2213_){
_start:
{
uint8_t v___x_2214_; 
v___x_2214_ = lean_usize_dec_eq(v_i_2211_, v_stop_2212_);
if (v___x_2214_ == 0)
{
lean_object* v___x_2215_; lean_object* v_name_2216_; lean_object* v___x_2217_; size_t v___x_2218_; size_t v___x_2219_; 
v___x_2215_ = lean_array_uget_borrowed(v_as_2210_, v_i_2211_);
v_name_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_name_2216_);
v___x_2217_ = l_Lean_Compiler_LCNF_setDeclPublic(v_b_2213_, v_name_2216_);
v___x_2218_ = ((size_t)1ULL);
v___x_2219_ = lean_usize_add(v_i_2211_, v___x_2218_);
v_i_2211_ = v___x_2219_;
v_b_2213_ = v___x_2217_;
goto _start;
}
else
{
return v_b_2213_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object* v_as_2221_, lean_object* v_i_2222_, lean_object* v_stop_2223_, lean_object* v_b_2224_){
_start:
{
size_t v_i_boxed_2225_; size_t v_stop_boxed_2226_; lean_object* v_res_2227_; 
v_i_boxed_2225_ = lean_unbox_usize(v_i_2222_);
lean_dec(v_i_2222_);
v_stop_boxed_2226_ = lean_unbox_usize(v_stop_2223_);
lean_dec(v_stop_2223_);
v_res_2227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v_as_2221_, v_i_boxed_2225_, v_stop_boxed_2226_, v_b_2224_);
lean_dec_ref(v_as_2221_);
return v_res_2227_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0(uint8_t v___y_2228_, uint8_t v_suppressElabErrors_2229_, lean_object* v_x_2230_){
_start:
{
if (lean_obj_tag(v_x_2230_) == 1)
{
lean_object* v_pre_2231_; 
v_pre_2231_ = lean_ctor_get(v_x_2230_, 0);
switch(lean_obj_tag(v_pre_2231_))
{
case 1:
{
lean_object* v_pre_2232_; 
v_pre_2232_ = lean_ctor_get(v_pre_2231_, 0);
switch(lean_obj_tag(v_pre_2232_))
{
case 0:
{
lean_object* v_str_2233_; lean_object* v_str_2234_; lean_object* v___x_2235_; uint8_t v___x_2236_; 
v_str_2233_ = lean_ctor_get(v_x_2230_, 1);
v_str_2234_ = lean_ctor_get(v_pre_2231_, 1);
v___x_2235_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0));
v___x_2236_ = lean_string_dec_eq(v_str_2234_, v___x_2235_);
if (v___x_2236_ == 0)
{
lean_object* v___x_2237_; uint8_t v___x_2238_; 
v___x_2237_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1));
v___x_2238_ = lean_string_dec_eq(v_str_2234_, v___x_2237_);
if (v___x_2238_ == 0)
{
return v___y_2228_;
}
else
{
lean_object* v___x_2239_; uint8_t v___x_2240_; 
v___x_2239_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2));
v___x_2240_ = lean_string_dec_eq(v_str_2233_, v___x_2239_);
if (v___x_2240_ == 0)
{
return v___y_2228_;
}
else
{
return v_suppressElabErrors_2229_;
}
}
}
else
{
lean_object* v___x_2241_; uint8_t v___x_2242_; 
v___x_2241_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3));
v___x_2242_ = lean_string_dec_eq(v_str_2233_, v___x_2241_);
if (v___x_2242_ == 0)
{
return v___y_2228_;
}
else
{
return v_suppressElabErrors_2229_;
}
}
}
case 1:
{
lean_object* v_pre_2243_; 
v_pre_2243_ = lean_ctor_get(v_pre_2232_, 0);
if (lean_obj_tag(v_pre_2243_) == 0)
{
lean_object* v_str_2244_; lean_object* v_str_2245_; lean_object* v_str_2246_; lean_object* v___x_2247_; uint8_t v___x_2248_; 
v_str_2244_ = lean_ctor_get(v_x_2230_, 1);
v_str_2245_ = lean_ctor_get(v_pre_2231_, 1);
v_str_2246_ = lean_ctor_get(v_pre_2232_, 1);
v___x_2247_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4));
v___x_2248_ = lean_string_dec_eq(v_str_2246_, v___x_2247_);
if (v___x_2248_ == 0)
{
return v___y_2228_;
}
else
{
lean_object* v___x_2249_; uint8_t v___x_2250_; 
v___x_2249_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5));
v___x_2250_ = lean_string_dec_eq(v_str_2245_, v___x_2249_);
if (v___x_2250_ == 0)
{
return v___y_2228_;
}
else
{
lean_object* v___x_2251_; uint8_t v___x_2252_; 
v___x_2251_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6));
v___x_2252_ = lean_string_dec_eq(v_str_2244_, v___x_2251_);
if (v___x_2252_ == 0)
{
return v___y_2228_;
}
else
{
return v_suppressElabErrors_2229_;
}
}
}
}
else
{
return v___y_2228_;
}
}
default: 
{
return v___y_2228_;
}
}
}
case 0:
{
lean_object* v_str_2253_; lean_object* v___x_2254_; uint8_t v___x_2255_; 
v_str_2253_ = lean_ctor_get(v_x_2230_, 1);
v___x_2254_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_2255_ = lean_string_dec_eq(v_str_2253_, v___x_2254_);
if (v___x_2255_ == 0)
{
return v___y_2228_;
}
else
{
return v_suppressElabErrors_2229_;
}
}
default: 
{
return v___y_2228_;
}
}
}
else
{
return v___y_2228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0___boxed(lean_object* v___y_2256_, lean_object* v_suppressElabErrors_2257_, lean_object* v_x_2258_){
_start:
{
uint8_t v___y_38886__boxed_2259_; uint8_t v_suppressElabErrors_boxed_2260_; uint8_t v_res_2261_; lean_object* v_r_2262_; 
v___y_38886__boxed_2259_ = lean_unbox(v___y_2256_);
v_suppressElabErrors_boxed_2260_ = lean_unbox(v_suppressElabErrors_2257_);
v_res_2261_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0(v___y_38886__boxed_2259_, v_suppressElabErrors_boxed_2260_, v_x_2258_);
lean_dec(v_x_2258_);
v_r_2262_ = lean_box(v_res_2261_);
return v_r_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(lean_object* v_ref_2263_, lean_object* v_msgData_2264_, uint8_t v_severity_2265_, uint8_t v_isSilent_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v___y_2271_; lean_object* v___y_2272_; uint8_t v___y_2273_; uint8_t v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2307_; uint8_t v___y_2308_; uint8_t v___y_2309_; uint8_t v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2332_; uint8_t v___y_2333_; uint8_t v___y_2334_; uint8_t v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2343_; uint8_t v___y_2344_; uint8_t v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___y_2348_; uint8_t v___y_2349_; uint8_t v___x_2354_; uint8_t v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2360_; uint8_t v___y_2361_; uint8_t v___y_2362_; uint8_t v___y_2364_; uint8_t v___x_2379_; 
v___x_2354_ = 2;
v___x_2379_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2265_, v___x_2354_);
if (v___x_2379_ == 0)
{
v___y_2364_ = v___x_2379_;
goto v___jp_2363_;
}
else
{
uint8_t v___x_2380_; 
lean_inc_ref(v_msgData_2264_);
v___x_2380_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2264_);
v___y_2364_ = v___x_2380_;
goto v___jp_2363_;
}
v___jp_2270_:
{
lean_object* v___x_2280_; lean_object* v_currNamespace_2281_; lean_object* v_openDecls_2282_; lean_object* v_env_2283_; lean_object* v_nextMacroScope_2284_; lean_object* v_ngen_2285_; lean_object* v_auxDeclNGen_2286_; lean_object* v_traceState_2287_; lean_object* v_cache_2288_; lean_object* v_messages_2289_; lean_object* v_infoState_2290_; lean_object* v_snapshotTasks_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2305_; 
v___x_2280_ = lean_st_ref_take(v___y_2279_);
v_currNamespace_2281_ = lean_ctor_get(v___y_2278_, 6);
v_openDecls_2282_ = lean_ctor_get(v___y_2278_, 7);
v_env_2283_ = lean_ctor_get(v___x_2280_, 0);
v_nextMacroScope_2284_ = lean_ctor_get(v___x_2280_, 1);
v_ngen_2285_ = lean_ctor_get(v___x_2280_, 2);
v_auxDeclNGen_2286_ = lean_ctor_get(v___x_2280_, 3);
v_traceState_2287_ = lean_ctor_get(v___x_2280_, 4);
v_cache_2288_ = lean_ctor_get(v___x_2280_, 5);
v_messages_2289_ = lean_ctor_get(v___x_2280_, 6);
v_infoState_2290_ = lean_ctor_get(v___x_2280_, 7);
v_snapshotTasks_2291_ = lean_ctor_get(v___x_2280_, 8);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2293_ = v___x_2280_;
v_isShared_2294_ = v_isSharedCheck_2305_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_snapshotTasks_2291_);
lean_inc(v_infoState_2290_);
lean_inc(v_messages_2289_);
lean_inc(v_cache_2288_);
lean_inc(v_traceState_2287_);
lean_inc(v_auxDeclNGen_2286_);
lean_inc(v_ngen_2285_);
lean_inc(v_nextMacroScope_2284_);
lean_inc(v_env_2283_);
lean_dec(v___x_2280_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2305_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2300_; 
lean_inc(v_openDecls_2282_);
lean_inc(v_currNamespace_2281_);
v___x_2295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2295_, 0, v_currNamespace_2281_);
lean_ctor_set(v___x_2295_, 1, v_openDecls_2282_);
v___x_2296_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
lean_ctor_set(v___x_2296_, 1, v___y_2276_);
lean_inc_ref(v___y_2272_);
lean_inc_ref(v___y_2277_);
v___x_2297_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2297_, 0, v___y_2277_);
lean_ctor_set(v___x_2297_, 1, v___y_2275_);
lean_ctor_set(v___x_2297_, 2, v___y_2271_);
lean_ctor_set(v___x_2297_, 3, v___y_2272_);
lean_ctor_set(v___x_2297_, 4, v___x_2296_);
lean_ctor_set_uint8(v___x_2297_, sizeof(void*)*5, v___y_2273_);
lean_ctor_set_uint8(v___x_2297_, sizeof(void*)*5 + 1, v___y_2274_);
lean_ctor_set_uint8(v___x_2297_, sizeof(void*)*5 + 2, v_isSilent_2266_);
v___x_2298_ = l_Lean_MessageLog_add(v___x_2297_, v_messages_2289_);
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 6, v___x_2298_);
v___x_2300_ = v___x_2293_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_env_2283_);
lean_ctor_set(v_reuseFailAlloc_2304_, 1, v_nextMacroScope_2284_);
lean_ctor_set(v_reuseFailAlloc_2304_, 2, v_ngen_2285_);
lean_ctor_set(v_reuseFailAlloc_2304_, 3, v_auxDeclNGen_2286_);
lean_ctor_set(v_reuseFailAlloc_2304_, 4, v_traceState_2287_);
lean_ctor_set(v_reuseFailAlloc_2304_, 5, v_cache_2288_);
lean_ctor_set(v_reuseFailAlloc_2304_, 6, v___x_2298_);
lean_ctor_set(v_reuseFailAlloc_2304_, 7, v_infoState_2290_);
lean_ctor_set(v_reuseFailAlloc_2304_, 8, v_snapshotTasks_2291_);
v___x_2300_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2301_ = lean_st_ref_set(v___y_2279_, v___x_2300_);
v___x_2302_ = lean_box(0);
v___x_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
return v___x_2303_;
}
}
}
v___jp_2306_:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2330_; 
v___x_2315_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2264_);
v___x_2316_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v___x_2315_, v___y_2267_, v___y_2268_);
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2319_ = v___x_2316_;
v_isShared_2320_ = v_isSharedCheck_2330_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2316_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2330_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
lean_inc_ref_n(v___y_2311_, 2);
v___x_2321_ = l_Lean_FileMap_toPosition(v___y_2311_, v___y_2312_);
lean_dec(v___y_2312_);
v___x_2322_ = l_Lean_FileMap_toPosition(v___y_2311_, v___y_2314_);
lean_dec(v___y_2314_);
v___x_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
v___x_2324_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1));
if (v___y_2308_ == 0)
{
lean_del_object(v___x_2319_);
lean_dec_ref(v___y_2307_);
v___y_2271_ = v___x_2323_;
v___y_2272_ = v___x_2324_;
v___y_2273_ = v___y_2309_;
v___y_2274_ = v___y_2310_;
v___y_2275_ = v___x_2321_;
v___y_2276_ = v_a_2317_;
v___y_2277_ = v___y_2313_;
v___y_2278_ = v___y_2267_;
v___y_2279_ = v___y_2268_;
goto v___jp_2270_;
}
else
{
uint8_t v___x_2325_; 
lean_inc(v_a_2317_);
v___x_2325_ = l_Lean_MessageData_hasTag(v___y_2307_, v_a_2317_);
if (v___x_2325_ == 0)
{
lean_object* v___x_2326_; lean_object* v___x_2328_; 
lean_dec_ref(v___x_2323_);
lean_dec_ref(v___x_2321_);
lean_dec(v_a_2317_);
v___x_2326_ = lean_box(0);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 0, v___x_2326_);
v___x_2328_ = v___x_2319_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2326_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
else
{
lean_del_object(v___x_2319_);
v___y_2271_ = v___x_2323_;
v___y_2272_ = v___x_2324_;
v___y_2273_ = v___y_2309_;
v___y_2274_ = v___y_2310_;
v___y_2275_ = v___x_2321_;
v___y_2276_ = v_a_2317_;
v___y_2277_ = v___y_2313_;
v___y_2278_ = v___y_2267_;
v___y_2279_ = v___y_2268_;
goto v___jp_2270_;
}
}
}
}
v___jp_2331_:
{
lean_object* v___x_2340_; 
v___x_2340_ = l_Lean_Syntax_getTailPos_x3f(v___y_2337_, v___y_2334_);
lean_dec(v___y_2337_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_inc(v___y_2339_);
v___y_2307_ = v___y_2332_;
v___y_2308_ = v___y_2333_;
v___y_2309_ = v___y_2334_;
v___y_2310_ = v___y_2335_;
v___y_2311_ = v___y_2336_;
v___y_2312_ = v___y_2339_;
v___y_2313_ = v___y_2338_;
v___y_2314_ = v___y_2339_;
goto v___jp_2306_;
}
else
{
lean_object* v_val_2341_; 
v_val_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_val_2341_);
lean_dec_ref(v___x_2340_);
v___y_2307_ = v___y_2332_;
v___y_2308_ = v___y_2333_;
v___y_2309_ = v___y_2334_;
v___y_2310_ = v___y_2335_;
v___y_2311_ = v___y_2336_;
v___y_2312_ = v___y_2339_;
v___y_2313_ = v___y_2338_;
v___y_2314_ = v_val_2341_;
goto v___jp_2306_;
}
}
v___jp_2342_:
{
lean_object* v_ref_2350_; lean_object* v___x_2351_; 
v_ref_2350_ = l_Lean_replaceRef(v_ref_2263_, v___y_2347_);
v___x_2351_ = l_Lean_Syntax_getPos_x3f(v_ref_2350_, v___y_2345_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v___x_2352_; 
v___x_2352_ = lean_unsigned_to_nat(0u);
v___y_2332_ = v___y_2343_;
v___y_2333_ = v___y_2344_;
v___y_2334_ = v___y_2345_;
v___y_2335_ = v___y_2349_;
v___y_2336_ = v___y_2346_;
v___y_2337_ = v_ref_2350_;
v___y_2338_ = v___y_2348_;
v___y_2339_ = v___x_2352_;
goto v___jp_2331_;
}
else
{
lean_object* v_val_2353_; 
v_val_2353_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_val_2353_);
lean_dec_ref(v___x_2351_);
v___y_2332_ = v___y_2343_;
v___y_2333_ = v___y_2344_;
v___y_2334_ = v___y_2345_;
v___y_2335_ = v___y_2349_;
v___y_2336_ = v___y_2346_;
v___y_2337_ = v_ref_2350_;
v___y_2338_ = v___y_2348_;
v___y_2339_ = v_val_2353_;
goto v___jp_2331_;
}
}
v___jp_2355_:
{
if (v___y_2362_ == 0)
{
v___y_2343_ = v___y_2359_;
v___y_2344_ = v___y_2356_;
v___y_2345_ = v___y_2361_;
v___y_2346_ = v___y_2357_;
v___y_2347_ = v___y_2358_;
v___y_2348_ = v___y_2360_;
v___y_2349_ = v_severity_2265_;
goto v___jp_2342_;
}
else
{
v___y_2343_ = v___y_2359_;
v___y_2344_ = v___y_2356_;
v___y_2345_ = v___y_2361_;
v___y_2346_ = v___y_2357_;
v___y_2347_ = v___y_2358_;
v___y_2348_ = v___y_2360_;
v___y_2349_ = v___x_2354_;
goto v___jp_2342_;
}
}
v___jp_2363_:
{
if (v___y_2364_ == 0)
{
lean_object* v_fileName_2365_; lean_object* v_fileMap_2366_; lean_object* v_options_2367_; lean_object* v_ref_2368_; uint8_t v_suppressElabErrors_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___f_2372_; uint8_t v___x_2373_; uint8_t v___x_2374_; 
v_fileName_2365_ = lean_ctor_get(v___y_2267_, 0);
v_fileMap_2366_ = lean_ctor_get(v___y_2267_, 1);
v_options_2367_ = lean_ctor_get(v___y_2267_, 2);
v_ref_2368_ = lean_ctor_get(v___y_2267_, 5);
v_suppressElabErrors_2369_ = lean_ctor_get_uint8(v___y_2267_, sizeof(void*)*14 + 1);
v___x_2370_ = lean_box(v___y_2364_);
v___x_2371_ = lean_box(v_suppressElabErrors_2369_);
v___f_2372_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2372_, 0, v___x_2370_);
lean_closure_set(v___f_2372_, 1, v___x_2371_);
v___x_2373_ = 1;
v___x_2374_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2265_, v___x_2373_);
if (v___x_2374_ == 0)
{
v___y_2356_ = v_suppressElabErrors_2369_;
v___y_2357_ = v_fileMap_2366_;
v___y_2358_ = v_ref_2368_;
v___y_2359_ = v___f_2372_;
v___y_2360_ = v_fileName_2365_;
v___y_2361_ = v___y_2364_;
v___y_2362_ = v___x_2374_;
goto v___jp_2355_;
}
else
{
lean_object* v___x_2375_; uint8_t v___x_2376_; 
v___x_2375_ = l_Lean_warningAsError;
v___x_2376_ = l_Lean_Option_get___at___00main_spec__8(v_options_2367_, v___x_2375_);
v___y_2356_ = v_suppressElabErrors_2369_;
v___y_2357_ = v_fileMap_2366_;
v___y_2358_ = v_ref_2368_;
v___y_2359_ = v___f_2372_;
v___y_2360_ = v_fileName_2365_;
v___y_2361_ = v___y_2364_;
v___y_2362_ = v___x_2376_;
goto v___jp_2355_;
}
}
else
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
lean_dec_ref(v_msgData_2264_);
v___x_2377_ = lean_box(0);
v___x_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
return v___x_2378_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___boxed(lean_object* v_ref_2381_, lean_object* v_msgData_2382_, lean_object* v_severity_2383_, lean_object* v_isSilent_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
uint8_t v_severity_boxed_2388_; uint8_t v_isSilent_boxed_2389_; lean_object* v_res_2390_; 
v_severity_boxed_2388_ = lean_unbox(v_severity_2383_);
v_isSilent_boxed_2389_ = lean_unbox(v_isSilent_2384_);
v_res_2390_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(v_ref_2381_, v_msgData_2382_, v_severity_boxed_2388_, v_isSilent_boxed_2389_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v_ref_2381_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(lean_object* v_msgData_2391_, uint8_t v_severity_2392_, uint8_t v_isSilent_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v_ref_2397_; lean_object* v___x_2398_; 
v_ref_2397_ = lean_ctor_get(v___y_2394_, 5);
v___x_2398_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(v_ref_2397_, v_msgData_2391_, v_severity_2392_, v_isSilent_2393_, v___y_2394_, v___y_2395_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30___boxed(lean_object* v_msgData_2399_, lean_object* v_severity_2400_, lean_object* v_isSilent_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
uint8_t v_severity_boxed_2405_; uint8_t v_isSilent_boxed_2406_; lean_object* v_res_2407_; 
v_severity_boxed_2405_ = lean_unbox(v_severity_2400_);
v_isSilent_boxed_2406_ = lean_unbox(v_isSilent_2401_);
v_res_2407_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2399_, v_severity_boxed_2405_, v_isSilent_boxed_2406_, v___y_2402_, v___y_2403_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14(lean_object* v_msgData_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
uint8_t v___x_2412_; uint8_t v___x_2413_; lean_object* v___x_2414_; 
v___x_2412_ = 2;
v___x_2413_ = 0;
v___x_2414_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2408_, v___x_2412_, v___x_2413_, v___y_2409_, v___y_2410_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14___boxed(lean_object* v_msgData_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Lean_logError___at___00main_spec__14(v_msgData_2415_, v___y_2416_, v___y_2417_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(lean_object* v_x2_2420_, lean_object* v_as_2421_, size_t v_i_2422_, size_t v_stop_2423_, lean_object* v_b_2424_){
_start:
{
uint8_t v___x_2425_; 
v___x_2425_ = lean_usize_dec_eq(v_i_2422_, v_stop_2423_);
if (v___x_2425_ == 0)
{
lean_object* v___x_2426_; lean_object* v___x_2427_; size_t v___x_2428_; size_t v___x_2429_; 
v___x_2426_ = lean_array_uget_borrowed(v_as_2421_, v_i_2422_);
lean_inc_ref(v_x2_2420_);
lean_inc(v___x_2426_);
v___x_2427_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2426_, v_x2_2420_, v_b_2424_);
v___x_2428_ = ((size_t)1ULL);
v___x_2429_ = lean_usize_add(v_i_2422_, v___x_2428_);
v_i_2422_ = v___x_2429_;
v_b_2424_ = v___x_2427_;
goto _start;
}
else
{
lean_dec_ref(v_x2_2420_);
return v_b_2424_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(lean_object* v_x2_2431_, lean_object* v_as_2432_, lean_object* v_i_2433_, lean_object* v_stop_2434_, lean_object* v_b_2435_){
_start:
{
size_t v_i_boxed_2436_; size_t v_stop_boxed_2437_; lean_object* v_res_2438_; 
v_i_boxed_2436_ = lean_unbox_usize(v_i_2433_);
lean_dec(v_i_2433_);
v_stop_boxed_2437_ = lean_unbox_usize(v_stop_2434_);
lean_dec(v_stop_2434_);
v_res_2438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v_x2_2431_, v_as_2432_, v_i_boxed_2436_, v_stop_boxed_2437_, v_b_2435_);
lean_dec_ref(v_as_2432_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object* v_as_2439_, size_t v_i_2440_, size_t v_stop_2441_, lean_object* v_b_2442_){
_start:
{
lean_object* v___y_2444_; uint8_t v___x_2448_; 
v___x_2448_ = lean_usize_dec_eq(v_i_2440_, v_stop_2441_);
if (v___x_2448_ == 0)
{
lean_object* v___x_2449_; lean_object* v_declNames_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; uint8_t v___x_2453_; 
v___x_2449_ = lean_array_uget_borrowed(v_as_2439_, v_i_2440_);
v_declNames_2450_ = lean_ctor_get(v___x_2449_, 0);
v___x_2451_ = lean_unsigned_to_nat(0u);
v___x_2452_ = lean_array_get_size(v_declNames_2450_);
v___x_2453_ = lean_nat_dec_lt(v___x_2451_, v___x_2452_);
if (v___x_2453_ == 0)
{
v___y_2444_ = v_b_2442_;
goto v___jp_2443_;
}
else
{
uint8_t v___x_2454_; 
v___x_2454_ = lean_nat_dec_le(v___x_2452_, v___x_2452_);
if (v___x_2454_ == 0)
{
if (v___x_2453_ == 0)
{
v___y_2444_ = v_b_2442_;
goto v___jp_2443_;
}
else
{
size_t v___x_2455_; size_t v___x_2456_; lean_object* v___x_2457_; 
v___x_2455_ = ((size_t)0ULL);
v___x_2456_ = lean_usize_of_nat(v___x_2452_);
lean_inc(v___x_2449_);
v___x_2457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2449_, v_declNames_2450_, v___x_2455_, v___x_2456_, v_b_2442_);
v___y_2444_ = v___x_2457_;
goto v___jp_2443_;
}
}
else
{
size_t v___x_2458_; size_t v___x_2459_; lean_object* v___x_2460_; 
v___x_2458_ = ((size_t)0ULL);
v___x_2459_ = lean_usize_of_nat(v___x_2452_);
lean_inc(v___x_2449_);
v___x_2460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2449_, v_declNames_2450_, v___x_2458_, v___x_2459_, v_b_2442_);
v___y_2444_ = v___x_2460_;
goto v___jp_2443_;
}
}
}
else
{
return v_b_2442_;
}
v___jp_2443_:
{
size_t v___x_2445_; size_t v___x_2446_; 
v___x_2445_ = ((size_t)1ULL);
v___x_2446_ = lean_usize_add(v_i_2440_, v___x_2445_);
v_i_2440_ = v___x_2446_;
v_b_2442_ = v___y_2444_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object* v_as_2461_, lean_object* v_i_2462_, lean_object* v_stop_2463_, lean_object* v_b_2464_){
_start:
{
size_t v_i_boxed_2465_; size_t v_stop_boxed_2466_; lean_object* v_res_2467_; 
v_i_boxed_2465_ = lean_unbox_usize(v_i_2462_);
lean_dec(v_i_2462_);
v_stop_boxed_2466_ = lean_unbox_usize(v_stop_2463_);
lean_dec(v_stop_2463_);
v_res_2467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v_as_2461_, v_i_boxed_2465_, v_stop_boxed_2466_, v_b_2464_);
lean_dec_ref(v_as_2461_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(lean_object* v_a_2468_, lean_object* v_as_2469_, size_t v_i_2470_, size_t v_stop_2471_, lean_object* v_b_2472_){
_start:
{
lean_object* v___y_2474_; uint8_t v___x_2478_; 
v___x_2478_ = lean_usize_dec_eq(v_i_2470_, v_stop_2471_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2479_; lean_object* v_name_2480_; uint8_t v___x_2481_; 
v___x_2479_ = lean_array_uget_borrowed(v_as_2469_, v_i_2470_);
v_name_2480_ = lean_ctor_get(v___x_2479_, 0);
lean_inc(v_name_2480_);
lean_inc_ref(v_a_2468_);
v___x_2481_ = l_Lean_isExtern(v_a_2468_, v_name_2480_);
if (v___x_2481_ == 0)
{
v___y_2474_ = v_b_2472_;
goto v___jp_2473_;
}
else
{
lean_object* v___x_2482_; 
lean_inc(v___x_2479_);
v___x_2482_ = lean_array_push(v_b_2472_, v___x_2479_);
v___y_2474_ = v___x_2482_;
goto v___jp_2473_;
}
}
else
{
lean_dec_ref(v_a_2468_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19___boxed(lean_object* v_a_2483_, lean_object* v_as_2484_, lean_object* v_i_2485_, lean_object* v_stop_2486_, lean_object* v_b_2487_){
_start:
{
size_t v_i_boxed_2488_; size_t v_stop_boxed_2489_; lean_object* v_res_2490_; 
v_i_boxed_2488_ = lean_unbox_usize(v_i_2485_);
lean_dec(v_i_2485_);
v_stop_boxed_2489_ = lean_unbox_usize(v_stop_2486_);
lean_dec(v_stop_2486_);
v_res_2490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_2483_, v_as_2484_, v_i_boxed_2488_, v_stop_boxed_2489_, v_b_2487_);
lean_dec_ref(v_as_2484_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(lean_object* v_as_2491_, size_t v_sz_2492_, size_t v_i_2493_, lean_object* v_b_2494_){
_start:
{
uint8_t v___x_2496_; 
v___x_2496_ = lean_usize_dec_lt(v_i_2493_, v_sz_2492_);
if (v___x_2496_ == 0)
{
lean_object* v___x_2497_; 
v___x_2497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2497_, 0, v_b_2494_);
return v___x_2497_;
}
else
{
uint8_t v___x_2498_; lean_object* v_a_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
lean_dec_ref(v_b_2494_);
v___x_2498_ = 0;
v_a_2499_ = lean_array_uget_borrowed(v_as_2491_, v_i_2493_);
lean_inc(v_a_2499_);
v___x_2500_ = l_Lean_Message_toString(v_a_2499_, v___x_2498_);
v___x_2501_ = l_IO_eprintln___at___00main_spec__6(v___x_2500_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v___x_2502_; size_t v___x_2503_; size_t v___x_2504_; 
lean_dec_ref(v___x_2501_);
v___x_2502_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_2503_ = ((size_t)1ULL);
v___x_2504_ = lean_usize_add(v_i_2493_, v___x_2503_);
v_i_2493_ = v___x_2504_;
v_b_2494_ = v___x_2502_;
goto _start;
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
v_a_2506_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2501_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2501_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27___boxed(lean_object* v_as_2514_, lean_object* v_sz_2515_, lean_object* v_i_2516_, lean_object* v_b_2517_, lean_object* v___y_2518_){
_start:
{
size_t v_sz_boxed_2519_; size_t v_i_boxed_2520_; lean_object* v_res_2521_; 
v_sz_boxed_2519_ = lean_unbox_usize(v_sz_2515_);
lean_dec(v_sz_2515_);
v_i_boxed_2520_ = lean_unbox_usize(v_i_2516_);
lean_dec(v_i_2516_);
v_res_2521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2514_, v_sz_boxed_2519_, v_i_boxed_2520_, v_b_2517_);
lean_dec_ref(v_as_2514_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(lean_object* v_as_2522_, size_t v_sz_2523_, size_t v_i_2524_, lean_object* v_b_2525_){
_start:
{
uint8_t v___x_2527_; 
v___x_2527_ = lean_usize_dec_lt(v_i_2524_, v_sz_2523_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2528_; 
v___x_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2528_, 0, v_b_2525_);
return v___x_2528_;
}
else
{
uint8_t v___x_2529_; lean_object* v_a_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
lean_dec_ref(v_b_2525_);
v___x_2529_ = 0;
v_a_2530_ = lean_array_uget_borrowed(v_as_2522_, v_i_2524_);
lean_inc(v_a_2530_);
v___x_2531_ = l_Lean_Message_toString(v_a_2530_, v___x_2529_);
v___x_2532_ = l_IO_eprintln___at___00main_spec__6(v___x_2531_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v___x_2533_; size_t v___x_2534_; size_t v___x_2535_; lean_object* v___x_2536_; 
lean_dec_ref(v___x_2532_);
v___x_2533_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_2534_ = ((size_t)1ULL);
v___x_2535_ = lean_usize_add(v_i_2524_, v___x_2534_);
v___x_2536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2522_, v_sz_2523_, v___x_2535_, v___x_2533_);
return v___x_2536_;
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
v_a_2537_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2532_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2532_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14___boxed(lean_object* v_as_2545_, lean_object* v_sz_2546_, lean_object* v_i_2547_, lean_object* v_b_2548_, lean_object* v___y_2549_){
_start:
{
size_t v_sz_boxed_2550_; size_t v_i_boxed_2551_; lean_object* v_res_2552_; 
v_sz_boxed_2550_ = lean_unbox_usize(v_sz_2546_);
lean_dec(v_sz_2546_);
v_i_boxed_2551_ = lean_unbox_usize(v_i_2547_);
lean_dec(v_i_2547_);
v_res_2552_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_as_2545_, v_sz_boxed_2550_, v_i_boxed_2551_, v_b_2548_);
lean_dec_ref(v_as_2545_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(lean_object* v_init_2553_, lean_object* v_n_2554_, lean_object* v_b_2555_){
_start:
{
if (lean_obj_tag(v_n_2554_) == 0)
{
lean_object* v_cs_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; size_t v_sz_2560_; size_t v___x_2561_; lean_object* v___x_2562_; 
v_cs_2557_ = lean_ctor_get(v_n_2554_, 0);
v___x_2558_ = lean_box(0);
v___x_2559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
lean_ctor_set(v___x_2559_, 1, v_b_2555_);
v_sz_2560_ = lean_array_size(v_cs_2557_);
v___x_2561_ = ((size_t)0ULL);
v___x_2562_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2553_, v_cs_2557_, v_sz_2560_, v___x_2561_, v___x_2559_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2577_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2565_ = v___x_2562_;
v_isShared_2566_ = v_isSharedCheck_2577_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2562_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2577_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v_fst_2567_; 
v_fst_2567_ = lean_ctor_get(v_a_2563_, 0);
if (lean_obj_tag(v_fst_2567_) == 0)
{
lean_object* v_snd_2568_; lean_object* v___x_2569_; lean_object* v___x_2571_; 
v_snd_2568_ = lean_ctor_get(v_a_2563_, 1);
lean_inc(v_snd_2568_);
lean_dec(v_a_2563_);
v___x_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2569_, 0, v_snd_2568_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 0, v___x_2569_);
v___x_2571_ = v___x_2565_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v___x_2569_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
else
{
lean_object* v_val_2573_; lean_object* v___x_2575_; 
lean_inc_ref(v_fst_2567_);
lean_dec(v_a_2563_);
v_val_2573_ = lean_ctor_get(v_fst_2567_, 0);
lean_inc(v_val_2573_);
lean_dec_ref(v_fst_2567_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 0, v_val_2573_);
v___x_2575_ = v___x_2565_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_val_2573_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
v_a_2578_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2562_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2562_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
else
{
lean_object* v_vs_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; size_t v_sz_2589_; size_t v___x_2590_; lean_object* v___x_2591_; 
v_vs_2586_ = lean_ctor_get(v_n_2554_, 0);
v___x_2587_ = lean_box(0);
v___x_2588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
lean_ctor_set(v___x_2588_, 1, v_b_2555_);
v_sz_2589_ = lean_array_size(v_vs_2586_);
v___x_2590_ = ((size_t)0ULL);
v___x_2591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_vs_2586_, v_sz_2589_, v___x_2590_, v___x_2588_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2606_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2594_ = v___x_2591_;
v_isShared_2595_ = v_isSharedCheck_2606_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2591_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2606_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v_fst_2596_; 
v_fst_2596_ = lean_ctor_get(v_a_2592_, 0);
if (lean_obj_tag(v_fst_2596_) == 0)
{
lean_object* v_snd_2597_; lean_object* v___x_2598_; lean_object* v___x_2600_; 
v_snd_2597_ = lean_ctor_get(v_a_2592_, 1);
lean_inc(v_snd_2597_);
lean_dec(v_a_2592_);
v___x_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2598_, 0, v_snd_2597_);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v___x_2598_);
v___x_2600_ = v___x_2594_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
else
{
lean_object* v_val_2602_; lean_object* v___x_2604_; 
lean_inc_ref(v_fst_2596_);
lean_dec(v_a_2592_);
v_val_2602_ = lean_ctor_get(v_fst_2596_, 0);
lean_inc(v_val_2602_);
lean_dec_ref(v_fst_2596_);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v_val_2602_);
v___x_2604_ = v___x_2594_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_val_2602_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
v_a_2607_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2591_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2591_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(lean_object* v_init_2615_, lean_object* v_as_2616_, size_t v_sz_2617_, size_t v_i_2618_, lean_object* v_b_2619_){
_start:
{
uint8_t v___x_2621_; 
v___x_2621_ = lean_usize_dec_lt(v_i_2618_, v_sz_2617_);
if (v___x_2621_ == 0)
{
lean_object* v___x_2622_; 
v___x_2622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2622_, 0, v_b_2619_);
return v___x_2622_;
}
else
{
lean_object* v_snd_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2657_; 
v_snd_2623_ = lean_ctor_get(v_b_2619_, 1);
v_isSharedCheck_2657_ = !lean_is_exclusive(v_b_2619_);
if (v_isSharedCheck_2657_ == 0)
{
lean_object* v_unused_2658_; 
v_unused_2658_ = lean_ctor_get(v_b_2619_, 0);
lean_dec(v_unused_2658_);
v___x_2625_ = v_b_2619_;
v_isShared_2626_ = v_isSharedCheck_2657_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_snd_2623_);
lean_dec(v_b_2619_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2657_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v_a_2627_; lean_object* v___x_2628_; 
v_a_2627_ = lean_array_uget_borrowed(v_as_2616_, v_i_2618_);
lean_inc(v_snd_2623_);
v___x_2628_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2615_, v_a_2627_, v_snd_2623_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2648_; 
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2631_ = v___x_2628_;
v_isShared_2632_ = v_isSharedCheck_2648_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2628_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2648_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
if (lean_obj_tag(v_a_2629_) == 0)
{
lean_object* v___x_2633_; lean_object* v___x_2635_; 
v___x_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2633_, 0, v_a_2629_);
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 0, v___x_2633_);
v___x_2635_ = v___x_2625_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v___x_2633_);
lean_ctor_set(v_reuseFailAlloc_2639_, 1, v_snd_2623_);
v___x_2635_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
lean_object* v___x_2637_; 
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 0, v___x_2635_);
v___x_2637_ = v___x_2631_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v___x_2635_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2641_; lean_object* v___x_2643_; 
lean_del_object(v___x_2631_);
lean_dec(v_snd_2623_);
v_a_2640_ = lean_ctor_get(v_a_2629_, 0);
lean_inc(v_a_2640_);
lean_dec_ref(v_a_2629_);
v___x_2641_ = lean_box(0);
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 1, v_a_2640_);
lean_ctor_set(v___x_2625_, 0, v___x_2641_);
v___x_2643_ = v___x_2625_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v___x_2641_);
lean_ctor_set(v_reuseFailAlloc_2647_, 1, v_a_2640_);
v___x_2643_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
size_t v___x_2644_; size_t v___x_2645_; 
v___x_2644_ = ((size_t)1ULL);
v___x_2645_ = lean_usize_add(v_i_2618_, v___x_2644_);
v_i_2618_ = v___x_2645_;
v_b_2619_ = v___x_2643_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
lean_del_object(v___x_2625_);
lean_dec(v_snd_2623_);
v_a_2649_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v___x_2628_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2628_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2649_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13___boxed(lean_object* v_init_2659_, lean_object* v_as_2660_, lean_object* v_sz_2661_, lean_object* v_i_2662_, lean_object* v_b_2663_, lean_object* v___y_2664_){
_start:
{
size_t v_sz_boxed_2665_; size_t v_i_boxed_2666_; lean_object* v_res_2667_; 
v_sz_boxed_2665_ = lean_unbox_usize(v_sz_2661_);
lean_dec(v_sz_2661_);
v_i_boxed_2666_ = lean_unbox_usize(v_i_2662_);
lean_dec(v_i_2662_);
v_res_2667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2659_, v_as_2660_, v_sz_boxed_2665_, v_i_boxed_2666_, v_b_2663_);
lean_dec_ref(v_as_2660_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10___boxed(lean_object* v_init_2668_, lean_object* v_n_2669_, lean_object* v_b_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2668_, v_n_2669_, v_b_2670_);
lean_dec_ref(v_n_2669_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(lean_object* v_as_2673_, size_t v_sz_2674_, size_t v_i_2675_, lean_object* v_b_2676_){
_start:
{
uint8_t v___x_2678_; 
v___x_2678_ = lean_usize_dec_lt(v_i_2675_, v_sz_2674_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2679_; 
v___x_2679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2679_, 0, v_b_2676_);
return v___x_2679_;
}
else
{
uint8_t v___x_2680_; lean_object* v_a_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
lean_dec_ref(v_b_2676_);
v___x_2680_ = 0;
v_a_2681_ = lean_array_uget_borrowed(v_as_2673_, v_i_2675_);
lean_inc(v_a_2681_);
v___x_2682_ = l_Lean_Message_toString(v_a_2681_, v___x_2680_);
v___x_2683_ = l_IO_eprintln___at___00main_spec__6(v___x_2682_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v___x_2684_; size_t v___x_2685_; size_t v___x_2686_; 
lean_dec_ref(v___x_2683_);
v___x_2684_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_2685_ = ((size_t)1ULL);
v___x_2686_ = lean_usize_add(v_i_2675_, v___x_2685_);
v_i_2675_ = v___x_2686_;
v_b_2676_ = v___x_2684_;
goto _start;
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
v_a_2688_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2683_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2683_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16___boxed(lean_object* v_as_2696_, lean_object* v_sz_2697_, lean_object* v_i_2698_, lean_object* v_b_2699_, lean_object* v___y_2700_){
_start:
{
size_t v_sz_boxed_2701_; size_t v_i_boxed_2702_; lean_object* v_res_2703_; 
v_sz_boxed_2701_ = lean_unbox_usize(v_sz_2697_);
lean_dec(v_sz_2697_);
v_i_boxed_2702_ = lean_unbox_usize(v_i_2698_);
lean_dec(v_i_2698_);
v_res_2703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2696_, v_sz_boxed_2701_, v_i_boxed_2702_, v_b_2699_);
lean_dec_ref(v_as_2696_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(lean_object* v_as_2704_, size_t v_sz_2705_, size_t v_i_2706_, lean_object* v_b_2707_){
_start:
{
uint8_t v___x_2709_; 
v___x_2709_ = lean_usize_dec_lt(v_i_2706_, v_sz_2705_);
if (v___x_2709_ == 0)
{
lean_object* v___x_2710_; 
v___x_2710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2710_, 0, v_b_2707_);
return v___x_2710_;
}
else
{
uint8_t v___x_2711_; lean_object* v_a_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
lean_dec_ref(v_b_2707_);
v___x_2711_ = 0;
v_a_2712_ = lean_array_uget_borrowed(v_as_2704_, v_i_2706_);
lean_inc(v_a_2712_);
v___x_2713_ = l_Lean_Message_toString(v_a_2712_, v___x_2711_);
v___x_2714_ = l_IO_eprintln___at___00main_spec__6(v___x_2713_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v___x_2715_; size_t v___x_2716_; size_t v___x_2717_; lean_object* v___x_2718_; 
lean_dec_ref(v___x_2714_);
v___x_2715_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_2716_ = ((size_t)1ULL);
v___x_2717_ = lean_usize_add(v_i_2706_, v___x_2716_);
v___x_2718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2704_, v_sz_2705_, v___x_2717_, v___x_2715_);
return v___x_2718_;
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
v_a_2719_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2714_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2714_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11___boxed(lean_object* v_as_2727_, lean_object* v_sz_2728_, lean_object* v_i_2729_, lean_object* v_b_2730_, lean_object* v___y_2731_){
_start:
{
size_t v_sz_boxed_2732_; size_t v_i_boxed_2733_; lean_object* v_res_2734_; 
v_sz_boxed_2732_ = lean_unbox_usize(v_sz_2728_);
lean_dec(v_sz_2728_);
v_i_boxed_2733_ = lean_unbox_usize(v_i_2729_);
lean_dec(v_i_2729_);
v_res_2734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_as_2727_, v_sz_boxed_2732_, v_i_boxed_2733_, v_b_2730_);
lean_dec_ref(v_as_2727_);
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7(lean_object* v_t_2735_, lean_object* v_init_2736_){
_start:
{
lean_object* v_root_2738_; lean_object* v_tail_2739_; lean_object* v___x_2740_; 
v_root_2738_ = lean_ctor_get(v_t_2735_, 0);
v_tail_2739_ = lean_ctor_get(v_t_2735_, 1);
v___x_2740_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2736_, v_root_2738_, v_init_2736_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2777_; 
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2743_ = v___x_2740_;
v_isShared_2744_ = v_isSharedCheck_2777_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2740_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2777_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
if (lean_obj_tag(v_a_2741_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2747_; 
v_a_2745_ = lean_ctor_get(v_a_2741_, 0);
lean_inc(v_a_2745_);
lean_dec_ref(v_a_2741_);
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 0, v_a_2745_);
v___x_2747_ = v___x_2743_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_a_2745_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
else
{
lean_object* v_a_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; size_t v_sz_2752_; size_t v___x_2753_; lean_object* v___x_2754_; 
lean_del_object(v___x_2743_);
v_a_2749_ = lean_ctor_get(v_a_2741_, 0);
lean_inc(v_a_2749_);
lean_dec_ref(v_a_2741_);
v___x_2750_ = lean_box(0);
v___x_2751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2750_);
lean_ctor_set(v___x_2751_, 1, v_a_2749_);
v_sz_2752_ = lean_array_size(v_tail_2739_);
v___x_2753_ = ((size_t)0ULL);
v___x_2754_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_tail_2739_, v_sz_2752_, v___x_2753_, v___x_2751_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2768_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2757_ = v___x_2754_;
v_isShared_2758_ = v_isSharedCheck_2768_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2754_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2768_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v_fst_2759_; 
v_fst_2759_ = lean_ctor_get(v_a_2755_, 0);
if (lean_obj_tag(v_fst_2759_) == 0)
{
lean_object* v_snd_2760_; lean_object* v___x_2762_; 
v_snd_2760_ = lean_ctor_get(v_a_2755_, 1);
lean_inc(v_snd_2760_);
lean_dec(v_a_2755_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 0, v_snd_2760_);
v___x_2762_ = v___x_2757_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_snd_2760_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
else
{
lean_object* v_val_2764_; lean_object* v___x_2766_; 
lean_inc_ref(v_fst_2759_);
lean_dec(v_a_2755_);
v_val_2764_ = lean_ctor_get(v_fst_2759_, 0);
lean_inc(v_val_2764_);
lean_dec_ref(v_fst_2759_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 0, v_val_2764_);
v___x_2766_ = v___x_2757_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_val_2764_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
else
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
v_a_2769_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2754_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2754_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2769_);
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
else
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2785_; 
v_a_2778_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2780_ = v___x_2740_;
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2740_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2781_ == 0)
{
v___x_2783_ = v___x_2780_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2778_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7___boxed(lean_object* v_t_2786_, lean_object* v_init_2787_, lean_object* v___y_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_t_2786_, v_init_2787_);
lean_dec_ref(v_t_2786_);
return v_res_2789_;
}
}
static lean_object* _init_l_main___closed__3(void){
_start:
{
lean_object* v___x_2793_; 
v___x_2793_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_box(0), lean_box(0), lean_box(0));
return v___x_2793_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2794_ = l_Lean_instInhabitedClassState_default;
v___x_2795_ = lean_box(0);
v___x_2796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2795_);
lean_ctor_set(v___x_2796_, 1, v___x_2794_);
return v___x_2796_;
}
}
static lean_object* _init_l_main___closed__5(void){
_start:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2797_ = l_Lean_Meta_Match_Extension_instInhabitedState;
v___x_2798_ = lean_box(0);
v___x_2799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2798_);
lean_ctor_set(v___x_2799_, 1, v___x_2797_);
return v___x_2799_;
}
}
static lean_object* _init_l_main___closed__6(void){
_start:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2800_ = ((lean_object*)(l_main___closed__2));
v___x_2801_ = ((lean_object*)(l_main___closed__1));
v___x_2802_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_2801_, v___x_2800_);
return v___x_2802_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2803_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2804_ = lean_box(0);
v___x_2805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
lean_ctor_set(v___x_2805_, 1, v___x_2803_);
return v___x_2805_;
}
}
static lean_object* _init_l_main___closed__8(void){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_2807_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2806_);
return v___x_2807_;
}
}
static lean_object* _init_l_main___closed__9(void){
_start:
{
lean_object* v___x_2808_; 
v___x_2808_ = l_Array_instInhabited(lean_box(0));
return v___x_2808_;
}
}
static lean_object* _init_l_main___closed__14(void){
_start:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2816_ = l_Lean_Options_empty;
v___x_2817_ = l_Lean_Core_getMaxHeartbeats(v___x_2816_);
return v___x_2817_;
}
}
static lean_object* _init_l_main___closed__19(void){
_start:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2822_ = ((lean_object*)(l_main___closed__18));
v___x_2823_ = lean_unsigned_to_nat(27u);
v___x_2824_ = lean_unsigned_to_nat(144u);
v___x_2825_ = ((lean_object*)(l_main___closed__17));
v___x_2826_ = ((lean_object*)(l_main___closed__16));
v___x_2827_ = l_mkPanicMessageWithDecl(v___x_2826_, v___x_2825_, v___x_2824_, v___x_2823_, v___x_2822_);
return v___x_2827_;
}
}
static lean_object* _init_l_main___closed__21(void){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2829_ = ((lean_object*)(l_main___closed__18));
v___x_2830_ = lean_unsigned_to_nat(51u);
v___x_2831_ = lean_unsigned_to_nat(117u);
v___x_2832_ = ((lean_object*)(l_main___closed__17));
v___x_2833_ = ((lean_object*)(l_main___closed__16));
v___x_2834_ = l_mkPanicMessageWithDecl(v___x_2833_, v___x_2832_, v___x_2831_, v___x_2830_, v___x_2829_);
return v___x_2834_;
}
}
static lean_object* _init_l_main___closed__22(void){
_start:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2835_ = lean_unsigned_to_nat(1u);
v___x_2836_ = l_Lean_firstFrontendMacroScope;
v___x_2837_ = lean_nat_add(v___x_2836_, v___x_2835_);
return v___x_2837_;
}
}
static lean_object* _init_l_main___closed__26(void){
_start:
{
lean_object* v___x_2844_; uint64_t v___x_2845_; lean_object* v___x_2846_; 
v___x_2844_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2845_ = 0ULL;
v___x_2846_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2846_, 0, v___x_2844_);
lean_ctor_set_uint64(v___x_2846_, sizeof(void*)*1, v___x_2845_);
return v___x_2846_;
}
}
static lean_object* _init_l_main___closed__27(void){
_start:
{
lean_object* v___x_2847_; 
v___x_2847_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2847_;
}
}
static lean_object* _init_l_main___closed__28(void){
_start:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2848_ = lean_obj_once(&l_main___closed__27, &l_main___closed__27_once, _init_l_main___closed__27);
v___x_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
return v___x_2849_;
}
}
static lean_object* _init_l_main___closed__29(void){
_start:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2850_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_2851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2850_);
lean_ctor_set(v___x_2851_, 1, v___x_2850_);
return v___x_2851_;
}
}
static lean_object* _init_l_main___closed__30(void){
_start:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2852_ = l_Lean_NameSet_empty;
v___x_2853_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2854_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2853_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
lean_ctor_set(v___x_2854_, 2, v___x_2852_);
return v___x_2854_;
}
}
static lean_object* _init_l_main___closed__31(void){
_start:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; uint8_t v___x_2857_; lean_object* v___x_2858_; 
v___x_2855_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2856_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_2857_ = 1;
v___x_2858_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2858_, 0, v___x_2856_);
lean_ctor_set(v___x_2858_, 1, v___x_2856_);
lean_ctor_set(v___x_2858_, 2, v___x_2855_);
lean_ctor_set_uint8(v___x_2858_, sizeof(void*)*3, v___x_2857_);
return v___x_2858_;
}
}
static uint8_t _init_l_main___closed__36(void){
_start:
{
uint8_t v___x_2865_; uint8_t v___x_2866_; 
v___x_2865_ = 2;
v___x_2866_ = l_Lean_instOrdOLeanLevel_ord(v___x_2865_, v___x_2865_);
return v___x_2866_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_2867_; lean_object* v___x_2868_; 
v___x_2867_ = 1;
v___x_2868_ = lean_box_uint32(v___x_2867_);
return v___x_2868_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_2869_; lean_object* v___x_2870_; 
v___x_2869_ = 0;
v___x_2870_ = lean_box_uint32(v___x_2869_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_2871_){
_start:
{
if (lean_obj_tag(v_args_2871_) == 1)
{
lean_object* v_tail_2896_; 
v_tail_2896_ = lean_ctor_get(v_args_2871_, 1);
lean_inc(v_tail_2896_);
if (lean_obj_tag(v_tail_2896_) == 1)
{
lean_object* v_tail_2897_; 
v_tail_2897_ = lean_ctor_get(v_tail_2896_, 1);
lean_inc(v_tail_2897_);
if (lean_obj_tag(v_tail_2897_) == 1)
{
lean_object* v_head_2898_; lean_object* v_head_2899_; lean_object* v_head_2900_; lean_object* v_tail_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_3524_; 
v_head_2898_ = lean_ctor_get(v_args_2871_, 0);
lean_inc(v_head_2898_);
lean_dec_ref(v_args_2871_);
v_head_2899_ = lean_ctor_get(v_tail_2896_, 0);
lean_inc(v_head_2899_);
lean_dec_ref(v_tail_2896_);
v_head_2900_ = lean_ctor_get(v_tail_2897_, 0);
v_tail_2901_ = lean_ctor_get(v_tail_2897_, 1);
v_isSharedCheck_3524_ = !lean_is_exclusive(v_tail_2897_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_2903_ = v_tail_2897_;
v_isShared_2904_ = v_isSharedCheck_3524_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_tail_2901_);
lean_inc(v_head_2900_);
lean_dec(v_tail_2897_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_3524_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2905_; 
v___x_2905_ = l_Lean_ModuleSetup_load(v_head_2898_);
lean_dec(v_head_2898_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v_name_2907_; lean_object* v_options_2908_; uint8_t v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2913_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_a_2906_);
lean_dec_ref(v___x_2905_);
v_name_2907_ = lean_ctor_get(v_a_2906_, 0);
lean_inc(v_name_2907_);
v_options_2908_ = lean_ctor_get(v_a_2906_, 6);
lean_inc(v_options_2908_);
lean_dec(v_a_2906_);
v___x_2909_ = 0;
v___x_2910_ = l_Lean_LeanOptions_toOptions(v_options_2908_);
v___x_2911_ = lean_box(v___x_2909_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set_tag(v___x_2903_, 0);
lean_ctor_set(v___x_2903_, 1, v___x_2910_);
lean_ctor_set(v___x_2903_, 0, v___x_2911_);
v___x_2913_ = v___x_2903_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v___x_2911_);
lean_ctor_set(v_reuseFailAlloc_3515_, 1, v___x_2910_);
v___x_2913_ = v_reuseFailAlloc_3515_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
lean_object* v___x_2914_; 
v___x_2914_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_tail_2901_, v___x_2913_);
lean_dec(v_tail_2901_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v___x_2916_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
lean_dec_ref(v___x_2914_);
v___x_2916_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_2916_) == 0)
{
lean_object* v_a_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v_a_2917_ = lean_ctor_get(v___x_2916_, 0);
lean_inc(v_a_2917_);
lean_dec_ref(v___x_2916_);
v___x_2918_ = lean_box(0);
v___x_2919_ = l_Lean_initSearchPath(v_a_2917_, v___x_2918_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_fst_2920_; lean_object* v_snd_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_3490_; 
lean_dec_ref(v___x_2919_);
v_fst_2920_ = lean_ctor_get(v_a_2915_, 0);
v_snd_2921_ = lean_ctor_get(v_a_2915_, 1);
v_isSharedCheck_3490_ = !lean_is_exclusive(v_a_2915_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_2923_ = v_a_2915_;
v_isShared_2924_ = v_isSharedCheck_3490_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_snd_2921_);
lean_inc(v_fst_2920_);
lean_dec(v_a_2915_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_3490_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; uint8_t v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; uint8_t v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; uint8_t v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v_nextMacroScope_3087_; lean_object* v_ngen_3088_; lean_object* v_auxDeclNGen_3089_; lean_object* v_traceState_3090_; lean_object* v_messages_3091_; lean_object* v_infoState_3092_; lean_object* v_snapshotTasks_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; uint8_t v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; uint8_t v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; uint8_t v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; uint8_t v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; uint8_t v___y_3208_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; uint8_t v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; uint8_t v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; uint8_t v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; uint8_t v___y_3380_; lean_object* v___y_3381_; lean_object* v___x_3391_; lean_object* v___x_3392_; uint8_t v___x_3393_; uint8_t v___y_3395_; uint8_t v___x_3489_; 
v___x_2925_ = lean_obj_once(&l_main___closed__3, &l_main___closed__3_once, _init_l_main___closed__3);
v___x_2926_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2927_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_2928_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2929_ = lean_obj_once(&l_main___closed__8, &l_main___closed__8_once, _init_l_main___closed__8);
v___x_2930_ = lean_obj_once(&l_main___closed__9, &l_main___closed__9_once, _init_l_main___closed__9);
v___x_2931_ = lean_box(1);
v___x_2932_ = ((lean_object*)(l_main___closed__10));
v___x_2933_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_2934_ = 1;
v___x_2935_ = l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(v_snd_2921_, v___x_2933_, v___x_2934_);
v___x_2936_ = l_Lean_maxHeartbeats;
v___x_2937_ = lean_unsigned_to_nat(0u);
v___x_2938_ = l_Lean_Option_set___at___00main_spec__3(v___x_2935_, v___x_2936_, v___x_2937_);
v___x_3228_ = ((lean_object*)(l_main___closed__20));
lean_inc(v_name_2907_);
v___x_3229_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3229_, 0, v_name_2907_);
lean_ctor_set_uint8(v___x_3229_, sizeof(void*)*1, v___x_2934_);
lean_ctor_set_uint8(v___x_3229_, sizeof(void*)*1 + 1, v___x_2934_);
lean_ctor_set_uint8(v___x_3229_, sizeof(void*)*1 + 2, v___x_2934_);
v___x_3230_ = lean_unsigned_to_nat(1u);
v___x_3391_ = lean_mk_empty_array_with_capacity(v___x_3230_);
v___x_3392_ = lean_array_push(v___x_3391_, v___x_3229_);
v___x_3393_ = 2;
v___x_3489_ = lean_uint8_once(&l_main___closed__36, &l_main___closed__36_once, _init_l_main___closed__36);
if (v___x_3489_ == 0)
{
v___y_3395_ = v___x_2934_;
goto v___jp_3394_;
}
else
{
v___y_3395_ = v___x_2909_;
goto v___jp_3394_;
}
v___jp_2939_:
{
lean_object* v___x_2959_; lean_object* v_messages_2960_; lean_object* v_env_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_3062_; 
v___x_2959_ = lean_st_ref_get(v___y_2955_);
lean_dec(v___y_2955_);
v_messages_2960_ = lean_ctor_get(v___x_2959_, 6);
v_env_2961_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_3062_ == 0)
{
lean_object* v_unused_3063_; lean_object* v_unused_3064_; lean_object* v_unused_3065_; lean_object* v_unused_3066_; lean_object* v_unused_3067_; lean_object* v_unused_3068_; lean_object* v_unused_3069_; 
v_unused_3063_ = lean_ctor_get(v___x_2959_, 8);
lean_dec(v_unused_3063_);
v_unused_3064_ = lean_ctor_get(v___x_2959_, 7);
lean_dec(v_unused_3064_);
v_unused_3065_ = lean_ctor_get(v___x_2959_, 5);
lean_dec(v_unused_3065_);
v_unused_3066_ = lean_ctor_get(v___x_2959_, 4);
lean_dec(v_unused_3066_);
v_unused_3067_ = lean_ctor_get(v___x_2959_, 3);
lean_dec(v_unused_3067_);
v_unused_3068_ = lean_ctor_get(v___x_2959_, 2);
lean_dec(v_unused_3068_);
v_unused_3069_ = lean_ctor_get(v___x_2959_, 1);
lean_dec(v_unused_3069_);
v___x_2963_ = v___x_2959_;
v_isShared_2964_ = v_isSharedCheck_3062_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_messages_2960_);
lean_inc(v_env_2961_);
lean_dec(v___x_2959_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_3062_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v_unreported_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v_unreported_2965_ = lean_ctor_get(v_messages_2960_, 1);
v___x_2966_ = lean_box(0);
v___x_2967_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_unreported_2965_, v___x_2966_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_3052_; 
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_3052_ == 0)
{
lean_object* v_unused_3053_; 
v_unused_3053_ = lean_ctor_get(v___x_2967_, 0);
lean_dec(v_unused_3053_);
v___x_2969_ = v___x_2967_;
v_isShared_2970_ = v_isSharedCheck_3052_;
goto v_resetjp_2968_;
}
else
{
lean_dec(v___x_2967_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_3052_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
uint8_t v___x_2971_; 
v___x_2971_ = l_Lean_MessageLog_hasErrors(v_messages_2960_);
lean_dec_ref(v_messages_2960_);
if (v___x_2971_ == 0)
{
lean_object* v___x_2972_; 
lean_del_object(v___x_2969_);
lean_inc_ref(v_env_2961_);
v___x_2972_ = l___private_LeanIR_0__mkIRData(v_env_2961_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v_a_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
lean_inc(v_a_2973_);
lean_dec_ref(v___x_2972_);
v___x_2974_ = l_Lean_Environment_mainModule(v_env_2961_);
v___x_2975_ = ((lean_object*)(l_main___closed__12));
v___x_2976_ = l_Lean_Name_append(v___x_2974_, v___x_2975_);
lean_inc(v_head_2899_);
v___x_2977_ = l_Lean_saveModuleData(v_head_2899_, v___x_2976_, v_a_2973_);
lean_dec(v___x_2976_);
if (lean_obj_tag(v___x_2977_) == 0)
{
uint8_t v___x_2978_; lean_object* v___x_2979_; 
lean_dec_ref(v___x_2977_);
v___x_2978_ = 1;
v___x_2979_ = lean_io_prim_handle_mk(v_head_2900_, v___x_2978_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2985_; 
lean_dec(v_head_2900_);
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_a_2980_);
lean_dec_ref(v___x_2979_);
v___x_2981_ = ((lean_object*)(l_main___closed__13));
v___x_2982_ = l_Lean_Options_empty;
v___x_2983_ = lean_obj_once(&l_main___closed__14, &l_main___closed__14_once, _init_l_main___closed__14);
lean_inc_ref(v___y_2954_);
lean_inc_ref(v___y_2958_);
lean_inc_ref(v___y_2950_);
lean_inc_ref(v___y_2951_);
lean_inc_ref(v___y_2952_);
lean_inc_ref(v___y_2957_);
lean_inc(v___y_2953_);
lean_inc_ref(v_env_2961_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 8, v___y_2954_);
lean_ctor_set(v___x_2963_, 7, v___y_2958_);
lean_ctor_set(v___x_2963_, 6, v___y_2950_);
lean_ctor_set(v___x_2963_, 5, v___y_2951_);
lean_ctor_set(v___x_2963_, 4, v___y_2952_);
lean_ctor_set(v___x_2963_, 3, v___y_2956_);
lean_ctor_set(v___x_2963_, 2, v___y_2957_);
lean_ctor_set(v___x_2963_, 1, v___y_2953_);
v___x_2985_ = v___x_2963_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_env_2961_);
lean_ctor_set(v_reuseFailAlloc_3009_, 1, v___y_2953_);
lean_ctor_set(v_reuseFailAlloc_3009_, 2, v___y_2957_);
lean_ctor_set(v_reuseFailAlloc_3009_, 3, v___y_2956_);
lean_ctor_set(v_reuseFailAlloc_3009_, 4, v___y_2952_);
lean_ctor_set(v_reuseFailAlloc_3009_, 5, v___y_2951_);
lean_ctor_set(v_reuseFailAlloc_3009_, 6, v___y_2950_);
lean_ctor_set(v_reuseFailAlloc_3009_, 7, v___y_2958_);
lean_ctor_set(v_reuseFailAlloc_3009_, 8, v___y_2954_);
v___x_2985_ = v_reuseFailAlloc_3009_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___f_2988_; lean_object* v___x_2989_; 
v___x_2986_ = lean_box(v___x_2909_);
v___x_2987_ = lean_box(v___y_2945_);
lean_inc(v___y_2940_);
lean_inc(v___y_2943_);
lean_inc(v___y_2948_);
lean_inc_ref(v___y_2946_);
lean_inc_ref(v___y_2942_);
lean_inc(v___y_2947_);
v___f_2988_ = lean_alloc_closure((void*)(l_main___lam__1___boxed), 18, 17);
lean_closure_set(v___f_2988_, 0, v___x_2985_);
lean_closure_set(v___f_2988_, 1, v___y_2947_);
lean_closure_set(v___f_2988_, 2, v___x_2982_);
lean_closure_set(v___f_2988_, 3, v_name_2907_);
lean_closure_set(v___f_2988_, 4, v_a_2980_);
lean_closure_set(v___f_2988_, 5, v___y_2942_);
lean_closure_set(v___f_2988_, 6, v_head_2899_);
lean_closure_set(v___f_2988_, 7, v___y_2946_);
lean_closure_set(v___f_2988_, 8, v___x_2937_);
lean_closure_set(v___f_2988_, 9, v___y_2948_);
lean_closure_set(v___f_2988_, 10, v___y_2941_);
lean_closure_set(v___f_2988_, 11, v___y_2944_);
lean_closure_set(v___f_2988_, 12, v___x_2983_);
lean_closure_set(v___f_2988_, 13, v___y_2943_);
lean_closure_set(v___f_2988_, 14, v___y_2940_);
lean_closure_set(v___f_2988_, 15, v___x_2986_);
lean_closure_set(v___f_2988_, 16, v___x_2987_);
v___x_2989_ = l_Lean_profileitIOUnsafe___redArg(v___x_2981_, v___x_2938_, v___f_2988_, v___y_2949_);
lean_dec_ref(v___x_2938_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v___x_2990_; uint8_t v___x_2991_; 
lean_dec_ref(v___x_2989_);
v___x_2990_ = lean_display_cumulative_profiling_times();
v___x_2991_ = lean_unbox(v_fst_2920_);
lean_dec(v_fst_2920_);
if (v___x_2991_ == 0)
{
lean_dec_ref(v_env_2961_);
goto v___jp_2893_;
}
else
{
lean_object* v___x_2992_; 
v___x_2992_ = l_Lean_Environment_displayStats(v_env_2961_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_dec_ref(v___x_2992_);
goto v___jp_2893_;
}
else
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v___x_2992_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2992_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2993_);
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
}
else
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3008_; 
lean_dec_ref(v_env_2961_);
lean_dec(v_fst_2920_);
v_a_3001_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_3003_ = v___x_2989_;
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___x_2989_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3006_; 
if (v_isShared_3004_ == 0)
{
v___x_3006_ = v___x_3003_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_a_3001_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
}
}
else
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
lean_dec_ref(v___x_2979_);
lean_del_object(v___x_2963_);
lean_dec_ref(v_env_2961_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2949_);
lean_dec(v___y_2944_);
lean_dec(v___y_2941_);
lean_dec_ref(v___x_2938_);
lean_dec(v_fst_2920_);
lean_dec(v_name_2907_);
lean_dec(v_head_2899_);
v___x_3010_ = ((lean_object*)(l_main___closed__15));
v___x_3011_ = lean_string_append(v___x_3010_, v_head_2900_);
lean_dec(v_head_2900_);
v___x_3012_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__5));
v___x_3013_ = lean_string_append(v___x_3011_, v___x_3012_);
v___x_3014_ = l_IO_eprintln___at___00main_spec__6(v___x_3013_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3022_; 
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3022_ == 0)
{
lean_object* v_unused_3023_; 
v_unused_3023_ = lean_ctor_get(v___x_3014_, 0);
lean_dec(v_unused_3023_);
v___x_3016_ = v___x_3014_;
v_isShared_3017_ = v_isSharedCheck_3022_;
goto v_resetjp_3015_;
}
else
{
lean_dec(v___x_3014_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3022_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3018_; lean_object* v___x_3020_; 
v___x_3018_ = l_main___boxed__const__1;
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 0, v___x_3018_);
v___x_3020_ = v___x_3016_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_3018_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
else
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3031_; 
v_a_3024_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3026_ = v___x_3014_;
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3014_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3029_; 
if (v_isShared_3027_ == 0)
{
v___x_3029_ = v___x_3026_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3024_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
}
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
lean_del_object(v___x_2963_);
lean_dec_ref(v_env_2961_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2949_);
lean_dec(v___y_2944_);
lean_dec(v___y_2941_);
lean_dec_ref(v___x_2938_);
lean_dec(v_fst_2920_);
lean_dec(v_name_2907_);
lean_dec(v_head_2900_);
lean_dec(v_head_2899_);
v_a_3032_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_2977_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_2977_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
else
{
lean_object* v_a_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3047_; 
lean_del_object(v___x_2963_);
lean_dec_ref(v_env_2961_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2949_);
lean_dec(v___y_2944_);
lean_dec(v___y_2941_);
lean_dec_ref(v___x_2938_);
lean_dec(v_fst_2920_);
lean_dec(v_name_2907_);
lean_dec(v_head_2900_);
lean_dec(v_head_2899_);
v_a_3040_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3042_ = v___x_2972_;
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_2972_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3045_; 
if (v_isShared_3043_ == 0)
{
v___x_3045_ = v___x_3042_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_a_3040_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
}
else
{
lean_object* v___x_3048_; lean_object* v___x_3050_; 
lean_del_object(v___x_2963_);
lean_dec_ref(v_env_2961_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2949_);
lean_dec(v___y_2944_);
lean_dec(v___y_2941_);
lean_dec_ref(v___x_2938_);
lean_dec(v_fst_2920_);
lean_dec(v_name_2907_);
lean_dec(v_head_2900_);
lean_dec(v_head_2899_);
v___x_3048_ = l_main___boxed__const__1;
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 0, v___x_3048_);
v___x_3050_ = v___x_2969_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3048_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
else
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
lean_del_object(v___x_2963_);
lean_dec_ref(v_env_2961_);
lean_dec_ref(v_messages_2960_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2949_);
lean_dec(v___y_2944_);
lean_dec(v___y_2941_);
lean_dec_ref(v___x_2938_);
lean_dec(v_fst_2920_);
lean_dec(v_name_2907_);
lean_dec(v_head_2900_);
lean_dec(v_head_2899_);
v_a_3054_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___x_2967_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_2967_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3054_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
}
v___jp_3070_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; size_t v_sz_3104_; size_t v___x_3105_; lean_object* v___x_3106_; 
lean_inc_ref(v___y_3094_);
v___x_3101_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3101_, 0, v___y_3100_);
lean_ctor_set(v___x_3101_, 1, v_nextMacroScope_3087_);
lean_ctor_set(v___x_3101_, 2, v_ngen_3088_);
lean_ctor_set(v___x_3101_, 3, v_auxDeclNGen_3089_);
lean_ctor_set(v___x_3101_, 4, v_traceState_3090_);
lean_ctor_set(v___x_3101_, 5, v___y_3094_);
lean_ctor_set(v___x_3101_, 6, v_messages_3091_);
lean_ctor_set(v___x_3101_, 7, v_infoState_3092_);
lean_ctor_set(v___x_3101_, 8, v_snapshotTasks_3093_);
v___x_3102_ = lean_st_ref_set(v___y_3083_, v___x_3101_);
v___x_3103_ = lean_box(0);
v_sz_3104_ = lean_array_size(v___y_3099_);
v___x_3105_ = ((size_t)0ULL);
v___x_3106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v___y_3099_, v_sz_3104_, v___x_3105_, v___x_3103_, v___y_3095_, v___y_3083_);
lean_dec_ref(v___y_3099_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_dec_ref(v___x_3106_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3083_);
v___y_2940_ = v___y_3071_;
v___y_2941_ = v___y_3073_;
v___y_2942_ = v___y_3072_;
v___y_2943_ = v___y_3074_;
v___y_2944_ = v___y_3075_;
v___y_2945_ = v___y_3076_;
v___y_2946_ = v___y_3077_;
v___y_2947_ = v___y_3078_;
v___y_2948_ = v___y_3079_;
v___y_2949_ = v___y_3096_;
v___y_2950_ = v___y_3080_;
v___y_2951_ = v___y_3094_;
v___y_2952_ = v___y_3097_;
v___y_2953_ = v___y_3081_;
v___y_2954_ = v___y_3098_;
v___y_2955_ = v___y_3082_;
v___y_2956_ = v___y_3084_;
v___y_2957_ = v___y_3085_;
v___y_2958_ = v___y_3086_;
goto v___jp_2939_;
}
else
{
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_dec_ref(v___x_3106_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3083_);
v___y_2940_ = v___y_3071_;
v___y_2941_ = v___y_3073_;
v___y_2942_ = v___y_3072_;
v___y_2943_ = v___y_3074_;
v___y_2944_ = v___y_3075_;
v___y_2945_ = v___y_3076_;
v___y_2946_ = v___y_3077_;
v___y_2947_ = v___y_3078_;
v___y_2948_ = v___y_3079_;
v___y_2949_ = v___y_3096_;
v___y_2950_ = v___y_3080_;
v___y_2951_ = v___y_3094_;
v___y_2952_ = v___y_3097_;
v___y_2953_ = v___y_3081_;
v___y_2954_ = v___y_3098_;
v___y_2955_ = v___y_3082_;
v___y_2956_ = v___y_3084_;
v___y_2957_ = v___y_3085_;
v___y_2958_ = v___y_3086_;
goto v___jp_2939_;
}
else
{
lean_object* v_a_3107_; uint8_t v___x_3108_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_a_3107_);
lean_dec_ref(v___x_3106_);
v___x_3108_ = l_Lean_Exception_isInterrupt(v_a_3107_);
if (v___x_3108_ == 0)
{
lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3109_ = l_Lean_Exception_toMessageData(v_a_3107_);
v___x_3110_ = l_Lean_logError___at___00main_spec__14(v___x_3109_, v___y_3095_, v___y_3083_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3095_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_dec_ref(v___x_3110_);
v___y_2940_ = v___y_3071_;
v___y_2941_ = v___y_3073_;
v___y_2942_ = v___y_3072_;
v___y_2943_ = v___y_3074_;
v___y_2944_ = v___y_3075_;
v___y_2945_ = v___y_3076_;
v___y_2946_ = v___y_3077_;
v___y_2947_ = v___y_3078_;
v___y_2948_ = v___y_3079_;
v___y_2949_ = v___y_3096_;
v___y_2950_ = v___y_3080_;
v___y_2951_ = v___y_3094_;
v___y_2952_ = v___y_3097_;
v___y_2953_ = v___y_3081_;
v___y_2954_ = v___y_3098_;
v___y_2955_ = v___y_3082_;
v___y_2956_ = v___y_3084_;
v___y_2957_ = v___y_3085_;
v___y_2958_ = v___y_3086_;
goto v___jp_2939_;
}
else
{
lean_object* v___x_3111_; lean_object* v___x_3112_; 
lean_dec_ref(v___x_3110_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3082_);
lean_dec(v___y_3075_);
lean_dec(v___y_3073_);
lean_dec_ref(v___x_2938_);
lean_dec(v_fst_2920_);
lean_dec(v_name_2907_);
lean_dec(v_head_2900_);
lean_dec(v_head_2899_);
v___x_3111_ = lean_obj_once(&l_main___closed__19, &l_main___closed__19_once, _init_l_main___closed__19);
v___x_3112_ = l_panic___at___00main_spec__5(v___x_3111_);
return v___x_3112_;
}
}
else
{
lean_dec(v_a_3107_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3083_);
v___y_2940_ = v___y_3071_;
v___y_2941_ = v___y_3073_;
v___y_2942_ = v___y_3072_;
v___y_2943_ = v___y_3074_;
v___y_2944_ = v___y_3075_;
v___y_2945_ = v___y_3076_;
v___y_2946_ = v___y_3077_;
v___y_2947_ = v___y_3078_;
v___y_2948_ = v___y_3079_;
v___y_2949_ = v___y_3096_;
v___y_2950_ = v___y_3080_;
v___y_2951_ = v___y_3094_;
v___y_2952_ = v___y_3097_;
v___y_2953_ = v___y_3081_;
v___y_2954_ = v___y_3098_;
v___y_2955_ = v___y_3082_;
v___y_2956_ = v___y_3084_;
v___y_2957_ = v___y_3085_;
v___y_2958_ = v___y_3086_;
goto v___jp_2939_;
}
}
}
}
v___jp_3113_:
{
lean_object* v___x_3138_; lean_object* v_fileName_3139_; lean_object* v_fileMap_3140_; lean_object* v_currRecDepth_3141_; lean_object* v_ref_3142_; lean_object* v_currNamespace_3143_; lean_object* v_openDecls_3144_; lean_object* v_initHeartbeats_3145_; lean_object* v_maxHeartbeats_3146_; lean_object* v_quotContext_3147_; lean_object* v_currMacroScope_3148_; lean_object* v_cancelTk_x3f_3149_; uint8_t v_suppressElabErrors_3150_; lean_object* v_inheritedTraceOptions_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3181_; 
v___x_3138_ = lean_st_ref_take(v___y_3137_);
v_fileName_3139_ = lean_ctor_get(v___y_3136_, 0);
v_fileMap_3140_ = lean_ctor_get(v___y_3136_, 1);
v_currRecDepth_3141_ = lean_ctor_get(v___y_3136_, 3);
v_ref_3142_ = lean_ctor_get(v___y_3136_, 5);
v_currNamespace_3143_ = lean_ctor_get(v___y_3136_, 6);
v_openDecls_3144_ = lean_ctor_get(v___y_3136_, 7);
v_initHeartbeats_3145_ = lean_ctor_get(v___y_3136_, 8);
v_maxHeartbeats_3146_ = lean_ctor_get(v___y_3136_, 9);
v_quotContext_3147_ = lean_ctor_get(v___y_3136_, 10);
v_currMacroScope_3148_ = lean_ctor_get(v___y_3136_, 11);
v_cancelTk_x3f_3149_ = lean_ctor_get(v___y_3136_, 12);
v_suppressElabErrors_3150_ = lean_ctor_get_uint8(v___y_3136_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3151_ = lean_ctor_get(v___y_3136_, 13);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___y_3136_);
if (v_isSharedCheck_3181_ == 0)
{
lean_object* v_unused_3182_; lean_object* v_unused_3183_; 
v_unused_3182_ = lean_ctor_get(v___y_3136_, 4);
lean_dec(v_unused_3182_);
v_unused_3183_ = lean_ctor_get(v___y_3136_, 2);
lean_dec(v_unused_3183_);
v___x_3153_ = v___y_3136_;
v_isShared_3154_ = v_isSharedCheck_3181_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_inheritedTraceOptions_3151_);
lean_inc(v_cancelTk_x3f_3149_);
lean_inc(v_currMacroScope_3148_);
lean_inc(v_quotContext_3147_);
lean_inc(v_maxHeartbeats_3146_);
lean_inc(v_initHeartbeats_3145_);
lean_inc(v_openDecls_3144_);
lean_inc(v_currNamespace_3143_);
lean_inc(v_ref_3142_);
lean_inc(v_currRecDepth_3141_);
lean_inc(v_fileMap_3140_);
lean_inc(v_fileName_3139_);
lean_dec(v___y_3136_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3181_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v_env_3155_; lean_object* v_nextMacroScope_3156_; lean_object* v_ngen_3157_; lean_object* v_auxDeclNGen_3158_; lean_object* v_traceState_3159_; lean_object* v_messages_3160_; lean_object* v_infoState_3161_; lean_object* v_snapshotTasks_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3166_; 
v_env_3155_ = lean_ctor_get(v___x_3138_, 0);
lean_inc_ref(v_env_3155_);
v_nextMacroScope_3156_ = lean_ctor_get(v___x_3138_, 1);
lean_inc(v_nextMacroScope_3156_);
v_ngen_3157_ = lean_ctor_get(v___x_3138_, 2);
lean_inc_ref(v_ngen_3157_);
v_auxDeclNGen_3158_ = lean_ctor_get(v___x_3138_, 3);
lean_inc_ref(v_auxDeclNGen_3158_);
v_traceState_3159_ = lean_ctor_get(v___x_3138_, 4);
lean_inc_ref(v_traceState_3159_);
v_messages_3160_ = lean_ctor_get(v___x_3138_, 6);
lean_inc_ref(v_messages_3160_);
v_infoState_3161_ = lean_ctor_get(v___x_3138_, 7);
lean_inc_ref(v_infoState_3161_);
v_snapshotTasks_3162_ = lean_ctor_get(v___x_3138_, 8);
lean_inc_ref(v_snapshotTasks_3162_);
lean_dec(v___x_3138_);
v___x_3163_ = l_Lean_maxRecDepth;
v___x_3164_ = l_Lean_Option_get___at___00main_spec__9(v___x_2938_, v___x_3163_);
lean_inc_ref(v___x_2938_);
if (v_isShared_3154_ == 0)
{
lean_ctor_set(v___x_3153_, 4, v___x_3164_);
lean_ctor_set(v___x_3153_, 2, v___x_2938_);
v___x_3166_ = v___x_3153_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_fileName_3139_);
lean_ctor_set(v_reuseFailAlloc_3180_, 1, v_fileMap_3140_);
lean_ctor_set(v_reuseFailAlloc_3180_, 2, v___x_2938_);
lean_ctor_set(v_reuseFailAlloc_3180_, 3, v_currRecDepth_3141_);
lean_ctor_set(v_reuseFailAlloc_3180_, 4, v___x_3164_);
lean_ctor_set(v_reuseFailAlloc_3180_, 5, v_ref_3142_);
lean_ctor_set(v_reuseFailAlloc_3180_, 6, v_currNamespace_3143_);
lean_ctor_set(v_reuseFailAlloc_3180_, 7, v_openDecls_3144_);
lean_ctor_set(v_reuseFailAlloc_3180_, 8, v_initHeartbeats_3145_);
lean_ctor_set(v_reuseFailAlloc_3180_, 9, v_maxHeartbeats_3146_);
lean_ctor_set(v_reuseFailAlloc_3180_, 10, v_quotContext_3147_);
lean_ctor_set(v_reuseFailAlloc_3180_, 11, v_currMacroScope_3148_);
lean_ctor_set(v_reuseFailAlloc_3180_, 12, v_cancelTk_x3f_3149_);
lean_ctor_set(v_reuseFailAlloc_3180_, 13, v_inheritedTraceOptions_3151_);
lean_ctor_set_uint8(v_reuseFailAlloc_3180_, sizeof(void*)*14 + 1, v_suppressElabErrors_3150_);
v___x_3166_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
lean_object* v___x_3167_; uint8_t v___x_3168_; 
lean_ctor_set_uint8(v___x_3166_, sizeof(void*)*14, v___y_3123_);
v___x_3167_ = lean_array_get_size(v___y_3134_);
v___x_3168_ = lean_nat_dec_lt(v___x_2937_, v___x_3167_);
if (v___x_3168_ == 0)
{
lean_object* v___x_3169_; 
lean_inc_ref(v___y_3135_);
v___x_3169_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3135_, v_env_3155_, v___x_2931_);
v___y_3071_ = v___y_3114_;
v___y_3072_ = v___y_3116_;
v___y_3073_ = v___y_3115_;
v___y_3074_ = v___y_3117_;
v___y_3075_ = v___y_3118_;
v___y_3076_ = v___y_3119_;
v___y_3077_ = v___y_3120_;
v___y_3078_ = v___y_3121_;
v___y_3079_ = v___y_3122_;
v___y_3080_ = v___y_3124_;
v___y_3081_ = v___y_3125_;
v___y_3082_ = v___y_3126_;
v___y_3083_ = v___y_3137_;
v___y_3084_ = v___y_3127_;
v___y_3085_ = v___y_3128_;
v___y_3086_ = v___y_3129_;
v_nextMacroScope_3087_ = v_nextMacroScope_3156_;
v_ngen_3088_ = v_ngen_3157_;
v_auxDeclNGen_3089_ = v_auxDeclNGen_3158_;
v_traceState_3090_ = v_traceState_3159_;
v_messages_3091_ = v_messages_3160_;
v_infoState_3092_ = v_infoState_3161_;
v_snapshotTasks_3093_ = v_snapshotTasks_3162_;
v___y_3094_ = v___y_3130_;
v___y_3095_ = v___x_3166_;
v___y_3096_ = v___y_3131_;
v___y_3097_ = v___y_3132_;
v___y_3098_ = v___y_3133_;
v___y_3099_ = v___y_3134_;
v___y_3100_ = v___x_3169_;
goto v___jp_3070_;
}
else
{
uint8_t v___x_3170_; 
v___x_3170_ = lean_nat_dec_le(v___x_3167_, v___x_3167_);
if (v___x_3170_ == 0)
{
if (v___x_3168_ == 0)
{
lean_object* v___x_3171_; 
lean_inc_ref(v___y_3135_);
v___x_3171_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3135_, v_env_3155_, v___x_2931_);
v___y_3071_ = v___y_3114_;
v___y_3072_ = v___y_3116_;
v___y_3073_ = v___y_3115_;
v___y_3074_ = v___y_3117_;
v___y_3075_ = v___y_3118_;
v___y_3076_ = v___y_3119_;
v___y_3077_ = v___y_3120_;
v___y_3078_ = v___y_3121_;
v___y_3079_ = v___y_3122_;
v___y_3080_ = v___y_3124_;
v___y_3081_ = v___y_3125_;
v___y_3082_ = v___y_3126_;
v___y_3083_ = v___y_3137_;
v___y_3084_ = v___y_3127_;
v___y_3085_ = v___y_3128_;
v___y_3086_ = v___y_3129_;
v_nextMacroScope_3087_ = v_nextMacroScope_3156_;
v_ngen_3088_ = v_ngen_3157_;
v_auxDeclNGen_3089_ = v_auxDeclNGen_3158_;
v_traceState_3090_ = v_traceState_3159_;
v_messages_3091_ = v_messages_3160_;
v_infoState_3092_ = v_infoState_3161_;
v_snapshotTasks_3093_ = v_snapshotTasks_3162_;
v___y_3094_ = v___y_3130_;
v___y_3095_ = v___x_3166_;
v___y_3096_ = v___y_3131_;
v___y_3097_ = v___y_3132_;
v___y_3098_ = v___y_3133_;
v___y_3099_ = v___y_3134_;
v___y_3100_ = v___x_3171_;
goto v___jp_3070_;
}
else
{
size_t v___x_3172_; size_t v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3172_ = ((size_t)0ULL);
v___x_3173_ = lean_usize_of_nat(v___x_3167_);
v___x_3174_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3134_, v___x_3172_, v___x_3173_, v___x_2931_);
lean_inc_ref(v___y_3135_);
v___x_3175_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3135_, v_env_3155_, v___x_3174_);
v___y_3071_ = v___y_3114_;
v___y_3072_ = v___y_3116_;
v___y_3073_ = v___y_3115_;
v___y_3074_ = v___y_3117_;
v___y_3075_ = v___y_3118_;
v___y_3076_ = v___y_3119_;
v___y_3077_ = v___y_3120_;
v___y_3078_ = v___y_3121_;
v___y_3079_ = v___y_3122_;
v___y_3080_ = v___y_3124_;
v___y_3081_ = v___y_3125_;
v___y_3082_ = v___y_3126_;
v___y_3083_ = v___y_3137_;
v___y_3084_ = v___y_3127_;
v___y_3085_ = v___y_3128_;
v___y_3086_ = v___y_3129_;
v_nextMacroScope_3087_ = v_nextMacroScope_3156_;
v_ngen_3088_ = v_ngen_3157_;
v_auxDeclNGen_3089_ = v_auxDeclNGen_3158_;
v_traceState_3090_ = v_traceState_3159_;
v_messages_3091_ = v_messages_3160_;
v_infoState_3092_ = v_infoState_3161_;
v_snapshotTasks_3093_ = v_snapshotTasks_3162_;
v___y_3094_ = v___y_3130_;
v___y_3095_ = v___x_3166_;
v___y_3096_ = v___y_3131_;
v___y_3097_ = v___y_3132_;
v___y_3098_ = v___y_3133_;
v___y_3099_ = v___y_3134_;
v___y_3100_ = v___x_3175_;
goto v___jp_3070_;
}
}
else
{
size_t v___x_3176_; size_t v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3176_ = ((size_t)0ULL);
v___x_3177_ = lean_usize_of_nat(v___x_3167_);
v___x_3178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3134_, v___x_3176_, v___x_3177_, v___x_2931_);
lean_inc_ref(v___y_3135_);
v___x_3179_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3135_, v_env_3155_, v___x_3178_);
v___y_3071_ = v___y_3114_;
v___y_3072_ = v___y_3116_;
v___y_3073_ = v___y_3115_;
v___y_3074_ = v___y_3117_;
v___y_3075_ = v___y_3118_;
v___y_3076_ = v___y_3119_;
v___y_3077_ = v___y_3120_;
v___y_3078_ = v___y_3121_;
v___y_3079_ = v___y_3122_;
v___y_3080_ = v___y_3124_;
v___y_3081_ = v___y_3125_;
v___y_3082_ = v___y_3126_;
v___y_3083_ = v___y_3137_;
v___y_3084_ = v___y_3127_;
v___y_3085_ = v___y_3128_;
v___y_3086_ = v___y_3129_;
v_nextMacroScope_3087_ = v_nextMacroScope_3156_;
v_ngen_3088_ = v_ngen_3157_;
v_auxDeclNGen_3089_ = v_auxDeclNGen_3158_;
v_traceState_3090_ = v_traceState_3159_;
v_messages_3091_ = v_messages_3160_;
v_infoState_3092_ = v_infoState_3161_;
v_snapshotTasks_3093_ = v_snapshotTasks_3162_;
v___y_3094_ = v___y_3130_;
v___y_3095_ = v___x_3166_;
v___y_3096_ = v___y_3131_;
v___y_3097_ = v___y_3132_;
v___y_3098_ = v___y_3133_;
v___y_3099_ = v___y_3134_;
v___y_3100_ = v___x_3179_;
goto v___jp_3070_;
}
}
}
}
}
v___jp_3184_:
{
if (v___y_3208_ == 0)
{
lean_object* v___x_3209_; lean_object* v_env_3210_; lean_object* v_nextMacroScope_3211_; lean_object* v_ngen_3212_; lean_object* v_auxDeclNGen_3213_; lean_object* v_traceState_3214_; lean_object* v_messages_3215_; lean_object* v_infoState_3216_; lean_object* v_snapshotTasks_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3226_; 
v___x_3209_ = lean_st_ref_take(v___y_3197_);
v_env_3210_ = lean_ctor_get(v___x_3209_, 0);
v_nextMacroScope_3211_ = lean_ctor_get(v___x_3209_, 1);
v_ngen_3212_ = lean_ctor_get(v___x_3209_, 2);
v_auxDeclNGen_3213_ = lean_ctor_get(v___x_3209_, 3);
v_traceState_3214_ = lean_ctor_get(v___x_3209_, 4);
v_messages_3215_ = lean_ctor_get(v___x_3209_, 6);
v_infoState_3216_ = lean_ctor_get(v___x_3209_, 7);
v_snapshotTasks_3217_ = lean_ctor_get(v___x_3209_, 8);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3226_ == 0)
{
lean_object* v_unused_3227_; 
v_unused_3227_ = lean_ctor_get(v___x_3209_, 5);
lean_dec(v_unused_3227_);
v___x_3219_ = v___x_3209_;
v_isShared_3220_ = v_isSharedCheck_3226_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_snapshotTasks_3217_);
lean_inc(v_infoState_3216_);
lean_inc(v_messages_3215_);
lean_inc(v_traceState_3214_);
lean_inc(v_auxDeclNGen_3213_);
lean_inc(v_ngen_3212_);
lean_inc(v_nextMacroScope_3211_);
lean_inc(v_env_3210_);
lean_dec(v___x_3209_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3226_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3221_; lean_object* v___x_3223_; 
v___x_3221_ = l_Lean_Kernel_enableDiag(v_env_3210_, v___y_3194_);
lean_inc_ref(v___y_3202_);
if (v_isShared_3220_ == 0)
{
lean_ctor_set(v___x_3219_, 5, v___y_3202_);
lean_ctor_set(v___x_3219_, 0, v___x_3221_);
v___x_3223_ = v___x_3219_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3221_);
lean_ctor_set(v_reuseFailAlloc_3225_, 1, v_nextMacroScope_3211_);
lean_ctor_set(v_reuseFailAlloc_3225_, 2, v_ngen_3212_);
lean_ctor_set(v_reuseFailAlloc_3225_, 3, v_auxDeclNGen_3213_);
lean_ctor_set(v_reuseFailAlloc_3225_, 4, v_traceState_3214_);
lean_ctor_set(v_reuseFailAlloc_3225_, 5, v___y_3202_);
lean_ctor_set(v_reuseFailAlloc_3225_, 6, v_messages_3215_);
lean_ctor_set(v_reuseFailAlloc_3225_, 7, v_infoState_3216_);
lean_ctor_set(v_reuseFailAlloc_3225_, 8, v_snapshotTasks_3217_);
v___x_3223_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
lean_object* v___x_3224_; 
v___x_3224_ = lean_st_ref_set(v___y_3197_, v___x_3223_);
lean_inc(v___y_3197_);
v___y_3114_ = v___y_3185_;
v___y_3115_ = v___y_3187_;
v___y_3116_ = v___y_3186_;
v___y_3117_ = v___y_3188_;
v___y_3118_ = v___y_3189_;
v___y_3119_ = v___y_3190_;
v___y_3120_ = v___y_3191_;
v___y_3121_ = v___y_3192_;
v___y_3122_ = v___y_3193_;
v___y_3123_ = v___y_3194_;
v___y_3124_ = v___y_3195_;
v___y_3125_ = v___y_3196_;
v___y_3126_ = v___y_3197_;
v___y_3127_ = v___y_3198_;
v___y_3128_ = v___y_3200_;
v___y_3129_ = v___y_3201_;
v___y_3130_ = v___y_3202_;
v___y_3131_ = v___y_3203_;
v___y_3132_ = v___y_3204_;
v___y_3133_ = v___y_3205_;
v___y_3134_ = v___y_3207_;
v___y_3135_ = v___y_3206_;
v___y_3136_ = v___y_3199_;
v___y_3137_ = v___y_3197_;
goto v___jp_3113_;
}
}
}
else
{
lean_inc(v___y_3197_);
v___y_3114_ = v___y_3185_;
v___y_3115_ = v___y_3187_;
v___y_3116_ = v___y_3186_;
v___y_3117_ = v___y_3188_;
v___y_3118_ = v___y_3189_;
v___y_3119_ = v___y_3190_;
v___y_3120_ = v___y_3191_;
v___y_3121_ = v___y_3192_;
v___y_3122_ = v___y_3193_;
v___y_3123_ = v___y_3194_;
v___y_3124_ = v___y_3195_;
v___y_3125_ = v___y_3196_;
v___y_3126_ = v___y_3197_;
v___y_3127_ = v___y_3198_;
v___y_3128_ = v___y_3200_;
v___y_3129_ = v___y_3201_;
v___y_3130_ = v___y_3202_;
v___y_3131_ = v___y_3203_;
v___y_3132_ = v___y_3204_;
v___y_3133_ = v___y_3205_;
v___y_3134_ = v___y_3207_;
v___y_3135_ = v___y_3206_;
v___y_3136_ = v___y_3199_;
v___y_3137_ = v___y_3197_;
goto v___jp_3113_;
}
}
v___jp_3231_:
{
lean_object* v___x_3241_; 
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 1, v___y_3239_);
lean_ctor_set(v___x_2923_, 0, v___y_3235_);
v___x_3241_ = v___x_2923_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___y_3235_);
lean_ctor_set(v_reuseFailAlloc_3336_, 1, v___y_3239_);
v___x_3241_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v_moduleData_3245_; lean_object* v___x_3246_; uint8_t v___x_3247_; 
v___x_3242_ = lean_box(0);
lean_inc_ref(v___y_3236_);
v___x_3243_ = l_Lean_EnvExtension_setState___redArg(v___y_3236_, v___y_3234_, v___x_3241_, v___x_3242_);
v___x_3244_ = l_Lean_Environment_header(v___x_3243_);
v_moduleData_3245_ = lean_ctor_get(v___x_3244_, 6);
lean_inc_ref(v_moduleData_3245_);
lean_dec_ref(v___x_3244_);
v___x_3246_ = lean_array_get_size(v_moduleData_3245_);
v___x_3247_ = lean_nat_dec_lt(v___y_3237_, v___x_3246_);
if (v___x_3247_ == 0)
{
lean_object* v___x_3248_; lean_object* v___x_3249_; 
lean_dec_ref(v_moduleData_3245_);
lean_dec_ref(v___x_3243_);
lean_dec(v___y_3237_);
lean_dec(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___x_2938_);
lean_dec(v_fst_2920_);
lean_dec(v_name_2907_);
lean_dec(v_head_2900_);
lean_dec(v_head_2899_);
v___x_3248_ = lean_obj_once(&l_main___closed__21, &l_main___closed__21_once, _init_l_main___closed__21);
v___x_3249_ = l_panic___at___00main_spec__5(v___x_3248_);
return v___x_3249_;
}
else
{
lean_object* v_base_3250_; lean_object* v_private_3251_; lean_object* v_header_3252_; lean_object* v_serverBaseExts_3253_; lean_object* v_checked_3254_; lean_object* v_asyncConstsMap_3255_; lean_object* v_asyncCtx_x3f_3256_; lean_object* v_importRealizationCtx_x3f_3257_; lean_object* v_localRealizationCtxMap_3258_; lean_object* v_allRealizations_3259_; uint8_t v_isExporting_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3334_; 
v_base_3250_ = lean_ctor_get(v___x_3243_, 0);
lean_inc_ref(v_base_3250_);
v_private_3251_ = lean_ctor_get(v_base_3250_, 0);
lean_inc(v_private_3251_);
v_header_3252_ = lean_ctor_get(v_private_3251_, 5);
lean_inc_ref(v_header_3252_);
v_serverBaseExts_3253_ = lean_ctor_get(v___x_3243_, 1);
v_checked_3254_ = lean_ctor_get(v___x_3243_, 2);
v_asyncConstsMap_3255_ = lean_ctor_get(v___x_3243_, 3);
v_asyncCtx_x3f_3256_ = lean_ctor_get(v___x_3243_, 4);
v_importRealizationCtx_x3f_3257_ = lean_ctor_get(v___x_3243_, 5);
v_localRealizationCtxMap_3258_ = lean_ctor_get(v___x_3243_, 6);
v_allRealizations_3259_ = lean_ctor_get(v___x_3243_, 7);
v_isExporting_3260_ = lean_ctor_get_uint8(v___x_3243_, sizeof(void*)*8);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3334_ == 0)
{
lean_object* v_unused_3335_; 
v_unused_3335_ = lean_ctor_get(v___x_3243_, 0);
lean_dec(v_unused_3335_);
v___x_3262_ = v___x_3243_;
v_isShared_3263_ = v_isSharedCheck_3334_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_allRealizations_3259_);
lean_inc(v_localRealizationCtxMap_3258_);
lean_inc(v_importRealizationCtx_x3f_3257_);
lean_inc(v_asyncCtx_x3f_3256_);
lean_inc(v_asyncConstsMap_3255_);
lean_inc(v_checked_3254_);
lean_inc(v_serverBaseExts_3253_);
lean_dec(v___x_3243_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3334_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v_public_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3332_; 
v_public_3264_ = lean_ctor_get(v_base_3250_, 1);
v_isSharedCheck_3332_ = !lean_is_exclusive(v_base_3250_);
if (v_isSharedCheck_3332_ == 0)
{
lean_object* v_unused_3333_; 
v_unused_3333_ = lean_ctor_get(v_base_3250_, 0);
lean_dec(v_unused_3333_);
v___x_3266_ = v_base_3250_;
v_isShared_3267_ = v_isSharedCheck_3332_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_public_3264_);
lean_dec(v_base_3250_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3332_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v_constants_3268_; uint8_t v_quotInit_3269_; lean_object* v_diagnostics_3270_; lean_object* v_const2ModIdx_3271_; lean_object* v_extensions_3272_; lean_object* v_irBaseExts_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3330_; 
v_constants_3268_ = lean_ctor_get(v_private_3251_, 0);
v_quotInit_3269_ = lean_ctor_get_uint8(v_private_3251_, sizeof(void*)*6);
v_diagnostics_3270_ = lean_ctor_get(v_private_3251_, 1);
v_const2ModIdx_3271_ = lean_ctor_get(v_private_3251_, 2);
v_extensions_3272_ = lean_ctor_get(v_private_3251_, 3);
v_irBaseExts_3273_ = lean_ctor_get(v_private_3251_, 4);
v_isSharedCheck_3330_ = !lean_is_exclusive(v_private_3251_);
if (v_isSharedCheck_3330_ == 0)
{
lean_object* v_unused_3331_; 
v_unused_3331_ = lean_ctor_get(v_private_3251_, 5);
lean_dec(v_unused_3331_);
v___x_3275_ = v_private_3251_;
v_isShared_3276_ = v_isSharedCheck_3330_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_irBaseExts_3273_);
lean_inc(v_extensions_3272_);
lean_inc(v_const2ModIdx_3271_);
lean_inc(v_diagnostics_3270_);
lean_inc(v_constants_3268_);
lean_dec(v_private_3251_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3330_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
uint32_t v_trustLevel_3277_; lean_object* v_mainModule_3278_; uint8_t v_isModule_3279_; lean_object* v_regions_3280_; lean_object* v_modules_3281_; lean_object* v_moduleName2Idx_3282_; lean_object* v_importAllModules_3283_; lean_object* v_moduleData_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3328_; 
v_trustLevel_3277_ = lean_ctor_get_uint32(v_header_3252_, sizeof(void*)*7);
v_mainModule_3278_ = lean_ctor_get(v_header_3252_, 0);
v_isModule_3279_ = lean_ctor_get_uint8(v_header_3252_, sizeof(void*)*7 + 4);
v_regions_3280_ = lean_ctor_get(v_header_3252_, 2);
v_modules_3281_ = lean_ctor_get(v_header_3252_, 3);
v_moduleName2Idx_3282_ = lean_ctor_get(v_header_3252_, 4);
v_importAllModules_3283_ = lean_ctor_get(v_header_3252_, 5);
v_moduleData_3284_ = lean_ctor_get(v_header_3252_, 6);
v_isSharedCheck_3328_ = !lean_is_exclusive(v_header_3252_);
if (v_isSharedCheck_3328_ == 0)
{
lean_object* v_unused_3329_; 
v_unused_3329_ = lean_ctor_get(v_header_3252_, 1);
lean_dec(v_unused_3329_);
v___x_3286_ = v_header_3252_;
v_isShared_3287_ = v_isSharedCheck_3328_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_moduleData_3284_);
lean_inc(v_importAllModules_3283_);
lean_inc(v_moduleName2Idx_3282_);
lean_inc(v_modules_3281_);
lean_inc(v_regions_3280_);
lean_inc(v_mainModule_3278_);
lean_dec(v_header_3252_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3328_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3288_; lean_object* v_imports_3289_; lean_object* v___x_3291_; 
v___x_3288_ = lean_array_fget(v_moduleData_3245_, v___y_3237_);
lean_dec_ref(v_moduleData_3245_);
v_imports_3289_ = lean_ctor_get(v___x_3288_, 0);
lean_inc_ref(v_imports_3289_);
lean_dec(v___x_3288_);
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 1, v_imports_3289_);
v___x_3291_ = v___x_3286_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 7, 5);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_mainModule_3278_);
lean_ctor_set(v_reuseFailAlloc_3327_, 1, v_imports_3289_);
lean_ctor_set(v_reuseFailAlloc_3327_, 2, v_regions_3280_);
lean_ctor_set(v_reuseFailAlloc_3327_, 3, v_modules_3281_);
lean_ctor_set(v_reuseFailAlloc_3327_, 4, v_moduleName2Idx_3282_);
lean_ctor_set(v_reuseFailAlloc_3327_, 5, v_importAllModules_3283_);
lean_ctor_set(v_reuseFailAlloc_3327_, 6, v_moduleData_3284_);
lean_ctor_set_uint32(v_reuseFailAlloc_3327_, sizeof(void*)*7, v_trustLevel_3277_);
lean_ctor_set_uint8(v_reuseFailAlloc_3327_, sizeof(void*)*7 + 4, v_isModule_3279_);
v___x_3291_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
lean_object* v___x_3293_; 
if (v_isShared_3276_ == 0)
{
lean_ctor_set(v___x_3275_, 5, v___x_3291_);
v___x_3293_ = v___x_3275_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_constants_3268_);
lean_ctor_set(v_reuseFailAlloc_3326_, 1, v_diagnostics_3270_);
lean_ctor_set(v_reuseFailAlloc_3326_, 2, v_const2ModIdx_3271_);
lean_ctor_set(v_reuseFailAlloc_3326_, 3, v_extensions_3272_);
lean_ctor_set(v_reuseFailAlloc_3326_, 4, v_irBaseExts_3273_);
lean_ctor_set(v_reuseFailAlloc_3326_, 5, v___x_3291_);
lean_ctor_set_uint8(v_reuseFailAlloc_3326_, sizeof(void*)*6, v_quotInit_3269_);
v___x_3293_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
lean_object* v___x_3295_; 
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 0, v___x_3293_);
v___x_3295_ = v___x_3266_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3293_);
lean_ctor_set(v_reuseFailAlloc_3325_, 1, v_public_3264_);
v___x_3295_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
lean_object* v___x_3297_; 
if (v_isShared_3263_ == 0)
{
lean_ctor_set(v___x_3262_, 0, v___x_3295_);
v___x_3297_ = v___x_3262_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v___x_3295_);
lean_ctor_set(v_reuseFailAlloc_3324_, 1, v_serverBaseExts_3253_);
lean_ctor_set(v_reuseFailAlloc_3324_, 2, v_checked_3254_);
lean_ctor_set(v_reuseFailAlloc_3324_, 3, v_asyncConstsMap_3255_);
lean_ctor_set(v_reuseFailAlloc_3324_, 4, v_asyncCtx_x3f_3256_);
lean_ctor_set(v_reuseFailAlloc_3324_, 5, v_importRealizationCtx_x3f_3257_);
lean_ctor_set(v_reuseFailAlloc_3324_, 6, v_localRealizationCtxMap_3258_);
lean_ctor_set(v_reuseFailAlloc_3324_, 7, v_allRealizations_3259_);
lean_ctor_set_uint8(v_reuseFailAlloc_3324_, sizeof(void*)*8, v_isExporting_3260_);
v___x_3297_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v_env_3320_; lean_object* v___x_3321_; uint8_t v___x_3322_; uint8_t v___x_3323_; 
v___x_3298_ = l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
v___x_3299_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2932_, v___x_3298_, v___x_3297_, v___y_3237_, v___y_3238_);
lean_dec(v___y_3237_);
v___x_3300_ = l_Lean_firstFrontendMacroScope;
v___x_3301_ = lean_obj_once(&l_main___closed__22, &l_main___closed__22_once, _init_l_main___closed__22);
v___x_3302_ = ((lean_object*)(l_main___closed__25));
lean_inc_n(v___y_3233_, 3);
v___x_3303_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3303_, 0, v___y_3233_);
lean_ctor_set(v___x_3303_, 1, v___x_3230_);
lean_ctor_set(v___x_3303_, 2, v___x_2918_);
v___x_3304_ = lean_obj_once(&l_main___closed__26, &l_main___closed__26_once, _init_l_main___closed__26);
v___x_3305_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_3306_ = lean_obj_once(&l_main___closed__30, &l_main___closed__30_once, _init_l_main___closed__30);
v___x_3307_ = lean_obj_once(&l_main___closed__31, &l_main___closed__31_once, _init_l_main___closed__31);
v___x_3308_ = ((lean_object*)(l_main___closed__32));
lean_inc_ref(v___x_3303_);
v___x_3309_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3297_);
lean_ctor_set(v___x_3309_, 1, v___x_3301_);
lean_ctor_set(v___x_3309_, 2, v___x_3302_);
lean_ctor_set(v___x_3309_, 3, v___x_3303_);
lean_ctor_set(v___x_3309_, 4, v___x_3304_);
lean_ctor_set(v___x_3309_, 5, v___x_3305_);
lean_ctor_set(v___x_3309_, 6, v___x_3306_);
lean_ctor_set(v___x_3309_, 7, v___x_3307_);
lean_ctor_set(v___x_3309_, 8, v___x_3308_);
v___x_3310_ = lean_st_mk_ref(v___x_3309_);
v___x_3311_ = l_Lean_inheritedTraceOptions;
v___x_3312_ = lean_st_ref_get(v___x_3311_);
v___x_3313_ = lean_st_ref_get(v___x_3310_);
v___x_3314_ = l_Lean_instInhabitedFileMap_default;
v___x_3315_ = lean_unsigned_to_nat(1000u);
v___x_3316_ = lean_box(0);
v___x_3317_ = l_Lean_Core_getMaxHeartbeats(v___x_2938_);
v___x_3318_ = lean_box(0);
lean_inc_ref(v___x_2938_);
lean_inc(v_head_2899_);
v___x_3319_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3319_, 0, v_head_2899_);
lean_ctor_set(v___x_3319_, 1, v___x_3314_);
lean_ctor_set(v___x_3319_, 2, v___x_2938_);
lean_ctor_set(v___x_3319_, 3, v___x_2937_);
lean_ctor_set(v___x_3319_, 4, v___x_3315_);
lean_ctor_set(v___x_3319_, 5, v___x_3316_);
lean_ctor_set(v___x_3319_, 6, v___y_3233_);
lean_ctor_set(v___x_3319_, 7, v___x_2918_);
lean_ctor_set(v___x_3319_, 8, v___x_2937_);
lean_ctor_set(v___x_3319_, 9, v___x_3317_);
lean_ctor_set(v___x_3319_, 10, v___y_3233_);
lean_ctor_set(v___x_3319_, 11, v___x_3300_);
lean_ctor_set(v___x_3319_, 12, v___x_3318_);
lean_ctor_set(v___x_3319_, 13, v___x_3312_);
lean_ctor_set_uint8(v___x_3319_, sizeof(void*)*14, v___x_2909_);
lean_ctor_set_uint8(v___x_3319_, sizeof(void*)*14 + 1, v___x_2909_);
v_env_3320_ = lean_ctor_get(v___x_3313_, 0);
lean_inc_ref(v_env_3320_);
lean_dec(v___x_3313_);
v___x_3321_ = l_Lean_diagnostics;
v___x_3322_ = l_Lean_Option_get___at___00main_spec__8(v___x_2938_, v___x_3321_);
v___x_3323_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3320_);
lean_dec_ref(v_env_3320_);
if (v___x_3323_ == 0)
{
if (v___x_3322_ == 0)
{
v___y_3185_ = v___x_3318_;
v___y_3186_ = v___x_3305_;
v___y_3187_ = v___y_3232_;
v___y_3188_ = v___x_3300_;
v___y_3189_ = v___x_2918_;
v___y_3190_ = v___x_3247_;
v___y_3191_ = v___x_3314_;
v___y_3192_ = v___x_3311_;
v___y_3193_ = v___x_3316_;
v___y_3194_ = v___x_3322_;
v___y_3195_ = v___x_3306_;
v___y_3196_ = v___x_3301_;
v___y_3197_ = v___x_3310_;
v___y_3198_ = v___x_3303_;
v___y_3199_ = v___x_3319_;
v___y_3200_ = v___x_3302_;
v___y_3201_ = v___x_3307_;
v___y_3202_ = v___x_3305_;
v___y_3203_ = v___y_3233_;
v___y_3204_ = v___x_3304_;
v___y_3205_ = v___x_3308_;
v___y_3206_ = v___x_3298_;
v___y_3207_ = v___x_3299_;
v___y_3208_ = v___x_3247_;
goto v___jp_3184_;
}
else
{
v___y_3185_ = v___x_3318_;
v___y_3186_ = v___x_3305_;
v___y_3187_ = v___y_3232_;
v___y_3188_ = v___x_3300_;
v___y_3189_ = v___x_2918_;
v___y_3190_ = v___x_3247_;
v___y_3191_ = v___x_3314_;
v___y_3192_ = v___x_3311_;
v___y_3193_ = v___x_3316_;
v___y_3194_ = v___x_3322_;
v___y_3195_ = v___x_3306_;
v___y_3196_ = v___x_3301_;
v___y_3197_ = v___x_3310_;
v___y_3198_ = v___x_3303_;
v___y_3199_ = v___x_3319_;
v___y_3200_ = v___x_3302_;
v___y_3201_ = v___x_3307_;
v___y_3202_ = v___x_3305_;
v___y_3203_ = v___y_3233_;
v___y_3204_ = v___x_3304_;
v___y_3205_ = v___x_3308_;
v___y_3206_ = v___x_3298_;
v___y_3207_ = v___x_3299_;
v___y_3208_ = v___x_3323_;
goto v___jp_3184_;
}
}
else
{
v___y_3185_ = v___x_3318_;
v___y_3186_ = v___x_3305_;
v___y_3187_ = v___y_3232_;
v___y_3188_ = v___x_3300_;
v___y_3189_ = v___x_2918_;
v___y_3190_ = v___x_3247_;
v___y_3191_ = v___x_3314_;
v___y_3192_ = v___x_3311_;
v___y_3193_ = v___x_3316_;
v___y_3194_ = v___x_3322_;
v___y_3195_ = v___x_3306_;
v___y_3196_ = v___x_3301_;
v___y_3197_ = v___x_3310_;
v___y_3198_ = v___x_3303_;
v___y_3199_ = v___x_3319_;
v___y_3200_ = v___x_3302_;
v___y_3201_ = v___x_3307_;
v___y_3202_ = v___x_3305_;
v___y_3203_ = v___y_3233_;
v___y_3204_ = v___x_3304_;
v___y_3205_ = v___x_3308_;
v___y_3206_ = v___x_3298_;
v___y_3207_ = v___x_3299_;
v___y_3208_ = v___x_3322_;
goto v___jp_3184_;
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
v___jp_3337_:
{
lean_object* v___x_3343_; lean_object* v_toEnvExtension_3344_; lean_object* v_asyncMode_3345_; lean_object* v___x_3346_; lean_object* v_importedEntries_3347_; lean_object* v_state_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; uint8_t v___x_3351_; 
v___x_3343_ = l_Lean_IR_declMapExt;
v_toEnvExtension_3344_ = lean_ctor_get(v___x_3343_, 0);
v_asyncMode_3345_ = lean_ctor_get(v_toEnvExtension_3344_, 2);
lean_inc(v___y_3339_);
lean_inc_ref(v___y_3342_);
v___x_3346_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2929_, v_toEnvExtension_3344_, v___y_3342_, v_asyncMode_3345_, v___y_3339_);
v_importedEntries_3347_ = lean_ctor_get(v___x_3346_, 0);
lean_inc_ref(v_importedEntries_3347_);
v_state_3348_ = lean_ctor_get(v___x_3346_, 1);
lean_inc(v_state_3348_);
lean_dec(v___x_3346_);
v___x_3349_ = lean_array_get_borrowed(v___x_2930_, v_importedEntries_3347_, v___y_3340_);
v___x_3350_ = lean_array_get_size(v___x_3349_);
v___x_3351_ = lean_nat_dec_lt(v___x_2937_, v___x_3350_);
if (v___x_3351_ == 0)
{
v___y_3232_ = v___y_3338_;
v___y_3233_ = v___y_3339_;
v___y_3234_ = v___y_3342_;
v___y_3235_ = v_importedEntries_3347_;
v___y_3236_ = v_toEnvExtension_3344_;
v___y_3237_ = v___y_3340_;
v___y_3238_ = v___y_3341_;
v___y_3239_ = v_state_3348_;
goto v___jp_3231_;
}
else
{
uint8_t v___x_3352_; 
v___x_3352_ = lean_nat_dec_le(v___x_3350_, v___x_3350_);
if (v___x_3352_ == 0)
{
if (v___x_3351_ == 0)
{
v___y_3232_ = v___y_3338_;
v___y_3233_ = v___y_3339_;
v___y_3234_ = v___y_3342_;
v___y_3235_ = v_importedEntries_3347_;
v___y_3236_ = v_toEnvExtension_3344_;
v___y_3237_ = v___y_3340_;
v___y_3238_ = v___y_3341_;
v___y_3239_ = v_state_3348_;
goto v___jp_3231_;
}
else
{
size_t v___x_3353_; size_t v___x_3354_; lean_object* v___x_3355_; 
v___x_3353_ = ((size_t)0ULL);
v___x_3354_ = lean_usize_of_nat(v___x_3350_);
lean_inc_ref(v___y_3342_);
v___x_3355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3342_, v___x_3349_, v___x_3353_, v___x_3354_, v_state_3348_);
v___y_3232_ = v___y_3338_;
v___y_3233_ = v___y_3339_;
v___y_3234_ = v___y_3342_;
v___y_3235_ = v_importedEntries_3347_;
v___y_3236_ = v_toEnvExtension_3344_;
v___y_3237_ = v___y_3340_;
v___y_3238_ = v___y_3341_;
v___y_3239_ = v___x_3355_;
goto v___jp_3231_;
}
}
else
{
size_t v___x_3356_; size_t v___x_3357_; lean_object* v___x_3358_; 
v___x_3356_ = ((size_t)0ULL);
v___x_3357_ = lean_usize_of_nat(v___x_3350_);
lean_inc_ref(v___y_3342_);
v___x_3358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3342_, v___x_3349_, v___x_3356_, v___x_3357_, v_state_3348_);
v___y_3232_ = v___y_3338_;
v___y_3233_ = v___y_3339_;
v___y_3234_ = v___y_3342_;
v___y_3235_ = v_importedEntries_3347_;
v___y_3236_ = v_toEnvExtension_3344_;
v___y_3237_ = v___y_3340_;
v___y_3238_ = v___y_3341_;
v___y_3239_ = v___x_3358_;
goto v___jp_3231_;
}
}
}
v___jp_3359_:
{
uint8_t v___x_3367_; 
v___x_3367_ = lean_nat_dec_lt(v___x_2937_, v___y_3363_);
if (v___x_3367_ == 0)
{
lean_dec(v___y_3363_);
lean_dec_ref(v___y_3362_);
v___y_3338_ = v___y_3360_;
v___y_3339_ = v___y_3361_;
v___y_3340_ = v___y_3364_;
v___y_3341_ = v___y_3365_;
v___y_3342_ = v___y_3366_;
goto v___jp_3337_;
}
else
{
uint8_t v___x_3368_; 
v___x_3368_ = lean_nat_dec_le(v___y_3363_, v___y_3363_);
if (v___x_3368_ == 0)
{
if (v___x_3367_ == 0)
{
lean_dec(v___y_3363_);
lean_dec_ref(v___y_3362_);
v___y_3338_ = v___y_3360_;
v___y_3339_ = v___y_3361_;
v___y_3340_ = v___y_3364_;
v___y_3341_ = v___y_3365_;
v___y_3342_ = v___y_3366_;
goto v___jp_3337_;
}
else
{
size_t v___x_3369_; size_t v___x_3370_; lean_object* v___x_3371_; 
v___x_3369_ = ((size_t)0ULL);
v___x_3370_ = lean_usize_of_nat(v___y_3363_);
lean_dec(v___y_3363_);
v___x_3371_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3362_, v___x_3369_, v___x_3370_, v___y_3366_);
lean_dec_ref(v___y_3362_);
v___y_3338_ = v___y_3360_;
v___y_3339_ = v___y_3361_;
v___y_3340_ = v___y_3364_;
v___y_3341_ = v___y_3365_;
v___y_3342_ = v___x_3371_;
goto v___jp_3337_;
}
}
else
{
size_t v___x_3372_; size_t v___x_3373_; lean_object* v___x_3374_; 
v___x_3372_ = ((size_t)0ULL);
v___x_3373_ = lean_usize_of_nat(v___y_3363_);
lean_dec(v___y_3363_);
v___x_3374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3362_, v___x_3372_, v___x_3373_, v___y_3366_);
lean_dec_ref(v___y_3362_);
v___y_3338_ = v___y_3360_;
v___y_3339_ = v___y_3361_;
v___y_3340_ = v___y_3364_;
v___y_3341_ = v___y_3365_;
v___y_3342_ = v___x_3374_;
goto v___jp_3337_;
}
}
}
v___jp_3375_:
{
lean_object* v___x_3382_; uint8_t v___x_3383_; 
v___x_3382_ = lean_array_get_size(v___y_3381_);
v___x_3383_ = lean_nat_dec_lt(v___x_2937_, v___x_3382_);
if (v___x_3383_ == 0)
{
v___y_3360_ = v___y_3376_;
v___y_3361_ = v___y_3378_;
v___y_3362_ = v___y_3381_;
v___y_3363_ = v___x_3382_;
v___y_3364_ = v___y_3377_;
v___y_3365_ = v___y_3380_;
v___y_3366_ = v___y_3379_;
goto v___jp_3359_;
}
else
{
uint8_t v___x_3384_; 
v___x_3384_ = lean_nat_dec_le(v___x_3382_, v___x_3382_);
if (v___x_3384_ == 0)
{
if (v___x_3383_ == 0)
{
v___y_3360_ = v___y_3376_;
v___y_3361_ = v___y_3378_;
v___y_3362_ = v___y_3381_;
v___y_3363_ = v___x_3382_;
v___y_3364_ = v___y_3377_;
v___y_3365_ = v___y_3380_;
v___y_3366_ = v___y_3379_;
goto v___jp_3359_;
}
else
{
size_t v___x_3385_; size_t v___x_3386_; lean_object* v___x_3387_; 
v___x_3385_ = ((size_t)0ULL);
v___x_3386_ = lean_usize_of_nat(v___x_3382_);
v___x_3387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3381_, v___x_3385_, v___x_3386_, v___y_3379_);
v___y_3360_ = v___y_3376_;
v___y_3361_ = v___y_3378_;
v___y_3362_ = v___y_3381_;
v___y_3363_ = v___x_3382_;
v___y_3364_ = v___y_3377_;
v___y_3365_ = v___y_3380_;
v___y_3366_ = v___x_3387_;
goto v___jp_3359_;
}
}
else
{
size_t v___x_3388_; size_t v___x_3389_; lean_object* v___x_3390_; 
v___x_3388_ = ((size_t)0ULL);
v___x_3389_ = lean_usize_of_nat(v___x_3382_);
v___x_3390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3381_, v___x_3388_, v___x_3389_, v___y_3379_);
v___y_3360_ = v___y_3376_;
v___y_3361_ = v___y_3378_;
v___y_3362_ = v___y_3381_;
v___y_3363_ = v___x_3382_;
v___y_3364_ = v___y_3377_;
v___y_3365_ = v___y_3380_;
v___y_3366_ = v___x_3390_;
goto v___jp_3359_;
}
}
}
v___jp_3394_:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___f_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3396_ = l_Lean_instInhabitedImportState_default;
v___x_3397_ = lean_box(v___x_3393_);
v___x_3398_ = lean_box(v___y_3395_);
v___x_3399_ = lean_box(v___x_2934_);
v___x_3400_ = lean_box(v___x_2909_);
lean_inc_ref(v___x_2938_);
lean_inc(v_name_2907_);
v___f_3401_ = lean_alloc_closure((void*)(l_main___lam__0___boxed), 10, 9);
lean_closure_set(v___f_3401_, 0, v___x_3396_);
lean_closure_set(v___f_3401_, 1, v___x_3392_);
lean_closure_set(v___f_3401_, 2, v___x_3397_);
lean_closure_set(v___f_3401_, 3, v___x_2931_);
lean_closure_set(v___f_3401_, 4, v___x_3398_);
lean_closure_set(v___f_3401_, 5, v_name_2907_);
lean_closure_set(v___f_3401_, 6, v___x_2938_);
lean_closure_set(v___f_3401_, 7, v___x_3399_);
lean_closure_set(v___f_3401_, 8, v___x_3400_);
v___x_3402_ = lean_alloc_closure((void*)(l_Lean_withImporting___boxed), 3, 2);
lean_closure_set(v___x_3402_, 0, lean_box(0));
lean_closure_set(v___x_3402_, 1, v___f_3401_);
v___x_3403_ = lean_box(0);
v___x_3404_ = l_Lean_profileitIOUnsafe___redArg(v___x_3228_, v___x_2938_, v___x_3402_, v___x_3403_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_a_3405_; lean_object* v___x_3406_; lean_object* v_ext_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_a_3405_);
lean_dec_ref(v___x_3404_);
v___x_3406_ = l_Lean_Compiler_CSimp_ext;
v_ext_3407_ = lean_ctor_get(v___x_3406_, 1);
lean_inc(v_name_2907_);
v___x_3408_ = l_Lean_Environment_setMainModule(v_a_3405_, v_name_2907_);
lean_inc_ref(v_ext_3407_);
v___x_3409_ = l_main___elam__0___redArg(v___x_3403_, v___x_2925_, v_ext_3407_, v___x_3408_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v_a_3410_; lean_object* v___x_3411_; lean_object* v_ext_3412_; lean_object* v___x_3413_; 
v_a_3410_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_a_3410_);
lean_dec_ref(v___x_3409_);
v___x_3411_ = l_Lean_Meta_instanceExtension;
v_ext_3412_ = lean_ctor_get(v___x_3411_, 1);
lean_inc_ref(v_ext_3412_);
v___x_3413_ = l_main___elam__0___redArg(v___x_3403_, v___x_2925_, v_ext_3412_, v_a_3410_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_a_3414_);
lean_dec_ref(v___x_3413_);
v___x_3415_ = l_Lean_classExtension;
v___x_3416_ = l_main___elam__0___redArg(v___x_3403_, v___x_2926_, v___x_3415_, v_a_3414_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_a_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
lean_inc(v_a_3417_);
lean_dec_ref(v___x_3416_);
v___x_3418_ = l_Lean_Meta_Match_Extension_extension;
v___x_3419_ = l_main___elam__0___redArg(v___x_3403_, v___x_2927_, v___x_3418_, v_a_3417_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v_a_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3448_; 
v_a_3420_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3422_ = v___x_3419_;
v_isShared_3423_ = v_isSharedCheck_3448_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_a_3420_);
lean_dec(v___x_3419_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3448_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3424_; 
v___x_3424_ = l_Lean_Environment_getModuleIdx_x3f(v_a_3420_, v_name_2907_);
if (lean_obj_tag(v___x_3424_) == 1)
{
lean_object* v_val_3425_; lean_object* v___x_3426_; uint8_t v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; uint8_t v___x_3431_; 
lean_del_object(v___x_3422_);
v_val_3425_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_val_3425_);
lean_dec_ref(v___x_3424_);
v___x_3426_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_3427_ = 0;
v___x_3428_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2928_, v___x_3426_, v_a_3420_, v_val_3425_, v___x_3427_);
v___x_3429_ = lean_array_get_size(v___x_3428_);
v___x_3430_ = ((lean_object*)(l_main___closed__33));
v___x_3431_ = lean_nat_dec_lt(v___x_2937_, v___x_3429_);
if (v___x_3431_ == 0)
{
lean_dec_ref(v___x_3428_);
v___y_3376_ = v___x_3403_;
v___y_3377_ = v_val_3425_;
v___y_3378_ = v___x_3403_;
v___y_3379_ = v_a_3420_;
v___y_3380_ = v___x_3427_;
v___y_3381_ = v___x_3430_;
goto v___jp_3375_;
}
else
{
uint8_t v___x_3432_; 
v___x_3432_ = lean_nat_dec_le(v___x_3429_, v___x_3429_);
if (v___x_3432_ == 0)
{
if (v___x_3431_ == 0)
{
lean_dec_ref(v___x_3428_);
v___y_3376_ = v___x_3403_;
v___y_3377_ = v_val_3425_;
v___y_3378_ = v___x_3403_;
v___y_3379_ = v_a_3420_;
v___y_3380_ = v___x_3427_;
v___y_3381_ = v___x_3430_;
goto v___jp_3375_;
}
else
{
size_t v___x_3433_; size_t v___x_3434_; lean_object* v___x_3435_; 
v___x_3433_ = ((size_t)0ULL);
v___x_3434_ = lean_usize_of_nat(v___x_3429_);
lean_inc(v_a_3420_);
v___x_3435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3420_, v___x_3428_, v___x_3433_, v___x_3434_, v___x_3430_);
lean_dec_ref(v___x_3428_);
v___y_3376_ = v___x_3403_;
v___y_3377_ = v_val_3425_;
v___y_3378_ = v___x_3403_;
v___y_3379_ = v_a_3420_;
v___y_3380_ = v___x_3427_;
v___y_3381_ = v___x_3435_;
goto v___jp_3375_;
}
}
else
{
size_t v___x_3436_; size_t v___x_3437_; lean_object* v___x_3438_; 
v___x_3436_ = ((size_t)0ULL);
v___x_3437_ = lean_usize_of_nat(v___x_3429_);
lean_inc(v_a_3420_);
v___x_3438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3420_, v___x_3428_, v___x_3436_, v___x_3437_, v___x_3430_);
lean_dec_ref(v___x_3428_);
v___y_3376_ = v___x_3403_;
v___y_3377_ = v_val_3425_;
v___y_3378_ = v___x_3403_;
v___y_3379_ = v_a_3420_;
v___y_3380_ = v___x_3427_;
v___y_3381_ = v___x_3438_;
goto v___jp_3375_;
}
}
}
else
{
lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3446_; 
lean_dec(v___x_3424_);
lean_dec(v_a_3420_);
lean_dec_ref(v___x_2938_);
lean_del_object(v___x_2923_);
lean_dec(v_fst_2920_);
lean_dec(v_head_2900_);
lean_dec(v_head_2899_);
v___x_3439_ = ((lean_object*)(l_main___closed__34));
v___x_3440_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2907_, v___x_2934_);
v___x_3441_ = lean_string_append(v___x_3439_, v___x_3440_);
lean_dec_ref(v___x_3440_);
v___x_3442_ = ((lean_object*)(l_main___closed__35));
v___x_3443_ = lean_string_append(v___x_3441_, v___x_3442_);
v___x_3444_ = lean_mk_io_user_error(v___x_3443_);
if (v_isShared_3423_ == 0)
{
lean_ctor_set_tag(v___x_3422_, 1);
lean_ctor_set(v___x_3422_, 0, v___x_3444_);
v___x_3446_ = v___x_3422_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3444_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
}
else
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3456_; 
lean_dec_ref(v___x_2938_);
lean_del_object(v___x_2923_);
lean_dec(v_fst_2920_);
lean_dec(v_name_2907_);
lean_dec(v_head_2900_);
lean_dec(v_head_2899_);
v_a_3449_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3451_ = v___x_3419_;
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3419_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3454_; 
if (v_isShared_3452_ == 0)
{
v___x_3454_ = v___x_3451_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_a_3449_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
}
else
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3464_; 
lean_dec_ref(v___x_2938_);
lean_del_object(v___x_2923_);
lean_dec(v_fst_2920_);
lean_dec(v_name_2907_);
lean_dec(v_head_2900_);
lean_dec(v_head_2899_);
v_a_3457_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3459_ = v___x_3416_;
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3416_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3462_; 
if (v_isShared_3460_ == 0)
{
v___x_3462_ = v___x_3459_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3457_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3472_; 
lean_dec_ref(v___x_2938_);
lean_del_object(v___x_2923_);
lean_dec(v_fst_2920_);
lean_dec(v_name_2907_);
lean_dec(v_head_2900_);
lean_dec(v_head_2899_);
v_a_3465_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3467_ = v___x_3413_;
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3413_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3470_; 
if (v_isShared_3468_ == 0)
{
v___x_3470_ = v___x_3467_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3465_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
lean_dec_ref(v___x_2938_);
lean_del_object(v___x_2923_);
lean_dec(v_fst_2920_);
lean_dec(v_name_2907_);
lean_dec(v_head_2900_);
lean_dec(v_head_2899_);
v_a_3473_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3409_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3409_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3478_; 
if (v_isShared_3476_ == 0)
{
v___x_3478_ = v___x_3475_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
else
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3488_; 
lean_dec_ref(v___x_2938_);
lean_del_object(v___x_2923_);
lean_dec(v_fst_2920_);
lean_dec(v_name_2907_);
lean_dec(v_head_2900_);
lean_dec(v_head_2899_);
v_a_3481_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3483_ = v___x_3404_;
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3404_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3486_; 
if (v_isShared_3484_ == 0)
{
v___x_3486_ = v___x_3483_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_a_3481_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
}
}
}
else
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3498_; 
lean_dec(v_a_2915_);
lean_dec(v_name_2907_);
lean_dec(v_head_2900_);
lean_dec(v_head_2899_);
v_a_3491_ = lean_ctor_get(v___x_2919_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3493_ = v___x_2919_;
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_2919_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3496_; 
if (v_isShared_3494_ == 0)
{
v___x_3496_ = v___x_3493_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_a_3491_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
}
else
{
lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3506_; 
lean_dec(v_a_2915_);
lean_dec(v_name_2907_);
lean_dec(v_head_2900_);
lean_dec(v_head_2899_);
v_a_3499_ = lean_ctor_get(v___x_2916_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3501_ = v___x_2916_;
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3499_);
lean_dec(v___x_2916_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3504_; 
if (v_isShared_3502_ == 0)
{
v___x_3504_ = v___x_3501_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_a_3499_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
}
else
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3514_; 
lean_dec(v_name_2907_);
lean_dec(v_head_2900_);
lean_dec(v_head_2899_);
v_a_3507_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3509_ = v___x_2914_;
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_2914_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3512_; 
if (v_isShared_3510_ == 0)
{
v___x_3512_ = v___x_3509_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_a_3507_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
}
}
}
else
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3523_; 
lean_del_object(v___x_2903_);
lean_dec(v_tail_2901_);
lean_dec(v_head_2900_);
lean_dec(v_head_2899_);
v_a_3516_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3518_ = v___x_2905_;
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_2905_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3521_; 
if (v_isShared_3519_ == 0)
{
v___x_3521_ = v___x_3518_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3516_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
}
}
else
{
lean_dec_ref(v_tail_2896_);
lean_dec(v_tail_2897_);
lean_dec_ref(v_args_2871_);
goto v___jp_2873_;
}
}
else
{
lean_dec_ref(v_args_2871_);
lean_dec(v_tail_2896_);
goto v___jp_2873_;
}
}
else
{
lean_dec(v_args_2871_);
goto v___jp_2873_;
}
v___jp_2873_:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2874_ = ((lean_object*)(l_main___closed__0));
v___x_2875_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_2874_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2883_; 
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2883_ == 0)
{
lean_object* v_unused_2884_; 
v_unused_2884_ = lean_ctor_get(v___x_2875_, 0);
lean_dec(v_unused_2884_);
v___x_2877_ = v___x_2875_;
v_isShared_2878_ = v_isSharedCheck_2883_;
goto v_resetjp_2876_;
}
else
{
lean_dec(v___x_2875_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2883_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2879_; lean_object* v___x_2881_; 
v___x_2879_ = l_main___boxed__const__1;
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 0, v___x_2879_);
v___x_2881_ = v___x_2877_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2879_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
else
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2892_; 
v_a_2885_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2887_ = v___x_2875_;
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2875_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2890_; 
if (v_isShared_2888_ == 0)
{
v___x_2890_ = v___x_2887_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2885_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
}
v___jp_2893_:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2894_ = l_main___boxed__const__2;
v___x_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2894_);
return v___x_2895_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_3525_, lean_object* v_a_3526_){
_start:
{
lean_object* v_res_3527_; 
v_res_3527_ = _lean_main(v_args_3525_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object* v_as_3528_, lean_object* v_as_x27_3529_, lean_object* v_b_3530_, lean_object* v_a_3531_){
_start:
{
lean_object* v___x_3533_; 
v___x_3533_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_3529_, v_b_3530_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object* v_as_3534_, lean_object* v_as_x27_3535_, lean_object* v_b_3536_, lean_object* v_a_3537_, lean_object* v___y_3538_){
_start:
{
lean_object* v_res_3539_; 
v_res_3539_ = l_List_forIn_x27_loop___at___00main_spec__1(v_as_3534_, v_as_x27_3535_, v_b_3536_, v_a_3537_);
lean_dec(v_as_x27_3535_);
lean_dec(v_as_3534_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(lean_object* v___y_3540_, lean_object* v___y_3541_){
_start:
{
lean_object* v___x_3543_; 
v___x_3543_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_3541_);
return v___x_3543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___boxed(lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(v___y_3544_, v___y_3545_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(lean_object* v_00_u03b2_3548_, lean_object* v_m_3549_, lean_object* v_a_3550_, lean_object* v_fallback_3551_){
_start:
{
lean_object* v___x_3552_; 
v___x_3552_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_3549_, v_a_3550_, v_fallback_3551_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___boxed(lean_object* v_00_u03b2_3553_, lean_object* v_m_3554_, lean_object* v_a_3555_, lean_object* v_fallback_3556_){
_start:
{
lean_object* v_res_3557_; 
v_res_3557_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(v_00_u03b2_3553_, v_m_3554_, v_a_3555_, v_fallback_3556_);
lean_dec(v_fallback_3556_);
lean_dec_ref(v_a_3555_);
lean_dec_ref(v_m_3554_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18(lean_object* v_00_u03b2_3558_, lean_object* v_m_3559_, lean_object* v_a_3560_, lean_object* v_b_3561_){
_start:
{
lean_object* v___x_3562_; 
v___x_3562_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_m_3559_, v_a_3560_, v_b_3561_);
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(lean_object* v_n_3563_, lean_object* v_as_3564_, lean_object* v_lo_3565_, lean_object* v_hi_3566_, lean_object* v_w_3567_, lean_object* v_hlo_3568_, lean_object* v_hhi_3569_){
_start:
{
lean_object* v___x_3570_; 
v___x_3570_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_3563_, v_as_3564_, v_lo_3565_, v_hi_3566_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___boxed(lean_object* v_n_3571_, lean_object* v_as_3572_, lean_object* v_lo_3573_, lean_object* v_hi_3574_, lean_object* v_w_3575_, lean_object* v_hlo_3576_, lean_object* v_hhi_3577_){
_start:
{
lean_object* v_res_3578_; 
v_res_3578_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(v_n_3571_, v_as_3572_, v_lo_3573_, v_hi_3574_, v_w_3575_, v_hlo_3576_, v_hhi_3577_);
lean_dec(v_hi_3574_);
lean_dec(v_n_3571_);
return v_res_3578_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(lean_object* v_00_u03b2_3579_, lean_object* v_a_3580_, lean_object* v_fallback_3581_, lean_object* v_x_3582_){
_start:
{
lean_object* v___x_3583_; 
v___x_3583_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_3580_, v_fallback_3581_, v_x_3582_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3584_, lean_object* v_a_3585_, lean_object* v_fallback_3586_, lean_object* v_x_3587_){
_start:
{
lean_object* v_res_3588_; 
v_res_3588_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(v_00_u03b2_3584_, v_a_3585_, v_fallback_3586_, v_x_3587_);
lean_dec(v_x_3587_);
lean_dec(v_fallback_3586_);
lean_dec_ref(v_a_3585_);
return v_res_3588_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(lean_object* v_00_u03b2_3589_, lean_object* v_a_3590_, lean_object* v_x_3591_){
_start:
{
uint8_t v___x_3592_; 
v___x_3592_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_3590_, v_x_3591_);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___boxed(lean_object* v_00_u03b2_3593_, lean_object* v_a_3594_, lean_object* v_x_3595_){
_start:
{
uint8_t v_res_3596_; lean_object* v_r_3597_; 
v_res_3596_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(v_00_u03b2_3593_, v_a_3594_, v_x_3595_);
lean_dec(v_x_3595_);
lean_dec_ref(v_a_3594_);
v_r_3597_ = lean_box(v_res_3596_);
return v_r_3597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24(lean_object* v_00_u03b2_3598_, lean_object* v_data_3599_){
_start:
{
lean_object* v___x_3600_; 
v___x_3600_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_data_3599_);
return v___x_3600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25(lean_object* v_00_u03b2_3601_, lean_object* v_a_3602_, lean_object* v_b_3603_, lean_object* v_x_3604_){
_start:
{
lean_object* v___x_3605_; 
v___x_3605_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_3602_, v_b_3603_, v_x_3604_);
return v___x_3605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(lean_object* v_n_3606_, lean_object* v_lo_3607_, lean_object* v_hi_3608_, lean_object* v_hhi_3609_, lean_object* v_pivot_3610_, lean_object* v_as_3611_, lean_object* v_i_3612_, lean_object* v_k_3613_, lean_object* v_ilo_3614_, lean_object* v_ik_3615_, lean_object* v_w_3616_){
_start:
{
lean_object* v___x_3617_; 
v___x_3617_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_3608_, v_pivot_3610_, v_as_3611_, v_i_3612_, v_k_3613_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___boxed(lean_object* v_n_3618_, lean_object* v_lo_3619_, lean_object* v_hi_3620_, lean_object* v_hhi_3621_, lean_object* v_pivot_3622_, lean_object* v_as_3623_, lean_object* v_i_3624_, lean_object* v_k_3625_, lean_object* v_ilo_3626_, lean_object* v_ik_3627_, lean_object* v_w_3628_){
_start:
{
lean_object* v_res_3629_; 
v_res_3629_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(v_n_3618_, v_lo_3619_, v_hi_3620_, v_hhi_3621_, v_pivot_3622_, v_as_3623_, v_i_3624_, v_k_3625_, v_ilo_3626_, v_ik_3627_, v_w_3628_);
lean_dec_ref(v_pivot_3622_);
lean_dec(v_hi_3620_);
lean_dec(v_lo_3619_);
lean_dec(v_n_3618_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(lean_object* v_as_3630_, size_t v_sz_3631_, size_t v_i_3632_, lean_object* v_b_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_){
_start:
{
lean_object* v___x_3637_; 
v___x_3637_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_3630_, v_sz_3631_, v_i_3632_, v_b_3633_, v___y_3634_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___boxed(lean_object* v_as_3638_, lean_object* v_sz_3639_, lean_object* v_i_3640_, lean_object* v_b_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
size_t v_sz_boxed_3645_; size_t v_i_boxed_3646_; lean_object* v_res_3647_; 
v_sz_boxed_3645_ = lean_unbox_usize(v_sz_3639_);
lean_dec(v_sz_3639_);
v_i_boxed_3646_ = lean_unbox_usize(v_i_3640_);
lean_dec(v_i_3640_);
v_res_3647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(v_as_3638_, v_sz_boxed_3645_, v_i_boxed_3646_, v_b_3641_, v___y_3642_, v___y_3643_);
lean_dec(v___y_3643_);
lean_dec_ref(v___y_3642_);
lean_dec_ref(v_as_3638_);
return v_res_3647_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35(lean_object* v_00_u03b2_3648_, lean_object* v_i_3649_, lean_object* v_source_3650_, lean_object* v_target_3651_){
_start:
{
lean_object* v___x_3652_; 
v___x_3652_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v_i_3649_, v_source_3650_, v_target_3651_);
return v___x_3652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(uint8_t v___x_3653_, lean_object* v_as_3654_, size_t v_sz_3655_, size_t v_i_3656_, lean_object* v_b_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
lean_object* v___x_3661_; 
v___x_3661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_3653_, v_as_3654_, v_sz_3655_, v_i_3656_, v_b_3657_, v___y_3658_);
return v___x_3661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___boxed(lean_object* v___x_3662_, lean_object* v_as_3663_, lean_object* v_sz_3664_, lean_object* v_i_3665_, lean_object* v_b_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
uint8_t v___x_41215__boxed_3670_; size_t v_sz_boxed_3671_; size_t v_i_boxed_3672_; lean_object* v_res_3673_; 
v___x_41215__boxed_3670_ = lean_unbox(v___x_3662_);
v_sz_boxed_3671_ = lean_unbox_usize(v_sz_3664_);
lean_dec(v_sz_3664_);
v_i_boxed_3672_ = lean_unbox_usize(v_i_3665_);
lean_dec(v_i_3665_);
v_res_3673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(v___x_41215__boxed_3670_, v_as_3663_, v_sz_boxed_3671_, v_i_boxed_3672_, v_b_3666_, v___y_3667_, v___y_3668_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec_ref(v_as_3663_);
return v_res_3673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(lean_object* v_as_3674_, size_t v_sz_3675_, size_t v_i_3676_, lean_object* v_b_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_){
_start:
{
lean_object* v___x_3681_; 
v___x_3681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_3674_, v_sz_3675_, v_i_3676_, v_b_3677_, v___y_3678_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___boxed(lean_object* v_as_3682_, lean_object* v_sz_3683_, lean_object* v_i_3684_, lean_object* v_b_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
size_t v_sz_boxed_3689_; size_t v_i_boxed_3690_; lean_object* v_res_3691_; 
v_sz_boxed_3689_ = lean_unbox_usize(v_sz_3683_);
lean_dec(v_sz_3683_);
v_i_boxed_3690_ = lean_unbox_usize(v_i_3684_);
lean_dec(v_i_3684_);
v_res_3691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(v_as_3682_, v_sz_boxed_3689_, v_i_boxed_3690_, v_b_3685_, v___y_3686_, v___y_3687_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec_ref(v_as_3682_);
return v_res_3691_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44(lean_object* v_00_u03b2_3692_, lean_object* v_x_3693_, lean_object* v_x_3694_){
_start:
{
lean_object* v___x_3695_; 
v___x_3695_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_x_3693_, v_x_3694_);
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(uint8_t v___x_3696_, lean_object* v_as_3697_, size_t v_sz_3698_, size_t v_i_3699_, lean_object* v_b_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_){
_start:
{
lean_object* v___x_3704_; 
v___x_3704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_3696_, v_as_3697_, v_sz_3698_, v_i_3699_, v_b_3700_, v___y_3701_);
return v___x_3704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___boxed(lean_object* v___x_3705_, lean_object* v_as_3706_, lean_object* v_sz_3707_, lean_object* v_i_3708_, lean_object* v_b_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
uint8_t v___x_41246__boxed_3713_; size_t v_sz_boxed_3714_; size_t v_i_boxed_3715_; lean_object* v_res_3716_; 
v___x_41246__boxed_3713_ = lean_unbox(v___x_3705_);
v_sz_boxed_3714_ = lean_unbox_usize(v_sz_3707_);
lean_dec(v_sz_3707_);
v_i_boxed_3715_ = lean_unbox_usize(v_i_3708_);
lean_dec(v_i_3708_);
v_res_3716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(v___x_41246__boxed_3713_, v_as_3706_, v_sz_boxed_3714_, v_i_boxed_3715_, v_b_3709_, v___y_3710_, v___y_3711_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec_ref(v_as_3706_);
return v_res_3716_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_LeanIR(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
void lean_initialize();
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
  lean_initialize();
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
