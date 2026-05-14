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
lean_object* v___x_304_; lean_object* v___x_20177__overap_305_; lean_object* v___x_306_; 
v___x_304_ = lean_obj_once(&l_panic___at___00main_spec__5___closed__0, &l_panic___at___00main_spec__5___closed__0_once, _init_l_panic___at___00main_spec__5___closed__0);
v___x_20177__overap_305_ = lean_panic_fn_borrowed(v___x_304_, v_msg_302_);
v___x_306_ = lean_apply_1(v___x_20177__overap_305_, lean_box(0));
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
uint8_t v___x_36379__boxed_480_; uint8_t v___y_36381__boxed_481_; uint8_t v___x_36383__boxed_482_; uint8_t v___x_36384__boxed_483_; lean_object* v_res_484_; 
v___x_36379__boxed_480_ = lean_unbox(v___x_472_);
v___y_36381__boxed_481_ = lean_unbox(v___y_474_);
v___x_36383__boxed_482_ = lean_unbox(v___x_477_);
v___x_36384__boxed_483_ = lean_unbox(v___x_478_);
v_res_484_ = l_main___lam__0(v___x_470_, v___x_471_, v___x_36379__boxed_480_, v___x_473_, v___y_36381__boxed_481_, v_name_475_, v___x_476_, v___x_36383__boxed_482_, v___x_36384__boxed_483_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_main___lam__1(lean_object* v___x_486_, lean_object* v___x_487_, lean_object* v___x_488_, lean_object* v_name_489_, lean_object* v_a_490_, lean_object* v___x_491_, lean_object* v_head_492_, lean_object* v___x_493_, lean_object* v___x_494_, lean_object* v___x_495_, lean_object* v___x_496_, lean_object* v___x_497_, lean_object* v___x_498_, lean_object* v___x_499_, lean_object* v___x_500_, uint8_t v___x_501_, uint8_t v___x_502_){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v_env_508_; lean_object* v___x_509_; uint8_t v___x_510_; lean_object* v_fileName_512_; lean_object* v_fileMap_513_; lean_object* v_currRecDepth_514_; lean_object* v_ref_515_; lean_object* v_currNamespace_516_; lean_object* v_openDecls_517_; lean_object* v_initHeartbeats_518_; lean_object* v_maxHeartbeats_519_; lean_object* v_quotContext_520_; lean_object* v_currMacroScope_521_; lean_object* v_cancelTk_x3f_522_; uint8_t v_suppressElabErrors_523_; lean_object* v_inheritedTraceOptions_524_; lean_object* v___y_525_; uint8_t v___y_554_; uint8_t v___x_575_; 
v___x_504_ = lean_io_get_num_heartbeats();
v___x_505_ = lean_st_mk_ref(v___x_486_);
v___x_506_ = lean_st_ref_get(v___x_487_);
v___x_507_ = lean_st_ref_get(v___x_505_);
v_env_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc_ref(v_env_508_);
lean_dec(v___x_507_);
v___x_509_ = l_Lean_diagnostics;
v___x_510_ = l_Lean_Option_get___at___00main_spec__8(v___x_488_, v___x_509_);
v___x_575_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_508_);
lean_dec_ref(v_env_508_);
if (v___x_575_ == 0)
{
if (v___x_510_ == 0)
{
v___y_554_ = v___x_502_;
goto v___jp_553_;
}
else
{
v___y_554_ = v___x_575_;
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
lean_object* v___x_555_; lean_object* v_env_556_; lean_object* v_nextMacroScope_557_; lean_object* v_ngen_558_; lean_object* v_auxDeclNGen_559_; lean_object* v_traceState_560_; lean_object* v_messages_561_; lean_object* v_infoState_562_; lean_object* v_snapshotTasks_563_; lean_object* v_newDecls_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_573_; 
v___x_555_ = lean_st_ref_take(v___x_505_);
v_env_556_ = lean_ctor_get(v___x_555_, 0);
v_nextMacroScope_557_ = lean_ctor_get(v___x_555_, 1);
v_ngen_558_ = lean_ctor_get(v___x_555_, 2);
v_auxDeclNGen_559_ = lean_ctor_get(v___x_555_, 3);
v_traceState_560_ = lean_ctor_get(v___x_555_, 4);
v_messages_561_ = lean_ctor_get(v___x_555_, 6);
v_infoState_562_ = lean_ctor_get(v___x_555_, 7);
v_snapshotTasks_563_ = lean_ctor_get(v___x_555_, 8);
v_newDecls_564_ = lean_ctor_get(v___x_555_, 9);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; 
v_unused_574_ = lean_ctor_get(v___x_555_, 5);
lean_dec(v_unused_574_);
v___x_566_ = v___x_555_;
v_isShared_567_ = v_isSharedCheck_573_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_newDecls_564_);
lean_inc(v_snapshotTasks_563_);
lean_inc(v_infoState_562_);
lean_inc(v_messages_561_);
lean_inc(v_traceState_560_);
lean_inc(v_auxDeclNGen_559_);
lean_inc(v_ngen_558_);
lean_inc(v_nextMacroScope_557_);
lean_inc(v_env_556_);
lean_dec(v___x_555_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_573_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_568_ = l_Lean_Kernel_enableDiag(v_env_556_, v___x_510_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 5, v___x_491_);
lean_ctor_set(v___x_566_, 0, v___x_568_);
v___x_570_ = v___x_566_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_nextMacroScope_557_);
lean_ctor_set(v_reuseFailAlloc_572_, 2, v_ngen_558_);
lean_ctor_set(v_reuseFailAlloc_572_, 3, v_auxDeclNGen_559_);
lean_ctor_set(v_reuseFailAlloc_572_, 4, v_traceState_560_);
lean_ctor_set(v_reuseFailAlloc_572_, 5, v___x_491_);
lean_ctor_set(v_reuseFailAlloc_572_, 6, v_messages_561_);
lean_ctor_set(v_reuseFailAlloc_572_, 7, v_infoState_562_);
lean_ctor_set(v_reuseFailAlloc_572_, 8, v_snapshotTasks_563_);
lean_ctor_set(v_reuseFailAlloc_572_, 9, v_newDecls_564_);
v___x_570_ = v_reuseFailAlloc_572_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_571_; 
v___x_571_ = lean_st_ref_set(v___x_505_, v___x_570_);
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
lean_object* v___x_576_ = _args[0];
lean_object* v___x_577_ = _args[1];
lean_object* v___x_578_ = _args[2];
lean_object* v_name_579_ = _args[3];
lean_object* v_a_580_ = _args[4];
lean_object* v___x_581_ = _args[5];
lean_object* v_head_582_ = _args[6];
lean_object* v___x_583_ = _args[7];
lean_object* v___x_584_ = _args[8];
lean_object* v___x_585_ = _args[9];
lean_object* v___x_586_ = _args[10];
lean_object* v___x_587_ = _args[11];
lean_object* v___x_588_ = _args[12];
lean_object* v___x_589_ = _args[13];
lean_object* v___x_590_ = _args[14];
lean_object* v___x_591_ = _args[15];
lean_object* v___x_592_ = _args[16];
lean_object* v___y_593_ = _args[17];
_start:
{
uint8_t v___x_36469__boxed_594_; uint8_t v___x_36470__boxed_595_; lean_object* v_res_596_; 
v___x_36469__boxed_594_ = lean_unbox(v___x_591_);
v___x_36470__boxed_595_ = lean_unbox(v___x_592_);
v_res_596_ = l_main___lam__1(v___x_576_, v___x_577_, v___x_578_, v_name_579_, v_a_580_, v___x_581_, v_head_582_, v___x_583_, v___x_584_, v___x_585_, v___x_586_, v___x_587_, v___x_588_, v___x_589_, v___x_590_, v___x_36469__boxed_594_, v___x_36470__boxed_595_);
lean_dec(v_a_580_);
lean_dec(v___x_577_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(lean_object* v_s_597_){
_start:
{
lean_object* v___x_599_; lean_object* v_putStr_600_; lean_object* v___x_601_; 
v___x_599_ = lean_get_stderr();
v_putStr_600_ = lean_ctor_get(v___x_599_, 4);
lean_inc_ref(v_putStr_600_);
lean_dec_ref(v___x_599_);
v___x_601_ = lean_apply_2(v_putStr_600_, v_s_597_, lean_box(0));
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8___boxed(lean_object* v_s_602_, lean_object* v_a_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v_s_602_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6(lean_object* v_s_605_){
_start:
{
uint32_t v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_607_ = 10;
v___x_608_ = lean_string_push(v_s_605_, v___x_607_);
v___x_609_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6___boxed(lean_object* v_s_610_, lean_object* v_a_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_IO_eprintln___at___00main_spec__6(v_s_610_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(lean_object* v_o_616_, lean_object* v_k_617_, lean_object* v_v_618_){
_start:
{
lean_object* v_map_619_; uint8_t v_hasTrace_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_634_; 
v_map_619_ = lean_ctor_get(v_o_616_, 0);
v_hasTrace_620_ = lean_ctor_get_uint8(v_o_616_, sizeof(void*)*1);
v_isSharedCheck_634_ = !lean_is_exclusive(v_o_616_);
if (v_isSharedCheck_634_ == 0)
{
v___x_622_ = v_o_616_;
v_isShared_623_ = v_isSharedCheck_634_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_map_619_);
lean_dec(v_o_616_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_634_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_624_, 0, v_v_618_);
lean_inc(v_k_617_);
v___x_625_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_617_, v___x_624_, v_map_619_);
if (v_hasTrace_620_ == 0)
{
lean_object* v___x_626_; uint8_t v___x_627_; lean_object* v___x_629_; 
v___x_626_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_627_ = l_Lean_Name_isPrefixOf(v___x_626_, v_k_617_);
lean_dec(v_k_617_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v___x_625_);
v___x_629_ = v___x_622_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_625_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_ctor_set_uint8(v___x_629_, sizeof(void*)*1, v___x_627_);
return v___x_629_;
}
}
else
{
lean_object* v___x_632_; 
lean_dec(v_k_617_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v___x_625_);
v___x_632_ = v___x_622_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_625_);
lean_ctor_set_uint8(v_reuseFailAlloc_633_, sizeof(void*)*1, v_hasTrace_620_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00main_spec__3(lean_object* v_opts_635_, lean_object* v_opt_636_, lean_object* v_val_637_){
_start:
{
lean_object* v_name_638_; lean_object* v___x_639_; 
v_name_638_ = lean_ctor_get(v_opt_636_, 0);
lean_inc(v_name_638_);
lean_dec_ref(v_opt_636_);
v___x_639_ = l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(v_opts_635_, v_name_638_, v_val_637_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object* v___y_641_, lean_object* v_as_642_, size_t v_i_643_, size_t v_stop_644_, lean_object* v_b_645_){
_start:
{
lean_object* v___y_647_; uint8_t v___x_651_; 
v___x_651_ = lean_usize_dec_eq(v_i_643_, v_stop_644_);
if (v___x_651_ == 0)
{
lean_object* v_fst_652_; lean_object* v_snd_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___y_657_; 
v_fst_652_ = lean_ctor_get(v_b_645_, 0);
v_snd_653_ = lean_ctor_get(v_b_645_, 1);
v___x_654_ = lean_array_uget_borrowed(v_as_642_, v_i_643_);
v___x_655_ = l_Lean_IR_Decl_name(v___x_654_);
if (lean_obj_tag(v___x_655_) == 1)
{
lean_object* v_pre_670_; lean_object* v_str_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v_pre_670_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_pre_670_);
v_str_671_ = lean_ctor_get(v___x_655_, 1);
lean_inc_ref(v_str_671_);
v___x_672_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___closed__0));
v___x_673_ = lean_string_dec_eq(v_str_671_, v___x_672_);
lean_dec_ref(v_str_671_);
if (v___x_673_ == 0)
{
lean_dec(v_pre_670_);
lean_inc_ref(v___x_655_);
v___y_657_ = v___x_655_;
goto v___jp_656_;
}
else
{
v___y_657_ = v_pre_670_;
goto v___jp_656_;
}
}
else
{
lean_inc(v___x_655_);
v___y_657_ = v___x_655_;
goto v___jp_656_;
}
v___jp_656_:
{
uint8_t v___x_658_; 
lean_inc_ref(v___y_641_);
v___x_658_ = l_Lean_isExtern(v___y_641_, v___y_657_);
if (v___x_658_ == 0)
{
lean_dec(v___x_655_);
v___y_647_ = v_b_645_;
goto v___jp_646_;
}
else
{
lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_667_; 
lean_inc(v_snd_653_);
lean_inc(v_fst_652_);
v_isSharedCheck_667_ = !lean_is_exclusive(v_b_645_);
if (v_isSharedCheck_667_ == 0)
{
lean_object* v_unused_668_; lean_object* v_unused_669_; 
v_unused_668_ = lean_ctor_get(v_b_645_, 1);
lean_dec(v_unused_668_);
v_unused_669_ = lean_ctor_get(v_b_645_, 0);
lean_dec(v_unused_669_);
v___x_660_ = v_b_645_;
v_isShared_661_ = v_isSharedCheck_667_;
goto v_resetjp_659_;
}
else
{
lean_dec(v_b_645_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_667_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_665_; 
lean_inc_n(v___x_654_, 2);
v___x_662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_654_);
lean_ctor_set(v___x_662_, 1, v_fst_652_);
v___x_663_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_653_, v___x_655_, v___x_654_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 1, v___x_663_);
lean_ctor_set(v___x_660_, 0, v___x_662_);
v___x_665_ = v___x_660_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v___x_663_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
v___y_647_ = v___x_665_;
goto v___jp_646_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_641_);
return v_b_645_;
}
v___jp_646_:
{
size_t v___x_648_; size_t v___x_649_; 
v___x_648_ = ((size_t)1ULL);
v___x_649_ = lean_usize_add(v_i_643_, v___x_648_);
v_i_643_ = v___x_649_;
v_b_645_ = v___y_647_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object* v___y_674_, lean_object* v_as_675_, lean_object* v_i_676_, lean_object* v_stop_677_, lean_object* v_b_678_){
_start:
{
size_t v_i_boxed_679_; size_t v_stop_boxed_680_; lean_object* v_res_681_; 
v_i_boxed_679_ = lean_unbox_usize(v_i_676_);
lean_dec(v_i_676_);
v_stop_boxed_680_ = lean_unbox_usize(v_stop_677_);
lean_dec(v_stop_677_);
v_res_681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_674_, v_as_675_, v_i_boxed_679_, v_stop_boxed_680_, v_b_678_);
lean_dec_ref(v_as_675_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg(lean_object* v_as_x27_683_, lean_object* v_b_684_){
_start:
{
if (lean_obj_tag(v_as_x27_683_) == 0)
{
lean_object* v___x_686_; 
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v_b_684_);
return v___x_686_;
}
else
{
lean_object* v_head_687_; lean_object* v_tail_688_; lean_object* v_fst_689_; lean_object* v_snd_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_715_; 
v_head_687_ = lean_ctor_get(v_as_x27_683_, 0);
v_tail_688_ = lean_ctor_get(v_as_x27_683_, 1);
v_fst_689_ = lean_ctor_get(v_b_684_, 0);
v_snd_690_ = lean_ctor_get(v_b_684_, 1);
v_isSharedCheck_715_ = !lean_is_exclusive(v_b_684_);
if (v_isSharedCheck_715_ == 0)
{
v___x_692_ = v_b_684_;
v_isShared_693_ = v_isSharedCheck_715_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_snd_690_);
lean_inc(v_fst_689_);
lean_dec(v_b_684_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_715_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_694_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0));
v___x_695_ = lean_string_dec_eq(v_head_687_, v___x_694_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; 
lean_inc(v_head_687_);
v___x_696_ = l___private_LeanIR_0__setConfigOption(v_snd_690_, v_head_687_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v___x_699_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_a_697_);
lean_dec_ref(v___x_696_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v_a_697_);
v___x_699_ = v___x_692_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_fst_689_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_a_697_);
v___x_699_ = v_reuseFailAlloc_701_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
v_as_x27_683_ = v_tail_688_;
v_b_684_ = v___x_699_;
goto _start;
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_del_object(v___x_692_);
lean_dec(v_fst_689_);
v_a_702_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_696_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_696_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
else
{
lean_object* v___x_710_; lean_object* v___x_712_; 
lean_dec(v_fst_689_);
v___x_710_ = lean_box(v___x_695_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_710_);
v___x_712_ = v___x_692_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_snd_690_);
v___x_712_ = v_reuseFailAlloc_714_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
v_as_x27_683_ = v_tail_688_;
v_b_684_ = v___x_712_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(lean_object* v_as_x27_716_, lean_object* v_b_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_716_, v_b_717_);
lean_dec(v_as_x27_716_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object* v_as_720_, size_t v_i_721_, size_t v_stop_722_, lean_object* v_b_723_){
_start:
{
uint8_t v___x_724_; 
v___x_724_ = lean_usize_dec_eq(v_i_721_, v_stop_722_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v_toEnvExtension_726_; lean_object* v_asyncMode_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; size_t v___x_731_; size_t v___x_732_; 
v___x_725_ = l_Lean_Compiler_LCNF_impureSigExt;
v_toEnvExtension_726_ = lean_ctor_get(v___x_725_, 0);
v_asyncMode_727_ = lean_ctor_get(v_toEnvExtension_726_, 2);
v___x_728_ = lean_box(0);
v___x_729_ = lean_array_uget_borrowed(v_as_720_, v_i_721_);
lean_inc(v___x_729_);
v___x_730_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_725_, v_b_723_, v___x_729_, v_asyncMode_727_, v___x_728_);
v___x_731_ = ((size_t)1ULL);
v___x_732_ = lean_usize_add(v_i_721_, v___x_731_);
v_i_721_ = v___x_732_;
v_b_723_ = v___x_730_;
goto _start;
}
else
{
return v_b_723_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object* v_as_734_, lean_object* v_i_735_, lean_object* v_stop_736_, lean_object* v_b_737_){
_start:
{
size_t v_i_boxed_738_; size_t v_stop_boxed_739_; lean_object* v_res_740_; 
v_i_boxed_738_ = lean_unbox_usize(v_i_735_);
lean_dec(v_i_735_);
v_stop_boxed_739_ = lean_unbox_usize(v_stop_736_);
lean_dec(v_stop_736_);
v_res_740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_as_734_, v_i_boxed_738_, v_stop_boxed_739_, v_b_737_);
lean_dec_ref(v_as_734_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(lean_object* v_as_744_, size_t v_sz_745_, size_t v_i_746_, lean_object* v_b_747_, lean_object* v___y_748_){
_start:
{
uint8_t v___x_750_; 
v___x_750_ = lean_usize_dec_lt(v_i_746_, v_sz_745_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; 
v___x_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_751_, 0, v_b_747_);
return v___x_751_;
}
else
{
uint8_t v___x_752_; lean_object* v_a_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
lean_dec_ref(v_b_747_);
v___x_752_ = 0;
v_a_753_ = lean_array_uget_borrowed(v_as_744_, v_i_746_);
lean_inc(v_a_753_);
v___x_754_ = l_Lean_Message_toString(v_a_753_, v___x_752_);
v___x_755_ = l_IO_eprintln___at___00main_spec__6(v___x_754_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v___x_756_; size_t v___x_757_; size_t v___x_758_; 
lean_dec_ref(v___x_755_);
v___x_756_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_757_ = ((size_t)1ULL);
v___x_758_ = lean_usize_add(v_i_746_, v___x_757_);
v_i_746_ = v___x_758_;
v_b_747_ = v___x_756_;
goto _start;
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_772_; 
v_a_760_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_772_ == 0)
{
v___x_762_ = v___x_755_;
v_isShared_763_ = v_isSharedCheck_772_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_755_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_772_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v_ref_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_770_; 
v_ref_764_ = lean_ctor_get(v___y_748_, 5);
v___x_765_ = lean_io_error_to_string(v_a_760_);
v___x_766_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
v___x_767_ = l_Lean_MessageData_ofFormat(v___x_766_);
lean_inc(v_ref_764_);
v___x_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_768_, 0, v_ref_764_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v___x_768_);
v___x_770_ = v___x_762_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_768_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___boxed(lean_object* v_as_773_, lean_object* v_sz_774_, lean_object* v_i_775_, lean_object* v_b_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
size_t v_sz_boxed_779_; size_t v_i_boxed_780_; lean_object* v_res_781_; 
v_sz_boxed_779_ = lean_unbox_usize(v_sz_774_);
lean_dec(v_sz_774_);
v_i_boxed_780_ = lean_unbox_usize(v_i_775_);
lean_dec(v_i_775_);
v_res_781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_773_, v_sz_boxed_779_, v_i_boxed_780_, v_b_776_, v___y_777_);
lean_dec_ref(v___y_777_);
lean_dec_ref(v_as_773_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(lean_object* v_as_782_, size_t v_sz_783_, size_t v_i_784_, lean_object* v_b_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
uint8_t v___x_789_; 
v___x_789_ = lean_usize_dec_lt(v_i_784_, v_sz_783_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; 
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v_b_785_);
return v___x_790_;
}
else
{
uint8_t v___x_791_; lean_object* v_a_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
lean_dec_ref(v_b_785_);
v___x_791_ = 0;
v_a_792_ = lean_array_uget_borrowed(v_as_782_, v_i_784_);
lean_inc(v_a_792_);
v___x_793_ = l_Lean_Message_toString(v_a_792_, v___x_791_);
v___x_794_ = l_IO_eprintln___at___00main_spec__6(v___x_793_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v___x_795_; size_t v___x_796_; size_t v___x_797_; lean_object* v___x_798_; 
lean_dec_ref(v___x_794_);
v___x_795_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_796_ = ((size_t)1ULL);
v___x_797_ = lean_usize_add(v_i_784_, v___x_796_);
v___x_798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_782_, v_sz_783_, v___x_797_, v___x_795_, v___y_786_);
return v___x_798_;
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_811_; 
v_a_799_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_811_ == 0)
{
v___x_801_ = v___x_794_;
v_isShared_802_ = v_isSharedCheck_811_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_794_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_811_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v_ref_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_809_; 
v_ref_803_ = lean_ctor_get(v___y_786_, 5);
v___x_804_ = lean_io_error_to_string(v_a_799_);
v___x_805_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
v___x_806_ = l_Lean_MessageData_ofFormat(v___x_805_);
lean_inc(v_ref_803_);
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v_ref_803_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v___x_807_);
v___x_809_ = v___x_801_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27___boxed(lean_object* v_as_812_, lean_object* v_sz_813_, lean_object* v_i_814_, lean_object* v_b_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
size_t v_sz_boxed_819_; size_t v_i_boxed_820_; lean_object* v_res_821_; 
v_sz_boxed_819_ = lean_unbox_usize(v_sz_813_);
lean_dec(v_sz_813_);
v_i_boxed_820_ = lean_unbox_usize(v_i_814_);
lean_dec(v_i_814_);
v_res_821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(v_as_812_, v_sz_boxed_819_, v_i_boxed_820_, v_b_815_, v___y_816_, v___y_817_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec_ref(v_as_812_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(lean_object* v_as_825_, size_t v_sz_826_, size_t v_i_827_, lean_object* v_b_828_, lean_object* v___y_829_){
_start:
{
uint8_t v___x_831_; 
v___x_831_ = lean_usize_dec_lt(v_i_827_, v_sz_826_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; 
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v_b_828_);
return v___x_832_;
}
else
{
uint8_t v___x_833_; lean_object* v_a_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
lean_dec_ref(v_b_828_);
v___x_833_ = 0;
v_a_834_ = lean_array_uget_borrowed(v_as_825_, v_i_827_);
lean_inc(v_a_834_);
v___x_835_ = l_Lean_Message_toString(v_a_834_, v___x_833_);
v___x_836_ = l_IO_eprintln___at___00main_spec__6(v___x_835_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v___x_837_; size_t v___x_838_; size_t v___x_839_; 
lean_dec_ref(v___x_836_);
v___x_837_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_838_ = ((size_t)1ULL);
v___x_839_ = lean_usize_add(v_i_827_, v___x_838_);
v_i_827_ = v___x_839_;
v_b_828_ = v___x_837_;
goto _start;
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
v_ref_845_ = lean_ctor_get(v___y_829_, 5);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___boxed(lean_object* v_as_854_, lean_object* v_sz_855_, lean_object* v_i_856_, lean_object* v_b_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
size_t v_sz_boxed_860_; size_t v_i_boxed_861_; lean_object* v_res_862_; 
v_sz_boxed_860_ = lean_unbox_usize(v_sz_855_);
lean_dec(v_sz_855_);
v_i_boxed_861_ = lean_unbox_usize(v_i_856_);
lean_dec(v_i_856_);
v_res_862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_854_, v_sz_boxed_860_, v_i_boxed_861_, v_b_857_, v___y_858_);
lean_dec_ref(v___y_858_);
lean_dec_ref(v_as_854_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(lean_object* v_as_863_, size_t v_sz_864_, size_t v_i_865_, lean_object* v_b_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
uint8_t v___x_870_; 
v___x_870_ = lean_usize_dec_lt(v_i_865_, v_sz_864_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; 
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v_b_866_);
return v___x_871_;
}
else
{
uint8_t v___x_872_; lean_object* v_a_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
lean_dec_ref(v_b_866_);
v___x_872_ = 0;
v_a_873_ = lean_array_uget_borrowed(v_as_863_, v_i_865_);
lean_inc(v_a_873_);
v___x_874_ = l_Lean_Message_toString(v_a_873_, v___x_872_);
v___x_875_ = l_IO_eprintln___at___00main_spec__6(v___x_874_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v___x_876_; size_t v___x_877_; size_t v___x_878_; lean_object* v___x_879_; 
lean_dec_ref(v___x_875_);
v___x_876_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_877_ = ((size_t)1ULL);
v___x_878_ = lean_usize_add(v_i_865_, v___x_877_);
v___x_879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_863_, v_sz_864_, v___x_878_, v___x_876_, v___y_867_);
return v___x_879_;
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_892_; 
v_a_880_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_892_ == 0)
{
v___x_882_ = v___x_875_;
v_isShared_883_ = v_isSharedCheck_892_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_875_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_892_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v_ref_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
v_ref_884_ = lean_ctor_get(v___y_867_, 5);
v___x_885_ = lean_io_error_to_string(v_a_880_);
v___x_886_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
v___x_887_ = l_Lean_MessageData_ofFormat(v___x_886_);
lean_inc(v_ref_884_);
v___x_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_888_, 0, v_ref_884_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_888_);
v___x_890_ = v___x_882_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38___boxed(lean_object* v_as_893_, lean_object* v_sz_894_, lean_object* v_i_895_, lean_object* v_b_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
size_t v_sz_boxed_900_; size_t v_i_boxed_901_; lean_object* v_res_902_; 
v_sz_boxed_900_ = lean_unbox_usize(v_sz_894_);
lean_dec(v_sz_894_);
v_i_boxed_901_ = lean_unbox_usize(v_i_895_);
lean_dec(v_i_895_);
v_res_902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(v_as_893_, v_sz_boxed_900_, v_i_boxed_901_, v_b_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec_ref(v_as_893_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(lean_object* v_init_903_, lean_object* v_n_904_, lean_object* v_b_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
if (lean_obj_tag(v_n_904_) == 0)
{
lean_object* v_cs_909_; lean_object* v___x_910_; lean_object* v___x_911_; size_t v_sz_912_; size_t v___x_913_; lean_object* v___x_914_; 
v_cs_909_ = lean_ctor_get(v_n_904_, 0);
v___x_910_ = lean_box(0);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
lean_ctor_set(v___x_911_, 1, v_b_905_);
v_sz_912_ = lean_array_size(v_cs_909_);
v___x_913_ = ((size_t)0ULL);
v___x_914_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_init_903_, v_cs_909_, v_sz_912_, v___x_913_, v___x_911_, v___y_906_, v___y_907_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_929_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_929_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_929_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_929_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v_fst_919_; 
v_fst_919_ = lean_ctor_get(v_a_915_, 0);
if (lean_obj_tag(v_fst_919_) == 0)
{
lean_object* v_snd_920_; lean_object* v___x_921_; lean_object* v___x_923_; 
v_snd_920_ = lean_ctor_get(v_a_915_, 1);
lean_inc(v_snd_920_);
lean_dec(v_a_915_);
v___x_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_921_, 0, v_snd_920_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_921_);
v___x_923_ = v___x_917_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
else
{
lean_object* v_val_925_; lean_object* v___x_927_; 
lean_inc_ref(v_fst_919_);
lean_dec(v_a_915_);
v_val_925_ = lean_ctor_get(v_fst_919_, 0);
lean_inc(v_val_925_);
lean_dec_ref(v_fst_919_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v_val_925_);
v___x_927_ = v___x_917_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_val_925_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
v_a_930_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_914_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_914_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
else
{
lean_object* v_vs_938_; lean_object* v___x_939_; lean_object* v___x_940_; size_t v_sz_941_; size_t v___x_942_; lean_object* v___x_943_; 
v_vs_938_ = lean_ctor_get(v_n_904_, 0);
v___x_939_ = lean_box(0);
v___x_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
lean_ctor_set(v___x_940_, 1, v_b_905_);
v_sz_941_ = lean_array_size(v_vs_938_);
v___x_942_ = ((size_t)0ULL);
v___x_943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(v_vs_938_, v_sz_941_, v___x_942_, v___x_940_, v___y_906_, v___y_907_);
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
lean_dec_ref(v_fst_948_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(lean_object* v_init_967_, lean_object* v_as_968_, size_t v_sz_969_, size_t v_i_970_, lean_object* v_b_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
uint8_t v___x_975_; 
v___x_975_ = lean_usize_dec_lt(v_i_970_, v_sz_969_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; 
v___x_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_976_, 0, v_b_971_);
return v___x_976_;
}
else
{
lean_object* v_snd_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_1011_; 
v_snd_977_ = lean_ctor_get(v_b_971_, 1);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_b_971_);
if (v_isSharedCheck_1011_ == 0)
{
lean_object* v_unused_1012_; 
v_unused_1012_ = lean_ctor_get(v_b_971_, 0);
lean_dec(v_unused_1012_);
v___x_979_ = v_b_971_;
v_isShared_980_ = v_isSharedCheck_1011_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_snd_977_);
lean_dec(v_b_971_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_1011_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v_a_981_; lean_object* v___x_982_; 
v_a_981_ = lean_array_uget_borrowed(v_as_968_, v_i_970_);
lean_inc(v_snd_977_);
v___x_982_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_967_, v_a_981_, v_snd_977_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1002_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_985_ = v___x_982_;
v_isShared_986_ = v_isSharedCheck_1002_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_982_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1002_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
if (lean_obj_tag(v_a_983_) == 0)
{
lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_987_, 0, v_a_983_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v___x_987_);
v___x_989_ = v___x_979_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_987_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_snd_977_);
v___x_989_ = v_reuseFailAlloc_993_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_991_; 
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 0, v___x_989_);
v___x_991_ = v___x_985_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
else
{
lean_object* v_a_994_; lean_object* v___x_995_; lean_object* v___x_997_; 
lean_del_object(v___x_985_);
lean_dec(v_snd_977_);
v_a_994_ = lean_ctor_get(v_a_983_, 0);
lean_inc(v_a_994_);
lean_dec_ref(v_a_983_);
v___x_995_ = lean_box(0);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 1, v_a_994_);
lean_ctor_set(v___x_979_, 0, v___x_995_);
v___x_997_ = v___x_979_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_a_994_);
v___x_997_ = v_reuseFailAlloc_1001_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
size_t v___x_998_; size_t v___x_999_; 
v___x_998_ = ((size_t)1ULL);
v___x_999_ = lean_usize_add(v_i_970_, v___x_998_);
v_i_970_ = v___x_999_;
v_b_971_ = v___x_997_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_del_object(v___x_979_);
lean_dec(v_snd_977_);
v_a_1003_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_982_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_982_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37___boxed(lean_object* v_init_1013_, lean_object* v_as_1014_, lean_object* v_sz_1015_, lean_object* v_i_1016_, lean_object* v_b_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
size_t v_sz_boxed_1021_; size_t v_i_boxed_1022_; lean_object* v_res_1023_; 
v_sz_boxed_1021_ = lean_unbox_usize(v_sz_1015_);
lean_dec(v_sz_1015_);
v_i_boxed_1022_ = lean_unbox_usize(v_i_1016_);
lean_dec(v_i_1016_);
v_res_1023_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_init_1013_, v_as_1014_, v_sz_boxed_1021_, v_i_boxed_1022_, v_b_1017_, v___y_1018_, v___y_1019_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec_ref(v_as_1014_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26___boxed(lean_object* v_init_1024_, lean_object* v_n_1025_, lean_object* v_b_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1024_, v_n_1025_, v_b_1026_, v___y_1027_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec_ref(v_n_1025_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12(lean_object* v_t_1031_, lean_object* v_init_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_root_1036_; lean_object* v_tail_1037_; lean_object* v___x_1038_; 
v_root_1036_ = lean_ctor_get(v_t_1031_, 0);
v_tail_1037_ = lean_ctor_get(v_t_1031_, 1);
v___x_1038_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1032_, v_root_1036_, v_init_1032_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1075_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1041_ = v___x_1038_;
v_isShared_1042_ = v_isSharedCheck_1075_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1038_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1075_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
if (lean_obj_tag(v_a_1039_) == 0)
{
lean_object* v_a_1043_; lean_object* v___x_1045_; 
v_a_1043_ = lean_ctor_get(v_a_1039_, 0);
lean_inc(v_a_1043_);
lean_dec_ref(v_a_1039_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v_a_1043_);
v___x_1045_ = v___x_1041_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1043_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; size_t v_sz_1050_; size_t v___x_1051_; lean_object* v___x_1052_; 
lean_del_object(v___x_1041_);
v_a_1047_ = lean_ctor_get(v_a_1039_, 0);
lean_inc(v_a_1047_);
lean_dec_ref(v_a_1039_);
v___x_1048_ = lean_box(0);
v___x_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
lean_ctor_set(v___x_1049_, 1, v_a_1047_);
v_sz_1050_ = lean_array_size(v_tail_1037_);
v___x_1051_ = ((size_t)0ULL);
v___x_1052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(v_tail_1037_, v_sz_1050_, v___x_1051_, v___x_1049_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1066_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1055_ = v___x_1052_;
v_isShared_1056_ = v_isSharedCheck_1066_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1052_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1066_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v_fst_1057_; 
v_fst_1057_ = lean_ctor_get(v_a_1053_, 0);
if (lean_obj_tag(v_fst_1057_) == 0)
{
lean_object* v_snd_1058_; lean_object* v___x_1060_; 
v_snd_1058_ = lean_ctor_get(v_a_1053_, 1);
lean_inc(v_snd_1058_);
lean_dec(v_a_1053_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v_snd_1058_);
v___x_1060_ = v___x_1055_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_snd_1058_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
else
{
lean_object* v_val_1062_; lean_object* v___x_1064_; 
lean_inc_ref(v_fst_1057_);
lean_dec(v_a_1053_);
v_val_1062_ = lean_ctor_get(v_fst_1057_, 0);
lean_inc(v_val_1062_);
lean_dec_ref(v_fst_1057_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v_val_1062_);
v___x_1064_ = v___x_1055_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_val_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
v_a_1067_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_1052_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1052_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
v_a_1076_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1038_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1038_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12___boxed(lean_object* v_t_1084_, lean_object* v_init_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(v_t_1084_, v_init_1085_, v___y_1086_, v___y_1087_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec_ref(v_t_1084_);
return v_res_1089_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(uint8_t v___x_1097_, uint8_t v_suppressElabErrors_1098_, lean_object* v___x_1099_, lean_object* v_x_1100_){
_start:
{
if (lean_obj_tag(v_x_1100_) == 1)
{
lean_object* v_pre_1101_; 
v_pre_1101_ = lean_ctor_get(v_x_1100_, 0);
switch(lean_obj_tag(v_pre_1101_))
{
case 1:
{
lean_object* v_pre_1102_; 
v_pre_1102_ = lean_ctor_get(v_pre_1101_, 0);
switch(lean_obj_tag(v_pre_1102_))
{
case 0:
{
lean_object* v_str_1103_; lean_object* v_str_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; 
v_str_1103_ = lean_ctor_get(v_x_1100_, 1);
v_str_1104_ = lean_ctor_get(v_pre_1101_, 1);
v___x_1105_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0));
v___x_1106_ = lean_string_dec_eq(v_str_1104_, v___x_1105_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1107_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1));
v___x_1108_ = lean_string_dec_eq(v_str_1104_, v___x_1107_);
if (v___x_1108_ == 0)
{
return v___x_1097_;
}
else
{
lean_object* v___x_1109_; uint8_t v___x_1110_; 
v___x_1109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2));
v___x_1110_ = lean_string_dec_eq(v_str_1103_, v___x_1109_);
if (v___x_1110_ == 0)
{
return v___x_1097_;
}
else
{
return v_suppressElabErrors_1098_;
}
}
}
else
{
lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3));
v___x_1112_ = lean_string_dec_eq(v_str_1103_, v___x_1111_);
if (v___x_1112_ == 0)
{
return v___x_1097_;
}
else
{
return v_suppressElabErrors_1098_;
}
}
}
case 1:
{
lean_object* v_pre_1113_; 
v_pre_1113_ = lean_ctor_get(v_pre_1102_, 0);
if (lean_obj_tag(v_pre_1113_) == 0)
{
lean_object* v_str_1114_; lean_object* v_str_1115_; lean_object* v_str_1116_; lean_object* v___x_1117_; uint8_t v___x_1118_; 
v_str_1114_ = lean_ctor_get(v_x_1100_, 1);
v_str_1115_ = lean_ctor_get(v_pre_1101_, 1);
v_str_1116_ = lean_ctor_get(v_pre_1102_, 1);
v___x_1117_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4));
v___x_1118_ = lean_string_dec_eq(v_str_1116_, v___x_1117_);
if (v___x_1118_ == 0)
{
return v___x_1097_;
}
else
{
lean_object* v___x_1119_; uint8_t v___x_1120_; 
v___x_1119_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5));
v___x_1120_ = lean_string_dec_eq(v_str_1115_, v___x_1119_);
if (v___x_1120_ == 0)
{
return v___x_1097_;
}
else
{
lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1121_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6));
v___x_1122_ = lean_string_dec_eq(v_str_1114_, v___x_1121_);
if (v___x_1122_ == 0)
{
return v___x_1097_;
}
else
{
return v_suppressElabErrors_1098_;
}
}
}
}
else
{
return v___x_1097_;
}
}
default: 
{
return v___x_1097_;
}
}
}
case 0:
{
lean_object* v_str_1123_; uint8_t v___x_1124_; 
v_str_1123_ = lean_ctor_get(v_x_1100_, 1);
v___x_1124_ = lean_string_dec_eq(v_str_1123_, v___x_1099_);
if (v___x_1124_ == 0)
{
return v___x_1097_;
}
else
{
return v_suppressElabErrors_1098_;
}
}
default: 
{
return v___x_1097_;
}
}
}
else
{
return v___x_1097_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed(lean_object* v___x_1125_, lean_object* v_suppressElabErrors_1126_, lean_object* v___x_1127_, lean_object* v_x_1128_){
_start:
{
uint8_t v___x_37336__boxed_1129_; uint8_t v_suppressElabErrors_boxed_1130_; uint8_t v_res_1131_; lean_object* v_r_1132_; 
v___x_37336__boxed_1129_ = lean_unbox(v___x_1125_);
v_suppressElabErrors_boxed_1130_ = lean_unbox(v_suppressElabErrors_1126_);
v_res_1131_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(v___x_37336__boxed_1129_, v_suppressElabErrors_boxed_1130_, v___x_1127_, v_x_1128_);
lean_dec(v_x_1128_);
lean_dec_ref(v___x_1127_);
v_r_1132_ = lean_box(v_res_1131_);
return v_r_1132_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0(void){
_start:
{
lean_object* v___x_1133_; double v___x_1134_; 
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = lean_float_of_nat(v___x_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(uint8_t v___x_1136_, lean_object* v_as_1137_, size_t v_sz_1138_, size_t v_i_1139_, lean_object* v_b_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_a_1145_; uint8_t v___x_1149_; 
v___x_1149_ = lean_usize_dec_lt(v_i_1139_, v_sz_1138_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; 
v___x_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1150_, 0, v_b_1140_);
return v___x_1150_;
}
else
{
lean_object* v_a_1151_; lean_object* v_fst_1152_; lean_object* v_snd_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1230_; 
v_a_1151_ = lean_array_uget(v_as_1137_, v_i_1139_);
v_fst_1152_ = lean_ctor_get(v_a_1151_, 0);
v_snd_1153_ = lean_ctor_get(v_a_1151_, 1);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_a_1151_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1155_ = v_a_1151_;
v_isShared_1156_ = v_isSharedCheck_1230_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_snd_1153_);
lean_inc(v_fst_1152_);
lean_dec(v_a_1151_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1230_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v_fst_1157_; lean_object* v_snd_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1229_; 
v_fst_1157_ = lean_ctor_get(v_fst_1152_, 0);
v_snd_1158_ = lean_ctor_get(v_fst_1152_, 1);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_fst_1152_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1160_ = v_fst_1152_;
v_isShared_1161_ = v_isSharedCheck_1229_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_snd_1158_);
lean_inc(v_fst_1157_);
lean_dec(v_fst_1152_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1229_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; double v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v_fileName_1167_; lean_object* v_fileMap_1168_; uint8_t v_suppressElabErrors_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1176_; 
v___x_1162_ = lean_box(0);
v___x_1163_ = lean_box(0);
v___x_1164_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0);
v___x_1165_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1));
v___x_1166_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1166_, 0, v___x_1162_);
lean_ctor_set(v___x_1166_, 1, v___x_1163_);
lean_ctor_set(v___x_1166_, 2, v___x_1165_);
lean_ctor_set_float(v___x_1166_, sizeof(void*)*3, v___x_1164_);
lean_ctor_set_float(v___x_1166_, sizeof(void*)*3 + 8, v___x_1164_);
lean_ctor_set_uint8(v___x_1166_, sizeof(void*)*3 + 16, v___x_1149_);
v_fileName_1167_ = lean_ctor_get(v___y_1141_, 0);
v_fileMap_1168_ = lean_ctor_get(v___y_1141_, 1);
v_suppressElabErrors_1169_ = lean_ctor_get_uint8(v___y_1141_, sizeof(void*)*14 + 1);
v___x_1170_ = lean_box(0);
v___x_1171_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_1172_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_1173_ = l_Lean_MessageData_nil;
v___x_1174_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1166_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
lean_ctor_set(v___x_1174_, 2, v_snd_1153_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set_tag(v___x_1160_, 8);
lean_ctor_set(v___x_1160_, 1, v___x_1174_);
lean_ctor_set(v___x_1160_, 0, v___x_1172_);
v___x_1176_ = v___x_1160_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1172_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v___x_1174_);
v___x_1176_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
uint8_t v___x_1177_; lean_object* v___x_1178_; lean_object* v___y_1180_; lean_object* v___y_1181_; 
v___x_1177_ = 0;
lean_inc_ref(v_fileMap_1168_);
lean_inc_ref(v_fileName_1167_);
v___x_1178_ = l_Lean_Elab_mkMessageCore(v_fileName_1167_, v_fileMap_1168_, v___x_1176_, v___x_1177_, v_fst_1157_, v_snd_1158_);
lean_dec(v_snd_1158_);
lean_dec(v_fst_1157_);
if (v_suppressElabErrors_1169_ == 0)
{
v___y_1180_ = v___y_1141_;
v___y_1181_ = v___y_1142_;
goto v___jp_1179_;
}
else
{
lean_object* v_data_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___f_1226_; uint8_t v___x_1227_; 
v_data_1223_ = lean_ctor_get(v___x_1178_, 4);
lean_inc(v_data_1223_);
v___x_1224_ = lean_box(v___x_1136_);
v___x_1225_ = lean_box(v_suppressElabErrors_1169_);
v___f_1226_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1226_, 0, v___x_1224_);
lean_closure_set(v___f_1226_, 1, v___x_1225_);
lean_closure_set(v___f_1226_, 2, v___x_1171_);
v___x_1227_ = l_Lean_MessageData_hasTag(v___f_1226_, v_data_1223_);
if (v___x_1227_ == 0)
{
lean_dec_ref(v___x_1178_);
lean_del_object(v___x_1155_);
v_a_1145_ = v___x_1170_;
goto v___jp_1144_;
}
else
{
v___y_1180_ = v___y_1141_;
v___y_1181_ = v___y_1142_;
goto v___jp_1179_;
}
}
v___jp_1179_:
{
lean_object* v___x_1182_; lean_object* v_fileName_1183_; lean_object* v_pos_1184_; lean_object* v_endPos_1185_; uint8_t v_keepFullRange_1186_; uint8_t v_severity_1187_; uint8_t v_isSilent_1188_; lean_object* v_caption_1189_; lean_object* v_data_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1222_; 
v___x_1182_ = lean_st_ref_take(v___y_1181_);
v_fileName_1183_ = lean_ctor_get(v___x_1178_, 0);
v_pos_1184_ = lean_ctor_get(v___x_1178_, 1);
v_endPos_1185_ = lean_ctor_get(v___x_1178_, 2);
v_keepFullRange_1186_ = lean_ctor_get_uint8(v___x_1178_, sizeof(void*)*5);
v_severity_1187_ = lean_ctor_get_uint8(v___x_1178_, sizeof(void*)*5 + 1);
v_isSilent_1188_ = lean_ctor_get_uint8(v___x_1178_, sizeof(void*)*5 + 2);
v_caption_1189_ = lean_ctor_get(v___x_1178_, 3);
v_data_1190_ = lean_ctor_get(v___x_1178_, 4);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1192_ = v___x_1178_;
v_isShared_1193_ = v_isSharedCheck_1222_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_data_1190_);
lean_inc(v_caption_1189_);
lean_inc(v_endPos_1185_);
lean_inc(v_pos_1184_);
lean_inc(v_fileName_1183_);
lean_dec(v___x_1178_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1222_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v_currNamespace_1194_; lean_object* v_openDecls_1195_; lean_object* v_env_1196_; lean_object* v_nextMacroScope_1197_; lean_object* v_ngen_1198_; lean_object* v_auxDeclNGen_1199_; lean_object* v_traceState_1200_; lean_object* v_cache_1201_; lean_object* v_messages_1202_; lean_object* v_infoState_1203_; lean_object* v_snapshotTasks_1204_; lean_object* v_newDecls_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1221_; 
v_currNamespace_1194_ = lean_ctor_get(v___y_1180_, 6);
v_openDecls_1195_ = lean_ctor_get(v___y_1180_, 7);
v_env_1196_ = lean_ctor_get(v___x_1182_, 0);
v_nextMacroScope_1197_ = lean_ctor_get(v___x_1182_, 1);
v_ngen_1198_ = lean_ctor_get(v___x_1182_, 2);
v_auxDeclNGen_1199_ = lean_ctor_get(v___x_1182_, 3);
v_traceState_1200_ = lean_ctor_get(v___x_1182_, 4);
v_cache_1201_ = lean_ctor_get(v___x_1182_, 5);
v_messages_1202_ = lean_ctor_get(v___x_1182_, 6);
v_infoState_1203_ = lean_ctor_get(v___x_1182_, 7);
v_snapshotTasks_1204_ = lean_ctor_get(v___x_1182_, 8);
v_newDecls_1205_ = lean_ctor_get(v___x_1182_, 9);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1207_ = v___x_1182_;
v_isShared_1208_ = v_isSharedCheck_1221_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_newDecls_1205_);
lean_inc(v_snapshotTasks_1204_);
lean_inc(v_infoState_1203_);
lean_inc(v_messages_1202_);
lean_inc(v_cache_1201_);
lean_inc(v_traceState_1200_);
lean_inc(v_auxDeclNGen_1199_);
lean_inc(v_ngen_1198_);
lean_inc(v_nextMacroScope_1197_);
lean_inc(v_env_1196_);
lean_dec(v___x_1182_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1221_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
lean_inc(v_openDecls_1195_);
lean_inc(v_currNamespace_1194_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 1, v_openDecls_1195_);
lean_ctor_set(v___x_1155_, 0, v_currNamespace_1194_);
v___x_1210_ = v___x_1155_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_currNamespace_1194_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_openDecls_1195_);
v___x_1210_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
lean_object* v___x_1211_; lean_object* v___x_1213_; 
v___x_1211_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
lean_ctor_set(v___x_1211_, 1, v_data_1190_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 4, v___x_1211_);
v___x_1213_ = v___x_1192_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_fileName_1183_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_pos_1184_);
lean_ctor_set(v_reuseFailAlloc_1219_, 2, v_endPos_1185_);
lean_ctor_set(v_reuseFailAlloc_1219_, 3, v_caption_1189_);
lean_ctor_set(v_reuseFailAlloc_1219_, 4, v___x_1211_);
lean_ctor_set_uint8(v_reuseFailAlloc_1219_, sizeof(void*)*5, v_keepFullRange_1186_);
lean_ctor_set_uint8(v_reuseFailAlloc_1219_, sizeof(void*)*5 + 1, v_severity_1187_);
lean_ctor_set_uint8(v_reuseFailAlloc_1219_, sizeof(void*)*5 + 2, v_isSilent_1188_);
v___x_1213_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
lean_object* v___x_1214_; lean_object* v___x_1216_; 
v___x_1214_ = l_Lean_MessageLog_add(v___x_1213_, v_messages_1202_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 6, v___x_1214_);
v___x_1216_ = v___x_1207_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_env_1196_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v_nextMacroScope_1197_);
lean_ctor_set(v_reuseFailAlloc_1218_, 2, v_ngen_1198_);
lean_ctor_set(v_reuseFailAlloc_1218_, 3, v_auxDeclNGen_1199_);
lean_ctor_set(v_reuseFailAlloc_1218_, 4, v_traceState_1200_);
lean_ctor_set(v_reuseFailAlloc_1218_, 5, v_cache_1201_);
lean_ctor_set(v_reuseFailAlloc_1218_, 6, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1218_, 7, v_infoState_1203_);
lean_ctor_set(v_reuseFailAlloc_1218_, 8, v_snapshotTasks_1204_);
lean_ctor_set(v_reuseFailAlloc_1218_, 9, v_newDecls_1205_);
v___x_1216_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_st_ref_set(v___y_1181_, v___x_1216_);
v_a_1145_ = v___x_1170_;
goto v___jp_1144_;
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
v___jp_1144_:
{
size_t v___x_1146_; size_t v___x_1147_; 
v___x_1146_ = ((size_t)1ULL);
v___x_1147_ = lean_usize_add(v_i_1139_, v___x_1146_);
v_i_1139_ = v___x_1147_;
v_b_1140_ = v_a_1145_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___boxed(lean_object* v___x_1231_, lean_object* v_as_1232_, lean_object* v_sz_1233_, lean_object* v_i_1234_, lean_object* v_b_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
uint8_t v___x_37409__boxed_1239_; size_t v_sz_boxed_1240_; size_t v_i_boxed_1241_; lean_object* v_res_1242_; 
v___x_37409__boxed_1239_ = lean_unbox(v___x_1231_);
v_sz_boxed_1240_ = lean_unbox_usize(v_sz_1233_);
lean_dec(v_sz_1233_);
v_i_boxed_1241_ = lean_unbox_usize(v_i_1234_);
lean_dec(v_i_1234_);
v_res_1242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_37409__boxed_1239_, v_as_1232_, v_sz_boxed_1240_, v_i_boxed_1241_, v_b_1235_, v___y_1236_, v___y_1237_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec_ref(v_as_1232_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(lean_object* v_opts_1243_, lean_object* v_opt_1244_){
_start:
{
lean_object* v_name_1245_; lean_object* v_map_1246_; lean_object* v___x_1247_; 
v_name_1245_ = lean_ctor_get(v_opt_1244_, 0);
v_map_1246_ = lean_ctor_get(v_opts_1243_, 0);
v___x_1247_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1246_, v_name_1245_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v___x_1248_; 
v___x_1248_ = lean_box(0);
return v___x_1248_;
}
else
{
lean_object* v_val_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1258_; 
v_val_1249_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1251_ = v___x_1247_;
v_isShared_1252_ = v_isSharedCheck_1258_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_val_1249_);
lean_dec(v___x_1247_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1258_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
if (lean_obj_tag(v_val_1249_) == 0)
{
lean_object* v_v_1253_; lean_object* v___x_1255_; 
v_v_1253_ = lean_ctor_get(v_val_1249_, 0);
lean_inc_ref(v_v_1253_);
lean_dec_ref(v_val_1249_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v_v_1253_);
v___x_1255_ = v___x_1251_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_v_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
else
{
lean_object* v___x_1257_; 
lean_del_object(v___x_1251_);
lean_dec(v_val_1249_);
v___x_1257_ = lean_box(0);
return v___x_1257_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15___boxed(lean_object* v_opts_1259_, lean_object* v_opt_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(v_opts_1259_, v_opt_1260_);
lean_dec_ref(v_opt_1260_);
lean_dec_ref(v_opts_1259_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(lean_object* v_a_1262_, lean_object* v_fallback_1263_, lean_object* v_x_1264_){
_start:
{
if (lean_obj_tag(v_x_1264_) == 0)
{
lean_inc(v_fallback_1263_);
return v_fallback_1263_;
}
else
{
lean_object* v_key_1265_; lean_object* v_value_1266_; lean_object* v_tail_1267_; uint8_t v___y_1269_; lean_object* v_fst_1271_; lean_object* v_snd_1272_; lean_object* v_fst_1273_; lean_object* v_snd_1274_; uint8_t v___x_1275_; 
v_key_1265_ = lean_ctor_get(v_x_1264_, 0);
v_value_1266_ = lean_ctor_get(v_x_1264_, 1);
v_tail_1267_ = lean_ctor_get(v_x_1264_, 2);
v_fst_1271_ = lean_ctor_get(v_key_1265_, 0);
v_snd_1272_ = lean_ctor_get(v_key_1265_, 1);
v_fst_1273_ = lean_ctor_get(v_a_1262_, 0);
v_snd_1274_ = lean_ctor_get(v_a_1262_, 1);
v___x_1275_ = lean_nat_dec_eq(v_fst_1271_, v_fst_1273_);
if (v___x_1275_ == 0)
{
v___y_1269_ = v___x_1275_;
goto v___jp_1268_;
}
else
{
uint8_t v___x_1276_; 
v___x_1276_ = lean_nat_dec_eq(v_snd_1272_, v_snd_1274_);
v___y_1269_ = v___x_1276_;
goto v___jp_1268_;
}
v___jp_1268_:
{
if (v___y_1269_ == 0)
{
v_x_1264_ = v_tail_1267_;
goto _start;
}
else
{
lean_inc(v_value_1266_);
return v_value_1266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg___boxed(lean_object* v_a_1277_, lean_object* v_fallback_1278_, lean_object* v_x_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_1277_, v_fallback_1278_, v_x_1279_);
lean_dec(v_x_1279_);
lean_dec(v_fallback_1278_);
lean_dec_ref(v_a_1277_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(lean_object* v_m_1281_, lean_object* v_a_1282_, lean_object* v_fallback_1283_){
_start:
{
lean_object* v_buckets_1284_; lean_object* v_fst_1285_; lean_object* v_snd_1286_; lean_object* v___x_1287_; uint64_t v___x_1288_; uint64_t v___x_1289_; uint64_t v___x_1290_; uint64_t v___x_1291_; uint64_t v___x_1292_; uint64_t v_fold_1293_; uint64_t v___x_1294_; uint64_t v___x_1295_; uint64_t v___x_1296_; size_t v___x_1297_; size_t v___x_1298_; size_t v___x_1299_; size_t v___x_1300_; size_t v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v_buckets_1284_ = lean_ctor_get(v_m_1281_, 1);
v_fst_1285_ = lean_ctor_get(v_a_1282_, 0);
v_snd_1286_ = lean_ctor_get(v_a_1282_, 1);
v___x_1287_ = lean_array_get_size(v_buckets_1284_);
v___x_1288_ = l_String_instHashableRaw_hash(v_fst_1285_);
v___x_1289_ = l_String_instHashableRaw_hash(v_snd_1286_);
v___x_1290_ = lean_uint64_mix_hash(v___x_1288_, v___x_1289_);
v___x_1291_ = 32ULL;
v___x_1292_ = lean_uint64_shift_right(v___x_1290_, v___x_1291_);
v_fold_1293_ = lean_uint64_xor(v___x_1290_, v___x_1292_);
v___x_1294_ = 16ULL;
v___x_1295_ = lean_uint64_shift_right(v_fold_1293_, v___x_1294_);
v___x_1296_ = lean_uint64_xor(v_fold_1293_, v___x_1295_);
v___x_1297_ = lean_uint64_to_usize(v___x_1296_);
v___x_1298_ = lean_usize_of_nat(v___x_1287_);
v___x_1299_ = ((size_t)1ULL);
v___x_1300_ = lean_usize_sub(v___x_1298_, v___x_1299_);
v___x_1301_ = lean_usize_land(v___x_1297_, v___x_1300_);
v___x_1302_ = lean_array_uget_borrowed(v_buckets_1284_, v___x_1301_);
v___x_1303_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_1282_, v_fallback_1283_, v___x_1302_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg___boxed(lean_object* v_m_1304_, lean_object* v_a_1305_, lean_object* v_fallback_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_1304_, v_a_1305_, v_fallback_1306_);
lean_dec(v_fallback_1306_);
lean_dec_ref(v_a_1305_);
lean_dec_ref(v_m_1304_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(lean_object* v_x_1308_, lean_object* v_x_1309_){
_start:
{
if (lean_obj_tag(v_x_1309_) == 0)
{
return v_x_1308_;
}
else
{
lean_object* v_key_1310_; lean_object* v_value_1311_; lean_object* v_tail_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1339_; 
v_key_1310_ = lean_ctor_get(v_x_1309_, 0);
v_value_1311_ = lean_ctor_get(v_x_1309_, 1);
v_tail_1312_ = lean_ctor_get(v_x_1309_, 2);
v_isSharedCheck_1339_ = !lean_is_exclusive(v_x_1309_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1314_ = v_x_1309_;
v_isShared_1315_ = v_isSharedCheck_1339_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_tail_1312_);
lean_inc(v_value_1311_);
lean_inc(v_key_1310_);
lean_dec(v_x_1309_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1339_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v_fst_1316_; lean_object* v_snd_1317_; lean_object* v___x_1318_; uint64_t v___x_1319_; uint64_t v___x_1320_; uint64_t v___x_1321_; uint64_t v___x_1322_; uint64_t v___x_1323_; uint64_t v_fold_1324_; uint64_t v___x_1325_; uint64_t v___x_1326_; uint64_t v___x_1327_; size_t v___x_1328_; size_t v___x_1329_; size_t v___x_1330_; size_t v___x_1331_; size_t v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1335_; 
v_fst_1316_ = lean_ctor_get(v_key_1310_, 0);
v_snd_1317_ = lean_ctor_get(v_key_1310_, 1);
v___x_1318_ = lean_array_get_size(v_x_1308_);
v___x_1319_ = l_String_instHashableRaw_hash(v_fst_1316_);
v___x_1320_ = l_String_instHashableRaw_hash(v_snd_1317_);
v___x_1321_ = lean_uint64_mix_hash(v___x_1319_, v___x_1320_);
v___x_1322_ = 32ULL;
v___x_1323_ = lean_uint64_shift_right(v___x_1321_, v___x_1322_);
v_fold_1324_ = lean_uint64_xor(v___x_1321_, v___x_1323_);
v___x_1325_ = 16ULL;
v___x_1326_ = lean_uint64_shift_right(v_fold_1324_, v___x_1325_);
v___x_1327_ = lean_uint64_xor(v_fold_1324_, v___x_1326_);
v___x_1328_ = lean_uint64_to_usize(v___x_1327_);
v___x_1329_ = lean_usize_of_nat(v___x_1318_);
v___x_1330_ = ((size_t)1ULL);
v___x_1331_ = lean_usize_sub(v___x_1329_, v___x_1330_);
v___x_1332_ = lean_usize_land(v___x_1328_, v___x_1331_);
v___x_1333_ = lean_array_uget_borrowed(v_x_1308_, v___x_1332_);
lean_inc(v___x_1333_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 2, v___x_1333_);
v___x_1335_ = v___x_1314_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_key_1310_);
lean_ctor_set(v_reuseFailAlloc_1338_, 1, v_value_1311_);
lean_ctor_set(v_reuseFailAlloc_1338_, 2, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
lean_object* v___x_1336_; 
v___x_1336_ = lean_array_uset(v_x_1308_, v___x_1332_, v___x_1335_);
v_x_1308_ = v___x_1336_;
v_x_1309_ = v_tail_1312_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(lean_object* v_i_1340_, lean_object* v_source_1341_, lean_object* v_target_1342_){
_start:
{
lean_object* v___x_1343_; uint8_t v___x_1344_; 
v___x_1343_ = lean_array_get_size(v_source_1341_);
v___x_1344_ = lean_nat_dec_lt(v_i_1340_, v___x_1343_);
if (v___x_1344_ == 0)
{
lean_dec_ref(v_source_1341_);
lean_dec(v_i_1340_);
return v_target_1342_;
}
else
{
lean_object* v_es_1345_; lean_object* v___x_1346_; lean_object* v_source_1347_; lean_object* v_target_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v_es_1345_ = lean_array_fget(v_source_1341_, v_i_1340_);
v___x_1346_ = lean_box(0);
v_source_1347_ = lean_array_fset(v_source_1341_, v_i_1340_, v___x_1346_);
v_target_1348_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_target_1342_, v_es_1345_);
v___x_1349_ = lean_unsigned_to_nat(1u);
v___x_1350_ = lean_nat_add(v_i_1340_, v___x_1349_);
lean_dec(v_i_1340_);
v_i_1340_ = v___x_1350_;
v_source_1341_ = v_source_1347_;
v_target_1342_ = v_target_1348_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(lean_object* v_data_1352_){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v_nbuckets_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1353_ = lean_array_get_size(v_data_1352_);
v___x_1354_ = lean_unsigned_to_nat(2u);
v_nbuckets_1355_ = lean_nat_mul(v___x_1353_, v___x_1354_);
v___x_1356_ = lean_unsigned_to_nat(0u);
v___x_1357_ = lean_box(0);
v___x_1358_ = lean_mk_array(v_nbuckets_1355_, v___x_1357_);
v___x_1359_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v___x_1356_, v_data_1352_, v___x_1358_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(lean_object* v_a_1360_, lean_object* v_b_1361_, lean_object* v_x_1362_){
_start:
{
if (lean_obj_tag(v_x_1362_) == 0)
{
lean_dec(v_b_1361_);
lean_dec_ref(v_a_1360_);
return v_x_1362_;
}
else
{
lean_object* v_key_1363_; lean_object* v_value_1364_; lean_object* v_tail_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1384_; 
v_key_1363_ = lean_ctor_get(v_x_1362_, 0);
v_value_1364_ = lean_ctor_get(v_x_1362_, 1);
v_tail_1365_ = lean_ctor_get(v_x_1362_, 2);
v_isSharedCheck_1384_ = !lean_is_exclusive(v_x_1362_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1367_ = v_x_1362_;
v_isShared_1368_ = v_isSharedCheck_1384_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_tail_1365_);
lean_inc(v_value_1364_);
lean_inc(v_key_1363_);
lean_dec(v_x_1362_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1384_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
uint8_t v___y_1370_; lean_object* v_fst_1378_; lean_object* v_snd_1379_; lean_object* v_fst_1380_; lean_object* v_snd_1381_; uint8_t v___x_1382_; 
v_fst_1378_ = lean_ctor_get(v_key_1363_, 0);
v_snd_1379_ = lean_ctor_get(v_key_1363_, 1);
v_fst_1380_ = lean_ctor_get(v_a_1360_, 0);
v_snd_1381_ = lean_ctor_get(v_a_1360_, 1);
v___x_1382_ = lean_nat_dec_eq(v_fst_1378_, v_fst_1380_);
if (v___x_1382_ == 0)
{
v___y_1370_ = v___x_1382_;
goto v___jp_1369_;
}
else
{
uint8_t v___x_1383_; 
v___x_1383_ = lean_nat_dec_eq(v_snd_1379_, v_snd_1381_);
v___y_1370_ = v___x_1383_;
goto v___jp_1369_;
}
v___jp_1369_:
{
if (v___y_1370_ == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1371_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_1360_, v_b_1361_, v_tail_1365_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 2, v___x_1371_);
v___x_1373_ = v___x_1367_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_key_1363_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_value_1364_);
lean_ctor_set(v_reuseFailAlloc_1374_, 2, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
else
{
lean_object* v___x_1376_; 
lean_dec(v_value_1364_);
lean_dec(v_key_1363_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 1, v_b_1361_);
lean_ctor_set(v___x_1367_, 0, v_a_1360_);
v___x_1376_ = v___x_1367_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1360_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_b_1361_);
lean_ctor_set(v_reuseFailAlloc_1377_, 2, v_tail_1365_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(lean_object* v_a_1385_, lean_object* v_x_1386_){
_start:
{
if (lean_obj_tag(v_x_1386_) == 0)
{
uint8_t v___x_1387_; 
v___x_1387_ = 0;
return v___x_1387_;
}
else
{
lean_object* v_key_1388_; lean_object* v_tail_1389_; uint8_t v___y_1391_; lean_object* v_fst_1393_; lean_object* v_snd_1394_; lean_object* v_fst_1395_; lean_object* v_snd_1396_; uint8_t v___x_1397_; 
v_key_1388_ = lean_ctor_get(v_x_1386_, 0);
v_tail_1389_ = lean_ctor_get(v_x_1386_, 2);
v_fst_1393_ = lean_ctor_get(v_key_1388_, 0);
v_snd_1394_ = lean_ctor_get(v_key_1388_, 1);
v_fst_1395_ = lean_ctor_get(v_a_1385_, 0);
v_snd_1396_ = lean_ctor_get(v_a_1385_, 1);
v___x_1397_ = lean_nat_dec_eq(v_fst_1393_, v_fst_1395_);
if (v___x_1397_ == 0)
{
v___y_1391_ = v___x_1397_;
goto v___jp_1390_;
}
else
{
uint8_t v___x_1398_; 
v___x_1398_ = lean_nat_dec_eq(v_snd_1394_, v_snd_1396_);
v___y_1391_ = v___x_1398_;
goto v___jp_1390_;
}
v___jp_1390_:
{
if (v___y_1391_ == 0)
{
v_x_1386_ = v_tail_1389_;
goto _start;
}
else
{
return v___y_1391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg___boxed(lean_object* v_a_1399_, lean_object* v_x_1400_){
_start:
{
uint8_t v_res_1401_; lean_object* v_r_1402_; 
v_res_1401_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_1399_, v_x_1400_);
lean_dec(v_x_1400_);
lean_dec_ref(v_a_1399_);
v_r_1402_ = lean_box(v_res_1401_);
return v_r_1402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(lean_object* v_m_1403_, lean_object* v_a_1404_, lean_object* v_b_1405_){
_start:
{
lean_object* v_size_1406_; lean_object* v_buckets_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1454_; 
v_size_1406_ = lean_ctor_get(v_m_1403_, 0);
v_buckets_1407_ = lean_ctor_get(v_m_1403_, 1);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_m_1403_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1409_ = v_m_1403_;
v_isShared_1410_ = v_isSharedCheck_1454_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_buckets_1407_);
lean_inc(v_size_1406_);
lean_dec(v_m_1403_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1454_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v_fst_1411_; lean_object* v_snd_1412_; lean_object* v___x_1413_; uint64_t v___x_1414_; uint64_t v___x_1415_; uint64_t v___x_1416_; uint64_t v___x_1417_; uint64_t v___x_1418_; uint64_t v_fold_1419_; uint64_t v___x_1420_; uint64_t v___x_1421_; uint64_t v___x_1422_; size_t v___x_1423_; size_t v___x_1424_; size_t v___x_1425_; size_t v___x_1426_; size_t v___x_1427_; lean_object* v_bkt_1428_; uint8_t v___x_1429_; 
v_fst_1411_ = lean_ctor_get(v_a_1404_, 0);
v_snd_1412_ = lean_ctor_get(v_a_1404_, 1);
v___x_1413_ = lean_array_get_size(v_buckets_1407_);
v___x_1414_ = l_String_instHashableRaw_hash(v_fst_1411_);
v___x_1415_ = l_String_instHashableRaw_hash(v_snd_1412_);
v___x_1416_ = lean_uint64_mix_hash(v___x_1414_, v___x_1415_);
v___x_1417_ = 32ULL;
v___x_1418_ = lean_uint64_shift_right(v___x_1416_, v___x_1417_);
v_fold_1419_ = lean_uint64_xor(v___x_1416_, v___x_1418_);
v___x_1420_ = 16ULL;
v___x_1421_ = lean_uint64_shift_right(v_fold_1419_, v___x_1420_);
v___x_1422_ = lean_uint64_xor(v_fold_1419_, v___x_1421_);
v___x_1423_ = lean_uint64_to_usize(v___x_1422_);
v___x_1424_ = lean_usize_of_nat(v___x_1413_);
v___x_1425_ = ((size_t)1ULL);
v___x_1426_ = lean_usize_sub(v___x_1424_, v___x_1425_);
v___x_1427_ = lean_usize_land(v___x_1423_, v___x_1426_);
v_bkt_1428_ = lean_array_uget_borrowed(v_buckets_1407_, v___x_1427_);
v___x_1429_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_1404_, v_bkt_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; lean_object* v_size_x27_1431_; lean_object* v___x_1432_; lean_object* v_buckets_x27_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; 
v___x_1430_ = lean_unsigned_to_nat(1u);
v_size_x27_1431_ = lean_nat_add(v_size_1406_, v___x_1430_);
lean_dec(v_size_1406_);
lean_inc(v_bkt_1428_);
v___x_1432_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1432_, 0, v_a_1404_);
lean_ctor_set(v___x_1432_, 1, v_b_1405_);
lean_ctor_set(v___x_1432_, 2, v_bkt_1428_);
v_buckets_x27_1433_ = lean_array_uset(v_buckets_1407_, v___x_1427_, v___x_1432_);
v___x_1434_ = lean_unsigned_to_nat(4u);
v___x_1435_ = lean_nat_mul(v_size_x27_1431_, v___x_1434_);
v___x_1436_ = lean_unsigned_to_nat(3u);
v___x_1437_ = lean_nat_div(v___x_1435_, v___x_1436_);
lean_dec(v___x_1435_);
v___x_1438_ = lean_array_get_size(v_buckets_x27_1433_);
v___x_1439_ = lean_nat_dec_le(v___x_1437_, v___x_1438_);
lean_dec(v___x_1437_);
if (v___x_1439_ == 0)
{
lean_object* v_val_1440_; lean_object* v___x_1442_; 
v_val_1440_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_buckets_x27_1433_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 1, v_val_1440_);
lean_ctor_set(v___x_1409_, 0, v_size_x27_1431_);
v___x_1442_ = v___x_1409_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_size_x27_1431_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_val_1440_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
else
{
lean_object* v___x_1445_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 1, v_buckets_x27_1433_);
lean_ctor_set(v___x_1409_, 0, v_size_x27_1431_);
v___x_1445_ = v___x_1409_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_size_x27_1431_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_buckets_x27_1433_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
else
{
lean_object* v___x_1447_; lean_object* v_buckets_x27_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1452_; 
lean_inc(v_bkt_1428_);
v___x_1447_ = lean_box(0);
v_buckets_x27_1448_ = lean_array_uset(v_buckets_1407_, v___x_1427_, v___x_1447_);
v___x_1449_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_1404_, v_b_1405_, v_bkt_1428_);
v___x_1450_ = lean_array_uset(v_buckets_x27_1448_, v___x_1427_, v___x_1449_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 1, v___x_1450_);
v___x_1452_ = v___x_1409_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_size_1406_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(uint8_t v___x_1457_, lean_object* v_as_1458_, size_t v_sz_1459_, size_t v_i_1460_, lean_object* v_b_1461_, lean_object* v___y_1462_){
_start:
{
uint8_t v___x_1464_; 
v___x_1464_ = lean_usize_dec_lt(v_i_1460_, v_sz_1459_);
if (v___x_1464_ == 0)
{
lean_object* v___x_1465_; 
v___x_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1465_, 0, v_b_1461_);
return v___x_1465_;
}
else
{
lean_object* v_snd_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1503_; 
v_snd_1466_ = lean_ctor_get(v_b_1461_, 1);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_b_1461_);
if (v_isSharedCheck_1503_ == 0)
{
lean_object* v_unused_1504_; 
v_unused_1504_ = lean_ctor_get(v_b_1461_, 0);
lean_dec(v_unused_1504_);
v___x_1468_ = v_b_1461_;
v_isShared_1469_ = v_isSharedCheck_1503_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_snd_1466_);
lean_dec(v_b_1461_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1503_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v_ref_1470_; lean_object* v_a_1471_; lean_object* v_ref_1472_; lean_object* v_msg_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1502_; 
v_ref_1470_ = lean_ctor_get(v___y_1462_, 5);
v_a_1471_ = lean_array_uget(v_as_1458_, v_i_1460_);
v_ref_1472_ = lean_ctor_get(v_a_1471_, 0);
v_msg_1473_ = lean_ctor_get(v_a_1471_, 1);
v_isSharedCheck_1502_ = !lean_is_exclusive(v_a_1471_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1475_ = v_a_1471_;
v_isShared_1476_ = v_isSharedCheck_1502_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_msg_1473_);
lean_inc(v_ref_1472_);
lean_dec(v_a_1471_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1502_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v_ref_1494_; lean_object* v___y_1496_; lean_object* v___x_1499_; 
v___x_1477_ = lean_box(0);
v_ref_1494_ = l_Lean_replaceRef(v_ref_1472_, v_ref_1470_);
lean_dec(v_ref_1472_);
v___x_1499_ = l_Lean_Syntax_getPos_x3f(v_ref_1494_, v___x_1457_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v___x_1500_; 
v___x_1500_ = lean_unsigned_to_nat(0u);
v___y_1496_ = v___x_1500_;
goto v___jp_1495_;
}
else
{
lean_object* v_val_1501_; 
v_val_1501_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_val_1501_);
lean_dec_ref(v___x_1499_);
v___y_1496_ = v_val_1501_;
goto v___jp_1495_;
}
v___jp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 1, v___y_1480_);
lean_ctor_set(v___x_1468_, 0, v___y_1479_);
v___x_1482_ = v___x_1468_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___y_1479_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v___y_1480_);
v___x_1482_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v_pos2traces_1486_; lean_object* v___x_1488_; 
v___x_1483_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1484_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1466_, v___x_1482_, v___x_1483_);
v___x_1485_ = lean_array_push(v___x_1484_, v_msg_1473_);
v_pos2traces_1486_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1466_, v___x_1482_, v___x_1485_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 1, v_pos2traces_1486_);
lean_ctor_set(v___x_1475_, 0, v___x_1477_);
v___x_1488_ = v___x_1475_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1477_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v_pos2traces_1486_);
v___x_1488_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
size_t v___x_1489_; size_t v___x_1490_; 
v___x_1489_ = ((size_t)1ULL);
v___x_1490_ = lean_usize_add(v_i_1460_, v___x_1489_);
v_i_1460_ = v___x_1490_;
v_b_1461_ = v___x_1488_;
goto _start;
}
}
}
v___jp_1495_:
{
lean_object* v___x_1497_; 
v___x_1497_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1494_, v___x_1457_);
lean_dec(v_ref_1494_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_inc(v___y_1496_);
v___y_1479_ = v___y_1496_;
v___y_1480_ = v___y_1496_;
goto v___jp_1478_;
}
else
{
lean_object* v_val_1498_; 
v_val_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_val_1498_);
lean_dec_ref(v___x_1497_);
v___y_1479_ = v___y_1496_;
v___y_1480_ = v_val_1498_;
goto v___jp_1478_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___boxed(lean_object* v___x_1505_, lean_object* v_as_1506_, lean_object* v_sz_1507_, lean_object* v_i_1508_, lean_object* v_b_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
uint8_t v___x_37889__boxed_1512_; size_t v_sz_boxed_1513_; size_t v_i_boxed_1514_; lean_object* v_res_1515_; 
v___x_37889__boxed_1512_ = lean_unbox(v___x_1505_);
v_sz_boxed_1513_ = lean_unbox_usize(v_sz_1507_);
lean_dec(v_sz_1507_);
v_i_boxed_1514_ = lean_unbox_usize(v_i_1508_);
lean_dec(v_i_1508_);
v_res_1515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_37889__boxed_1512_, v_as_1506_, v_sz_boxed_1513_, v_i_boxed_1514_, v_b_1509_, v___y_1510_);
lean_dec_ref(v___y_1510_);
lean_dec_ref(v_as_1506_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(uint8_t v___x_1516_, lean_object* v_as_1517_, size_t v_sz_1518_, size_t v_i_1519_, lean_object* v_b_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
uint8_t v___x_1524_; 
v___x_1524_ = lean_usize_dec_lt(v_i_1519_, v_sz_1518_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1525_, 0, v_b_1520_);
return v___x_1525_;
}
else
{
lean_object* v_snd_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1563_; 
v_snd_1526_ = lean_ctor_get(v_b_1520_, 1);
v_isSharedCheck_1563_ = !lean_is_exclusive(v_b_1520_);
if (v_isSharedCheck_1563_ == 0)
{
lean_object* v_unused_1564_; 
v_unused_1564_ = lean_ctor_get(v_b_1520_, 0);
lean_dec(v_unused_1564_);
v___x_1528_ = v_b_1520_;
v_isShared_1529_ = v_isSharedCheck_1563_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_snd_1526_);
lean_dec(v_b_1520_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1563_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v_ref_1530_; lean_object* v_a_1531_; lean_object* v_ref_1532_; lean_object* v_msg_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1562_; 
v_ref_1530_ = lean_ctor_get(v___y_1521_, 5);
v_a_1531_ = lean_array_uget(v_as_1517_, v_i_1519_);
v_ref_1532_ = lean_ctor_get(v_a_1531_, 0);
v_msg_1533_ = lean_ctor_get(v_a_1531_, 1);
v_isSharedCheck_1562_ = !lean_is_exclusive(v_a_1531_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1535_ = v_a_1531_;
v_isShared_1536_ = v_isSharedCheck_1562_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_msg_1533_);
lean_inc(v_ref_1532_);
lean_dec(v_a_1531_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1562_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1537_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v_ref_1554_; lean_object* v___y_1556_; lean_object* v___x_1559_; 
v___x_1537_ = lean_box(0);
v_ref_1554_ = l_Lean_replaceRef(v_ref_1532_, v_ref_1530_);
lean_dec(v_ref_1532_);
v___x_1559_ = l_Lean_Syntax_getPos_x3f(v_ref_1554_, v___x_1516_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v___x_1560_; 
v___x_1560_ = lean_unsigned_to_nat(0u);
v___y_1556_ = v___x_1560_;
goto v___jp_1555_;
}
else
{
lean_object* v_val_1561_; 
v_val_1561_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_val_1561_);
lean_dec_ref(v___x_1559_);
v___y_1556_ = v_val_1561_;
goto v___jp_1555_;
}
v___jp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 1, v___y_1540_);
lean_ctor_set(v___x_1528_, 0, v___y_1539_);
v___x_1542_ = v___x_1528_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___y_1539_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v___y_1540_);
v___x_1542_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v_pos2traces_1546_; lean_object* v___x_1548_; 
v___x_1543_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1544_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1526_, v___x_1542_, v___x_1543_);
v___x_1545_ = lean_array_push(v___x_1544_, v_msg_1533_);
v_pos2traces_1546_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1526_, v___x_1542_, v___x_1545_);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 1, v_pos2traces_1546_);
lean_ctor_set(v___x_1535_, 0, v___x_1537_);
v___x_1548_ = v___x_1535_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1537_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_pos2traces_1546_);
v___x_1548_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
size_t v___x_1549_; size_t v___x_1550_; lean_object* v___x_1551_; 
v___x_1549_ = ((size_t)1ULL);
v___x_1550_ = lean_usize_add(v_i_1519_, v___x_1549_);
v___x_1551_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_1516_, v_as_1517_, v_sz_1518_, v___x_1550_, v___x_1548_, v___y_1521_);
return v___x_1551_;
}
}
}
v___jp_1555_:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1554_, v___x_1516_);
lean_dec(v_ref_1554_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_inc(v___y_1556_);
v___y_1539_ = v___y_1556_;
v___y_1540_ = v___y_1556_;
goto v___jp_1538_;
}
else
{
lean_object* v_val_1558_; 
v_val_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_val_1558_);
lean_dec_ref(v___x_1557_);
v___y_1539_ = v___y_1556_;
v___y_1540_ = v_val_1558_;
goto v___jp_1538_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40___boxed(lean_object* v___x_1565_, lean_object* v_as_1566_, lean_object* v_sz_1567_, lean_object* v_i_1568_, lean_object* v_b_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
uint8_t v___x_37970__boxed_1573_; size_t v_sz_boxed_1574_; size_t v_i_boxed_1575_; lean_object* v_res_1576_; 
v___x_37970__boxed_1573_ = lean_unbox(v___x_1565_);
v_sz_boxed_1574_ = lean_unbox_usize(v_sz_1567_);
lean_dec(v_sz_1567_);
v_i_boxed_1575_ = lean_unbox_usize(v_i_1568_);
lean_dec(v_i_1568_);
v_res_1576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_37970__boxed_1573_, v_as_1566_, v_sz_boxed_1574_, v_i_boxed_1575_, v_b_1569_, v___y_1570_, v___y_1571_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec_ref(v_as_1566_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(lean_object* v_init_1577_, uint8_t v___x_1578_, lean_object* v_n_1579_, lean_object* v_b_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
if (lean_obj_tag(v_n_1579_) == 0)
{
lean_object* v_cs_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; size_t v_sz_1587_; size_t v___x_1588_; lean_object* v___x_1589_; 
v_cs_1584_ = lean_ctor_get(v_n_1579_, 0);
v___x_1585_ = lean_box(0);
v___x_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1585_);
lean_ctor_set(v___x_1586_, 1, v_b_1580_);
v_sz_1587_ = lean_array_size(v_cs_1584_);
v___x_1588_ = ((size_t)0ULL);
v___x_1589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_1577_, v___x_1578_, v_cs_1584_, v_sz_1587_, v___x_1588_, v___x_1586_, v___y_1581_, v___y_1582_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1604_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1592_ = v___x_1589_;
v_isShared_1593_ = v_isSharedCheck_1604_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1589_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1604_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v_fst_1594_; 
v_fst_1594_ = lean_ctor_get(v_a_1590_, 0);
if (lean_obj_tag(v_fst_1594_) == 0)
{
lean_object* v_snd_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
v_snd_1595_ = lean_ctor_get(v_a_1590_, 1);
lean_inc(v_snd_1595_);
lean_dec(v_a_1590_);
v___x_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1596_, 0, v_snd_1595_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v___x_1596_);
v___x_1598_ = v___x_1592_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
else
{
lean_object* v_val_1600_; lean_object* v___x_1602_; 
lean_inc_ref(v_fst_1594_);
lean_dec(v_a_1590_);
v_val_1600_ = lean_ctor_get(v_fst_1594_, 0);
lean_inc(v_val_1600_);
lean_dec_ref(v_fst_1594_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v_val_1600_);
v___x_1602_ = v___x_1592_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_val_1600_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
v_a_1605_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1589_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1589_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
else
{
lean_object* v_vs_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; size_t v_sz_1616_; size_t v___x_1617_; lean_object* v___x_1618_; 
v_vs_1613_ = lean_ctor_get(v_n_1579_, 0);
v___x_1614_ = lean_box(0);
v___x_1615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
lean_ctor_set(v___x_1615_, 1, v_b_1580_);
v_sz_1616_ = lean_array_size(v_vs_1613_);
v___x_1617_ = ((size_t)0ULL);
v___x_1618_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_1578_, v_vs_1613_, v_sz_1616_, v___x_1617_, v___x_1615_, v___y_1581_, v___y_1582_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1633_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1621_ = v___x_1618_;
v_isShared_1622_ = v_isSharedCheck_1633_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1633_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v_fst_1623_; 
v_fst_1623_ = lean_ctor_get(v_a_1619_, 0);
if (lean_obj_tag(v_fst_1623_) == 0)
{
lean_object* v_snd_1624_; lean_object* v___x_1625_; lean_object* v___x_1627_; 
v_snd_1624_ = lean_ctor_get(v_a_1619_, 1);
lean_inc(v_snd_1624_);
lean_dec(v_a_1619_);
v___x_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1625_, 0, v_snd_1624_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v___x_1625_);
v___x_1627_ = v___x_1621_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1625_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
else
{
lean_object* v_val_1629_; lean_object* v___x_1631_; 
lean_inc_ref(v_fst_1623_);
lean_dec(v_a_1619_);
v_val_1629_ = lean_ctor_get(v_fst_1623_, 0);
lean_inc(v_val_1629_);
lean_dec_ref(v_fst_1623_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v_val_1629_);
v___x_1631_ = v___x_1621_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_val_1629_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
v_a_1634_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v___x_1618_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1618_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(lean_object* v_init_1642_, uint8_t v___x_1643_, lean_object* v_as_1644_, size_t v_sz_1645_, size_t v_i_1646_, lean_object* v_b_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
uint8_t v___x_1651_; 
v___x_1651_ = lean_usize_dec_lt(v_i_1646_, v_sz_1645_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; 
v___x_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1652_, 0, v_b_1647_);
return v___x_1652_;
}
else
{
lean_object* v_snd_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1687_; 
v_snd_1653_ = lean_ctor_get(v_b_1647_, 1);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_b_1647_);
if (v_isSharedCheck_1687_ == 0)
{
lean_object* v_unused_1688_; 
v_unused_1688_ = lean_ctor_get(v_b_1647_, 0);
lean_dec(v_unused_1688_);
v___x_1655_ = v_b_1647_;
v_isShared_1656_ = v_isSharedCheck_1687_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_snd_1653_);
lean_dec(v_b_1647_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1687_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v_a_1657_; lean_object* v___x_1658_; 
v_a_1657_ = lean_array_uget_borrowed(v_as_1644_, v_i_1646_);
lean_inc(v_snd_1653_);
v___x_1658_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1642_, v___x_1643_, v_a_1657_, v_snd_1653_, v___y_1648_, v___y_1649_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1678_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1661_ = v___x_1658_;
v_isShared_1662_ = v_isSharedCheck_1678_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1658_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1678_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
if (lean_obj_tag(v_a_1659_) == 0)
{
lean_object* v___x_1663_; lean_object* v___x_1665_; 
v___x_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1663_, 0, v_a_1659_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1663_);
v___x_1665_ = v___x_1655_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1663_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_snd_1653_);
v___x_1665_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
lean_object* v___x_1667_; 
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 0, v___x_1665_);
v___x_1667_ = v___x_1661_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1665_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1671_; lean_object* v___x_1673_; 
lean_del_object(v___x_1661_);
lean_dec(v_snd_1653_);
v_a_1670_ = lean_ctor_get(v_a_1659_, 0);
lean_inc(v_a_1670_);
lean_dec_ref(v_a_1659_);
v___x_1671_ = lean_box(0);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 1, v_a_1670_);
lean_ctor_set(v___x_1655_, 0, v___x_1671_);
v___x_1673_ = v___x_1655_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1671_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v_a_1670_);
v___x_1673_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
size_t v___x_1674_; size_t v___x_1675_; 
v___x_1674_ = ((size_t)1ULL);
v___x_1675_ = lean_usize_add(v_i_1646_, v___x_1674_);
v_i_1646_ = v___x_1675_;
v_b_1647_ = v___x_1673_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_del_object(v___x_1655_);
lean_dec(v_snd_1653_);
v_a_1679_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1658_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1658_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39___boxed(lean_object* v_init_1689_, lean_object* v___x_1690_, lean_object* v_as_1691_, lean_object* v_sz_1692_, lean_object* v_i_1693_, lean_object* v_b_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
uint8_t v___x_38051__boxed_1698_; size_t v_sz_boxed_1699_; size_t v_i_boxed_1700_; lean_object* v_res_1701_; 
v___x_38051__boxed_1698_ = lean_unbox(v___x_1690_);
v_sz_boxed_1699_ = lean_unbox_usize(v_sz_1692_);
lean_dec(v_sz_1692_);
v_i_boxed_1700_ = lean_unbox_usize(v_i_1693_);
lean_dec(v_i_1693_);
v_res_1701_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_1689_, v___x_38051__boxed_1698_, v_as_1691_, v_sz_boxed_1699_, v_i_boxed_1700_, v_b_1694_, v___y_1695_, v___y_1696_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec_ref(v_as_1691_);
lean_dec_ref(v_init_1689_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27___boxed(lean_object* v_init_1702_, lean_object* v___x_1703_, lean_object* v_n_1704_, lean_object* v_b_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
uint8_t v___x_38071__boxed_1709_; lean_object* v_res_1710_; 
v___x_38071__boxed_1709_ = lean_unbox(v___x_1703_);
v_res_1710_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1702_, v___x_38071__boxed_1709_, v_n_1704_, v_b_1705_, v___y_1706_, v___y_1707_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec_ref(v_n_1704_);
lean_dec_ref(v_init_1702_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(uint8_t v___x_1711_, lean_object* v_as_1712_, size_t v_sz_1713_, size_t v_i_1714_, lean_object* v_b_1715_, lean_object* v___y_1716_){
_start:
{
uint8_t v___x_1718_; 
v___x_1718_ = lean_usize_dec_lt(v_i_1714_, v_sz_1713_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; 
v___x_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1719_, 0, v_b_1715_);
return v___x_1719_;
}
else
{
lean_object* v_snd_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1757_; 
v_snd_1720_ = lean_ctor_get(v_b_1715_, 1);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_b_1715_);
if (v_isSharedCheck_1757_ == 0)
{
lean_object* v_unused_1758_; 
v_unused_1758_ = lean_ctor_get(v_b_1715_, 0);
lean_dec(v_unused_1758_);
v___x_1722_ = v_b_1715_;
v_isShared_1723_ = v_isSharedCheck_1757_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_snd_1720_);
lean_dec(v_b_1715_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1757_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v_ref_1724_; lean_object* v_a_1725_; lean_object* v_ref_1726_; lean_object* v_msg_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1756_; 
v_ref_1724_ = lean_ctor_get(v___y_1716_, 5);
v_a_1725_ = lean_array_uget(v_as_1712_, v_i_1714_);
v_ref_1726_ = lean_ctor_get(v_a_1725_, 0);
v_msg_1727_ = lean_ctor_get(v_a_1725_, 1);
v_isSharedCheck_1756_ = !lean_is_exclusive(v_a_1725_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1729_ = v_a_1725_;
v_isShared_1730_ = v_isSharedCheck_1756_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_msg_1727_);
lean_inc(v_ref_1726_);
lean_dec(v_a_1725_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1756_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1731_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v_ref_1748_; lean_object* v___y_1750_; lean_object* v___x_1753_; 
v___x_1731_ = lean_box(0);
v_ref_1748_ = l_Lean_replaceRef(v_ref_1726_, v_ref_1724_);
lean_dec(v_ref_1726_);
v___x_1753_ = l_Lean_Syntax_getPos_x3f(v_ref_1748_, v___x_1711_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v___x_1754_; 
v___x_1754_ = lean_unsigned_to_nat(0u);
v___y_1750_ = v___x_1754_;
goto v___jp_1749_;
}
else
{
lean_object* v_val_1755_; 
v_val_1755_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_val_1755_);
lean_dec_ref(v___x_1753_);
v___y_1750_ = v_val_1755_;
goto v___jp_1749_;
}
v___jp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 1, v___y_1734_);
lean_ctor_set(v___x_1722_, 0, v___y_1733_);
v___x_1736_ = v___x_1722_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___y_1733_);
lean_ctor_set(v_reuseFailAlloc_1747_, 1, v___y_1734_);
v___x_1736_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v_pos2traces_1740_; lean_object* v___x_1742_; 
v___x_1737_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1738_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1720_, v___x_1736_, v___x_1737_);
v___x_1739_ = lean_array_push(v___x_1738_, v_msg_1727_);
v_pos2traces_1740_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1720_, v___x_1736_, v___x_1739_);
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 1, v_pos2traces_1740_);
lean_ctor_set(v___x_1729_, 0, v___x_1731_);
v___x_1742_ = v___x_1729_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1731_);
lean_ctor_set(v_reuseFailAlloc_1746_, 1, v_pos2traces_1740_);
v___x_1742_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
size_t v___x_1743_; size_t v___x_1744_; 
v___x_1743_ = ((size_t)1ULL);
v___x_1744_ = lean_usize_add(v_i_1714_, v___x_1743_);
v_i_1714_ = v___x_1744_;
v_b_1715_ = v___x_1742_;
goto _start;
}
}
}
v___jp_1749_:
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1748_, v___x_1711_);
lean_dec(v_ref_1748_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_inc(v___y_1750_);
v___y_1733_ = v___y_1750_;
v___y_1734_ = v___y_1750_;
goto v___jp_1732_;
}
else
{
lean_object* v_val_1752_; 
v_val_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_val_1752_);
lean_dec_ref(v___x_1751_);
v___y_1733_ = v___y_1750_;
v___y_1734_ = v_val_1752_;
goto v___jp_1732_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg___boxed(lean_object* v___x_1759_, lean_object* v_as_1760_, lean_object* v_sz_1761_, lean_object* v_i_1762_, lean_object* v_b_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
uint8_t v___x_38254__boxed_1766_; size_t v_sz_boxed_1767_; size_t v_i_boxed_1768_; lean_object* v_res_1769_; 
v___x_38254__boxed_1766_ = lean_unbox(v___x_1759_);
v_sz_boxed_1767_ = lean_unbox_usize(v_sz_1761_);
lean_dec(v_sz_1761_);
v_i_boxed_1768_ = lean_unbox_usize(v_i_1762_);
lean_dec(v_i_1762_);
v_res_1769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_38254__boxed_1766_, v_as_1760_, v_sz_boxed_1767_, v_i_boxed_1768_, v_b_1763_, v___y_1764_);
lean_dec_ref(v___y_1764_);
lean_dec_ref(v_as_1760_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(uint8_t v___x_1770_, lean_object* v_as_1771_, size_t v_sz_1772_, size_t v_i_1773_, lean_object* v_b_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
uint8_t v___x_1778_; 
v___x_1778_ = lean_usize_dec_lt(v_i_1773_, v_sz_1772_);
if (v___x_1778_ == 0)
{
lean_object* v___x_1779_; 
v___x_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1779_, 0, v_b_1774_);
return v___x_1779_;
}
else
{
lean_object* v_snd_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1817_; 
v_snd_1780_ = lean_ctor_get(v_b_1774_, 1);
v_isSharedCheck_1817_ = !lean_is_exclusive(v_b_1774_);
if (v_isSharedCheck_1817_ == 0)
{
lean_object* v_unused_1818_; 
v_unused_1818_ = lean_ctor_get(v_b_1774_, 0);
lean_dec(v_unused_1818_);
v___x_1782_ = v_b_1774_;
v_isShared_1783_ = v_isSharedCheck_1817_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_snd_1780_);
lean_dec(v_b_1774_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1817_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v_ref_1784_; lean_object* v_a_1785_; lean_object* v_ref_1786_; lean_object* v_msg_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1816_; 
v_ref_1784_ = lean_ctor_get(v___y_1775_, 5);
v_a_1785_ = lean_array_uget(v_as_1771_, v_i_1773_);
v_ref_1786_ = lean_ctor_get(v_a_1785_, 0);
v_msg_1787_ = lean_ctor_get(v_a_1785_, 1);
v_isSharedCheck_1816_ = !lean_is_exclusive(v_a_1785_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1789_ = v_a_1785_;
v_isShared_1790_ = v_isSharedCheck_1816_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_msg_1787_);
lean_inc(v_ref_1786_);
lean_dec(v_a_1785_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1816_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1791_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v_ref_1808_; lean_object* v___y_1810_; lean_object* v___x_1813_; 
v___x_1791_ = lean_box(0);
v_ref_1808_ = l_Lean_replaceRef(v_ref_1786_, v_ref_1784_);
lean_dec(v_ref_1786_);
v___x_1813_ = l_Lean_Syntax_getPos_x3f(v_ref_1808_, v___x_1770_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v___x_1814_; 
v___x_1814_ = lean_unsigned_to_nat(0u);
v___y_1810_ = v___x_1814_;
goto v___jp_1809_;
}
else
{
lean_object* v_val_1815_; 
v_val_1815_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_val_1815_);
lean_dec_ref(v___x_1813_);
v___y_1810_ = v_val_1815_;
goto v___jp_1809_;
}
v___jp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 1, v___y_1794_);
lean_ctor_set(v___x_1782_, 0, v___y_1793_);
v___x_1796_ = v___x_1782_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___y_1793_);
lean_ctor_set(v_reuseFailAlloc_1807_, 1, v___y_1794_);
v___x_1796_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v_pos2traces_1800_; lean_object* v___x_1802_; 
v___x_1797_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1798_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1780_, v___x_1796_, v___x_1797_);
v___x_1799_ = lean_array_push(v___x_1798_, v_msg_1787_);
v_pos2traces_1800_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1780_, v___x_1796_, v___x_1799_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 1, v_pos2traces_1800_);
lean_ctor_set(v___x_1789_, 0, v___x_1791_);
v___x_1802_ = v___x_1789_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1791_);
lean_ctor_set(v_reuseFailAlloc_1806_, 1, v_pos2traces_1800_);
v___x_1802_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
size_t v___x_1803_; size_t v___x_1804_; lean_object* v___x_1805_; 
v___x_1803_ = ((size_t)1ULL);
v___x_1804_ = lean_usize_add(v_i_1773_, v___x_1803_);
v___x_1805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_1770_, v_as_1771_, v_sz_1772_, v___x_1804_, v___x_1802_, v___y_1775_);
return v___x_1805_;
}
}
}
v___jp_1809_:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1808_, v___x_1770_);
lean_dec(v_ref_1808_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_inc(v___y_1810_);
v___y_1793_ = v___y_1810_;
v___y_1794_ = v___y_1810_;
goto v___jp_1792_;
}
else
{
lean_object* v_val_1812_; 
v_val_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_val_1812_);
lean_dec_ref(v___x_1811_);
v___y_1793_ = v___y_1810_;
v___y_1794_ = v_val_1812_;
goto v___jp_1792_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28___boxed(lean_object* v___x_1819_, lean_object* v_as_1820_, lean_object* v_sz_1821_, lean_object* v_i_1822_, lean_object* v_b_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
uint8_t v___x_38334__boxed_1827_; size_t v_sz_boxed_1828_; size_t v_i_boxed_1829_; lean_object* v_res_1830_; 
v___x_38334__boxed_1827_ = lean_unbox(v___x_1819_);
v_sz_boxed_1828_ = lean_unbox_usize(v_sz_1821_);
lean_dec(v_sz_1821_);
v_i_boxed_1829_ = lean_unbox_usize(v_i_1822_);
lean_dec(v_i_1822_);
v_res_1830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_38334__boxed_1827_, v_as_1820_, v_sz_boxed_1828_, v_i_boxed_1829_, v_b_1823_, v___y_1824_, v___y_1825_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec_ref(v_as_1820_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(uint8_t v___x_1831_, lean_object* v_t_1832_, lean_object* v_init_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v_root_1837_; lean_object* v_tail_1838_; lean_object* v___x_1839_; 
v_root_1837_ = lean_ctor_get(v_t_1832_, 0);
v_tail_1838_ = lean_ctor_get(v_t_1832_, 1);
lean_inc_ref(v_init_1833_);
v___x_1839_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1833_, v___x_1831_, v_root_1837_, v_init_1833_, v___y_1834_, v___y_1835_);
lean_dec_ref(v_init_1833_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1876_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1842_ = v___x_1839_;
v_isShared_1843_ = v_isSharedCheck_1876_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1876_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
if (lean_obj_tag(v_a_1840_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1846_; 
v_a_1844_ = lean_ctor_get(v_a_1840_, 0);
lean_inc(v_a_1844_);
lean_dec_ref(v_a_1840_);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v_a_1844_);
v___x_1846_ = v___x_1842_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1844_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
else
{
lean_object* v_a_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; size_t v_sz_1851_; size_t v___x_1852_; lean_object* v___x_1853_; 
lean_del_object(v___x_1842_);
v_a_1848_ = lean_ctor_get(v_a_1840_, 0);
lean_inc(v_a_1848_);
lean_dec_ref(v_a_1840_);
v___x_1849_ = lean_box(0);
v___x_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
lean_ctor_set(v___x_1850_, 1, v_a_1848_);
v_sz_1851_ = lean_array_size(v_tail_1838_);
v___x_1852_ = ((size_t)0ULL);
v___x_1853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_1831_, v_tail_1838_, v_sz_1851_, v___x_1852_, v___x_1850_, v___y_1834_, v___y_1835_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1867_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1856_ = v___x_1853_;
v_isShared_1857_ = v_isSharedCheck_1867_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1853_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1867_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v_fst_1858_; 
v_fst_1858_ = lean_ctor_get(v_a_1854_, 0);
if (lean_obj_tag(v_fst_1858_) == 0)
{
lean_object* v_snd_1859_; lean_object* v___x_1861_; 
v_snd_1859_ = lean_ctor_get(v_a_1854_, 1);
lean_inc(v_snd_1859_);
lean_dec(v_a_1854_);
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 0, v_snd_1859_);
v___x_1861_ = v___x_1856_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_snd_1859_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
else
{
lean_object* v_val_1863_; lean_object* v___x_1865_; 
lean_inc_ref(v_fst_1858_);
lean_dec(v_a_1854_);
v_val_1863_ = lean_ctor_get(v_fst_1858_, 0);
lean_inc(v_val_1863_);
lean_dec_ref(v_fst_1858_);
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 0, v_val_1863_);
v___x_1865_ = v___x_1856_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_val_1863_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
v_a_1868_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1853_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1853_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
v_a_1877_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1839_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1839_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19___boxed(lean_object* v___x_1885_, lean_object* v_t_1886_, lean_object* v_init_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
uint8_t v___x_38415__boxed_1891_; lean_object* v_res_1892_; 
v___x_38415__boxed_1891_ = lean_unbox(v___x_1885_);
v_res_1892_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_38415__boxed_1891_, v_t_1886_, v_init_1887_, v___y_1888_, v___y_1889_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec_ref(v_t_1886_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(lean_object* v_x_1893_, lean_object* v_x_1894_){
_start:
{
if (lean_obj_tag(v_x_1894_) == 0)
{
return v_x_1893_;
}
else
{
lean_object* v_key_1895_; lean_object* v_value_1896_; lean_object* v_tail_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v_key_1895_ = lean_ctor_get(v_x_1894_, 0);
v_value_1896_ = lean_ctor_get(v_x_1894_, 1);
v_tail_1897_ = lean_ctor_get(v_x_1894_, 2);
lean_inc(v_value_1896_);
lean_inc(v_key_1895_);
v___x_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1898_, 0, v_key_1895_);
lean_ctor_set(v___x_1898_, 1, v_value_1896_);
v___x_1899_ = lean_array_push(v_x_1893_, v___x_1898_);
v_x_1893_ = v___x_1899_;
v_x_1894_ = v_tail_1897_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22___boxed(lean_object* v_x_1901_, lean_object* v_x_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_x_1901_, v_x_1902_);
lean_dec(v_x_1902_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(lean_object* v_as_1904_, size_t v_i_1905_, size_t v_stop_1906_, lean_object* v_b_1907_){
_start:
{
uint8_t v___x_1908_; 
v___x_1908_ = lean_usize_dec_eq(v_i_1905_, v_stop_1906_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1909_; lean_object* v___x_1910_; size_t v___x_1911_; size_t v___x_1912_; 
v___x_1909_ = lean_array_uget_borrowed(v_as_1904_, v_i_1905_);
v___x_1910_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_b_1907_, v___x_1909_);
v___x_1911_ = ((size_t)1ULL);
v___x_1912_ = lean_usize_add(v_i_1905_, v___x_1911_);
v_i_1905_ = v___x_1912_;
v_b_1907_ = v___x_1910_;
goto _start;
}
else
{
return v_b_1907_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23___boxed(lean_object* v_as_1914_, lean_object* v_i_1915_, lean_object* v_stop_1916_, lean_object* v_b_1917_){
_start:
{
size_t v_i_boxed_1918_; size_t v_stop_boxed_1919_; lean_object* v_res_1920_; 
v_i_boxed_1918_ = lean_unbox_usize(v_i_1915_);
lean_dec(v_i_1915_);
v_stop_boxed_1919_ = lean_unbox_usize(v_stop_1916_);
lean_dec(v_stop_1916_);
v_res_1920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_as_1914_, v_i_boxed_1918_, v_stop_boxed_1919_, v_b_1917_);
lean_dec_ref(v_as_1914_);
return v_res_1920_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0(void){
_start:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1921_ = lean_unsigned_to_nat(32u);
v___x_1922_ = lean_mk_empty_array_with_capacity(v___x_1921_);
v___x_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
return v___x_1923_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1(void){
_start:
{
size_t v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1924_ = ((size_t)5ULL);
v___x_1925_ = lean_unsigned_to_nat(0u);
v___x_1926_ = lean_unsigned_to_nat(32u);
v___x_1927_ = lean_mk_empty_array_with_capacity(v___x_1926_);
v___x_1928_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0);
v___x_1929_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
lean_ctor_set(v___x_1929_, 1, v___x_1927_);
lean_ctor_set(v___x_1929_, 2, v___x_1925_);
lean_ctor_set(v___x_1929_, 3, v___x_1925_);
lean_ctor_set_usize(v___x_1929_, 4, v___x_1924_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(lean_object* v___y_1930_){
_start:
{
lean_object* v___x_1932_; lean_object* v_traceState_1933_; lean_object* v_traces_1934_; lean_object* v___x_1935_; lean_object* v_traceState_1936_; lean_object* v_env_1937_; lean_object* v_nextMacroScope_1938_; lean_object* v_ngen_1939_; lean_object* v_auxDeclNGen_1940_; lean_object* v_cache_1941_; lean_object* v_messages_1942_; lean_object* v_infoState_1943_; lean_object* v_snapshotTasks_1944_; lean_object* v_newDecls_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1964_; 
v___x_1932_ = lean_st_ref_get(v___y_1930_);
v_traceState_1933_ = lean_ctor_get(v___x_1932_, 4);
lean_inc_ref(v_traceState_1933_);
lean_dec(v___x_1932_);
v_traces_1934_ = lean_ctor_get(v_traceState_1933_, 0);
lean_inc_ref(v_traces_1934_);
lean_dec_ref(v_traceState_1933_);
v___x_1935_ = lean_st_ref_take(v___y_1930_);
v_traceState_1936_ = lean_ctor_get(v___x_1935_, 4);
v_env_1937_ = lean_ctor_get(v___x_1935_, 0);
v_nextMacroScope_1938_ = lean_ctor_get(v___x_1935_, 1);
v_ngen_1939_ = lean_ctor_get(v___x_1935_, 2);
v_auxDeclNGen_1940_ = lean_ctor_get(v___x_1935_, 3);
v_cache_1941_ = lean_ctor_get(v___x_1935_, 5);
v_messages_1942_ = lean_ctor_get(v___x_1935_, 6);
v_infoState_1943_ = lean_ctor_get(v___x_1935_, 7);
v_snapshotTasks_1944_ = lean_ctor_get(v___x_1935_, 8);
v_newDecls_1945_ = lean_ctor_get(v___x_1935_, 9);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1947_ = v___x_1935_;
v_isShared_1948_ = v_isSharedCheck_1964_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_newDecls_1945_);
lean_inc(v_snapshotTasks_1944_);
lean_inc(v_infoState_1943_);
lean_inc(v_messages_1942_);
lean_inc(v_cache_1941_);
lean_inc(v_traceState_1936_);
lean_inc(v_auxDeclNGen_1940_);
lean_inc(v_ngen_1939_);
lean_inc(v_nextMacroScope_1938_);
lean_inc(v_env_1937_);
lean_dec(v___x_1935_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1964_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
uint64_t v_tid_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1962_; 
v_tid_1949_ = lean_ctor_get_uint64(v_traceState_1936_, sizeof(void*)*1);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_traceState_1936_);
if (v_isSharedCheck_1962_ == 0)
{
lean_object* v_unused_1963_; 
v_unused_1963_ = lean_ctor_get(v_traceState_1936_, 0);
lean_dec(v_unused_1963_);
v___x_1951_ = v_traceState_1936_;
v_isShared_1952_ = v_isSharedCheck_1962_;
goto v_resetjp_1950_;
}
else
{
lean_dec(v_traceState_1936_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1962_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1953_; lean_object* v___x_1955_; 
v___x_1953_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v___x_1953_);
v___x_1955_ = v___x_1951_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1953_);
lean_ctor_set_uint64(v_reuseFailAlloc_1961_, sizeof(void*)*1, v_tid_1949_);
v___x_1955_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
lean_object* v___x_1957_; 
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 4, v___x_1955_);
v___x_1957_ = v___x_1947_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_env_1937_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v_nextMacroScope_1938_);
lean_ctor_set(v_reuseFailAlloc_1960_, 2, v_ngen_1939_);
lean_ctor_set(v_reuseFailAlloc_1960_, 3, v_auxDeclNGen_1940_);
lean_ctor_set(v_reuseFailAlloc_1960_, 4, v___x_1955_);
lean_ctor_set(v_reuseFailAlloc_1960_, 5, v_cache_1941_);
lean_ctor_set(v_reuseFailAlloc_1960_, 6, v_messages_1942_);
lean_ctor_set(v_reuseFailAlloc_1960_, 7, v_infoState_1943_);
lean_ctor_set(v_reuseFailAlloc_1960_, 8, v_snapshotTasks_1944_);
lean_ctor_set(v_reuseFailAlloc_1960_, 9, v_newDecls_1945_);
v___x_1957_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = lean_st_ref_set(v___y_1930_, v___x_1957_);
v___x_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1959_, 0, v_traces_1934_);
return v___x_1959_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___boxed(lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_1965_);
lean_dec(v___y_1965_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(lean_object* v_hi_1968_, lean_object* v_pivot_1969_, lean_object* v_as_1970_, lean_object* v_i_1971_, lean_object* v_k_1972_){
_start:
{
uint8_t v___x_1973_; 
v___x_1973_ = lean_nat_dec_lt(v_k_1972_, v_hi_1968_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
lean_dec(v_k_1972_);
v___x_1974_ = lean_array_fswap(v_as_1970_, v_i_1971_, v_hi_1968_);
v___x_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1975_, 0, v_i_1971_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
return v___x_1975_;
}
else
{
lean_object* v___x_1976_; lean_object* v_fst_1977_; lean_object* v_fst_1978_; lean_object* v_fst_1979_; lean_object* v_fst_1980_; uint8_t v___x_1981_; 
v___x_1976_ = lean_array_fget_borrowed(v_as_1970_, v_k_1972_);
v_fst_1977_ = lean_ctor_get(v___x_1976_, 0);
v_fst_1978_ = lean_ctor_get(v_pivot_1969_, 0);
v_fst_1979_ = lean_ctor_get(v_fst_1977_, 0);
v_fst_1980_ = lean_ctor_get(v_fst_1978_, 0);
v___x_1981_ = lean_nat_dec_lt(v_fst_1979_, v_fst_1980_);
if (v___x_1981_ == 0)
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = lean_unsigned_to_nat(1u);
v___x_1983_ = lean_nat_add(v_k_1972_, v___x_1982_);
lean_dec(v_k_1972_);
v_k_1972_ = v___x_1983_;
goto _start;
}
else
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1985_ = lean_array_fswap(v_as_1970_, v_i_1971_, v_k_1972_);
v___x_1986_ = lean_unsigned_to_nat(1u);
v___x_1987_ = lean_nat_add(v_i_1971_, v___x_1986_);
lean_dec(v_i_1971_);
v___x_1988_ = lean_nat_add(v_k_1972_, v___x_1986_);
lean_dec(v_k_1972_);
v_as_1970_ = v___x_1985_;
v_i_1971_ = v___x_1987_;
v_k_1972_ = v___x_1988_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg___boxed(lean_object* v_hi_1990_, lean_object* v_pivot_1991_, lean_object* v_as_1992_, lean_object* v_i_1993_, lean_object* v_k_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_1990_, v_pivot_1991_, v_as_1992_, v_i_1993_, v_k_1994_);
lean_dec_ref(v_pivot_1991_);
lean_dec(v_hi_1990_);
return v_res_1995_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(lean_object* v_x_1996_, lean_object* v_x_1997_){
_start:
{
lean_object* v_fst_1998_; lean_object* v_fst_1999_; lean_object* v_fst_2000_; lean_object* v_fst_2001_; uint8_t v___x_2002_; 
v_fst_1998_ = lean_ctor_get(v_x_1996_, 0);
v_fst_1999_ = lean_ctor_get(v_x_1997_, 0);
v_fst_2000_ = lean_ctor_get(v_fst_1998_, 0);
v_fst_2001_ = lean_ctor_get(v_fst_1999_, 0);
v___x_2002_ = lean_nat_dec_lt(v_fst_2000_, v_fst_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0___boxed(lean_object* v_x_2003_, lean_object* v_x_2004_){
_start:
{
uint8_t v_res_2005_; lean_object* v_r_2006_; 
v_res_2005_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v_x_2003_, v_x_2004_);
lean_dec_ref(v_x_2004_);
lean_dec_ref(v_x_2003_);
v_r_2006_ = lean_box(v_res_2005_);
return v_r_2006_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(lean_object* v_n_2007_, lean_object* v_as_2008_, lean_object* v_lo_2009_, lean_object* v_hi_2010_){
_start:
{
lean_object* v___y_2012_; uint8_t v___x_2022_; 
v___x_2022_ = lean_nat_dec_lt(v_lo_2009_, v_hi_2010_);
if (v___x_2022_ == 0)
{
lean_dec(v_lo_2009_);
return v_as_2008_;
}
else
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v_mid_2025_; lean_object* v___y_2027_; lean_object* v___y_2033_; lean_object* v___x_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; 
v___x_2023_ = lean_nat_add(v_lo_2009_, v_hi_2010_);
v___x_2024_ = lean_unsigned_to_nat(1u);
v_mid_2025_ = lean_nat_shiftr(v___x_2023_, v___x_2024_);
lean_dec(v___x_2023_);
v___x_2038_ = lean_array_fget_borrowed(v_as_2008_, v_mid_2025_);
v___x_2039_ = lean_array_fget_borrowed(v_as_2008_, v_lo_2009_);
v___x_2040_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2038_, v___x_2039_);
if (v___x_2040_ == 0)
{
v___y_2033_ = v_as_2008_;
goto v___jp_2032_;
}
else
{
lean_object* v___x_2041_; 
v___x_2041_ = lean_array_fswap(v_as_2008_, v_lo_2009_, v_mid_2025_);
v___y_2033_ = v___x_2041_;
goto v___jp_2032_;
}
v___jp_2026_:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; uint8_t v___x_2030_; 
v___x_2028_ = lean_array_fget_borrowed(v___y_2027_, v_mid_2025_);
v___x_2029_ = lean_array_fget_borrowed(v___y_2027_, v_hi_2010_);
v___x_2030_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2028_, v___x_2029_);
if (v___x_2030_ == 0)
{
lean_dec(v_mid_2025_);
v___y_2012_ = v___y_2027_;
goto v___jp_2011_;
}
else
{
lean_object* v___x_2031_; 
v___x_2031_ = lean_array_fswap(v___y_2027_, v_mid_2025_, v_hi_2010_);
lean_dec(v_mid_2025_);
v___y_2012_ = v___x_2031_;
goto v___jp_2011_;
}
}
v___jp_2032_:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; uint8_t v___x_2036_; 
v___x_2034_ = lean_array_fget_borrowed(v___y_2033_, v_hi_2010_);
v___x_2035_ = lean_array_fget_borrowed(v___y_2033_, v_lo_2009_);
v___x_2036_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2034_, v___x_2035_);
if (v___x_2036_ == 0)
{
v___y_2027_ = v___y_2033_;
goto v___jp_2026_;
}
else
{
lean_object* v___x_2037_; 
v___x_2037_ = lean_array_fswap(v___y_2033_, v_lo_2009_, v_hi_2010_);
v___y_2027_ = v___x_2037_;
goto v___jp_2026_;
}
}
}
v___jp_2011_:
{
lean_object* v_pivot_2013_; lean_object* v___x_2014_; lean_object* v_fst_2015_; lean_object* v_snd_2016_; uint8_t v___x_2017_; 
v_pivot_2013_ = lean_array_fget(v___y_2012_, v_hi_2010_);
lean_inc_n(v_lo_2009_, 2);
v___x_2014_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_2010_, v_pivot_2013_, v___y_2012_, v_lo_2009_, v_lo_2009_);
lean_dec(v_pivot_2013_);
v_fst_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_fst_2015_);
v_snd_2016_ = lean_ctor_get(v___x_2014_, 1);
lean_inc(v_snd_2016_);
lean_dec_ref(v___x_2014_);
v___x_2017_ = lean_nat_dec_le(v_hi_2010_, v_fst_2015_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2018_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_2007_, v_snd_2016_, v_lo_2009_, v_fst_2015_);
v___x_2019_ = lean_unsigned_to_nat(1u);
v___x_2020_ = lean_nat_add(v_fst_2015_, v___x_2019_);
lean_dec(v_fst_2015_);
v_as_2008_ = v___x_2018_;
v_lo_2009_ = v___x_2020_;
goto _start;
}
else
{
lean_dec(v_fst_2015_);
lean_dec(v_lo_2009_);
return v_snd_2016_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___boxed(lean_object* v_n_2042_, lean_object* v_as_2043_, lean_object* v_lo_2044_, lean_object* v_hi_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_2042_, v_as_2043_, v_lo_2044_, v_hi_2045_);
lean_dec(v_hi_2045_);
lean_dec(v_n_2042_);
return v_res_2046_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2047_ = lean_box(0);
v___x_2048_ = lean_unsigned_to_nat(16u);
v___x_2049_ = lean_mk_array(v___x_2048_, v___x_2047_);
return v___x_2049_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1(void){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v_pos2traces_2052_; 
v___x_2050_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0);
v___x_2051_ = lean_unsigned_to_nat(0u);
v_pos2traces_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_2052_, 0, v___x_2051_);
lean_ctor_set(v_pos2traces_2052_, 1, v___x_2050_);
return v_pos2traces_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10(lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v_options_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v_options_2059_ = lean_ctor_get(v___y_2053_, 2);
v___x_2060_ = l_Lean_trace_profiler_output;
v___x_2061_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(v_options_2059_, v___x_2060_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v___x_2062_; uint8_t v___x_2063_; 
v___x_2062_ = l_Lean_trace_profiler_serve;
v___x_2063_ = l_Lean_Option_get___at___00main_spec__8(v_options_2059_, v___x_2062_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2131_; 
v___x_2064_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_2054_);
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2067_ = v___x_2064_;
v_isShared_2068_ = v_isSharedCheck_2131_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2064_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2131_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
uint8_t v___x_2069_; 
v___x_2069_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_2065_);
if (v___x_2069_ == 0)
{
lean_object* v___x_2070_; lean_object* v_pos2traces_2071_; lean_object* v___x_2072_; 
lean_del_object(v___x_2067_);
v___x_2070_ = lean_unsigned_to_nat(0u);
v_pos2traces_2071_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1);
v___x_2072_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_2069_, v_a_2065_, v_pos2traces_2071_, v___y_2053_, v___y_2054_);
lean_dec(v_a_2065_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v___y_2075_; lean_object* v___y_2089_; lean_object* v___y_2090_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2101_; lean_object* v_size_2107_; lean_object* v_buckets_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2073_);
lean_dec_ref(v___x_2072_);
v_size_2107_ = lean_ctor_get(v_a_2073_, 0);
lean_inc(v_size_2107_);
v_buckets_2108_ = lean_ctor_get(v_a_2073_, 1);
lean_inc_ref(v_buckets_2108_);
lean_dec(v_a_2073_);
v___x_2109_ = lean_mk_empty_array_with_capacity(v_size_2107_);
lean_dec(v_size_2107_);
v___x_2110_ = lean_array_get_size(v_buckets_2108_);
v___x_2111_ = lean_nat_dec_lt(v___x_2070_, v___x_2110_);
if (v___x_2111_ == 0)
{
lean_dec_ref(v_buckets_2108_);
v___y_2101_ = v___x_2109_;
goto v___jp_2100_;
}
else
{
uint8_t v___x_2112_; 
v___x_2112_ = lean_nat_dec_le(v___x_2110_, v___x_2110_);
if (v___x_2112_ == 0)
{
if (v___x_2111_ == 0)
{
lean_dec_ref(v_buckets_2108_);
v___y_2101_ = v___x_2109_;
goto v___jp_2100_;
}
else
{
size_t v___x_2113_; size_t v___x_2114_; lean_object* v___x_2115_; 
v___x_2113_ = ((size_t)0ULL);
v___x_2114_ = lean_usize_of_nat(v___x_2110_);
v___x_2115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_buckets_2108_, v___x_2113_, v___x_2114_, v___x_2109_);
lean_dec_ref(v_buckets_2108_);
v___y_2101_ = v___x_2115_;
goto v___jp_2100_;
}
}
else
{
size_t v___x_2116_; size_t v___x_2117_; lean_object* v___x_2118_; 
v___x_2116_ = ((size_t)0ULL);
v___x_2117_ = lean_usize_of_nat(v___x_2110_);
v___x_2118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_buckets_2108_, v___x_2116_, v___x_2117_, v___x_2109_);
lean_dec_ref(v_buckets_2108_);
v___y_2101_ = v___x_2118_;
goto v___jp_2100_;
}
}
v___jp_2074_:
{
lean_object* v___x_2076_; size_t v_sz_2077_; size_t v___x_2078_; lean_object* v___x_2079_; 
v___x_2076_ = lean_box(0);
v_sz_2077_ = lean_array_size(v___y_2075_);
v___x_2078_ = ((size_t)0ULL);
v___x_2079_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_2063_, v___y_2075_, v_sz_2077_, v___x_2078_, v___x_2076_, v___y_2053_, v___y_2054_);
lean_dec_ref(v___y_2075_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2086_ == 0)
{
lean_object* v_unused_2087_; 
v_unused_2087_ = lean_ctor_get(v___x_2079_, 0);
lean_dec(v_unused_2087_);
v___x_2081_ = v___x_2079_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_dec(v___x_2079_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 0, v___x_2076_);
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2076_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
else
{
return v___x_2079_;
}
}
v___jp_2088_:
{
lean_object* v___x_2093_; 
v___x_2093_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v___y_2091_, v___y_2089_, v___y_2090_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec(v___y_2091_);
v___y_2075_ = v___x_2093_;
goto v___jp_2074_;
}
v___jp_2094_:
{
uint8_t v___x_2099_; 
v___x_2099_ = lean_nat_dec_le(v___y_2098_, v___y_2095_);
if (v___x_2099_ == 0)
{
lean_dec(v___y_2095_);
lean_inc(v___y_2098_);
v___y_2089_ = v___y_2096_;
v___y_2090_ = v___y_2098_;
v___y_2091_ = v___y_2097_;
v___y_2092_ = v___y_2098_;
goto v___jp_2088_;
}
else
{
v___y_2089_ = v___y_2096_;
v___y_2090_ = v___y_2098_;
v___y_2091_ = v___y_2097_;
v___y_2092_ = v___y_2095_;
goto v___jp_2088_;
}
}
v___jp_2100_:
{
lean_object* v___x_2102_; uint8_t v___x_2103_; 
v___x_2102_ = lean_array_get_size(v___y_2101_);
v___x_2103_ = lean_nat_dec_eq(v___x_2102_, v___x_2070_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
v___x_2104_ = lean_unsigned_to_nat(1u);
v___x_2105_ = lean_nat_sub(v___x_2102_, v___x_2104_);
v___x_2106_ = lean_nat_dec_le(v___x_2070_, v___x_2105_);
if (v___x_2106_ == 0)
{
lean_inc(v___x_2105_);
v___y_2095_ = v___x_2105_;
v___y_2096_ = v___y_2101_;
v___y_2097_ = v___x_2102_;
v___y_2098_ = v___x_2105_;
goto v___jp_2094_;
}
else
{
v___y_2095_ = v___x_2105_;
v___y_2096_ = v___y_2101_;
v___y_2097_ = v___x_2102_;
v___y_2098_ = v___x_2070_;
goto v___jp_2094_;
}
}
else
{
v___y_2075_ = v___y_2101_;
goto v___jp_2074_;
}
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
v_a_2119_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2072_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2072_);
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
else
{
lean_object* v___x_2127_; lean_object* v___x_2129_; 
lean_dec(v_a_2065_);
v___x_2127_ = lean_box(0);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 0, v___x_2127_);
v___x_2129_ = v___x_2067_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2127_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
else
{
goto v___jp_2056_;
}
}
else
{
lean_dec_ref(v___x_2061_);
goto v___jp_2056_;
}
v___jp_2056_:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = lean_box(0);
v___x_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
return v___x_2058_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10___boxed(lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2132_, v___y_2133_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(lean_object* v_as_2136_, size_t v_sz_2137_, size_t v_i_2138_, lean_object* v_b_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
uint8_t v___x_2143_; 
v___x_2143_ = lean_usize_dec_lt(v_i_2138_, v_sz_2137_);
if (v___x_2143_ == 0)
{
lean_object* v___x_2144_; 
v___x_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2144_, 0, v_b_2139_);
return v___x_2144_;
}
else
{
lean_object* v_options_2145_; lean_object* v_a_2146_; lean_object* v___x_2147_; 
v_options_2145_ = lean_ctor_get(v___y_2140_, 2);
v_a_2146_ = lean_array_uget_borrowed(v_as_2136_, v_i_2138_);
lean_inc_ref(v_options_2145_);
lean_inc(v_a_2146_);
v___x_2147_ = l_Lean_Compiler_LCNF_resumeCompilation(v_a_2146_, v_options_2145_, v___y_2140_, v___y_2141_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v___x_2148_; 
lean_dec_ref(v___x_2147_);
v___x_2148_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2140_, v___y_2141_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v___x_2149_; size_t v___x_2150_; size_t v___x_2151_; 
lean_dec_ref(v___x_2148_);
v___x_2149_ = lean_box(0);
v___x_2150_ = ((size_t)1ULL);
v___x_2151_ = lean_usize_add(v_i_2138_, v___x_2150_);
v_i_2138_ = v___x_2151_;
v_b_2139_ = v___x_2149_;
goto _start;
}
else
{
return v___x_2148_;
}
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2154_; 
v_a_2153_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2153_);
lean_dec_ref(v___x_2147_);
v___x_2154_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2140_, v___y_2141_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2161_ == 0)
{
lean_object* v_unused_2162_; 
v_unused_2162_ = lean_ctor_get(v___x_2154_, 0);
lean_dec(v_unused_2162_);
v___x_2156_ = v___x_2154_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_dec(v___x_2154_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
lean_ctor_set_tag(v___x_2156_, 1);
lean_ctor_set(v___x_2156_, 0, v_a_2153_);
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2153_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
else
{
lean_dec(v_a_2153_);
return v___x_2154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11___boxed(lean_object* v_as_2163_, lean_object* v_sz_2164_, lean_object* v_i_2165_, lean_object* v_b_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
size_t v_sz_boxed_2170_; size_t v_i_boxed_2171_; lean_object* v_res_2172_; 
v_sz_boxed_2170_ = lean_unbox_usize(v_sz_2164_);
lean_dec(v_sz_2164_);
v_i_boxed_2171_ = lean_unbox_usize(v_i_2165_);
lean_dec(v_i_2165_);
v_res_2172_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_as_2163_, v_sz_boxed_2170_, v_i_boxed_2171_, v_b_2166_, v___y_2167_, v___y_2168_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec_ref(v_as_2163_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(lean_object* v_as_2173_, size_t v_sz_2174_, size_t v_i_2175_, lean_object* v_b_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
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
lean_object* v_a_2182_; lean_object* v_declNames_2183_; lean_object* v___x_2184_; size_t v_sz_2185_; size_t v___x_2186_; lean_object* v___x_2187_; 
v_a_2182_ = lean_array_uget_borrowed(v_as_2173_, v_i_2175_);
v_declNames_2183_ = lean_ctor_get(v_a_2182_, 0);
v___x_2184_ = lean_box(0);
v_sz_2185_ = lean_array_size(v_declNames_2183_);
v___x_2186_ = ((size_t)0ULL);
v___x_2187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_declNames_2183_, v_sz_2185_, v___x_2186_, v___x_2184_, v___y_2177_, v___y_2178_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v___x_2188_; 
lean_dec_ref(v___x_2187_);
v___x_2188_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v___y_2178_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; lean_object* v_unreported_2190_; lean_object* v___x_2191_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_a_2189_);
lean_dec_ref(v___x_2188_);
v_unreported_2190_ = lean_ctor_get(v_a_2189_, 1);
lean_inc_ref(v_unreported_2190_);
lean_dec(v_a_2189_);
v___x_2191_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(v_unreported_2190_, v___x_2184_, v___y_2177_, v___y_2178_);
lean_dec_ref(v_unreported_2190_);
if (lean_obj_tag(v___x_2191_) == 0)
{
size_t v___x_2192_; size_t v___x_2193_; 
lean_dec_ref(v___x_2191_);
v___x_2192_ = ((size_t)1ULL);
v___x_2193_ = lean_usize_add(v_i_2175_, v___x_2192_);
v_i_2175_ = v___x_2193_;
v_b_2176_ = v___x_2184_;
goto _start;
}
else
{
return v___x_2191_;
}
}
else
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2202_; 
v_a_2195_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2197_ = v___x_2188_;
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2188_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2200_; 
if (v_isShared_2198_ == 0)
{
v___x_2200_ = v___x_2197_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_a_2195_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
else
{
return v___x_2187_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13___boxed(lean_object* v_as_2203_, lean_object* v_sz_2204_, lean_object* v_i_2205_, lean_object* v_b_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
size_t v_sz_boxed_2210_; size_t v_i_boxed_2211_; lean_object* v_res_2212_; 
v_sz_boxed_2210_ = lean_unbox_usize(v_sz_2204_);
lean_dec(v_sz_2204_);
v_i_boxed_2211_ = lean_unbox_usize(v_i_2205_);
lean_dec(v_i_2205_);
v_res_2212_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v_as_2203_, v_sz_boxed_2210_, v_i_boxed_2211_, v_b_2206_, v___y_2207_, v___y_2208_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec_ref(v_as_2203_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object* v_as_2213_, size_t v_i_2214_, size_t v_stop_2215_, lean_object* v_b_2216_){
_start:
{
uint8_t v___x_2217_; 
v___x_2217_ = lean_usize_dec_eq(v_i_2214_, v_stop_2215_);
if (v___x_2217_ == 0)
{
lean_object* v___x_2218_; lean_object* v_name_2219_; lean_object* v___x_2220_; size_t v___x_2221_; size_t v___x_2222_; 
v___x_2218_ = lean_array_uget_borrowed(v_as_2213_, v_i_2214_);
v_name_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_name_2219_);
v___x_2220_ = l_Lean_Compiler_LCNF_setDeclPublic(v_b_2216_, v_name_2219_);
v___x_2221_ = ((size_t)1ULL);
v___x_2222_ = lean_usize_add(v_i_2214_, v___x_2221_);
v_i_2214_ = v___x_2222_;
v_b_2216_ = v___x_2220_;
goto _start;
}
else
{
return v_b_2216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object* v_as_2224_, lean_object* v_i_2225_, lean_object* v_stop_2226_, lean_object* v_b_2227_){
_start:
{
size_t v_i_boxed_2228_; size_t v_stop_boxed_2229_; lean_object* v_res_2230_; 
v_i_boxed_2228_ = lean_unbox_usize(v_i_2225_);
lean_dec(v_i_2225_);
v_stop_boxed_2229_ = lean_unbox_usize(v_stop_2226_);
lean_dec(v_stop_2226_);
v_res_2230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v_as_2224_, v_i_boxed_2228_, v_stop_boxed_2229_, v_b_2227_);
lean_dec_ref(v_as_2224_);
return v_res_2230_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0(uint8_t v___y_2231_, uint8_t v_suppressElabErrors_2232_, lean_object* v_x_2233_){
_start:
{
if (lean_obj_tag(v_x_2233_) == 1)
{
lean_object* v_pre_2234_; 
v_pre_2234_ = lean_ctor_get(v_x_2233_, 0);
switch(lean_obj_tag(v_pre_2234_))
{
case 1:
{
lean_object* v_pre_2235_; 
v_pre_2235_ = lean_ctor_get(v_pre_2234_, 0);
switch(lean_obj_tag(v_pre_2235_))
{
case 0:
{
lean_object* v_str_2236_; lean_object* v_str_2237_; lean_object* v___x_2238_; uint8_t v___x_2239_; 
v_str_2236_ = lean_ctor_get(v_x_2233_, 1);
v_str_2237_ = lean_ctor_get(v_pre_2234_, 1);
v___x_2238_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0));
v___x_2239_ = lean_string_dec_eq(v_str_2237_, v___x_2238_);
if (v___x_2239_ == 0)
{
lean_object* v___x_2240_; uint8_t v___x_2241_; 
v___x_2240_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1));
v___x_2241_ = lean_string_dec_eq(v_str_2237_, v___x_2240_);
if (v___x_2241_ == 0)
{
return v___y_2231_;
}
else
{
lean_object* v___x_2242_; uint8_t v___x_2243_; 
v___x_2242_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2));
v___x_2243_ = lean_string_dec_eq(v_str_2236_, v___x_2242_);
if (v___x_2243_ == 0)
{
return v___y_2231_;
}
else
{
return v_suppressElabErrors_2232_;
}
}
}
else
{
lean_object* v___x_2244_; uint8_t v___x_2245_; 
v___x_2244_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3));
v___x_2245_ = lean_string_dec_eq(v_str_2236_, v___x_2244_);
if (v___x_2245_ == 0)
{
return v___y_2231_;
}
else
{
return v_suppressElabErrors_2232_;
}
}
}
case 1:
{
lean_object* v_pre_2246_; 
v_pre_2246_ = lean_ctor_get(v_pre_2235_, 0);
if (lean_obj_tag(v_pre_2246_) == 0)
{
lean_object* v_str_2247_; lean_object* v_str_2248_; lean_object* v_str_2249_; lean_object* v___x_2250_; uint8_t v___x_2251_; 
v_str_2247_ = lean_ctor_get(v_x_2233_, 1);
v_str_2248_ = lean_ctor_get(v_pre_2234_, 1);
v_str_2249_ = lean_ctor_get(v_pre_2235_, 1);
v___x_2250_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4));
v___x_2251_ = lean_string_dec_eq(v_str_2249_, v___x_2250_);
if (v___x_2251_ == 0)
{
return v___y_2231_;
}
else
{
lean_object* v___x_2252_; uint8_t v___x_2253_; 
v___x_2252_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5));
v___x_2253_ = lean_string_dec_eq(v_str_2248_, v___x_2252_);
if (v___x_2253_ == 0)
{
return v___y_2231_;
}
else
{
lean_object* v___x_2254_; uint8_t v___x_2255_; 
v___x_2254_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6));
v___x_2255_ = lean_string_dec_eq(v_str_2247_, v___x_2254_);
if (v___x_2255_ == 0)
{
return v___y_2231_;
}
else
{
return v_suppressElabErrors_2232_;
}
}
}
}
else
{
return v___y_2231_;
}
}
default: 
{
return v___y_2231_;
}
}
}
case 0:
{
lean_object* v_str_2256_; lean_object* v___x_2257_; uint8_t v___x_2258_; 
v_str_2256_ = lean_ctor_get(v_x_2233_, 1);
v___x_2257_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_2258_ = lean_string_dec_eq(v_str_2256_, v___x_2257_);
if (v___x_2258_ == 0)
{
return v___y_2231_;
}
else
{
return v_suppressElabErrors_2232_;
}
}
default: 
{
return v___y_2231_;
}
}
}
else
{
return v___y_2231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0___boxed(lean_object* v___y_2259_, lean_object* v_suppressElabErrors_2260_, lean_object* v_x_2261_){
_start:
{
uint8_t v___y_39019__boxed_2262_; uint8_t v_suppressElabErrors_boxed_2263_; uint8_t v_res_2264_; lean_object* v_r_2265_; 
v___y_39019__boxed_2262_ = lean_unbox(v___y_2259_);
v_suppressElabErrors_boxed_2263_ = lean_unbox(v_suppressElabErrors_2260_);
v_res_2264_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0(v___y_39019__boxed_2262_, v_suppressElabErrors_boxed_2263_, v_x_2261_);
lean_dec(v_x_2261_);
v_r_2265_ = lean_box(v_res_2264_);
return v_r_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(lean_object* v_ref_2266_, lean_object* v_msgData_2267_, uint8_t v_severity_2268_, uint8_t v_isSilent_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; uint8_t v___y_2279_; uint8_t v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2313_; uint8_t v___y_2314_; uint8_t v___y_2315_; uint8_t v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; uint8_t v___y_2339_; lean_object* v___y_2340_; uint8_t v___y_2341_; uint8_t v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2347_; lean_object* v___y_2348_; lean_object* v___y_2349_; uint8_t v___y_2350_; lean_object* v___y_2351_; uint8_t v___y_2352_; uint8_t v___y_2353_; uint8_t v___x_2358_; lean_object* v___y_2360_; lean_object* v___y_2361_; uint8_t v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; uint8_t v___y_2365_; uint8_t v___y_2366_; uint8_t v___y_2368_; uint8_t v___x_2383_; 
v___x_2358_ = 2;
v___x_2383_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2268_, v___x_2358_);
if (v___x_2383_ == 0)
{
v___y_2368_ = v___x_2383_;
goto v___jp_2367_;
}
else
{
uint8_t v___x_2384_; 
lean_inc_ref(v_msgData_2267_);
v___x_2384_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2267_);
v___y_2368_ = v___x_2384_;
goto v___jp_2367_;
}
v___jp_2273_:
{
lean_object* v___x_2283_; lean_object* v_currNamespace_2284_; lean_object* v_openDecls_2285_; lean_object* v_env_2286_; lean_object* v_nextMacroScope_2287_; lean_object* v_ngen_2288_; lean_object* v_auxDeclNGen_2289_; lean_object* v_traceState_2290_; lean_object* v_cache_2291_; lean_object* v_messages_2292_; lean_object* v_infoState_2293_; lean_object* v_snapshotTasks_2294_; lean_object* v_newDecls_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2309_; 
v___x_2283_ = lean_st_ref_take(v___y_2282_);
v_currNamespace_2284_ = lean_ctor_get(v___y_2281_, 6);
v_openDecls_2285_ = lean_ctor_get(v___y_2281_, 7);
v_env_2286_ = lean_ctor_get(v___x_2283_, 0);
v_nextMacroScope_2287_ = lean_ctor_get(v___x_2283_, 1);
v_ngen_2288_ = lean_ctor_get(v___x_2283_, 2);
v_auxDeclNGen_2289_ = lean_ctor_get(v___x_2283_, 3);
v_traceState_2290_ = lean_ctor_get(v___x_2283_, 4);
v_cache_2291_ = lean_ctor_get(v___x_2283_, 5);
v_messages_2292_ = lean_ctor_get(v___x_2283_, 6);
v_infoState_2293_ = lean_ctor_get(v___x_2283_, 7);
v_snapshotTasks_2294_ = lean_ctor_get(v___x_2283_, 8);
v_newDecls_2295_ = lean_ctor_get(v___x_2283_, 9);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2297_ = v___x_2283_;
v_isShared_2298_ = v_isSharedCheck_2309_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_newDecls_2295_);
lean_inc(v_snapshotTasks_2294_);
lean_inc(v_infoState_2293_);
lean_inc(v_messages_2292_);
lean_inc(v_cache_2291_);
lean_inc(v_traceState_2290_);
lean_inc(v_auxDeclNGen_2289_);
lean_inc(v_ngen_2288_);
lean_inc(v_nextMacroScope_2287_);
lean_inc(v_env_2286_);
lean_dec(v___x_2283_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2309_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2304_; 
lean_inc(v_openDecls_2285_);
lean_inc(v_currNamespace_2284_);
v___x_2299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2299_, 0, v_currNamespace_2284_);
lean_ctor_set(v___x_2299_, 1, v_openDecls_2285_);
v___x_2300_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
lean_ctor_set(v___x_2300_, 1, v___y_2277_);
lean_inc_ref(v___y_2278_);
lean_inc_ref(v___y_2274_);
v___x_2301_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2301_, 0, v___y_2274_);
lean_ctor_set(v___x_2301_, 1, v___y_2276_);
lean_ctor_set(v___x_2301_, 2, v___y_2275_);
lean_ctor_set(v___x_2301_, 3, v___y_2278_);
lean_ctor_set(v___x_2301_, 4, v___x_2300_);
lean_ctor_set_uint8(v___x_2301_, sizeof(void*)*5, v___y_2280_);
lean_ctor_set_uint8(v___x_2301_, sizeof(void*)*5 + 1, v___y_2279_);
lean_ctor_set_uint8(v___x_2301_, sizeof(void*)*5 + 2, v_isSilent_2269_);
v___x_2302_ = l_Lean_MessageLog_add(v___x_2301_, v_messages_2292_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 6, v___x_2302_);
v___x_2304_ = v___x_2297_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_env_2286_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_nextMacroScope_2287_);
lean_ctor_set(v_reuseFailAlloc_2308_, 2, v_ngen_2288_);
lean_ctor_set(v_reuseFailAlloc_2308_, 3, v_auxDeclNGen_2289_);
lean_ctor_set(v_reuseFailAlloc_2308_, 4, v_traceState_2290_);
lean_ctor_set(v_reuseFailAlloc_2308_, 5, v_cache_2291_);
lean_ctor_set(v_reuseFailAlloc_2308_, 6, v___x_2302_);
lean_ctor_set(v_reuseFailAlloc_2308_, 7, v_infoState_2293_);
lean_ctor_set(v_reuseFailAlloc_2308_, 8, v_snapshotTasks_2294_);
lean_ctor_set(v_reuseFailAlloc_2308_, 9, v_newDecls_2295_);
v___x_2304_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = lean_st_ref_set(v___y_2282_, v___x_2304_);
v___x_2306_ = lean_box(0);
v___x_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
return v___x_2307_;
}
}
}
v___jp_2310_:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2334_; 
v___x_2319_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2267_);
v___x_2320_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v___x_2319_, v___y_2270_, v___y_2271_);
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2323_ = v___x_2320_;
v_isShared_2324_ = v_isSharedCheck_2334_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2320_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2334_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
lean_inc_ref_n(v___y_2312_, 2);
v___x_2325_ = l_Lean_FileMap_toPosition(v___y_2312_, v___y_2317_);
lean_dec(v___y_2317_);
v___x_2326_ = l_Lean_FileMap_toPosition(v___y_2312_, v___y_2318_);
lean_dec(v___y_2318_);
v___x_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
v___x_2328_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1));
if (v___y_2314_ == 0)
{
lean_del_object(v___x_2323_);
lean_dec_ref(v___y_2311_);
v___y_2274_ = v___y_2313_;
v___y_2275_ = v___x_2327_;
v___y_2276_ = v___x_2325_;
v___y_2277_ = v_a_2321_;
v___y_2278_ = v___x_2328_;
v___y_2279_ = v___y_2315_;
v___y_2280_ = v___y_2316_;
v___y_2281_ = v___y_2270_;
v___y_2282_ = v___y_2271_;
goto v___jp_2273_;
}
else
{
uint8_t v___x_2329_; 
lean_inc(v_a_2321_);
v___x_2329_ = l_Lean_MessageData_hasTag(v___y_2311_, v_a_2321_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; lean_object* v___x_2332_; 
lean_dec_ref(v___x_2327_);
lean_dec_ref(v___x_2325_);
lean_dec(v_a_2321_);
v___x_2330_ = lean_box(0);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 0, v___x_2330_);
v___x_2332_ = v___x_2323_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
else
{
lean_del_object(v___x_2323_);
v___y_2274_ = v___y_2313_;
v___y_2275_ = v___x_2327_;
v___y_2276_ = v___x_2325_;
v___y_2277_ = v_a_2321_;
v___y_2278_ = v___x_2328_;
v___y_2279_ = v___y_2315_;
v___y_2280_ = v___y_2316_;
v___y_2281_ = v___y_2270_;
v___y_2282_ = v___y_2271_;
goto v___jp_2273_;
}
}
}
}
v___jp_2335_:
{
lean_object* v___x_2344_; 
v___x_2344_ = l_Lean_Syntax_getTailPos_x3f(v___y_2340_, v___y_2342_);
lean_dec(v___y_2340_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_inc(v___y_2343_);
v___y_2311_ = v___y_2336_;
v___y_2312_ = v___y_2337_;
v___y_2313_ = v___y_2338_;
v___y_2314_ = v___y_2339_;
v___y_2315_ = v___y_2341_;
v___y_2316_ = v___y_2342_;
v___y_2317_ = v___y_2343_;
v___y_2318_ = v___y_2343_;
goto v___jp_2310_;
}
else
{
lean_object* v_val_2345_; 
v_val_2345_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_val_2345_);
lean_dec_ref(v___x_2344_);
v___y_2311_ = v___y_2336_;
v___y_2312_ = v___y_2337_;
v___y_2313_ = v___y_2338_;
v___y_2314_ = v___y_2339_;
v___y_2315_ = v___y_2341_;
v___y_2316_ = v___y_2342_;
v___y_2317_ = v___y_2343_;
v___y_2318_ = v_val_2345_;
goto v___jp_2310_;
}
}
v___jp_2346_:
{
lean_object* v_ref_2354_; lean_object* v___x_2355_; 
v_ref_2354_ = l_Lean_replaceRef(v_ref_2266_, v___y_2351_);
v___x_2355_ = l_Lean_Syntax_getPos_x3f(v_ref_2354_, v___y_2352_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v___x_2356_; 
v___x_2356_ = lean_unsigned_to_nat(0u);
v___y_2336_ = v___y_2347_;
v___y_2337_ = v___y_2348_;
v___y_2338_ = v___y_2349_;
v___y_2339_ = v___y_2350_;
v___y_2340_ = v_ref_2354_;
v___y_2341_ = v___y_2353_;
v___y_2342_ = v___y_2352_;
v___y_2343_ = v___x_2356_;
goto v___jp_2335_;
}
else
{
lean_object* v_val_2357_; 
v_val_2357_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_val_2357_);
lean_dec_ref(v___x_2355_);
v___y_2336_ = v___y_2347_;
v___y_2337_ = v___y_2348_;
v___y_2338_ = v___y_2349_;
v___y_2339_ = v___y_2350_;
v___y_2340_ = v_ref_2354_;
v___y_2341_ = v___y_2353_;
v___y_2342_ = v___y_2352_;
v___y_2343_ = v_val_2357_;
goto v___jp_2335_;
}
}
v___jp_2359_:
{
if (v___y_2366_ == 0)
{
v___y_2347_ = v___y_2364_;
v___y_2348_ = v___y_2360_;
v___y_2349_ = v___y_2361_;
v___y_2350_ = v___y_2362_;
v___y_2351_ = v___y_2363_;
v___y_2352_ = v___y_2365_;
v___y_2353_ = v_severity_2268_;
goto v___jp_2346_;
}
else
{
v___y_2347_ = v___y_2364_;
v___y_2348_ = v___y_2360_;
v___y_2349_ = v___y_2361_;
v___y_2350_ = v___y_2362_;
v___y_2351_ = v___y_2363_;
v___y_2352_ = v___y_2365_;
v___y_2353_ = v___x_2358_;
goto v___jp_2346_;
}
}
v___jp_2367_:
{
if (v___y_2368_ == 0)
{
lean_object* v_fileName_2369_; lean_object* v_fileMap_2370_; lean_object* v_options_2371_; lean_object* v_ref_2372_; uint8_t v_suppressElabErrors_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___f_2376_; uint8_t v___x_2377_; uint8_t v___x_2378_; 
v_fileName_2369_ = lean_ctor_get(v___y_2270_, 0);
v_fileMap_2370_ = lean_ctor_get(v___y_2270_, 1);
v_options_2371_ = lean_ctor_get(v___y_2270_, 2);
v_ref_2372_ = lean_ctor_get(v___y_2270_, 5);
v_suppressElabErrors_2373_ = lean_ctor_get_uint8(v___y_2270_, sizeof(void*)*14 + 1);
v___x_2374_ = lean_box(v___y_2368_);
v___x_2375_ = lean_box(v_suppressElabErrors_2373_);
v___f_2376_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2376_, 0, v___x_2374_);
lean_closure_set(v___f_2376_, 1, v___x_2375_);
v___x_2377_ = 1;
v___x_2378_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2268_, v___x_2377_);
if (v___x_2378_ == 0)
{
v___y_2360_ = v_fileMap_2370_;
v___y_2361_ = v_fileName_2369_;
v___y_2362_ = v_suppressElabErrors_2373_;
v___y_2363_ = v_ref_2372_;
v___y_2364_ = v___f_2376_;
v___y_2365_ = v___y_2368_;
v___y_2366_ = v___x_2378_;
goto v___jp_2359_;
}
else
{
lean_object* v___x_2379_; uint8_t v___x_2380_; 
v___x_2379_ = l_Lean_warningAsError;
v___x_2380_ = l_Lean_Option_get___at___00main_spec__8(v_options_2371_, v___x_2379_);
v___y_2360_ = v_fileMap_2370_;
v___y_2361_ = v_fileName_2369_;
v___y_2362_ = v_suppressElabErrors_2373_;
v___y_2363_ = v_ref_2372_;
v___y_2364_ = v___f_2376_;
v___y_2365_ = v___y_2368_;
v___y_2366_ = v___x_2380_;
goto v___jp_2359_;
}
}
else
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
lean_dec_ref(v_msgData_2267_);
v___x_2381_ = lean_box(0);
v___x_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2381_);
return v___x_2382_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___boxed(lean_object* v_ref_2385_, lean_object* v_msgData_2386_, lean_object* v_severity_2387_, lean_object* v_isSilent_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
uint8_t v_severity_boxed_2392_; uint8_t v_isSilent_boxed_2393_; lean_object* v_res_2394_; 
v_severity_boxed_2392_ = lean_unbox(v_severity_2387_);
v_isSilent_boxed_2393_ = lean_unbox(v_isSilent_2388_);
v_res_2394_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(v_ref_2385_, v_msgData_2386_, v_severity_boxed_2392_, v_isSilent_boxed_2393_, v___y_2389_, v___y_2390_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v_ref_2385_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(lean_object* v_msgData_2395_, uint8_t v_severity_2396_, uint8_t v_isSilent_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v_ref_2401_; lean_object* v___x_2402_; 
v_ref_2401_ = lean_ctor_get(v___y_2398_, 5);
v___x_2402_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(v_ref_2401_, v_msgData_2395_, v_severity_2396_, v_isSilent_2397_, v___y_2398_, v___y_2399_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30___boxed(lean_object* v_msgData_2403_, lean_object* v_severity_2404_, lean_object* v_isSilent_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
uint8_t v_severity_boxed_2409_; uint8_t v_isSilent_boxed_2410_; lean_object* v_res_2411_; 
v_severity_boxed_2409_ = lean_unbox(v_severity_2404_);
v_isSilent_boxed_2410_ = lean_unbox(v_isSilent_2405_);
v_res_2411_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2403_, v_severity_boxed_2409_, v_isSilent_boxed_2410_, v___y_2406_, v___y_2407_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14(lean_object* v_msgData_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
uint8_t v___x_2416_; uint8_t v___x_2417_; lean_object* v___x_2418_; 
v___x_2416_ = 2;
v___x_2417_ = 0;
v___x_2418_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2412_, v___x_2416_, v___x_2417_, v___y_2413_, v___y_2414_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14___boxed(lean_object* v_msgData_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Lean_logError___at___00main_spec__14(v_msgData_2419_, v___y_2420_, v___y_2421_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(lean_object* v_x2_2424_, lean_object* v_as_2425_, size_t v_i_2426_, size_t v_stop_2427_, lean_object* v_b_2428_){
_start:
{
uint8_t v___x_2429_; 
v___x_2429_ = lean_usize_dec_eq(v_i_2426_, v_stop_2427_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2430_; lean_object* v___x_2431_; size_t v___x_2432_; size_t v___x_2433_; 
v___x_2430_ = lean_array_uget_borrowed(v_as_2425_, v_i_2426_);
lean_inc_ref(v_x2_2424_);
lean_inc(v___x_2430_);
v___x_2431_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2430_, v_x2_2424_, v_b_2428_);
v___x_2432_ = ((size_t)1ULL);
v___x_2433_ = lean_usize_add(v_i_2426_, v___x_2432_);
v_i_2426_ = v___x_2433_;
v_b_2428_ = v___x_2431_;
goto _start;
}
else
{
lean_dec_ref(v_x2_2424_);
return v_b_2428_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(lean_object* v_x2_2435_, lean_object* v_as_2436_, lean_object* v_i_2437_, lean_object* v_stop_2438_, lean_object* v_b_2439_){
_start:
{
size_t v_i_boxed_2440_; size_t v_stop_boxed_2441_; lean_object* v_res_2442_; 
v_i_boxed_2440_ = lean_unbox_usize(v_i_2437_);
lean_dec(v_i_2437_);
v_stop_boxed_2441_ = lean_unbox_usize(v_stop_2438_);
lean_dec(v_stop_2438_);
v_res_2442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v_x2_2435_, v_as_2436_, v_i_boxed_2440_, v_stop_boxed_2441_, v_b_2439_);
lean_dec_ref(v_as_2436_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object* v_as_2443_, size_t v_i_2444_, size_t v_stop_2445_, lean_object* v_b_2446_){
_start:
{
lean_object* v___y_2448_; uint8_t v___x_2452_; 
v___x_2452_ = lean_usize_dec_eq(v_i_2444_, v_stop_2445_);
if (v___x_2452_ == 0)
{
lean_object* v___x_2453_; lean_object* v_declNames_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; uint8_t v___x_2457_; 
v___x_2453_ = lean_array_uget_borrowed(v_as_2443_, v_i_2444_);
v_declNames_2454_ = lean_ctor_get(v___x_2453_, 0);
v___x_2455_ = lean_unsigned_to_nat(0u);
v___x_2456_ = lean_array_get_size(v_declNames_2454_);
v___x_2457_ = lean_nat_dec_lt(v___x_2455_, v___x_2456_);
if (v___x_2457_ == 0)
{
v___y_2448_ = v_b_2446_;
goto v___jp_2447_;
}
else
{
uint8_t v___x_2458_; 
v___x_2458_ = lean_nat_dec_le(v___x_2456_, v___x_2456_);
if (v___x_2458_ == 0)
{
if (v___x_2457_ == 0)
{
v___y_2448_ = v_b_2446_;
goto v___jp_2447_;
}
else
{
size_t v___x_2459_; size_t v___x_2460_; lean_object* v___x_2461_; 
v___x_2459_ = ((size_t)0ULL);
v___x_2460_ = lean_usize_of_nat(v___x_2456_);
lean_inc(v___x_2453_);
v___x_2461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2453_, v_declNames_2454_, v___x_2459_, v___x_2460_, v_b_2446_);
v___y_2448_ = v___x_2461_;
goto v___jp_2447_;
}
}
else
{
size_t v___x_2462_; size_t v___x_2463_; lean_object* v___x_2464_; 
v___x_2462_ = ((size_t)0ULL);
v___x_2463_ = lean_usize_of_nat(v___x_2456_);
lean_inc(v___x_2453_);
v___x_2464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2453_, v_declNames_2454_, v___x_2462_, v___x_2463_, v_b_2446_);
v___y_2448_ = v___x_2464_;
goto v___jp_2447_;
}
}
}
else
{
return v_b_2446_;
}
v___jp_2447_:
{
size_t v___x_2449_; size_t v___x_2450_; 
v___x_2449_ = ((size_t)1ULL);
v___x_2450_ = lean_usize_add(v_i_2444_, v___x_2449_);
v_i_2444_ = v___x_2450_;
v_b_2446_ = v___y_2448_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object* v_as_2465_, lean_object* v_i_2466_, lean_object* v_stop_2467_, lean_object* v_b_2468_){
_start:
{
size_t v_i_boxed_2469_; size_t v_stop_boxed_2470_; lean_object* v_res_2471_; 
v_i_boxed_2469_ = lean_unbox_usize(v_i_2466_);
lean_dec(v_i_2466_);
v_stop_boxed_2470_ = lean_unbox_usize(v_stop_2467_);
lean_dec(v_stop_2467_);
v_res_2471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v_as_2465_, v_i_boxed_2469_, v_stop_boxed_2470_, v_b_2468_);
lean_dec_ref(v_as_2465_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(lean_object* v_a_2472_, lean_object* v_as_2473_, size_t v_i_2474_, size_t v_stop_2475_, lean_object* v_b_2476_){
_start:
{
lean_object* v___y_2478_; uint8_t v___x_2482_; 
v___x_2482_ = lean_usize_dec_eq(v_i_2474_, v_stop_2475_);
if (v___x_2482_ == 0)
{
lean_object* v___x_2483_; lean_object* v_name_2484_; uint8_t v___x_2485_; 
v___x_2483_ = lean_array_uget_borrowed(v_as_2473_, v_i_2474_);
v_name_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_name_2484_);
lean_inc_ref(v_a_2472_);
v___x_2485_ = l_Lean_isExtern(v_a_2472_, v_name_2484_);
if (v___x_2485_ == 0)
{
v___y_2478_ = v_b_2476_;
goto v___jp_2477_;
}
else
{
lean_object* v___x_2486_; 
lean_inc(v___x_2483_);
v___x_2486_ = lean_array_push(v_b_2476_, v___x_2483_);
v___y_2478_ = v___x_2486_;
goto v___jp_2477_;
}
}
else
{
lean_dec_ref(v_a_2472_);
return v_b_2476_;
}
v___jp_2477_:
{
size_t v___x_2479_; size_t v___x_2480_; 
v___x_2479_ = ((size_t)1ULL);
v___x_2480_ = lean_usize_add(v_i_2474_, v___x_2479_);
v_i_2474_ = v___x_2480_;
v_b_2476_ = v___y_2478_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19___boxed(lean_object* v_a_2487_, lean_object* v_as_2488_, lean_object* v_i_2489_, lean_object* v_stop_2490_, lean_object* v_b_2491_){
_start:
{
size_t v_i_boxed_2492_; size_t v_stop_boxed_2493_; lean_object* v_res_2494_; 
v_i_boxed_2492_ = lean_unbox_usize(v_i_2489_);
lean_dec(v_i_2489_);
v_stop_boxed_2493_ = lean_unbox_usize(v_stop_2490_);
lean_dec(v_stop_2490_);
v_res_2494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_2487_, v_as_2488_, v_i_boxed_2492_, v_stop_boxed_2493_, v_b_2491_);
lean_dec_ref(v_as_2488_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(lean_object* v_as_2495_, size_t v_sz_2496_, size_t v_i_2497_, lean_object* v_b_2498_){
_start:
{
uint8_t v___x_2500_; 
v___x_2500_ = lean_usize_dec_lt(v_i_2497_, v_sz_2496_);
if (v___x_2500_ == 0)
{
lean_object* v___x_2501_; 
v___x_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2501_, 0, v_b_2498_);
return v___x_2501_;
}
else
{
uint8_t v___x_2502_; lean_object* v_a_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
lean_dec_ref(v_b_2498_);
v___x_2502_ = 0;
v_a_2503_ = lean_array_uget_borrowed(v_as_2495_, v_i_2497_);
lean_inc(v_a_2503_);
v___x_2504_ = l_Lean_Message_toString(v_a_2503_, v___x_2502_);
v___x_2505_ = l_IO_eprintln___at___00main_spec__6(v___x_2504_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v___x_2506_; size_t v___x_2507_; size_t v___x_2508_; 
lean_dec_ref(v___x_2505_);
v___x_2506_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_2507_ = ((size_t)1ULL);
v___x_2508_ = lean_usize_add(v_i_2497_, v___x_2507_);
v_i_2497_ = v___x_2508_;
v_b_2498_ = v___x_2506_;
goto _start;
}
else
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2517_; 
v_a_2510_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2512_ = v___x_2505_;
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2505_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2513_ == 0)
{
v___x_2515_ = v___x_2512_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_a_2510_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27___boxed(lean_object* v_as_2518_, lean_object* v_sz_2519_, lean_object* v_i_2520_, lean_object* v_b_2521_, lean_object* v___y_2522_){
_start:
{
size_t v_sz_boxed_2523_; size_t v_i_boxed_2524_; lean_object* v_res_2525_; 
v_sz_boxed_2523_ = lean_unbox_usize(v_sz_2519_);
lean_dec(v_sz_2519_);
v_i_boxed_2524_ = lean_unbox_usize(v_i_2520_);
lean_dec(v_i_2520_);
v_res_2525_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2518_, v_sz_boxed_2523_, v_i_boxed_2524_, v_b_2521_);
lean_dec_ref(v_as_2518_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(lean_object* v_as_2526_, size_t v_sz_2527_, size_t v_i_2528_, lean_object* v_b_2529_){
_start:
{
uint8_t v___x_2531_; 
v___x_2531_ = lean_usize_dec_lt(v_i_2528_, v_sz_2527_);
if (v___x_2531_ == 0)
{
lean_object* v___x_2532_; 
v___x_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2532_, 0, v_b_2529_);
return v___x_2532_;
}
else
{
uint8_t v___x_2533_; lean_object* v_a_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
lean_dec_ref(v_b_2529_);
v___x_2533_ = 0;
v_a_2534_ = lean_array_uget_borrowed(v_as_2526_, v_i_2528_);
lean_inc(v_a_2534_);
v___x_2535_ = l_Lean_Message_toString(v_a_2534_, v___x_2533_);
v___x_2536_ = l_IO_eprintln___at___00main_spec__6(v___x_2535_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v___x_2537_; size_t v___x_2538_; size_t v___x_2539_; lean_object* v___x_2540_; 
lean_dec_ref(v___x_2536_);
v___x_2537_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_2538_ = ((size_t)1ULL);
v___x_2539_ = lean_usize_add(v_i_2528_, v___x_2538_);
v___x_2540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2526_, v_sz_2527_, v___x_2539_, v___x_2537_);
return v___x_2540_;
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
v_a_2541_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2536_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2536_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14___boxed(lean_object* v_as_2549_, lean_object* v_sz_2550_, lean_object* v_i_2551_, lean_object* v_b_2552_, lean_object* v___y_2553_){
_start:
{
size_t v_sz_boxed_2554_; size_t v_i_boxed_2555_; lean_object* v_res_2556_; 
v_sz_boxed_2554_ = lean_unbox_usize(v_sz_2550_);
lean_dec(v_sz_2550_);
v_i_boxed_2555_ = lean_unbox_usize(v_i_2551_);
lean_dec(v_i_2551_);
v_res_2556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_as_2549_, v_sz_boxed_2554_, v_i_boxed_2555_, v_b_2552_);
lean_dec_ref(v_as_2549_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(lean_object* v_init_2557_, lean_object* v_n_2558_, lean_object* v_b_2559_){
_start:
{
if (lean_obj_tag(v_n_2558_) == 0)
{
lean_object* v_cs_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; size_t v_sz_2564_; size_t v___x_2565_; lean_object* v___x_2566_; 
v_cs_2561_ = lean_ctor_get(v_n_2558_, 0);
v___x_2562_ = lean_box(0);
v___x_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2562_);
lean_ctor_set(v___x_2563_, 1, v_b_2559_);
v_sz_2564_ = lean_array_size(v_cs_2561_);
v___x_2565_ = ((size_t)0ULL);
v___x_2566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2557_, v_cs_2561_, v_sz_2564_, v___x_2565_, v___x_2563_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2581_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2569_ = v___x_2566_;
v_isShared_2570_ = v_isSharedCheck_2581_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2566_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2581_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v_fst_2571_; 
v_fst_2571_ = lean_ctor_get(v_a_2567_, 0);
if (lean_obj_tag(v_fst_2571_) == 0)
{
lean_object* v_snd_2572_; lean_object* v___x_2573_; lean_object* v___x_2575_; 
v_snd_2572_ = lean_ctor_get(v_a_2567_, 1);
lean_inc(v_snd_2572_);
lean_dec(v_a_2567_);
v___x_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2573_, 0, v_snd_2572_);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v___x_2573_);
v___x_2575_ = v___x_2569_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v___x_2573_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
else
{
lean_object* v_val_2577_; lean_object* v___x_2579_; 
lean_inc_ref(v_fst_2571_);
lean_dec(v_a_2567_);
v_val_2577_ = lean_ctor_get(v_fst_2571_, 0);
lean_inc(v_val_2577_);
lean_dec_ref(v_fst_2571_);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v_val_2577_);
v___x_2579_ = v___x_2569_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_val_2577_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
else
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
v_a_2582_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___x_2566_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2566_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
else
{
lean_object* v_vs_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; size_t v_sz_2593_; size_t v___x_2594_; lean_object* v___x_2595_; 
v_vs_2590_ = lean_ctor_get(v_n_2558_, 0);
v___x_2591_ = lean_box(0);
v___x_2592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
lean_ctor_set(v___x_2592_, 1, v_b_2559_);
v_sz_2593_ = lean_array_size(v_vs_2590_);
v___x_2594_ = ((size_t)0ULL);
v___x_2595_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_vs_2590_, v_sz_2593_, v___x_2594_, v___x_2592_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2610_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2598_ = v___x_2595_;
v_isShared_2599_ = v_isSharedCheck_2610_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2595_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2610_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v_fst_2600_; 
v_fst_2600_ = lean_ctor_get(v_a_2596_, 0);
if (lean_obj_tag(v_fst_2600_) == 0)
{
lean_object* v_snd_2601_; lean_object* v___x_2602_; lean_object* v___x_2604_; 
v_snd_2601_ = lean_ctor_get(v_a_2596_, 1);
lean_inc(v_snd_2601_);
lean_dec(v_a_2596_);
v___x_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2602_, 0, v_snd_2601_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v___x_2602_);
v___x_2604_ = v___x_2598_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2602_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
else
{
lean_object* v_val_2606_; lean_object* v___x_2608_; 
lean_inc_ref(v_fst_2600_);
lean_dec(v_a_2596_);
v_val_2606_ = lean_ctor_get(v_fst_2600_, 0);
lean_inc(v_val_2606_);
lean_dec_ref(v_fst_2600_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v_val_2606_);
v___x_2608_ = v___x_2598_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_val_2606_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
v_a_2611_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2595_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2595_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(lean_object* v_init_2619_, lean_object* v_as_2620_, size_t v_sz_2621_, size_t v_i_2622_, lean_object* v_b_2623_){
_start:
{
uint8_t v___x_2625_; 
v___x_2625_ = lean_usize_dec_lt(v_i_2622_, v_sz_2621_);
if (v___x_2625_ == 0)
{
lean_object* v___x_2626_; 
v___x_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2626_, 0, v_b_2623_);
return v___x_2626_;
}
else
{
lean_object* v_snd_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2661_; 
v_snd_2627_ = lean_ctor_get(v_b_2623_, 1);
v_isSharedCheck_2661_ = !lean_is_exclusive(v_b_2623_);
if (v_isSharedCheck_2661_ == 0)
{
lean_object* v_unused_2662_; 
v_unused_2662_ = lean_ctor_get(v_b_2623_, 0);
lean_dec(v_unused_2662_);
v___x_2629_ = v_b_2623_;
v_isShared_2630_ = v_isSharedCheck_2661_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_snd_2627_);
lean_dec(v_b_2623_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2661_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v_a_2631_; lean_object* v___x_2632_; 
v_a_2631_ = lean_array_uget_borrowed(v_as_2620_, v_i_2622_);
lean_inc(v_snd_2627_);
v___x_2632_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2619_, v_a_2631_, v_snd_2627_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2652_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2635_ = v___x_2632_;
v_isShared_2636_ = v_isSharedCheck_2652_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2632_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2652_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
if (lean_obj_tag(v_a_2633_) == 0)
{
lean_object* v___x_2637_; lean_object* v___x_2639_; 
v___x_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2637_, 0, v_a_2633_);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v___x_2637_);
v___x_2639_ = v___x_2629_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v___x_2637_);
lean_ctor_set(v_reuseFailAlloc_2643_, 1, v_snd_2627_);
v___x_2639_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
lean_object* v___x_2641_; 
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 0, v___x_2639_);
v___x_2641_ = v___x_2635_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2639_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2645_; lean_object* v___x_2647_; 
lean_del_object(v___x_2635_);
lean_dec(v_snd_2627_);
v_a_2644_ = lean_ctor_get(v_a_2633_, 0);
lean_inc(v_a_2644_);
lean_dec_ref(v_a_2633_);
v___x_2645_ = lean_box(0);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 1, v_a_2644_);
lean_ctor_set(v___x_2629_, 0, v___x_2645_);
v___x_2647_ = v___x_2629_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2645_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v_a_2644_);
v___x_2647_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
size_t v___x_2648_; size_t v___x_2649_; 
v___x_2648_ = ((size_t)1ULL);
v___x_2649_ = lean_usize_add(v_i_2622_, v___x_2648_);
v_i_2622_ = v___x_2649_;
v_b_2623_ = v___x_2647_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
lean_del_object(v___x_2629_);
lean_dec(v_snd_2627_);
v_a_2653_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v___x_2632_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2632_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
v___x_2658_ = v___x_2655_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2653_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13___boxed(lean_object* v_init_2663_, lean_object* v_as_2664_, lean_object* v_sz_2665_, lean_object* v_i_2666_, lean_object* v_b_2667_, lean_object* v___y_2668_){
_start:
{
size_t v_sz_boxed_2669_; size_t v_i_boxed_2670_; lean_object* v_res_2671_; 
v_sz_boxed_2669_ = lean_unbox_usize(v_sz_2665_);
lean_dec(v_sz_2665_);
v_i_boxed_2670_ = lean_unbox_usize(v_i_2666_);
lean_dec(v_i_2666_);
v_res_2671_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2663_, v_as_2664_, v_sz_boxed_2669_, v_i_boxed_2670_, v_b_2667_);
lean_dec_ref(v_as_2664_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10___boxed(lean_object* v_init_2672_, lean_object* v_n_2673_, lean_object* v_b_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2672_, v_n_2673_, v_b_2674_);
lean_dec_ref(v_n_2673_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(lean_object* v_as_2677_, size_t v_sz_2678_, size_t v_i_2679_, lean_object* v_b_2680_){
_start:
{
uint8_t v___x_2682_; 
v___x_2682_ = lean_usize_dec_lt(v_i_2679_, v_sz_2678_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; 
v___x_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2683_, 0, v_b_2680_);
return v___x_2683_;
}
else
{
uint8_t v___x_2684_; lean_object* v_a_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
lean_dec_ref(v_b_2680_);
v___x_2684_ = 0;
v_a_2685_ = lean_array_uget_borrowed(v_as_2677_, v_i_2679_);
lean_inc(v_a_2685_);
v___x_2686_ = l_Lean_Message_toString(v_a_2685_, v___x_2684_);
v___x_2687_ = l_IO_eprintln___at___00main_spec__6(v___x_2686_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v___x_2688_; size_t v___x_2689_; size_t v___x_2690_; 
lean_dec_ref(v___x_2687_);
v___x_2688_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_2689_ = ((size_t)1ULL);
v___x_2690_ = lean_usize_add(v_i_2679_, v___x_2689_);
v_i_2679_ = v___x_2690_;
v_b_2680_ = v___x_2688_;
goto _start;
}
else
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
v_a_2692_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2694_ = v___x_2687_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2687_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16___boxed(lean_object* v_as_2700_, lean_object* v_sz_2701_, lean_object* v_i_2702_, lean_object* v_b_2703_, lean_object* v___y_2704_){
_start:
{
size_t v_sz_boxed_2705_; size_t v_i_boxed_2706_; lean_object* v_res_2707_; 
v_sz_boxed_2705_ = lean_unbox_usize(v_sz_2701_);
lean_dec(v_sz_2701_);
v_i_boxed_2706_ = lean_unbox_usize(v_i_2702_);
lean_dec(v_i_2702_);
v_res_2707_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2700_, v_sz_boxed_2705_, v_i_boxed_2706_, v_b_2703_);
lean_dec_ref(v_as_2700_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(lean_object* v_as_2708_, size_t v_sz_2709_, size_t v_i_2710_, lean_object* v_b_2711_){
_start:
{
uint8_t v___x_2713_; 
v___x_2713_ = lean_usize_dec_lt(v_i_2710_, v_sz_2709_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2714_; 
v___x_2714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2714_, 0, v_b_2711_);
return v___x_2714_;
}
else
{
uint8_t v___x_2715_; lean_object* v_a_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
lean_dec_ref(v_b_2711_);
v___x_2715_ = 0;
v_a_2716_ = lean_array_uget_borrowed(v_as_2708_, v_i_2710_);
lean_inc(v_a_2716_);
v___x_2717_ = l_Lean_Message_toString(v_a_2716_, v___x_2715_);
v___x_2718_ = l_IO_eprintln___at___00main_spec__6(v___x_2717_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v___x_2719_; size_t v___x_2720_; size_t v___x_2721_; lean_object* v___x_2722_; 
lean_dec_ref(v___x_2718_);
v___x_2719_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_2720_ = ((size_t)1ULL);
v___x_2721_ = lean_usize_add(v_i_2710_, v___x_2720_);
v___x_2722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2708_, v_sz_2709_, v___x_2721_, v___x_2719_);
return v___x_2722_;
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
v_a_2723_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___x_2718_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2718_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11___boxed(lean_object* v_as_2731_, lean_object* v_sz_2732_, lean_object* v_i_2733_, lean_object* v_b_2734_, lean_object* v___y_2735_){
_start:
{
size_t v_sz_boxed_2736_; size_t v_i_boxed_2737_; lean_object* v_res_2738_; 
v_sz_boxed_2736_ = lean_unbox_usize(v_sz_2732_);
lean_dec(v_sz_2732_);
v_i_boxed_2737_ = lean_unbox_usize(v_i_2733_);
lean_dec(v_i_2733_);
v_res_2738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_as_2731_, v_sz_boxed_2736_, v_i_boxed_2737_, v_b_2734_);
lean_dec_ref(v_as_2731_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7(lean_object* v_t_2739_, lean_object* v_init_2740_){
_start:
{
lean_object* v_root_2742_; lean_object* v_tail_2743_; lean_object* v___x_2744_; 
v_root_2742_ = lean_ctor_get(v_t_2739_, 0);
v_tail_2743_ = lean_ctor_get(v_t_2739_, 1);
v___x_2744_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2740_, v_root_2742_, v_init_2740_);
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
lean_dec_ref(v_a_2745_);
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
lean_dec_ref(v_a_2745_);
v___x_2754_ = lean_box(0);
v___x_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2754_);
lean_ctor_set(v___x_2755_, 1, v_a_2753_);
v_sz_2756_ = lean_array_size(v_tail_2743_);
v___x_2757_ = ((size_t)0ULL);
v___x_2758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_tail_2743_, v_sz_2756_, v___x_2757_, v___x_2755_);
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
lean_dec_ref(v_fst_2763_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7___boxed(lean_object* v_t_2790_, lean_object* v_init_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v_res_2793_; 
v_res_2793_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_t_2790_, v_init_2791_);
lean_dec_ref(v_t_2790_);
return v_res_2793_;
}
}
static lean_object* _init_l_main___closed__3(void){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_box(0), lean_box(0), lean_box(0));
return v___x_2797_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2798_ = l_Lean_instInhabitedClassState_default;
v___x_2799_ = lean_box(0);
v___x_2800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2799_);
lean_ctor_set(v___x_2800_, 1, v___x_2798_);
return v___x_2800_;
}
}
static lean_object* _init_l_main___closed__5(void){
_start:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2801_ = l_Lean_Meta_Match_Extension_instInhabitedState;
v___x_2802_ = lean_box(0);
v___x_2803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2802_);
lean_ctor_set(v___x_2803_, 1, v___x_2801_);
return v___x_2803_;
}
}
static lean_object* _init_l_main___closed__6(void){
_start:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2804_ = ((lean_object*)(l_main___closed__2));
v___x_2805_ = ((lean_object*)(l_main___closed__1));
v___x_2806_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_2805_, v___x_2804_);
return v___x_2806_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2807_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2808_ = lean_box(0);
v___x_2809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2808_);
lean_ctor_set(v___x_2809_, 1, v___x_2807_);
return v___x_2809_;
}
}
static lean_object* _init_l_main___closed__8(void){
_start:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2810_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_2811_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2810_);
return v___x_2811_;
}
}
static lean_object* _init_l_main___closed__9(void){
_start:
{
lean_object* v___x_2812_; 
v___x_2812_ = l_Array_instInhabited(lean_box(0));
return v___x_2812_;
}
}
static lean_object* _init_l_main___closed__14(void){
_start:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = l_Lean_Options_empty;
v___x_2821_ = l_Lean_Core_getMaxHeartbeats(v___x_2820_);
return v___x_2821_;
}
}
static lean_object* _init_l_main___closed__19(void){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2826_ = ((lean_object*)(l_main___closed__18));
v___x_2827_ = lean_unsigned_to_nat(27u);
v___x_2828_ = lean_unsigned_to_nat(144u);
v___x_2829_ = ((lean_object*)(l_main___closed__17));
v___x_2830_ = ((lean_object*)(l_main___closed__16));
v___x_2831_ = l_mkPanicMessageWithDecl(v___x_2830_, v___x_2829_, v___x_2828_, v___x_2827_, v___x_2826_);
return v___x_2831_;
}
}
static lean_object* _init_l_main___closed__21(void){
_start:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2833_ = ((lean_object*)(l_main___closed__18));
v___x_2834_ = lean_unsigned_to_nat(51u);
v___x_2835_ = lean_unsigned_to_nat(117u);
v___x_2836_ = ((lean_object*)(l_main___closed__17));
v___x_2837_ = ((lean_object*)(l_main___closed__16));
v___x_2838_ = l_mkPanicMessageWithDecl(v___x_2837_, v___x_2836_, v___x_2835_, v___x_2834_, v___x_2833_);
return v___x_2838_;
}
}
static lean_object* _init_l_main___closed__22(void){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2839_ = lean_unsigned_to_nat(1u);
v___x_2840_ = l_Lean_firstFrontendMacroScope;
v___x_2841_ = lean_nat_add(v___x_2840_, v___x_2839_);
return v___x_2841_;
}
}
static lean_object* _init_l_main___closed__26(void){
_start:
{
lean_object* v___x_2848_; uint64_t v___x_2849_; lean_object* v___x_2850_; 
v___x_2848_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2849_ = 0ULL;
v___x_2850_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2850_, 0, v___x_2848_);
lean_ctor_set_uint64(v___x_2850_, sizeof(void*)*1, v___x_2849_);
return v___x_2850_;
}
}
static lean_object* _init_l_main___closed__27(void){
_start:
{
lean_object* v___x_2851_; 
v___x_2851_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2851_;
}
}
static lean_object* _init_l_main___closed__28(void){
_start:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2852_ = lean_obj_once(&l_main___closed__27, &l_main___closed__27_once, _init_l_main___closed__27);
v___x_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
return v___x_2853_;
}
}
static lean_object* _init_l_main___closed__29(void){
_start:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2854_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_2855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
lean_ctor_set(v___x_2855_, 1, v___x_2854_);
return v___x_2855_;
}
}
static lean_object* _init_l_main___closed__30(void){
_start:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2856_ = l_Lean_NameSet_empty;
v___x_2857_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2858_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2857_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
lean_ctor_set(v___x_2858_, 2, v___x_2856_);
return v___x_2858_;
}
}
static lean_object* _init_l_main___closed__31(void){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; uint8_t v___x_2861_; lean_object* v___x_2862_; 
v___x_2859_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2860_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_2861_ = 1;
v___x_2862_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2862_, 0, v___x_2860_);
lean_ctor_set(v___x_2862_, 1, v___x_2860_);
lean_ctor_set(v___x_2862_, 2, v___x_2859_);
lean_ctor_set_uint8(v___x_2862_, sizeof(void*)*3, v___x_2861_);
return v___x_2862_;
}
}
static uint8_t _init_l_main___closed__36(void){
_start:
{
uint8_t v___x_2869_; uint8_t v___x_2870_; 
v___x_2869_ = 2;
v___x_2870_ = l_Lean_instOrdOLeanLevel_ord(v___x_2869_, v___x_2869_);
return v___x_2870_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_2871_; lean_object* v___x_2872_; 
v___x_2871_ = 1;
v___x_2872_ = lean_box_uint32(v___x_2871_);
return v___x_2872_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_2873_; lean_object* v___x_2874_; 
v___x_2873_ = 0;
v___x_2874_ = lean_box_uint32(v___x_2873_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_2875_){
_start:
{
if (lean_obj_tag(v_args_2875_) == 1)
{
lean_object* v_tail_2900_; 
v_tail_2900_ = lean_ctor_get(v_args_2875_, 1);
lean_inc(v_tail_2900_);
if (lean_obj_tag(v_tail_2900_) == 1)
{
lean_object* v_tail_2901_; 
v_tail_2901_ = lean_ctor_get(v_tail_2900_, 1);
lean_inc(v_tail_2901_);
if (lean_obj_tag(v_tail_2901_) == 1)
{
lean_object* v_head_2902_; lean_object* v_head_2903_; lean_object* v_head_2904_; lean_object* v_tail_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_3536_; 
v_head_2902_ = lean_ctor_get(v_args_2875_, 0);
lean_inc(v_head_2902_);
lean_dec_ref(v_args_2875_);
v_head_2903_ = lean_ctor_get(v_tail_2900_, 0);
lean_inc(v_head_2903_);
lean_dec_ref(v_tail_2900_);
v_head_2904_ = lean_ctor_get(v_tail_2901_, 0);
v_tail_2905_ = lean_ctor_get(v_tail_2901_, 1);
v_isSharedCheck_3536_ = !lean_is_exclusive(v_tail_2901_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_2907_ = v_tail_2901_;
v_isShared_2908_ = v_isSharedCheck_3536_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_tail_2905_);
lean_inc(v_head_2904_);
lean_dec(v_tail_2901_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_3536_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2909_; 
v___x_2909_ = l_Lean_ModuleSetup_load(v_head_2902_);
lean_dec(v_head_2902_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_a_2910_; lean_object* v_name_2911_; lean_object* v_options_2912_; uint8_t v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2917_; 
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc(v_a_2910_);
lean_dec_ref(v___x_2909_);
v_name_2911_ = lean_ctor_get(v_a_2910_, 0);
lean_inc(v_name_2911_);
v_options_2912_ = lean_ctor_get(v_a_2910_, 6);
lean_inc(v_options_2912_);
lean_dec(v_a_2910_);
v___x_2913_ = 0;
v___x_2914_ = l_Lean_LeanOptions_toOptions(v_options_2912_);
v___x_2915_ = lean_box(v___x_2913_);
if (v_isShared_2908_ == 0)
{
lean_ctor_set_tag(v___x_2907_, 0);
lean_ctor_set(v___x_2907_, 1, v___x_2914_);
lean_ctor_set(v___x_2907_, 0, v___x_2915_);
v___x_2917_ = v___x_2907_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_2915_);
lean_ctor_set(v_reuseFailAlloc_3527_, 1, v___x_2914_);
v___x_2917_ = v_reuseFailAlloc_3527_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
lean_object* v___x_2918_; 
v___x_2918_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_tail_2905_, v___x_2917_);
lean_dec(v_tail_2905_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_object* v_a_2919_; lean_object* v___x_2920_; 
v_a_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc(v_a_2919_);
lean_dec_ref(v___x_2918_);
v___x_2920_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
lean_dec_ref(v___x_2920_);
v___x_2922_ = lean_box(0);
v___x_2923_ = l_Lean_initSearchPath(v_a_2921_, v___x_2922_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v_fst_2924_; lean_object* v_snd_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_3502_; 
lean_dec_ref(v___x_2923_);
v_fst_2924_ = lean_ctor_get(v_a_2919_, 0);
v_snd_2925_ = lean_ctor_get(v_a_2919_, 1);
v_isSharedCheck_3502_ = !lean_is_exclusive(v_a_2919_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_2927_ = v_a_2919_;
v_isShared_2928_ = v_isSharedCheck_3502_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_snd_2925_);
lean_inc(v_fst_2924_);
lean_dec(v_a_2919_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_3502_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; uint8_t v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; uint8_t v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; uint8_t v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v_nextMacroScope_3092_; lean_object* v_ngen_3093_; lean_object* v_auxDeclNGen_3094_; lean_object* v_traceState_3095_; lean_object* v_messages_3096_; lean_object* v_infoState_3097_; lean_object* v_snapshotTasks_3098_; lean_object* v_newDecls_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; uint8_t v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; uint8_t v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; uint8_t v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; uint8_t v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; uint8_t v___y_3219_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; uint8_t v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; uint8_t v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; uint8_t v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; uint8_t v___y_3392_; lean_object* v___y_3393_; lean_object* v___x_3403_; lean_object* v___x_3404_; uint8_t v___x_3405_; uint8_t v___y_3407_; uint8_t v___x_3501_; 
v___x_2929_ = lean_obj_once(&l_main___closed__3, &l_main___closed__3_once, _init_l_main___closed__3);
v___x_2930_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2931_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_2932_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2933_ = lean_obj_once(&l_main___closed__8, &l_main___closed__8_once, _init_l_main___closed__8);
v___x_2934_ = lean_obj_once(&l_main___closed__9, &l_main___closed__9_once, _init_l_main___closed__9);
v___x_2935_ = lean_box(1);
v___x_2936_ = ((lean_object*)(l_main___closed__10));
v___x_2937_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_2938_ = 1;
v___x_2939_ = l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(v_snd_2925_, v___x_2937_, v___x_2938_);
v___x_2940_ = l_Lean_maxHeartbeats;
v___x_2941_ = lean_unsigned_to_nat(0u);
v___x_2942_ = l_Lean_Option_set___at___00main_spec__3(v___x_2939_, v___x_2940_, v___x_2941_);
v___x_3240_ = ((lean_object*)(l_main___closed__20));
lean_inc(v_name_2911_);
v___x_3241_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3241_, 0, v_name_2911_);
lean_ctor_set_uint8(v___x_3241_, sizeof(void*)*1, v___x_2938_);
lean_ctor_set_uint8(v___x_3241_, sizeof(void*)*1 + 1, v___x_2938_);
lean_ctor_set_uint8(v___x_3241_, sizeof(void*)*1 + 2, v___x_2938_);
v___x_3242_ = lean_unsigned_to_nat(1u);
v___x_3403_ = lean_mk_empty_array_with_capacity(v___x_3242_);
v___x_3404_ = lean_array_push(v___x_3403_, v___x_3241_);
v___x_3405_ = 2;
v___x_3501_ = lean_uint8_once(&l_main___closed__36, &l_main___closed__36_once, _init_l_main___closed__36);
if (v___x_3501_ == 0)
{
v___y_3407_ = v___x_2938_;
goto v___jp_3406_;
}
else
{
v___y_3407_ = v___x_2913_;
goto v___jp_3406_;
}
v___jp_2943_:
{
lean_object* v___x_2964_; lean_object* v_messages_2965_; lean_object* v_env_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_3067_; 
v___x_2964_ = lean_st_ref_get(v___y_2960_);
lean_dec(v___y_2960_);
v_messages_2965_ = lean_ctor_get(v___x_2964_, 6);
v_env_2966_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_3067_ == 0)
{
lean_object* v_unused_3068_; lean_object* v_unused_3069_; lean_object* v_unused_3070_; lean_object* v_unused_3071_; lean_object* v_unused_3072_; lean_object* v_unused_3073_; lean_object* v_unused_3074_; lean_object* v_unused_3075_; 
v_unused_3068_ = lean_ctor_get(v___x_2964_, 9);
lean_dec(v_unused_3068_);
v_unused_3069_ = lean_ctor_get(v___x_2964_, 8);
lean_dec(v_unused_3069_);
v_unused_3070_ = lean_ctor_get(v___x_2964_, 7);
lean_dec(v_unused_3070_);
v_unused_3071_ = lean_ctor_get(v___x_2964_, 5);
lean_dec(v_unused_3071_);
v_unused_3072_ = lean_ctor_get(v___x_2964_, 4);
lean_dec(v_unused_3072_);
v_unused_3073_ = lean_ctor_get(v___x_2964_, 3);
lean_dec(v_unused_3073_);
v_unused_3074_ = lean_ctor_get(v___x_2964_, 2);
lean_dec(v_unused_3074_);
v_unused_3075_ = lean_ctor_get(v___x_2964_, 1);
lean_dec(v_unused_3075_);
v___x_2968_ = v___x_2964_;
v_isShared_2969_ = v_isSharedCheck_3067_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_messages_2965_);
lean_inc(v_env_2966_);
lean_dec(v___x_2964_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_3067_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v_unreported_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
v_unreported_2970_ = lean_ctor_get(v_messages_2965_, 1);
v___x_2971_ = lean_box(0);
v___x_2972_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_unreported_2970_, v___x_2971_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_3057_; 
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_3057_ == 0)
{
lean_object* v_unused_3058_; 
v_unused_3058_ = lean_ctor_get(v___x_2972_, 0);
lean_dec(v_unused_3058_);
v___x_2974_ = v___x_2972_;
v_isShared_2975_ = v_isSharedCheck_3057_;
goto v_resetjp_2973_;
}
else
{
lean_dec(v___x_2972_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_3057_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
uint8_t v___x_2976_; 
v___x_2976_ = l_Lean_MessageLog_hasErrors(v_messages_2965_);
lean_dec_ref(v_messages_2965_);
if (v___x_2976_ == 0)
{
lean_object* v___x_2977_; 
lean_del_object(v___x_2974_);
lean_inc_ref(v_env_2966_);
v___x_2977_ = l___private_LeanIR_0__mkIRData(v_env_2966_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_a_2978_);
lean_dec_ref(v___x_2977_);
v___x_2979_ = l_Lean_Environment_mainModule(v_env_2966_);
v___x_2980_ = ((lean_object*)(l_main___closed__12));
v___x_2981_ = l_Lean_Name_append(v___x_2979_, v___x_2980_);
lean_inc(v_head_2903_);
v___x_2982_ = l_Lean_saveModuleData(v_head_2903_, v___x_2981_, v_a_2978_);
lean_dec(v___x_2981_);
if (lean_obj_tag(v___x_2982_) == 0)
{
uint8_t v___x_2983_; lean_object* v___x_2984_; 
lean_dec_ref(v___x_2982_);
v___x_2983_ = 1;
v___x_2984_ = lean_io_prim_handle_mk(v_head_2904_, v___x_2983_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v_a_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2990_; 
lean_dec(v_head_2904_);
v_a_2985_ = lean_ctor_get(v___x_2984_, 0);
lean_inc(v_a_2985_);
lean_dec_ref(v___x_2984_);
v___x_2986_ = ((lean_object*)(l_main___closed__13));
v___x_2987_ = l_Lean_Options_empty;
v___x_2988_ = lean_obj_once(&l_main___closed__14, &l_main___closed__14_once, _init_l_main___closed__14);
lean_inc_ref(v___y_2962_);
lean_inc_ref(v___y_2954_);
lean_inc_ref(v___y_2961_);
lean_inc_ref(v___y_2959_);
lean_inc_ref(v___y_2955_);
lean_inc_ref(v___y_2958_);
lean_inc_ref(v___y_2963_);
lean_inc(v___y_2953_);
lean_inc_ref(v_env_2966_);
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 9, v___y_2962_);
lean_ctor_set(v___x_2968_, 8, v___y_2954_);
lean_ctor_set(v___x_2968_, 7, v___y_2961_);
lean_ctor_set(v___x_2968_, 6, v___y_2959_);
lean_ctor_set(v___x_2968_, 5, v___y_2955_);
lean_ctor_set(v___x_2968_, 4, v___y_2958_);
lean_ctor_set(v___x_2968_, 3, v___y_2956_);
lean_ctor_set(v___x_2968_, 2, v___y_2963_);
lean_ctor_set(v___x_2968_, 1, v___y_2953_);
v___x_2990_ = v___x_2968_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_env_2966_);
lean_ctor_set(v_reuseFailAlloc_3014_, 1, v___y_2953_);
lean_ctor_set(v_reuseFailAlloc_3014_, 2, v___y_2963_);
lean_ctor_set(v_reuseFailAlloc_3014_, 3, v___y_2956_);
lean_ctor_set(v_reuseFailAlloc_3014_, 4, v___y_2958_);
lean_ctor_set(v_reuseFailAlloc_3014_, 5, v___y_2955_);
lean_ctor_set(v_reuseFailAlloc_3014_, 6, v___y_2959_);
lean_ctor_set(v_reuseFailAlloc_3014_, 7, v___y_2961_);
lean_ctor_set(v_reuseFailAlloc_3014_, 8, v___y_2954_);
lean_ctor_set(v_reuseFailAlloc_3014_, 9, v___y_2962_);
v___x_2990_ = v_reuseFailAlloc_3014_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___f_2993_; lean_object* v___x_2994_; 
v___x_2991_ = lean_box(v___x_2913_);
v___x_2992_ = lean_box(v___y_2947_);
lean_inc(v___y_2950_);
lean_inc(v___y_2949_);
lean_inc(v___y_2945_);
lean_inc_ref(v___y_2952_);
lean_inc_ref(v___y_2946_);
lean_inc(v___y_2951_);
v___f_2993_ = lean_alloc_closure((void*)(l_main___lam__1___boxed), 18, 17);
lean_closure_set(v___f_2993_, 0, v___x_2990_);
lean_closure_set(v___f_2993_, 1, v___y_2951_);
lean_closure_set(v___f_2993_, 2, v___x_2987_);
lean_closure_set(v___f_2993_, 3, v_name_2911_);
lean_closure_set(v___f_2993_, 4, v_a_2985_);
lean_closure_set(v___f_2993_, 5, v___y_2946_);
lean_closure_set(v___f_2993_, 6, v_head_2903_);
lean_closure_set(v___f_2993_, 7, v___y_2952_);
lean_closure_set(v___f_2993_, 8, v___x_2941_);
lean_closure_set(v___f_2993_, 9, v___y_2945_);
lean_closure_set(v___f_2993_, 10, v___y_2948_);
lean_closure_set(v___f_2993_, 11, v___y_2944_);
lean_closure_set(v___f_2993_, 12, v___x_2988_);
lean_closure_set(v___f_2993_, 13, v___y_2949_);
lean_closure_set(v___f_2993_, 14, v___y_2950_);
lean_closure_set(v___f_2993_, 15, v___x_2991_);
lean_closure_set(v___f_2993_, 16, v___x_2992_);
v___x_2994_ = l_Lean_profileitIOUnsafe___redArg(v___x_2986_, v___x_2942_, v___f_2993_, v___y_2957_);
lean_dec_ref(v___x_2942_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v___x_2995_; uint8_t v___x_2996_; 
lean_dec_ref(v___x_2994_);
v___x_2995_ = lean_display_cumulative_profiling_times();
v___x_2996_ = lean_unbox(v_fst_2924_);
lean_dec(v_fst_2924_);
if (v___x_2996_ == 0)
{
lean_dec_ref(v_env_2966_);
goto v___jp_2897_;
}
else
{
lean_object* v___x_2997_; 
v___x_2997_ = l_Lean_Environment_displayStats(v_env_2966_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_dec_ref(v___x_2997_);
goto v___jp_2897_;
}
else
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2997_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2997_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
}
else
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3013_; 
lean_dec_ref(v_env_2966_);
lean_dec(v_fst_2924_);
v_a_3006_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3008_ = v___x_2994_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_2994_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3011_; 
if (v_isShared_3009_ == 0)
{
v___x_3011_ = v___x_3008_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
}
else
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
lean_dec_ref(v___x_2984_);
lean_del_object(v___x_2968_);
lean_dec_ref(v_env_2966_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2948_);
lean_dec(v___y_2944_);
lean_dec_ref(v___x_2942_);
lean_dec(v_fst_2924_);
lean_dec(v_name_2911_);
lean_dec(v_head_2903_);
v___x_3015_ = ((lean_object*)(l_main___closed__15));
v___x_3016_ = lean_string_append(v___x_3015_, v_head_2904_);
lean_dec(v_head_2904_);
v___x_3017_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__5));
v___x_3018_ = lean_string_append(v___x_3016_, v___x_3017_);
v___x_3019_ = l_IO_eprintln___at___00main_spec__6(v___x_3018_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3027_; 
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3027_ == 0)
{
lean_object* v_unused_3028_; 
v_unused_3028_ = lean_ctor_get(v___x_3019_, 0);
lean_dec(v_unused_3028_);
v___x_3021_ = v___x_3019_;
v_isShared_3022_ = v_isSharedCheck_3027_;
goto v_resetjp_3020_;
}
else
{
lean_dec(v___x_3019_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3027_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3023_; lean_object* v___x_3025_; 
v___x_3023_ = l_main___boxed__const__1;
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 0, v___x_3023_);
v___x_3025_ = v___x_3021_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v___x_3023_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
else
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
v_a_3029_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_3019_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3019_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3029_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_del_object(v___x_2968_);
lean_dec_ref(v_env_2966_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2948_);
lean_dec(v___y_2944_);
lean_dec_ref(v___x_2942_);
lean_dec(v_fst_2924_);
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v_a_3037_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_2982_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_2982_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
else
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3052_; 
lean_del_object(v___x_2968_);
lean_dec_ref(v_env_2966_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2948_);
lean_dec(v___y_2944_);
lean_dec_ref(v___x_2942_);
lean_dec(v_fst_2924_);
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v_a_3045_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3047_ = v___x_2977_;
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_2977_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3050_; 
if (v_isShared_3048_ == 0)
{
v___x_3050_ = v___x_3047_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_a_3045_);
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
lean_object* v___x_3053_; lean_object* v___x_3055_; 
lean_del_object(v___x_2968_);
lean_dec_ref(v_env_2966_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2948_);
lean_dec(v___y_2944_);
lean_dec_ref(v___x_2942_);
lean_dec(v_fst_2924_);
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v___x_3053_ = l_main___boxed__const__1;
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 0, v___x_3053_);
v___x_3055_ = v___x_2974_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v___x_3053_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
else
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3066_; 
lean_del_object(v___x_2968_);
lean_dec_ref(v_env_2966_);
lean_dec_ref(v_messages_2965_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2948_);
lean_dec(v___y_2944_);
lean_dec_ref(v___x_2942_);
lean_dec(v_fst_2924_);
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v_a_3059_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3061_ = v___x_2972_;
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_2972_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3064_; 
if (v_isShared_3062_ == 0)
{
v___x_3064_ = v___x_3061_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_a_3059_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
}
v___jp_3076_:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; size_t v_sz_3112_; size_t v___x_3113_; lean_object* v___x_3114_; 
lean_inc_ref(v___y_3086_);
v___x_3109_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3109_, 0, v___y_3108_);
lean_ctor_set(v___x_3109_, 1, v_nextMacroScope_3092_);
lean_ctor_set(v___x_3109_, 2, v_ngen_3093_);
lean_ctor_set(v___x_3109_, 3, v_auxDeclNGen_3094_);
lean_ctor_set(v___x_3109_, 4, v_traceState_3095_);
lean_ctor_set(v___x_3109_, 5, v___y_3086_);
lean_ctor_set(v___x_3109_, 6, v_messages_3096_);
lean_ctor_set(v___x_3109_, 7, v_infoState_3097_);
lean_ctor_set(v___x_3109_, 8, v_snapshotTasks_3098_);
lean_ctor_set(v___x_3109_, 9, v_newDecls_3099_);
v___x_3110_ = lean_st_ref_set(v___y_3091_, v___x_3109_);
v___x_3111_ = lean_box(0);
v_sz_3112_ = lean_array_size(v___y_3104_);
v___x_3113_ = ((size_t)0ULL);
v___x_3114_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v___y_3104_, v_sz_3112_, v___x_3113_, v___x_3111_, v___y_3087_, v___y_3091_);
lean_dec_ref(v___y_3104_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_dec_ref(v___x_3114_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3087_);
v___y_2944_ = v___y_3078_;
v___y_2945_ = v___y_3077_;
v___y_2946_ = v___y_3079_;
v___y_2947_ = v___y_3081_;
v___y_2948_ = v___y_3080_;
v___y_2949_ = v___y_3082_;
v___y_2950_ = v___y_3083_;
v___y_2951_ = v___y_3084_;
v___y_2952_ = v___y_3085_;
v___y_2953_ = v___y_3100_;
v___y_2954_ = v___y_3088_;
v___y_2955_ = v___y_3086_;
v___y_2956_ = v___y_3101_;
v___y_2957_ = v___y_3089_;
v___y_2958_ = v___y_3102_;
v___y_2959_ = v___y_3103_;
v___y_2960_ = v___y_3090_;
v___y_2961_ = v___y_3105_;
v___y_2962_ = v___y_3107_;
v___y_2963_ = v___y_3106_;
goto v___jp_2943_;
}
else
{
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_dec_ref(v___x_3114_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3087_);
v___y_2944_ = v___y_3078_;
v___y_2945_ = v___y_3077_;
v___y_2946_ = v___y_3079_;
v___y_2947_ = v___y_3081_;
v___y_2948_ = v___y_3080_;
v___y_2949_ = v___y_3082_;
v___y_2950_ = v___y_3083_;
v___y_2951_ = v___y_3084_;
v___y_2952_ = v___y_3085_;
v___y_2953_ = v___y_3100_;
v___y_2954_ = v___y_3088_;
v___y_2955_ = v___y_3086_;
v___y_2956_ = v___y_3101_;
v___y_2957_ = v___y_3089_;
v___y_2958_ = v___y_3102_;
v___y_2959_ = v___y_3103_;
v___y_2960_ = v___y_3090_;
v___y_2961_ = v___y_3105_;
v___y_2962_ = v___y_3107_;
v___y_2963_ = v___y_3106_;
goto v___jp_2943_;
}
else
{
lean_object* v_a_3115_; uint8_t v___x_3116_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_a_3115_);
lean_dec_ref(v___x_3114_);
v___x_3116_ = l_Lean_Exception_isInterrupt(v_a_3115_);
if (v___x_3116_ == 0)
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3117_ = l_Lean_Exception_toMessageData(v_a_3115_);
v___x_3118_ = l_Lean_logError___at___00main_spec__14(v___x_3117_, v___y_3087_, v___y_3091_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3087_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_dec_ref(v___x_3118_);
v___y_2944_ = v___y_3078_;
v___y_2945_ = v___y_3077_;
v___y_2946_ = v___y_3079_;
v___y_2947_ = v___y_3081_;
v___y_2948_ = v___y_3080_;
v___y_2949_ = v___y_3082_;
v___y_2950_ = v___y_3083_;
v___y_2951_ = v___y_3084_;
v___y_2952_ = v___y_3085_;
v___y_2953_ = v___y_3100_;
v___y_2954_ = v___y_3088_;
v___y_2955_ = v___y_3086_;
v___y_2956_ = v___y_3101_;
v___y_2957_ = v___y_3089_;
v___y_2958_ = v___y_3102_;
v___y_2959_ = v___y_3103_;
v___y_2960_ = v___y_3090_;
v___y_2961_ = v___y_3105_;
v___y_2962_ = v___y_3107_;
v___y_2963_ = v___y_3106_;
goto v___jp_2943_;
}
else
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
lean_dec_ref(v___x_3118_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3090_);
lean_dec(v___y_3089_);
lean_dec(v___y_3080_);
lean_dec(v___y_3078_);
lean_dec_ref(v___x_2942_);
lean_dec(v_fst_2924_);
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v___x_3119_ = lean_obj_once(&l_main___closed__19, &l_main___closed__19_once, _init_l_main___closed__19);
v___x_3120_ = l_panic___at___00main_spec__5(v___x_3119_);
return v___x_3120_;
}
}
else
{
lean_dec(v_a_3115_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3087_);
v___y_2944_ = v___y_3078_;
v___y_2945_ = v___y_3077_;
v___y_2946_ = v___y_3079_;
v___y_2947_ = v___y_3081_;
v___y_2948_ = v___y_3080_;
v___y_2949_ = v___y_3082_;
v___y_2950_ = v___y_3083_;
v___y_2951_ = v___y_3084_;
v___y_2952_ = v___y_3085_;
v___y_2953_ = v___y_3100_;
v___y_2954_ = v___y_3088_;
v___y_2955_ = v___y_3086_;
v___y_2956_ = v___y_3101_;
v___y_2957_ = v___y_3089_;
v___y_2958_ = v___y_3102_;
v___y_2959_ = v___y_3103_;
v___y_2960_ = v___y_3090_;
v___y_2961_ = v___y_3105_;
v___y_2962_ = v___y_3107_;
v___y_2963_ = v___y_3106_;
goto v___jp_2943_;
}
}
}
}
v___jp_3121_:
{
lean_object* v___x_3147_; lean_object* v_fileName_3148_; lean_object* v_fileMap_3149_; lean_object* v_currRecDepth_3150_; lean_object* v_ref_3151_; lean_object* v_currNamespace_3152_; lean_object* v_openDecls_3153_; lean_object* v_initHeartbeats_3154_; lean_object* v_maxHeartbeats_3155_; lean_object* v_quotContext_3156_; lean_object* v_currMacroScope_3157_; lean_object* v_cancelTk_x3f_3158_; uint8_t v_suppressElabErrors_3159_; lean_object* v_inheritedTraceOptions_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3191_; 
v___x_3147_ = lean_st_ref_take(v___y_3146_);
v_fileName_3148_ = lean_ctor_get(v___y_3145_, 0);
v_fileMap_3149_ = lean_ctor_get(v___y_3145_, 1);
v_currRecDepth_3150_ = lean_ctor_get(v___y_3145_, 3);
v_ref_3151_ = lean_ctor_get(v___y_3145_, 5);
v_currNamespace_3152_ = lean_ctor_get(v___y_3145_, 6);
v_openDecls_3153_ = lean_ctor_get(v___y_3145_, 7);
v_initHeartbeats_3154_ = lean_ctor_get(v___y_3145_, 8);
v_maxHeartbeats_3155_ = lean_ctor_get(v___y_3145_, 9);
v_quotContext_3156_ = lean_ctor_get(v___y_3145_, 10);
v_currMacroScope_3157_ = lean_ctor_get(v___y_3145_, 11);
v_cancelTk_x3f_3158_ = lean_ctor_get(v___y_3145_, 12);
v_suppressElabErrors_3159_ = lean_ctor_get_uint8(v___y_3145_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3160_ = lean_ctor_get(v___y_3145_, 13);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___y_3145_);
if (v_isSharedCheck_3191_ == 0)
{
lean_object* v_unused_3192_; lean_object* v_unused_3193_; 
v_unused_3192_ = lean_ctor_get(v___y_3145_, 4);
lean_dec(v_unused_3192_);
v_unused_3193_ = lean_ctor_get(v___y_3145_, 2);
lean_dec(v_unused_3193_);
v___x_3162_ = v___y_3145_;
v_isShared_3163_ = v_isSharedCheck_3191_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_inheritedTraceOptions_3160_);
lean_inc(v_cancelTk_x3f_3158_);
lean_inc(v_currMacroScope_3157_);
lean_inc(v_quotContext_3156_);
lean_inc(v_maxHeartbeats_3155_);
lean_inc(v_initHeartbeats_3154_);
lean_inc(v_openDecls_3153_);
lean_inc(v_currNamespace_3152_);
lean_inc(v_ref_3151_);
lean_inc(v_currRecDepth_3150_);
lean_inc(v_fileMap_3149_);
lean_inc(v_fileName_3148_);
lean_dec(v___y_3145_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3191_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v_env_3164_; lean_object* v_nextMacroScope_3165_; lean_object* v_ngen_3166_; lean_object* v_auxDeclNGen_3167_; lean_object* v_traceState_3168_; lean_object* v_messages_3169_; lean_object* v_infoState_3170_; lean_object* v_snapshotTasks_3171_; lean_object* v_newDecls_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3176_; 
v_env_3164_ = lean_ctor_get(v___x_3147_, 0);
lean_inc_ref(v_env_3164_);
v_nextMacroScope_3165_ = lean_ctor_get(v___x_3147_, 1);
lean_inc(v_nextMacroScope_3165_);
v_ngen_3166_ = lean_ctor_get(v___x_3147_, 2);
lean_inc_ref(v_ngen_3166_);
v_auxDeclNGen_3167_ = lean_ctor_get(v___x_3147_, 3);
lean_inc_ref(v_auxDeclNGen_3167_);
v_traceState_3168_ = lean_ctor_get(v___x_3147_, 4);
lean_inc_ref(v_traceState_3168_);
v_messages_3169_ = lean_ctor_get(v___x_3147_, 6);
lean_inc_ref(v_messages_3169_);
v_infoState_3170_ = lean_ctor_get(v___x_3147_, 7);
lean_inc_ref(v_infoState_3170_);
v_snapshotTasks_3171_ = lean_ctor_get(v___x_3147_, 8);
lean_inc_ref(v_snapshotTasks_3171_);
v_newDecls_3172_ = lean_ctor_get(v___x_3147_, 9);
lean_inc_ref(v_newDecls_3172_);
lean_dec(v___x_3147_);
v___x_3173_ = l_Lean_maxRecDepth;
v___x_3174_ = l_Lean_Option_get___at___00main_spec__9(v___x_2942_, v___x_3173_);
lean_inc_ref(v___x_2942_);
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 4, v___x_3174_);
lean_ctor_set(v___x_3162_, 2, v___x_2942_);
v___x_3176_ = v___x_3162_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_fileName_3148_);
lean_ctor_set(v_reuseFailAlloc_3190_, 1, v_fileMap_3149_);
lean_ctor_set(v_reuseFailAlloc_3190_, 2, v___x_2942_);
lean_ctor_set(v_reuseFailAlloc_3190_, 3, v_currRecDepth_3150_);
lean_ctor_set(v_reuseFailAlloc_3190_, 4, v___x_3174_);
lean_ctor_set(v_reuseFailAlloc_3190_, 5, v_ref_3151_);
lean_ctor_set(v_reuseFailAlloc_3190_, 6, v_currNamespace_3152_);
lean_ctor_set(v_reuseFailAlloc_3190_, 7, v_openDecls_3153_);
lean_ctor_set(v_reuseFailAlloc_3190_, 8, v_initHeartbeats_3154_);
lean_ctor_set(v_reuseFailAlloc_3190_, 9, v_maxHeartbeats_3155_);
lean_ctor_set(v_reuseFailAlloc_3190_, 10, v_quotContext_3156_);
lean_ctor_set(v_reuseFailAlloc_3190_, 11, v_currMacroScope_3157_);
lean_ctor_set(v_reuseFailAlloc_3190_, 12, v_cancelTk_x3f_3158_);
lean_ctor_set(v_reuseFailAlloc_3190_, 13, v_inheritedTraceOptions_3160_);
lean_ctor_set_uint8(v_reuseFailAlloc_3190_, sizeof(void*)*14 + 1, v_suppressElabErrors_3159_);
v___x_3176_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
lean_object* v___x_3177_; uint8_t v___x_3178_; 
lean_ctor_set_uint8(v___x_3176_, sizeof(void*)*14, v___y_3135_);
v___x_3177_ = lean_array_get_size(v___y_3141_);
v___x_3178_ = lean_nat_dec_lt(v___x_2941_, v___x_3177_);
if (v___x_3178_ == 0)
{
lean_object* v___x_3179_; 
lean_inc_ref(v___y_3137_);
v___x_3179_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3137_, v_env_3164_, v___x_2935_);
v___y_3077_ = v___y_3123_;
v___y_3078_ = v___y_3122_;
v___y_3079_ = v___y_3124_;
v___y_3080_ = v___y_3126_;
v___y_3081_ = v___y_3125_;
v___y_3082_ = v___y_3127_;
v___y_3083_ = v___y_3128_;
v___y_3084_ = v___y_3129_;
v___y_3085_ = v___y_3130_;
v___y_3086_ = v___y_3131_;
v___y_3087_ = v___x_3176_;
v___y_3088_ = v___y_3132_;
v___y_3089_ = v___y_3133_;
v___y_3090_ = v___y_3134_;
v___y_3091_ = v___y_3146_;
v_nextMacroScope_3092_ = v_nextMacroScope_3165_;
v_ngen_3093_ = v_ngen_3166_;
v_auxDeclNGen_3094_ = v_auxDeclNGen_3167_;
v_traceState_3095_ = v_traceState_3168_;
v_messages_3096_ = v_messages_3169_;
v_infoState_3097_ = v_infoState_3170_;
v_snapshotTasks_3098_ = v_snapshotTasks_3171_;
v_newDecls_3099_ = v_newDecls_3172_;
v___y_3100_ = v___y_3136_;
v___y_3101_ = v___y_3138_;
v___y_3102_ = v___y_3139_;
v___y_3103_ = v___y_3140_;
v___y_3104_ = v___y_3141_;
v___y_3105_ = v___y_3142_;
v___y_3106_ = v___y_3143_;
v___y_3107_ = v___y_3144_;
v___y_3108_ = v___x_3179_;
goto v___jp_3076_;
}
else
{
uint8_t v___x_3180_; 
v___x_3180_ = lean_nat_dec_le(v___x_3177_, v___x_3177_);
if (v___x_3180_ == 0)
{
if (v___x_3178_ == 0)
{
lean_object* v___x_3181_; 
lean_inc_ref(v___y_3137_);
v___x_3181_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3137_, v_env_3164_, v___x_2935_);
v___y_3077_ = v___y_3123_;
v___y_3078_ = v___y_3122_;
v___y_3079_ = v___y_3124_;
v___y_3080_ = v___y_3126_;
v___y_3081_ = v___y_3125_;
v___y_3082_ = v___y_3127_;
v___y_3083_ = v___y_3128_;
v___y_3084_ = v___y_3129_;
v___y_3085_ = v___y_3130_;
v___y_3086_ = v___y_3131_;
v___y_3087_ = v___x_3176_;
v___y_3088_ = v___y_3132_;
v___y_3089_ = v___y_3133_;
v___y_3090_ = v___y_3134_;
v___y_3091_ = v___y_3146_;
v_nextMacroScope_3092_ = v_nextMacroScope_3165_;
v_ngen_3093_ = v_ngen_3166_;
v_auxDeclNGen_3094_ = v_auxDeclNGen_3167_;
v_traceState_3095_ = v_traceState_3168_;
v_messages_3096_ = v_messages_3169_;
v_infoState_3097_ = v_infoState_3170_;
v_snapshotTasks_3098_ = v_snapshotTasks_3171_;
v_newDecls_3099_ = v_newDecls_3172_;
v___y_3100_ = v___y_3136_;
v___y_3101_ = v___y_3138_;
v___y_3102_ = v___y_3139_;
v___y_3103_ = v___y_3140_;
v___y_3104_ = v___y_3141_;
v___y_3105_ = v___y_3142_;
v___y_3106_ = v___y_3143_;
v___y_3107_ = v___y_3144_;
v___y_3108_ = v___x_3181_;
goto v___jp_3076_;
}
else
{
size_t v___x_3182_; size_t v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3182_ = ((size_t)0ULL);
v___x_3183_ = lean_usize_of_nat(v___x_3177_);
v___x_3184_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3141_, v___x_3182_, v___x_3183_, v___x_2935_);
lean_inc_ref(v___y_3137_);
v___x_3185_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3137_, v_env_3164_, v___x_3184_);
v___y_3077_ = v___y_3123_;
v___y_3078_ = v___y_3122_;
v___y_3079_ = v___y_3124_;
v___y_3080_ = v___y_3126_;
v___y_3081_ = v___y_3125_;
v___y_3082_ = v___y_3127_;
v___y_3083_ = v___y_3128_;
v___y_3084_ = v___y_3129_;
v___y_3085_ = v___y_3130_;
v___y_3086_ = v___y_3131_;
v___y_3087_ = v___x_3176_;
v___y_3088_ = v___y_3132_;
v___y_3089_ = v___y_3133_;
v___y_3090_ = v___y_3134_;
v___y_3091_ = v___y_3146_;
v_nextMacroScope_3092_ = v_nextMacroScope_3165_;
v_ngen_3093_ = v_ngen_3166_;
v_auxDeclNGen_3094_ = v_auxDeclNGen_3167_;
v_traceState_3095_ = v_traceState_3168_;
v_messages_3096_ = v_messages_3169_;
v_infoState_3097_ = v_infoState_3170_;
v_snapshotTasks_3098_ = v_snapshotTasks_3171_;
v_newDecls_3099_ = v_newDecls_3172_;
v___y_3100_ = v___y_3136_;
v___y_3101_ = v___y_3138_;
v___y_3102_ = v___y_3139_;
v___y_3103_ = v___y_3140_;
v___y_3104_ = v___y_3141_;
v___y_3105_ = v___y_3142_;
v___y_3106_ = v___y_3143_;
v___y_3107_ = v___y_3144_;
v___y_3108_ = v___x_3185_;
goto v___jp_3076_;
}
}
else
{
size_t v___x_3186_; size_t v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3186_ = ((size_t)0ULL);
v___x_3187_ = lean_usize_of_nat(v___x_3177_);
v___x_3188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3141_, v___x_3186_, v___x_3187_, v___x_2935_);
lean_inc_ref(v___y_3137_);
v___x_3189_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3137_, v_env_3164_, v___x_3188_);
v___y_3077_ = v___y_3123_;
v___y_3078_ = v___y_3122_;
v___y_3079_ = v___y_3124_;
v___y_3080_ = v___y_3126_;
v___y_3081_ = v___y_3125_;
v___y_3082_ = v___y_3127_;
v___y_3083_ = v___y_3128_;
v___y_3084_ = v___y_3129_;
v___y_3085_ = v___y_3130_;
v___y_3086_ = v___y_3131_;
v___y_3087_ = v___x_3176_;
v___y_3088_ = v___y_3132_;
v___y_3089_ = v___y_3133_;
v___y_3090_ = v___y_3134_;
v___y_3091_ = v___y_3146_;
v_nextMacroScope_3092_ = v_nextMacroScope_3165_;
v_ngen_3093_ = v_ngen_3166_;
v_auxDeclNGen_3094_ = v_auxDeclNGen_3167_;
v_traceState_3095_ = v_traceState_3168_;
v_messages_3096_ = v_messages_3169_;
v_infoState_3097_ = v_infoState_3170_;
v_snapshotTasks_3098_ = v_snapshotTasks_3171_;
v_newDecls_3099_ = v_newDecls_3172_;
v___y_3100_ = v___y_3136_;
v___y_3101_ = v___y_3138_;
v___y_3102_ = v___y_3139_;
v___y_3103_ = v___y_3140_;
v___y_3104_ = v___y_3141_;
v___y_3105_ = v___y_3142_;
v___y_3106_ = v___y_3143_;
v___y_3107_ = v___y_3144_;
v___y_3108_ = v___x_3189_;
goto v___jp_3076_;
}
}
}
}
}
v___jp_3194_:
{
if (v___y_3219_ == 0)
{
lean_object* v___x_3220_; lean_object* v_env_3221_; lean_object* v_nextMacroScope_3222_; lean_object* v_ngen_3223_; lean_object* v_auxDeclNGen_3224_; lean_object* v_traceState_3225_; lean_object* v_messages_3226_; lean_object* v_infoState_3227_; lean_object* v_snapshotTasks_3228_; lean_object* v_newDecls_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3238_; 
v___x_3220_ = lean_st_ref_take(v___y_3207_);
v_env_3221_ = lean_ctor_get(v___x_3220_, 0);
v_nextMacroScope_3222_ = lean_ctor_get(v___x_3220_, 1);
v_ngen_3223_ = lean_ctor_get(v___x_3220_, 2);
v_auxDeclNGen_3224_ = lean_ctor_get(v___x_3220_, 3);
v_traceState_3225_ = lean_ctor_get(v___x_3220_, 4);
v_messages_3226_ = lean_ctor_get(v___x_3220_, 6);
v_infoState_3227_ = lean_ctor_get(v___x_3220_, 7);
v_snapshotTasks_3228_ = lean_ctor_get(v___x_3220_, 8);
v_newDecls_3229_ = lean_ctor_get(v___x_3220_, 9);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3238_ == 0)
{
lean_object* v_unused_3239_; 
v_unused_3239_ = lean_ctor_get(v___x_3220_, 5);
lean_dec(v_unused_3239_);
v___x_3231_ = v___x_3220_;
v_isShared_3232_ = v_isSharedCheck_3238_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_newDecls_3229_);
lean_inc(v_snapshotTasks_3228_);
lean_inc(v_infoState_3227_);
lean_inc(v_messages_3226_);
lean_inc(v_traceState_3225_);
lean_inc(v_auxDeclNGen_3224_);
lean_inc(v_ngen_3223_);
lean_inc(v_nextMacroScope_3222_);
lean_inc(v_env_3221_);
lean_dec(v___x_3220_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3238_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3233_; lean_object* v___x_3235_; 
v___x_3233_ = l_Lean_Kernel_enableDiag(v_env_3221_, v___y_3209_);
lean_inc_ref(v___y_3204_);
if (v_isShared_3232_ == 0)
{
lean_ctor_set(v___x_3231_, 5, v___y_3204_);
lean_ctor_set(v___x_3231_, 0, v___x_3233_);
v___x_3235_ = v___x_3231_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3233_);
lean_ctor_set(v_reuseFailAlloc_3237_, 1, v_nextMacroScope_3222_);
lean_ctor_set(v_reuseFailAlloc_3237_, 2, v_ngen_3223_);
lean_ctor_set(v_reuseFailAlloc_3237_, 3, v_auxDeclNGen_3224_);
lean_ctor_set(v_reuseFailAlloc_3237_, 4, v_traceState_3225_);
lean_ctor_set(v_reuseFailAlloc_3237_, 5, v___y_3204_);
lean_ctor_set(v_reuseFailAlloc_3237_, 6, v_messages_3226_);
lean_ctor_set(v_reuseFailAlloc_3237_, 7, v_infoState_3227_);
lean_ctor_set(v_reuseFailAlloc_3237_, 8, v_snapshotTasks_3228_);
lean_ctor_set(v_reuseFailAlloc_3237_, 9, v_newDecls_3229_);
v___x_3235_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
lean_object* v___x_3236_; 
v___x_3236_ = lean_st_ref_set(v___y_3207_, v___x_3235_);
lean_inc(v___y_3207_);
v___y_3122_ = v___y_3196_;
v___y_3123_ = v___y_3195_;
v___y_3124_ = v___y_3197_;
v___y_3125_ = v___y_3199_;
v___y_3126_ = v___y_3198_;
v___y_3127_ = v___y_3200_;
v___y_3128_ = v___y_3201_;
v___y_3129_ = v___y_3202_;
v___y_3130_ = v___y_3203_;
v___y_3131_ = v___y_3204_;
v___y_3132_ = v___y_3205_;
v___y_3133_ = v___y_3206_;
v___y_3134_ = v___y_3207_;
v___y_3135_ = v___y_3209_;
v___y_3136_ = v___y_3210_;
v___y_3137_ = v___y_3211_;
v___y_3138_ = v___y_3212_;
v___y_3139_ = v___y_3213_;
v___y_3140_ = v___y_3214_;
v___y_3141_ = v___y_3215_;
v___y_3142_ = v___y_3216_;
v___y_3143_ = v___y_3218_;
v___y_3144_ = v___y_3217_;
v___y_3145_ = v___y_3208_;
v___y_3146_ = v___y_3207_;
goto v___jp_3121_;
}
}
}
else
{
lean_inc(v___y_3207_);
v___y_3122_ = v___y_3196_;
v___y_3123_ = v___y_3195_;
v___y_3124_ = v___y_3197_;
v___y_3125_ = v___y_3199_;
v___y_3126_ = v___y_3198_;
v___y_3127_ = v___y_3200_;
v___y_3128_ = v___y_3201_;
v___y_3129_ = v___y_3202_;
v___y_3130_ = v___y_3203_;
v___y_3131_ = v___y_3204_;
v___y_3132_ = v___y_3205_;
v___y_3133_ = v___y_3206_;
v___y_3134_ = v___y_3207_;
v___y_3135_ = v___y_3209_;
v___y_3136_ = v___y_3210_;
v___y_3137_ = v___y_3211_;
v___y_3138_ = v___y_3212_;
v___y_3139_ = v___y_3213_;
v___y_3140_ = v___y_3214_;
v___y_3141_ = v___y_3215_;
v___y_3142_ = v___y_3216_;
v___y_3143_ = v___y_3218_;
v___y_3144_ = v___y_3217_;
v___y_3145_ = v___y_3208_;
v___y_3146_ = v___y_3207_;
goto v___jp_3121_;
}
}
v___jp_3243_:
{
lean_object* v___x_3253_; 
if (v_isShared_2928_ == 0)
{
lean_ctor_set(v___x_2927_, 1, v___y_3251_);
lean_ctor_set(v___x_2927_, 0, v___y_3250_);
v___x_3253_ = v___x_2927_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___y_3250_);
lean_ctor_set(v_reuseFailAlloc_3348_, 1, v___y_3251_);
v___x_3253_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v_moduleData_3257_; lean_object* v___x_3258_; uint8_t v___x_3259_; 
v___x_3254_ = lean_box(0);
lean_inc_ref(v___y_3247_);
v___x_3255_ = l_Lean_EnvExtension_setState___redArg(v___y_3247_, v___y_3248_, v___x_3253_, v___x_3254_);
v___x_3256_ = l_Lean_Environment_header(v___x_3255_);
v_moduleData_3257_ = lean_ctor_get(v___x_3256_, 6);
lean_inc_ref(v_moduleData_3257_);
lean_dec_ref(v___x_3256_);
v___x_3258_ = lean_array_get_size(v_moduleData_3257_);
v___x_3259_ = lean_nat_dec_lt(v___y_3245_, v___x_3258_);
if (v___x_3259_ == 0)
{
lean_object* v___x_3260_; lean_object* v___x_3261_; 
lean_dec_ref(v_moduleData_3257_);
lean_dec_ref(v___x_3255_);
lean_dec(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec_ref(v___x_2942_);
lean_dec(v_fst_2924_);
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v___x_3260_ = lean_obj_once(&l_main___closed__21, &l_main___closed__21_once, _init_l_main___closed__21);
v___x_3261_ = l_panic___at___00main_spec__5(v___x_3260_);
return v___x_3261_;
}
else
{
lean_object* v_base_3262_; lean_object* v_private_3263_; lean_object* v_header_3264_; lean_object* v_serverBaseExts_3265_; lean_object* v_checked_3266_; lean_object* v_asyncConstsMap_3267_; lean_object* v_asyncCtx_x3f_3268_; lean_object* v_importRealizationCtx_x3f_3269_; lean_object* v_localRealizationCtxMap_3270_; lean_object* v_allRealizations_3271_; uint8_t v_isExporting_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3346_; 
v_base_3262_ = lean_ctor_get(v___x_3255_, 0);
lean_inc_ref(v_base_3262_);
v_private_3263_ = lean_ctor_get(v_base_3262_, 0);
lean_inc(v_private_3263_);
v_header_3264_ = lean_ctor_get(v_private_3263_, 5);
lean_inc_ref(v_header_3264_);
v_serverBaseExts_3265_ = lean_ctor_get(v___x_3255_, 1);
v_checked_3266_ = lean_ctor_get(v___x_3255_, 2);
v_asyncConstsMap_3267_ = lean_ctor_get(v___x_3255_, 3);
v_asyncCtx_x3f_3268_ = lean_ctor_get(v___x_3255_, 4);
v_importRealizationCtx_x3f_3269_ = lean_ctor_get(v___x_3255_, 5);
v_localRealizationCtxMap_3270_ = lean_ctor_get(v___x_3255_, 6);
v_allRealizations_3271_ = lean_ctor_get(v___x_3255_, 7);
v_isExporting_3272_ = lean_ctor_get_uint8(v___x_3255_, sizeof(void*)*8);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3346_ == 0)
{
lean_object* v_unused_3347_; 
v_unused_3347_ = lean_ctor_get(v___x_3255_, 0);
lean_dec(v_unused_3347_);
v___x_3274_ = v___x_3255_;
v_isShared_3275_ = v_isSharedCheck_3346_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_allRealizations_3271_);
lean_inc(v_localRealizationCtxMap_3270_);
lean_inc(v_importRealizationCtx_x3f_3269_);
lean_inc(v_asyncCtx_x3f_3268_);
lean_inc(v_asyncConstsMap_3267_);
lean_inc(v_checked_3266_);
lean_inc(v_serverBaseExts_3265_);
lean_dec(v___x_3255_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3346_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v_public_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3344_; 
v_public_3276_ = lean_ctor_get(v_base_3262_, 1);
v_isSharedCheck_3344_ = !lean_is_exclusive(v_base_3262_);
if (v_isSharedCheck_3344_ == 0)
{
lean_object* v_unused_3345_; 
v_unused_3345_ = lean_ctor_get(v_base_3262_, 0);
lean_dec(v_unused_3345_);
v___x_3278_ = v_base_3262_;
v_isShared_3279_ = v_isSharedCheck_3344_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_public_3276_);
lean_dec(v_base_3262_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3344_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v_constants_3280_; uint8_t v_quotInit_3281_; lean_object* v_diagnostics_3282_; lean_object* v_const2ModIdx_3283_; lean_object* v_extensions_3284_; lean_object* v_irBaseExts_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3342_; 
v_constants_3280_ = lean_ctor_get(v_private_3263_, 0);
v_quotInit_3281_ = lean_ctor_get_uint8(v_private_3263_, sizeof(void*)*6);
v_diagnostics_3282_ = lean_ctor_get(v_private_3263_, 1);
v_const2ModIdx_3283_ = lean_ctor_get(v_private_3263_, 2);
v_extensions_3284_ = lean_ctor_get(v_private_3263_, 3);
v_irBaseExts_3285_ = lean_ctor_get(v_private_3263_, 4);
v_isSharedCheck_3342_ = !lean_is_exclusive(v_private_3263_);
if (v_isSharedCheck_3342_ == 0)
{
lean_object* v_unused_3343_; 
v_unused_3343_ = lean_ctor_get(v_private_3263_, 5);
lean_dec(v_unused_3343_);
v___x_3287_ = v_private_3263_;
v_isShared_3288_ = v_isSharedCheck_3342_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_irBaseExts_3285_);
lean_inc(v_extensions_3284_);
lean_inc(v_const2ModIdx_3283_);
lean_inc(v_diagnostics_3282_);
lean_inc(v_constants_3280_);
lean_dec(v_private_3263_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3342_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
uint32_t v_trustLevel_3289_; lean_object* v_mainModule_3290_; uint8_t v_isModule_3291_; lean_object* v_regions_3292_; lean_object* v_modules_3293_; lean_object* v_moduleName2Idx_3294_; lean_object* v_importAllModules_3295_; lean_object* v_moduleData_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3340_; 
v_trustLevel_3289_ = lean_ctor_get_uint32(v_header_3264_, sizeof(void*)*7);
v_mainModule_3290_ = lean_ctor_get(v_header_3264_, 0);
v_isModule_3291_ = lean_ctor_get_uint8(v_header_3264_, sizeof(void*)*7 + 4);
v_regions_3292_ = lean_ctor_get(v_header_3264_, 2);
v_modules_3293_ = lean_ctor_get(v_header_3264_, 3);
v_moduleName2Idx_3294_ = lean_ctor_get(v_header_3264_, 4);
v_importAllModules_3295_ = lean_ctor_get(v_header_3264_, 5);
v_moduleData_3296_ = lean_ctor_get(v_header_3264_, 6);
v_isSharedCheck_3340_ = !lean_is_exclusive(v_header_3264_);
if (v_isSharedCheck_3340_ == 0)
{
lean_object* v_unused_3341_; 
v_unused_3341_ = lean_ctor_get(v_header_3264_, 1);
lean_dec(v_unused_3341_);
v___x_3298_ = v_header_3264_;
v_isShared_3299_ = v_isSharedCheck_3340_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_moduleData_3296_);
lean_inc(v_importAllModules_3295_);
lean_inc(v_moduleName2Idx_3294_);
lean_inc(v_modules_3293_);
lean_inc(v_regions_3292_);
lean_inc(v_mainModule_3290_);
lean_dec(v_header_3264_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3340_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3300_; lean_object* v_imports_3301_; lean_object* v___x_3303_; 
v___x_3300_ = lean_array_fget(v_moduleData_3257_, v___y_3245_);
lean_dec_ref(v_moduleData_3257_);
v_imports_3301_ = lean_ctor_get(v___x_3300_, 0);
lean_inc_ref(v_imports_3301_);
lean_dec(v___x_3300_);
if (v_isShared_3299_ == 0)
{
lean_ctor_set(v___x_3298_, 1, v_imports_3301_);
v___x_3303_ = v___x_3298_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 7, 5);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_mainModule_3290_);
lean_ctor_set(v_reuseFailAlloc_3339_, 1, v_imports_3301_);
lean_ctor_set(v_reuseFailAlloc_3339_, 2, v_regions_3292_);
lean_ctor_set(v_reuseFailAlloc_3339_, 3, v_modules_3293_);
lean_ctor_set(v_reuseFailAlloc_3339_, 4, v_moduleName2Idx_3294_);
lean_ctor_set(v_reuseFailAlloc_3339_, 5, v_importAllModules_3295_);
lean_ctor_set(v_reuseFailAlloc_3339_, 6, v_moduleData_3296_);
lean_ctor_set_uint32(v_reuseFailAlloc_3339_, sizeof(void*)*7, v_trustLevel_3289_);
lean_ctor_set_uint8(v_reuseFailAlloc_3339_, sizeof(void*)*7 + 4, v_isModule_3291_);
v___x_3303_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
lean_object* v___x_3305_; 
if (v_isShared_3288_ == 0)
{
lean_ctor_set(v___x_3287_, 5, v___x_3303_);
v___x_3305_ = v___x_3287_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_constants_3280_);
lean_ctor_set(v_reuseFailAlloc_3338_, 1, v_diagnostics_3282_);
lean_ctor_set(v_reuseFailAlloc_3338_, 2, v_const2ModIdx_3283_);
lean_ctor_set(v_reuseFailAlloc_3338_, 3, v_extensions_3284_);
lean_ctor_set(v_reuseFailAlloc_3338_, 4, v_irBaseExts_3285_);
lean_ctor_set(v_reuseFailAlloc_3338_, 5, v___x_3303_);
lean_ctor_set_uint8(v_reuseFailAlloc_3338_, sizeof(void*)*6, v_quotInit_3281_);
v___x_3305_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
lean_object* v___x_3307_; 
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 0, v___x_3305_);
v___x_3307_ = v___x_3278_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3305_);
lean_ctor_set(v_reuseFailAlloc_3337_, 1, v_public_3276_);
v___x_3307_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
lean_object* v___x_3309_; 
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v___x_3307_);
v___x_3309_ = v___x_3274_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3307_);
lean_ctor_set(v_reuseFailAlloc_3336_, 1, v_serverBaseExts_3265_);
lean_ctor_set(v_reuseFailAlloc_3336_, 2, v_checked_3266_);
lean_ctor_set(v_reuseFailAlloc_3336_, 3, v_asyncConstsMap_3267_);
lean_ctor_set(v_reuseFailAlloc_3336_, 4, v_asyncCtx_x3f_3268_);
lean_ctor_set(v_reuseFailAlloc_3336_, 5, v_importRealizationCtx_x3f_3269_);
lean_ctor_set(v_reuseFailAlloc_3336_, 6, v_localRealizationCtxMap_3270_);
lean_ctor_set(v_reuseFailAlloc_3336_, 7, v_allRealizations_3271_);
lean_ctor_set_uint8(v_reuseFailAlloc_3336_, sizeof(void*)*8, v_isExporting_3272_);
v___x_3309_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v_env_3332_; lean_object* v___x_3333_; uint8_t v___x_3334_; uint8_t v___x_3335_; 
v___x_3310_ = l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
v___x_3311_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2936_, v___x_3310_, v___x_3309_, v___y_3245_, v___y_3249_);
lean_dec(v___y_3245_);
v___x_3312_ = l_Lean_firstFrontendMacroScope;
v___x_3313_ = lean_obj_once(&l_main___closed__22, &l_main___closed__22_once, _init_l_main___closed__22);
v___x_3314_ = ((lean_object*)(l_main___closed__25));
lean_inc_n(v___y_3246_, 3);
v___x_3315_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3315_, 0, v___y_3246_);
lean_ctor_set(v___x_3315_, 1, v___x_3242_);
lean_ctor_set(v___x_3315_, 2, v___x_2922_);
v___x_3316_ = lean_obj_once(&l_main___closed__26, &l_main___closed__26_once, _init_l_main___closed__26);
v___x_3317_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_3318_ = lean_obj_once(&l_main___closed__30, &l_main___closed__30_once, _init_l_main___closed__30);
v___x_3319_ = lean_obj_once(&l_main___closed__31, &l_main___closed__31_once, _init_l_main___closed__31);
v___x_3320_ = ((lean_object*)(l_main___closed__32));
lean_inc_ref(v___x_3315_);
v___x_3321_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3309_);
lean_ctor_set(v___x_3321_, 1, v___x_3313_);
lean_ctor_set(v___x_3321_, 2, v___x_3314_);
lean_ctor_set(v___x_3321_, 3, v___x_3315_);
lean_ctor_set(v___x_3321_, 4, v___x_3316_);
lean_ctor_set(v___x_3321_, 5, v___x_3317_);
lean_ctor_set(v___x_3321_, 6, v___x_3318_);
lean_ctor_set(v___x_3321_, 7, v___x_3319_);
lean_ctor_set(v___x_3321_, 8, v___x_3320_);
lean_ctor_set(v___x_3321_, 9, v___x_3320_);
v___x_3322_ = lean_st_mk_ref(v___x_3321_);
v___x_3323_ = l_Lean_inheritedTraceOptions;
v___x_3324_ = lean_st_ref_get(v___x_3323_);
v___x_3325_ = lean_st_ref_get(v___x_3322_);
v___x_3326_ = l_Lean_instInhabitedFileMap_default;
v___x_3327_ = lean_unsigned_to_nat(1000u);
v___x_3328_ = lean_box(0);
v___x_3329_ = l_Lean_Core_getMaxHeartbeats(v___x_2942_);
v___x_3330_ = lean_box(0);
lean_inc_ref(v___x_2942_);
lean_inc(v_head_2903_);
v___x_3331_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3331_, 0, v_head_2903_);
lean_ctor_set(v___x_3331_, 1, v___x_3326_);
lean_ctor_set(v___x_3331_, 2, v___x_2942_);
lean_ctor_set(v___x_3331_, 3, v___x_2941_);
lean_ctor_set(v___x_3331_, 4, v___x_3327_);
lean_ctor_set(v___x_3331_, 5, v___x_3328_);
lean_ctor_set(v___x_3331_, 6, v___y_3246_);
lean_ctor_set(v___x_3331_, 7, v___x_2922_);
lean_ctor_set(v___x_3331_, 8, v___x_2941_);
lean_ctor_set(v___x_3331_, 9, v___x_3329_);
lean_ctor_set(v___x_3331_, 10, v___y_3246_);
lean_ctor_set(v___x_3331_, 11, v___x_3312_);
lean_ctor_set(v___x_3331_, 12, v___x_3330_);
lean_ctor_set(v___x_3331_, 13, v___x_3324_);
lean_ctor_set_uint8(v___x_3331_, sizeof(void*)*14, v___x_2913_);
lean_ctor_set_uint8(v___x_3331_, sizeof(void*)*14 + 1, v___x_2913_);
v_env_3332_ = lean_ctor_get(v___x_3325_, 0);
lean_inc_ref(v_env_3332_);
lean_dec(v___x_3325_);
v___x_3333_ = l_Lean_diagnostics;
v___x_3334_ = l_Lean_Option_get___at___00main_spec__8(v___x_2942_, v___x_3333_);
v___x_3335_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3332_);
lean_dec_ref(v_env_3332_);
if (v___x_3335_ == 0)
{
if (v___x_3334_ == 0)
{
v___y_3195_ = v___x_3328_;
v___y_3196_ = v___x_2922_;
v___y_3197_ = v___x_3317_;
v___y_3198_ = v___y_3244_;
v___y_3199_ = v___x_3259_;
v___y_3200_ = v___x_3312_;
v___y_3201_ = v___x_3330_;
v___y_3202_ = v___x_3323_;
v___y_3203_ = v___x_3326_;
v___y_3204_ = v___x_3317_;
v___y_3205_ = v___x_3320_;
v___y_3206_ = v___y_3246_;
v___y_3207_ = v___x_3322_;
v___y_3208_ = v___x_3331_;
v___y_3209_ = v___x_3334_;
v___y_3210_ = v___x_3313_;
v___y_3211_ = v___x_3310_;
v___y_3212_ = v___x_3315_;
v___y_3213_ = v___x_3316_;
v___y_3214_ = v___x_3318_;
v___y_3215_ = v___x_3311_;
v___y_3216_ = v___x_3319_;
v___y_3217_ = v___x_3320_;
v___y_3218_ = v___x_3314_;
v___y_3219_ = v___x_3259_;
goto v___jp_3194_;
}
else
{
v___y_3195_ = v___x_3328_;
v___y_3196_ = v___x_2922_;
v___y_3197_ = v___x_3317_;
v___y_3198_ = v___y_3244_;
v___y_3199_ = v___x_3259_;
v___y_3200_ = v___x_3312_;
v___y_3201_ = v___x_3330_;
v___y_3202_ = v___x_3323_;
v___y_3203_ = v___x_3326_;
v___y_3204_ = v___x_3317_;
v___y_3205_ = v___x_3320_;
v___y_3206_ = v___y_3246_;
v___y_3207_ = v___x_3322_;
v___y_3208_ = v___x_3331_;
v___y_3209_ = v___x_3334_;
v___y_3210_ = v___x_3313_;
v___y_3211_ = v___x_3310_;
v___y_3212_ = v___x_3315_;
v___y_3213_ = v___x_3316_;
v___y_3214_ = v___x_3318_;
v___y_3215_ = v___x_3311_;
v___y_3216_ = v___x_3319_;
v___y_3217_ = v___x_3320_;
v___y_3218_ = v___x_3314_;
v___y_3219_ = v___x_3335_;
goto v___jp_3194_;
}
}
else
{
v___y_3195_ = v___x_3328_;
v___y_3196_ = v___x_2922_;
v___y_3197_ = v___x_3317_;
v___y_3198_ = v___y_3244_;
v___y_3199_ = v___x_3259_;
v___y_3200_ = v___x_3312_;
v___y_3201_ = v___x_3330_;
v___y_3202_ = v___x_3323_;
v___y_3203_ = v___x_3326_;
v___y_3204_ = v___x_3317_;
v___y_3205_ = v___x_3320_;
v___y_3206_ = v___y_3246_;
v___y_3207_ = v___x_3322_;
v___y_3208_ = v___x_3331_;
v___y_3209_ = v___x_3334_;
v___y_3210_ = v___x_3313_;
v___y_3211_ = v___x_3310_;
v___y_3212_ = v___x_3315_;
v___y_3213_ = v___x_3316_;
v___y_3214_ = v___x_3318_;
v___y_3215_ = v___x_3311_;
v___y_3216_ = v___x_3319_;
v___y_3217_ = v___x_3320_;
v___y_3218_ = v___x_3314_;
v___y_3219_ = v___x_3334_;
goto v___jp_3194_;
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
v___jp_3349_:
{
lean_object* v___x_3355_; lean_object* v_toEnvExtension_3356_; lean_object* v_asyncMode_3357_; lean_object* v___x_3358_; lean_object* v_importedEntries_3359_; lean_object* v_state_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; uint8_t v___x_3363_; 
v___x_3355_ = l_Lean_IR_declMapExt;
v_toEnvExtension_3356_ = lean_ctor_get(v___x_3355_, 0);
v_asyncMode_3357_ = lean_ctor_get(v_toEnvExtension_3356_, 2);
lean_inc(v___y_3352_);
lean_inc_ref(v___y_3354_);
v___x_3358_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2933_, v_toEnvExtension_3356_, v___y_3354_, v_asyncMode_3357_, v___y_3352_);
v_importedEntries_3359_ = lean_ctor_get(v___x_3358_, 0);
lean_inc_ref(v_importedEntries_3359_);
v_state_3360_ = lean_ctor_get(v___x_3358_, 1);
lean_inc(v_state_3360_);
lean_dec(v___x_3358_);
v___x_3361_ = lean_array_get_borrowed(v___x_2934_, v_importedEntries_3359_, v___y_3351_);
v___x_3362_ = lean_array_get_size(v___x_3361_);
v___x_3363_ = lean_nat_dec_lt(v___x_2941_, v___x_3362_);
if (v___x_3363_ == 0)
{
v___y_3244_ = v___y_3350_;
v___y_3245_ = v___y_3351_;
v___y_3246_ = v___y_3352_;
v___y_3247_ = v_toEnvExtension_3356_;
v___y_3248_ = v___y_3354_;
v___y_3249_ = v___y_3353_;
v___y_3250_ = v_importedEntries_3359_;
v___y_3251_ = v_state_3360_;
goto v___jp_3243_;
}
else
{
uint8_t v___x_3364_; 
v___x_3364_ = lean_nat_dec_le(v___x_3362_, v___x_3362_);
if (v___x_3364_ == 0)
{
if (v___x_3363_ == 0)
{
v___y_3244_ = v___y_3350_;
v___y_3245_ = v___y_3351_;
v___y_3246_ = v___y_3352_;
v___y_3247_ = v_toEnvExtension_3356_;
v___y_3248_ = v___y_3354_;
v___y_3249_ = v___y_3353_;
v___y_3250_ = v_importedEntries_3359_;
v___y_3251_ = v_state_3360_;
goto v___jp_3243_;
}
else
{
size_t v___x_3365_; size_t v___x_3366_; lean_object* v___x_3367_; 
v___x_3365_ = ((size_t)0ULL);
v___x_3366_ = lean_usize_of_nat(v___x_3362_);
lean_inc_ref(v___y_3354_);
v___x_3367_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3354_, v___x_3361_, v___x_3365_, v___x_3366_, v_state_3360_);
v___y_3244_ = v___y_3350_;
v___y_3245_ = v___y_3351_;
v___y_3246_ = v___y_3352_;
v___y_3247_ = v_toEnvExtension_3356_;
v___y_3248_ = v___y_3354_;
v___y_3249_ = v___y_3353_;
v___y_3250_ = v_importedEntries_3359_;
v___y_3251_ = v___x_3367_;
goto v___jp_3243_;
}
}
else
{
size_t v___x_3368_; size_t v___x_3369_; lean_object* v___x_3370_; 
v___x_3368_ = ((size_t)0ULL);
v___x_3369_ = lean_usize_of_nat(v___x_3362_);
lean_inc_ref(v___y_3354_);
v___x_3370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3354_, v___x_3361_, v___x_3368_, v___x_3369_, v_state_3360_);
v___y_3244_ = v___y_3350_;
v___y_3245_ = v___y_3351_;
v___y_3246_ = v___y_3352_;
v___y_3247_ = v_toEnvExtension_3356_;
v___y_3248_ = v___y_3354_;
v___y_3249_ = v___y_3353_;
v___y_3250_ = v_importedEntries_3359_;
v___y_3251_ = v___x_3370_;
goto v___jp_3243_;
}
}
}
v___jp_3371_:
{
uint8_t v___x_3379_; 
v___x_3379_ = lean_nat_dec_lt(v___x_2941_, v___y_3374_);
if (v___x_3379_ == 0)
{
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
v___y_3350_ = v___y_3372_;
v___y_3351_ = v___y_3375_;
v___y_3352_ = v___y_3376_;
v___y_3353_ = v___y_3377_;
v___y_3354_ = v___y_3378_;
goto v___jp_3349_;
}
else
{
uint8_t v___x_3380_; 
v___x_3380_ = lean_nat_dec_le(v___y_3374_, v___y_3374_);
if (v___x_3380_ == 0)
{
if (v___x_3379_ == 0)
{
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
v___y_3350_ = v___y_3372_;
v___y_3351_ = v___y_3375_;
v___y_3352_ = v___y_3376_;
v___y_3353_ = v___y_3377_;
v___y_3354_ = v___y_3378_;
goto v___jp_3349_;
}
else
{
size_t v___x_3381_; size_t v___x_3382_; lean_object* v___x_3383_; 
v___x_3381_ = ((size_t)0ULL);
v___x_3382_ = lean_usize_of_nat(v___y_3374_);
lean_dec(v___y_3374_);
v___x_3383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3373_, v___x_3381_, v___x_3382_, v___y_3378_);
lean_dec_ref(v___y_3373_);
v___y_3350_ = v___y_3372_;
v___y_3351_ = v___y_3375_;
v___y_3352_ = v___y_3376_;
v___y_3353_ = v___y_3377_;
v___y_3354_ = v___x_3383_;
goto v___jp_3349_;
}
}
else
{
size_t v___x_3384_; size_t v___x_3385_; lean_object* v___x_3386_; 
v___x_3384_ = ((size_t)0ULL);
v___x_3385_ = lean_usize_of_nat(v___y_3374_);
lean_dec(v___y_3374_);
v___x_3386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3373_, v___x_3384_, v___x_3385_, v___y_3378_);
lean_dec_ref(v___y_3373_);
v___y_3350_ = v___y_3372_;
v___y_3351_ = v___y_3375_;
v___y_3352_ = v___y_3376_;
v___y_3353_ = v___y_3377_;
v___y_3354_ = v___x_3386_;
goto v___jp_3349_;
}
}
}
v___jp_3387_:
{
lean_object* v___x_3394_; uint8_t v___x_3395_; 
v___x_3394_ = lean_array_get_size(v___y_3393_);
v___x_3395_ = lean_nat_dec_lt(v___x_2941_, v___x_3394_);
if (v___x_3395_ == 0)
{
v___y_3372_ = v___y_3389_;
v___y_3373_ = v___y_3393_;
v___y_3374_ = v___x_3394_;
v___y_3375_ = v___y_3388_;
v___y_3376_ = v___y_3390_;
v___y_3377_ = v___y_3392_;
v___y_3378_ = v___y_3391_;
goto v___jp_3371_;
}
else
{
uint8_t v___x_3396_; 
v___x_3396_ = lean_nat_dec_le(v___x_3394_, v___x_3394_);
if (v___x_3396_ == 0)
{
if (v___x_3395_ == 0)
{
v___y_3372_ = v___y_3389_;
v___y_3373_ = v___y_3393_;
v___y_3374_ = v___x_3394_;
v___y_3375_ = v___y_3388_;
v___y_3376_ = v___y_3390_;
v___y_3377_ = v___y_3392_;
v___y_3378_ = v___y_3391_;
goto v___jp_3371_;
}
else
{
size_t v___x_3397_; size_t v___x_3398_; lean_object* v___x_3399_; 
v___x_3397_ = ((size_t)0ULL);
v___x_3398_ = lean_usize_of_nat(v___x_3394_);
v___x_3399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3393_, v___x_3397_, v___x_3398_, v___y_3391_);
v___y_3372_ = v___y_3389_;
v___y_3373_ = v___y_3393_;
v___y_3374_ = v___x_3394_;
v___y_3375_ = v___y_3388_;
v___y_3376_ = v___y_3390_;
v___y_3377_ = v___y_3392_;
v___y_3378_ = v___x_3399_;
goto v___jp_3371_;
}
}
else
{
size_t v___x_3400_; size_t v___x_3401_; lean_object* v___x_3402_; 
v___x_3400_ = ((size_t)0ULL);
v___x_3401_ = lean_usize_of_nat(v___x_3394_);
v___x_3402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3393_, v___x_3400_, v___x_3401_, v___y_3391_);
v___y_3372_ = v___y_3389_;
v___y_3373_ = v___y_3393_;
v___y_3374_ = v___x_3394_;
v___y_3375_ = v___y_3388_;
v___y_3376_ = v___y_3390_;
v___y_3377_ = v___y_3392_;
v___y_3378_ = v___x_3402_;
goto v___jp_3371_;
}
}
}
v___jp_3406_:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___f_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3408_ = l_Lean_instInhabitedImportState_default;
v___x_3409_ = lean_box(v___x_3405_);
v___x_3410_ = lean_box(v___y_3407_);
v___x_3411_ = lean_box(v___x_2938_);
v___x_3412_ = lean_box(v___x_2913_);
lean_inc_ref(v___x_2942_);
lean_inc(v_name_2911_);
v___f_3413_ = lean_alloc_closure((void*)(l_main___lam__0___boxed), 10, 9);
lean_closure_set(v___f_3413_, 0, v___x_3408_);
lean_closure_set(v___f_3413_, 1, v___x_3404_);
lean_closure_set(v___f_3413_, 2, v___x_3409_);
lean_closure_set(v___f_3413_, 3, v___x_2935_);
lean_closure_set(v___f_3413_, 4, v___x_3410_);
lean_closure_set(v___f_3413_, 5, v_name_2911_);
lean_closure_set(v___f_3413_, 6, v___x_2942_);
lean_closure_set(v___f_3413_, 7, v___x_3411_);
lean_closure_set(v___f_3413_, 8, v___x_3412_);
v___x_3414_ = lean_alloc_closure((void*)(l_Lean_withImporting___boxed), 3, 2);
lean_closure_set(v___x_3414_, 0, lean_box(0));
lean_closure_set(v___x_3414_, 1, v___f_3413_);
v___x_3415_ = lean_box(0);
v___x_3416_ = l_Lean_profileitIOUnsafe___redArg(v___x_3240_, v___x_2942_, v___x_3414_, v___x_3415_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_a_3417_; lean_object* v___x_3418_; lean_object* v_ext_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
lean_inc(v_a_3417_);
lean_dec_ref(v___x_3416_);
v___x_3418_ = l_Lean_Compiler_CSimp_ext;
v_ext_3419_ = lean_ctor_get(v___x_3418_, 1);
lean_inc(v_name_2911_);
v___x_3420_ = l_Lean_Environment_setMainModule(v_a_3417_, v_name_2911_);
lean_inc_ref(v_ext_3419_);
v___x_3421_ = l_main___elam__0___redArg(v___x_3415_, v___x_2929_, v_ext_3419_, v___x_3420_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v_a_3422_; lean_object* v___x_3423_; lean_object* v_ext_3424_; lean_object* v___x_3425_; 
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
lean_inc(v_a_3422_);
lean_dec_ref(v___x_3421_);
v___x_3423_ = l_Lean_Meta_instanceExtension;
v_ext_3424_ = lean_ctor_get(v___x_3423_, 1);
lean_inc_ref(v_ext_3424_);
v___x_3425_ = l_main___elam__0___redArg(v___x_3415_, v___x_2929_, v_ext_3424_, v_a_3422_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_a_3426_);
lean_dec_ref(v___x_3425_);
v___x_3427_ = l_Lean_classExtension;
v___x_3428_ = l_main___elam__0___redArg(v___x_3415_, v___x_2930_, v___x_3427_, v_a_3426_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_a_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_a_3429_);
lean_dec_ref(v___x_3428_);
v___x_3430_ = l_Lean_Meta_Match_Extension_extension;
v___x_3431_ = l_main___elam__0___redArg(v___x_3415_, v___x_2931_, v___x_3430_, v_a_3429_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3460_; 
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3434_ = v___x_3431_;
v_isShared_3435_ = v_isSharedCheck_3460_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___x_3431_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3460_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3436_; 
v___x_3436_ = l_Lean_Environment_getModuleIdx_x3f(v_a_3432_, v_name_2911_);
if (lean_obj_tag(v___x_3436_) == 1)
{
lean_object* v_val_3437_; lean_object* v___x_3438_; uint8_t v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; uint8_t v___x_3443_; 
lean_del_object(v___x_3434_);
v_val_3437_ = lean_ctor_get(v___x_3436_, 0);
lean_inc(v_val_3437_);
lean_dec_ref(v___x_3436_);
v___x_3438_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_3439_ = 0;
v___x_3440_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2932_, v___x_3438_, v_a_3432_, v_val_3437_, v___x_3439_);
v___x_3441_ = lean_array_get_size(v___x_3440_);
v___x_3442_ = ((lean_object*)(l_main___closed__33));
v___x_3443_ = lean_nat_dec_lt(v___x_2941_, v___x_3441_);
if (v___x_3443_ == 0)
{
lean_dec_ref(v___x_3440_);
v___y_3388_ = v_val_3437_;
v___y_3389_ = v___x_3415_;
v___y_3390_ = v___x_3415_;
v___y_3391_ = v_a_3432_;
v___y_3392_ = v___x_3439_;
v___y_3393_ = v___x_3442_;
goto v___jp_3387_;
}
else
{
uint8_t v___x_3444_; 
v___x_3444_ = lean_nat_dec_le(v___x_3441_, v___x_3441_);
if (v___x_3444_ == 0)
{
if (v___x_3443_ == 0)
{
lean_dec_ref(v___x_3440_);
v___y_3388_ = v_val_3437_;
v___y_3389_ = v___x_3415_;
v___y_3390_ = v___x_3415_;
v___y_3391_ = v_a_3432_;
v___y_3392_ = v___x_3439_;
v___y_3393_ = v___x_3442_;
goto v___jp_3387_;
}
else
{
size_t v___x_3445_; size_t v___x_3446_; lean_object* v___x_3447_; 
v___x_3445_ = ((size_t)0ULL);
v___x_3446_ = lean_usize_of_nat(v___x_3441_);
lean_inc(v_a_3432_);
v___x_3447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3432_, v___x_3440_, v___x_3445_, v___x_3446_, v___x_3442_);
lean_dec_ref(v___x_3440_);
v___y_3388_ = v_val_3437_;
v___y_3389_ = v___x_3415_;
v___y_3390_ = v___x_3415_;
v___y_3391_ = v_a_3432_;
v___y_3392_ = v___x_3439_;
v___y_3393_ = v___x_3447_;
goto v___jp_3387_;
}
}
else
{
size_t v___x_3448_; size_t v___x_3449_; lean_object* v___x_3450_; 
v___x_3448_ = ((size_t)0ULL);
v___x_3449_ = lean_usize_of_nat(v___x_3441_);
lean_inc(v_a_3432_);
v___x_3450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3432_, v___x_3440_, v___x_3448_, v___x_3449_, v___x_3442_);
lean_dec_ref(v___x_3440_);
v___y_3388_ = v_val_3437_;
v___y_3389_ = v___x_3415_;
v___y_3390_ = v___x_3415_;
v___y_3391_ = v_a_3432_;
v___y_3392_ = v___x_3439_;
v___y_3393_ = v___x_3450_;
goto v___jp_3387_;
}
}
}
else
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3458_; 
lean_dec(v___x_3436_);
lean_dec(v_a_3432_);
lean_dec_ref(v___x_2942_);
lean_del_object(v___x_2927_);
lean_dec(v_fst_2924_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v___x_3451_ = ((lean_object*)(l_main___closed__34));
v___x_3452_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2911_, v___x_2938_);
v___x_3453_ = lean_string_append(v___x_3451_, v___x_3452_);
lean_dec_ref(v___x_3452_);
v___x_3454_ = ((lean_object*)(l_main___closed__35));
v___x_3455_ = lean_string_append(v___x_3453_, v___x_3454_);
v___x_3456_ = lean_mk_io_user_error(v___x_3455_);
if (v_isShared_3435_ == 0)
{
lean_ctor_set_tag(v___x_3434_, 1);
lean_ctor_set(v___x_3434_, 0, v___x_3456_);
v___x_3458_ = v___x_3434_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v___x_3456_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
else
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3468_; 
lean_dec_ref(v___x_2942_);
lean_del_object(v___x_2927_);
lean_dec(v_fst_2924_);
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v_a_3461_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3463_ = v___x_3431_;
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v___x_3431_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3466_; 
if (v_isShared_3464_ == 0)
{
v___x_3466_ = v___x_3463_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3461_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
}
else
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3476_; 
lean_dec_ref(v___x_2942_);
lean_del_object(v___x_2927_);
lean_dec(v_fst_2924_);
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v_a_3469_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3471_ = v___x_3428_;
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3428_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3474_; 
if (v_isShared_3472_ == 0)
{
v___x_3474_ = v___x_3471_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_a_3469_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
}
else
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3484_; 
lean_dec_ref(v___x_2942_);
lean_del_object(v___x_2927_);
lean_dec(v_fst_2924_);
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v_a_3477_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3479_ = v___x_3425_;
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3425_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3482_; 
if (v_isShared_3480_ == 0)
{
v___x_3482_ = v___x_3479_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_a_3477_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
else
{
lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3492_; 
lean_dec_ref(v___x_2942_);
lean_del_object(v___x_2927_);
lean_dec(v_fst_2924_);
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v_a_3485_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3487_ = v___x_3421_;
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___x_3421_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3488_ == 0)
{
v___x_3490_ = v___x_3487_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_a_3485_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
else
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3500_; 
lean_dec_ref(v___x_2942_);
lean_del_object(v___x_2927_);
lean_dec(v_fst_2924_);
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v_a_3493_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3495_ = v___x_3416_;
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3416_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3498_; 
if (v_isShared_3496_ == 0)
{
v___x_3498_ = v___x_3495_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_a_3493_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
}
}
}
else
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3510_; 
lean_dec(v_a_2919_);
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v_a_3503_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3505_ = v___x_2923_;
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_2923_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3508_; 
if (v_isShared_3506_ == 0)
{
v___x_3508_ = v___x_3505_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_a_3503_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
}
else
{
lean_object* v_a_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3518_; 
lean_dec(v_a_2919_);
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v_a_3511_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3513_ = v___x_2920_;
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_a_3511_);
lean_dec(v___x_2920_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3516_; 
if (v_isShared_3514_ == 0)
{
v___x_3516_ = v___x_3513_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_a_3511_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
}
else
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3526_; 
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v_a_3519_ = lean_ctor_get(v___x_2918_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3521_ = v___x_2918_;
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_2918_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3524_; 
if (v_isShared_3522_ == 0)
{
v___x_3524_ = v___x_3521_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_a_3519_);
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
}
else
{
lean_object* v_a_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3535_; 
lean_del_object(v___x_2907_);
lean_dec(v_tail_2905_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v_a_3528_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3530_ = v___x_2909_;
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_a_3528_);
lean_dec(v___x_2909_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3533_; 
if (v_isShared_3531_ == 0)
{
v___x_3533_ = v___x_3530_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_a_3528_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
}
else
{
lean_dec_ref(v_tail_2900_);
lean_dec(v_tail_2901_);
lean_dec_ref(v_args_2875_);
goto v___jp_2877_;
}
}
else
{
lean_dec_ref(v_args_2875_);
lean_dec(v_tail_2900_);
goto v___jp_2877_;
}
}
else
{
lean_dec(v_args_2875_);
goto v___jp_2877_;
}
v___jp_2877_:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2878_ = ((lean_object*)(l_main___closed__0));
v___x_2879_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_2878_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2887_; 
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2887_ == 0)
{
lean_object* v_unused_2888_; 
v_unused_2888_ = lean_ctor_get(v___x_2879_, 0);
lean_dec(v_unused_2888_);
v___x_2881_ = v___x_2879_;
v_isShared_2882_ = v_isSharedCheck_2887_;
goto v_resetjp_2880_;
}
else
{
lean_dec(v___x_2879_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2887_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2883_; lean_object* v___x_2885_; 
v___x_2883_ = l_main___boxed__const__1;
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 0, v___x_2883_);
v___x_2885_ = v___x_2881_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2883_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
else
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
v_a_2889_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2879_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2879_);
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
v___jp_2897_:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = l_main___boxed__const__2;
v___x_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
return v___x_2899_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_3537_, lean_object* v_a_3538_){
_start:
{
lean_object* v_res_3539_; 
v_res_3539_ = _lean_main(v_args_3537_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object* v_as_3540_, lean_object* v_as_x27_3541_, lean_object* v_b_3542_, lean_object* v_a_3543_){
_start:
{
lean_object* v___x_3545_; 
v___x_3545_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_3541_, v_b_3542_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object* v_as_3546_, lean_object* v_as_x27_3547_, lean_object* v_b_3548_, lean_object* v_a_3549_, lean_object* v___y_3550_){
_start:
{
lean_object* v_res_3551_; 
v_res_3551_ = l_List_forIn_x27_loop___at___00main_spec__1(v_as_3546_, v_as_x27_3547_, v_b_3548_, v_a_3549_);
lean_dec(v_as_x27_3547_);
lean_dec(v_as_3546_);
return v_res_3551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
lean_object* v___x_3555_; 
v___x_3555_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_3553_);
return v___x_3555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___boxed(lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
lean_object* v_res_3559_; 
v_res_3559_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(v___y_3556_, v___y_3557_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(lean_object* v_00_u03b2_3560_, lean_object* v_m_3561_, lean_object* v_a_3562_, lean_object* v_fallback_3563_){
_start:
{
lean_object* v___x_3564_; 
v___x_3564_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_3561_, v_a_3562_, v_fallback_3563_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___boxed(lean_object* v_00_u03b2_3565_, lean_object* v_m_3566_, lean_object* v_a_3567_, lean_object* v_fallback_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(v_00_u03b2_3565_, v_m_3566_, v_a_3567_, v_fallback_3568_);
lean_dec(v_fallback_3568_);
lean_dec_ref(v_a_3567_);
lean_dec_ref(v_m_3566_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18(lean_object* v_00_u03b2_3570_, lean_object* v_m_3571_, lean_object* v_a_3572_, lean_object* v_b_3573_){
_start:
{
lean_object* v___x_3574_; 
v___x_3574_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_m_3571_, v_a_3572_, v_b_3573_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(lean_object* v_n_3575_, lean_object* v_as_3576_, lean_object* v_lo_3577_, lean_object* v_hi_3578_, lean_object* v_w_3579_, lean_object* v_hlo_3580_, lean_object* v_hhi_3581_){
_start:
{
lean_object* v___x_3582_; 
v___x_3582_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_3575_, v_as_3576_, v_lo_3577_, v_hi_3578_);
return v___x_3582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___boxed(lean_object* v_n_3583_, lean_object* v_as_3584_, lean_object* v_lo_3585_, lean_object* v_hi_3586_, lean_object* v_w_3587_, lean_object* v_hlo_3588_, lean_object* v_hhi_3589_){
_start:
{
lean_object* v_res_3590_; 
v_res_3590_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(v_n_3583_, v_as_3584_, v_lo_3585_, v_hi_3586_, v_w_3587_, v_hlo_3588_, v_hhi_3589_);
lean_dec(v_hi_3586_);
lean_dec(v_n_3583_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(lean_object* v_00_u03b2_3591_, lean_object* v_a_3592_, lean_object* v_fallback_3593_, lean_object* v_x_3594_){
_start:
{
lean_object* v___x_3595_; 
v___x_3595_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_3592_, v_fallback_3593_, v_x_3594_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3596_, lean_object* v_a_3597_, lean_object* v_fallback_3598_, lean_object* v_x_3599_){
_start:
{
lean_object* v_res_3600_; 
v_res_3600_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(v_00_u03b2_3596_, v_a_3597_, v_fallback_3598_, v_x_3599_);
lean_dec(v_x_3599_);
lean_dec(v_fallback_3598_);
lean_dec_ref(v_a_3597_);
return v_res_3600_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(lean_object* v_00_u03b2_3601_, lean_object* v_a_3602_, lean_object* v_x_3603_){
_start:
{
uint8_t v___x_3604_; 
v___x_3604_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_3602_, v_x_3603_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___boxed(lean_object* v_00_u03b2_3605_, lean_object* v_a_3606_, lean_object* v_x_3607_){
_start:
{
uint8_t v_res_3608_; lean_object* v_r_3609_; 
v_res_3608_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(v_00_u03b2_3605_, v_a_3606_, v_x_3607_);
lean_dec(v_x_3607_);
lean_dec_ref(v_a_3606_);
v_r_3609_ = lean_box(v_res_3608_);
return v_r_3609_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24(lean_object* v_00_u03b2_3610_, lean_object* v_data_3611_){
_start:
{
lean_object* v___x_3612_; 
v___x_3612_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_data_3611_);
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25(lean_object* v_00_u03b2_3613_, lean_object* v_a_3614_, lean_object* v_b_3615_, lean_object* v_x_3616_){
_start:
{
lean_object* v___x_3617_; 
v___x_3617_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_3614_, v_b_3615_, v_x_3616_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(lean_object* v_n_3618_, lean_object* v_lo_3619_, lean_object* v_hi_3620_, lean_object* v_hhi_3621_, lean_object* v_pivot_3622_, lean_object* v_as_3623_, lean_object* v_i_3624_, lean_object* v_k_3625_, lean_object* v_ilo_3626_, lean_object* v_ik_3627_, lean_object* v_w_3628_){
_start:
{
lean_object* v___x_3629_; 
v___x_3629_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_3620_, v_pivot_3622_, v_as_3623_, v_i_3624_, v_k_3625_);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___boxed(lean_object* v_n_3630_, lean_object* v_lo_3631_, lean_object* v_hi_3632_, lean_object* v_hhi_3633_, lean_object* v_pivot_3634_, lean_object* v_as_3635_, lean_object* v_i_3636_, lean_object* v_k_3637_, lean_object* v_ilo_3638_, lean_object* v_ik_3639_, lean_object* v_w_3640_){
_start:
{
lean_object* v_res_3641_; 
v_res_3641_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(v_n_3630_, v_lo_3631_, v_hi_3632_, v_hhi_3633_, v_pivot_3634_, v_as_3635_, v_i_3636_, v_k_3637_, v_ilo_3638_, v_ik_3639_, v_w_3640_);
lean_dec_ref(v_pivot_3634_);
lean_dec(v_hi_3632_);
lean_dec(v_lo_3631_);
lean_dec(v_n_3630_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(lean_object* v_as_3642_, size_t v_sz_3643_, size_t v_i_3644_, lean_object* v_b_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
lean_object* v___x_3649_; 
v___x_3649_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_3642_, v_sz_3643_, v_i_3644_, v_b_3645_, v___y_3646_);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___boxed(lean_object* v_as_3650_, lean_object* v_sz_3651_, lean_object* v_i_3652_, lean_object* v_b_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_){
_start:
{
size_t v_sz_boxed_3657_; size_t v_i_boxed_3658_; lean_object* v_res_3659_; 
v_sz_boxed_3657_ = lean_unbox_usize(v_sz_3651_);
lean_dec(v_sz_3651_);
v_i_boxed_3658_ = lean_unbox_usize(v_i_3652_);
lean_dec(v_i_3652_);
v_res_3659_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(v_as_3650_, v_sz_boxed_3657_, v_i_boxed_3658_, v_b_3653_, v___y_3654_, v___y_3655_);
lean_dec(v___y_3655_);
lean_dec_ref(v___y_3654_);
lean_dec_ref(v_as_3650_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35(lean_object* v_00_u03b2_3660_, lean_object* v_i_3661_, lean_object* v_source_3662_, lean_object* v_target_3663_){
_start:
{
lean_object* v___x_3664_; 
v___x_3664_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v_i_3661_, v_source_3662_, v_target_3663_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(uint8_t v___x_3665_, lean_object* v_as_3666_, size_t v_sz_3667_, size_t v_i_3668_, lean_object* v_b_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_){
_start:
{
lean_object* v___x_3673_; 
v___x_3673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_3665_, v_as_3666_, v_sz_3667_, v_i_3668_, v_b_3669_, v___y_3670_);
return v___x_3673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___boxed(lean_object* v___x_3674_, lean_object* v_as_3675_, lean_object* v_sz_3676_, lean_object* v_i_3677_, lean_object* v_b_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
uint8_t v___x_41358__boxed_3682_; size_t v_sz_boxed_3683_; size_t v_i_boxed_3684_; lean_object* v_res_3685_; 
v___x_41358__boxed_3682_ = lean_unbox(v___x_3674_);
v_sz_boxed_3683_ = lean_unbox_usize(v_sz_3676_);
lean_dec(v_sz_3676_);
v_i_boxed_3684_ = lean_unbox_usize(v_i_3677_);
lean_dec(v_i_3677_);
v_res_3685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(v___x_41358__boxed_3682_, v_as_3675_, v_sz_boxed_3683_, v_i_boxed_3684_, v_b_3678_, v___y_3679_, v___y_3680_);
lean_dec(v___y_3680_);
lean_dec_ref(v___y_3679_);
lean_dec_ref(v_as_3675_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(lean_object* v_as_3686_, size_t v_sz_3687_, size_t v_i_3688_, lean_object* v_b_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_){
_start:
{
lean_object* v___x_3693_; 
v___x_3693_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_3686_, v_sz_3687_, v_i_3688_, v_b_3689_, v___y_3690_);
return v___x_3693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___boxed(lean_object* v_as_3694_, lean_object* v_sz_3695_, lean_object* v_i_3696_, lean_object* v_b_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
size_t v_sz_boxed_3701_; size_t v_i_boxed_3702_; lean_object* v_res_3703_; 
v_sz_boxed_3701_ = lean_unbox_usize(v_sz_3695_);
lean_dec(v_sz_3695_);
v_i_boxed_3702_ = lean_unbox_usize(v_i_3696_);
lean_dec(v_i_3696_);
v_res_3703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(v_as_3694_, v_sz_boxed_3701_, v_i_boxed_3702_, v_b_3697_, v___y_3698_, v___y_3699_);
lean_dec(v___y_3699_);
lean_dec_ref(v___y_3698_);
lean_dec_ref(v_as_3694_);
return v_res_3703_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44(lean_object* v_00_u03b2_3704_, lean_object* v_x_3705_, lean_object* v_x_3706_){
_start:
{
lean_object* v___x_3707_; 
v___x_3707_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_x_3705_, v_x_3706_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(uint8_t v___x_3708_, lean_object* v_as_3709_, size_t v_sz_3710_, size_t v_i_3711_, lean_object* v_b_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_){
_start:
{
lean_object* v___x_3716_; 
v___x_3716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_3708_, v_as_3709_, v_sz_3710_, v_i_3711_, v_b_3712_, v___y_3713_);
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___boxed(lean_object* v___x_3717_, lean_object* v_as_3718_, lean_object* v_sz_3719_, lean_object* v_i_3720_, lean_object* v_b_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_){
_start:
{
uint8_t v___x_41389__boxed_3725_; size_t v_sz_boxed_3726_; size_t v_i_boxed_3727_; lean_object* v_res_3728_; 
v___x_41389__boxed_3725_ = lean_unbox(v___x_3717_);
v_sz_boxed_3726_ = lean_unbox_usize(v_sz_3719_);
lean_dec(v_sz_3719_);
v_i_boxed_3727_ = lean_unbox_usize(v_i_3720_);
lean_dec(v_i_3720_);
v_res_3728_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(v___x_41389__boxed_3725_, v_as_3718_, v_sz_boxed_3726_, v_i_boxed_3727_, v_b_3721_, v___y_3722_, v___y_3723_);
lean_dec(v___y_3723_);
lean_dec_ref(v___y_3722_);
lean_dec_ref(v_as_3718_);
return v_res_3728_;
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
