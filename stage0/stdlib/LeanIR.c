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
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecls();
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_toName(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_setOption(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
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
static lean_object* _init_l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__0));
v___x_119_ = lean_string_utf8_byte_size(v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(lean_object* v_s_120_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_121_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__0));
v___x_122_ = lean_string_utf8_byte_size(v_s_120_);
v___x_123_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__1, &l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___closed__1);
v___x_124_ = lean_nat_dec_le(v___x_123_, v___x_122_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; 
lean_dec_ref(v_s_120_);
v___x_125_ = lean_box(0);
return v___x_125_;
}
else
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_string_memcmp(v_s_120_, v___x_121_, v___x_126_, v___x_126_, v___x_123_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; 
lean_dec_ref(v_s_120_);
v___x_128_ = lean_box(0);
return v___x_128_;
}
else
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
lean_inc_ref(v_s_120_);
v___x_129_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_129_, 0, v_s_120_);
lean_ctor_set(v___x_129_, 1, v___x_126_);
lean_ctor_set(v___x_129_, 2, v___x_122_);
v___x_130_ = l_String_Slice_pos_x21(v___x_129_, v___x_123_);
lean_dec_ref_known(v___x_129_, 3);
v___x_131_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_131_, 0, v_s_120_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
lean_ctor_set(v___x_131_, 2, v___x_122_);
v___x_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
return v___x_132_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0(lean_object* v_s_133_, lean_object* v_pat_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(v_s_133_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___boxed(lean_object* v_s_136_, lean_object* v_pat_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0(v_s_136_, v_pat_137_);
lean_dec_ref(v_pat_137_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(lean_object* v_val_139_, lean_object* v_a_140_, lean_object* v_b_141_){
_start:
{
lean_object* v_str_142_; lean_object* v_startInclusive_143_; lean_object* v_endExclusive_144_; lean_object* v___x_145_; uint8_t v___x_146_; 
v_str_142_ = lean_ctor_get(v_val_139_, 0);
v_startInclusive_143_ = lean_ctor_get(v_val_139_, 1);
v_endExclusive_144_ = lean_ctor_get(v_val_139_, 2);
v___x_145_ = lean_nat_sub(v_endExclusive_144_, v_startInclusive_143_);
v___x_146_ = lean_nat_dec_eq(v_a_140_, v___x_145_);
lean_dec(v___x_145_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; uint32_t v___x_148_; uint32_t v___x_149_; uint8_t v___x_150_; 
v___x_147_ = lean_nat_add(v_startInclusive_143_, v_a_140_);
v___x_148_ = lean_string_utf8_get_fast(v_str_142_, v___x_147_);
v___x_149_ = 61;
v___x_150_ = lean_uint32_dec_eq(v___x_148_, v___x_149_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
lean_dec(v_a_140_);
v___x_151_ = lean_box(0);
v___x_152_ = lean_string_utf8_next_fast(v_str_142_, v___x_147_);
lean_dec(v___x_147_);
v___x_153_ = lean_nat_sub(v___x_152_, v_startInclusive_143_);
v_a_140_ = v___x_153_;
v_b_141_ = v___x_151_;
goto _start;
}
else
{
lean_object* v___x_155_; 
lean_dec(v___x_147_);
v___x_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_155_, 0, v_a_140_);
return v___x_155_;
}
}
else
{
lean_dec(v_a_140_);
lean_inc(v_b_141_);
return v_b_141_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg___boxed(lean_object* v_val_156_, lean_object* v_a_157_, lean_object* v_b_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(v_val_156_, v_a_157_, v_b_158_);
lean_dec(v_b_158_);
lean_dec_ref(v_val_156_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption(lean_object* v_opts_167_, lean_object* v_arg_168_){
_start:
{
lean_object* v___x_170_; 
lean_inc_ref(v_arg_168_);
v___x_170_ = l_String_dropPrefix_x3f___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(v_arg_168_);
if (lean_obj_tag(v___x_170_) == 1)
{
lean_object* v_val_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_235_; 
lean_dec_ref(v_arg_168_);
v_val_171_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_235_ == 0)
{
v___x_173_ = v___x_170_;
v_isShared_174_ = v_isSharedCheck_235_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_val_171_);
lean_dec(v___x_170_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_235_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___y_176_; lean_object* v_searcher_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v_searcher_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = lean_box(0);
v___x_230_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(v_val_171_, v_searcher_228_, v___x_229_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_startInclusive_231_; lean_object* v_endExclusive_232_; lean_object* v___x_233_; 
v_startInclusive_231_ = lean_ctor_get(v_val_171_, 1);
v_endExclusive_232_ = lean_ctor_get(v_val_171_, 2);
v___x_233_ = lean_nat_sub(v_endExclusive_232_, v_startInclusive_231_);
v___y_176_ = v___x_233_;
goto v___jp_175_;
}
else
{
lean_object* v_val_234_; 
v_val_234_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_val_234_);
lean_dec_ref_known(v___x_230_, 1);
v___y_176_ = v_val_234_;
goto v___jp_175_;
}
v___jp_175_:
{
lean_object* v_str_177_; lean_object* v_startInclusive_178_; lean_object* v_endExclusive_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_227_; 
v_str_177_ = lean_ctor_get(v_val_171_, 0);
v_startInclusive_178_ = lean_ctor_get(v_val_171_, 1);
v_endExclusive_179_ = lean_ctor_get(v_val_171_, 2);
v_isSharedCheck_227_ = !lean_is_exclusive(v_val_171_);
if (v_isSharedCheck_227_ == 0)
{
v___x_181_ = v_val_171_;
v_isShared_182_ = v_isSharedCheck_227_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_endExclusive_179_);
lean_inc(v_startInclusive_178_);
lean_inc(v_str_177_);
lean_dec(v_val_171_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_227_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_183_ = lean_nat_sub(v_endExclusive_179_, v_startInclusive_178_);
v___x_184_ = lean_nat_dec_eq(v___y_176_, v___x_183_);
lean_dec(v___x_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; 
v___x_185_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_214_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_214_ == 0)
{
v___x_188_ = v___x_185_;
v_isShared_189_ = v_isSharedCheck_214_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_185_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_214_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; lean_object* v___x_192_; 
v___x_190_ = lean_nat_add(v_startInclusive_178_, v___y_176_);
lean_dec(v___y_176_);
lean_inc(v___x_190_);
lean_inc(v_startInclusive_178_);
lean_inc_ref(v_str_177_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 2, v___x_190_);
v___x_192_ = v___x_181_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_str_177_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v_startInclusive_178_);
lean_ctor_set(v_reuseFailAlloc_213_, 2, v___x_190_);
v___x_192_ = v_reuseFailAlloc_213_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
lean_object* v_name_193_; lean_object* v___x_194_; 
v_name_193_ = l_String_Slice_toName(v___x_192_);
lean_dec_ref(v___x_192_);
v___x_194_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_186_, v_name_193_);
lean_dec(v_a_186_);
if (lean_obj_tag(v___x_194_) == 1)
{
lean_object* v_val_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v_val_199_; lean_object* v___x_200_; 
lean_del_object(v___x_188_);
lean_del_object(v___x_173_);
v_val_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_val_195_);
lean_dec_ref_known(v___x_194_, 1);
v___x_196_ = lean_string_utf8_next_fast(v_str_177_, v___x_190_);
lean_dec(v___x_190_);
v___x_197_ = lean_nat_sub(v___x_196_, v_startInclusive_178_);
v___x_198_ = lean_nat_add(v_startInclusive_178_, v___x_197_);
lean_dec(v___x_197_);
lean_dec(v_startInclusive_178_);
v_val_199_ = lean_string_utf8_extract(v_str_177_, v___x_198_, v_endExclusive_179_);
lean_dec(v_endExclusive_179_);
lean_dec(v___x_198_);
lean_dec_ref(v_str_177_);
v___x_200_ = l_Lean_Language_Lean_setOption(v_opts_167_, v_val_195_, v_name_193_, v_val_199_);
return v___x_200_;
}
else
{
lean_object* v___x_201_; uint8_t v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_208_; 
lean_dec(v___x_194_);
lean_dec(v___x_190_);
lean_dec(v_endExclusive_179_);
lean_dec(v_startInclusive_178_);
lean_dec_ref(v_str_177_);
lean_dec_ref(v_opts_167_);
v___x_201_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__0));
v___x_202_ = 1;
v___x_203_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_193_, v___x_202_);
v___x_204_ = lean_string_append(v___x_201_, v___x_203_);
lean_dec_ref(v___x_203_);
v___x_205_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__1));
v___x_206_ = lean_string_append(v___x_204_, v___x_205_);
if (v_isShared_174_ == 0)
{
lean_ctor_set_tag(v___x_173_, 18);
lean_ctor_set(v___x_173_, 0, v___x_206_);
v___x_208_ = v___x_173_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_206_);
v___x_208_ = v_reuseFailAlloc_212_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_210_; 
if (v_isShared_189_ == 0)
{
lean_ctor_set_tag(v___x_188_, 1);
lean_ctor_set(v___x_188_, 0, v___x_208_);
v___x_210_ = v___x_188_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_208_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
}
}
else
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
lean_del_object(v___x_181_);
lean_dec(v_endExclusive_179_);
lean_dec(v_startInclusive_178_);
lean_dec_ref(v_str_177_);
lean_dec(v___y_176_);
lean_del_object(v___x_173_);
lean_dec_ref(v_opts_167_);
v_a_215_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_222_ == 0)
{
v___x_217_ = v___x_185_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_185_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_220_; 
if (v_isShared_218_ == 0)
{
v___x_220_ = v___x_217_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_a_215_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
else
{
lean_object* v___x_223_; lean_object* v___x_225_; 
lean_del_object(v___x_181_);
lean_dec(v_endExclusive_179_);
lean_dec(v_startInclusive_178_);
lean_dec_ref(v_str_177_);
lean_dec(v___y_176_);
lean_dec_ref(v_opts_167_);
v___x_223_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__3));
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 0, v___x_223_);
v___x_225_ = v___x_173_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
}
}
else
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec(v___x_170_);
lean_dec_ref(v_opts_167_);
v___x_236_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__4));
v___x_237_ = lean_string_append(v___x_236_, v_arg_168_);
lean_dec_ref(v_arg_168_);
v___x_238_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__5));
v___x_239_ = lean_string_append(v___x_237_, v___x_238_);
v___x_240_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
v___x_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption___boxed(lean_object* v_opts_242_, lean_object* v_arg_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_LeanIR_0__setConfigOption(v_opts_242_, v_arg_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1(lean_object* v_val_246_, lean_object* v_inst_247_, lean_object* v_R_248_, lean_object* v_a_249_, lean_object* v_b_250_, lean_object* v_c_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___redArg(v_val_246_, v_a_249_, v_b_250_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1___boxed(lean_object* v_val_253_, lean_object* v_inst_254_, lean_object* v_R_255_, lean_object* v_a_256_, lean_object* v_b_257_, lean_object* v_c_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__1(v_val_253_, v_inst_254_, v_R_255_, v_a_256_, v_b_257_, v_c_258_);
lean_dec(v_b_257_);
lean_dec_ref(v_val_253_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg(lean_object* v___x_260_, lean_object* v_inst_261_, lean_object* v_ext_262_, lean_object* v_env_263_){
_start:
{
lean_object* v_toEnvExtension_265_; lean_object* v_addImportedFn_266_; lean_object* v_asyncMode_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v_importedEntries_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_298_; 
v_toEnvExtension_265_ = lean_ctor_get(v_ext_262_, 0);
lean_inc_ref(v_toEnvExtension_265_);
v_addImportedFn_266_ = lean_ctor_get(v_ext_262_, 2);
lean_inc_ref(v_addImportedFn_266_);
lean_dec_ref(v_ext_262_);
v_asyncMode_267_ = lean_ctor_get(v_toEnvExtension_265_, 2);
v___x_268_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v_inst_261_);
lean_inc_ref(v_env_263_);
v___x_269_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_268_, v_toEnvExtension_265_, v_env_263_, v_asyncMode_267_, v___x_260_);
lean_dec_ref(v___x_268_);
v_importedEntries_270_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_298_ == 0)
{
lean_object* v_unused_299_; 
v_unused_299_ = lean_ctor_get(v___x_269_, 1);
lean_dec(v_unused_299_);
v___x_272_ = v___x_269_;
v_isShared_273_ = v_isSharedCheck_298_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_importedEntries_270_);
lean_dec(v___x_269_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_298_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = l_Lean_Options_empty;
lean_inc_ref(v_env_263_);
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v_env_263_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
lean_inc_ref(v_importedEntries_270_);
v___x_276_ = lean_apply_3(v_addImportedFn_266_, v_importedEntries_270_, v___x_275_, lean_box(0));
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_289_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_289_ == 0)
{
v___x_279_ = v___x_276_;
v_isShared_280_ = v_isSharedCheck_289_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_276_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_289_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 1, v_a_277_);
v___x_282_ = v___x_272_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_importedEntries_270_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_a_277_);
v___x_282_ = v_reuseFailAlloc_288_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_283_ = lean_box(0);
v___x_284_ = l_Lean_EnvExtension_setState___redArg(v_toEnvExtension_265_, v_env_263_, v___x_282_, v___x_283_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_284_);
v___x_286_ = v___x_279_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
else
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
lean_del_object(v___x_272_);
lean_dec_ref(v_importedEntries_270_);
lean_dec_ref(v_toEnvExtension_265_);
lean_dec_ref(v_env_263_);
v_a_290_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___x_276_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_276_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_290_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg___boxed(lean_object* v___x_300_, lean_object* v_inst_301_, lean_object* v_ext_302_, lean_object* v_env_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_main___elam__0___redArg(v___x_300_, v_inst_301_, v_ext_302_, v_env_303_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0(lean_object* v___x_306_, lean_object* v_00_u03b1_307_, lean_object* v_00_u03b2_308_, lean_object* v_00_u03c3_309_, lean_object* v_inst_310_, lean_object* v_ext_311_, lean_object* v_env_312_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_main___elam__0___redArg(v___x_306_, v_inst_310_, v_ext_311_, v_env_312_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___boxed(lean_object* v___x_315_, lean_object* v_00_u03b1_316_, lean_object* v_00_u03b2_317_, lean_object* v_00_u03c3_318_, lean_object* v_inst_319_, lean_object* v_ext_320_, lean_object* v_env_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_main___elam__0(v___x_315_, v_00_u03b1_316_, v_00_u03b2_317_, v_00_u03c3_318_, v_inst_319_, v_ext_320_, v_env_321_);
return v_res_323_;
}
}
static lean_object* _init_l_panic___at___00main_spec__5___closed__0(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = l_instInhabitedError;
v___x_325_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_325_, 0, lean_box(0));
lean_closure_set(v___x_325_, 1, lean_box(0));
lean_closure_set(v___x_325_, 2, v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5(lean_object* v_msg_326_){
_start:
{
lean_object* v___x_328_; lean_object* v___x_20091__overap_329_; lean_object* v___x_330_; 
v___x_328_ = lean_obj_once(&l_panic___at___00main_spec__5___closed__0, &l_panic___at___00main_spec__5___closed__0_once, _init_l_panic___at___00main_spec__5___closed__0);
v___x_20091__overap_329_ = lean_panic_fn_borrowed(v___x_328_, v_msg_326_);
v___x_330_ = lean_apply_1(v___x_20091__overap_329_, lean_box(0));
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5___boxed(lean_object* v_msg_331_, lean_object* v___y_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_panic___at___00main_spec__5(v_msg_331_);
return v_res_333_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00main_spec__8(lean_object* v_opts_334_, lean_object* v_opt_335_){
_start:
{
lean_object* v_name_336_; lean_object* v_defValue_337_; lean_object* v_map_338_; lean_object* v___x_339_; 
v_name_336_ = lean_ctor_get(v_opt_335_, 0);
v_defValue_337_ = lean_ctor_get(v_opt_335_, 1);
v_map_338_ = lean_ctor_get(v_opts_334_, 0);
v___x_339_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_338_, v_name_336_);
if (lean_obj_tag(v___x_339_) == 0)
{
uint8_t v___x_340_; 
v___x_340_ = lean_unbox(v_defValue_337_);
return v___x_340_;
}
else
{
lean_object* v_val_341_; 
v_val_341_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_val_341_);
lean_dec_ref_known(v___x_339_, 1);
if (lean_obj_tag(v_val_341_) == 1)
{
uint8_t v_v_342_; 
v_v_342_ = lean_ctor_get_uint8(v_val_341_, 0);
lean_dec_ref_known(v_val_341_, 0);
return v_v_342_;
}
else
{
uint8_t v___x_343_; 
lean_dec(v_val_341_);
v___x_343_ = lean_unbox(v_defValue_337_);
return v___x_343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8___boxed(lean_object* v_opts_344_, lean_object* v_opt_345_){
_start:
{
uint8_t v_res_346_; lean_object* v_r_347_; 
v_res_346_ = l_Lean_Option_get___at___00main_spec__8(v_opts_344_, v_opt_345_);
lean_dec_ref(v_opt_345_);
lean_dec_ref(v_opts_344_);
v_r_347_ = lean_box(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__9(lean_object* v_opts_348_, lean_object* v_opt_349_){
_start:
{
lean_object* v_name_350_; lean_object* v_defValue_351_; lean_object* v_map_352_; lean_object* v___x_353_; 
v_name_350_ = lean_ctor_get(v_opt_349_, 0);
v_defValue_351_ = lean_ctor_get(v_opt_349_, 1);
v_map_352_ = lean_ctor_get(v_opts_348_, 0);
v___x_353_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_352_, v_name_350_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_inc(v_defValue_351_);
return v_defValue_351_;
}
else
{
lean_object* v_val_354_; 
v_val_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_val_354_);
lean_dec_ref_known(v___x_353_, 1);
if (lean_obj_tag(v_val_354_) == 3)
{
lean_object* v_v_355_; 
v_v_355_ = lean_ctor_get(v_val_354_, 0);
lean_inc(v_v_355_);
lean_dec_ref_known(v_val_354_, 1);
return v_v_355_;
}
else
{
lean_dec(v_val_354_);
lean_inc(v_defValue_351_);
return v_defValue_351_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__9___boxed(lean_object* v_opts_356_, lean_object* v_opt_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Option_get___at___00main_spec__9(v_opts_356_, v_opt_357_);
lean_dec_ref(v_opt_357_);
lean_dec_ref(v_opts_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(lean_object* v___x_359_, lean_object* v_a_360_, lean_object* v_x_361_){
_start:
{
if (lean_obj_tag(v_x_361_) == 0)
{
lean_dec(v_a_360_);
return v_x_361_;
}
else
{
lean_object* v_key_362_; lean_object* v_value_363_; lean_object* v_tail_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_411_; 
v_key_362_ = lean_ctor_get(v_x_361_, 0);
v_value_363_ = lean_ctor_get(v_x_361_, 1);
v_tail_364_ = lean_ctor_get(v_x_361_, 2);
v_isSharedCheck_411_ = !lean_is_exclusive(v_x_361_);
if (v_isSharedCheck_411_ == 0)
{
v___x_366_ = v_x_361_;
v_isShared_367_ = v_isSharedCheck_411_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_tail_364_);
lean_inc(v_value_363_);
lean_inc(v_key_362_);
lean_dec(v_x_361_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_411_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
uint8_t v___x_368_; 
v___x_368_ = lean_name_eq(v_key_362_, v_a_360_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_369_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v___x_359_, v_a_360_, v_tail_364_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 2, v___x_369_);
v___x_371_ = v___x_366_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_key_362_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_value_363_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
else
{
lean_object* v_toEffectiveImport_373_; lean_object* v_toImport_374_; lean_object* v_parts_375_; lean_object* v_irData_x3f_376_; uint8_t v_needsIRTrans_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_409_; 
lean_dec(v_key_362_);
v_toEffectiveImport_373_ = lean_ctor_get(v_value_363_, 0);
lean_inc_ref(v_toEffectiveImport_373_);
v_toImport_374_ = lean_ctor_get(v_toEffectiveImport_373_, 0);
lean_inc_ref(v_toImport_374_);
v_parts_375_ = lean_ctor_get(v_value_363_, 1);
v_irData_x3f_376_ = lean_ctor_get(v_value_363_, 2);
v_needsIRTrans_377_ = lean_ctor_get_uint8(v_value_363_, sizeof(void*)*3);
v_isSharedCheck_409_ = !lean_is_exclusive(v_value_363_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; 
v_unused_410_ = lean_ctor_get(v_value_363_, 0);
lean_dec(v_unused_410_);
v___x_379_ = v_value_363_;
v_isShared_380_ = v_isSharedCheck_409_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_irData_x3f_376_);
lean_inc(v_parts_375_);
lean_dec(v_value_363_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_409_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
uint8_t v_hasData_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_407_; 
v_hasData_381_ = lean_ctor_get_uint8(v_toEffectiveImport_373_, sizeof(void*)*1 + 1);
v_isSharedCheck_407_ = !lean_is_exclusive(v_toEffectiveImport_373_);
if (v_isSharedCheck_407_ == 0)
{
lean_object* v_unused_408_; 
v_unused_408_ = lean_ctor_get(v_toEffectiveImport_373_, 0);
lean_dec(v_unused_408_);
v___x_383_ = v_toEffectiveImport_373_;
v_isShared_384_ = v_isSharedCheck_407_;
goto v_resetjp_382_;
}
else
{
lean_dec(v_toEffectiveImport_373_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_407_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v_module_385_; uint8_t v___x_386_; 
v_module_385_ = lean_ctor_get(v_toImport_374_, 0);
v___x_386_ = lean_name_eq(v_module_385_, v___x_359_);
if (v___x_386_ == 0)
{
uint8_t v___x_387_; lean_object* v___x_389_; 
v___x_387_ = 2;
if (v_isShared_384_ == 0)
{
v___x_389_ = v___x_383_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_toImport_374_);
lean_ctor_set_uint8(v_reuseFailAlloc_396_, sizeof(void*)*1 + 1, v_hasData_381_);
v___x_389_ = v_reuseFailAlloc_396_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v___x_391_; 
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*1, v___x_387_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v___x_389_);
v___x_391_ = v___x_379_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_389_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_parts_375_);
lean_ctor_set(v_reuseFailAlloc_395_, 2, v_irData_x3f_376_);
lean_ctor_set_uint8(v_reuseFailAlloc_395_, sizeof(void*)*3, v_needsIRTrans_377_);
v___x_391_ = v_reuseFailAlloc_395_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___x_393_; 
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 1, v___x_391_);
lean_ctor_set(v___x_366_, 0, v_a_360_);
v___x_393_ = v___x_366_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_360_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_394_, 2, v_tail_364_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
else
{
uint8_t v___x_397_; lean_object* v___x_399_; 
v___x_397_ = 0;
if (v_isShared_384_ == 0)
{
v___x_399_ = v___x_383_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_toImport_374_);
lean_ctor_set_uint8(v_reuseFailAlloc_406_, sizeof(void*)*1 + 1, v_hasData_381_);
v___x_399_ = v_reuseFailAlloc_406_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_401_; 
lean_ctor_set_uint8(v___x_399_, sizeof(void*)*1, v___x_397_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v___x_399_);
v___x_401_ = v___x_379_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_parts_375_);
lean_ctor_set(v_reuseFailAlloc_405_, 2, v_irData_x3f_376_);
lean_ctor_set_uint8(v_reuseFailAlloc_405_, sizeof(void*)*3, v_needsIRTrans_377_);
v___x_401_ = v_reuseFailAlloc_405_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_403_; 
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 1, v___x_401_);
lean_ctor_set(v___x_366_, 0, v_a_360_);
v___x_403_ = v___x_366_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_360_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v_tail_364_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5___boxed(lean_object* v___x_412_, lean_object* v_a_413_, lean_object* v_x_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v___x_412_, v_a_413_, v_x_414_);
lean_dec(v___x_412_);
return v_res_415_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0(void){
_start:
{
lean_object* v___x_416_; uint64_t v___x_417_; 
v___x_416_ = lean_unsigned_to_nat(1723u);
v___x_417_ = lean_uint64_of_nat(v___x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(lean_object* v___x_418_, lean_object* v_m_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_size_421_; lean_object* v_buckets_422_; lean_object* v___x_423_; uint64_t v___y_425_; 
v_size_421_ = lean_ctor_get(v_m_419_, 0);
v_buckets_422_ = lean_ctor_get(v_m_419_, 1);
v___x_423_ = lean_array_get_size(v_buckets_422_);
if (lean_obj_tag(v_a_420_) == 0)
{
uint64_t v___x_452_; 
v___x_452_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0);
v___y_425_ = v___x_452_;
goto v___jp_424_;
}
else
{
uint64_t v_hash_453_; 
v_hash_453_ = lean_ctor_get_uint64(v_a_420_, sizeof(void*)*2);
v___y_425_ = v_hash_453_;
goto v___jp_424_;
}
v___jp_424_:
{
uint64_t v___x_426_; uint64_t v___x_427_; uint64_t v_fold_428_; uint64_t v___x_429_; uint64_t v___x_430_; uint64_t v___x_431_; size_t v___x_432_; size_t v___x_433_; size_t v___x_434_; size_t v___x_435_; size_t v___x_436_; lean_object* v_bucket_437_; uint8_t v___x_438_; 
v___x_426_ = 32ULL;
v___x_427_ = lean_uint64_shift_right(v___y_425_, v___x_426_);
v_fold_428_ = lean_uint64_xor(v___y_425_, v___x_427_);
v___x_429_ = 16ULL;
v___x_430_ = lean_uint64_shift_right(v_fold_428_, v___x_429_);
v___x_431_ = lean_uint64_xor(v_fold_428_, v___x_430_);
v___x_432_ = lean_uint64_to_usize(v___x_431_);
v___x_433_ = lean_usize_of_nat(v___x_423_);
v___x_434_ = ((size_t)1ULL);
v___x_435_ = lean_usize_sub(v___x_433_, v___x_434_);
v___x_436_ = lean_usize_land(v___x_432_, v___x_435_);
v_bucket_437_ = lean_array_uget_borrowed(v_buckets_422_, v___x_436_);
v___x_438_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_a_420_, v_bucket_437_);
if (v___x_438_ == 0)
{
lean_dec(v_a_420_);
return v_m_419_;
}
else
{
lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_449_; 
lean_inc(v_bucket_437_);
lean_inc_ref(v_buckets_422_);
lean_inc(v_size_421_);
v_isSharedCheck_449_ = !lean_is_exclusive(v_m_419_);
if (v_isSharedCheck_449_ == 0)
{
lean_object* v_unused_450_; lean_object* v_unused_451_; 
v_unused_450_ = lean_ctor_get(v_m_419_, 1);
lean_dec(v_unused_450_);
v_unused_451_ = lean_ctor_get(v_m_419_, 0);
lean_dec(v_unused_451_);
v___x_440_ = v_m_419_;
v_isShared_441_ = v_isSharedCheck_449_;
goto v_resetjp_439_;
}
else
{
lean_dec(v_m_419_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_449_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v_buckets_443_; lean_object* v_bucket_444_; lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_442_ = lean_box(0);
v_buckets_443_ = lean_array_uset(v_buckets_422_, v___x_436_, v___x_442_);
v_bucket_444_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v___x_418_, v_a_420_, v_bucket_437_);
v___x_445_ = lean_array_uset(v_buckets_443_, v___x_436_, v_bucket_444_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 1, v___x_445_);
v___x_447_ = v___x_440_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_size_421_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v___x_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___boxed(lean_object* v___x_454_, lean_object* v_m_455_, lean_object* v_a_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(v___x_454_, v_m_455_, v_a_456_);
lean_dec(v___x_454_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_main___lam__0(lean_object* v___x_458_, lean_object* v___x_459_, uint8_t v___x_460_, lean_object* v___x_461_, uint8_t v___y_462_, lean_object* v_name_463_, lean_object* v___x_464_, uint8_t v___x_465_, uint8_t v___x_466_){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_st_mk_ref(v___x_458_);
v___x_469_ = l_Lean_importModulesCore(v___x_459_, v___x_460_, v___x_461_, v___y_462_, v___x_468_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v___x_470_; lean_object* v_moduleNameMap_471_; lean_object* v_moduleNames_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_485_; 
lean_dec_ref_known(v___x_469_, 1);
v___x_470_ = lean_st_ref_get(v___x_468_);
lean_dec(v___x_468_);
v_moduleNameMap_471_ = lean_ctor_get(v___x_470_, 0);
v_moduleNames_472_ = lean_ctor_get(v___x_470_, 1);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_485_ == 0)
{
v___x_474_ = v___x_470_;
v_isShared_475_ = v_isSharedCheck_485_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_moduleNames_472_);
lean_inc(v_moduleNameMap_471_);
lean_dec(v___x_470_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_485_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v___x_478_; 
lean_inc(v_name_463_);
v___x_476_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(v_name_463_, v_moduleNameMap_471_, v_name_463_);
lean_dec(v_name_463_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_476_);
v___x_478_ = v___x_474_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_moduleNames_472_);
v___x_478_ = v_reuseFailAlloc_484_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
uint32_t v___x_479_; uint8_t v___x_480_; uint8_t v___x_481_; 
v___x_479_ = 0;
v___x_480_ = 0;
v___x_481_ = l_Lean_instDecidableEqOLeanLevel(v___x_480_, v___x_460_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_finalizeImport(v___x_478_, v___x_459_, v___x_464_, v___x_479_, v___x_465_, v___x_466_, v___x_480_, v___x_465_);
lean_dec_ref(v___x_478_);
return v___x_482_;
}
else
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_finalizeImport(v___x_478_, v___x_459_, v___x_464_, v___x_479_, v___x_465_, v___x_466_, v___x_480_, v___x_466_);
lean_dec_ref(v___x_478_);
return v___x_483_;
}
}
}
}
else
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
lean_dec(v___x_468_);
lean_dec_ref(v___x_464_);
lean_dec(v_name_463_);
lean_dec_ref(v___x_459_);
v_a_486_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_469_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_469_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__0___boxed(lean_object* v___x_494_, lean_object* v___x_495_, lean_object* v___x_496_, lean_object* v___x_497_, lean_object* v___y_498_, lean_object* v_name_499_, lean_object* v___x_500_, lean_object* v___x_501_, lean_object* v___x_502_, lean_object* v___y_503_){
_start:
{
uint8_t v___x_36246__boxed_504_; uint8_t v___y_36248__boxed_505_; uint8_t v___x_36250__boxed_506_; uint8_t v___x_36251__boxed_507_; lean_object* v_res_508_; 
v___x_36246__boxed_504_ = lean_unbox(v___x_496_);
v___y_36248__boxed_505_ = lean_unbox(v___y_498_);
v___x_36250__boxed_506_ = lean_unbox(v___x_501_);
v___x_36251__boxed_507_ = lean_unbox(v___x_502_);
v_res_508_ = l_main___lam__0(v___x_494_, v___x_495_, v___x_36246__boxed_504_, v___x_497_, v___y_36248__boxed_505_, v_name_499_, v___x_500_, v___x_36250__boxed_506_, v___x_36251__boxed_507_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_main___lam__1(lean_object* v___x_510_, lean_object* v___x_511_, lean_object* v___x_512_, lean_object* v_name_513_, lean_object* v_a_514_, lean_object* v___x_515_, lean_object* v_head_516_, lean_object* v___x_517_, lean_object* v___x_518_, lean_object* v___x_519_, lean_object* v___x_520_, lean_object* v___x_521_, lean_object* v___x_522_, lean_object* v___x_523_, lean_object* v___x_524_, uint8_t v___x_525_, uint8_t v___x_526_){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v_env_532_; lean_object* v___x_533_; uint8_t v___x_534_; lean_object* v_fileName_536_; lean_object* v_fileMap_537_; lean_object* v_currRecDepth_538_; lean_object* v_ref_539_; lean_object* v_currNamespace_540_; lean_object* v_openDecls_541_; lean_object* v_initHeartbeats_542_; lean_object* v_maxHeartbeats_543_; lean_object* v_quotContext_544_; lean_object* v_currMacroScope_545_; lean_object* v_cancelTk_x3f_546_; uint8_t v_suppressElabErrors_547_; lean_object* v_inheritedTraceOptions_548_; lean_object* v___y_549_; uint8_t v___y_578_; uint8_t v___x_598_; 
v___x_528_ = lean_io_get_num_heartbeats();
v___x_529_ = lean_st_mk_ref(v___x_510_);
v___x_530_ = lean_st_ref_get(v___x_511_);
v___x_531_ = lean_st_ref_get(v___x_529_);
v_env_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc_ref(v_env_532_);
lean_dec(v___x_531_);
v___x_533_ = l_Lean_diagnostics;
v___x_534_ = l_Lean_Option_get___at___00main_spec__8(v___x_512_, v___x_533_);
v___x_598_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_532_);
lean_dec_ref(v_env_532_);
if (v___x_598_ == 0)
{
if (v___x_534_ == 0)
{
v___y_578_ = v___x_526_;
goto v___jp_577_;
}
else
{
v___y_578_ = v___x_598_;
goto v___jp_577_;
}
}
else
{
v___y_578_ = v___x_534_;
goto v___jp_577_;
}
v___jp_535_:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_550_ = l_Lean_maxRecDepth;
v___x_551_ = l_Lean_Option_get___at___00main_spec__9(v___x_512_, v___x_550_);
v___x_552_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_552_, 0, v_fileName_536_);
lean_ctor_set(v___x_552_, 1, v_fileMap_537_);
lean_ctor_set(v___x_552_, 2, v___x_512_);
lean_ctor_set(v___x_552_, 3, v_currRecDepth_538_);
lean_ctor_set(v___x_552_, 4, v___x_551_);
lean_ctor_set(v___x_552_, 5, v_ref_539_);
lean_ctor_set(v___x_552_, 6, v_currNamespace_540_);
lean_ctor_set(v___x_552_, 7, v_openDecls_541_);
lean_ctor_set(v___x_552_, 8, v_initHeartbeats_542_);
lean_ctor_set(v___x_552_, 9, v_maxHeartbeats_543_);
lean_ctor_set(v___x_552_, 10, v_quotContext_544_);
lean_ctor_set(v___x_552_, 11, v_currMacroScope_545_);
lean_ctor_set(v___x_552_, 12, v_cancelTk_x3f_546_);
lean_ctor_set(v___x_552_, 13, v_inheritedTraceOptions_548_);
lean_ctor_set_uint8(v___x_552_, sizeof(void*)*14, v___x_534_);
lean_ctor_set_uint8(v___x_552_, sizeof(void*)*14 + 1, v_suppressElabErrors_547_);
v___x_553_ = l_Lean_Compiler_LCNF_emitC(v_name_513_, v___x_552_, v___y_549_);
lean_dec(v___y_549_);
lean_dec_ref_known(v___x_552_, 14);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref_known(v___x_553_, 1);
v___x_555_ = lean_st_ref_get(v___x_529_);
lean_dec(v___x_529_);
lean_dec(v___x_555_);
v___x_556_ = lean_string_to_utf8(v_a_554_);
lean_dec(v_a_554_);
v___x_557_ = lean_io_prim_handle_write(v_a_514_, v___x_556_);
lean_dec_ref(v___x_556_);
return v___x_557_;
}
else
{
lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_576_; 
lean_dec(v___x_529_);
v_a_558_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_576_ == 0)
{
v___x_560_ = v___x_553_;
v_isShared_561_ = v_isSharedCheck_576_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_553_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_576_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
if (lean_obj_tag(v_a_558_) == 0)
{
lean_object* v_msg_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_566_; 
v_msg_562_ = lean_ctor_get(v_a_558_, 1);
lean_inc_ref(v_msg_562_);
lean_dec_ref_known(v_a_558_, 2);
v___x_563_ = l_Lean_MessageData_toString(v_msg_562_);
v___x_564_ = lean_mk_io_user_error(v___x_563_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v___x_564_);
v___x_566_ = v___x_560_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_564_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
else
{
lean_object* v_id_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
v_id_568_ = lean_ctor_get(v_a_558_, 0);
lean_inc(v_id_568_);
lean_dec_ref_known(v_a_558_, 2);
v___x_569_ = ((lean_object*)(l_main___lam__1___closed__0));
v___x_570_ = l_Nat_reprFast(v_id_568_);
v___x_571_ = lean_string_append(v___x_569_, v___x_570_);
lean_dec_ref(v___x_570_);
v___x_572_ = lean_mk_io_user_error(v___x_571_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v___x_572_);
v___x_574_ = v___x_560_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
}
v___jp_577_:
{
if (v___y_578_ == 0)
{
lean_object* v___x_579_; lean_object* v_env_580_; lean_object* v_nextMacroScope_581_; lean_object* v_ngen_582_; lean_object* v_auxDeclNGen_583_; lean_object* v_traceState_584_; lean_object* v_messages_585_; lean_object* v_infoState_586_; lean_object* v_snapshotTasks_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_596_; 
v___x_579_ = lean_st_ref_take(v___x_529_);
v_env_580_ = lean_ctor_get(v___x_579_, 0);
v_nextMacroScope_581_ = lean_ctor_get(v___x_579_, 1);
v_ngen_582_ = lean_ctor_get(v___x_579_, 2);
v_auxDeclNGen_583_ = lean_ctor_get(v___x_579_, 3);
v_traceState_584_ = lean_ctor_get(v___x_579_, 4);
v_messages_585_ = lean_ctor_get(v___x_579_, 6);
v_infoState_586_ = lean_ctor_get(v___x_579_, 7);
v_snapshotTasks_587_ = lean_ctor_get(v___x_579_, 8);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_596_ == 0)
{
lean_object* v_unused_597_; 
v_unused_597_ = lean_ctor_get(v___x_579_, 5);
lean_dec(v_unused_597_);
v___x_589_ = v___x_579_;
v_isShared_590_ = v_isSharedCheck_596_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_snapshotTasks_587_);
lean_inc(v_infoState_586_);
lean_inc(v_messages_585_);
lean_inc(v_traceState_584_);
lean_inc(v_auxDeclNGen_583_);
lean_inc(v_ngen_582_);
lean_inc(v_nextMacroScope_581_);
lean_inc(v_env_580_);
lean_dec(v___x_579_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_596_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_591_ = l_Lean_Kernel_enableDiag(v_env_580_, v___x_534_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 5, v___x_515_);
lean_ctor_set(v___x_589_, 0, v___x_591_);
v___x_593_ = v___x_589_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_nextMacroScope_581_);
lean_ctor_set(v_reuseFailAlloc_595_, 2, v_ngen_582_);
lean_ctor_set(v_reuseFailAlloc_595_, 3, v_auxDeclNGen_583_);
lean_ctor_set(v_reuseFailAlloc_595_, 4, v_traceState_584_);
lean_ctor_set(v_reuseFailAlloc_595_, 5, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_595_, 6, v_messages_585_);
lean_ctor_set(v_reuseFailAlloc_595_, 7, v_infoState_586_);
lean_ctor_set(v_reuseFailAlloc_595_, 8, v_snapshotTasks_587_);
v___x_593_ = v_reuseFailAlloc_595_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
lean_object* v___x_594_; 
v___x_594_ = lean_st_ref_set(v___x_529_, v___x_593_);
lean_inc(v___x_529_);
lean_inc(v___x_520_);
v_fileName_536_ = v_head_516_;
v_fileMap_537_ = v___x_517_;
v_currRecDepth_538_ = v___x_518_;
v_ref_539_ = v___x_519_;
v_currNamespace_540_ = v___x_520_;
v_openDecls_541_ = v___x_521_;
v_initHeartbeats_542_ = v___x_528_;
v_maxHeartbeats_543_ = v___x_522_;
v_quotContext_544_ = v___x_520_;
v_currMacroScope_545_ = v___x_523_;
v_cancelTk_x3f_546_ = v___x_524_;
v_suppressElabErrors_547_ = v___x_525_;
v_inheritedTraceOptions_548_ = v___x_530_;
v___y_549_ = v___x_529_;
goto v___jp_535_;
}
}
}
else
{
lean_dec_ref(v___x_515_);
lean_inc(v___x_529_);
lean_inc(v___x_520_);
v_fileName_536_ = v_head_516_;
v_fileMap_537_ = v___x_517_;
v_currRecDepth_538_ = v___x_518_;
v_ref_539_ = v___x_519_;
v_currNamespace_540_ = v___x_520_;
v_openDecls_541_ = v___x_521_;
v_initHeartbeats_542_ = v___x_528_;
v_maxHeartbeats_543_ = v___x_522_;
v_quotContext_544_ = v___x_520_;
v_currMacroScope_545_ = v___x_523_;
v_cancelTk_x3f_546_ = v___x_524_;
v_suppressElabErrors_547_ = v___x_525_;
v_inheritedTraceOptions_548_ = v___x_530_;
v___y_549_ = v___x_529_;
goto v___jp_535_;
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__1___boxed(lean_object** _args){
lean_object* v___x_599_ = _args[0];
lean_object* v___x_600_ = _args[1];
lean_object* v___x_601_ = _args[2];
lean_object* v_name_602_ = _args[3];
lean_object* v_a_603_ = _args[4];
lean_object* v___x_604_ = _args[5];
lean_object* v_head_605_ = _args[6];
lean_object* v___x_606_ = _args[7];
lean_object* v___x_607_ = _args[8];
lean_object* v___x_608_ = _args[9];
lean_object* v___x_609_ = _args[10];
lean_object* v___x_610_ = _args[11];
lean_object* v___x_611_ = _args[12];
lean_object* v___x_612_ = _args[13];
lean_object* v___x_613_ = _args[14];
lean_object* v___x_614_ = _args[15];
lean_object* v___x_615_ = _args[16];
lean_object* v___y_616_ = _args[17];
_start:
{
uint8_t v___x_36336__boxed_617_; uint8_t v___x_36337__boxed_618_; lean_object* v_res_619_; 
v___x_36336__boxed_617_ = lean_unbox(v___x_614_);
v___x_36337__boxed_618_ = lean_unbox(v___x_615_);
v_res_619_ = l_main___lam__1(v___x_599_, v___x_600_, v___x_601_, v_name_602_, v_a_603_, v___x_604_, v_head_605_, v___x_606_, v___x_607_, v___x_608_, v___x_609_, v___x_610_, v___x_611_, v___x_612_, v___x_613_, v___x_36336__boxed_617_, v___x_36337__boxed_618_);
lean_dec(v_a_603_);
lean_dec(v___x_600_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(lean_object* v_s_620_){
_start:
{
lean_object* v___x_622_; lean_object* v_putStr_623_; lean_object* v___x_624_; 
v___x_622_ = lean_get_stderr();
v_putStr_623_ = lean_ctor_get(v___x_622_, 4);
lean_inc_ref(v_putStr_623_);
lean_dec_ref(v___x_622_);
v___x_624_ = lean_apply_2(v_putStr_623_, v_s_620_, lean_box(0));
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8___boxed(lean_object* v_s_625_, lean_object* v_a_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v_s_625_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6(lean_object* v_s_628_){
_start:
{
uint32_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_630_ = 10;
v___x_631_ = lean_string_push(v_s_628_, v___x_630_);
v___x_632_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v___x_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6___boxed(lean_object* v_s_633_, lean_object* v_a_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_IO_eprintln___at___00main_spec__6(v_s_633_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(lean_object* v_o_639_, lean_object* v_k_640_, lean_object* v_v_641_){
_start:
{
lean_object* v_map_642_; uint8_t v_hasTrace_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_657_; 
v_map_642_ = lean_ctor_get(v_o_639_, 0);
v_hasTrace_643_ = lean_ctor_get_uint8(v_o_639_, sizeof(void*)*1);
v_isSharedCheck_657_ = !lean_is_exclusive(v_o_639_);
if (v_isSharedCheck_657_ == 0)
{
v___x_645_ = v_o_639_;
v_isShared_646_ = v_isSharedCheck_657_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_map_642_);
lean_dec(v_o_639_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_657_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_647_, 0, v_v_641_);
lean_inc(v_k_640_);
v___x_648_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_640_, v___x_647_, v_map_642_);
if (v_hasTrace_643_ == 0)
{
lean_object* v___x_649_; uint8_t v___x_650_; lean_object* v___x_652_; 
v___x_649_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_650_ = l_Lean_Name_isPrefixOf(v___x_649_, v_k_640_);
lean_dec(v_k_640_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v___x_648_);
v___x_652_ = v___x_645_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_648_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
lean_ctor_set_uint8(v___x_652_, sizeof(void*)*1, v___x_650_);
return v___x_652_;
}
}
else
{
lean_object* v___x_655_; 
lean_dec(v_k_640_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v___x_648_);
v___x_655_ = v___x_645_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_648_);
lean_ctor_set_uint8(v_reuseFailAlloc_656_, sizeof(void*)*1, v_hasTrace_643_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00main_spec__3(lean_object* v_opts_658_, lean_object* v_opt_659_, lean_object* v_val_660_){
_start:
{
lean_object* v_name_661_; lean_object* v___x_662_; 
v_name_661_ = lean_ctor_get(v_opt_659_, 0);
lean_inc(v_name_661_);
lean_dec_ref(v_opt_659_);
v___x_662_ = l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(v_opts_658_, v_name_661_, v_val_660_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object* v___y_664_, lean_object* v_as_665_, size_t v_i_666_, size_t v_stop_667_, lean_object* v_b_668_){
_start:
{
lean_object* v___y_670_; uint8_t v___x_674_; 
v___x_674_ = lean_usize_dec_eq(v_i_666_, v_stop_667_);
if (v___x_674_ == 0)
{
lean_object* v_fst_675_; lean_object* v_snd_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___y_680_; 
v_fst_675_ = lean_ctor_get(v_b_668_, 0);
v_snd_676_ = lean_ctor_get(v_b_668_, 1);
v___x_677_ = lean_array_uget_borrowed(v_as_665_, v_i_666_);
v___x_678_ = l_Lean_IR_Decl_name(v___x_677_);
if (lean_obj_tag(v___x_678_) == 1)
{
lean_object* v_pre_693_; lean_object* v_str_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v_pre_693_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_pre_693_);
v_str_694_ = lean_ctor_get(v___x_678_, 1);
lean_inc_ref(v_str_694_);
v___x_695_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___closed__0));
v___x_696_ = lean_string_dec_eq(v_str_694_, v___x_695_);
lean_dec_ref(v_str_694_);
if (v___x_696_ == 0)
{
lean_dec(v_pre_693_);
lean_inc_ref(v___x_678_);
v___y_680_ = v___x_678_;
goto v___jp_679_;
}
else
{
v___y_680_ = v_pre_693_;
goto v___jp_679_;
}
}
else
{
lean_inc(v___x_678_);
v___y_680_ = v___x_678_;
goto v___jp_679_;
}
v___jp_679_:
{
uint8_t v___x_681_; 
lean_inc_ref(v___y_664_);
v___x_681_ = l_Lean_isExtern(v___y_664_, v___y_680_);
if (v___x_681_ == 0)
{
lean_dec(v___x_678_);
v___y_670_ = v_b_668_;
goto v___jp_669_;
}
else
{
lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_690_; 
lean_inc(v_snd_676_);
lean_inc(v_fst_675_);
v_isSharedCheck_690_ = !lean_is_exclusive(v_b_668_);
if (v_isSharedCheck_690_ == 0)
{
lean_object* v_unused_691_; lean_object* v_unused_692_; 
v_unused_691_ = lean_ctor_get(v_b_668_, 1);
lean_dec(v_unused_691_);
v_unused_692_ = lean_ctor_get(v_b_668_, 0);
lean_dec(v_unused_692_);
v___x_683_ = v_b_668_;
v_isShared_684_ = v_isSharedCheck_690_;
goto v_resetjp_682_;
}
else
{
lean_dec(v_b_668_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_690_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_688_; 
lean_inc_n(v___x_677_, 2);
v___x_685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_677_);
lean_ctor_set(v___x_685_, 1, v_fst_675_);
v___x_686_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_676_, v___x_678_, v___x_677_);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 1, v___x_686_);
lean_ctor_set(v___x_683_, 0, v___x_685_);
v___x_688_ = v___x_683_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_685_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v___x_686_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
v___y_670_ = v___x_688_;
goto v___jp_669_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_664_);
return v_b_668_;
}
v___jp_669_:
{
size_t v___x_671_; size_t v___x_672_; 
v___x_671_ = ((size_t)1ULL);
v___x_672_ = lean_usize_add(v_i_666_, v___x_671_);
v_i_666_ = v___x_672_;
v_b_668_ = v___y_670_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object* v___y_697_, lean_object* v_as_698_, lean_object* v_i_699_, lean_object* v_stop_700_, lean_object* v_b_701_){
_start:
{
size_t v_i_boxed_702_; size_t v_stop_boxed_703_; lean_object* v_res_704_; 
v_i_boxed_702_ = lean_unbox_usize(v_i_699_);
lean_dec(v_i_699_);
v_stop_boxed_703_ = lean_unbox_usize(v_stop_700_);
lean_dec(v_stop_700_);
v_res_704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_697_, v_as_698_, v_i_boxed_702_, v_stop_boxed_703_, v_b_701_);
lean_dec_ref(v_as_698_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg(lean_object* v_as_x27_706_, lean_object* v_b_707_){
_start:
{
if (lean_obj_tag(v_as_x27_706_) == 0)
{
lean_object* v___x_709_; 
v___x_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_709_, 0, v_b_707_);
return v___x_709_;
}
else
{
lean_object* v_head_710_; lean_object* v_tail_711_; lean_object* v_fst_712_; lean_object* v_snd_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_738_; 
v_head_710_ = lean_ctor_get(v_as_x27_706_, 0);
v_tail_711_ = lean_ctor_get(v_as_x27_706_, 1);
v_fst_712_ = lean_ctor_get(v_b_707_, 0);
v_snd_713_ = lean_ctor_get(v_b_707_, 1);
v_isSharedCheck_738_ = !lean_is_exclusive(v_b_707_);
if (v_isSharedCheck_738_ == 0)
{
v___x_715_ = v_b_707_;
v_isShared_716_ = v_isSharedCheck_738_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_snd_713_);
lean_inc(v_fst_712_);
lean_dec(v_b_707_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_738_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_717_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0));
v___x_718_ = lean_string_dec_eq(v_head_710_, v___x_717_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; 
lean_inc(v_head_710_);
v___x_719_ = l___private_LeanIR_0__setConfigOption(v_snd_713_, v_head_710_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_722_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_720_);
lean_dec_ref_known(v___x_719_, 1);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 1, v_a_720_);
v___x_722_ = v___x_715_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_fst_712_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_a_720_);
v___x_722_ = v_reuseFailAlloc_724_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
v_as_x27_706_ = v_tail_711_;
v_b_707_ = v___x_722_;
goto _start;
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_del_object(v___x_715_);
lean_dec(v_fst_712_);
v_a_725_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_719_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_719_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
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
else
{
lean_object* v___x_733_; lean_object* v___x_735_; 
lean_dec(v_fst_712_);
v___x_733_ = lean_box(v___x_718_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_733_);
v___x_735_ = v___x_715_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_snd_713_);
v___x_735_ = v_reuseFailAlloc_737_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
v_as_x27_706_ = v_tail_711_;
v_b_707_ = v___x_735_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(lean_object* v_as_x27_739_, lean_object* v_b_740_, lean_object* v___y_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_739_, v_b_740_);
lean_dec(v_as_x27_739_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object* v_as_743_, size_t v_i_744_, size_t v_stop_745_, lean_object* v_b_746_){
_start:
{
uint8_t v___x_747_; 
v___x_747_ = lean_usize_dec_eq(v_i_744_, v_stop_745_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; lean_object* v_toEnvExtension_749_; lean_object* v_asyncMode_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; size_t v___x_754_; size_t v___x_755_; 
v___x_748_ = l_Lean_Compiler_LCNF_impureSigExt;
v_toEnvExtension_749_ = lean_ctor_get(v___x_748_, 0);
v_asyncMode_750_ = lean_ctor_get(v_toEnvExtension_749_, 2);
v___x_751_ = lean_box(0);
v___x_752_ = lean_array_uget_borrowed(v_as_743_, v_i_744_);
lean_inc(v___x_752_);
v___x_753_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_748_, v_b_746_, v___x_752_, v_asyncMode_750_, v___x_751_);
v___x_754_ = ((size_t)1ULL);
v___x_755_ = lean_usize_add(v_i_744_, v___x_754_);
v_i_744_ = v___x_755_;
v_b_746_ = v___x_753_;
goto _start;
}
else
{
return v_b_746_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object* v_as_757_, lean_object* v_i_758_, lean_object* v_stop_759_, lean_object* v_b_760_){
_start:
{
size_t v_i_boxed_761_; size_t v_stop_boxed_762_; lean_object* v_res_763_; 
v_i_boxed_761_ = lean_unbox_usize(v_i_758_);
lean_dec(v_i_758_);
v_stop_boxed_762_ = lean_unbox_usize(v_stop_759_);
lean_dec(v_stop_759_);
v_res_763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_as_757_, v_i_boxed_761_, v_stop_boxed_762_, v_b_760_);
lean_dec_ref(v_as_757_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(lean_object* v_as_767_, size_t v_sz_768_, size_t v_i_769_, lean_object* v_b_770_, lean_object* v___y_771_){
_start:
{
uint8_t v___x_773_; 
v___x_773_ = lean_usize_dec_lt(v_i_769_, v_sz_768_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; 
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v_b_770_);
return v___x_774_;
}
else
{
uint8_t v___x_775_; lean_object* v_a_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
lean_dec_ref(v_b_770_);
v___x_775_ = 0;
v_a_776_ = lean_array_uget_borrowed(v_as_767_, v_i_769_);
lean_inc(v_a_776_);
v___x_777_ = l_Lean_Message_toString(v_a_776_, v___x_775_);
v___x_778_ = l_IO_eprintln___at___00main_spec__6(v___x_777_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v___x_779_; size_t v___x_780_; size_t v___x_781_; 
lean_dec_ref_known(v___x_778_, 1);
v___x_779_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_780_ = ((size_t)1ULL);
v___x_781_ = lean_usize_add(v_i_769_, v___x_780_);
v_i_769_ = v___x_781_;
v_b_770_ = v___x_779_;
goto _start;
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_795_; 
v_a_783_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_795_ == 0)
{
v___x_785_ = v___x_778_;
v_isShared_786_ = v_isSharedCheck_795_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_778_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_795_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v_ref_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_793_; 
v_ref_787_ = lean_ctor_get(v___y_771_, 5);
v___x_788_ = lean_io_error_to_string(v_a_783_);
v___x_789_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
v___x_790_ = l_Lean_MessageData_ofFormat(v___x_789_);
lean_inc(v_ref_787_);
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v_ref_787_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___x_791_);
v___x_793_ = v___x_785_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_791_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___boxed(lean_object* v_as_796_, lean_object* v_sz_797_, lean_object* v_i_798_, lean_object* v_b_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
size_t v_sz_boxed_802_; size_t v_i_boxed_803_; lean_object* v_res_804_; 
v_sz_boxed_802_ = lean_unbox_usize(v_sz_797_);
lean_dec(v_sz_797_);
v_i_boxed_803_ = lean_unbox_usize(v_i_798_);
lean_dec(v_i_798_);
v_res_804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_796_, v_sz_boxed_802_, v_i_boxed_803_, v_b_799_, v___y_800_);
lean_dec_ref(v___y_800_);
lean_dec_ref(v_as_796_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(lean_object* v_as_805_, size_t v_sz_806_, size_t v_i_807_, lean_object* v_b_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
uint8_t v___x_812_; 
v___x_812_ = lean_usize_dec_lt(v_i_807_, v_sz_806_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; 
v___x_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_813_, 0, v_b_808_);
return v___x_813_;
}
else
{
uint8_t v___x_814_; lean_object* v_a_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
lean_dec_ref(v_b_808_);
v___x_814_ = 0;
v_a_815_ = lean_array_uget_borrowed(v_as_805_, v_i_807_);
lean_inc(v_a_815_);
v___x_816_ = l_Lean_Message_toString(v_a_815_, v___x_814_);
v___x_817_ = l_IO_eprintln___at___00main_spec__6(v___x_816_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v___x_818_; size_t v___x_819_; size_t v___x_820_; lean_object* v___x_821_; 
lean_dec_ref_known(v___x_817_, 1);
v___x_818_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_819_ = ((size_t)1ULL);
v___x_820_ = lean_usize_add(v_i_807_, v___x_819_);
v___x_821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_805_, v_sz_806_, v___x_820_, v___x_818_, v___y_809_);
return v___x_821_;
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_834_; 
v_a_822_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_834_ == 0)
{
v___x_824_ = v___x_817_;
v_isShared_825_ = v_isSharedCheck_834_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_817_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_834_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v_ref_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_832_; 
v_ref_826_ = lean_ctor_get(v___y_809_, 5);
v___x_827_ = lean_io_error_to_string(v_a_822_);
v___x_828_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
v___x_829_ = l_Lean_MessageData_ofFormat(v___x_828_);
lean_inc(v_ref_826_);
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v_ref_826_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_830_);
v___x_832_ = v___x_824_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27___boxed(lean_object* v_as_835_, lean_object* v_sz_836_, lean_object* v_i_837_, lean_object* v_b_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
size_t v_sz_boxed_842_; size_t v_i_boxed_843_; lean_object* v_res_844_; 
v_sz_boxed_842_ = lean_unbox_usize(v_sz_836_);
lean_dec(v_sz_836_);
v_i_boxed_843_ = lean_unbox_usize(v_i_837_);
lean_dec(v_i_837_);
v_res_844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(v_as_835_, v_sz_boxed_842_, v_i_boxed_843_, v_b_838_, v___y_839_, v___y_840_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec_ref(v_as_835_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(lean_object* v_as_848_, size_t v_sz_849_, size_t v_i_850_, lean_object* v_b_851_, lean_object* v___y_852_){
_start:
{
uint8_t v___x_854_; 
v___x_854_ = lean_usize_dec_lt(v_i_850_, v_sz_849_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; 
v___x_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_855_, 0, v_b_851_);
return v___x_855_;
}
else
{
uint8_t v___x_856_; lean_object* v_a_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
lean_dec_ref(v_b_851_);
v___x_856_ = 0;
v_a_857_ = lean_array_uget_borrowed(v_as_848_, v_i_850_);
lean_inc(v_a_857_);
v___x_858_ = l_Lean_Message_toString(v_a_857_, v___x_856_);
v___x_859_ = l_IO_eprintln___at___00main_spec__6(v___x_858_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v___x_860_; size_t v___x_861_; size_t v___x_862_; 
lean_dec_ref_known(v___x_859_, 1);
v___x_860_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_861_ = ((size_t)1ULL);
v___x_862_ = lean_usize_add(v_i_850_, v___x_861_);
v_i_850_ = v___x_862_;
v_b_851_ = v___x_860_;
goto _start;
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_876_; 
v_a_864_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_876_ == 0)
{
v___x_866_ = v___x_859_;
v_isShared_867_ = v_isSharedCheck_876_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_859_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_876_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v_ref_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_874_; 
v_ref_868_ = lean_ctor_get(v___y_852_, 5);
v___x_869_ = lean_io_error_to_string(v_a_864_);
v___x_870_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
v___x_871_ = l_Lean_MessageData_ofFormat(v___x_870_);
lean_inc(v_ref_868_);
v___x_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_872_, 0, v_ref_868_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_872_);
v___x_874_ = v___x_866_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___boxed(lean_object* v_as_877_, lean_object* v_sz_878_, lean_object* v_i_879_, lean_object* v_b_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
size_t v_sz_boxed_883_; size_t v_i_boxed_884_; lean_object* v_res_885_; 
v_sz_boxed_883_ = lean_unbox_usize(v_sz_878_);
lean_dec(v_sz_878_);
v_i_boxed_884_ = lean_unbox_usize(v_i_879_);
lean_dec(v_i_879_);
v_res_885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_877_, v_sz_boxed_883_, v_i_boxed_884_, v_b_880_, v___y_881_);
lean_dec_ref(v___y_881_);
lean_dec_ref(v_as_877_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(lean_object* v_as_886_, size_t v_sz_887_, size_t v_i_888_, lean_object* v_b_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
uint8_t v___x_893_; 
v___x_893_ = lean_usize_dec_lt(v_i_888_, v_sz_887_);
if (v___x_893_ == 0)
{
lean_object* v___x_894_; 
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v_b_889_);
return v___x_894_;
}
else
{
uint8_t v___x_895_; lean_object* v_a_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
lean_dec_ref(v_b_889_);
v___x_895_ = 0;
v_a_896_ = lean_array_uget_borrowed(v_as_886_, v_i_888_);
lean_inc(v_a_896_);
v___x_897_ = l_Lean_Message_toString(v_a_896_, v___x_895_);
v___x_898_ = l_IO_eprintln___at___00main_spec__6(v___x_897_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v___x_899_; size_t v___x_900_; size_t v___x_901_; lean_object* v___x_902_; 
lean_dec_ref_known(v___x_898_, 1);
v___x_899_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_900_ = ((size_t)1ULL);
v___x_901_ = lean_usize_add(v_i_888_, v___x_900_);
v___x_902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_886_, v_sz_887_, v___x_901_, v___x_899_, v___y_890_);
return v___x_902_;
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_915_; 
v_a_903_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_915_ == 0)
{
v___x_905_ = v___x_898_;
v_isShared_906_ = v_isSharedCheck_915_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_898_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_915_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v_ref_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_913_; 
v_ref_907_ = lean_ctor_get(v___y_890_, 5);
v___x_908_ = lean_io_error_to_string(v_a_903_);
v___x_909_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
v___x_910_ = l_Lean_MessageData_ofFormat(v___x_909_);
lean_inc(v_ref_907_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v_ref_907_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v___x_911_);
v___x_913_ = v___x_905_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38___boxed(lean_object* v_as_916_, lean_object* v_sz_917_, lean_object* v_i_918_, lean_object* v_b_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
size_t v_sz_boxed_923_; size_t v_i_boxed_924_; lean_object* v_res_925_; 
v_sz_boxed_923_ = lean_unbox_usize(v_sz_917_);
lean_dec(v_sz_917_);
v_i_boxed_924_ = lean_unbox_usize(v_i_918_);
lean_dec(v_i_918_);
v_res_925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(v_as_916_, v_sz_boxed_923_, v_i_boxed_924_, v_b_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec_ref(v_as_916_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(lean_object* v_init_926_, lean_object* v_n_927_, lean_object* v_b_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
if (lean_obj_tag(v_n_927_) == 0)
{
lean_object* v_cs_932_; lean_object* v___x_933_; lean_object* v___x_934_; size_t v_sz_935_; size_t v___x_936_; lean_object* v___x_937_; 
v_cs_932_ = lean_ctor_get(v_n_927_, 0);
v___x_933_ = lean_box(0);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
lean_ctor_set(v___x_934_, 1, v_b_928_);
v_sz_935_ = lean_array_size(v_cs_932_);
v___x_936_ = ((size_t)0ULL);
v___x_937_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_init_926_, v_cs_932_, v_sz_935_, v___x_936_, v___x_934_, v___y_929_, v___y_930_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_952_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_952_ == 0)
{
v___x_940_ = v___x_937_;
v_isShared_941_ = v_isSharedCheck_952_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_937_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_952_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v_fst_942_; 
v_fst_942_ = lean_ctor_get(v_a_938_, 0);
if (lean_obj_tag(v_fst_942_) == 0)
{
lean_object* v_snd_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
v_snd_943_ = lean_ctor_get(v_a_938_, 1);
lean_inc(v_snd_943_);
lean_dec(v_a_938_);
v___x_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_944_, 0, v_snd_943_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v___x_944_);
v___x_946_ = v___x_940_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
else
{
lean_object* v_val_948_; lean_object* v___x_950_; 
lean_inc_ref(v_fst_942_);
lean_dec(v_a_938_);
v_val_948_ = lean_ctor_get(v_fst_942_, 0);
lean_inc(v_val_948_);
lean_dec_ref_known(v_fst_942_, 1);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v_val_948_);
v___x_950_ = v___x_940_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_val_948_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
v_a_953_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_937_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_937_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
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
lean_object* v_vs_961_; lean_object* v___x_962_; lean_object* v___x_963_; size_t v_sz_964_; size_t v___x_965_; lean_object* v___x_966_; 
v_vs_961_ = lean_ctor_get(v_n_927_, 0);
v___x_962_ = lean_box(0);
v___x_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
lean_ctor_set(v___x_963_, 1, v_b_928_);
v_sz_964_ = lean_array_size(v_vs_961_);
v___x_965_ = ((size_t)0ULL);
v___x_966_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(v_vs_961_, v_sz_964_, v___x_965_, v___x_963_, v___y_929_, v___y_930_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_981_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_981_ == 0)
{
v___x_969_ = v___x_966_;
v_isShared_970_ = v_isSharedCheck_981_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_966_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_981_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v_fst_971_; 
v_fst_971_ = lean_ctor_get(v_a_967_, 0);
if (lean_obj_tag(v_fst_971_) == 0)
{
lean_object* v_snd_972_; lean_object* v___x_973_; lean_object* v___x_975_; 
v_snd_972_ = lean_ctor_get(v_a_967_, 1);
lean_inc(v_snd_972_);
lean_dec(v_a_967_);
v___x_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_973_, 0, v_snd_972_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v___x_973_);
v___x_975_ = v___x_969_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
else
{
lean_object* v_val_977_; lean_object* v___x_979_; 
lean_inc_ref(v_fst_971_);
lean_dec(v_a_967_);
v_val_977_ = lean_ctor_get(v_fst_971_, 0);
lean_inc(v_val_977_);
lean_dec_ref_known(v_fst_971_, 1);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v_val_977_);
v___x_979_ = v___x_969_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_val_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
v_a_982_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___x_966_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_966_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_982_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(lean_object* v_init_990_, lean_object* v_as_991_, size_t v_sz_992_, size_t v_i_993_, lean_object* v_b_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
uint8_t v___x_998_; 
v___x_998_ = lean_usize_dec_lt(v_i_993_, v_sz_992_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; 
v___x_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_999_, 0, v_b_994_);
return v___x_999_;
}
else
{
lean_object* v_snd_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1034_; 
v_snd_1000_ = lean_ctor_get(v_b_994_, 1);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_b_994_);
if (v_isSharedCheck_1034_ == 0)
{
lean_object* v_unused_1035_; 
v_unused_1035_ = lean_ctor_get(v_b_994_, 0);
lean_dec(v_unused_1035_);
v___x_1002_ = v_b_994_;
v_isShared_1003_ = v_isSharedCheck_1034_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_snd_1000_);
lean_dec(v_b_994_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1034_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v_a_1004_; lean_object* v___x_1005_; 
v_a_1004_ = lean_array_uget_borrowed(v_as_991_, v_i_993_);
lean_inc(v_snd_1000_);
v___x_1005_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_990_, v_a_1004_, v_snd_1000_, v___y_995_, v___y_996_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1025_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1025_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1025_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
if (lean_obj_tag(v_a_1006_) == 0)
{
lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1010_, 0, v_a_1006_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v___x_1010_);
v___x_1012_ = v___x_1002_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_snd_1000_);
v___x_1012_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1014_; 
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1012_);
v___x_1014_ = v___x_1008_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1012_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1018_; lean_object* v___x_1020_; 
lean_del_object(v___x_1008_);
lean_dec(v_snd_1000_);
v_a_1017_ = lean_ctor_get(v_a_1006_, 0);
lean_inc(v_a_1017_);
lean_dec_ref_known(v_a_1006_, 1);
v___x_1018_ = lean_box(0);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 1, v_a_1017_);
lean_ctor_set(v___x_1002_, 0, v___x_1018_);
v___x_1020_ = v___x_1002_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1018_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_a_1017_);
v___x_1020_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
size_t v___x_1021_; size_t v___x_1022_; 
v___x_1021_ = ((size_t)1ULL);
v___x_1022_ = lean_usize_add(v_i_993_, v___x_1021_);
v_i_993_ = v___x_1022_;
v_b_994_ = v___x_1020_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_del_object(v___x_1002_);
lean_dec(v_snd_1000_);
v_a_1026_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1005_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1005_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37___boxed(lean_object* v_init_1036_, lean_object* v_as_1037_, lean_object* v_sz_1038_, lean_object* v_i_1039_, lean_object* v_b_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
size_t v_sz_boxed_1044_; size_t v_i_boxed_1045_; lean_object* v_res_1046_; 
v_sz_boxed_1044_ = lean_unbox_usize(v_sz_1038_);
lean_dec(v_sz_1038_);
v_i_boxed_1045_ = lean_unbox_usize(v_i_1039_);
lean_dec(v_i_1039_);
v_res_1046_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_init_1036_, v_as_1037_, v_sz_boxed_1044_, v_i_boxed_1045_, v_b_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec_ref(v_as_1037_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26___boxed(lean_object* v_init_1047_, lean_object* v_n_1048_, lean_object* v_b_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1047_, v_n_1048_, v_b_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec_ref(v_n_1048_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12(lean_object* v_t_1054_, lean_object* v_init_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_root_1059_; lean_object* v_tail_1060_; lean_object* v___x_1061_; 
v_root_1059_ = lean_ctor_get(v_t_1054_, 0);
v_tail_1060_ = lean_ctor_get(v_t_1054_, 1);
v___x_1061_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1055_, v_root_1059_, v_init_1055_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1098_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1064_ = v___x_1061_;
v_isShared_1065_ = v_isSharedCheck_1098_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1061_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1098_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
if (lean_obj_tag(v_a_1062_) == 0)
{
lean_object* v_a_1066_; lean_object* v___x_1068_; 
v_a_1066_ = lean_ctor_get(v_a_1062_, 0);
lean_inc(v_a_1066_);
lean_dec_ref_known(v_a_1062_, 1);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v_a_1066_);
v___x_1068_ = v___x_1064_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1066_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; size_t v_sz_1073_; size_t v___x_1074_; lean_object* v___x_1075_; 
lean_del_object(v___x_1064_);
v_a_1070_ = lean_ctor_get(v_a_1062_, 0);
lean_inc(v_a_1070_);
lean_dec_ref_known(v_a_1062_, 1);
v___x_1071_ = lean_box(0);
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
lean_ctor_set(v___x_1072_, 1, v_a_1070_);
v_sz_1073_ = lean_array_size(v_tail_1060_);
v___x_1074_ = ((size_t)0ULL);
v___x_1075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(v_tail_1060_, v_sz_1073_, v___x_1074_, v___x_1072_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1089_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1078_ = v___x_1075_;
v_isShared_1079_ = v_isSharedCheck_1089_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1075_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1089_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v_fst_1080_; 
v_fst_1080_ = lean_ctor_get(v_a_1076_, 0);
if (lean_obj_tag(v_fst_1080_) == 0)
{
lean_object* v_snd_1081_; lean_object* v___x_1083_; 
v_snd_1081_ = lean_ctor_get(v_a_1076_, 1);
lean_inc(v_snd_1081_);
lean_dec(v_a_1076_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v_snd_1081_);
v___x_1083_ = v___x_1078_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_snd_1081_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
else
{
lean_object* v_val_1085_; lean_object* v___x_1087_; 
lean_inc_ref(v_fst_1080_);
lean_dec(v_a_1076_);
v_val_1085_ = lean_ctor_get(v_fst_1080_, 0);
lean_inc(v_val_1085_);
lean_dec_ref_known(v_fst_1080_, 1);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v_val_1085_);
v___x_1087_ = v___x_1078_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_val_1085_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
v_a_1090_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1075_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1075_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
v_a_1099_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1061_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1061_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12___boxed(lean_object* v_t_1107_, lean_object* v_init_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(v_t_1107_, v_init_1108_, v___y_1109_, v___y_1110_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec_ref(v_t_1107_);
return v_res_1112_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(uint8_t v___x_1120_, uint8_t v_suppressElabErrors_1121_, lean_object* v___x_1122_, lean_object* v_x_1123_){
_start:
{
if (lean_obj_tag(v_x_1123_) == 1)
{
lean_object* v_pre_1124_; 
v_pre_1124_ = lean_ctor_get(v_x_1123_, 0);
switch(lean_obj_tag(v_pre_1124_))
{
case 1:
{
lean_object* v_pre_1125_; 
v_pre_1125_ = lean_ctor_get(v_pre_1124_, 0);
switch(lean_obj_tag(v_pre_1125_))
{
case 0:
{
lean_object* v_str_1126_; lean_object* v_str_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; 
v_str_1126_ = lean_ctor_get(v_x_1123_, 1);
v_str_1127_ = lean_ctor_get(v_pre_1124_, 1);
v___x_1128_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0));
v___x_1129_ = lean_string_dec_eq(v_str_1127_, v___x_1128_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1130_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1));
v___x_1131_ = lean_string_dec_eq(v_str_1127_, v___x_1130_);
if (v___x_1131_ == 0)
{
return v___x_1120_;
}
else
{
lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1132_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2));
v___x_1133_ = lean_string_dec_eq(v_str_1126_, v___x_1132_);
if (v___x_1133_ == 0)
{
return v___x_1120_;
}
else
{
return v_suppressElabErrors_1121_;
}
}
}
else
{
lean_object* v___x_1134_; uint8_t v___x_1135_; 
v___x_1134_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3));
v___x_1135_ = lean_string_dec_eq(v_str_1126_, v___x_1134_);
if (v___x_1135_ == 0)
{
return v___x_1120_;
}
else
{
return v_suppressElabErrors_1121_;
}
}
}
case 1:
{
lean_object* v_pre_1136_; 
v_pre_1136_ = lean_ctor_get(v_pre_1125_, 0);
if (lean_obj_tag(v_pre_1136_) == 0)
{
lean_object* v_str_1137_; lean_object* v_str_1138_; lean_object* v_str_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
v_str_1137_ = lean_ctor_get(v_x_1123_, 1);
v_str_1138_ = lean_ctor_get(v_pre_1124_, 1);
v_str_1139_ = lean_ctor_get(v_pre_1125_, 1);
v___x_1140_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4));
v___x_1141_ = lean_string_dec_eq(v_str_1139_, v___x_1140_);
if (v___x_1141_ == 0)
{
return v___x_1120_;
}
else
{
lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5));
v___x_1143_ = lean_string_dec_eq(v_str_1138_, v___x_1142_);
if (v___x_1143_ == 0)
{
return v___x_1120_;
}
else
{
lean_object* v___x_1144_; uint8_t v___x_1145_; 
v___x_1144_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6));
v___x_1145_ = lean_string_dec_eq(v_str_1137_, v___x_1144_);
if (v___x_1145_ == 0)
{
return v___x_1120_;
}
else
{
return v_suppressElabErrors_1121_;
}
}
}
}
else
{
return v___x_1120_;
}
}
default: 
{
return v___x_1120_;
}
}
}
case 0:
{
lean_object* v_str_1146_; uint8_t v___x_1147_; 
v_str_1146_ = lean_ctor_get(v_x_1123_, 1);
v___x_1147_ = lean_string_dec_eq(v_str_1146_, v___x_1122_);
if (v___x_1147_ == 0)
{
return v___x_1120_;
}
else
{
return v_suppressElabErrors_1121_;
}
}
default: 
{
return v___x_1120_;
}
}
}
else
{
return v___x_1120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed(lean_object* v___x_1148_, lean_object* v_suppressElabErrors_1149_, lean_object* v___x_1150_, lean_object* v_x_1151_){
_start:
{
uint8_t v___x_37203__boxed_1152_; uint8_t v_suppressElabErrors_boxed_1153_; uint8_t v_res_1154_; lean_object* v_r_1155_; 
v___x_37203__boxed_1152_ = lean_unbox(v___x_1148_);
v_suppressElabErrors_boxed_1153_ = lean_unbox(v_suppressElabErrors_1149_);
v_res_1154_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(v___x_37203__boxed_1152_, v_suppressElabErrors_boxed_1153_, v___x_1150_, v_x_1151_);
lean_dec(v_x_1151_);
lean_dec_ref(v___x_1150_);
v_r_1155_ = lean_box(v_res_1154_);
return v_r_1155_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0(void){
_start:
{
lean_object* v___x_1156_; double v___x_1157_; 
v___x_1156_ = lean_unsigned_to_nat(0u);
v___x_1157_ = lean_float_of_nat(v___x_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(uint8_t v___x_1159_, lean_object* v_as_1160_, size_t v_sz_1161_, size_t v_i_1162_, lean_object* v_b_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_a_1168_; uint8_t v___x_1172_; 
v___x_1172_ = lean_usize_dec_lt(v_i_1162_, v_sz_1161_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; 
v___x_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1173_, 0, v_b_1163_);
return v___x_1173_;
}
else
{
lean_object* v_a_1174_; lean_object* v_fst_1175_; lean_object* v_snd_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1252_; 
v_a_1174_ = lean_array_uget(v_as_1160_, v_i_1162_);
v_fst_1175_ = lean_ctor_get(v_a_1174_, 0);
v_snd_1176_ = lean_ctor_get(v_a_1174_, 1);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_a_1174_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1178_ = v_a_1174_;
v_isShared_1179_ = v_isSharedCheck_1252_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_snd_1176_);
lean_inc(v_fst_1175_);
lean_dec(v_a_1174_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1252_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v_fst_1180_; lean_object* v_snd_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1251_; 
v_fst_1180_ = lean_ctor_get(v_fst_1175_, 0);
v_snd_1181_ = lean_ctor_get(v_fst_1175_, 1);
v_isSharedCheck_1251_ = !lean_is_exclusive(v_fst_1175_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1183_ = v_fst_1175_;
v_isShared_1184_ = v_isSharedCheck_1251_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_snd_1181_);
lean_inc(v_fst_1180_);
lean_dec(v_fst_1175_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1251_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; double v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v_fileName_1190_; lean_object* v_fileMap_1191_; uint8_t v_suppressElabErrors_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1185_ = lean_box(0);
v___x_1186_ = lean_box(0);
v___x_1187_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0);
v___x_1188_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1));
v___x_1189_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1189_, 0, v___x_1185_);
lean_ctor_set(v___x_1189_, 1, v___x_1186_);
lean_ctor_set(v___x_1189_, 2, v___x_1188_);
lean_ctor_set_float(v___x_1189_, sizeof(void*)*3, v___x_1187_);
lean_ctor_set_float(v___x_1189_, sizeof(void*)*3 + 8, v___x_1187_);
lean_ctor_set_uint8(v___x_1189_, sizeof(void*)*3 + 16, v___x_1172_);
v_fileName_1190_ = lean_ctor_get(v___y_1164_, 0);
v_fileMap_1191_ = lean_ctor_get(v___y_1164_, 1);
v_suppressElabErrors_1192_ = lean_ctor_get_uint8(v___y_1164_, sizeof(void*)*14 + 1);
v___x_1193_ = lean_box(0);
v___x_1194_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_1195_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_1196_ = l_Lean_MessageData_nil;
v___x_1197_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1189_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
lean_ctor_set(v___x_1197_, 2, v_snd_1176_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set_tag(v___x_1183_, 8);
lean_ctor_set(v___x_1183_, 1, v___x_1197_);
lean_ctor_set(v___x_1183_, 0, v___x_1195_);
v___x_1199_ = v___x_1183_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
uint8_t v___x_1200_; lean_object* v___x_1201_; lean_object* v___y_1203_; lean_object* v___y_1204_; 
v___x_1200_ = 0;
lean_inc_ref(v_fileMap_1191_);
lean_inc_ref(v_fileName_1190_);
v___x_1201_ = l_Lean_Elab_mkMessageCore(v_fileName_1190_, v_fileMap_1191_, v___x_1199_, v___x_1200_, v_fst_1180_, v_snd_1181_);
lean_dec(v_snd_1181_);
lean_dec(v_fst_1180_);
if (v_suppressElabErrors_1192_ == 0)
{
v___y_1203_ = v___y_1164_;
v___y_1204_ = v___y_1165_;
goto v___jp_1202_;
}
else
{
lean_object* v_data_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___f_1248_; uint8_t v___x_1249_; 
v_data_1245_ = lean_ctor_get(v___x_1201_, 4);
lean_inc(v_data_1245_);
v___x_1246_ = lean_box(v___x_1159_);
v___x_1247_ = lean_box(v_suppressElabErrors_1192_);
v___f_1248_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1248_, 0, v___x_1246_);
lean_closure_set(v___f_1248_, 1, v___x_1247_);
lean_closure_set(v___f_1248_, 2, v___x_1194_);
v___x_1249_ = l_Lean_MessageData_hasTag(v___f_1248_, v_data_1245_);
if (v___x_1249_ == 0)
{
lean_dec_ref(v___x_1201_);
lean_del_object(v___x_1178_);
v_a_1168_ = v___x_1193_;
goto v___jp_1167_;
}
else
{
v___y_1203_ = v___y_1164_;
v___y_1204_ = v___y_1165_;
goto v___jp_1202_;
}
}
v___jp_1202_:
{
lean_object* v___x_1205_; lean_object* v_fileName_1206_; lean_object* v_pos_1207_; lean_object* v_endPos_1208_; uint8_t v_keepFullRange_1209_; uint8_t v_severity_1210_; uint8_t v_isSilent_1211_; lean_object* v_caption_1212_; lean_object* v_data_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1244_; 
v___x_1205_ = lean_st_ref_take(v___y_1204_);
v_fileName_1206_ = lean_ctor_get(v___x_1201_, 0);
v_pos_1207_ = lean_ctor_get(v___x_1201_, 1);
v_endPos_1208_ = lean_ctor_get(v___x_1201_, 2);
v_keepFullRange_1209_ = lean_ctor_get_uint8(v___x_1201_, sizeof(void*)*5);
v_severity_1210_ = lean_ctor_get_uint8(v___x_1201_, sizeof(void*)*5 + 1);
v_isSilent_1211_ = lean_ctor_get_uint8(v___x_1201_, sizeof(void*)*5 + 2);
v_caption_1212_ = lean_ctor_get(v___x_1201_, 3);
v_data_1213_ = lean_ctor_get(v___x_1201_, 4);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1215_ = v___x_1201_;
v_isShared_1216_ = v_isSharedCheck_1244_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_data_1213_);
lean_inc(v_caption_1212_);
lean_inc(v_endPos_1208_);
lean_inc(v_pos_1207_);
lean_inc(v_fileName_1206_);
lean_dec(v___x_1201_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1244_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v_currNamespace_1217_; lean_object* v_openDecls_1218_; lean_object* v_env_1219_; lean_object* v_nextMacroScope_1220_; lean_object* v_ngen_1221_; lean_object* v_auxDeclNGen_1222_; lean_object* v_traceState_1223_; lean_object* v_cache_1224_; lean_object* v_messages_1225_; lean_object* v_infoState_1226_; lean_object* v_snapshotTasks_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1243_; 
v_currNamespace_1217_ = lean_ctor_get(v___y_1203_, 6);
v_openDecls_1218_ = lean_ctor_get(v___y_1203_, 7);
v_env_1219_ = lean_ctor_get(v___x_1205_, 0);
v_nextMacroScope_1220_ = lean_ctor_get(v___x_1205_, 1);
v_ngen_1221_ = lean_ctor_get(v___x_1205_, 2);
v_auxDeclNGen_1222_ = lean_ctor_get(v___x_1205_, 3);
v_traceState_1223_ = lean_ctor_get(v___x_1205_, 4);
v_cache_1224_ = lean_ctor_get(v___x_1205_, 5);
v_messages_1225_ = lean_ctor_get(v___x_1205_, 6);
v_infoState_1226_ = lean_ctor_get(v___x_1205_, 7);
v_snapshotTasks_1227_ = lean_ctor_get(v___x_1205_, 8);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1229_ = v___x_1205_;
v_isShared_1230_ = v_isSharedCheck_1243_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_snapshotTasks_1227_);
lean_inc(v_infoState_1226_);
lean_inc(v_messages_1225_);
lean_inc(v_cache_1224_);
lean_inc(v_traceState_1223_);
lean_inc(v_auxDeclNGen_1222_);
lean_inc(v_ngen_1221_);
lean_inc(v_nextMacroScope_1220_);
lean_inc(v_env_1219_);
lean_dec(v___x_1205_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1243_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
lean_inc(v_openDecls_1218_);
lean_inc(v_currNamespace_1217_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v_openDecls_1218_);
lean_ctor_set(v___x_1178_, 0, v_currNamespace_1217_);
v___x_1232_ = v___x_1178_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_currNamespace_1217_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_openDecls_1218_);
v___x_1232_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1233_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
lean_ctor_set(v___x_1233_, 1, v_data_1213_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 4, v___x_1233_);
v___x_1235_ = v___x_1215_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_fileName_1206_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_pos_1207_);
lean_ctor_set(v_reuseFailAlloc_1241_, 2, v_endPos_1208_);
lean_ctor_set(v_reuseFailAlloc_1241_, 3, v_caption_1212_);
lean_ctor_set(v_reuseFailAlloc_1241_, 4, v___x_1233_);
lean_ctor_set_uint8(v_reuseFailAlloc_1241_, sizeof(void*)*5, v_keepFullRange_1209_);
lean_ctor_set_uint8(v_reuseFailAlloc_1241_, sizeof(void*)*5 + 1, v_severity_1210_);
lean_ctor_set_uint8(v_reuseFailAlloc_1241_, sizeof(void*)*5 + 2, v_isSilent_1211_);
v___x_1235_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v___x_1236_; lean_object* v___x_1238_; 
v___x_1236_ = l_Lean_MessageLog_add(v___x_1235_, v_messages_1225_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 6, v___x_1236_);
v___x_1238_ = v___x_1229_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_env_1219_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_nextMacroScope_1220_);
lean_ctor_set(v_reuseFailAlloc_1240_, 2, v_ngen_1221_);
lean_ctor_set(v_reuseFailAlloc_1240_, 3, v_auxDeclNGen_1222_);
lean_ctor_set(v_reuseFailAlloc_1240_, 4, v_traceState_1223_);
lean_ctor_set(v_reuseFailAlloc_1240_, 5, v_cache_1224_);
lean_ctor_set(v_reuseFailAlloc_1240_, 6, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1240_, 7, v_infoState_1226_);
lean_ctor_set(v_reuseFailAlloc_1240_, 8, v_snapshotTasks_1227_);
v___x_1238_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
lean_object* v___x_1239_; 
v___x_1239_ = lean_st_ref_set(v___y_1204_, v___x_1238_);
v_a_1168_ = v___x_1193_;
goto v___jp_1167_;
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
v___jp_1167_:
{
size_t v___x_1169_; size_t v___x_1170_; 
v___x_1169_ = ((size_t)1ULL);
v___x_1170_ = lean_usize_add(v_i_1162_, v___x_1169_);
v_i_1162_ = v___x_1170_;
v_b_1163_ = v_a_1168_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___boxed(lean_object* v___x_1253_, lean_object* v_as_1254_, lean_object* v_sz_1255_, lean_object* v_i_1256_, lean_object* v_b_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
uint8_t v___x_37276__boxed_1261_; size_t v_sz_boxed_1262_; size_t v_i_boxed_1263_; lean_object* v_res_1264_; 
v___x_37276__boxed_1261_ = lean_unbox(v___x_1253_);
v_sz_boxed_1262_ = lean_unbox_usize(v_sz_1255_);
lean_dec(v_sz_1255_);
v_i_boxed_1263_ = lean_unbox_usize(v_i_1256_);
lean_dec(v_i_1256_);
v_res_1264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_37276__boxed_1261_, v_as_1254_, v_sz_boxed_1262_, v_i_boxed_1263_, v_b_1257_, v___y_1258_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec_ref(v_as_1254_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(lean_object* v_opts_1265_, lean_object* v_opt_1266_){
_start:
{
lean_object* v_name_1267_; lean_object* v_map_1268_; lean_object* v___x_1269_; 
v_name_1267_ = lean_ctor_get(v_opt_1266_, 0);
v_map_1268_ = lean_ctor_get(v_opts_1265_, 0);
v___x_1269_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1268_, v_name_1267_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v___x_1270_; 
v___x_1270_ = lean_box(0);
return v___x_1270_;
}
else
{
lean_object* v_val_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1280_; 
v_val_1271_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1273_ = v___x_1269_;
v_isShared_1274_ = v_isSharedCheck_1280_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_val_1271_);
lean_dec(v___x_1269_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1280_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
if (lean_obj_tag(v_val_1271_) == 0)
{
lean_object* v_v_1275_; lean_object* v___x_1277_; 
v_v_1275_ = lean_ctor_get(v_val_1271_, 0);
lean_inc_ref(v_v_1275_);
lean_dec_ref_known(v_val_1271_, 1);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v_v_1275_);
v___x_1277_ = v___x_1273_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_v_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
else
{
lean_object* v___x_1279_; 
lean_del_object(v___x_1273_);
lean_dec(v_val_1271_);
v___x_1279_ = lean_box(0);
return v___x_1279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15___boxed(lean_object* v_opts_1281_, lean_object* v_opt_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(v_opts_1281_, v_opt_1282_);
lean_dec_ref(v_opt_1282_);
lean_dec_ref(v_opts_1281_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(lean_object* v_a_1284_, lean_object* v_fallback_1285_, lean_object* v_x_1286_){
_start:
{
if (lean_obj_tag(v_x_1286_) == 0)
{
lean_inc(v_fallback_1285_);
return v_fallback_1285_;
}
else
{
lean_object* v_key_1287_; lean_object* v_value_1288_; lean_object* v_tail_1289_; uint8_t v___y_1291_; lean_object* v_fst_1293_; lean_object* v_snd_1294_; lean_object* v_fst_1295_; lean_object* v_snd_1296_; uint8_t v___x_1297_; 
v_key_1287_ = lean_ctor_get(v_x_1286_, 0);
v_value_1288_ = lean_ctor_get(v_x_1286_, 1);
v_tail_1289_ = lean_ctor_get(v_x_1286_, 2);
v_fst_1293_ = lean_ctor_get(v_key_1287_, 0);
v_snd_1294_ = lean_ctor_get(v_key_1287_, 1);
v_fst_1295_ = lean_ctor_get(v_a_1284_, 0);
v_snd_1296_ = lean_ctor_get(v_a_1284_, 1);
v___x_1297_ = lean_nat_dec_eq(v_fst_1293_, v_fst_1295_);
if (v___x_1297_ == 0)
{
v___y_1291_ = v___x_1297_;
goto v___jp_1290_;
}
else
{
uint8_t v___x_1298_; 
v___x_1298_ = lean_nat_dec_eq(v_snd_1294_, v_snd_1296_);
v___y_1291_ = v___x_1298_;
goto v___jp_1290_;
}
v___jp_1290_:
{
if (v___y_1291_ == 0)
{
v_x_1286_ = v_tail_1289_;
goto _start;
}
else
{
lean_inc(v_value_1288_);
return v_value_1288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg___boxed(lean_object* v_a_1299_, lean_object* v_fallback_1300_, lean_object* v_x_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_1299_, v_fallback_1300_, v_x_1301_);
lean_dec(v_x_1301_);
lean_dec(v_fallback_1300_);
lean_dec_ref(v_a_1299_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(lean_object* v_m_1303_, lean_object* v_a_1304_, lean_object* v_fallback_1305_){
_start:
{
lean_object* v_buckets_1306_; lean_object* v_fst_1307_; lean_object* v_snd_1308_; lean_object* v___x_1309_; uint64_t v___x_1310_; uint64_t v___x_1311_; uint64_t v___x_1312_; uint64_t v___x_1313_; uint64_t v___x_1314_; uint64_t v_fold_1315_; uint64_t v___x_1316_; uint64_t v___x_1317_; uint64_t v___x_1318_; size_t v___x_1319_; size_t v___x_1320_; size_t v___x_1321_; size_t v___x_1322_; size_t v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_buckets_1306_ = lean_ctor_get(v_m_1303_, 1);
v_fst_1307_ = lean_ctor_get(v_a_1304_, 0);
v_snd_1308_ = lean_ctor_get(v_a_1304_, 1);
v___x_1309_ = lean_array_get_size(v_buckets_1306_);
v___x_1310_ = l_String_instHashableRaw_hash(v_fst_1307_);
v___x_1311_ = l_String_instHashableRaw_hash(v_snd_1308_);
v___x_1312_ = lean_uint64_mix_hash(v___x_1310_, v___x_1311_);
v___x_1313_ = 32ULL;
v___x_1314_ = lean_uint64_shift_right(v___x_1312_, v___x_1313_);
v_fold_1315_ = lean_uint64_xor(v___x_1312_, v___x_1314_);
v___x_1316_ = 16ULL;
v___x_1317_ = lean_uint64_shift_right(v_fold_1315_, v___x_1316_);
v___x_1318_ = lean_uint64_xor(v_fold_1315_, v___x_1317_);
v___x_1319_ = lean_uint64_to_usize(v___x_1318_);
v___x_1320_ = lean_usize_of_nat(v___x_1309_);
v___x_1321_ = ((size_t)1ULL);
v___x_1322_ = lean_usize_sub(v___x_1320_, v___x_1321_);
v___x_1323_ = lean_usize_land(v___x_1319_, v___x_1322_);
v___x_1324_ = lean_array_uget_borrowed(v_buckets_1306_, v___x_1323_);
v___x_1325_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_1304_, v_fallback_1305_, v___x_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg___boxed(lean_object* v_m_1326_, lean_object* v_a_1327_, lean_object* v_fallback_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_1326_, v_a_1327_, v_fallback_1328_);
lean_dec(v_fallback_1328_);
lean_dec_ref(v_a_1327_);
lean_dec_ref(v_m_1326_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(lean_object* v_x_1330_, lean_object* v_x_1331_){
_start:
{
if (lean_obj_tag(v_x_1331_) == 0)
{
return v_x_1330_;
}
else
{
lean_object* v_key_1332_; lean_object* v_value_1333_; lean_object* v_tail_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1361_; 
v_key_1332_ = lean_ctor_get(v_x_1331_, 0);
v_value_1333_ = lean_ctor_get(v_x_1331_, 1);
v_tail_1334_ = lean_ctor_get(v_x_1331_, 2);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_x_1331_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1336_ = v_x_1331_;
v_isShared_1337_ = v_isSharedCheck_1361_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_tail_1334_);
lean_inc(v_value_1333_);
lean_inc(v_key_1332_);
lean_dec(v_x_1331_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1361_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v_fst_1338_; lean_object* v_snd_1339_; lean_object* v___x_1340_; uint64_t v___x_1341_; uint64_t v___x_1342_; uint64_t v___x_1343_; uint64_t v___x_1344_; uint64_t v___x_1345_; uint64_t v_fold_1346_; uint64_t v___x_1347_; uint64_t v___x_1348_; uint64_t v___x_1349_; size_t v___x_1350_; size_t v___x_1351_; size_t v___x_1352_; size_t v___x_1353_; size_t v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1357_; 
v_fst_1338_ = lean_ctor_get(v_key_1332_, 0);
v_snd_1339_ = lean_ctor_get(v_key_1332_, 1);
v___x_1340_ = lean_array_get_size(v_x_1330_);
v___x_1341_ = l_String_instHashableRaw_hash(v_fst_1338_);
v___x_1342_ = l_String_instHashableRaw_hash(v_snd_1339_);
v___x_1343_ = lean_uint64_mix_hash(v___x_1341_, v___x_1342_);
v___x_1344_ = 32ULL;
v___x_1345_ = lean_uint64_shift_right(v___x_1343_, v___x_1344_);
v_fold_1346_ = lean_uint64_xor(v___x_1343_, v___x_1345_);
v___x_1347_ = 16ULL;
v___x_1348_ = lean_uint64_shift_right(v_fold_1346_, v___x_1347_);
v___x_1349_ = lean_uint64_xor(v_fold_1346_, v___x_1348_);
v___x_1350_ = lean_uint64_to_usize(v___x_1349_);
v___x_1351_ = lean_usize_of_nat(v___x_1340_);
v___x_1352_ = ((size_t)1ULL);
v___x_1353_ = lean_usize_sub(v___x_1351_, v___x_1352_);
v___x_1354_ = lean_usize_land(v___x_1350_, v___x_1353_);
v___x_1355_ = lean_array_uget_borrowed(v_x_1330_, v___x_1354_);
lean_inc(v___x_1355_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 2, v___x_1355_);
v___x_1357_ = v___x_1336_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_key_1332_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_value_1333_);
lean_ctor_set(v_reuseFailAlloc_1360_, 2, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1358_; 
v___x_1358_ = lean_array_uset(v_x_1330_, v___x_1354_, v___x_1357_);
v_x_1330_ = v___x_1358_;
v_x_1331_ = v_tail_1334_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(lean_object* v_i_1362_, lean_object* v_source_1363_, lean_object* v_target_1364_){
_start:
{
lean_object* v___x_1365_; uint8_t v___x_1366_; 
v___x_1365_ = lean_array_get_size(v_source_1363_);
v___x_1366_ = lean_nat_dec_lt(v_i_1362_, v___x_1365_);
if (v___x_1366_ == 0)
{
lean_dec_ref(v_source_1363_);
lean_dec(v_i_1362_);
return v_target_1364_;
}
else
{
lean_object* v_es_1367_; lean_object* v___x_1368_; lean_object* v_source_1369_; lean_object* v_target_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v_es_1367_ = lean_array_fget(v_source_1363_, v_i_1362_);
v___x_1368_ = lean_box(0);
v_source_1369_ = lean_array_fset(v_source_1363_, v_i_1362_, v___x_1368_);
v_target_1370_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_target_1364_, v_es_1367_);
v___x_1371_ = lean_unsigned_to_nat(1u);
v___x_1372_ = lean_nat_add(v_i_1362_, v___x_1371_);
lean_dec(v_i_1362_);
v_i_1362_ = v___x_1372_;
v_source_1363_ = v_source_1369_;
v_target_1364_ = v_target_1370_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(lean_object* v_data_1374_){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v_nbuckets_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1375_ = lean_array_get_size(v_data_1374_);
v___x_1376_ = lean_unsigned_to_nat(2u);
v_nbuckets_1377_ = lean_nat_mul(v___x_1375_, v___x_1376_);
v___x_1378_ = lean_unsigned_to_nat(0u);
v___x_1379_ = lean_box(0);
v___x_1380_ = lean_mk_array(v_nbuckets_1377_, v___x_1379_);
v___x_1381_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v___x_1378_, v_data_1374_, v___x_1380_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(lean_object* v_a_1382_, lean_object* v_b_1383_, lean_object* v_x_1384_){
_start:
{
if (lean_obj_tag(v_x_1384_) == 0)
{
lean_dec(v_b_1383_);
lean_dec_ref(v_a_1382_);
return v_x_1384_;
}
else
{
lean_object* v_key_1385_; lean_object* v_value_1386_; lean_object* v_tail_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1406_; 
v_key_1385_ = lean_ctor_get(v_x_1384_, 0);
v_value_1386_ = lean_ctor_get(v_x_1384_, 1);
v_tail_1387_ = lean_ctor_get(v_x_1384_, 2);
v_isSharedCheck_1406_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1389_ = v_x_1384_;
v_isShared_1390_ = v_isSharedCheck_1406_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_tail_1387_);
lean_inc(v_value_1386_);
lean_inc(v_key_1385_);
lean_dec(v_x_1384_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1406_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
uint8_t v___y_1392_; lean_object* v_fst_1400_; lean_object* v_snd_1401_; lean_object* v_fst_1402_; lean_object* v_snd_1403_; uint8_t v___x_1404_; 
v_fst_1400_ = lean_ctor_get(v_key_1385_, 0);
v_snd_1401_ = lean_ctor_get(v_key_1385_, 1);
v_fst_1402_ = lean_ctor_get(v_a_1382_, 0);
v_snd_1403_ = lean_ctor_get(v_a_1382_, 1);
v___x_1404_ = lean_nat_dec_eq(v_fst_1400_, v_fst_1402_);
if (v___x_1404_ == 0)
{
v___y_1392_ = v___x_1404_;
goto v___jp_1391_;
}
else
{
uint8_t v___x_1405_; 
v___x_1405_ = lean_nat_dec_eq(v_snd_1401_, v_snd_1403_);
v___y_1392_ = v___x_1405_;
goto v___jp_1391_;
}
v___jp_1391_:
{
if (v___y_1392_ == 0)
{
lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1393_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_1382_, v_b_1383_, v_tail_1387_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 2, v___x_1393_);
v___x_1395_ = v___x_1389_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_key_1385_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_value_1386_);
lean_ctor_set(v_reuseFailAlloc_1396_, 2, v___x_1393_);
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
lean_object* v___x_1398_; 
lean_dec(v_value_1386_);
lean_dec(v_key_1385_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 1, v_b_1383_);
lean_ctor_set(v___x_1389_, 0, v_a_1382_);
v___x_1398_ = v___x_1389_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1382_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_b_1383_);
lean_ctor_set(v_reuseFailAlloc_1399_, 2, v_tail_1387_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(lean_object* v_a_1407_, lean_object* v_x_1408_){
_start:
{
if (lean_obj_tag(v_x_1408_) == 0)
{
uint8_t v___x_1409_; 
v___x_1409_ = 0;
return v___x_1409_;
}
else
{
lean_object* v_key_1410_; lean_object* v_tail_1411_; uint8_t v___y_1413_; lean_object* v_fst_1415_; lean_object* v_snd_1416_; lean_object* v_fst_1417_; lean_object* v_snd_1418_; uint8_t v___x_1419_; 
v_key_1410_ = lean_ctor_get(v_x_1408_, 0);
v_tail_1411_ = lean_ctor_get(v_x_1408_, 2);
v_fst_1415_ = lean_ctor_get(v_key_1410_, 0);
v_snd_1416_ = lean_ctor_get(v_key_1410_, 1);
v_fst_1417_ = lean_ctor_get(v_a_1407_, 0);
v_snd_1418_ = lean_ctor_get(v_a_1407_, 1);
v___x_1419_ = lean_nat_dec_eq(v_fst_1415_, v_fst_1417_);
if (v___x_1419_ == 0)
{
v___y_1413_ = v___x_1419_;
goto v___jp_1412_;
}
else
{
uint8_t v___x_1420_; 
v___x_1420_ = lean_nat_dec_eq(v_snd_1416_, v_snd_1418_);
v___y_1413_ = v___x_1420_;
goto v___jp_1412_;
}
v___jp_1412_:
{
if (v___y_1413_ == 0)
{
v_x_1408_ = v_tail_1411_;
goto _start;
}
else
{
return v___y_1413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg___boxed(lean_object* v_a_1421_, lean_object* v_x_1422_){
_start:
{
uint8_t v_res_1423_; lean_object* v_r_1424_; 
v_res_1423_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_1421_, v_x_1422_);
lean_dec(v_x_1422_);
lean_dec_ref(v_a_1421_);
v_r_1424_ = lean_box(v_res_1423_);
return v_r_1424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(lean_object* v_m_1425_, lean_object* v_a_1426_, lean_object* v_b_1427_){
_start:
{
lean_object* v_size_1428_; lean_object* v_buckets_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1476_; 
v_size_1428_ = lean_ctor_get(v_m_1425_, 0);
v_buckets_1429_ = lean_ctor_get(v_m_1425_, 1);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_m_1425_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1431_ = v_m_1425_;
v_isShared_1432_ = v_isSharedCheck_1476_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_buckets_1429_);
lean_inc(v_size_1428_);
lean_dec(v_m_1425_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1476_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v_fst_1433_; lean_object* v_snd_1434_; lean_object* v___x_1435_; uint64_t v___x_1436_; uint64_t v___x_1437_; uint64_t v___x_1438_; uint64_t v___x_1439_; uint64_t v___x_1440_; uint64_t v_fold_1441_; uint64_t v___x_1442_; uint64_t v___x_1443_; uint64_t v___x_1444_; size_t v___x_1445_; size_t v___x_1446_; size_t v___x_1447_; size_t v___x_1448_; size_t v___x_1449_; lean_object* v_bkt_1450_; uint8_t v___x_1451_; 
v_fst_1433_ = lean_ctor_get(v_a_1426_, 0);
v_snd_1434_ = lean_ctor_get(v_a_1426_, 1);
v___x_1435_ = lean_array_get_size(v_buckets_1429_);
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
v_bkt_1450_ = lean_array_uget_borrowed(v_buckets_1429_, v___x_1449_);
v___x_1451_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_1426_, v_bkt_1450_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; lean_object* v_size_x27_1453_; lean_object* v___x_1454_; lean_object* v_buckets_x27_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; 
v___x_1452_ = lean_unsigned_to_nat(1u);
v_size_x27_1453_ = lean_nat_add(v_size_1428_, v___x_1452_);
lean_dec(v_size_1428_);
lean_inc(v_bkt_1450_);
v___x_1454_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1454_, 0, v_a_1426_);
lean_ctor_set(v___x_1454_, 1, v_b_1427_);
lean_ctor_set(v___x_1454_, 2, v_bkt_1450_);
v_buckets_x27_1455_ = lean_array_uset(v_buckets_1429_, v___x_1449_, v___x_1454_);
v___x_1456_ = lean_unsigned_to_nat(4u);
v___x_1457_ = lean_nat_mul(v_size_x27_1453_, v___x_1456_);
v___x_1458_ = lean_unsigned_to_nat(3u);
v___x_1459_ = lean_nat_div(v___x_1457_, v___x_1458_);
lean_dec(v___x_1457_);
v___x_1460_ = lean_array_get_size(v_buckets_x27_1455_);
v___x_1461_ = lean_nat_dec_le(v___x_1459_, v___x_1460_);
lean_dec(v___x_1459_);
if (v___x_1461_ == 0)
{
lean_object* v_val_1462_; lean_object* v___x_1464_; 
v_val_1462_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_buckets_x27_1455_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 1, v_val_1462_);
lean_ctor_set(v___x_1431_, 0, v_size_x27_1453_);
v___x_1464_ = v___x_1431_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_size_x27_1453_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_val_1462_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
else
{
lean_object* v___x_1467_; 
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 1, v_buckets_x27_1455_);
lean_ctor_set(v___x_1431_, 0, v_size_x27_1453_);
v___x_1467_ = v___x_1431_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_size_x27_1453_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_buckets_x27_1455_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
else
{
lean_object* v___x_1469_; lean_object* v_buckets_x27_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1474_; 
lean_inc(v_bkt_1450_);
v___x_1469_ = lean_box(0);
v_buckets_x27_1470_ = lean_array_uset(v_buckets_1429_, v___x_1449_, v___x_1469_);
v___x_1471_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_1426_, v_b_1427_, v_bkt_1450_);
v___x_1472_ = lean_array_uset(v_buckets_x27_1470_, v___x_1449_, v___x_1471_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 1, v___x_1472_);
v___x_1474_ = v___x_1431_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_size_1428_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v___x_1472_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(uint8_t v___x_1479_, lean_object* v_as_1480_, size_t v_sz_1481_, size_t v_i_1482_, lean_object* v_b_1483_, lean_object* v___y_1484_){
_start:
{
uint8_t v___x_1486_; 
v___x_1486_ = lean_usize_dec_lt(v_i_1482_, v_sz_1481_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; 
v___x_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1487_, 0, v_b_1483_);
return v___x_1487_;
}
else
{
lean_object* v_snd_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1525_; 
v_snd_1488_ = lean_ctor_get(v_b_1483_, 1);
v_isSharedCheck_1525_ = !lean_is_exclusive(v_b_1483_);
if (v_isSharedCheck_1525_ == 0)
{
lean_object* v_unused_1526_; 
v_unused_1526_ = lean_ctor_get(v_b_1483_, 0);
lean_dec(v_unused_1526_);
v___x_1490_ = v_b_1483_;
v_isShared_1491_ = v_isSharedCheck_1525_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_snd_1488_);
lean_dec(v_b_1483_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1525_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v_ref_1492_; lean_object* v_a_1493_; lean_object* v_ref_1494_; lean_object* v_msg_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1524_; 
v_ref_1492_ = lean_ctor_get(v___y_1484_, 5);
v_a_1493_ = lean_array_uget(v_as_1480_, v_i_1482_);
v_ref_1494_ = lean_ctor_get(v_a_1493_, 0);
v_msg_1495_ = lean_ctor_get(v_a_1493_, 1);
v_isSharedCheck_1524_ = !lean_is_exclusive(v_a_1493_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1497_ = v_a_1493_;
v_isShared_1498_ = v_isSharedCheck_1524_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_msg_1495_);
lean_inc(v_ref_1494_);
lean_dec(v_a_1493_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1524_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1499_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v_ref_1516_; lean_object* v___y_1518_; lean_object* v___x_1521_; 
v___x_1499_ = lean_box(0);
v_ref_1516_ = l_Lean_replaceRef(v_ref_1494_, v_ref_1492_);
lean_dec(v_ref_1494_);
v___x_1521_ = l_Lean_Syntax_getPos_x3f(v_ref_1516_, v___x_1479_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_unsigned_to_nat(0u);
v___y_1518_ = v___x_1522_;
goto v___jp_1517_;
}
else
{
lean_object* v_val_1523_; 
v_val_1523_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_val_1523_);
lean_dec_ref_known(v___x_1521_, 1);
v___y_1518_ = v_val_1523_;
goto v___jp_1517_;
}
v___jp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 1, v___y_1502_);
lean_ctor_set(v___x_1490_, 0, v___y_1501_);
v___x_1504_ = v___x_1490_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___y_1501_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v___y_1502_);
v___x_1504_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v_pos2traces_1508_; lean_object* v___x_1510_; 
v___x_1505_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1506_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1488_, v___x_1504_, v___x_1505_);
v___x_1507_ = lean_array_push(v___x_1506_, v_msg_1495_);
v_pos2traces_1508_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1488_, v___x_1504_, v___x_1507_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 1, v_pos2traces_1508_);
lean_ctor_set(v___x_1497_, 0, v___x_1499_);
v___x_1510_ = v___x_1497_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1499_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_pos2traces_1508_);
v___x_1510_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
size_t v___x_1511_; size_t v___x_1512_; 
v___x_1511_ = ((size_t)1ULL);
v___x_1512_ = lean_usize_add(v_i_1482_, v___x_1511_);
v_i_1482_ = v___x_1512_;
v_b_1483_ = v___x_1510_;
goto _start;
}
}
}
v___jp_1517_:
{
lean_object* v___x_1519_; 
v___x_1519_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1516_, v___x_1479_);
lean_dec(v_ref_1516_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_inc(v___y_1518_);
v___y_1501_ = v___y_1518_;
v___y_1502_ = v___y_1518_;
goto v___jp_1500_;
}
else
{
lean_object* v_val_1520_; 
v_val_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_val_1520_);
lean_dec_ref_known(v___x_1519_, 1);
v___y_1501_ = v___y_1518_;
v___y_1502_ = v_val_1520_;
goto v___jp_1500_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___boxed(lean_object* v___x_1527_, lean_object* v_as_1528_, lean_object* v_sz_1529_, lean_object* v_i_1530_, lean_object* v_b_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
uint8_t v___x_37756__boxed_1534_; size_t v_sz_boxed_1535_; size_t v_i_boxed_1536_; lean_object* v_res_1537_; 
v___x_37756__boxed_1534_ = lean_unbox(v___x_1527_);
v_sz_boxed_1535_ = lean_unbox_usize(v_sz_1529_);
lean_dec(v_sz_1529_);
v_i_boxed_1536_ = lean_unbox_usize(v_i_1530_);
lean_dec(v_i_1530_);
v_res_1537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_37756__boxed_1534_, v_as_1528_, v_sz_boxed_1535_, v_i_boxed_1536_, v_b_1531_, v___y_1532_);
lean_dec_ref(v___y_1532_);
lean_dec_ref(v_as_1528_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(uint8_t v___x_1538_, lean_object* v_as_1539_, size_t v_sz_1540_, size_t v_i_1541_, lean_object* v_b_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
uint8_t v___x_1546_; 
v___x_1546_ = lean_usize_dec_lt(v_i_1541_, v_sz_1540_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; 
v___x_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1547_, 0, v_b_1542_);
return v___x_1547_;
}
else
{
lean_object* v_snd_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1585_; 
v_snd_1548_ = lean_ctor_get(v_b_1542_, 1);
v_isSharedCheck_1585_ = !lean_is_exclusive(v_b_1542_);
if (v_isSharedCheck_1585_ == 0)
{
lean_object* v_unused_1586_; 
v_unused_1586_ = lean_ctor_get(v_b_1542_, 0);
lean_dec(v_unused_1586_);
v___x_1550_ = v_b_1542_;
v_isShared_1551_ = v_isSharedCheck_1585_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_snd_1548_);
lean_dec(v_b_1542_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1585_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v_ref_1552_; lean_object* v_a_1553_; lean_object* v_ref_1554_; lean_object* v_msg_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1584_; 
v_ref_1552_ = lean_ctor_get(v___y_1543_, 5);
v_a_1553_ = lean_array_uget(v_as_1539_, v_i_1541_);
v_ref_1554_ = lean_ctor_get(v_a_1553_, 0);
v_msg_1555_ = lean_ctor_get(v_a_1553_, 1);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_a_1553_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1557_ = v_a_1553_;
v_isShared_1558_ = v_isSharedCheck_1584_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_msg_1555_);
lean_inc(v_ref_1554_);
lean_dec(v_a_1553_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1584_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1559_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v_ref_1576_; lean_object* v___y_1578_; lean_object* v___x_1581_; 
v___x_1559_ = lean_box(0);
v_ref_1576_ = l_Lean_replaceRef(v_ref_1554_, v_ref_1552_);
lean_dec(v_ref_1554_);
v___x_1581_ = l_Lean_Syntax_getPos_x3f(v_ref_1576_, v___x_1538_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_unsigned_to_nat(0u);
v___y_1578_ = v___x_1582_;
goto v___jp_1577_;
}
else
{
lean_object* v_val_1583_; 
v_val_1583_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_val_1583_);
lean_dec_ref_known(v___x_1581_, 1);
v___y_1578_ = v_val_1583_;
goto v___jp_1577_;
}
v___jp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 1, v___y_1562_);
lean_ctor_set(v___x_1550_, 0, v___y_1561_);
v___x_1564_ = v___x_1550_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___y_1561_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v___y_1562_);
v___x_1564_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v_pos2traces_1568_; lean_object* v___x_1570_; 
v___x_1565_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1566_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1548_, v___x_1564_, v___x_1565_);
v___x_1567_ = lean_array_push(v___x_1566_, v_msg_1555_);
v_pos2traces_1568_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1548_, v___x_1564_, v___x_1567_);
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 1, v_pos2traces_1568_);
lean_ctor_set(v___x_1557_, 0, v___x_1559_);
v___x_1570_ = v___x_1557_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1559_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v_pos2traces_1568_);
v___x_1570_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
size_t v___x_1571_; size_t v___x_1572_; lean_object* v___x_1573_; 
v___x_1571_ = ((size_t)1ULL);
v___x_1572_ = lean_usize_add(v_i_1541_, v___x_1571_);
v___x_1573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_1538_, v_as_1539_, v_sz_1540_, v___x_1572_, v___x_1570_, v___y_1543_);
return v___x_1573_;
}
}
}
v___jp_1577_:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1576_, v___x_1538_);
lean_dec(v_ref_1576_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_inc(v___y_1578_);
v___y_1561_ = v___y_1578_;
v___y_1562_ = v___y_1578_;
goto v___jp_1560_;
}
else
{
lean_object* v_val_1580_; 
v_val_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_val_1580_);
lean_dec_ref_known(v___x_1579_, 1);
v___y_1561_ = v___y_1578_;
v___y_1562_ = v_val_1580_;
goto v___jp_1560_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40___boxed(lean_object* v___x_1587_, lean_object* v_as_1588_, lean_object* v_sz_1589_, lean_object* v_i_1590_, lean_object* v_b_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
uint8_t v___x_37837__boxed_1595_; size_t v_sz_boxed_1596_; size_t v_i_boxed_1597_; lean_object* v_res_1598_; 
v___x_37837__boxed_1595_ = lean_unbox(v___x_1587_);
v_sz_boxed_1596_ = lean_unbox_usize(v_sz_1589_);
lean_dec(v_sz_1589_);
v_i_boxed_1597_ = lean_unbox_usize(v_i_1590_);
lean_dec(v_i_1590_);
v_res_1598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_37837__boxed_1595_, v_as_1588_, v_sz_boxed_1596_, v_i_boxed_1597_, v_b_1591_, v___y_1592_, v___y_1593_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec_ref(v_as_1588_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(lean_object* v_init_1599_, uint8_t v___x_1600_, lean_object* v_n_1601_, lean_object* v_b_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
if (lean_obj_tag(v_n_1601_) == 0)
{
lean_object* v_cs_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; size_t v_sz_1609_; size_t v___x_1610_; lean_object* v___x_1611_; 
v_cs_1606_ = lean_ctor_get(v_n_1601_, 0);
v___x_1607_ = lean_box(0);
v___x_1608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
lean_ctor_set(v___x_1608_, 1, v_b_1602_);
v_sz_1609_ = lean_array_size(v_cs_1606_);
v___x_1610_ = ((size_t)0ULL);
v___x_1611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_1599_, v___x_1600_, v_cs_1606_, v_sz_1609_, v___x_1610_, v___x_1608_, v___y_1603_, v___y_1604_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1626_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1614_ = v___x_1611_;
v_isShared_1615_ = v_isSharedCheck_1626_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1611_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1626_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v_fst_1616_; 
v_fst_1616_ = lean_ctor_get(v_a_1612_, 0);
if (lean_obj_tag(v_fst_1616_) == 0)
{
lean_object* v_snd_1617_; lean_object* v___x_1618_; lean_object* v___x_1620_; 
v_snd_1617_ = lean_ctor_get(v_a_1612_, 1);
lean_inc(v_snd_1617_);
lean_dec(v_a_1612_);
v___x_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1618_, 0, v_snd_1617_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 0, v___x_1618_);
v___x_1620_ = v___x_1614_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1618_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
else
{
lean_object* v_val_1622_; lean_object* v___x_1624_; 
lean_inc_ref(v_fst_1616_);
lean_dec(v_a_1612_);
v_val_1622_ = lean_ctor_get(v_fst_1616_, 0);
lean_inc(v_val_1622_);
lean_dec_ref_known(v_fst_1616_, 1);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 0, v_val_1622_);
v___x_1624_ = v___x_1614_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_val_1622_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
v_a_1627_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1611_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1611_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
else
{
lean_object* v_vs_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; size_t v_sz_1638_; size_t v___x_1639_; lean_object* v___x_1640_; 
v_vs_1635_ = lean_ctor_get(v_n_1601_, 0);
v___x_1636_ = lean_box(0);
v___x_1637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
lean_ctor_set(v___x_1637_, 1, v_b_1602_);
v_sz_1638_ = lean_array_size(v_vs_1635_);
v___x_1639_ = ((size_t)0ULL);
v___x_1640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_1600_, v_vs_1635_, v_sz_1638_, v___x_1639_, v___x_1637_, v___y_1603_, v___y_1604_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1655_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1643_ = v___x_1640_;
v_isShared_1644_ = v_isSharedCheck_1655_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1640_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1655_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v_fst_1645_; 
v_fst_1645_ = lean_ctor_get(v_a_1641_, 0);
if (lean_obj_tag(v_fst_1645_) == 0)
{
lean_object* v_snd_1646_; lean_object* v___x_1647_; lean_object* v___x_1649_; 
v_snd_1646_ = lean_ctor_get(v_a_1641_, 1);
lean_inc(v_snd_1646_);
lean_dec(v_a_1641_);
v___x_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1647_, 0, v_snd_1646_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v___x_1647_);
v___x_1649_ = v___x_1643_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
else
{
lean_object* v_val_1651_; lean_object* v___x_1653_; 
lean_inc_ref(v_fst_1645_);
lean_dec(v_a_1641_);
v_val_1651_ = lean_ctor_get(v_fst_1645_, 0);
lean_inc(v_val_1651_);
lean_dec_ref_known(v_fst_1645_, 1);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v_val_1651_);
v___x_1653_ = v___x_1643_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_val_1651_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
v_a_1656_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1640_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1640_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(lean_object* v_init_1664_, uint8_t v___x_1665_, lean_object* v_as_1666_, size_t v_sz_1667_, size_t v_i_1668_, lean_object* v_b_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
uint8_t v___x_1673_; 
v___x_1673_ = lean_usize_dec_lt(v_i_1668_, v_sz_1667_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; 
v___x_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1674_, 0, v_b_1669_);
return v___x_1674_;
}
else
{
lean_object* v_snd_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1709_; 
v_snd_1675_ = lean_ctor_get(v_b_1669_, 1);
v_isSharedCheck_1709_ = !lean_is_exclusive(v_b_1669_);
if (v_isSharedCheck_1709_ == 0)
{
lean_object* v_unused_1710_; 
v_unused_1710_ = lean_ctor_get(v_b_1669_, 0);
lean_dec(v_unused_1710_);
v___x_1677_ = v_b_1669_;
v_isShared_1678_ = v_isSharedCheck_1709_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_snd_1675_);
lean_dec(v_b_1669_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1709_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v_a_1679_; lean_object* v___x_1680_; 
v_a_1679_ = lean_array_uget_borrowed(v_as_1666_, v_i_1668_);
lean_inc(v_snd_1675_);
v___x_1680_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1664_, v___x_1665_, v_a_1679_, v_snd_1675_, v___y_1670_, v___y_1671_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1700_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1683_ = v___x_1680_;
v_isShared_1684_ = v_isSharedCheck_1700_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1680_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1700_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
if (lean_obj_tag(v_a_1681_) == 0)
{
lean_object* v___x_1685_; lean_object* v___x_1687_; 
v___x_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1685_, 0, v_a_1681_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v___x_1685_);
v___x_1687_ = v___x_1677_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1685_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v_snd_1675_);
v___x_1687_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1689_; 
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 0, v___x_1687_);
v___x_1689_ = v___x_1683_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1687_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
else
{
lean_object* v_a_1692_; lean_object* v___x_1693_; lean_object* v___x_1695_; 
lean_del_object(v___x_1683_);
lean_dec(v_snd_1675_);
v_a_1692_ = lean_ctor_get(v_a_1681_, 0);
lean_inc(v_a_1692_);
lean_dec_ref_known(v_a_1681_, 1);
v___x_1693_ = lean_box(0);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 1, v_a_1692_);
lean_ctor_set(v___x_1677_, 0, v___x_1693_);
v___x_1695_ = v___x_1677_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1693_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_a_1692_);
v___x_1695_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
size_t v___x_1696_; size_t v___x_1697_; 
v___x_1696_ = ((size_t)1ULL);
v___x_1697_ = lean_usize_add(v_i_1668_, v___x_1696_);
v_i_1668_ = v___x_1697_;
v_b_1669_ = v___x_1695_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
lean_del_object(v___x_1677_);
lean_dec(v_snd_1675_);
v_a_1701_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1703_ = v___x_1680_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1680_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1701_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39___boxed(lean_object* v_init_1711_, lean_object* v___x_1712_, lean_object* v_as_1713_, lean_object* v_sz_1714_, lean_object* v_i_1715_, lean_object* v_b_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
uint8_t v___x_37918__boxed_1720_; size_t v_sz_boxed_1721_; size_t v_i_boxed_1722_; lean_object* v_res_1723_; 
v___x_37918__boxed_1720_ = lean_unbox(v___x_1712_);
v_sz_boxed_1721_ = lean_unbox_usize(v_sz_1714_);
lean_dec(v_sz_1714_);
v_i_boxed_1722_ = lean_unbox_usize(v_i_1715_);
lean_dec(v_i_1715_);
v_res_1723_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_1711_, v___x_37918__boxed_1720_, v_as_1713_, v_sz_boxed_1721_, v_i_boxed_1722_, v_b_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec_ref(v_as_1713_);
lean_dec_ref(v_init_1711_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27___boxed(lean_object* v_init_1724_, lean_object* v___x_1725_, lean_object* v_n_1726_, lean_object* v_b_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
uint8_t v___x_37938__boxed_1731_; lean_object* v_res_1732_; 
v___x_37938__boxed_1731_ = lean_unbox(v___x_1725_);
v_res_1732_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1724_, v___x_37938__boxed_1731_, v_n_1726_, v_b_1727_, v___y_1728_, v___y_1729_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec_ref(v_n_1726_);
lean_dec_ref(v_init_1724_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(uint8_t v___x_1733_, lean_object* v_as_1734_, size_t v_sz_1735_, size_t v_i_1736_, lean_object* v_b_1737_, lean_object* v___y_1738_){
_start:
{
uint8_t v___x_1740_; 
v___x_1740_ = lean_usize_dec_lt(v_i_1736_, v_sz_1735_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; 
v___x_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1741_, 0, v_b_1737_);
return v___x_1741_;
}
else
{
lean_object* v_snd_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1779_; 
v_snd_1742_ = lean_ctor_get(v_b_1737_, 1);
v_isSharedCheck_1779_ = !lean_is_exclusive(v_b_1737_);
if (v_isSharedCheck_1779_ == 0)
{
lean_object* v_unused_1780_; 
v_unused_1780_ = lean_ctor_get(v_b_1737_, 0);
lean_dec(v_unused_1780_);
v___x_1744_ = v_b_1737_;
v_isShared_1745_ = v_isSharedCheck_1779_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_snd_1742_);
lean_dec(v_b_1737_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1779_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v_ref_1746_; lean_object* v_a_1747_; lean_object* v_ref_1748_; lean_object* v_msg_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1778_; 
v_ref_1746_ = lean_ctor_get(v___y_1738_, 5);
v_a_1747_ = lean_array_uget(v_as_1734_, v_i_1736_);
v_ref_1748_ = lean_ctor_get(v_a_1747_, 0);
v_msg_1749_ = lean_ctor_get(v_a_1747_, 1);
v_isSharedCheck_1778_ = !lean_is_exclusive(v_a_1747_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1751_ = v_a_1747_;
v_isShared_1752_ = v_isSharedCheck_1778_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_msg_1749_);
lean_inc(v_ref_1748_);
lean_dec(v_a_1747_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1778_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1753_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v_ref_1770_; lean_object* v___y_1772_; lean_object* v___x_1775_; 
v___x_1753_ = lean_box(0);
v_ref_1770_ = l_Lean_replaceRef(v_ref_1748_, v_ref_1746_);
lean_dec(v_ref_1748_);
v___x_1775_ = l_Lean_Syntax_getPos_x3f(v_ref_1770_, v___x_1733_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v___x_1776_; 
v___x_1776_ = lean_unsigned_to_nat(0u);
v___y_1772_ = v___x_1776_;
goto v___jp_1771_;
}
else
{
lean_object* v_val_1777_; 
v_val_1777_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_val_1777_);
lean_dec_ref_known(v___x_1775_, 1);
v___y_1772_ = v_val_1777_;
goto v___jp_1771_;
}
v___jp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 1, v___y_1756_);
lean_ctor_set(v___x_1744_, 0, v___y_1755_);
v___x_1758_ = v___x_1744_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___y_1755_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v___y_1756_);
v___x_1758_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v_pos2traces_1762_; lean_object* v___x_1764_; 
v___x_1759_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1760_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1742_, v___x_1758_, v___x_1759_);
v___x_1761_ = lean_array_push(v___x_1760_, v_msg_1749_);
v_pos2traces_1762_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1742_, v___x_1758_, v___x_1761_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 1, v_pos2traces_1762_);
lean_ctor_set(v___x_1751_, 0, v___x_1753_);
v___x_1764_ = v___x_1751_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1753_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_pos2traces_1762_);
v___x_1764_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
size_t v___x_1765_; size_t v___x_1766_; 
v___x_1765_ = ((size_t)1ULL);
v___x_1766_ = lean_usize_add(v_i_1736_, v___x_1765_);
v_i_1736_ = v___x_1766_;
v_b_1737_ = v___x_1764_;
goto _start;
}
}
}
v___jp_1771_:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1770_, v___x_1733_);
lean_dec(v_ref_1770_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_inc(v___y_1772_);
v___y_1755_ = v___y_1772_;
v___y_1756_ = v___y_1772_;
goto v___jp_1754_;
}
else
{
lean_object* v_val_1774_; 
v_val_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_val_1774_);
lean_dec_ref_known(v___x_1773_, 1);
v___y_1755_ = v___y_1772_;
v___y_1756_ = v_val_1774_;
goto v___jp_1754_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg___boxed(lean_object* v___x_1781_, lean_object* v_as_1782_, lean_object* v_sz_1783_, lean_object* v_i_1784_, lean_object* v_b_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
uint8_t v___x_38121__boxed_1788_; size_t v_sz_boxed_1789_; size_t v_i_boxed_1790_; lean_object* v_res_1791_; 
v___x_38121__boxed_1788_ = lean_unbox(v___x_1781_);
v_sz_boxed_1789_ = lean_unbox_usize(v_sz_1783_);
lean_dec(v_sz_1783_);
v_i_boxed_1790_ = lean_unbox_usize(v_i_1784_);
lean_dec(v_i_1784_);
v_res_1791_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_38121__boxed_1788_, v_as_1782_, v_sz_boxed_1789_, v_i_boxed_1790_, v_b_1785_, v___y_1786_);
lean_dec_ref(v___y_1786_);
lean_dec_ref(v_as_1782_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(uint8_t v___x_1792_, lean_object* v_as_1793_, size_t v_sz_1794_, size_t v_i_1795_, lean_object* v_b_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
uint8_t v___x_1800_; 
v___x_1800_ = lean_usize_dec_lt(v_i_1795_, v_sz_1794_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1801_; 
v___x_1801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1801_, 0, v_b_1796_);
return v___x_1801_;
}
else
{
lean_object* v_snd_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1839_; 
v_snd_1802_ = lean_ctor_get(v_b_1796_, 1);
v_isSharedCheck_1839_ = !lean_is_exclusive(v_b_1796_);
if (v_isSharedCheck_1839_ == 0)
{
lean_object* v_unused_1840_; 
v_unused_1840_ = lean_ctor_get(v_b_1796_, 0);
lean_dec(v_unused_1840_);
v___x_1804_ = v_b_1796_;
v_isShared_1805_ = v_isSharedCheck_1839_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_snd_1802_);
lean_dec(v_b_1796_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1839_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v_ref_1806_; lean_object* v_a_1807_; lean_object* v_ref_1808_; lean_object* v_msg_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1838_; 
v_ref_1806_ = lean_ctor_get(v___y_1797_, 5);
v_a_1807_ = lean_array_uget(v_as_1793_, v_i_1795_);
v_ref_1808_ = lean_ctor_get(v_a_1807_, 0);
v_msg_1809_ = lean_ctor_get(v_a_1807_, 1);
v_isSharedCheck_1838_ = !lean_is_exclusive(v_a_1807_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1811_ = v_a_1807_;
v_isShared_1812_ = v_isSharedCheck_1838_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_msg_1809_);
lean_inc(v_ref_1808_);
lean_dec(v_a_1807_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1838_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1813_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v_ref_1830_; lean_object* v___y_1832_; lean_object* v___x_1835_; 
v___x_1813_ = lean_box(0);
v_ref_1830_ = l_Lean_replaceRef(v_ref_1808_, v_ref_1806_);
lean_dec(v_ref_1808_);
v___x_1835_ = l_Lean_Syntax_getPos_x3f(v_ref_1830_, v___x_1792_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v___x_1836_; 
v___x_1836_ = lean_unsigned_to_nat(0u);
v___y_1832_ = v___x_1836_;
goto v___jp_1831_;
}
else
{
lean_object* v_val_1837_; 
v_val_1837_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_val_1837_);
lean_dec_ref_known(v___x_1835_, 1);
v___y_1832_ = v_val_1837_;
goto v___jp_1831_;
}
v___jp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 1, v___y_1816_);
lean_ctor_set(v___x_1804_, 0, v___y_1815_);
v___x_1818_ = v___x_1804_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___y_1815_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v___y_1816_);
v___x_1818_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v_pos2traces_1822_; lean_object* v___x_1824_; 
v___x_1819_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1820_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1802_, v___x_1818_, v___x_1819_);
v___x_1821_ = lean_array_push(v___x_1820_, v_msg_1809_);
v_pos2traces_1822_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1802_, v___x_1818_, v___x_1821_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 1, v_pos2traces_1822_);
lean_ctor_set(v___x_1811_, 0, v___x_1813_);
v___x_1824_ = v___x_1811_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1813_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v_pos2traces_1822_);
v___x_1824_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
size_t v___x_1825_; size_t v___x_1826_; lean_object* v___x_1827_; 
v___x_1825_ = ((size_t)1ULL);
v___x_1826_ = lean_usize_add(v_i_1795_, v___x_1825_);
v___x_1827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_1792_, v_as_1793_, v_sz_1794_, v___x_1826_, v___x_1824_, v___y_1797_);
return v___x_1827_;
}
}
}
v___jp_1831_:
{
lean_object* v___x_1833_; 
v___x_1833_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1830_, v___x_1792_);
lean_dec(v_ref_1830_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_inc(v___y_1832_);
v___y_1815_ = v___y_1832_;
v___y_1816_ = v___y_1832_;
goto v___jp_1814_;
}
else
{
lean_object* v_val_1834_; 
v_val_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_val_1834_);
lean_dec_ref_known(v___x_1833_, 1);
v___y_1815_ = v___y_1832_;
v___y_1816_ = v_val_1834_;
goto v___jp_1814_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28___boxed(lean_object* v___x_1841_, lean_object* v_as_1842_, lean_object* v_sz_1843_, lean_object* v_i_1844_, lean_object* v_b_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
uint8_t v___x_38201__boxed_1849_; size_t v_sz_boxed_1850_; size_t v_i_boxed_1851_; lean_object* v_res_1852_; 
v___x_38201__boxed_1849_ = lean_unbox(v___x_1841_);
v_sz_boxed_1850_ = lean_unbox_usize(v_sz_1843_);
lean_dec(v_sz_1843_);
v_i_boxed_1851_ = lean_unbox_usize(v_i_1844_);
lean_dec(v_i_1844_);
v_res_1852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_38201__boxed_1849_, v_as_1842_, v_sz_boxed_1850_, v_i_boxed_1851_, v_b_1845_, v___y_1846_, v___y_1847_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec_ref(v_as_1842_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(uint8_t v___x_1853_, lean_object* v_t_1854_, lean_object* v_init_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v_root_1859_; lean_object* v_tail_1860_; lean_object* v___x_1861_; 
v_root_1859_ = lean_ctor_get(v_t_1854_, 0);
v_tail_1860_ = lean_ctor_get(v_t_1854_, 1);
lean_inc_ref(v_init_1855_);
v___x_1861_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1855_, v___x_1853_, v_root_1859_, v_init_1855_, v___y_1856_, v___y_1857_);
lean_dec_ref(v_init_1855_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1898_; 
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1864_ = v___x_1861_;
v_isShared_1865_ = v_isSharedCheck_1898_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1861_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1898_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
if (lean_obj_tag(v_a_1862_) == 0)
{
lean_object* v_a_1866_; lean_object* v___x_1868_; 
v_a_1866_ = lean_ctor_get(v_a_1862_, 0);
lean_inc(v_a_1866_);
lean_dec_ref_known(v_a_1862_, 1);
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 0, v_a_1866_);
v___x_1868_ = v___x_1864_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1866_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; size_t v_sz_1873_; size_t v___x_1874_; lean_object* v___x_1875_; 
lean_del_object(v___x_1864_);
v_a_1870_ = lean_ctor_get(v_a_1862_, 0);
lean_inc(v_a_1870_);
lean_dec_ref_known(v_a_1862_, 1);
v___x_1871_ = lean_box(0);
v___x_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
lean_ctor_set(v___x_1872_, 1, v_a_1870_);
v_sz_1873_ = lean_array_size(v_tail_1860_);
v___x_1874_ = ((size_t)0ULL);
v___x_1875_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_1853_, v_tail_1860_, v_sz_1873_, v___x_1874_, v___x_1872_, v___y_1856_, v___y_1857_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1889_; 
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1878_ = v___x_1875_;
v_isShared_1879_ = v_isSharedCheck_1889_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1875_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1889_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v_fst_1880_; 
v_fst_1880_ = lean_ctor_get(v_a_1876_, 0);
if (lean_obj_tag(v_fst_1880_) == 0)
{
lean_object* v_snd_1881_; lean_object* v___x_1883_; 
v_snd_1881_ = lean_ctor_get(v_a_1876_, 1);
lean_inc(v_snd_1881_);
lean_dec(v_a_1876_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v_snd_1881_);
v___x_1883_ = v___x_1878_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_snd_1881_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
else
{
lean_object* v_val_1885_; lean_object* v___x_1887_; 
lean_inc_ref(v_fst_1880_);
lean_dec(v_a_1876_);
v_val_1885_ = lean_ctor_get(v_fst_1880_, 0);
lean_inc(v_val_1885_);
lean_dec_ref_known(v_fst_1880_, 1);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v_val_1885_);
v___x_1887_ = v___x_1878_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_val_1885_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
v_a_1890_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1875_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1875_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
}
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
v_a_1899_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1861_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1861_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19___boxed(lean_object* v___x_1907_, lean_object* v_t_1908_, lean_object* v_init_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
uint8_t v___x_38282__boxed_1913_; lean_object* v_res_1914_; 
v___x_38282__boxed_1913_ = lean_unbox(v___x_1907_);
v_res_1914_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_38282__boxed_1913_, v_t_1908_, v_init_1909_, v___y_1910_, v___y_1911_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec_ref(v_t_1908_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(lean_object* v_x_1915_, lean_object* v_x_1916_){
_start:
{
if (lean_obj_tag(v_x_1916_) == 0)
{
return v_x_1915_;
}
else
{
lean_object* v_key_1917_; lean_object* v_value_1918_; lean_object* v_tail_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v_key_1917_ = lean_ctor_get(v_x_1916_, 0);
v_value_1918_ = lean_ctor_get(v_x_1916_, 1);
v_tail_1919_ = lean_ctor_get(v_x_1916_, 2);
lean_inc(v_value_1918_);
lean_inc(v_key_1917_);
v___x_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1920_, 0, v_key_1917_);
lean_ctor_set(v___x_1920_, 1, v_value_1918_);
v___x_1921_ = lean_array_push(v_x_1915_, v___x_1920_);
v_x_1915_ = v___x_1921_;
v_x_1916_ = v_tail_1919_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22___boxed(lean_object* v_x_1923_, lean_object* v_x_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_x_1923_, v_x_1924_);
lean_dec(v_x_1924_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(lean_object* v_as_1926_, size_t v_i_1927_, size_t v_stop_1928_, lean_object* v_b_1929_){
_start:
{
uint8_t v___x_1930_; 
v___x_1930_ = lean_usize_dec_eq(v_i_1927_, v_stop_1928_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; lean_object* v___x_1932_; size_t v___x_1933_; size_t v___x_1934_; 
v___x_1931_ = lean_array_uget_borrowed(v_as_1926_, v_i_1927_);
v___x_1932_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_b_1929_, v___x_1931_);
v___x_1933_ = ((size_t)1ULL);
v___x_1934_ = lean_usize_add(v_i_1927_, v___x_1933_);
v_i_1927_ = v___x_1934_;
v_b_1929_ = v___x_1932_;
goto _start;
}
else
{
return v_b_1929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23___boxed(lean_object* v_as_1936_, lean_object* v_i_1937_, lean_object* v_stop_1938_, lean_object* v_b_1939_){
_start:
{
size_t v_i_boxed_1940_; size_t v_stop_boxed_1941_; lean_object* v_res_1942_; 
v_i_boxed_1940_ = lean_unbox_usize(v_i_1937_);
lean_dec(v_i_1937_);
v_stop_boxed_1941_ = lean_unbox_usize(v_stop_1938_);
lean_dec(v_stop_1938_);
v_res_1942_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_as_1936_, v_i_boxed_1940_, v_stop_boxed_1941_, v_b_1939_);
lean_dec_ref(v_as_1936_);
return v_res_1942_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0(void){
_start:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1943_ = lean_unsigned_to_nat(32u);
v___x_1944_ = lean_mk_empty_array_with_capacity(v___x_1943_);
v___x_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
return v___x_1945_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1(void){
_start:
{
size_t v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1946_ = ((size_t)5ULL);
v___x_1947_ = lean_unsigned_to_nat(0u);
v___x_1948_ = lean_unsigned_to_nat(32u);
v___x_1949_ = lean_mk_empty_array_with_capacity(v___x_1948_);
v___x_1950_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0);
v___x_1951_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
lean_ctor_set(v___x_1951_, 1, v___x_1949_);
lean_ctor_set(v___x_1951_, 2, v___x_1947_);
lean_ctor_set(v___x_1951_, 3, v___x_1947_);
lean_ctor_set_usize(v___x_1951_, 4, v___x_1946_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(lean_object* v___y_1952_){
_start:
{
lean_object* v___x_1954_; lean_object* v_traceState_1955_; lean_object* v_traces_1956_; lean_object* v___x_1957_; lean_object* v_traceState_1958_; lean_object* v_env_1959_; lean_object* v_nextMacroScope_1960_; lean_object* v_ngen_1961_; lean_object* v_auxDeclNGen_1962_; lean_object* v_cache_1963_; lean_object* v_messages_1964_; lean_object* v_infoState_1965_; lean_object* v_snapshotTasks_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1985_; 
v___x_1954_ = lean_st_ref_get(v___y_1952_);
v_traceState_1955_ = lean_ctor_get(v___x_1954_, 4);
lean_inc_ref(v_traceState_1955_);
lean_dec(v___x_1954_);
v_traces_1956_ = lean_ctor_get(v_traceState_1955_, 0);
lean_inc_ref(v_traces_1956_);
lean_dec_ref(v_traceState_1955_);
v___x_1957_ = lean_st_ref_take(v___y_1952_);
v_traceState_1958_ = lean_ctor_get(v___x_1957_, 4);
v_env_1959_ = lean_ctor_get(v___x_1957_, 0);
v_nextMacroScope_1960_ = lean_ctor_get(v___x_1957_, 1);
v_ngen_1961_ = lean_ctor_get(v___x_1957_, 2);
v_auxDeclNGen_1962_ = lean_ctor_get(v___x_1957_, 3);
v_cache_1963_ = lean_ctor_get(v___x_1957_, 5);
v_messages_1964_ = lean_ctor_get(v___x_1957_, 6);
v_infoState_1965_ = lean_ctor_get(v___x_1957_, 7);
v_snapshotTasks_1966_ = lean_ctor_get(v___x_1957_, 8);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1968_ = v___x_1957_;
v_isShared_1969_ = v_isSharedCheck_1985_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_snapshotTasks_1966_);
lean_inc(v_infoState_1965_);
lean_inc(v_messages_1964_);
lean_inc(v_cache_1963_);
lean_inc(v_traceState_1958_);
lean_inc(v_auxDeclNGen_1962_);
lean_inc(v_ngen_1961_);
lean_inc(v_nextMacroScope_1960_);
lean_inc(v_env_1959_);
lean_dec(v___x_1957_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1985_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
uint64_t v_tid_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1983_; 
v_tid_1970_ = lean_ctor_get_uint64(v_traceState_1958_, sizeof(void*)*1);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_traceState_1958_);
if (v_isSharedCheck_1983_ == 0)
{
lean_object* v_unused_1984_; 
v_unused_1984_ = lean_ctor_get(v_traceState_1958_, 0);
lean_dec(v_unused_1984_);
v___x_1972_ = v_traceState_1958_;
v_isShared_1973_ = v_isSharedCheck_1983_;
goto v_resetjp_1971_;
}
else
{
lean_dec(v_traceState_1958_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1983_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1974_; lean_object* v___x_1976_; 
v___x_1974_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1974_);
v___x_1976_ = v___x_1972_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1974_);
lean_ctor_set_uint64(v_reuseFailAlloc_1982_, sizeof(void*)*1, v_tid_1970_);
v___x_1976_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v___x_1978_; 
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 4, v___x_1976_);
v___x_1978_ = v___x_1968_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_env_1959_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v_nextMacroScope_1960_);
lean_ctor_set(v_reuseFailAlloc_1981_, 2, v_ngen_1961_);
lean_ctor_set(v_reuseFailAlloc_1981_, 3, v_auxDeclNGen_1962_);
lean_ctor_set(v_reuseFailAlloc_1981_, 4, v___x_1976_);
lean_ctor_set(v_reuseFailAlloc_1981_, 5, v_cache_1963_);
lean_ctor_set(v_reuseFailAlloc_1981_, 6, v_messages_1964_);
lean_ctor_set(v_reuseFailAlloc_1981_, 7, v_infoState_1965_);
lean_ctor_set(v_reuseFailAlloc_1981_, 8, v_snapshotTasks_1966_);
v___x_1978_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = lean_st_ref_set(v___y_1952_, v___x_1978_);
v___x_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1980_, 0, v_traces_1956_);
return v___x_1980_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___boxed(lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_1986_);
lean_dec(v___y_1986_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(lean_object* v_hi_1989_, lean_object* v_pivot_1990_, lean_object* v_as_1991_, lean_object* v_i_1992_, lean_object* v_k_1993_){
_start:
{
uint8_t v___x_1994_; 
v___x_1994_ = lean_nat_dec_lt(v_k_1993_, v_hi_1989_);
if (v___x_1994_ == 0)
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
lean_dec(v_k_1993_);
v___x_1995_ = lean_array_fswap(v_as_1991_, v_i_1992_, v_hi_1989_);
v___x_1996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1996_, 0, v_i_1992_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
return v___x_1996_;
}
else
{
lean_object* v___x_1997_; lean_object* v_fst_1998_; lean_object* v_fst_1999_; lean_object* v_fst_2000_; lean_object* v_fst_2001_; uint8_t v___x_2002_; 
v___x_1997_ = lean_array_fget_borrowed(v_as_1991_, v_k_1993_);
v_fst_1998_ = lean_ctor_get(v___x_1997_, 0);
v_fst_1999_ = lean_ctor_get(v_pivot_1990_, 0);
v_fst_2000_ = lean_ctor_get(v_fst_1998_, 0);
v_fst_2001_ = lean_ctor_get(v_fst_1999_, 0);
v___x_2002_ = lean_nat_dec_lt(v_fst_2000_, v_fst_2001_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = lean_unsigned_to_nat(1u);
v___x_2004_ = lean_nat_add(v_k_1993_, v___x_2003_);
lean_dec(v_k_1993_);
v_k_1993_ = v___x_2004_;
goto _start;
}
else
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2006_ = lean_array_fswap(v_as_1991_, v_i_1992_, v_k_1993_);
v___x_2007_ = lean_unsigned_to_nat(1u);
v___x_2008_ = lean_nat_add(v_i_1992_, v___x_2007_);
lean_dec(v_i_1992_);
v___x_2009_ = lean_nat_add(v_k_1993_, v___x_2007_);
lean_dec(v_k_1993_);
v_as_1991_ = v___x_2006_;
v_i_1992_ = v___x_2008_;
v_k_1993_ = v___x_2009_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg___boxed(lean_object* v_hi_2011_, lean_object* v_pivot_2012_, lean_object* v_as_2013_, lean_object* v_i_2014_, lean_object* v_k_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_2011_, v_pivot_2012_, v_as_2013_, v_i_2014_, v_k_2015_);
lean_dec_ref(v_pivot_2012_);
lean_dec(v_hi_2011_);
return v_res_2016_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(lean_object* v_x_2017_, lean_object* v_x_2018_){
_start:
{
lean_object* v_fst_2019_; lean_object* v_fst_2020_; lean_object* v_fst_2021_; lean_object* v_fst_2022_; uint8_t v___x_2023_; 
v_fst_2019_ = lean_ctor_get(v_x_2017_, 0);
v_fst_2020_ = lean_ctor_get(v_x_2018_, 0);
v_fst_2021_ = lean_ctor_get(v_fst_2019_, 0);
v_fst_2022_ = lean_ctor_get(v_fst_2020_, 0);
v___x_2023_ = lean_nat_dec_lt(v_fst_2021_, v_fst_2022_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0___boxed(lean_object* v_x_2024_, lean_object* v_x_2025_){
_start:
{
uint8_t v_res_2026_; lean_object* v_r_2027_; 
v_res_2026_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v_x_2024_, v_x_2025_);
lean_dec_ref(v_x_2025_);
lean_dec_ref(v_x_2024_);
v_r_2027_ = lean_box(v_res_2026_);
return v_r_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(lean_object* v_n_2028_, lean_object* v_as_2029_, lean_object* v_lo_2030_, lean_object* v_hi_2031_){
_start:
{
lean_object* v___y_2033_; uint8_t v___x_2043_; 
v___x_2043_ = lean_nat_dec_lt(v_lo_2030_, v_hi_2031_);
if (v___x_2043_ == 0)
{
lean_dec(v_lo_2030_);
return v_as_2029_;
}
else
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v_mid_2046_; lean_object* v___y_2048_; lean_object* v___y_2054_; lean_object* v___x_2059_; lean_object* v___x_2060_; uint8_t v___x_2061_; 
v___x_2044_ = lean_nat_add(v_lo_2030_, v_hi_2031_);
v___x_2045_ = lean_unsigned_to_nat(1u);
v_mid_2046_ = lean_nat_shiftr(v___x_2044_, v___x_2045_);
lean_dec(v___x_2044_);
v___x_2059_ = lean_array_fget_borrowed(v_as_2029_, v_mid_2046_);
v___x_2060_ = lean_array_fget_borrowed(v_as_2029_, v_lo_2030_);
v___x_2061_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2059_, v___x_2060_);
if (v___x_2061_ == 0)
{
v___y_2054_ = v_as_2029_;
goto v___jp_2053_;
}
else
{
lean_object* v___x_2062_; 
v___x_2062_ = lean_array_fswap(v_as_2029_, v_lo_2030_, v_mid_2046_);
v___y_2054_ = v___x_2062_;
goto v___jp_2053_;
}
v___jp_2047_:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; uint8_t v___x_2051_; 
v___x_2049_ = lean_array_fget_borrowed(v___y_2048_, v_mid_2046_);
v___x_2050_ = lean_array_fget_borrowed(v___y_2048_, v_hi_2031_);
v___x_2051_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2049_, v___x_2050_);
if (v___x_2051_ == 0)
{
lean_dec(v_mid_2046_);
v___y_2033_ = v___y_2048_;
goto v___jp_2032_;
}
else
{
lean_object* v___x_2052_; 
v___x_2052_ = lean_array_fswap(v___y_2048_, v_mid_2046_, v_hi_2031_);
lean_dec(v_mid_2046_);
v___y_2033_ = v___x_2052_;
goto v___jp_2032_;
}
}
v___jp_2053_:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; uint8_t v___x_2057_; 
v___x_2055_ = lean_array_fget_borrowed(v___y_2054_, v_hi_2031_);
v___x_2056_ = lean_array_fget_borrowed(v___y_2054_, v_lo_2030_);
v___x_2057_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2055_, v___x_2056_);
if (v___x_2057_ == 0)
{
v___y_2048_ = v___y_2054_;
goto v___jp_2047_;
}
else
{
lean_object* v___x_2058_; 
v___x_2058_ = lean_array_fswap(v___y_2054_, v_lo_2030_, v_hi_2031_);
v___y_2048_ = v___x_2058_;
goto v___jp_2047_;
}
}
}
v___jp_2032_:
{
lean_object* v_pivot_2034_; lean_object* v___x_2035_; lean_object* v_fst_2036_; lean_object* v_snd_2037_; uint8_t v___x_2038_; 
v_pivot_2034_ = lean_array_fget(v___y_2033_, v_hi_2031_);
lean_inc_n(v_lo_2030_, 2);
v___x_2035_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_2031_, v_pivot_2034_, v___y_2033_, v_lo_2030_, v_lo_2030_);
lean_dec(v_pivot_2034_);
v_fst_2036_ = lean_ctor_get(v___x_2035_, 0);
lean_inc(v_fst_2036_);
v_snd_2037_ = lean_ctor_get(v___x_2035_, 1);
lean_inc(v_snd_2037_);
lean_dec_ref(v___x_2035_);
v___x_2038_ = lean_nat_dec_le(v_hi_2031_, v_fst_2036_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2039_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_2028_, v_snd_2037_, v_lo_2030_, v_fst_2036_);
v___x_2040_ = lean_unsigned_to_nat(1u);
v___x_2041_ = lean_nat_add(v_fst_2036_, v___x_2040_);
lean_dec(v_fst_2036_);
v_as_2029_ = v___x_2039_;
v_lo_2030_ = v___x_2041_;
goto _start;
}
else
{
lean_dec(v_fst_2036_);
lean_dec(v_lo_2030_);
return v_snd_2037_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___boxed(lean_object* v_n_2063_, lean_object* v_as_2064_, lean_object* v_lo_2065_, lean_object* v_hi_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_2063_, v_as_2064_, v_lo_2065_, v_hi_2066_);
lean_dec(v_hi_2066_);
lean_dec(v_n_2063_);
return v_res_2067_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2068_ = lean_box(0);
v___x_2069_ = lean_unsigned_to_nat(16u);
v___x_2070_ = lean_mk_array(v___x_2069_, v___x_2068_);
return v___x_2070_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1(void){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v_pos2traces_2073_; 
v___x_2071_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0);
v___x_2072_ = lean_unsigned_to_nat(0u);
v_pos2traces_2073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_2073_, 0, v___x_2072_);
lean_ctor_set(v_pos2traces_2073_, 1, v___x_2071_);
return v_pos2traces_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10(lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v_options_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v_options_2080_ = lean_ctor_get(v___y_2074_, 2);
v___x_2081_ = l_Lean_trace_profiler_output;
v___x_2082_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(v_options_2080_, v___x_2081_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v___x_2083_; uint8_t v___x_2084_; 
v___x_2083_ = l_Lean_trace_profiler_serve;
v___x_2084_ = l_Lean_Option_get___at___00main_spec__8(v_options_2080_, v___x_2083_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2152_; 
v___x_2085_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_2075_);
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2088_ = v___x_2085_;
v_isShared_2089_ = v_isSharedCheck_2152_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2085_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2152_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
uint8_t v___x_2090_; 
v___x_2090_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_2086_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; lean_object* v_pos2traces_2092_; lean_object* v___x_2093_; 
lean_del_object(v___x_2088_);
v___x_2091_ = lean_unsigned_to_nat(0u);
v_pos2traces_2092_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1);
v___x_2093_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_2090_, v_a_2086_, v_pos2traces_2092_, v___y_2074_, v___y_2075_);
lean_dec(v_a_2086_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v___y_2096_; lean_object* v___y_2110_; lean_object* v___y_2111_; lean_object* v___y_2112_; lean_object* v___y_2113_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2122_; lean_object* v_size_2128_; lean_object* v_buckets_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; uint8_t v___x_2132_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_a_2094_);
lean_dec_ref_known(v___x_2093_, 1);
v_size_2128_ = lean_ctor_get(v_a_2094_, 0);
lean_inc(v_size_2128_);
v_buckets_2129_ = lean_ctor_get(v_a_2094_, 1);
lean_inc_ref(v_buckets_2129_);
lean_dec(v_a_2094_);
v___x_2130_ = lean_mk_empty_array_with_capacity(v_size_2128_);
lean_dec(v_size_2128_);
v___x_2131_ = lean_array_get_size(v_buckets_2129_);
v___x_2132_ = lean_nat_dec_lt(v___x_2091_, v___x_2131_);
if (v___x_2132_ == 0)
{
lean_dec_ref(v_buckets_2129_);
v___y_2122_ = v___x_2130_;
goto v___jp_2121_;
}
else
{
uint8_t v___x_2133_; 
v___x_2133_ = lean_nat_dec_le(v___x_2131_, v___x_2131_);
if (v___x_2133_ == 0)
{
if (v___x_2132_ == 0)
{
lean_dec_ref(v_buckets_2129_);
v___y_2122_ = v___x_2130_;
goto v___jp_2121_;
}
else
{
size_t v___x_2134_; size_t v___x_2135_; lean_object* v___x_2136_; 
v___x_2134_ = ((size_t)0ULL);
v___x_2135_ = lean_usize_of_nat(v___x_2131_);
v___x_2136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_buckets_2129_, v___x_2134_, v___x_2135_, v___x_2130_);
lean_dec_ref(v_buckets_2129_);
v___y_2122_ = v___x_2136_;
goto v___jp_2121_;
}
}
else
{
size_t v___x_2137_; size_t v___x_2138_; lean_object* v___x_2139_; 
v___x_2137_ = ((size_t)0ULL);
v___x_2138_ = lean_usize_of_nat(v___x_2131_);
v___x_2139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_buckets_2129_, v___x_2137_, v___x_2138_, v___x_2130_);
lean_dec_ref(v_buckets_2129_);
v___y_2122_ = v___x_2139_;
goto v___jp_2121_;
}
}
v___jp_2095_:
{
lean_object* v___x_2097_; size_t v_sz_2098_; size_t v___x_2099_; lean_object* v___x_2100_; 
v___x_2097_ = lean_box(0);
v_sz_2098_ = lean_array_size(v___y_2096_);
v___x_2099_ = ((size_t)0ULL);
v___x_2100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_2084_, v___y_2096_, v_sz_2098_, v___x_2099_, v___x_2097_, v___y_2074_, v___y_2075_);
lean_dec_ref(v___y_2096_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2107_ == 0)
{
lean_object* v_unused_2108_; 
v_unused_2108_ = lean_ctor_get(v___x_2100_, 0);
lean_dec(v_unused_2108_);
v___x_2102_ = v___x_2100_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_dec(v___x_2100_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2097_);
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2097_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
else
{
return v___x_2100_;
}
}
v___jp_2109_:
{
lean_object* v___x_2114_; 
v___x_2114_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
lean_dec(v___y_2113_);
lean_dec(v___y_2110_);
v___y_2096_ = v___x_2114_;
goto v___jp_2095_;
}
v___jp_2115_:
{
uint8_t v___x_2120_; 
v___x_2120_ = lean_nat_dec_le(v___y_2119_, v___y_2117_);
if (v___x_2120_ == 0)
{
lean_dec(v___y_2117_);
lean_inc(v___y_2119_);
v___y_2110_ = v___y_2116_;
v___y_2111_ = v___y_2118_;
v___y_2112_ = v___y_2119_;
v___y_2113_ = v___y_2119_;
goto v___jp_2109_;
}
else
{
v___y_2110_ = v___y_2116_;
v___y_2111_ = v___y_2118_;
v___y_2112_ = v___y_2119_;
v___y_2113_ = v___y_2117_;
goto v___jp_2109_;
}
}
v___jp_2121_:
{
lean_object* v___x_2123_; uint8_t v___x_2124_; 
v___x_2123_ = lean_array_get_size(v___y_2122_);
v___x_2124_ = lean_nat_dec_eq(v___x_2123_, v___x_2091_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; lean_object* v___x_2126_; uint8_t v___x_2127_; 
v___x_2125_ = lean_unsigned_to_nat(1u);
v___x_2126_ = lean_nat_sub(v___x_2123_, v___x_2125_);
v___x_2127_ = lean_nat_dec_le(v___x_2091_, v___x_2126_);
if (v___x_2127_ == 0)
{
lean_inc(v___x_2126_);
v___y_2116_ = v___x_2123_;
v___y_2117_ = v___x_2126_;
v___y_2118_ = v___y_2122_;
v___y_2119_ = v___x_2126_;
goto v___jp_2115_;
}
else
{
v___y_2116_ = v___x_2123_;
v___y_2117_ = v___x_2126_;
v___y_2118_ = v___y_2122_;
v___y_2119_ = v___x_2091_;
goto v___jp_2115_;
}
}
else
{
v___y_2096_ = v___y_2122_;
goto v___jp_2095_;
}
}
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
v_a_2140_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2093_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2093_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
else
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
lean_dec(v_a_2086_);
v___x_2148_ = lean_box(0);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 0, v___x_2148_);
v___x_2150_ = v___x_2088_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
else
{
goto v___jp_2077_;
}
}
else
{
lean_dec_ref_known(v___x_2082_, 1);
goto v___jp_2077_;
}
v___jp_2077_:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = lean_box(0);
v___x_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
return v___x_2079_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10___boxed(lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(lean_object* v_as_2157_, size_t v_sz_2158_, size_t v_i_2159_, lean_object* v_b_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
uint8_t v___x_2164_; 
v___x_2164_ = lean_usize_dec_lt(v_i_2159_, v_sz_2158_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; 
v___x_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2165_, 0, v_b_2160_);
return v___x_2165_;
}
else
{
lean_object* v_options_2166_; lean_object* v_a_2167_; lean_object* v___x_2168_; 
v_options_2166_ = lean_ctor_get(v___y_2161_, 2);
v_a_2167_ = lean_array_uget_borrowed(v_as_2157_, v_i_2159_);
lean_inc_ref(v_options_2166_);
lean_inc(v_a_2167_);
v___x_2168_ = l_Lean_Compiler_LCNF_resumeCompilation(v_a_2167_, v_options_2166_, v___y_2161_, v___y_2162_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v___x_2169_; 
lean_dec_ref_known(v___x_2168_, 1);
v___x_2169_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2161_, v___y_2162_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v___x_2170_; size_t v___x_2171_; size_t v___x_2172_; 
lean_dec_ref_known(v___x_2169_, 1);
v___x_2170_ = lean_box(0);
v___x_2171_ = ((size_t)1ULL);
v___x_2172_ = lean_usize_add(v_i_2159_, v___x_2171_);
v_i_2159_ = v___x_2172_;
v_b_2160_ = v___x_2170_;
goto _start;
}
else
{
return v___x_2169_;
}
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2175_; 
v_a_2174_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2174_);
lean_dec_ref_known(v___x_2168_, 1);
v___x_2175_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2161_, v___y_2162_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2182_ == 0)
{
lean_object* v_unused_2183_; 
v_unused_2183_ = lean_ctor_get(v___x_2175_, 0);
lean_dec(v_unused_2183_);
v___x_2177_ = v___x_2175_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_dec(v___x_2175_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
lean_ctor_set_tag(v___x_2177_, 1);
lean_ctor_set(v___x_2177_, 0, v_a_2174_);
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2174_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
else
{
lean_dec(v_a_2174_);
return v___x_2175_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11___boxed(lean_object* v_as_2184_, lean_object* v_sz_2185_, lean_object* v_i_2186_, lean_object* v_b_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
size_t v_sz_boxed_2191_; size_t v_i_boxed_2192_; lean_object* v_res_2193_; 
v_sz_boxed_2191_ = lean_unbox_usize(v_sz_2185_);
lean_dec(v_sz_2185_);
v_i_boxed_2192_ = lean_unbox_usize(v_i_2186_);
lean_dec(v_i_2186_);
v_res_2193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_as_2184_, v_sz_boxed_2191_, v_i_boxed_2192_, v_b_2187_, v___y_2188_, v___y_2189_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec_ref(v_as_2184_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(lean_object* v_as_2194_, size_t v_sz_2195_, size_t v_i_2196_, lean_object* v_b_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
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
lean_object* v_a_2203_; lean_object* v_declNames_2204_; lean_object* v___x_2205_; size_t v_sz_2206_; size_t v___x_2207_; lean_object* v___x_2208_; 
v_a_2203_ = lean_array_uget_borrowed(v_as_2194_, v_i_2196_);
v_declNames_2204_ = lean_ctor_get(v_a_2203_, 0);
v___x_2205_ = lean_box(0);
v_sz_2206_ = lean_array_size(v_declNames_2204_);
v___x_2207_ = ((size_t)0ULL);
v___x_2208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_declNames_2204_, v_sz_2206_, v___x_2207_, v___x_2205_, v___y_2198_, v___y_2199_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v___x_2209_; 
lean_dec_ref_known(v___x_2208_, 1);
v___x_2209_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v___y_2199_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; lean_object* v_unreported_2211_; lean_object* v___x_2212_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_a_2210_);
lean_dec_ref_known(v___x_2209_, 1);
v_unreported_2211_ = lean_ctor_get(v_a_2210_, 1);
lean_inc_ref(v_unreported_2211_);
lean_dec(v_a_2210_);
v___x_2212_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(v_unreported_2211_, v___x_2205_, v___y_2198_, v___y_2199_);
lean_dec_ref(v_unreported_2211_);
if (lean_obj_tag(v___x_2212_) == 0)
{
size_t v___x_2213_; size_t v___x_2214_; 
lean_dec_ref_known(v___x_2212_, 1);
v___x_2213_ = ((size_t)1ULL);
v___x_2214_ = lean_usize_add(v_i_2196_, v___x_2213_);
v_i_2196_ = v___x_2214_;
v_b_2197_ = v___x_2205_;
goto _start;
}
else
{
return v___x_2212_;
}
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
v_a_2216_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2209_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2209_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
else
{
return v___x_2208_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13___boxed(lean_object* v_as_2224_, lean_object* v_sz_2225_, lean_object* v_i_2226_, lean_object* v_b_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
size_t v_sz_boxed_2231_; size_t v_i_boxed_2232_; lean_object* v_res_2233_; 
v_sz_boxed_2231_ = lean_unbox_usize(v_sz_2225_);
lean_dec(v_sz_2225_);
v_i_boxed_2232_ = lean_unbox_usize(v_i_2226_);
lean_dec(v_i_2226_);
v_res_2233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v_as_2224_, v_sz_boxed_2231_, v_i_boxed_2232_, v_b_2227_, v___y_2228_, v___y_2229_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec_ref(v_as_2224_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object* v_as_2234_, size_t v_i_2235_, size_t v_stop_2236_, lean_object* v_b_2237_){
_start:
{
uint8_t v___x_2238_; 
v___x_2238_ = lean_usize_dec_eq(v_i_2235_, v_stop_2236_);
if (v___x_2238_ == 0)
{
lean_object* v___x_2239_; lean_object* v_name_2240_; lean_object* v___x_2241_; size_t v___x_2242_; size_t v___x_2243_; 
v___x_2239_ = lean_array_uget_borrowed(v_as_2234_, v_i_2235_);
v_name_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_name_2240_);
v___x_2241_ = l_Lean_Compiler_LCNF_setDeclPublic(v_b_2237_, v_name_2240_);
v___x_2242_ = ((size_t)1ULL);
v___x_2243_ = lean_usize_add(v_i_2235_, v___x_2242_);
v_i_2235_ = v___x_2243_;
v_b_2237_ = v___x_2241_;
goto _start;
}
else
{
return v_b_2237_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object* v_as_2245_, lean_object* v_i_2246_, lean_object* v_stop_2247_, lean_object* v_b_2248_){
_start:
{
size_t v_i_boxed_2249_; size_t v_stop_boxed_2250_; lean_object* v_res_2251_; 
v_i_boxed_2249_ = lean_unbox_usize(v_i_2246_);
lean_dec(v_i_2246_);
v_stop_boxed_2250_ = lean_unbox_usize(v_stop_2247_);
lean_dec(v_stop_2247_);
v_res_2251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v_as_2245_, v_i_boxed_2249_, v_stop_boxed_2250_, v_b_2248_);
lean_dec_ref(v_as_2245_);
return v_res_2251_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0(uint8_t v___y_2252_, uint8_t v_suppressElabErrors_2253_, lean_object* v_x_2254_){
_start:
{
if (lean_obj_tag(v_x_2254_) == 1)
{
lean_object* v_pre_2255_; 
v_pre_2255_ = lean_ctor_get(v_x_2254_, 0);
switch(lean_obj_tag(v_pre_2255_))
{
case 1:
{
lean_object* v_pre_2256_; 
v_pre_2256_ = lean_ctor_get(v_pre_2255_, 0);
switch(lean_obj_tag(v_pre_2256_))
{
case 0:
{
lean_object* v_str_2257_; lean_object* v_str_2258_; lean_object* v___x_2259_; uint8_t v___x_2260_; 
v_str_2257_ = lean_ctor_get(v_x_2254_, 1);
v_str_2258_ = lean_ctor_get(v_pre_2255_, 1);
v___x_2259_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0));
v___x_2260_ = lean_string_dec_eq(v_str_2258_, v___x_2259_);
if (v___x_2260_ == 0)
{
lean_object* v___x_2261_; uint8_t v___x_2262_; 
v___x_2261_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1));
v___x_2262_ = lean_string_dec_eq(v_str_2258_, v___x_2261_);
if (v___x_2262_ == 0)
{
return v___y_2252_;
}
else
{
lean_object* v___x_2263_; uint8_t v___x_2264_; 
v___x_2263_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2));
v___x_2264_ = lean_string_dec_eq(v_str_2257_, v___x_2263_);
if (v___x_2264_ == 0)
{
return v___y_2252_;
}
else
{
return v_suppressElabErrors_2253_;
}
}
}
else
{
lean_object* v___x_2265_; uint8_t v___x_2266_; 
v___x_2265_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3));
v___x_2266_ = lean_string_dec_eq(v_str_2257_, v___x_2265_);
if (v___x_2266_ == 0)
{
return v___y_2252_;
}
else
{
return v_suppressElabErrors_2253_;
}
}
}
case 1:
{
lean_object* v_pre_2267_; 
v_pre_2267_ = lean_ctor_get(v_pre_2256_, 0);
if (lean_obj_tag(v_pre_2267_) == 0)
{
lean_object* v_str_2268_; lean_object* v_str_2269_; lean_object* v_str_2270_; lean_object* v___x_2271_; uint8_t v___x_2272_; 
v_str_2268_ = lean_ctor_get(v_x_2254_, 1);
v_str_2269_ = lean_ctor_get(v_pre_2255_, 1);
v_str_2270_ = lean_ctor_get(v_pre_2256_, 1);
v___x_2271_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4));
v___x_2272_ = lean_string_dec_eq(v_str_2270_, v___x_2271_);
if (v___x_2272_ == 0)
{
return v___y_2252_;
}
else
{
lean_object* v___x_2273_; uint8_t v___x_2274_; 
v___x_2273_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5));
v___x_2274_ = lean_string_dec_eq(v_str_2269_, v___x_2273_);
if (v___x_2274_ == 0)
{
return v___y_2252_;
}
else
{
lean_object* v___x_2275_; uint8_t v___x_2276_; 
v___x_2275_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6));
v___x_2276_ = lean_string_dec_eq(v_str_2268_, v___x_2275_);
if (v___x_2276_ == 0)
{
return v___y_2252_;
}
else
{
return v_suppressElabErrors_2253_;
}
}
}
}
else
{
return v___y_2252_;
}
}
default: 
{
return v___y_2252_;
}
}
}
case 0:
{
lean_object* v_str_2277_; lean_object* v___x_2278_; uint8_t v___x_2279_; 
v_str_2277_ = lean_ctor_get(v_x_2254_, 1);
v___x_2278_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_2279_ = lean_string_dec_eq(v_str_2277_, v___x_2278_);
if (v___x_2279_ == 0)
{
return v___y_2252_;
}
else
{
return v_suppressElabErrors_2253_;
}
}
default: 
{
return v___y_2252_;
}
}
}
else
{
return v___y_2252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0___boxed(lean_object* v___y_2280_, lean_object* v_suppressElabErrors_2281_, lean_object* v_x_2282_){
_start:
{
uint8_t v___y_38886__boxed_2283_; uint8_t v_suppressElabErrors_boxed_2284_; uint8_t v_res_2285_; lean_object* v_r_2286_; 
v___y_38886__boxed_2283_ = lean_unbox(v___y_2280_);
v_suppressElabErrors_boxed_2284_ = lean_unbox(v_suppressElabErrors_2281_);
v_res_2285_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0(v___y_38886__boxed_2283_, v_suppressElabErrors_boxed_2284_, v_x_2282_);
lean_dec(v_x_2282_);
v_r_2286_ = lean_box(v_res_2285_);
return v_r_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(lean_object* v_ref_2287_, lean_object* v_msgData_2288_, uint8_t v_severity_2289_, uint8_t v_isSilent_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
uint8_t v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; uint8_t v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v___y_2331_; lean_object* v___y_2332_; uint8_t v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; uint8_t v___y_2336_; uint8_t v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2356_; lean_object* v___y_2357_; uint8_t v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2360_; uint8_t v___y_2361_; uint8_t v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2367_; lean_object* v___y_2368_; uint8_t v___y_2369_; lean_object* v___y_2370_; uint8_t v___y_2371_; lean_object* v___y_2372_; uint8_t v___y_2373_; uint8_t v___x_2378_; lean_object* v___y_2380_; lean_object* v___y_2381_; uint8_t v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; uint8_t v___y_2385_; uint8_t v___y_2386_; uint8_t v___y_2388_; uint8_t v___x_2403_; 
v___x_2378_ = 2;
v___x_2403_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2289_, v___x_2378_);
if (v___x_2403_ == 0)
{
v___y_2388_ = v___x_2403_;
goto v___jp_2387_;
}
else
{
uint8_t v___x_2404_; 
lean_inc_ref(v_msgData_2288_);
v___x_2404_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2288_);
v___y_2388_ = v___x_2404_;
goto v___jp_2387_;
}
v___jp_2294_:
{
lean_object* v___x_2304_; lean_object* v_currNamespace_2305_; lean_object* v_openDecls_2306_; lean_object* v_env_2307_; lean_object* v_nextMacroScope_2308_; lean_object* v_ngen_2309_; lean_object* v_auxDeclNGen_2310_; lean_object* v_traceState_2311_; lean_object* v_cache_2312_; lean_object* v_messages_2313_; lean_object* v_infoState_2314_; lean_object* v_snapshotTasks_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2329_; 
v___x_2304_ = lean_st_ref_take(v___y_2303_);
v_currNamespace_2305_ = lean_ctor_get(v___y_2302_, 6);
v_openDecls_2306_ = lean_ctor_get(v___y_2302_, 7);
v_env_2307_ = lean_ctor_get(v___x_2304_, 0);
v_nextMacroScope_2308_ = lean_ctor_get(v___x_2304_, 1);
v_ngen_2309_ = lean_ctor_get(v___x_2304_, 2);
v_auxDeclNGen_2310_ = lean_ctor_get(v___x_2304_, 3);
v_traceState_2311_ = lean_ctor_get(v___x_2304_, 4);
v_cache_2312_ = lean_ctor_get(v___x_2304_, 5);
v_messages_2313_ = lean_ctor_get(v___x_2304_, 6);
v_infoState_2314_ = lean_ctor_get(v___x_2304_, 7);
v_snapshotTasks_2315_ = lean_ctor_get(v___x_2304_, 8);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2317_ = v___x_2304_;
v_isShared_2318_ = v_isSharedCheck_2329_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_snapshotTasks_2315_);
lean_inc(v_infoState_2314_);
lean_inc(v_messages_2313_);
lean_inc(v_cache_2312_);
lean_inc(v_traceState_2311_);
lean_inc(v_auxDeclNGen_2310_);
lean_inc(v_ngen_2309_);
lean_inc(v_nextMacroScope_2308_);
lean_inc(v_env_2307_);
lean_dec(v___x_2304_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2329_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2324_; 
lean_inc(v_openDecls_2306_);
lean_inc(v_currNamespace_2305_);
v___x_2319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2319_, 0, v_currNamespace_2305_);
lean_ctor_set(v___x_2319_, 1, v_openDecls_2306_);
v___x_2320_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2319_);
lean_ctor_set(v___x_2320_, 1, v___y_2300_);
lean_inc_ref(v___y_2299_);
lean_inc_ref(v___y_2297_);
v___x_2321_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2321_, 0, v___y_2297_);
lean_ctor_set(v___x_2321_, 1, v___y_2298_);
lean_ctor_set(v___x_2321_, 2, v___y_2296_);
lean_ctor_set(v___x_2321_, 3, v___y_2299_);
lean_ctor_set(v___x_2321_, 4, v___x_2320_);
lean_ctor_set_uint8(v___x_2321_, sizeof(void*)*5, v___y_2295_);
lean_ctor_set_uint8(v___x_2321_, sizeof(void*)*5 + 1, v___y_2301_);
lean_ctor_set_uint8(v___x_2321_, sizeof(void*)*5 + 2, v_isSilent_2290_);
v___x_2322_ = l_Lean_MessageLog_add(v___x_2321_, v_messages_2313_);
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 6, v___x_2322_);
v___x_2324_ = v___x_2317_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_env_2307_);
lean_ctor_set(v_reuseFailAlloc_2328_, 1, v_nextMacroScope_2308_);
lean_ctor_set(v_reuseFailAlloc_2328_, 2, v_ngen_2309_);
lean_ctor_set(v_reuseFailAlloc_2328_, 3, v_auxDeclNGen_2310_);
lean_ctor_set(v_reuseFailAlloc_2328_, 4, v_traceState_2311_);
lean_ctor_set(v_reuseFailAlloc_2328_, 5, v_cache_2312_);
lean_ctor_set(v_reuseFailAlloc_2328_, 6, v___x_2322_);
lean_ctor_set(v_reuseFailAlloc_2328_, 7, v_infoState_2314_);
lean_ctor_set(v_reuseFailAlloc_2328_, 8, v_snapshotTasks_2315_);
v___x_2324_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2325_ = lean_st_ref_set(v___y_2303_, v___x_2324_);
v___x_2326_ = lean_box(0);
v___x_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
return v___x_2327_;
}
}
}
v___jp_2330_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2354_; 
v___x_2339_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2288_);
v___x_2340_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v___x_2339_, v___y_2291_, v___y_2292_);
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
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
lean_inc_ref_n(v___y_2332_, 2);
v___x_2345_ = l_Lean_FileMap_toPosition(v___y_2332_, v___y_2335_);
lean_dec(v___y_2335_);
v___x_2346_ = l_Lean_FileMap_toPosition(v___y_2332_, v___y_2338_);
lean_dec(v___y_2338_);
v___x_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2346_);
v___x_2348_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1));
if (v___y_2336_ == 0)
{
lean_del_object(v___x_2343_);
lean_dec_ref(v___y_2331_);
v___y_2295_ = v___y_2333_;
v___y_2296_ = v___x_2347_;
v___y_2297_ = v___y_2334_;
v___y_2298_ = v___x_2345_;
v___y_2299_ = v___x_2348_;
v___y_2300_ = v_a_2341_;
v___y_2301_ = v___y_2337_;
v___y_2302_ = v___y_2291_;
v___y_2303_ = v___y_2292_;
goto v___jp_2294_;
}
else
{
uint8_t v___x_2349_; 
lean_inc(v_a_2341_);
v___x_2349_ = l_Lean_MessageData_hasTag(v___y_2331_, v_a_2341_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2350_; lean_object* v___x_2352_; 
lean_dec_ref_known(v___x_2347_, 1);
lean_dec_ref(v___x_2345_);
lean_dec(v_a_2341_);
v___x_2350_ = lean_box(0);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 0, v___x_2350_);
v___x_2352_ = v___x_2343_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2350_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
else
{
lean_del_object(v___x_2343_);
v___y_2295_ = v___y_2333_;
v___y_2296_ = v___x_2347_;
v___y_2297_ = v___y_2334_;
v___y_2298_ = v___x_2345_;
v___y_2299_ = v___x_2348_;
v___y_2300_ = v_a_2341_;
v___y_2301_ = v___y_2337_;
v___y_2302_ = v___y_2291_;
v___y_2303_ = v___y_2292_;
goto v___jp_2294_;
}
}
}
}
v___jp_2355_:
{
lean_object* v___x_2364_; 
v___x_2364_ = l_Lean_Syntax_getTailPos_x3f(v___y_2360_, v___y_2358_);
lean_dec(v___y_2360_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_inc(v___y_2363_);
v___y_2331_ = v___y_2356_;
v___y_2332_ = v___y_2357_;
v___y_2333_ = v___y_2358_;
v___y_2334_ = v___y_2359_;
v___y_2335_ = v___y_2363_;
v___y_2336_ = v___y_2361_;
v___y_2337_ = v___y_2362_;
v___y_2338_ = v___y_2363_;
goto v___jp_2330_;
}
else
{
lean_object* v_val_2365_; 
v_val_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_val_2365_);
lean_dec_ref_known(v___x_2364_, 1);
v___y_2331_ = v___y_2356_;
v___y_2332_ = v___y_2357_;
v___y_2333_ = v___y_2358_;
v___y_2334_ = v___y_2359_;
v___y_2335_ = v___y_2363_;
v___y_2336_ = v___y_2361_;
v___y_2337_ = v___y_2362_;
v___y_2338_ = v_val_2365_;
goto v___jp_2330_;
}
}
v___jp_2366_:
{
lean_object* v_ref_2374_; lean_object* v___x_2375_; 
v_ref_2374_ = l_Lean_replaceRef(v_ref_2287_, v___y_2372_);
v___x_2375_ = l_Lean_Syntax_getPos_x3f(v_ref_2374_, v___y_2369_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v___x_2376_; 
v___x_2376_ = lean_unsigned_to_nat(0u);
v___y_2356_ = v___y_2367_;
v___y_2357_ = v___y_2368_;
v___y_2358_ = v___y_2369_;
v___y_2359_ = v___y_2370_;
v___y_2360_ = v_ref_2374_;
v___y_2361_ = v___y_2371_;
v___y_2362_ = v___y_2373_;
v___y_2363_ = v___x_2376_;
goto v___jp_2355_;
}
else
{
lean_object* v_val_2377_; 
v_val_2377_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_val_2377_);
lean_dec_ref_known(v___x_2375_, 1);
v___y_2356_ = v___y_2367_;
v___y_2357_ = v___y_2368_;
v___y_2358_ = v___y_2369_;
v___y_2359_ = v___y_2370_;
v___y_2360_ = v_ref_2374_;
v___y_2361_ = v___y_2371_;
v___y_2362_ = v___y_2373_;
v___y_2363_ = v_val_2377_;
goto v___jp_2355_;
}
}
v___jp_2379_:
{
if (v___y_2386_ == 0)
{
v___y_2367_ = v___y_2383_;
v___y_2368_ = v___y_2380_;
v___y_2369_ = v___y_2385_;
v___y_2370_ = v___y_2381_;
v___y_2371_ = v___y_2382_;
v___y_2372_ = v___y_2384_;
v___y_2373_ = v_severity_2289_;
goto v___jp_2366_;
}
else
{
v___y_2367_ = v___y_2383_;
v___y_2368_ = v___y_2380_;
v___y_2369_ = v___y_2385_;
v___y_2370_ = v___y_2381_;
v___y_2371_ = v___y_2382_;
v___y_2372_ = v___y_2384_;
v___y_2373_ = v___x_2378_;
goto v___jp_2366_;
}
}
v___jp_2387_:
{
if (v___y_2388_ == 0)
{
lean_object* v_fileName_2389_; lean_object* v_fileMap_2390_; lean_object* v_options_2391_; lean_object* v_ref_2392_; uint8_t v_suppressElabErrors_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___f_2396_; uint8_t v___x_2397_; uint8_t v___x_2398_; 
v_fileName_2389_ = lean_ctor_get(v___y_2291_, 0);
v_fileMap_2390_ = lean_ctor_get(v___y_2291_, 1);
v_options_2391_ = lean_ctor_get(v___y_2291_, 2);
v_ref_2392_ = lean_ctor_get(v___y_2291_, 5);
v_suppressElabErrors_2393_ = lean_ctor_get_uint8(v___y_2291_, sizeof(void*)*14 + 1);
v___x_2394_ = lean_box(v___y_2388_);
v___x_2395_ = lean_box(v_suppressElabErrors_2393_);
v___f_2396_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2396_, 0, v___x_2394_);
lean_closure_set(v___f_2396_, 1, v___x_2395_);
v___x_2397_ = 1;
v___x_2398_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2289_, v___x_2397_);
if (v___x_2398_ == 0)
{
v___y_2380_ = v_fileMap_2390_;
v___y_2381_ = v_fileName_2389_;
v___y_2382_ = v_suppressElabErrors_2393_;
v___y_2383_ = v___f_2396_;
v___y_2384_ = v_ref_2392_;
v___y_2385_ = v___y_2388_;
v___y_2386_ = v___x_2398_;
goto v___jp_2379_;
}
else
{
lean_object* v___x_2399_; uint8_t v___x_2400_; 
v___x_2399_ = l_Lean_warningAsError;
v___x_2400_ = l_Lean_Option_get___at___00main_spec__8(v_options_2391_, v___x_2399_);
v___y_2380_ = v_fileMap_2390_;
v___y_2381_ = v_fileName_2389_;
v___y_2382_ = v_suppressElabErrors_2393_;
v___y_2383_ = v___f_2396_;
v___y_2384_ = v_ref_2392_;
v___y_2385_ = v___y_2388_;
v___y_2386_ = v___x_2400_;
goto v___jp_2379_;
}
}
else
{
lean_object* v___x_2401_; lean_object* v___x_2402_; 
lean_dec_ref(v_msgData_2288_);
v___x_2401_ = lean_box(0);
v___x_2402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2401_);
return v___x_2402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___boxed(lean_object* v_ref_2405_, lean_object* v_msgData_2406_, lean_object* v_severity_2407_, lean_object* v_isSilent_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
uint8_t v_severity_boxed_2412_; uint8_t v_isSilent_boxed_2413_; lean_object* v_res_2414_; 
v_severity_boxed_2412_ = lean_unbox(v_severity_2407_);
v_isSilent_boxed_2413_ = lean_unbox(v_isSilent_2408_);
v_res_2414_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(v_ref_2405_, v_msgData_2406_, v_severity_boxed_2412_, v_isSilent_boxed_2413_, v___y_2409_, v___y_2410_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v_ref_2405_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(lean_object* v_msgData_2415_, uint8_t v_severity_2416_, uint8_t v_isSilent_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v_ref_2421_; lean_object* v___x_2422_; 
v_ref_2421_ = lean_ctor_get(v___y_2418_, 5);
v___x_2422_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(v_ref_2421_, v_msgData_2415_, v_severity_2416_, v_isSilent_2417_, v___y_2418_, v___y_2419_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30___boxed(lean_object* v_msgData_2423_, lean_object* v_severity_2424_, lean_object* v_isSilent_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
uint8_t v_severity_boxed_2429_; uint8_t v_isSilent_boxed_2430_; lean_object* v_res_2431_; 
v_severity_boxed_2429_ = lean_unbox(v_severity_2424_);
v_isSilent_boxed_2430_ = lean_unbox(v_isSilent_2425_);
v_res_2431_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2423_, v_severity_boxed_2429_, v_isSilent_boxed_2430_, v___y_2426_, v___y_2427_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14(lean_object* v_msgData_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
uint8_t v___x_2436_; uint8_t v___x_2437_; lean_object* v___x_2438_; 
v___x_2436_ = 2;
v___x_2437_ = 0;
v___x_2438_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2432_, v___x_2436_, v___x_2437_, v___y_2433_, v___y_2434_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14___boxed(lean_object* v_msgData_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_Lean_logError___at___00main_spec__14(v_msgData_2439_, v___y_2440_, v___y_2441_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(lean_object* v_x2_2444_, lean_object* v_as_2445_, size_t v_i_2446_, size_t v_stop_2447_, lean_object* v_b_2448_){
_start:
{
uint8_t v___x_2449_; 
v___x_2449_ = lean_usize_dec_eq(v_i_2446_, v_stop_2447_);
if (v___x_2449_ == 0)
{
lean_object* v___x_2450_; lean_object* v___x_2451_; size_t v___x_2452_; size_t v___x_2453_; 
v___x_2450_ = lean_array_uget_borrowed(v_as_2445_, v_i_2446_);
lean_inc_ref(v_x2_2444_);
lean_inc(v___x_2450_);
v___x_2451_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2450_, v_x2_2444_, v_b_2448_);
v___x_2452_ = ((size_t)1ULL);
v___x_2453_ = lean_usize_add(v_i_2446_, v___x_2452_);
v_i_2446_ = v___x_2453_;
v_b_2448_ = v___x_2451_;
goto _start;
}
else
{
lean_dec_ref(v_x2_2444_);
return v_b_2448_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(lean_object* v_x2_2455_, lean_object* v_as_2456_, lean_object* v_i_2457_, lean_object* v_stop_2458_, lean_object* v_b_2459_){
_start:
{
size_t v_i_boxed_2460_; size_t v_stop_boxed_2461_; lean_object* v_res_2462_; 
v_i_boxed_2460_ = lean_unbox_usize(v_i_2457_);
lean_dec(v_i_2457_);
v_stop_boxed_2461_ = lean_unbox_usize(v_stop_2458_);
lean_dec(v_stop_2458_);
v_res_2462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v_x2_2455_, v_as_2456_, v_i_boxed_2460_, v_stop_boxed_2461_, v_b_2459_);
lean_dec_ref(v_as_2456_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object* v_as_2463_, size_t v_i_2464_, size_t v_stop_2465_, lean_object* v_b_2466_){
_start:
{
lean_object* v___y_2468_; uint8_t v___x_2472_; 
v___x_2472_ = lean_usize_dec_eq(v_i_2464_, v_stop_2465_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; lean_object* v_declNames_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; uint8_t v___x_2477_; 
v___x_2473_ = lean_array_uget_borrowed(v_as_2463_, v_i_2464_);
v_declNames_2474_ = lean_ctor_get(v___x_2473_, 0);
v___x_2475_ = lean_unsigned_to_nat(0u);
v___x_2476_ = lean_array_get_size(v_declNames_2474_);
v___x_2477_ = lean_nat_dec_lt(v___x_2475_, v___x_2476_);
if (v___x_2477_ == 0)
{
v___y_2468_ = v_b_2466_;
goto v___jp_2467_;
}
else
{
uint8_t v___x_2478_; 
v___x_2478_ = lean_nat_dec_le(v___x_2476_, v___x_2476_);
if (v___x_2478_ == 0)
{
if (v___x_2477_ == 0)
{
v___y_2468_ = v_b_2466_;
goto v___jp_2467_;
}
else
{
size_t v___x_2479_; size_t v___x_2480_; lean_object* v___x_2481_; 
v___x_2479_ = ((size_t)0ULL);
v___x_2480_ = lean_usize_of_nat(v___x_2476_);
lean_inc(v___x_2473_);
v___x_2481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2473_, v_declNames_2474_, v___x_2479_, v___x_2480_, v_b_2466_);
v___y_2468_ = v___x_2481_;
goto v___jp_2467_;
}
}
else
{
size_t v___x_2482_; size_t v___x_2483_; lean_object* v___x_2484_; 
v___x_2482_ = ((size_t)0ULL);
v___x_2483_ = lean_usize_of_nat(v___x_2476_);
lean_inc(v___x_2473_);
v___x_2484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2473_, v_declNames_2474_, v___x_2482_, v___x_2483_, v_b_2466_);
v___y_2468_ = v___x_2484_;
goto v___jp_2467_;
}
}
}
else
{
return v_b_2466_;
}
v___jp_2467_:
{
size_t v___x_2469_; size_t v___x_2470_; 
v___x_2469_ = ((size_t)1ULL);
v___x_2470_ = lean_usize_add(v_i_2464_, v___x_2469_);
v_i_2464_ = v___x_2470_;
v_b_2466_ = v___y_2468_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object* v_as_2485_, lean_object* v_i_2486_, lean_object* v_stop_2487_, lean_object* v_b_2488_){
_start:
{
size_t v_i_boxed_2489_; size_t v_stop_boxed_2490_; lean_object* v_res_2491_; 
v_i_boxed_2489_ = lean_unbox_usize(v_i_2486_);
lean_dec(v_i_2486_);
v_stop_boxed_2490_ = lean_unbox_usize(v_stop_2487_);
lean_dec(v_stop_2487_);
v_res_2491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v_as_2485_, v_i_boxed_2489_, v_stop_boxed_2490_, v_b_2488_);
lean_dec_ref(v_as_2485_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(lean_object* v_a_2492_, lean_object* v_as_2493_, size_t v_i_2494_, size_t v_stop_2495_, lean_object* v_b_2496_){
_start:
{
lean_object* v___y_2498_; uint8_t v___x_2502_; 
v___x_2502_ = lean_usize_dec_eq(v_i_2494_, v_stop_2495_);
if (v___x_2502_ == 0)
{
lean_object* v___x_2503_; lean_object* v_name_2504_; uint8_t v___x_2505_; 
v___x_2503_ = lean_array_uget_borrowed(v_as_2493_, v_i_2494_);
v_name_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_name_2504_);
lean_inc_ref(v_a_2492_);
v___x_2505_ = l_Lean_isExtern(v_a_2492_, v_name_2504_);
if (v___x_2505_ == 0)
{
v___y_2498_ = v_b_2496_;
goto v___jp_2497_;
}
else
{
lean_object* v___x_2506_; 
lean_inc(v___x_2503_);
v___x_2506_ = lean_array_push(v_b_2496_, v___x_2503_);
v___y_2498_ = v___x_2506_;
goto v___jp_2497_;
}
}
else
{
lean_dec_ref(v_a_2492_);
return v_b_2496_;
}
v___jp_2497_:
{
size_t v___x_2499_; size_t v___x_2500_; 
v___x_2499_ = ((size_t)1ULL);
v___x_2500_ = lean_usize_add(v_i_2494_, v___x_2499_);
v_i_2494_ = v___x_2500_;
v_b_2496_ = v___y_2498_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19___boxed(lean_object* v_a_2507_, lean_object* v_as_2508_, lean_object* v_i_2509_, lean_object* v_stop_2510_, lean_object* v_b_2511_){
_start:
{
size_t v_i_boxed_2512_; size_t v_stop_boxed_2513_; lean_object* v_res_2514_; 
v_i_boxed_2512_ = lean_unbox_usize(v_i_2509_);
lean_dec(v_i_2509_);
v_stop_boxed_2513_ = lean_unbox_usize(v_stop_2510_);
lean_dec(v_stop_2510_);
v_res_2514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_2507_, v_as_2508_, v_i_boxed_2512_, v_stop_boxed_2513_, v_b_2511_);
lean_dec_ref(v_as_2508_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(lean_object* v_as_2515_, size_t v_sz_2516_, size_t v_i_2517_, lean_object* v_b_2518_){
_start:
{
uint8_t v___x_2520_; 
v___x_2520_ = lean_usize_dec_lt(v_i_2517_, v_sz_2516_);
if (v___x_2520_ == 0)
{
lean_object* v___x_2521_; 
v___x_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2521_, 0, v_b_2518_);
return v___x_2521_;
}
else
{
uint8_t v___x_2522_; lean_object* v_a_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
lean_dec_ref(v_b_2518_);
v___x_2522_ = 0;
v_a_2523_ = lean_array_uget_borrowed(v_as_2515_, v_i_2517_);
lean_inc(v_a_2523_);
v___x_2524_ = l_Lean_Message_toString(v_a_2523_, v___x_2522_);
v___x_2525_ = l_IO_eprintln___at___00main_spec__6(v___x_2524_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v___x_2526_; size_t v___x_2527_; size_t v___x_2528_; 
lean_dec_ref_known(v___x_2525_, 1);
v___x_2526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_2527_ = ((size_t)1ULL);
v___x_2528_ = lean_usize_add(v_i_2517_, v___x_2527_);
v_i_2517_ = v___x_2528_;
v_b_2518_ = v___x_2526_;
goto _start;
}
else
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2537_; 
v_a_2530_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2532_ = v___x_2525_;
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2525_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2535_; 
if (v_isShared_2533_ == 0)
{
v___x_2535_ = v___x_2532_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2530_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27___boxed(lean_object* v_as_2538_, lean_object* v_sz_2539_, lean_object* v_i_2540_, lean_object* v_b_2541_, lean_object* v___y_2542_){
_start:
{
size_t v_sz_boxed_2543_; size_t v_i_boxed_2544_; lean_object* v_res_2545_; 
v_sz_boxed_2543_ = lean_unbox_usize(v_sz_2539_);
lean_dec(v_sz_2539_);
v_i_boxed_2544_ = lean_unbox_usize(v_i_2540_);
lean_dec(v_i_2540_);
v_res_2545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2538_, v_sz_boxed_2543_, v_i_boxed_2544_, v_b_2541_);
lean_dec_ref(v_as_2538_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(lean_object* v_as_2546_, size_t v_sz_2547_, size_t v_i_2548_, lean_object* v_b_2549_){
_start:
{
uint8_t v___x_2551_; 
v___x_2551_ = lean_usize_dec_lt(v_i_2548_, v_sz_2547_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2552_; 
v___x_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2552_, 0, v_b_2549_);
return v___x_2552_;
}
else
{
uint8_t v___x_2553_; lean_object* v_a_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
lean_dec_ref(v_b_2549_);
v___x_2553_ = 0;
v_a_2554_ = lean_array_uget_borrowed(v_as_2546_, v_i_2548_);
lean_inc(v_a_2554_);
v___x_2555_ = l_Lean_Message_toString(v_a_2554_, v___x_2553_);
v___x_2556_ = l_IO_eprintln___at___00main_spec__6(v___x_2555_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v___x_2557_; size_t v___x_2558_; size_t v___x_2559_; lean_object* v___x_2560_; 
lean_dec_ref_known(v___x_2556_, 1);
v___x_2557_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_2558_ = ((size_t)1ULL);
v___x_2559_ = lean_usize_add(v_i_2548_, v___x_2558_);
v___x_2560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2546_, v_sz_2547_, v___x_2559_, v___x_2557_);
return v___x_2560_;
}
else
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
v_a_2561_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2563_ = v___x_2556_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2556_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2564_ == 0)
{
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14___boxed(lean_object* v_as_2569_, lean_object* v_sz_2570_, lean_object* v_i_2571_, lean_object* v_b_2572_, lean_object* v___y_2573_){
_start:
{
size_t v_sz_boxed_2574_; size_t v_i_boxed_2575_; lean_object* v_res_2576_; 
v_sz_boxed_2574_ = lean_unbox_usize(v_sz_2570_);
lean_dec(v_sz_2570_);
v_i_boxed_2575_ = lean_unbox_usize(v_i_2571_);
lean_dec(v_i_2571_);
v_res_2576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_as_2569_, v_sz_boxed_2574_, v_i_boxed_2575_, v_b_2572_);
lean_dec_ref(v_as_2569_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(lean_object* v_init_2577_, lean_object* v_n_2578_, lean_object* v_b_2579_){
_start:
{
if (lean_obj_tag(v_n_2578_) == 0)
{
lean_object* v_cs_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; size_t v_sz_2584_; size_t v___x_2585_; lean_object* v___x_2586_; 
v_cs_2581_ = lean_ctor_get(v_n_2578_, 0);
v___x_2582_ = lean_box(0);
v___x_2583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2582_);
lean_ctor_set(v___x_2583_, 1, v_b_2579_);
v_sz_2584_ = lean_array_size(v_cs_2581_);
v___x_2585_ = ((size_t)0ULL);
v___x_2586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2577_, v_cs_2581_, v_sz_2584_, v___x_2585_, v___x_2583_);
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
v_vs_2610_ = lean_ctor_get(v_n_2578_, 0);
v___x_2611_ = lean_box(0);
v___x_2612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
lean_ctor_set(v___x_2612_, 1, v_b_2579_);
v_sz_2613_ = lean_array_size(v_vs_2610_);
v___x_2614_ = ((size_t)0ULL);
v___x_2615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_vs_2610_, v_sz_2613_, v___x_2614_, v___x_2612_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(lean_object* v_init_2639_, lean_object* v_as_2640_, size_t v_sz_2641_, size_t v_i_2642_, lean_object* v_b_2643_){
_start:
{
uint8_t v___x_2645_; 
v___x_2645_ = lean_usize_dec_lt(v_i_2642_, v_sz_2641_);
if (v___x_2645_ == 0)
{
lean_object* v___x_2646_; 
v___x_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2646_, 0, v_b_2643_);
return v___x_2646_;
}
else
{
lean_object* v_snd_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2681_; 
v_snd_2647_ = lean_ctor_get(v_b_2643_, 1);
v_isSharedCheck_2681_ = !lean_is_exclusive(v_b_2643_);
if (v_isSharedCheck_2681_ == 0)
{
lean_object* v_unused_2682_; 
v_unused_2682_ = lean_ctor_get(v_b_2643_, 0);
lean_dec(v_unused_2682_);
v___x_2649_ = v_b_2643_;
v_isShared_2650_ = v_isSharedCheck_2681_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_snd_2647_);
lean_dec(v_b_2643_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2681_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v_a_2651_; lean_object* v___x_2652_; 
v_a_2651_ = lean_array_uget_borrowed(v_as_2640_, v_i_2642_);
lean_inc(v_snd_2647_);
v___x_2652_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2639_, v_a_2651_, v_snd_2647_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2672_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2655_ = v___x_2652_;
v_isShared_2656_ = v_isSharedCheck_2672_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2652_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2672_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
if (lean_obj_tag(v_a_2653_) == 0)
{
lean_object* v___x_2657_; lean_object* v___x_2659_; 
v___x_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2657_, 0, v_a_2653_);
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 0, v___x_2657_);
v___x_2659_ = v___x_2649_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2657_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v_snd_2647_);
v___x_2659_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
lean_object* v___x_2661_; 
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 0, v___x_2659_);
v___x_2661_ = v___x_2655_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2659_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
else
{
lean_object* v_a_2664_; lean_object* v___x_2665_; lean_object* v___x_2667_; 
lean_del_object(v___x_2655_);
lean_dec(v_snd_2647_);
v_a_2664_ = lean_ctor_get(v_a_2653_, 0);
lean_inc(v_a_2664_);
lean_dec_ref_known(v_a_2653_, 1);
v___x_2665_ = lean_box(0);
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 1, v_a_2664_);
lean_ctor_set(v___x_2649_, 0, v___x_2665_);
v___x_2667_ = v___x_2649_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2665_);
lean_ctor_set(v_reuseFailAlloc_2671_, 1, v_a_2664_);
v___x_2667_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
size_t v___x_2668_; size_t v___x_2669_; 
v___x_2668_ = ((size_t)1ULL);
v___x_2669_ = lean_usize_add(v_i_2642_, v___x_2668_);
v_i_2642_ = v___x_2669_;
v_b_2643_ = v___x_2667_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2680_; 
lean_del_object(v___x_2649_);
lean_dec(v_snd_2647_);
v_a_2673_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2675_ = v___x_2652_;
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2652_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2678_; 
if (v_isShared_2676_ == 0)
{
v___x_2678_ = v___x_2675_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2673_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13___boxed(lean_object* v_init_2683_, lean_object* v_as_2684_, lean_object* v_sz_2685_, lean_object* v_i_2686_, lean_object* v_b_2687_, lean_object* v___y_2688_){
_start:
{
size_t v_sz_boxed_2689_; size_t v_i_boxed_2690_; lean_object* v_res_2691_; 
v_sz_boxed_2689_ = lean_unbox_usize(v_sz_2685_);
lean_dec(v_sz_2685_);
v_i_boxed_2690_ = lean_unbox_usize(v_i_2686_);
lean_dec(v_i_2686_);
v_res_2691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2683_, v_as_2684_, v_sz_boxed_2689_, v_i_boxed_2690_, v_b_2687_);
lean_dec_ref(v_as_2684_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10___boxed(lean_object* v_init_2692_, lean_object* v_n_2693_, lean_object* v_b_2694_, lean_object* v___y_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2692_, v_n_2693_, v_b_2694_);
lean_dec_ref(v_n_2693_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(lean_object* v_as_2697_, size_t v_sz_2698_, size_t v_i_2699_, lean_object* v_b_2700_){
_start:
{
uint8_t v___x_2702_; 
v___x_2702_ = lean_usize_dec_lt(v_i_2699_, v_sz_2698_);
if (v___x_2702_ == 0)
{
lean_object* v___x_2703_; 
v___x_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2703_, 0, v_b_2700_);
return v___x_2703_;
}
else
{
uint8_t v___x_2704_; lean_object* v_a_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
lean_dec_ref(v_b_2700_);
v___x_2704_ = 0;
v_a_2705_ = lean_array_uget_borrowed(v_as_2697_, v_i_2699_);
lean_inc(v_a_2705_);
v___x_2706_ = l_Lean_Message_toString(v_a_2705_, v___x_2704_);
v___x_2707_ = l_IO_eprintln___at___00main_spec__6(v___x_2706_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v___x_2708_; size_t v___x_2709_; size_t v___x_2710_; 
lean_dec_ref_known(v___x_2707_, 1);
v___x_2708_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_2709_ = ((size_t)1ULL);
v___x_2710_ = lean_usize_add(v_i_2699_, v___x_2709_);
v_i_2699_ = v___x_2710_;
v_b_2700_ = v___x_2708_;
goto _start;
}
else
{
lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2719_; 
v_a_2712_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2714_ = v___x_2707_;
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2707_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2717_; 
if (v_isShared_2715_ == 0)
{
v___x_2717_ = v___x_2714_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_a_2712_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16___boxed(lean_object* v_as_2720_, lean_object* v_sz_2721_, lean_object* v_i_2722_, lean_object* v_b_2723_, lean_object* v___y_2724_){
_start:
{
size_t v_sz_boxed_2725_; size_t v_i_boxed_2726_; lean_object* v_res_2727_; 
v_sz_boxed_2725_ = lean_unbox_usize(v_sz_2721_);
lean_dec(v_sz_2721_);
v_i_boxed_2726_ = lean_unbox_usize(v_i_2722_);
lean_dec(v_i_2722_);
v_res_2727_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2720_, v_sz_boxed_2725_, v_i_boxed_2726_, v_b_2723_);
lean_dec_ref(v_as_2720_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(lean_object* v_as_2728_, size_t v_sz_2729_, size_t v_i_2730_, lean_object* v_b_2731_){
_start:
{
uint8_t v___x_2733_; 
v___x_2733_ = lean_usize_dec_lt(v_i_2730_, v_sz_2729_);
if (v___x_2733_ == 0)
{
lean_object* v___x_2734_; 
v___x_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2734_, 0, v_b_2731_);
return v___x_2734_;
}
else
{
uint8_t v___x_2735_; lean_object* v_a_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
lean_dec_ref(v_b_2731_);
v___x_2735_ = 0;
v_a_2736_ = lean_array_uget_borrowed(v_as_2728_, v_i_2730_);
lean_inc(v_a_2736_);
v___x_2737_ = l_Lean_Message_toString(v_a_2736_, v___x_2735_);
v___x_2738_ = l_IO_eprintln___at___00main_spec__6(v___x_2737_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v___x_2739_; size_t v___x_2740_; size_t v___x_2741_; lean_object* v___x_2742_; 
lean_dec_ref_known(v___x_2738_, 1);
v___x_2739_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_2740_ = ((size_t)1ULL);
v___x_2741_ = lean_usize_add(v_i_2730_, v___x_2740_);
v___x_2742_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2728_, v_sz_2729_, v___x_2741_, v___x_2739_);
return v___x_2742_;
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
v_a_2743_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2738_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2738_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11___boxed(lean_object* v_as_2751_, lean_object* v_sz_2752_, lean_object* v_i_2753_, lean_object* v_b_2754_, lean_object* v___y_2755_){
_start:
{
size_t v_sz_boxed_2756_; size_t v_i_boxed_2757_; lean_object* v_res_2758_; 
v_sz_boxed_2756_ = lean_unbox_usize(v_sz_2752_);
lean_dec(v_sz_2752_);
v_i_boxed_2757_ = lean_unbox_usize(v_i_2753_);
lean_dec(v_i_2753_);
v_res_2758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_as_2751_, v_sz_boxed_2756_, v_i_boxed_2757_, v_b_2754_);
lean_dec_ref(v_as_2751_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7(lean_object* v_t_2759_, lean_object* v_init_2760_){
_start:
{
lean_object* v_root_2762_; lean_object* v_tail_2763_; lean_object* v___x_2764_; 
v_root_2762_ = lean_ctor_get(v_t_2759_, 0);
v_tail_2763_ = lean_ctor_get(v_t_2759_, 1);
v___x_2764_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2760_, v_root_2762_, v_init_2760_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2801_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2767_ = v___x_2764_;
v_isShared_2768_ = v_isSharedCheck_2801_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2764_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2801_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
if (lean_obj_tag(v_a_2765_) == 0)
{
lean_object* v_a_2769_; lean_object* v___x_2771_; 
v_a_2769_ = lean_ctor_get(v_a_2765_, 0);
lean_inc(v_a_2769_);
lean_dec_ref_known(v_a_2765_, 1);
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 0, v_a_2769_);
v___x_2771_ = v___x_2767_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2769_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
else
{
lean_object* v_a_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; size_t v_sz_2776_; size_t v___x_2777_; lean_object* v___x_2778_; 
lean_del_object(v___x_2767_);
v_a_2773_ = lean_ctor_get(v_a_2765_, 0);
lean_inc(v_a_2773_);
lean_dec_ref_known(v_a_2765_, 1);
v___x_2774_ = lean_box(0);
v___x_2775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2774_);
lean_ctor_set(v___x_2775_, 1, v_a_2773_);
v_sz_2776_ = lean_array_size(v_tail_2763_);
v___x_2777_ = ((size_t)0ULL);
v___x_2778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_tail_2763_, v_sz_2776_, v___x_2777_, v___x_2775_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2792_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2781_ = v___x_2778_;
v_isShared_2782_ = v_isSharedCheck_2792_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2792_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v_fst_2783_; 
v_fst_2783_ = lean_ctor_get(v_a_2779_, 0);
if (lean_obj_tag(v_fst_2783_) == 0)
{
lean_object* v_snd_2784_; lean_object* v___x_2786_; 
v_snd_2784_ = lean_ctor_get(v_a_2779_, 1);
lean_inc(v_snd_2784_);
lean_dec(v_a_2779_);
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v_snd_2784_);
v___x_2786_ = v___x_2781_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_snd_2784_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
else
{
lean_object* v_val_2788_; lean_object* v___x_2790_; 
lean_inc_ref(v_fst_2783_);
lean_dec(v_a_2779_);
v_val_2788_ = lean_ctor_get(v_fst_2783_, 0);
lean_inc(v_val_2788_);
lean_dec_ref_known(v_fst_2783_, 1);
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v_val_2788_);
v___x_2790_ = v___x_2781_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_val_2788_);
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
else
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
v_a_2793_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___x_2778_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2778_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
}
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
v_a_2802_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2764_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2764_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7___boxed(lean_object* v_t_2810_, lean_object* v_init_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_t_2810_, v_init_2811_);
lean_dec_ref(v_t_2810_);
return v_res_2813_;
}
}
static lean_object* _init_l_main___closed__3(void){
_start:
{
lean_object* v___x_2817_; 
v___x_2817_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_box(0), lean_box(0), lean_box(0));
return v___x_2817_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2818_ = l_Lean_instInhabitedClassState_default;
v___x_2819_ = lean_box(0);
v___x_2820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2819_);
lean_ctor_set(v___x_2820_, 1, v___x_2818_);
return v___x_2820_;
}
}
static lean_object* _init_l_main___closed__5(void){
_start:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2821_ = l_Lean_Meta_Match_Extension_instInhabitedState;
v___x_2822_ = lean_box(0);
v___x_2823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2822_);
lean_ctor_set(v___x_2823_, 1, v___x_2821_);
return v___x_2823_;
}
}
static lean_object* _init_l_main___closed__6(void){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2824_ = ((lean_object*)(l_main___closed__2));
v___x_2825_ = ((lean_object*)(l_main___closed__1));
v___x_2826_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_2825_, v___x_2824_);
return v___x_2826_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2827_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2828_ = lean_box(0);
v___x_2829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
lean_ctor_set(v___x_2829_, 1, v___x_2827_);
return v___x_2829_;
}
}
static lean_object* _init_l_main___closed__8(void){
_start:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2830_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_2831_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2830_);
return v___x_2831_;
}
}
static lean_object* _init_l_main___closed__9(void){
_start:
{
lean_object* v___x_2832_; 
v___x_2832_ = l_Array_instInhabited(lean_box(0));
return v___x_2832_;
}
}
static lean_object* _init_l_main___closed__14(void){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = l_Lean_Options_empty;
v___x_2841_ = l_Lean_Core_getMaxHeartbeats(v___x_2840_);
return v___x_2841_;
}
}
static lean_object* _init_l_main___closed__19(void){
_start:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2846_ = ((lean_object*)(l_main___closed__18));
v___x_2847_ = lean_unsigned_to_nat(27u);
v___x_2848_ = lean_unsigned_to_nat(143u);
v___x_2849_ = ((lean_object*)(l_main___closed__17));
v___x_2850_ = ((lean_object*)(l_main___closed__16));
v___x_2851_ = l_mkPanicMessageWithDecl(v___x_2850_, v___x_2849_, v___x_2848_, v___x_2847_, v___x_2846_);
return v___x_2851_;
}
}
static lean_object* _init_l_main___closed__21(void){
_start:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2853_ = ((lean_object*)(l_main___closed__18));
v___x_2854_ = lean_unsigned_to_nat(51u);
v___x_2855_ = lean_unsigned_to_nat(116u);
v___x_2856_ = ((lean_object*)(l_main___closed__17));
v___x_2857_ = ((lean_object*)(l_main___closed__16));
v___x_2858_ = l_mkPanicMessageWithDecl(v___x_2857_, v___x_2856_, v___x_2855_, v___x_2854_, v___x_2853_);
return v___x_2858_;
}
}
static lean_object* _init_l_main___closed__22(void){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2859_ = lean_unsigned_to_nat(1u);
v___x_2860_ = l_Lean_firstFrontendMacroScope;
v___x_2861_ = lean_nat_add(v___x_2860_, v___x_2859_);
return v___x_2861_;
}
}
static lean_object* _init_l_main___closed__26(void){
_start:
{
lean_object* v___x_2868_; uint64_t v___x_2869_; lean_object* v___x_2870_; 
v___x_2868_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2869_ = 0ULL;
v___x_2870_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2870_, 0, v___x_2868_);
lean_ctor_set_uint64(v___x_2870_, sizeof(void*)*1, v___x_2869_);
return v___x_2870_;
}
}
static lean_object* _init_l_main___closed__27(void){
_start:
{
lean_object* v___x_2871_; 
v___x_2871_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2871_;
}
}
static lean_object* _init_l_main___closed__28(void){
_start:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2872_ = lean_obj_once(&l_main___closed__27, &l_main___closed__27_once, _init_l_main___closed__27);
v___x_2873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2872_);
return v___x_2873_;
}
}
static lean_object* _init_l_main___closed__29(void){
_start:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2874_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_2875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2874_);
lean_ctor_set(v___x_2875_, 1, v___x_2874_);
return v___x_2875_;
}
}
static lean_object* _init_l_main___closed__30(void){
_start:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2876_ = l_Lean_NameSet_empty;
v___x_2877_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2878_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2877_);
lean_ctor_set(v___x_2878_, 1, v___x_2877_);
lean_ctor_set(v___x_2878_, 2, v___x_2876_);
return v___x_2878_;
}
}
static lean_object* _init_l_main___closed__31(void){
_start:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; uint8_t v___x_2881_; lean_object* v___x_2882_; 
v___x_2879_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2880_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_2881_ = 1;
v___x_2882_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2882_, 0, v___x_2880_);
lean_ctor_set(v___x_2882_, 1, v___x_2880_);
lean_ctor_set(v___x_2882_, 2, v___x_2879_);
lean_ctor_set_uint8(v___x_2882_, sizeof(void*)*3, v___x_2881_);
return v___x_2882_;
}
}
static uint8_t _init_l_main___closed__36(void){
_start:
{
uint8_t v___x_2889_; uint8_t v___x_2890_; 
v___x_2889_ = 2;
v___x_2890_ = l_Lean_instOrdOLeanLevel_ord(v___x_2889_, v___x_2889_);
return v___x_2890_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_2891_; lean_object* v___x_2892_; 
v___x_2891_ = 1;
v___x_2892_ = lean_box_uint32(v___x_2891_);
return v___x_2892_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_2893_; lean_object* v___x_2894_; 
v___x_2893_ = 0;
v___x_2894_ = lean_box_uint32(v___x_2893_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_2895_){
_start:
{
if (lean_obj_tag(v_args_2895_) == 1)
{
lean_object* v_tail_2920_; 
v_tail_2920_ = lean_ctor_get(v_args_2895_, 1);
lean_inc(v_tail_2920_);
if (lean_obj_tag(v_tail_2920_) == 1)
{
lean_object* v_tail_2921_; 
v_tail_2921_ = lean_ctor_get(v_tail_2920_, 1);
lean_inc(v_tail_2921_);
if (lean_obj_tag(v_tail_2921_) == 1)
{
lean_object* v_head_2922_; lean_object* v_head_2923_; lean_object* v_head_2924_; lean_object* v_tail_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_3548_; 
v_head_2922_ = lean_ctor_get(v_args_2895_, 0);
lean_inc(v_head_2922_);
lean_dec_ref_known(v_args_2895_, 2);
v_head_2923_ = lean_ctor_get(v_tail_2920_, 0);
lean_inc(v_head_2923_);
lean_dec_ref_known(v_tail_2920_, 2);
v_head_2924_ = lean_ctor_get(v_tail_2921_, 0);
v_tail_2925_ = lean_ctor_get(v_tail_2921_, 1);
v_isSharedCheck_3548_ = !lean_is_exclusive(v_tail_2921_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_2927_ = v_tail_2921_;
v_isShared_2928_ = v_isSharedCheck_3548_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_tail_2925_);
lean_inc(v_head_2924_);
lean_dec(v_tail_2921_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_3548_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Lean_ModuleSetup_load(v_head_2922_);
lean_dec(v_head_2922_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v_a_2930_; lean_object* v_name_2931_; lean_object* v_options_2932_; uint8_t v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2937_; 
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_a_2930_);
lean_dec_ref_known(v___x_2929_, 1);
v_name_2931_ = lean_ctor_get(v_a_2930_, 0);
lean_inc(v_name_2931_);
v_options_2932_ = lean_ctor_get(v_a_2930_, 6);
lean_inc(v_options_2932_);
lean_dec(v_a_2930_);
v___x_2933_ = 0;
v___x_2934_ = l_Lean_LeanOptions_toOptions(v_options_2932_);
v___x_2935_ = lean_box(v___x_2933_);
if (v_isShared_2928_ == 0)
{
lean_ctor_set_tag(v___x_2927_, 0);
lean_ctor_set(v___x_2927_, 1, v___x_2934_);
lean_ctor_set(v___x_2927_, 0, v___x_2935_);
v___x_2937_ = v___x_2927_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_2935_);
lean_ctor_set(v_reuseFailAlloc_3539_, 1, v___x_2934_);
v___x_2937_ = v_reuseFailAlloc_3539_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
lean_object* v___x_2938_; 
v___x_2938_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_tail_2925_, v___x_2937_);
lean_dec(v_tail_2925_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v___x_2940_; 
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2939_);
lean_dec_ref_known(v___x_2938_, 1);
v___x_2940_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_a_2941_);
lean_dec_ref_known(v___x_2940_, 1);
v___x_2942_ = lean_box(0);
v___x_2943_ = l_Lean_initSearchPath(v_a_2941_, v___x_2942_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_fst_2944_; lean_object* v_snd_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_3514_; 
lean_dec_ref_known(v___x_2943_, 1);
v_fst_2944_ = lean_ctor_get(v_a_2939_, 0);
v_snd_2945_ = lean_ctor_get(v_a_2939_, 1);
v_isSharedCheck_3514_ = !lean_is_exclusive(v_a_2939_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_2947_ = v_a_2939_;
v_isShared_2948_ = v_isSharedCheck_3514_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_snd_2945_);
lean_inc(v_fst_2944_);
lean_dec(v_a_2939_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_3514_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; uint8_t v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; uint8_t v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; uint8_t v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v_nextMacroScope_3115_; lean_object* v_ngen_3116_; lean_object* v_auxDeclNGen_3117_; lean_object* v_traceState_3118_; lean_object* v_messages_3119_; lean_object* v_infoState_3120_; lean_object* v_snapshotTasks_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; uint8_t v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; uint8_t v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; uint8_t v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; uint8_t v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; uint8_t v___y_3232_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; uint8_t v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; uint8_t v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; uint8_t v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; uint8_t v___y_3404_; lean_object* v___y_3405_; lean_object* v___x_3415_; lean_object* v___x_3416_; uint8_t v___x_3417_; uint8_t v___y_3419_; uint8_t v___x_3513_; 
v___x_2949_ = lean_obj_once(&l_main___closed__3, &l_main___closed__3_once, _init_l_main___closed__3);
v___x_2950_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2951_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_2952_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2953_ = lean_obj_once(&l_main___closed__8, &l_main___closed__8_once, _init_l_main___closed__8);
v___x_2954_ = lean_obj_once(&l_main___closed__9, &l_main___closed__9_once, _init_l_main___closed__9);
v___x_2955_ = lean_box(1);
v___x_2956_ = ((lean_object*)(l_main___closed__10));
v___x_2957_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_2958_ = 1;
v___x_2959_ = l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(v_snd_2945_, v___x_2957_, v___x_2958_);
v___x_2960_ = l_Lean_maxHeartbeats;
v___x_2961_ = lean_unsigned_to_nat(0u);
v___x_2962_ = l_Lean_Option_set___at___00main_spec__3(v___x_2959_, v___x_2960_, v___x_2961_);
v___x_3252_ = ((lean_object*)(l_main___closed__20));
lean_inc(v_name_2931_);
v___x_3253_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3253_, 0, v_name_2931_);
lean_ctor_set_uint8(v___x_3253_, sizeof(void*)*1, v___x_2958_);
lean_ctor_set_uint8(v___x_3253_, sizeof(void*)*1 + 1, v___x_2958_);
lean_ctor_set_uint8(v___x_3253_, sizeof(void*)*1 + 2, v___x_2958_);
v___x_3254_ = lean_unsigned_to_nat(1u);
v___x_3415_ = lean_mk_empty_array_with_capacity(v___x_3254_);
v___x_3416_ = lean_array_push(v___x_3415_, v___x_3253_);
v___x_3417_ = 2;
v___x_3513_ = lean_uint8_once(&l_main___closed__36, &l_main___closed__36_once, _init_l_main___closed__36);
if (v___x_3513_ == 0)
{
v___y_3419_ = v___x_2958_;
goto v___jp_3418_;
}
else
{
v___y_3419_ = v___x_2933_;
goto v___jp_3418_;
}
v___jp_2963_:
{
lean_object* v___x_2983_; lean_object* v_messages_2984_; lean_object* v_env_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_3086_; 
v___x_2983_ = lean_st_ref_get(v___y_2979_);
lean_dec(v___y_2979_);
v_messages_2984_ = lean_ctor_get(v___x_2983_, 6);
v_env_2985_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3086_ == 0)
{
lean_object* v_unused_3087_; lean_object* v_unused_3088_; lean_object* v_unused_3089_; lean_object* v_unused_3090_; lean_object* v_unused_3091_; lean_object* v_unused_3092_; lean_object* v_unused_3093_; 
v_unused_3087_ = lean_ctor_get(v___x_2983_, 8);
lean_dec(v_unused_3087_);
v_unused_3088_ = lean_ctor_get(v___x_2983_, 7);
lean_dec(v_unused_3088_);
v_unused_3089_ = lean_ctor_get(v___x_2983_, 5);
lean_dec(v_unused_3089_);
v_unused_3090_ = lean_ctor_get(v___x_2983_, 4);
lean_dec(v_unused_3090_);
v_unused_3091_ = lean_ctor_get(v___x_2983_, 3);
lean_dec(v_unused_3091_);
v_unused_3092_ = lean_ctor_get(v___x_2983_, 2);
lean_dec(v_unused_3092_);
v_unused_3093_ = lean_ctor_get(v___x_2983_, 1);
lean_dec(v_unused_3093_);
v___x_2987_ = v___x_2983_;
v_isShared_2988_ = v_isSharedCheck_3086_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_messages_2984_);
lean_inc(v_env_2985_);
lean_dec(v___x_2983_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_3086_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v_unreported_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
v_unreported_2989_ = lean_ctor_get(v_messages_2984_, 1);
v___x_2990_ = lean_box(0);
v___x_2991_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_unreported_2989_, v___x_2990_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3076_; 
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3076_ == 0)
{
lean_object* v_unused_3077_; 
v_unused_3077_ = lean_ctor_get(v___x_2991_, 0);
lean_dec(v_unused_3077_);
v___x_2993_ = v___x_2991_;
v_isShared_2994_ = v_isSharedCheck_3076_;
goto v_resetjp_2992_;
}
else
{
lean_dec(v___x_2991_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3076_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
uint8_t v___x_2995_; 
v___x_2995_ = l_Lean_MessageLog_hasErrors(v_messages_2984_);
lean_dec_ref(v_messages_2984_);
if (v___x_2995_ == 0)
{
lean_object* v___x_2996_; 
lean_del_object(v___x_2993_);
lean_inc_ref(v_env_2985_);
v___x_2996_ = l___private_LeanIR_0__mkIRData(v_env_2985_);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_object* v_a_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_a_2997_);
lean_dec_ref_known(v___x_2996_, 1);
v___x_2998_ = l_Lean_Environment_mainModule(v_env_2985_);
v___x_2999_ = ((lean_object*)(l_main___closed__12));
v___x_3000_ = l_Lean_Name_append(v___x_2998_, v___x_2999_);
v___x_3001_ = l_Lean_saveModuleData(v_head_2923_, v___x_3000_, v_a_2997_);
lean_dec(v_a_2997_);
lean_dec(v___x_3000_);
if (lean_obj_tag(v___x_3001_) == 0)
{
uint8_t v___x_3002_; lean_object* v___x_3003_; 
lean_dec_ref_known(v___x_3001_, 1);
v___x_3002_ = 1;
v___x_3003_ = lean_io_prim_handle_mk(v_head_2924_, v___x_3002_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3009_; 
lean_dec(v_head_2924_);
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref_known(v___x_3003_, 1);
v___x_3005_ = ((lean_object*)(l_main___closed__13));
v___x_3006_ = l_Lean_Options_empty;
v___x_3007_ = lean_obj_once(&l_main___closed__14, &l_main___closed__14_once, _init_l_main___closed__14);
lean_inc_ref(v___y_2974_);
lean_inc_ref(v___y_2976_);
lean_inc_ref(v___y_2980_);
lean_inc_ref(v___y_2982_);
lean_inc_ref(v___y_2981_);
lean_inc_ref(v___y_2977_);
lean_inc(v___y_2973_);
lean_inc_ref(v_env_2985_);
if (v_isShared_2988_ == 0)
{
lean_ctor_set(v___x_2987_, 8, v___y_2974_);
lean_ctor_set(v___x_2987_, 7, v___y_2976_);
lean_ctor_set(v___x_2987_, 6, v___y_2980_);
lean_ctor_set(v___x_2987_, 5, v___y_2982_);
lean_ctor_set(v___x_2987_, 4, v___y_2981_);
lean_ctor_set(v___x_2987_, 3, v___y_2978_);
lean_ctor_set(v___x_2987_, 2, v___y_2977_);
lean_ctor_set(v___x_2987_, 1, v___y_2973_);
v___x_3009_ = v___x_2987_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_env_2985_);
lean_ctor_set(v_reuseFailAlloc_3033_, 1, v___y_2973_);
lean_ctor_set(v_reuseFailAlloc_3033_, 2, v___y_2977_);
lean_ctor_set(v_reuseFailAlloc_3033_, 3, v___y_2978_);
lean_ctor_set(v_reuseFailAlloc_3033_, 4, v___y_2981_);
lean_ctor_set(v_reuseFailAlloc_3033_, 5, v___y_2982_);
lean_ctor_set(v_reuseFailAlloc_3033_, 6, v___y_2980_);
lean_ctor_set(v_reuseFailAlloc_3033_, 7, v___y_2976_);
lean_ctor_set(v_reuseFailAlloc_3033_, 8, v___y_2974_);
v___x_3009_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___f_3012_; lean_object* v___x_3013_; 
v___x_3010_ = lean_box(v___x_2933_);
v___x_3011_ = lean_box(v___y_2967_);
lean_inc(v___y_2968_);
lean_inc(v___y_2969_);
lean_inc(v___y_2965_);
lean_inc_ref(v___y_2966_);
lean_inc_ref(v___y_2972_);
lean_inc(v___y_2971_);
v___f_3012_ = lean_alloc_closure((void*)(l_main___lam__1___boxed), 18, 17);
lean_closure_set(v___f_3012_, 0, v___x_3009_);
lean_closure_set(v___f_3012_, 1, v___y_2971_);
lean_closure_set(v___f_3012_, 2, v___x_3006_);
lean_closure_set(v___f_3012_, 3, v_name_2931_);
lean_closure_set(v___f_3012_, 4, v_a_3004_);
lean_closure_set(v___f_3012_, 5, v___y_2972_);
lean_closure_set(v___f_3012_, 6, v_head_2923_);
lean_closure_set(v___f_3012_, 7, v___y_2966_);
lean_closure_set(v___f_3012_, 8, v___x_2961_);
lean_closure_set(v___f_3012_, 9, v___y_2965_);
lean_closure_set(v___f_3012_, 10, v___y_2964_);
lean_closure_set(v___f_3012_, 11, v___y_2970_);
lean_closure_set(v___f_3012_, 12, v___x_3007_);
lean_closure_set(v___f_3012_, 13, v___y_2969_);
lean_closure_set(v___f_3012_, 14, v___y_2968_);
lean_closure_set(v___f_3012_, 15, v___x_3010_);
lean_closure_set(v___f_3012_, 16, v___x_3011_);
v___x_3013_ = l_Lean_profileitIOUnsafe___redArg(v___x_3005_, v___x_2962_, v___f_3012_, v___y_2975_);
lean_dec_ref(v___x_2962_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v___x_3014_; uint8_t v___x_3015_; 
lean_dec_ref_known(v___x_3013_, 1);
v___x_3014_ = lean_display_cumulative_profiling_times();
v___x_3015_ = lean_unbox(v_fst_2944_);
lean_dec(v_fst_2944_);
if (v___x_3015_ == 0)
{
lean_dec_ref(v_env_2985_);
goto v___jp_2917_;
}
else
{
lean_object* v___x_3016_; 
v___x_3016_ = l_Lean_Environment_displayStats(v_env_2985_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_dec_ref_known(v___x_3016_, 1);
goto v___jp_2917_;
}
else
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3024_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3019_ = v___x_3016_;
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_3016_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3022_; 
if (v_isShared_3020_ == 0)
{
v___x_3022_ = v___x_3019_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_a_3017_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
}
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
lean_dec_ref(v_env_2985_);
lean_dec(v_fst_2944_);
v_a_3025_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_3013_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_3013_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3028_ == 0)
{
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3025_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
}
else
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
lean_dec_ref_known(v___x_3003_, 1);
lean_del_object(v___x_2987_);
lean_dec_ref(v_env_2985_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2975_);
lean_dec(v___y_2970_);
lean_dec(v___y_2964_);
lean_dec_ref(v___x_2962_);
lean_dec(v_fst_2944_);
lean_dec(v_name_2931_);
lean_dec(v_head_2923_);
v___x_3034_ = ((lean_object*)(l_main___closed__15));
v___x_3035_ = lean_string_append(v___x_3034_, v_head_2924_);
lean_dec(v_head_2924_);
v___x_3036_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__1));
v___x_3037_ = lean_string_append(v___x_3035_, v___x_3036_);
v___x_3038_ = l_IO_eprintln___at___00main_spec__6(v___x_3037_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3046_; 
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3046_ == 0)
{
lean_object* v_unused_3047_; 
v_unused_3047_ = lean_ctor_get(v___x_3038_, 0);
lean_dec(v_unused_3047_);
v___x_3040_ = v___x_3038_;
v_isShared_3041_ = v_isSharedCheck_3046_;
goto v_resetjp_3039_;
}
else
{
lean_dec(v___x_3038_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3046_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3042_; lean_object* v___x_3044_; 
v___x_3042_ = l_main___boxed__const__1;
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 0, v___x_3042_);
v___x_3044_ = v___x_3040_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___x_3042_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
}
else
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3055_; 
v_a_3048_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3050_ = v___x_3038_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_3038_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3053_; 
if (v_isShared_3051_ == 0)
{
v___x_3053_ = v___x_3050_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_3048_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
}
}
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_del_object(v___x_2987_);
lean_dec_ref(v_env_2985_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2975_);
lean_dec(v___y_2970_);
lean_dec(v___y_2964_);
lean_dec_ref(v___x_2962_);
lean_dec(v_fst_2944_);
lean_dec(v_name_2931_);
lean_dec(v_head_2924_);
lean_dec(v_head_2923_);
v_a_3056_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_3001_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3001_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_del_object(v___x_2987_);
lean_dec_ref(v_env_2985_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2975_);
lean_dec(v___y_2970_);
lean_dec(v___y_2964_);
lean_dec_ref(v___x_2962_);
lean_dec(v_fst_2944_);
lean_dec(v_name_2931_);
lean_dec(v_head_2924_);
lean_dec(v_head_2923_);
v_a_3064_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_2996_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_2996_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3064_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
}
else
{
lean_object* v___x_3072_; lean_object* v___x_3074_; 
lean_del_object(v___x_2987_);
lean_dec_ref(v_env_2985_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2975_);
lean_dec(v___y_2970_);
lean_dec(v___y_2964_);
lean_dec_ref(v___x_2962_);
lean_dec(v_fst_2944_);
lean_dec(v_name_2931_);
lean_dec(v_head_2924_);
lean_dec(v_head_2923_);
v___x_3072_ = l_main___boxed__const__1;
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 0, v___x_3072_);
v___x_3074_ = v___x_2993_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v___x_3072_);
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
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_del_object(v___x_2987_);
lean_dec_ref(v_env_2985_);
lean_dec_ref(v_messages_2984_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2975_);
lean_dec(v___y_2970_);
lean_dec(v___y_2964_);
lean_dec_ref(v___x_2962_);
lean_dec(v_fst_2944_);
lean_dec(v_name_2931_);
lean_dec(v_head_2924_);
lean_dec(v_head_2923_);
v_a_3078_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_2991_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_2991_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
}
v___jp_3094_:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; size_t v_sz_3128_; size_t v___x_3129_; lean_object* v___x_3130_; 
lean_inc_ref(v___y_3123_);
v___x_3125_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3125_, 0, v___y_3124_);
lean_ctor_set(v___x_3125_, 1, v_nextMacroScope_3115_);
lean_ctor_set(v___x_3125_, 2, v_ngen_3116_);
lean_ctor_set(v___x_3125_, 3, v_auxDeclNGen_3117_);
lean_ctor_set(v___x_3125_, 4, v_traceState_3118_);
lean_ctor_set(v___x_3125_, 5, v___y_3123_);
lean_ctor_set(v___x_3125_, 6, v_messages_3119_);
lean_ctor_set(v___x_3125_, 7, v_infoState_3120_);
lean_ctor_set(v___x_3125_, 8, v_snapshotTasks_3121_);
v___x_3126_ = lean_st_ref_set(v___y_3109_, v___x_3125_);
v___x_3127_ = lean_box(0);
v_sz_3128_ = lean_array_size(v___y_3108_);
v___x_3129_ = ((size_t)0ULL);
v___x_3130_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v___y_3108_, v_sz_3128_, v___x_3129_, v___x_3127_, v___y_3104_, v___y_3109_);
lean_dec_ref(v___y_3108_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_dec_ref_known(v___x_3130_, 1);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3104_);
v___y_2964_ = v___y_3095_;
v___y_2965_ = v___y_3096_;
v___y_2966_ = v___y_3097_;
v___y_2967_ = v___y_3098_;
v___y_2968_ = v___y_3100_;
v___y_2969_ = v___y_3099_;
v___y_2970_ = v___y_3101_;
v___y_2971_ = v___y_3102_;
v___y_2972_ = v___y_3103_;
v___y_2973_ = v___y_3110_;
v___y_2974_ = v___y_3111_;
v___y_2975_ = v___y_3105_;
v___y_2976_ = v___y_3106_;
v___y_2977_ = v___y_3107_;
v___y_2978_ = v___y_3112_;
v___y_2979_ = v___y_3113_;
v___y_2980_ = v___y_3114_;
v___y_2981_ = v___y_3122_;
v___y_2982_ = v___y_3123_;
goto v___jp_2963_;
}
else
{
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_dec_ref_known(v___x_3130_, 1);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3104_);
v___y_2964_ = v___y_3095_;
v___y_2965_ = v___y_3096_;
v___y_2966_ = v___y_3097_;
v___y_2967_ = v___y_3098_;
v___y_2968_ = v___y_3100_;
v___y_2969_ = v___y_3099_;
v___y_2970_ = v___y_3101_;
v___y_2971_ = v___y_3102_;
v___y_2972_ = v___y_3103_;
v___y_2973_ = v___y_3110_;
v___y_2974_ = v___y_3111_;
v___y_2975_ = v___y_3105_;
v___y_2976_ = v___y_3106_;
v___y_2977_ = v___y_3107_;
v___y_2978_ = v___y_3112_;
v___y_2979_ = v___y_3113_;
v___y_2980_ = v___y_3114_;
v___y_2981_ = v___y_3122_;
v___y_2982_ = v___y_3123_;
goto v___jp_2963_;
}
else
{
lean_object* v_a_3131_; uint8_t v___x_3132_; 
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_a_3131_);
lean_dec_ref_known(v___x_3130_, 1);
v___x_3132_ = l_Lean_Exception_isInterrupt(v_a_3131_);
if (v___x_3132_ == 0)
{
lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3133_ = l_Lean_Exception_toMessageData(v_a_3131_);
v___x_3134_ = l_Lean_logError___at___00main_spec__14(v___x_3133_, v___y_3104_, v___y_3109_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3104_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_dec_ref_known(v___x_3134_, 1);
v___y_2964_ = v___y_3095_;
v___y_2965_ = v___y_3096_;
v___y_2966_ = v___y_3097_;
v___y_2967_ = v___y_3098_;
v___y_2968_ = v___y_3100_;
v___y_2969_ = v___y_3099_;
v___y_2970_ = v___y_3101_;
v___y_2971_ = v___y_3102_;
v___y_2972_ = v___y_3103_;
v___y_2973_ = v___y_3110_;
v___y_2974_ = v___y_3111_;
v___y_2975_ = v___y_3105_;
v___y_2976_ = v___y_3106_;
v___y_2977_ = v___y_3107_;
v___y_2978_ = v___y_3112_;
v___y_2979_ = v___y_3113_;
v___y_2980_ = v___y_3114_;
v___y_2981_ = v___y_3122_;
v___y_2982_ = v___y_3123_;
goto v___jp_2963_;
}
else
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
lean_dec_ref_known(v___x_3134_, 1);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3105_);
lean_dec(v___y_3101_);
lean_dec(v___y_3095_);
lean_dec_ref(v___x_2962_);
lean_dec(v_fst_2944_);
lean_dec(v_name_2931_);
lean_dec(v_head_2924_);
lean_dec(v_head_2923_);
v___x_3135_ = lean_obj_once(&l_main___closed__19, &l_main___closed__19_once, _init_l_main___closed__19);
v___x_3136_ = l_panic___at___00main_spec__5(v___x_3135_);
return v___x_3136_;
}
}
else
{
lean_dec(v_a_3131_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3104_);
v___y_2964_ = v___y_3095_;
v___y_2965_ = v___y_3096_;
v___y_2966_ = v___y_3097_;
v___y_2967_ = v___y_3098_;
v___y_2968_ = v___y_3100_;
v___y_2969_ = v___y_3099_;
v___y_2970_ = v___y_3101_;
v___y_2971_ = v___y_3102_;
v___y_2972_ = v___y_3103_;
v___y_2973_ = v___y_3110_;
v___y_2974_ = v___y_3111_;
v___y_2975_ = v___y_3105_;
v___y_2976_ = v___y_3106_;
v___y_2977_ = v___y_3107_;
v___y_2978_ = v___y_3112_;
v___y_2979_ = v___y_3113_;
v___y_2980_ = v___y_3114_;
v___y_2981_ = v___y_3122_;
v___y_2982_ = v___y_3123_;
goto v___jp_2963_;
}
}
}
}
v___jp_3137_:
{
lean_object* v___x_3162_; lean_object* v_fileName_3163_; lean_object* v_fileMap_3164_; lean_object* v_currRecDepth_3165_; lean_object* v_ref_3166_; lean_object* v_currNamespace_3167_; lean_object* v_openDecls_3168_; lean_object* v_initHeartbeats_3169_; lean_object* v_maxHeartbeats_3170_; lean_object* v_quotContext_3171_; lean_object* v_currMacroScope_3172_; lean_object* v_cancelTk_x3f_3173_; uint8_t v_suppressElabErrors_3174_; lean_object* v_inheritedTraceOptions_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3205_; 
v___x_3162_ = lean_st_ref_take(v___y_3161_);
v_fileName_3163_ = lean_ctor_get(v___y_3160_, 0);
v_fileMap_3164_ = lean_ctor_get(v___y_3160_, 1);
v_currRecDepth_3165_ = lean_ctor_get(v___y_3160_, 3);
v_ref_3166_ = lean_ctor_get(v___y_3160_, 5);
v_currNamespace_3167_ = lean_ctor_get(v___y_3160_, 6);
v_openDecls_3168_ = lean_ctor_get(v___y_3160_, 7);
v_initHeartbeats_3169_ = lean_ctor_get(v___y_3160_, 8);
v_maxHeartbeats_3170_ = lean_ctor_get(v___y_3160_, 9);
v_quotContext_3171_ = lean_ctor_get(v___y_3160_, 10);
v_currMacroScope_3172_ = lean_ctor_get(v___y_3160_, 11);
v_cancelTk_x3f_3173_ = lean_ctor_get(v___y_3160_, 12);
v_suppressElabErrors_3174_ = lean_ctor_get_uint8(v___y_3160_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3175_ = lean_ctor_get(v___y_3160_, 13);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___y_3160_);
if (v_isSharedCheck_3205_ == 0)
{
lean_object* v_unused_3206_; lean_object* v_unused_3207_; 
v_unused_3206_ = lean_ctor_get(v___y_3160_, 4);
lean_dec(v_unused_3206_);
v_unused_3207_ = lean_ctor_get(v___y_3160_, 2);
lean_dec(v_unused_3207_);
v___x_3177_ = v___y_3160_;
v_isShared_3178_ = v_isSharedCheck_3205_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_inheritedTraceOptions_3175_);
lean_inc(v_cancelTk_x3f_3173_);
lean_inc(v_currMacroScope_3172_);
lean_inc(v_quotContext_3171_);
lean_inc(v_maxHeartbeats_3170_);
lean_inc(v_initHeartbeats_3169_);
lean_inc(v_openDecls_3168_);
lean_inc(v_currNamespace_3167_);
lean_inc(v_ref_3166_);
lean_inc(v_currRecDepth_3165_);
lean_inc(v_fileMap_3164_);
lean_inc(v_fileName_3163_);
lean_dec(v___y_3160_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3205_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v_env_3179_; lean_object* v_nextMacroScope_3180_; lean_object* v_ngen_3181_; lean_object* v_auxDeclNGen_3182_; lean_object* v_traceState_3183_; lean_object* v_messages_3184_; lean_object* v_infoState_3185_; lean_object* v_snapshotTasks_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3190_; 
v_env_3179_ = lean_ctor_get(v___x_3162_, 0);
lean_inc_ref(v_env_3179_);
v_nextMacroScope_3180_ = lean_ctor_get(v___x_3162_, 1);
lean_inc(v_nextMacroScope_3180_);
v_ngen_3181_ = lean_ctor_get(v___x_3162_, 2);
lean_inc_ref(v_ngen_3181_);
v_auxDeclNGen_3182_ = lean_ctor_get(v___x_3162_, 3);
lean_inc_ref(v_auxDeclNGen_3182_);
v_traceState_3183_ = lean_ctor_get(v___x_3162_, 4);
lean_inc_ref(v_traceState_3183_);
v_messages_3184_ = lean_ctor_get(v___x_3162_, 6);
lean_inc_ref(v_messages_3184_);
v_infoState_3185_ = lean_ctor_get(v___x_3162_, 7);
lean_inc_ref(v_infoState_3185_);
v_snapshotTasks_3186_ = lean_ctor_get(v___x_3162_, 8);
lean_inc_ref(v_snapshotTasks_3186_);
lean_dec(v___x_3162_);
v___x_3187_ = l_Lean_maxRecDepth;
v___x_3188_ = l_Lean_Option_get___at___00main_spec__9(v___x_2962_, v___x_3187_);
lean_inc_ref(v___x_2962_);
if (v_isShared_3178_ == 0)
{
lean_ctor_set(v___x_3177_, 4, v___x_3188_);
lean_ctor_set(v___x_3177_, 2, v___x_2962_);
v___x_3190_ = v___x_3177_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_fileName_3163_);
lean_ctor_set(v_reuseFailAlloc_3204_, 1, v_fileMap_3164_);
lean_ctor_set(v_reuseFailAlloc_3204_, 2, v___x_2962_);
lean_ctor_set(v_reuseFailAlloc_3204_, 3, v_currRecDepth_3165_);
lean_ctor_set(v_reuseFailAlloc_3204_, 4, v___x_3188_);
lean_ctor_set(v_reuseFailAlloc_3204_, 5, v_ref_3166_);
lean_ctor_set(v_reuseFailAlloc_3204_, 6, v_currNamespace_3167_);
lean_ctor_set(v_reuseFailAlloc_3204_, 7, v_openDecls_3168_);
lean_ctor_set(v_reuseFailAlloc_3204_, 8, v_initHeartbeats_3169_);
lean_ctor_set(v_reuseFailAlloc_3204_, 9, v_maxHeartbeats_3170_);
lean_ctor_set(v_reuseFailAlloc_3204_, 10, v_quotContext_3171_);
lean_ctor_set(v_reuseFailAlloc_3204_, 11, v_currMacroScope_3172_);
lean_ctor_set(v_reuseFailAlloc_3204_, 12, v_cancelTk_x3f_3173_);
lean_ctor_set(v_reuseFailAlloc_3204_, 13, v_inheritedTraceOptions_3175_);
lean_ctor_set_uint8(v_reuseFailAlloc_3204_, sizeof(void*)*14 + 1, v_suppressElabErrors_3174_);
v___x_3190_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
lean_object* v___x_3191_; uint8_t v___x_3192_; 
lean_ctor_set_uint8(v___x_3190_, sizeof(void*)*14, v___y_3154_);
v___x_3191_ = lean_array_get_size(v___y_3151_);
v___x_3192_ = lean_nat_dec_lt(v___x_2961_, v___x_3191_);
if (v___x_3192_ == 0)
{
lean_object* v___x_3193_; 
lean_inc_ref(v___y_3147_);
v___x_3193_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3147_, v_env_3179_, v___x_2955_);
v___y_3095_ = v___y_3138_;
v___y_3096_ = v___y_3139_;
v___y_3097_ = v___y_3140_;
v___y_3098_ = v___y_3141_;
v___y_3099_ = v___y_3143_;
v___y_3100_ = v___y_3142_;
v___y_3101_ = v___y_3144_;
v___y_3102_ = v___y_3145_;
v___y_3103_ = v___y_3146_;
v___y_3104_ = v___x_3190_;
v___y_3105_ = v___y_3148_;
v___y_3106_ = v___y_3149_;
v___y_3107_ = v___y_3150_;
v___y_3108_ = v___y_3151_;
v___y_3109_ = v___y_3161_;
v___y_3110_ = v___y_3152_;
v___y_3111_ = v___y_3153_;
v___y_3112_ = v___y_3155_;
v___y_3113_ = v___y_3156_;
v___y_3114_ = v___y_3157_;
v_nextMacroScope_3115_ = v_nextMacroScope_3180_;
v_ngen_3116_ = v_ngen_3181_;
v_auxDeclNGen_3117_ = v_auxDeclNGen_3182_;
v_traceState_3118_ = v_traceState_3183_;
v_messages_3119_ = v_messages_3184_;
v_infoState_3120_ = v_infoState_3185_;
v_snapshotTasks_3121_ = v_snapshotTasks_3186_;
v___y_3122_ = v___y_3158_;
v___y_3123_ = v___y_3159_;
v___y_3124_ = v___x_3193_;
goto v___jp_3094_;
}
else
{
uint8_t v___x_3194_; 
v___x_3194_ = lean_nat_dec_le(v___x_3191_, v___x_3191_);
if (v___x_3194_ == 0)
{
if (v___x_3192_ == 0)
{
lean_object* v___x_3195_; 
lean_inc_ref(v___y_3147_);
v___x_3195_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3147_, v_env_3179_, v___x_2955_);
v___y_3095_ = v___y_3138_;
v___y_3096_ = v___y_3139_;
v___y_3097_ = v___y_3140_;
v___y_3098_ = v___y_3141_;
v___y_3099_ = v___y_3143_;
v___y_3100_ = v___y_3142_;
v___y_3101_ = v___y_3144_;
v___y_3102_ = v___y_3145_;
v___y_3103_ = v___y_3146_;
v___y_3104_ = v___x_3190_;
v___y_3105_ = v___y_3148_;
v___y_3106_ = v___y_3149_;
v___y_3107_ = v___y_3150_;
v___y_3108_ = v___y_3151_;
v___y_3109_ = v___y_3161_;
v___y_3110_ = v___y_3152_;
v___y_3111_ = v___y_3153_;
v___y_3112_ = v___y_3155_;
v___y_3113_ = v___y_3156_;
v___y_3114_ = v___y_3157_;
v_nextMacroScope_3115_ = v_nextMacroScope_3180_;
v_ngen_3116_ = v_ngen_3181_;
v_auxDeclNGen_3117_ = v_auxDeclNGen_3182_;
v_traceState_3118_ = v_traceState_3183_;
v_messages_3119_ = v_messages_3184_;
v_infoState_3120_ = v_infoState_3185_;
v_snapshotTasks_3121_ = v_snapshotTasks_3186_;
v___y_3122_ = v___y_3158_;
v___y_3123_ = v___y_3159_;
v___y_3124_ = v___x_3195_;
goto v___jp_3094_;
}
else
{
size_t v___x_3196_; size_t v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3196_ = ((size_t)0ULL);
v___x_3197_ = lean_usize_of_nat(v___x_3191_);
v___x_3198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3151_, v___x_3196_, v___x_3197_, v___x_2955_);
lean_inc_ref(v___y_3147_);
v___x_3199_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3147_, v_env_3179_, v___x_3198_);
v___y_3095_ = v___y_3138_;
v___y_3096_ = v___y_3139_;
v___y_3097_ = v___y_3140_;
v___y_3098_ = v___y_3141_;
v___y_3099_ = v___y_3143_;
v___y_3100_ = v___y_3142_;
v___y_3101_ = v___y_3144_;
v___y_3102_ = v___y_3145_;
v___y_3103_ = v___y_3146_;
v___y_3104_ = v___x_3190_;
v___y_3105_ = v___y_3148_;
v___y_3106_ = v___y_3149_;
v___y_3107_ = v___y_3150_;
v___y_3108_ = v___y_3151_;
v___y_3109_ = v___y_3161_;
v___y_3110_ = v___y_3152_;
v___y_3111_ = v___y_3153_;
v___y_3112_ = v___y_3155_;
v___y_3113_ = v___y_3156_;
v___y_3114_ = v___y_3157_;
v_nextMacroScope_3115_ = v_nextMacroScope_3180_;
v_ngen_3116_ = v_ngen_3181_;
v_auxDeclNGen_3117_ = v_auxDeclNGen_3182_;
v_traceState_3118_ = v_traceState_3183_;
v_messages_3119_ = v_messages_3184_;
v_infoState_3120_ = v_infoState_3185_;
v_snapshotTasks_3121_ = v_snapshotTasks_3186_;
v___y_3122_ = v___y_3158_;
v___y_3123_ = v___y_3159_;
v___y_3124_ = v___x_3199_;
goto v___jp_3094_;
}
}
else
{
size_t v___x_3200_; size_t v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3200_ = ((size_t)0ULL);
v___x_3201_ = lean_usize_of_nat(v___x_3191_);
v___x_3202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3151_, v___x_3200_, v___x_3201_, v___x_2955_);
lean_inc_ref(v___y_3147_);
v___x_3203_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3147_, v_env_3179_, v___x_3202_);
v___y_3095_ = v___y_3138_;
v___y_3096_ = v___y_3139_;
v___y_3097_ = v___y_3140_;
v___y_3098_ = v___y_3141_;
v___y_3099_ = v___y_3143_;
v___y_3100_ = v___y_3142_;
v___y_3101_ = v___y_3144_;
v___y_3102_ = v___y_3145_;
v___y_3103_ = v___y_3146_;
v___y_3104_ = v___x_3190_;
v___y_3105_ = v___y_3148_;
v___y_3106_ = v___y_3149_;
v___y_3107_ = v___y_3150_;
v___y_3108_ = v___y_3151_;
v___y_3109_ = v___y_3161_;
v___y_3110_ = v___y_3152_;
v___y_3111_ = v___y_3153_;
v___y_3112_ = v___y_3155_;
v___y_3113_ = v___y_3156_;
v___y_3114_ = v___y_3157_;
v_nextMacroScope_3115_ = v_nextMacroScope_3180_;
v_ngen_3116_ = v_ngen_3181_;
v_auxDeclNGen_3117_ = v_auxDeclNGen_3182_;
v_traceState_3118_ = v_traceState_3183_;
v_messages_3119_ = v_messages_3184_;
v_infoState_3120_ = v_infoState_3185_;
v_snapshotTasks_3121_ = v_snapshotTasks_3186_;
v___y_3122_ = v___y_3158_;
v___y_3123_ = v___y_3159_;
v___y_3124_ = v___x_3203_;
goto v___jp_3094_;
}
}
}
}
}
v___jp_3208_:
{
if (v___y_3232_ == 0)
{
lean_object* v___x_3233_; lean_object* v_env_3234_; lean_object* v_nextMacroScope_3235_; lean_object* v_ngen_3236_; lean_object* v_auxDeclNGen_3237_; lean_object* v_traceState_3238_; lean_object* v_messages_3239_; lean_object* v_infoState_3240_; lean_object* v_snapshotTasks_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3250_; 
v___x_3233_ = lean_st_ref_take(v___y_3227_);
v_env_3234_ = lean_ctor_get(v___x_3233_, 0);
v_nextMacroScope_3235_ = lean_ctor_get(v___x_3233_, 1);
v_ngen_3236_ = lean_ctor_get(v___x_3233_, 2);
v_auxDeclNGen_3237_ = lean_ctor_get(v___x_3233_, 3);
v_traceState_3238_ = lean_ctor_get(v___x_3233_, 4);
v_messages_3239_ = lean_ctor_get(v___x_3233_, 6);
v_infoState_3240_ = lean_ctor_get(v___x_3233_, 7);
v_snapshotTasks_3241_ = lean_ctor_get(v___x_3233_, 8);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3250_ == 0)
{
lean_object* v_unused_3251_; 
v_unused_3251_ = lean_ctor_get(v___x_3233_, 5);
lean_dec(v_unused_3251_);
v___x_3243_ = v___x_3233_;
v_isShared_3244_ = v_isSharedCheck_3250_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_snapshotTasks_3241_);
lean_inc(v_infoState_3240_);
lean_inc(v_messages_3239_);
lean_inc(v_traceState_3238_);
lean_inc(v_auxDeclNGen_3237_);
lean_inc(v_ngen_3236_);
lean_inc(v_nextMacroScope_3235_);
lean_inc(v_env_3234_);
lean_dec(v___x_3233_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3250_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___x_3245_; lean_object* v___x_3247_; 
v___x_3245_ = l_Lean_Kernel_enableDiag(v_env_3234_, v___y_3225_);
lean_inc_ref(v___y_3231_);
if (v_isShared_3244_ == 0)
{
lean_ctor_set(v___x_3243_, 5, v___y_3231_);
lean_ctor_set(v___x_3243_, 0, v___x_3245_);
v___x_3247_ = v___x_3243_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___x_3245_);
lean_ctor_set(v_reuseFailAlloc_3249_, 1, v_nextMacroScope_3235_);
lean_ctor_set(v_reuseFailAlloc_3249_, 2, v_ngen_3236_);
lean_ctor_set(v_reuseFailAlloc_3249_, 3, v_auxDeclNGen_3237_);
lean_ctor_set(v_reuseFailAlloc_3249_, 4, v_traceState_3238_);
lean_ctor_set(v_reuseFailAlloc_3249_, 5, v___y_3231_);
lean_ctor_set(v_reuseFailAlloc_3249_, 6, v_messages_3239_);
lean_ctor_set(v_reuseFailAlloc_3249_, 7, v_infoState_3240_);
lean_ctor_set(v_reuseFailAlloc_3249_, 8, v_snapshotTasks_3241_);
v___x_3247_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
lean_object* v___x_3248_; 
v___x_3248_ = lean_st_ref_set(v___y_3227_, v___x_3247_);
lean_inc(v___y_3227_);
v___y_3138_ = v___y_3209_;
v___y_3139_ = v___y_3210_;
v___y_3140_ = v___y_3211_;
v___y_3141_ = v___y_3212_;
v___y_3142_ = v___y_3214_;
v___y_3143_ = v___y_3213_;
v___y_3144_ = v___y_3215_;
v___y_3145_ = v___y_3216_;
v___y_3146_ = v___y_3217_;
v___y_3147_ = v___y_3218_;
v___y_3148_ = v___y_3219_;
v___y_3149_ = v___y_3220_;
v___y_3150_ = v___y_3221_;
v___y_3151_ = v___y_3222_;
v___y_3152_ = v___y_3223_;
v___y_3153_ = v___y_3224_;
v___y_3154_ = v___y_3225_;
v___y_3155_ = v___y_3226_;
v___y_3156_ = v___y_3227_;
v___y_3157_ = v___y_3228_;
v___y_3158_ = v___y_3230_;
v___y_3159_ = v___y_3231_;
v___y_3160_ = v___y_3229_;
v___y_3161_ = v___y_3227_;
goto v___jp_3137_;
}
}
}
else
{
lean_inc(v___y_3227_);
v___y_3138_ = v___y_3209_;
v___y_3139_ = v___y_3210_;
v___y_3140_ = v___y_3211_;
v___y_3141_ = v___y_3212_;
v___y_3142_ = v___y_3214_;
v___y_3143_ = v___y_3213_;
v___y_3144_ = v___y_3215_;
v___y_3145_ = v___y_3216_;
v___y_3146_ = v___y_3217_;
v___y_3147_ = v___y_3218_;
v___y_3148_ = v___y_3219_;
v___y_3149_ = v___y_3220_;
v___y_3150_ = v___y_3221_;
v___y_3151_ = v___y_3222_;
v___y_3152_ = v___y_3223_;
v___y_3153_ = v___y_3224_;
v___y_3154_ = v___y_3225_;
v___y_3155_ = v___y_3226_;
v___y_3156_ = v___y_3227_;
v___y_3157_ = v___y_3228_;
v___y_3158_ = v___y_3230_;
v___y_3159_ = v___y_3231_;
v___y_3160_ = v___y_3229_;
v___y_3161_ = v___y_3227_;
goto v___jp_3137_;
}
}
v___jp_3255_:
{
lean_object* v___x_3265_; 
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 1, v___y_3263_);
lean_ctor_set(v___x_2947_, 0, v___y_3260_);
v___x_3265_ = v___x_2947_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___y_3260_);
lean_ctor_set(v_reuseFailAlloc_3360_, 1, v___y_3263_);
v___x_3265_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v_moduleData_3269_; lean_object* v___x_3270_; uint8_t v___x_3271_; 
v___x_3266_ = lean_box(0);
lean_inc_ref(v___y_3262_);
v___x_3267_ = l_Lean_EnvExtension_setState___redArg(v___y_3262_, v___y_3259_, v___x_3265_, v___x_3266_);
v___x_3268_ = l_Lean_Environment_header(v___x_3267_);
v_moduleData_3269_ = lean_ctor_get(v___x_3268_, 6);
lean_inc_ref(v_moduleData_3269_);
lean_dec_ref(v___x_3268_);
v___x_3270_ = lean_array_get_size(v_moduleData_3269_);
v___x_3271_ = lean_nat_dec_lt(v___y_3258_, v___x_3270_);
if (v___x_3271_ == 0)
{
lean_object* v___x_3272_; lean_object* v___x_3273_; 
lean_dec_ref(v_moduleData_3269_);
lean_dec_ref(v___x_3267_);
lean_dec(v___y_3258_);
lean_dec(v___y_3257_);
lean_dec(v___y_3256_);
lean_dec_ref(v___x_2962_);
lean_dec(v_fst_2944_);
lean_dec(v_name_2931_);
lean_dec(v_head_2924_);
lean_dec(v_head_2923_);
v___x_3272_ = lean_obj_once(&l_main___closed__21, &l_main___closed__21_once, _init_l_main___closed__21);
v___x_3273_ = l_panic___at___00main_spec__5(v___x_3272_);
return v___x_3273_;
}
else
{
lean_object* v_base_3274_; lean_object* v_private_3275_; lean_object* v_header_3276_; lean_object* v_serverBaseExts_3277_; lean_object* v_checked_3278_; lean_object* v_asyncConstsMap_3279_; lean_object* v_asyncCtx_x3f_3280_; lean_object* v_importRealizationCtx_x3f_3281_; lean_object* v_localRealizationCtxMap_3282_; lean_object* v_allRealizations_3283_; uint8_t v_isExporting_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3358_; 
v_base_3274_ = lean_ctor_get(v___x_3267_, 0);
lean_inc_ref(v_base_3274_);
v_private_3275_ = lean_ctor_get(v_base_3274_, 0);
lean_inc(v_private_3275_);
v_header_3276_ = lean_ctor_get(v_private_3275_, 5);
lean_inc_ref(v_header_3276_);
v_serverBaseExts_3277_ = lean_ctor_get(v___x_3267_, 1);
v_checked_3278_ = lean_ctor_get(v___x_3267_, 2);
v_asyncConstsMap_3279_ = lean_ctor_get(v___x_3267_, 3);
v_asyncCtx_x3f_3280_ = lean_ctor_get(v___x_3267_, 4);
v_importRealizationCtx_x3f_3281_ = lean_ctor_get(v___x_3267_, 5);
v_localRealizationCtxMap_3282_ = lean_ctor_get(v___x_3267_, 6);
v_allRealizations_3283_ = lean_ctor_get(v___x_3267_, 7);
v_isExporting_3284_ = lean_ctor_get_uint8(v___x_3267_, sizeof(void*)*8);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3267_);
if (v_isSharedCheck_3358_ == 0)
{
lean_object* v_unused_3359_; 
v_unused_3359_ = lean_ctor_get(v___x_3267_, 0);
lean_dec(v_unused_3359_);
v___x_3286_ = v___x_3267_;
v_isShared_3287_ = v_isSharedCheck_3358_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_allRealizations_3283_);
lean_inc(v_localRealizationCtxMap_3282_);
lean_inc(v_importRealizationCtx_x3f_3281_);
lean_inc(v_asyncCtx_x3f_3280_);
lean_inc(v_asyncConstsMap_3279_);
lean_inc(v_checked_3278_);
lean_inc(v_serverBaseExts_3277_);
lean_dec(v___x_3267_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3358_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v_public_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3356_; 
v_public_3288_ = lean_ctor_get(v_base_3274_, 1);
v_isSharedCheck_3356_ = !lean_is_exclusive(v_base_3274_);
if (v_isSharedCheck_3356_ == 0)
{
lean_object* v_unused_3357_; 
v_unused_3357_ = lean_ctor_get(v_base_3274_, 0);
lean_dec(v_unused_3357_);
v___x_3290_ = v_base_3274_;
v_isShared_3291_ = v_isSharedCheck_3356_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_public_3288_);
lean_dec(v_base_3274_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3356_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v_constants_3292_; uint8_t v_quotInit_3293_; lean_object* v_diagnostics_3294_; lean_object* v_const2ModIdx_3295_; lean_object* v_extensions_3296_; lean_object* v_irBaseExts_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3354_; 
v_constants_3292_ = lean_ctor_get(v_private_3275_, 0);
v_quotInit_3293_ = lean_ctor_get_uint8(v_private_3275_, sizeof(void*)*6);
v_diagnostics_3294_ = lean_ctor_get(v_private_3275_, 1);
v_const2ModIdx_3295_ = lean_ctor_get(v_private_3275_, 2);
v_extensions_3296_ = lean_ctor_get(v_private_3275_, 3);
v_irBaseExts_3297_ = lean_ctor_get(v_private_3275_, 4);
v_isSharedCheck_3354_ = !lean_is_exclusive(v_private_3275_);
if (v_isSharedCheck_3354_ == 0)
{
lean_object* v_unused_3355_; 
v_unused_3355_ = lean_ctor_get(v_private_3275_, 5);
lean_dec(v_unused_3355_);
v___x_3299_ = v_private_3275_;
v_isShared_3300_ = v_isSharedCheck_3354_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_irBaseExts_3297_);
lean_inc(v_extensions_3296_);
lean_inc(v_const2ModIdx_3295_);
lean_inc(v_diagnostics_3294_);
lean_inc(v_constants_3292_);
lean_dec(v_private_3275_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3354_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
uint32_t v_trustLevel_3301_; lean_object* v_mainModule_3302_; uint8_t v_isModule_3303_; lean_object* v_regions_3304_; lean_object* v_modules_3305_; lean_object* v_moduleName2Idx_3306_; lean_object* v_importAllModules_3307_; lean_object* v_moduleData_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3352_; 
v_trustLevel_3301_ = lean_ctor_get_uint32(v_header_3276_, sizeof(void*)*7);
v_mainModule_3302_ = lean_ctor_get(v_header_3276_, 0);
v_isModule_3303_ = lean_ctor_get_uint8(v_header_3276_, sizeof(void*)*7 + 4);
v_regions_3304_ = lean_ctor_get(v_header_3276_, 2);
v_modules_3305_ = lean_ctor_get(v_header_3276_, 3);
v_moduleName2Idx_3306_ = lean_ctor_get(v_header_3276_, 4);
v_importAllModules_3307_ = lean_ctor_get(v_header_3276_, 5);
v_moduleData_3308_ = lean_ctor_get(v_header_3276_, 6);
v_isSharedCheck_3352_ = !lean_is_exclusive(v_header_3276_);
if (v_isSharedCheck_3352_ == 0)
{
lean_object* v_unused_3353_; 
v_unused_3353_ = lean_ctor_get(v_header_3276_, 1);
lean_dec(v_unused_3353_);
v___x_3310_ = v_header_3276_;
v_isShared_3311_ = v_isSharedCheck_3352_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_moduleData_3308_);
lean_inc(v_importAllModules_3307_);
lean_inc(v_moduleName2Idx_3306_);
lean_inc(v_modules_3305_);
lean_inc(v_regions_3304_);
lean_inc(v_mainModule_3302_);
lean_dec(v_header_3276_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3352_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3312_; lean_object* v_imports_3313_; lean_object* v___x_3315_; 
v___x_3312_ = lean_array_fget(v_moduleData_3269_, v___y_3258_);
lean_dec_ref(v_moduleData_3269_);
v_imports_3313_ = lean_ctor_get(v___x_3312_, 0);
lean_inc_ref(v_imports_3313_);
lean_dec(v___x_3312_);
if (v_isShared_3311_ == 0)
{
lean_ctor_set(v___x_3310_, 1, v_imports_3313_);
v___x_3315_ = v___x_3310_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(0, 7, 5);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_mainModule_3302_);
lean_ctor_set(v_reuseFailAlloc_3351_, 1, v_imports_3313_);
lean_ctor_set(v_reuseFailAlloc_3351_, 2, v_regions_3304_);
lean_ctor_set(v_reuseFailAlloc_3351_, 3, v_modules_3305_);
lean_ctor_set(v_reuseFailAlloc_3351_, 4, v_moduleName2Idx_3306_);
lean_ctor_set(v_reuseFailAlloc_3351_, 5, v_importAllModules_3307_);
lean_ctor_set(v_reuseFailAlloc_3351_, 6, v_moduleData_3308_);
lean_ctor_set_uint32(v_reuseFailAlloc_3351_, sizeof(void*)*7, v_trustLevel_3301_);
lean_ctor_set_uint8(v_reuseFailAlloc_3351_, sizeof(void*)*7 + 4, v_isModule_3303_);
v___x_3315_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
lean_object* v___x_3317_; 
if (v_isShared_3300_ == 0)
{
lean_ctor_set(v___x_3299_, 5, v___x_3315_);
v___x_3317_ = v___x_3299_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_constants_3292_);
lean_ctor_set(v_reuseFailAlloc_3350_, 1, v_diagnostics_3294_);
lean_ctor_set(v_reuseFailAlloc_3350_, 2, v_const2ModIdx_3295_);
lean_ctor_set(v_reuseFailAlloc_3350_, 3, v_extensions_3296_);
lean_ctor_set(v_reuseFailAlloc_3350_, 4, v_irBaseExts_3297_);
lean_ctor_set(v_reuseFailAlloc_3350_, 5, v___x_3315_);
lean_ctor_set_uint8(v_reuseFailAlloc_3350_, sizeof(void*)*6, v_quotInit_3293_);
v___x_3317_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
lean_object* v___x_3319_; 
if (v_isShared_3291_ == 0)
{
lean_ctor_set(v___x_3290_, 0, v___x_3317_);
v___x_3319_ = v___x_3290_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3317_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v_public_3288_);
v___x_3319_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
lean_object* v___x_3321_; 
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 0, v___x_3319_);
v___x_3321_ = v___x_3286_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3319_);
lean_ctor_set(v_reuseFailAlloc_3348_, 1, v_serverBaseExts_3277_);
lean_ctor_set(v_reuseFailAlloc_3348_, 2, v_checked_3278_);
lean_ctor_set(v_reuseFailAlloc_3348_, 3, v_asyncConstsMap_3279_);
lean_ctor_set(v_reuseFailAlloc_3348_, 4, v_asyncCtx_x3f_3280_);
lean_ctor_set(v_reuseFailAlloc_3348_, 5, v_importRealizationCtx_x3f_3281_);
lean_ctor_set(v_reuseFailAlloc_3348_, 6, v_localRealizationCtxMap_3282_);
lean_ctor_set(v_reuseFailAlloc_3348_, 7, v_allRealizations_3283_);
lean_ctor_set_uint8(v_reuseFailAlloc_3348_, sizeof(void*)*8, v_isExporting_3284_);
v___x_3321_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v_env_3344_; lean_object* v___x_3345_; uint8_t v___x_3346_; uint8_t v___x_3347_; 
v___x_3322_ = l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
v___x_3323_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2956_, v___x_3322_, v___x_3321_, v___y_3258_, v___y_3261_);
lean_dec(v___y_3258_);
v___x_3324_ = l_Lean_firstFrontendMacroScope;
v___x_3325_ = lean_obj_once(&l_main___closed__22, &l_main___closed__22_once, _init_l_main___closed__22);
v___x_3326_ = ((lean_object*)(l_main___closed__25));
lean_inc_n(v___y_3257_, 3);
v___x_3327_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3327_, 0, v___y_3257_);
lean_ctor_set(v___x_3327_, 1, v___x_3254_);
lean_ctor_set(v___x_3327_, 2, v___x_2942_);
v___x_3328_ = lean_obj_once(&l_main___closed__26, &l_main___closed__26_once, _init_l_main___closed__26);
v___x_3329_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_3330_ = lean_obj_once(&l_main___closed__30, &l_main___closed__30_once, _init_l_main___closed__30);
v___x_3331_ = lean_obj_once(&l_main___closed__31, &l_main___closed__31_once, _init_l_main___closed__31);
v___x_3332_ = ((lean_object*)(l_main___closed__32));
lean_inc_ref(v___x_3327_);
v___x_3333_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3321_);
lean_ctor_set(v___x_3333_, 1, v___x_3325_);
lean_ctor_set(v___x_3333_, 2, v___x_3326_);
lean_ctor_set(v___x_3333_, 3, v___x_3327_);
lean_ctor_set(v___x_3333_, 4, v___x_3328_);
lean_ctor_set(v___x_3333_, 5, v___x_3329_);
lean_ctor_set(v___x_3333_, 6, v___x_3330_);
lean_ctor_set(v___x_3333_, 7, v___x_3331_);
lean_ctor_set(v___x_3333_, 8, v___x_3332_);
v___x_3334_ = lean_st_mk_ref(v___x_3333_);
v___x_3335_ = l_Lean_inheritedTraceOptions;
v___x_3336_ = lean_st_ref_get(v___x_3335_);
v___x_3337_ = lean_st_ref_get(v___x_3334_);
v___x_3338_ = l_Lean_instInhabitedFileMap_default;
v___x_3339_ = lean_unsigned_to_nat(1000u);
v___x_3340_ = lean_box(0);
v___x_3341_ = l_Lean_Core_getMaxHeartbeats(v___x_2962_);
v___x_3342_ = lean_box(0);
lean_inc_ref(v___x_2962_);
lean_inc(v_head_2923_);
v___x_3343_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3343_, 0, v_head_2923_);
lean_ctor_set(v___x_3343_, 1, v___x_3338_);
lean_ctor_set(v___x_3343_, 2, v___x_2962_);
lean_ctor_set(v___x_3343_, 3, v___x_2961_);
lean_ctor_set(v___x_3343_, 4, v___x_3339_);
lean_ctor_set(v___x_3343_, 5, v___x_3340_);
lean_ctor_set(v___x_3343_, 6, v___y_3257_);
lean_ctor_set(v___x_3343_, 7, v___x_2942_);
lean_ctor_set(v___x_3343_, 8, v___x_2961_);
lean_ctor_set(v___x_3343_, 9, v___x_3341_);
lean_ctor_set(v___x_3343_, 10, v___y_3257_);
lean_ctor_set(v___x_3343_, 11, v___x_3324_);
lean_ctor_set(v___x_3343_, 12, v___x_3342_);
lean_ctor_set(v___x_3343_, 13, v___x_3336_);
lean_ctor_set_uint8(v___x_3343_, sizeof(void*)*14, v___x_2933_);
lean_ctor_set_uint8(v___x_3343_, sizeof(void*)*14 + 1, v___x_2933_);
v_env_3344_ = lean_ctor_get(v___x_3337_, 0);
lean_inc_ref(v_env_3344_);
lean_dec(v___x_3337_);
v___x_3345_ = l_Lean_diagnostics;
v___x_3346_ = l_Lean_Option_get___at___00main_spec__8(v___x_2962_, v___x_3345_);
v___x_3347_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3344_);
lean_dec_ref(v_env_3344_);
if (v___x_3347_ == 0)
{
if (v___x_3346_ == 0)
{
v___y_3209_ = v___y_3256_;
v___y_3210_ = v___x_3340_;
v___y_3211_ = v___x_3338_;
v___y_3212_ = v___x_3271_;
v___y_3213_ = v___x_3324_;
v___y_3214_ = v___x_3342_;
v___y_3215_ = v___x_2942_;
v___y_3216_ = v___x_3335_;
v___y_3217_ = v___x_3329_;
v___y_3218_ = v___x_3322_;
v___y_3219_ = v___y_3257_;
v___y_3220_ = v___x_3331_;
v___y_3221_ = v___x_3326_;
v___y_3222_ = v___x_3323_;
v___y_3223_ = v___x_3325_;
v___y_3224_ = v___x_3332_;
v___y_3225_ = v___x_3346_;
v___y_3226_ = v___x_3327_;
v___y_3227_ = v___x_3334_;
v___y_3228_ = v___x_3330_;
v___y_3229_ = v___x_3343_;
v___y_3230_ = v___x_3328_;
v___y_3231_ = v___x_3329_;
v___y_3232_ = v___x_3271_;
goto v___jp_3208_;
}
else
{
v___y_3209_ = v___y_3256_;
v___y_3210_ = v___x_3340_;
v___y_3211_ = v___x_3338_;
v___y_3212_ = v___x_3271_;
v___y_3213_ = v___x_3324_;
v___y_3214_ = v___x_3342_;
v___y_3215_ = v___x_2942_;
v___y_3216_ = v___x_3335_;
v___y_3217_ = v___x_3329_;
v___y_3218_ = v___x_3322_;
v___y_3219_ = v___y_3257_;
v___y_3220_ = v___x_3331_;
v___y_3221_ = v___x_3326_;
v___y_3222_ = v___x_3323_;
v___y_3223_ = v___x_3325_;
v___y_3224_ = v___x_3332_;
v___y_3225_ = v___x_3346_;
v___y_3226_ = v___x_3327_;
v___y_3227_ = v___x_3334_;
v___y_3228_ = v___x_3330_;
v___y_3229_ = v___x_3343_;
v___y_3230_ = v___x_3328_;
v___y_3231_ = v___x_3329_;
v___y_3232_ = v___x_3347_;
goto v___jp_3208_;
}
}
else
{
v___y_3209_ = v___y_3256_;
v___y_3210_ = v___x_3340_;
v___y_3211_ = v___x_3338_;
v___y_3212_ = v___x_3271_;
v___y_3213_ = v___x_3324_;
v___y_3214_ = v___x_3342_;
v___y_3215_ = v___x_2942_;
v___y_3216_ = v___x_3335_;
v___y_3217_ = v___x_3329_;
v___y_3218_ = v___x_3322_;
v___y_3219_ = v___y_3257_;
v___y_3220_ = v___x_3331_;
v___y_3221_ = v___x_3326_;
v___y_3222_ = v___x_3323_;
v___y_3223_ = v___x_3325_;
v___y_3224_ = v___x_3332_;
v___y_3225_ = v___x_3346_;
v___y_3226_ = v___x_3327_;
v___y_3227_ = v___x_3334_;
v___y_3228_ = v___x_3330_;
v___y_3229_ = v___x_3343_;
v___y_3230_ = v___x_3328_;
v___y_3231_ = v___x_3329_;
v___y_3232_ = v___x_3346_;
goto v___jp_3208_;
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
v___jp_3361_:
{
lean_object* v___x_3367_; lean_object* v_toEnvExtension_3368_; lean_object* v_asyncMode_3369_; lean_object* v___x_3370_; lean_object* v_importedEntries_3371_; lean_object* v_state_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; uint8_t v___x_3375_; 
v___x_3367_ = l_Lean_IR_declMapExt;
v_toEnvExtension_3368_ = lean_ctor_get(v___x_3367_, 0);
v_asyncMode_3369_ = lean_ctor_get(v_toEnvExtension_3368_, 2);
lean_inc(v___y_3364_);
lean_inc_ref(v___y_3366_);
v___x_3370_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2953_, v_toEnvExtension_3368_, v___y_3366_, v_asyncMode_3369_, v___y_3364_);
v_importedEntries_3371_ = lean_ctor_get(v___x_3370_, 0);
lean_inc_ref(v_importedEntries_3371_);
v_state_3372_ = lean_ctor_get(v___x_3370_, 1);
lean_inc(v_state_3372_);
lean_dec(v___x_3370_);
v___x_3373_ = lean_array_get_borrowed(v___x_2954_, v_importedEntries_3371_, v___y_3363_);
v___x_3374_ = lean_array_get_size(v___x_3373_);
v___x_3375_ = lean_nat_dec_lt(v___x_2961_, v___x_3374_);
if (v___x_3375_ == 0)
{
v___y_3256_ = v___y_3362_;
v___y_3257_ = v___y_3364_;
v___y_3258_ = v___y_3363_;
v___y_3259_ = v___y_3366_;
v___y_3260_ = v_importedEntries_3371_;
v___y_3261_ = v___y_3365_;
v___y_3262_ = v_toEnvExtension_3368_;
v___y_3263_ = v_state_3372_;
goto v___jp_3255_;
}
else
{
uint8_t v___x_3376_; 
v___x_3376_ = lean_nat_dec_le(v___x_3374_, v___x_3374_);
if (v___x_3376_ == 0)
{
if (v___x_3375_ == 0)
{
v___y_3256_ = v___y_3362_;
v___y_3257_ = v___y_3364_;
v___y_3258_ = v___y_3363_;
v___y_3259_ = v___y_3366_;
v___y_3260_ = v_importedEntries_3371_;
v___y_3261_ = v___y_3365_;
v___y_3262_ = v_toEnvExtension_3368_;
v___y_3263_ = v_state_3372_;
goto v___jp_3255_;
}
else
{
size_t v___x_3377_; size_t v___x_3378_; lean_object* v___x_3379_; 
v___x_3377_ = ((size_t)0ULL);
v___x_3378_ = lean_usize_of_nat(v___x_3374_);
lean_inc_ref(v___y_3366_);
v___x_3379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3366_, v___x_3373_, v___x_3377_, v___x_3378_, v_state_3372_);
v___y_3256_ = v___y_3362_;
v___y_3257_ = v___y_3364_;
v___y_3258_ = v___y_3363_;
v___y_3259_ = v___y_3366_;
v___y_3260_ = v_importedEntries_3371_;
v___y_3261_ = v___y_3365_;
v___y_3262_ = v_toEnvExtension_3368_;
v___y_3263_ = v___x_3379_;
goto v___jp_3255_;
}
}
else
{
size_t v___x_3380_; size_t v___x_3381_; lean_object* v___x_3382_; 
v___x_3380_ = ((size_t)0ULL);
v___x_3381_ = lean_usize_of_nat(v___x_3374_);
lean_inc_ref(v___y_3366_);
v___x_3382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3366_, v___x_3373_, v___x_3380_, v___x_3381_, v_state_3372_);
v___y_3256_ = v___y_3362_;
v___y_3257_ = v___y_3364_;
v___y_3258_ = v___y_3363_;
v___y_3259_ = v___y_3366_;
v___y_3260_ = v_importedEntries_3371_;
v___y_3261_ = v___y_3365_;
v___y_3262_ = v_toEnvExtension_3368_;
v___y_3263_ = v___x_3382_;
goto v___jp_3255_;
}
}
}
v___jp_3383_:
{
uint8_t v___x_3391_; 
v___x_3391_ = lean_nat_dec_lt(v___x_2961_, v___y_3387_);
if (v___x_3391_ == 0)
{
lean_dec_ref(v___y_3389_);
lean_dec(v___y_3387_);
v___y_3362_ = v___y_3384_;
v___y_3363_ = v___y_3386_;
v___y_3364_ = v___y_3385_;
v___y_3365_ = v___y_3388_;
v___y_3366_ = v___y_3390_;
goto v___jp_3361_;
}
else
{
uint8_t v___x_3392_; 
v___x_3392_ = lean_nat_dec_le(v___y_3387_, v___y_3387_);
if (v___x_3392_ == 0)
{
if (v___x_3391_ == 0)
{
lean_dec_ref(v___y_3389_);
lean_dec(v___y_3387_);
v___y_3362_ = v___y_3384_;
v___y_3363_ = v___y_3386_;
v___y_3364_ = v___y_3385_;
v___y_3365_ = v___y_3388_;
v___y_3366_ = v___y_3390_;
goto v___jp_3361_;
}
else
{
size_t v___x_3393_; size_t v___x_3394_; lean_object* v___x_3395_; 
v___x_3393_ = ((size_t)0ULL);
v___x_3394_ = lean_usize_of_nat(v___y_3387_);
lean_dec(v___y_3387_);
v___x_3395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3389_, v___x_3393_, v___x_3394_, v___y_3390_);
lean_dec_ref(v___y_3389_);
v___y_3362_ = v___y_3384_;
v___y_3363_ = v___y_3386_;
v___y_3364_ = v___y_3385_;
v___y_3365_ = v___y_3388_;
v___y_3366_ = v___x_3395_;
goto v___jp_3361_;
}
}
else
{
size_t v___x_3396_; size_t v___x_3397_; lean_object* v___x_3398_; 
v___x_3396_ = ((size_t)0ULL);
v___x_3397_ = lean_usize_of_nat(v___y_3387_);
lean_dec(v___y_3387_);
v___x_3398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3389_, v___x_3396_, v___x_3397_, v___y_3390_);
lean_dec_ref(v___y_3389_);
v___y_3362_ = v___y_3384_;
v___y_3363_ = v___y_3386_;
v___y_3364_ = v___y_3385_;
v___y_3365_ = v___y_3388_;
v___y_3366_ = v___x_3398_;
goto v___jp_3361_;
}
}
}
v___jp_3399_:
{
lean_object* v___x_3406_; uint8_t v___x_3407_; 
v___x_3406_ = lean_array_get_size(v___y_3405_);
v___x_3407_ = lean_nat_dec_lt(v___x_2961_, v___x_3406_);
if (v___x_3407_ == 0)
{
v___y_3384_ = v___y_3400_;
v___y_3385_ = v___y_3403_;
v___y_3386_ = v___y_3401_;
v___y_3387_ = v___x_3406_;
v___y_3388_ = v___y_3404_;
v___y_3389_ = v___y_3405_;
v___y_3390_ = v___y_3402_;
goto v___jp_3383_;
}
else
{
uint8_t v___x_3408_; 
v___x_3408_ = lean_nat_dec_le(v___x_3406_, v___x_3406_);
if (v___x_3408_ == 0)
{
if (v___x_3407_ == 0)
{
v___y_3384_ = v___y_3400_;
v___y_3385_ = v___y_3403_;
v___y_3386_ = v___y_3401_;
v___y_3387_ = v___x_3406_;
v___y_3388_ = v___y_3404_;
v___y_3389_ = v___y_3405_;
v___y_3390_ = v___y_3402_;
goto v___jp_3383_;
}
else
{
size_t v___x_3409_; size_t v___x_3410_; lean_object* v___x_3411_; 
v___x_3409_ = ((size_t)0ULL);
v___x_3410_ = lean_usize_of_nat(v___x_3406_);
v___x_3411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3405_, v___x_3409_, v___x_3410_, v___y_3402_);
v___y_3384_ = v___y_3400_;
v___y_3385_ = v___y_3403_;
v___y_3386_ = v___y_3401_;
v___y_3387_ = v___x_3406_;
v___y_3388_ = v___y_3404_;
v___y_3389_ = v___y_3405_;
v___y_3390_ = v___x_3411_;
goto v___jp_3383_;
}
}
else
{
size_t v___x_3412_; size_t v___x_3413_; lean_object* v___x_3414_; 
v___x_3412_ = ((size_t)0ULL);
v___x_3413_ = lean_usize_of_nat(v___x_3406_);
v___x_3414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3405_, v___x_3412_, v___x_3413_, v___y_3402_);
v___y_3384_ = v___y_3400_;
v___y_3385_ = v___y_3403_;
v___y_3386_ = v___y_3401_;
v___y_3387_ = v___x_3406_;
v___y_3388_ = v___y_3404_;
v___y_3389_ = v___y_3405_;
v___y_3390_ = v___x_3414_;
goto v___jp_3383_;
}
}
}
v___jp_3418_:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___f_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3420_ = l_Lean_instInhabitedImportState_default;
v___x_3421_ = lean_box(v___x_3417_);
v___x_3422_ = lean_box(v___y_3419_);
v___x_3423_ = lean_box(v___x_2958_);
v___x_3424_ = lean_box(v___x_2933_);
lean_inc_ref(v___x_2962_);
lean_inc(v_name_2931_);
v___f_3425_ = lean_alloc_closure((void*)(l_main___lam__0___boxed), 10, 9);
lean_closure_set(v___f_3425_, 0, v___x_3420_);
lean_closure_set(v___f_3425_, 1, v___x_3416_);
lean_closure_set(v___f_3425_, 2, v___x_3421_);
lean_closure_set(v___f_3425_, 3, v___x_2955_);
lean_closure_set(v___f_3425_, 4, v___x_3422_);
lean_closure_set(v___f_3425_, 5, v_name_2931_);
lean_closure_set(v___f_3425_, 6, v___x_2962_);
lean_closure_set(v___f_3425_, 7, v___x_3423_);
lean_closure_set(v___f_3425_, 8, v___x_3424_);
v___x_3426_ = lean_alloc_closure((void*)(l_Lean_withImporting___boxed), 3, 2);
lean_closure_set(v___x_3426_, 0, lean_box(0));
lean_closure_set(v___x_3426_, 1, v___f_3425_);
v___x_3427_ = lean_box(0);
v___x_3428_ = l_Lean_profileitIOUnsafe___redArg(v___x_3252_, v___x_2962_, v___x_3426_, v___x_3427_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_a_3429_; lean_object* v___x_3430_; lean_object* v_ext_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_a_3429_);
lean_dec_ref_known(v___x_3428_, 1);
v___x_3430_ = l_Lean_Compiler_CSimp_ext;
v_ext_3431_ = lean_ctor_get(v___x_3430_, 1);
lean_inc(v_name_2931_);
v___x_3432_ = l_Lean_Environment_setMainModule(v_a_3429_, v_name_2931_);
lean_inc_ref(v_ext_3431_);
v___x_3433_ = l_main___elam__0___redArg(v___x_3427_, v___x_2949_, v_ext_3431_, v___x_3432_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v_a_3434_; lean_object* v___x_3435_; lean_object* v_ext_3436_; lean_object* v___x_3437_; 
v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
lean_inc(v_a_3434_);
lean_dec_ref_known(v___x_3433_, 1);
v___x_3435_ = l_Lean_Meta_instanceExtension;
v_ext_3436_ = lean_ctor_get(v___x_3435_, 1);
lean_inc_ref(v_ext_3436_);
v___x_3437_ = l_main___elam__0___redArg(v___x_3427_, v___x_2949_, v_ext_3436_, v_a_3434_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3438_);
lean_dec_ref_known(v___x_3437_, 1);
v___x_3439_ = l_Lean_classExtension;
v___x_3440_ = l_main___elam__0___redArg(v___x_3427_, v___x_2950_, v___x_3439_, v_a_3438_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v_a_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
lean_inc(v_a_3441_);
lean_dec_ref_known(v___x_3440_, 1);
v___x_3442_ = l_Lean_Meta_Match_Extension_extension;
v___x_3443_ = l_main___elam__0___redArg(v___x_3427_, v___x_2951_, v___x_3442_, v_a_3441_);
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3472_; 
v_a_3444_ = lean_ctor_get(v___x_3443_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3446_ = v___x_3443_;
v_isShared_3447_ = v_isSharedCheck_3472_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3443_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3472_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3448_; 
v___x_3448_ = l_Lean_Environment_getModuleIdx_x3f(v_a_3444_, v_name_2931_);
if (lean_obj_tag(v___x_3448_) == 1)
{
lean_object* v_val_3449_; lean_object* v___x_3450_; uint8_t v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; uint8_t v___x_3455_; 
lean_del_object(v___x_3446_);
v_val_3449_ = lean_ctor_get(v___x_3448_, 0);
lean_inc(v_val_3449_);
lean_dec_ref_known(v___x_3448_, 1);
v___x_3450_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_3451_ = 0;
v___x_3452_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2952_, v___x_3450_, v_a_3444_, v_val_3449_, v___x_3451_);
v___x_3453_ = lean_array_get_size(v___x_3452_);
v___x_3454_ = ((lean_object*)(l_main___closed__33));
v___x_3455_ = lean_nat_dec_lt(v___x_2961_, v___x_3453_);
if (v___x_3455_ == 0)
{
lean_dec_ref(v___x_3452_);
v___y_3400_ = v___x_3427_;
v___y_3401_ = v_val_3449_;
v___y_3402_ = v_a_3444_;
v___y_3403_ = v___x_3427_;
v___y_3404_ = v___x_3451_;
v___y_3405_ = v___x_3454_;
goto v___jp_3399_;
}
else
{
uint8_t v___x_3456_; 
v___x_3456_ = lean_nat_dec_le(v___x_3453_, v___x_3453_);
if (v___x_3456_ == 0)
{
if (v___x_3455_ == 0)
{
lean_dec_ref(v___x_3452_);
v___y_3400_ = v___x_3427_;
v___y_3401_ = v_val_3449_;
v___y_3402_ = v_a_3444_;
v___y_3403_ = v___x_3427_;
v___y_3404_ = v___x_3451_;
v___y_3405_ = v___x_3454_;
goto v___jp_3399_;
}
else
{
size_t v___x_3457_; size_t v___x_3458_; lean_object* v___x_3459_; 
v___x_3457_ = ((size_t)0ULL);
v___x_3458_ = lean_usize_of_nat(v___x_3453_);
lean_inc(v_a_3444_);
v___x_3459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3444_, v___x_3452_, v___x_3457_, v___x_3458_, v___x_3454_);
lean_dec_ref(v___x_3452_);
v___y_3400_ = v___x_3427_;
v___y_3401_ = v_val_3449_;
v___y_3402_ = v_a_3444_;
v___y_3403_ = v___x_3427_;
v___y_3404_ = v___x_3451_;
v___y_3405_ = v___x_3459_;
goto v___jp_3399_;
}
}
else
{
size_t v___x_3460_; size_t v___x_3461_; lean_object* v___x_3462_; 
v___x_3460_ = ((size_t)0ULL);
v___x_3461_ = lean_usize_of_nat(v___x_3453_);
lean_inc(v_a_3444_);
v___x_3462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3444_, v___x_3452_, v___x_3460_, v___x_3461_, v___x_3454_);
lean_dec_ref(v___x_3452_);
v___y_3400_ = v___x_3427_;
v___y_3401_ = v_val_3449_;
v___y_3402_ = v_a_3444_;
v___y_3403_ = v___x_3427_;
v___y_3404_ = v___x_3451_;
v___y_3405_ = v___x_3462_;
goto v___jp_3399_;
}
}
}
else
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3470_; 
lean_dec(v___x_3448_);
lean_dec(v_a_3444_);
lean_dec_ref(v___x_2962_);
lean_del_object(v___x_2947_);
lean_dec(v_fst_2944_);
lean_dec(v_head_2924_);
lean_dec(v_head_2923_);
v___x_3463_ = ((lean_object*)(l_main___closed__34));
v___x_3464_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2931_, v___x_2958_);
v___x_3465_ = lean_string_append(v___x_3463_, v___x_3464_);
lean_dec_ref(v___x_3464_);
v___x_3466_ = ((lean_object*)(l_main___closed__35));
v___x_3467_ = lean_string_append(v___x_3465_, v___x_3466_);
v___x_3468_ = lean_mk_io_user_error(v___x_3467_);
if (v_isShared_3447_ == 0)
{
lean_ctor_set_tag(v___x_3446_, 1);
lean_ctor_set(v___x_3446_, 0, v___x_3468_);
v___x_3470_ = v___x_3446_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v___x_3468_);
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
lean_dec_ref(v___x_2962_);
lean_del_object(v___x_2947_);
lean_dec(v_fst_2944_);
lean_dec(v_name_2931_);
lean_dec(v_head_2924_);
lean_dec(v_head_2923_);
v_a_3473_ = lean_ctor_get(v___x_3443_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3443_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3443_);
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
lean_dec_ref(v___x_2962_);
lean_del_object(v___x_2947_);
lean_dec(v_fst_2944_);
lean_dec(v_name_2931_);
lean_dec(v_head_2924_);
lean_dec(v_head_2923_);
v_a_3481_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3483_ = v___x_3440_;
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3440_);
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
else
{
lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3496_; 
lean_dec_ref(v___x_2962_);
lean_del_object(v___x_2947_);
lean_dec(v_fst_2944_);
lean_dec(v_name_2931_);
lean_dec(v_head_2924_);
lean_dec(v_head_2923_);
v_a_3489_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3491_ = v___x_3437_;
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_dec(v___x_3437_);
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
else
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
lean_dec_ref(v___x_2962_);
lean_del_object(v___x_2947_);
lean_dec(v_fst_2944_);
lean_dec(v_name_2931_);
lean_dec(v_head_2924_);
lean_dec(v_head_2923_);
v_a_3497_ = lean_ctor_get(v___x_3433_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___x_3433_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3433_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_dec_ref(v___x_2962_);
lean_del_object(v___x_2947_);
lean_dec(v_fst_2944_);
lean_dec(v_name_2931_);
lean_dec(v_head_2924_);
lean_dec(v_head_2923_);
v_a_3505_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3428_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3428_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
}
}
else
{
lean_object* v_a_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3522_; 
lean_dec(v_a_2939_);
lean_dec(v_name_2931_);
lean_dec(v_head_2924_);
lean_dec(v_head_2923_);
v_a_3515_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3517_ = v___x_2943_;
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_a_3515_);
lean_dec(v___x_2943_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3520_; 
if (v_isShared_3518_ == 0)
{
v___x_3520_ = v___x_3517_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_a_3515_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
}
}
else
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3530_; 
lean_dec(v_a_2939_);
lean_dec(v_name_2931_);
lean_dec(v_head_2924_);
lean_dec(v_head_2923_);
v_a_3523_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3525_ = v___x_2940_;
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_2940_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3528_; 
if (v_isShared_3526_ == 0)
{
v___x_3528_ = v___x_3525_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3523_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
else
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3538_; 
lean_dec(v_name_2931_);
lean_dec(v_head_2924_);
lean_dec(v_head_2923_);
v_a_3531_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3533_ = v___x_2938_;
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_2938_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3536_; 
if (v_isShared_3534_ == 0)
{
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3531_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
}
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
lean_del_object(v___x_2927_);
lean_dec(v_tail_2925_);
lean_dec(v_head_2924_);
lean_dec(v_head_2923_);
v_a_3540_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_2929_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_2929_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3540_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_tail_2920_, 2);
lean_dec(v_tail_2921_);
lean_dec_ref_known(v_args_2895_, 2);
goto v___jp_2897_;
}
}
else
{
lean_dec(v_tail_2920_);
lean_dec_ref_known(v_args_2895_, 2);
goto v___jp_2897_;
}
}
else
{
lean_dec(v_args_2895_);
goto v___jp_2897_;
}
v___jp_2897_:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = ((lean_object*)(l_main___closed__0));
v___x_2899_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_2898_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2907_; 
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2907_ == 0)
{
lean_object* v_unused_2908_; 
v_unused_2908_ = lean_ctor_get(v___x_2899_, 0);
lean_dec(v_unused_2908_);
v___x_2901_ = v___x_2899_;
v_isShared_2902_ = v_isSharedCheck_2907_;
goto v_resetjp_2900_;
}
else
{
lean_dec(v___x_2899_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2907_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2903_; lean_object* v___x_2905_; 
v___x_2903_ = l_main___boxed__const__1;
if (v_isShared_2902_ == 0)
{
lean_ctor_set(v___x_2901_, 0, v___x_2903_);
v___x_2905_ = v___x_2901_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v___x_2903_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
else
{
lean_object* v_a_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2916_; 
v_a_2909_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2911_ = v___x_2899_;
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_a_2909_);
lean_dec(v___x_2899_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2914_; 
if (v_isShared_2912_ == 0)
{
v___x_2914_ = v___x_2911_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_a_2909_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
v___jp_2917_:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2918_ = l_main___boxed__const__2;
v___x_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
return v___x_2919_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_3549_, lean_object* v_a_3550_){
_start:
{
lean_object* v_res_3551_; 
v_res_3551_ = _lean_main(v_args_3549_);
return v_res_3551_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object* v_as_3552_, lean_object* v_as_x27_3553_, lean_object* v_b_3554_, lean_object* v_a_3555_){
_start:
{
lean_object* v___x_3557_; 
v___x_3557_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_3553_, v_b_3554_);
return v___x_3557_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object* v_as_3558_, lean_object* v_as_x27_3559_, lean_object* v_b_3560_, lean_object* v_a_3561_, lean_object* v___y_3562_){
_start:
{
lean_object* v_res_3563_; 
v_res_3563_ = l_List_forIn_x27_loop___at___00main_spec__1(v_as_3558_, v_as_x27_3559_, v_b_3560_, v_a_3561_);
lean_dec(v_as_x27_3559_);
lean_dec(v_as_3558_);
return v_res_3563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(lean_object* v___y_3564_, lean_object* v___y_3565_){
_start:
{
lean_object* v___x_3567_; 
v___x_3567_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_3565_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___boxed(lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_){
_start:
{
lean_object* v_res_3571_; 
v_res_3571_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(v___y_3568_, v___y_3569_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
return v_res_3571_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(lean_object* v_00_u03b2_3572_, lean_object* v_m_3573_, lean_object* v_a_3574_, lean_object* v_fallback_3575_){
_start:
{
lean_object* v___x_3576_; 
v___x_3576_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_3573_, v_a_3574_, v_fallback_3575_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___boxed(lean_object* v_00_u03b2_3577_, lean_object* v_m_3578_, lean_object* v_a_3579_, lean_object* v_fallback_3580_){
_start:
{
lean_object* v_res_3581_; 
v_res_3581_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(v_00_u03b2_3577_, v_m_3578_, v_a_3579_, v_fallback_3580_);
lean_dec(v_fallback_3580_);
lean_dec_ref(v_a_3579_);
lean_dec_ref(v_m_3578_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18(lean_object* v_00_u03b2_3582_, lean_object* v_m_3583_, lean_object* v_a_3584_, lean_object* v_b_3585_){
_start:
{
lean_object* v___x_3586_; 
v___x_3586_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_m_3583_, v_a_3584_, v_b_3585_);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(lean_object* v_n_3587_, lean_object* v_as_3588_, lean_object* v_lo_3589_, lean_object* v_hi_3590_, lean_object* v_w_3591_, lean_object* v_hlo_3592_, lean_object* v_hhi_3593_){
_start:
{
lean_object* v___x_3594_; 
v___x_3594_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_3587_, v_as_3588_, v_lo_3589_, v_hi_3590_);
return v___x_3594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___boxed(lean_object* v_n_3595_, lean_object* v_as_3596_, lean_object* v_lo_3597_, lean_object* v_hi_3598_, lean_object* v_w_3599_, lean_object* v_hlo_3600_, lean_object* v_hhi_3601_){
_start:
{
lean_object* v_res_3602_; 
v_res_3602_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(v_n_3595_, v_as_3596_, v_lo_3597_, v_hi_3598_, v_w_3599_, v_hlo_3600_, v_hhi_3601_);
lean_dec(v_hi_3598_);
lean_dec(v_n_3595_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(lean_object* v_00_u03b2_3603_, lean_object* v_a_3604_, lean_object* v_fallback_3605_, lean_object* v_x_3606_){
_start:
{
lean_object* v___x_3607_; 
v___x_3607_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_3604_, v_fallback_3605_, v_x_3606_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3608_, lean_object* v_a_3609_, lean_object* v_fallback_3610_, lean_object* v_x_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(v_00_u03b2_3608_, v_a_3609_, v_fallback_3610_, v_x_3611_);
lean_dec(v_x_3611_);
lean_dec(v_fallback_3610_);
lean_dec_ref(v_a_3609_);
return v_res_3612_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(lean_object* v_00_u03b2_3613_, lean_object* v_a_3614_, lean_object* v_x_3615_){
_start:
{
uint8_t v___x_3616_; 
v___x_3616_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_3614_, v_x_3615_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___boxed(lean_object* v_00_u03b2_3617_, lean_object* v_a_3618_, lean_object* v_x_3619_){
_start:
{
uint8_t v_res_3620_; lean_object* v_r_3621_; 
v_res_3620_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(v_00_u03b2_3617_, v_a_3618_, v_x_3619_);
lean_dec(v_x_3619_);
lean_dec_ref(v_a_3618_);
v_r_3621_ = lean_box(v_res_3620_);
return v_r_3621_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24(lean_object* v_00_u03b2_3622_, lean_object* v_data_3623_){
_start:
{
lean_object* v___x_3624_; 
v___x_3624_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_data_3623_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25(lean_object* v_00_u03b2_3625_, lean_object* v_a_3626_, lean_object* v_b_3627_, lean_object* v_x_3628_){
_start:
{
lean_object* v___x_3629_; 
v___x_3629_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_3626_, v_b_3627_, v_x_3628_);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(lean_object* v_n_3630_, lean_object* v_lo_3631_, lean_object* v_hi_3632_, lean_object* v_hhi_3633_, lean_object* v_pivot_3634_, lean_object* v_as_3635_, lean_object* v_i_3636_, lean_object* v_k_3637_, lean_object* v_ilo_3638_, lean_object* v_ik_3639_, lean_object* v_w_3640_){
_start:
{
lean_object* v___x_3641_; 
v___x_3641_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_3632_, v_pivot_3634_, v_as_3635_, v_i_3636_, v_k_3637_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___boxed(lean_object* v_n_3642_, lean_object* v_lo_3643_, lean_object* v_hi_3644_, lean_object* v_hhi_3645_, lean_object* v_pivot_3646_, lean_object* v_as_3647_, lean_object* v_i_3648_, lean_object* v_k_3649_, lean_object* v_ilo_3650_, lean_object* v_ik_3651_, lean_object* v_w_3652_){
_start:
{
lean_object* v_res_3653_; 
v_res_3653_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(v_n_3642_, v_lo_3643_, v_hi_3644_, v_hhi_3645_, v_pivot_3646_, v_as_3647_, v_i_3648_, v_k_3649_, v_ilo_3650_, v_ik_3651_, v_w_3652_);
lean_dec_ref(v_pivot_3646_);
lean_dec(v_hi_3644_);
lean_dec(v_lo_3643_);
lean_dec(v_n_3642_);
return v_res_3653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(lean_object* v_as_3654_, size_t v_sz_3655_, size_t v_i_3656_, lean_object* v_b_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
lean_object* v___x_3661_; 
v___x_3661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_3654_, v_sz_3655_, v_i_3656_, v_b_3657_, v___y_3658_);
return v___x_3661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___boxed(lean_object* v_as_3662_, lean_object* v_sz_3663_, lean_object* v_i_3664_, lean_object* v_b_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_){
_start:
{
size_t v_sz_boxed_3669_; size_t v_i_boxed_3670_; lean_object* v_res_3671_; 
v_sz_boxed_3669_ = lean_unbox_usize(v_sz_3663_);
lean_dec(v_sz_3663_);
v_i_boxed_3670_ = lean_unbox_usize(v_i_3664_);
lean_dec(v_i_3664_);
v_res_3671_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(v_as_3662_, v_sz_boxed_3669_, v_i_boxed_3670_, v_b_3665_, v___y_3666_, v___y_3667_);
lean_dec(v___y_3667_);
lean_dec_ref(v___y_3666_);
lean_dec_ref(v_as_3662_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35(lean_object* v_00_u03b2_3672_, lean_object* v_i_3673_, lean_object* v_source_3674_, lean_object* v_target_3675_){
_start:
{
lean_object* v___x_3676_; 
v___x_3676_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v_i_3673_, v_source_3674_, v_target_3675_);
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(uint8_t v___x_3677_, lean_object* v_as_3678_, size_t v_sz_3679_, size_t v_i_3680_, lean_object* v_b_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_){
_start:
{
lean_object* v___x_3685_; 
v___x_3685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_3677_, v_as_3678_, v_sz_3679_, v_i_3680_, v_b_3681_, v___y_3682_);
return v___x_3685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___boxed(lean_object* v___x_3686_, lean_object* v_as_3687_, lean_object* v_sz_3688_, lean_object* v_i_3689_, lean_object* v_b_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_){
_start:
{
uint8_t v___x_41215__boxed_3694_; size_t v_sz_boxed_3695_; size_t v_i_boxed_3696_; lean_object* v_res_3697_; 
v___x_41215__boxed_3694_ = lean_unbox(v___x_3686_);
v_sz_boxed_3695_ = lean_unbox_usize(v_sz_3688_);
lean_dec(v_sz_3688_);
v_i_boxed_3696_ = lean_unbox_usize(v_i_3689_);
lean_dec(v_i_3689_);
v_res_3697_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(v___x_41215__boxed_3694_, v_as_3687_, v_sz_boxed_3695_, v_i_boxed_3696_, v_b_3690_, v___y_3691_, v___y_3692_);
lean_dec(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec_ref(v_as_3687_);
return v_res_3697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(lean_object* v_as_3698_, size_t v_sz_3699_, size_t v_i_3700_, lean_object* v_b_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
lean_object* v___x_3705_; 
v___x_3705_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_3698_, v_sz_3699_, v_i_3700_, v_b_3701_, v___y_3702_);
return v___x_3705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___boxed(lean_object* v_as_3706_, lean_object* v_sz_3707_, lean_object* v_i_3708_, lean_object* v_b_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
size_t v_sz_boxed_3713_; size_t v_i_boxed_3714_; lean_object* v_res_3715_; 
v_sz_boxed_3713_ = lean_unbox_usize(v_sz_3707_);
lean_dec(v_sz_3707_);
v_i_boxed_3714_ = lean_unbox_usize(v_i_3708_);
lean_dec(v_i_3708_);
v_res_3715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(v_as_3706_, v_sz_boxed_3713_, v_i_boxed_3714_, v_b_3709_, v___y_3710_, v___y_3711_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec_ref(v_as_3706_);
return v_res_3715_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44(lean_object* v_00_u03b2_3716_, lean_object* v_x_3717_, lean_object* v_x_3718_){
_start:
{
lean_object* v___x_3719_; 
v___x_3719_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_x_3717_, v_x_3718_);
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(uint8_t v___x_3720_, lean_object* v_as_3721_, size_t v_sz_3722_, size_t v_i_3723_, lean_object* v_b_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_){
_start:
{
lean_object* v___x_3728_; 
v___x_3728_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_3720_, v_as_3721_, v_sz_3722_, v_i_3723_, v_b_3724_, v___y_3725_);
return v___x_3728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___boxed(lean_object* v___x_3729_, lean_object* v_as_3730_, lean_object* v_sz_3731_, lean_object* v_i_3732_, lean_object* v_b_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_){
_start:
{
uint8_t v___x_41246__boxed_3737_; size_t v_sz_boxed_3738_; size_t v_i_boxed_3739_; lean_object* v_res_3740_; 
v___x_41246__boxed_3737_ = lean_unbox(v___x_3729_);
v_sz_boxed_3738_ = lean_unbox_usize(v_sz_3731_);
lean_dec(v_sz_3731_);
v_i_boxed_3739_ = lean_unbox_usize(v_i_3732_);
lean_dec(v_i_3732_);
v_res_3740_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(v___x_41246__boxed_3737_, v_as_3730_, v_sz_boxed_3738_, v_i_boxed_3739_, v_b_3733_, v___y_3734_, v___y_3735_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
lean_dec_ref(v_as_3730_);
return v_res_3740_;
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
