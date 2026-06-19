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
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_get_num_heartbeats();
extern lean_object* l_Lean_diagnostics;
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Compiler_LCNF_emitC(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_io_prim_handle_write(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
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
static const lean_string_object l_main___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "internal exception "};
static const lean_object* l_main___lam__1___closed__0 = (const lean_object*)&l_main___lam__1___closed__0_value;
static const lean_string_object l_main___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l_main___lam__1___closed__1 = (const lean_object*)&l_main___lam__1___closed__1_value;
static const lean_string_object l_main___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " (unknown)"};
static const lean_object* l_main___lam__1___closed__2 = (const lean_object*)&l_main___lam__1___closed__2_value;
LEAN_EXPORT lean_object* l_main___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
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
lean_object* v___x_328_; lean_object* v___x_20119__overap_329_; lean_object* v___x_330_; 
v___x_328_ = lean_obj_once(&l_panic___at___00main_spec__5___closed__0, &l_panic___at___00main_spec__5___closed__0_once, _init_l_panic___at___00main_spec__5___closed__0);
v___x_20119__overap_329_ = lean_panic_fn_borrowed(v___x_328_, v_msg_326_);
v___x_330_ = lean_apply_1(v___x_20119__overap_329_, lean_box(0));
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
uint8_t v___x_36296__boxed_504_; uint8_t v___y_36298__boxed_505_; uint8_t v___x_36300__boxed_506_; uint8_t v___x_36301__boxed_507_; lean_object* v_res_508_; 
v___x_36296__boxed_504_ = lean_unbox(v___x_496_);
v___y_36298__boxed_505_ = lean_unbox(v___y_498_);
v___x_36300__boxed_506_ = lean_unbox(v___x_501_);
v___x_36301__boxed_507_ = lean_unbox(v___x_502_);
v_res_508_ = l_main___lam__0(v___x_494_, v___x_495_, v___x_36296__boxed_504_, v___x_497_, v___y_36298__boxed_505_, v_name_499_, v___x_500_, v___x_36300__boxed_506_, v___x_36301__boxed_507_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_main___lam__1(lean_object* v___x_512_, lean_object* v___x_513_, lean_object* v___x_514_, lean_object* v_name_515_, lean_object* v_a_516_, uint8_t v___x_517_, lean_object* v___x_518_, lean_object* v_head_519_, lean_object* v___x_520_, lean_object* v___x_521_, lean_object* v___x_522_, lean_object* v___x_523_, lean_object* v___x_524_, lean_object* v___x_525_, lean_object* v___x_526_, lean_object* v___x_527_, uint8_t v___x_528_, uint8_t v___x_529_){
_start:
{
lean_object* v_a_532_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v_env_539_; lean_object* v___x_540_; uint8_t v___x_541_; lean_object* v_fileName_543_; lean_object* v_fileMap_544_; lean_object* v_currRecDepth_545_; lean_object* v_ref_546_; lean_object* v_currNamespace_547_; lean_object* v_openDecls_548_; lean_object* v_initHeartbeats_549_; lean_object* v_maxHeartbeats_550_; lean_object* v_quotContext_551_; lean_object* v_currMacroScope_552_; lean_object* v_cancelTk_x3f_553_; uint8_t v_suppressElabErrors_554_; lean_object* v_inheritedTraceOptions_555_; lean_object* v___y_556_; uint8_t v___y_588_; uint8_t v___x_608_; 
v___x_535_ = lean_io_get_num_heartbeats();
v___x_536_ = lean_st_mk_ref(v___x_512_);
v___x_537_ = lean_st_ref_get(v___x_513_);
v___x_538_ = lean_st_ref_get(v___x_536_);
v_env_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc_ref(v_env_539_);
lean_dec(v___x_538_);
v___x_540_ = l_Lean_diagnostics;
v___x_541_ = l_Lean_Option_get___at___00main_spec__8(v___x_514_, v___x_540_);
v___x_608_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_539_);
lean_dec_ref(v_env_539_);
if (v___x_608_ == 0)
{
if (v___x_541_ == 0)
{
v___y_588_ = v___x_529_;
goto v___jp_587_;
}
else
{
v___y_588_ = v___x_608_;
goto v___jp_587_;
}
}
else
{
v___y_588_ = v___x_541_;
goto v___jp_587_;
}
v___jp_531_:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_mk_io_user_error(v_a_532_);
v___x_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
v___jp_542_:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_557_ = l_Lean_maxRecDepth;
v___x_558_ = l_Lean_Option_get___at___00main_spec__9(v___x_514_, v___x_557_);
v___x_559_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_559_, 0, v_fileName_543_);
lean_ctor_set(v___x_559_, 1, v_fileMap_544_);
lean_ctor_set(v___x_559_, 2, v___x_514_);
lean_ctor_set(v___x_559_, 3, v_currRecDepth_545_);
lean_ctor_set(v___x_559_, 4, v___x_558_);
lean_ctor_set(v___x_559_, 5, v_ref_546_);
lean_ctor_set(v___x_559_, 6, v_currNamespace_547_);
lean_ctor_set(v___x_559_, 7, v_openDecls_548_);
lean_ctor_set(v___x_559_, 8, v_initHeartbeats_549_);
lean_ctor_set(v___x_559_, 9, v_maxHeartbeats_550_);
lean_ctor_set(v___x_559_, 10, v_quotContext_551_);
lean_ctor_set(v___x_559_, 11, v_currMacroScope_552_);
lean_ctor_set(v___x_559_, 12, v_cancelTk_x3f_553_);
lean_ctor_set(v___x_559_, 13, v_inheritedTraceOptions_555_);
lean_ctor_set_uint8(v___x_559_, sizeof(void*)*14, v___x_541_);
lean_ctor_set_uint8(v___x_559_, sizeof(void*)*14 + 1, v_suppressElabErrors_554_);
v___x_560_ = l_Lean_Compiler_LCNF_emitC(v_name_515_, v___x_559_, v___y_556_);
lean_dec(v___y_556_);
lean_dec_ref_known(v___x_559_, 14);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_a_561_);
lean_dec_ref_known(v___x_560_, 1);
v___x_562_ = lean_st_ref_get(v___x_536_);
lean_dec(v___x_536_);
lean_dec(v___x_562_);
v___x_563_ = lean_string_to_utf8(v_a_561_);
lean_dec(v_a_561_);
v___x_564_ = lean_io_prim_handle_write(v_a_516_, v___x_563_);
lean_dec_ref(v___x_563_);
return v___x_564_;
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_586_; 
lean_dec(v___x_536_);
v_a_565_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_586_ == 0)
{
v___x_567_ = v___x_560_;
v_isShared_568_ = v_isSharedCheck_586_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_560_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_586_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
if (lean_obj_tag(v_a_565_) == 0)
{
lean_object* v_msg_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_573_; 
v_msg_569_ = lean_ctor_get(v_a_565_, 1);
lean_inc_ref(v_msg_569_);
lean_dec_ref_known(v_a_565_, 2);
v___x_570_ = l_Lean_MessageData_toString(v_msg_569_);
v___x_571_ = lean_mk_io_user_error(v___x_570_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_571_);
v___x_573_ = v___x_567_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_571_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
else
{
lean_object* v_id_575_; lean_object* v___x_576_; 
lean_del_object(v___x_567_);
v_id_575_ = lean_ctor_get(v_a_565_, 0);
lean_inc(v_id_575_);
lean_dec_ref_known(v_a_565_, 2);
v___x_576_ = l_Lean_InternalExceptionId_getName(v_id_575_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
lean_dec(v_id_575_);
v_a_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_a_577_);
lean_dec_ref_known(v___x_576_, 1);
v___x_578_ = ((lean_object*)(l_main___lam__1___closed__0));
v___x_579_ = l_Lean_Name_toString(v_a_577_, v___x_517_);
v___x_580_ = lean_string_append(v___x_578_, v___x_579_);
lean_dec_ref(v___x_579_);
v_a_532_ = v___x_580_;
goto v___jp_531_;
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec_ref_known(v___x_576_, 1);
v___x_581_ = ((lean_object*)(l_main___lam__1___closed__1));
v___x_582_ = l_Nat_reprFast(v_id_575_);
v___x_583_ = lean_string_append(v___x_581_, v___x_582_);
lean_dec_ref(v___x_582_);
v___x_584_ = ((lean_object*)(l_main___lam__1___closed__2));
v___x_585_ = lean_string_append(v___x_583_, v___x_584_);
v_a_532_ = v___x_585_;
goto v___jp_531_;
}
}
}
}
}
v___jp_587_:
{
if (v___y_588_ == 0)
{
lean_object* v___x_589_; lean_object* v_env_590_; lean_object* v_nextMacroScope_591_; lean_object* v_ngen_592_; lean_object* v_auxDeclNGen_593_; lean_object* v_traceState_594_; lean_object* v_messages_595_; lean_object* v_infoState_596_; lean_object* v_snapshotTasks_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_606_; 
v___x_589_ = lean_st_ref_take(v___x_536_);
v_env_590_ = lean_ctor_get(v___x_589_, 0);
v_nextMacroScope_591_ = lean_ctor_get(v___x_589_, 1);
v_ngen_592_ = lean_ctor_get(v___x_589_, 2);
v_auxDeclNGen_593_ = lean_ctor_get(v___x_589_, 3);
v_traceState_594_ = lean_ctor_get(v___x_589_, 4);
v_messages_595_ = lean_ctor_get(v___x_589_, 6);
v_infoState_596_ = lean_ctor_get(v___x_589_, 7);
v_snapshotTasks_597_ = lean_ctor_get(v___x_589_, 8);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; 
v_unused_607_ = lean_ctor_get(v___x_589_, 5);
lean_dec(v_unused_607_);
v___x_599_ = v___x_589_;
v_isShared_600_ = v_isSharedCheck_606_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_snapshotTasks_597_);
lean_inc(v_infoState_596_);
lean_inc(v_messages_595_);
lean_inc(v_traceState_594_);
lean_inc(v_auxDeclNGen_593_);
lean_inc(v_ngen_592_);
lean_inc(v_nextMacroScope_591_);
lean_inc(v_env_590_);
lean_dec(v___x_589_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_606_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_601_ = l_Lean_Kernel_enableDiag(v_env_590_, v___x_541_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 5, v___x_518_);
lean_ctor_set(v___x_599_, 0, v___x_601_);
v___x_603_ = v___x_599_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_601_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_nextMacroScope_591_);
lean_ctor_set(v_reuseFailAlloc_605_, 2, v_ngen_592_);
lean_ctor_set(v_reuseFailAlloc_605_, 3, v_auxDeclNGen_593_);
lean_ctor_set(v_reuseFailAlloc_605_, 4, v_traceState_594_);
lean_ctor_set(v_reuseFailAlloc_605_, 5, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_605_, 6, v_messages_595_);
lean_ctor_set(v_reuseFailAlloc_605_, 7, v_infoState_596_);
lean_ctor_set(v_reuseFailAlloc_605_, 8, v_snapshotTasks_597_);
v___x_603_ = v_reuseFailAlloc_605_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
lean_object* v___x_604_; 
v___x_604_ = lean_st_ref_set(v___x_536_, v___x_603_);
lean_inc(v___x_536_);
lean_inc(v___x_523_);
v_fileName_543_ = v_head_519_;
v_fileMap_544_ = v___x_520_;
v_currRecDepth_545_ = v___x_521_;
v_ref_546_ = v___x_522_;
v_currNamespace_547_ = v___x_523_;
v_openDecls_548_ = v___x_524_;
v_initHeartbeats_549_ = v___x_535_;
v_maxHeartbeats_550_ = v___x_525_;
v_quotContext_551_ = v___x_523_;
v_currMacroScope_552_ = v___x_526_;
v_cancelTk_x3f_553_ = v___x_527_;
v_suppressElabErrors_554_ = v___x_528_;
v_inheritedTraceOptions_555_ = v___x_537_;
v___y_556_ = v___x_536_;
goto v___jp_542_;
}
}
}
else
{
lean_dec_ref(v___x_518_);
lean_inc(v___x_536_);
lean_inc(v___x_523_);
v_fileName_543_ = v_head_519_;
v_fileMap_544_ = v___x_520_;
v_currRecDepth_545_ = v___x_521_;
v_ref_546_ = v___x_522_;
v_currNamespace_547_ = v___x_523_;
v_openDecls_548_ = v___x_524_;
v_initHeartbeats_549_ = v___x_535_;
v_maxHeartbeats_550_ = v___x_525_;
v_quotContext_551_ = v___x_523_;
v_currMacroScope_552_ = v___x_526_;
v_cancelTk_x3f_553_ = v___x_527_;
v_suppressElabErrors_554_ = v___x_528_;
v_inheritedTraceOptions_555_ = v___x_537_;
v___y_556_ = v___x_536_;
goto v___jp_542_;
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__1___boxed(lean_object** _args){
lean_object* v___x_609_ = _args[0];
lean_object* v___x_610_ = _args[1];
lean_object* v___x_611_ = _args[2];
lean_object* v_name_612_ = _args[3];
lean_object* v_a_613_ = _args[4];
lean_object* v___x_614_ = _args[5];
lean_object* v___x_615_ = _args[6];
lean_object* v_head_616_ = _args[7];
lean_object* v___x_617_ = _args[8];
lean_object* v___x_618_ = _args[9];
lean_object* v___x_619_ = _args[10];
lean_object* v___x_620_ = _args[11];
lean_object* v___x_621_ = _args[12];
lean_object* v___x_622_ = _args[13];
lean_object* v___x_623_ = _args[14];
lean_object* v___x_624_ = _args[15];
lean_object* v___x_625_ = _args[16];
lean_object* v___x_626_ = _args[17];
lean_object* v___y_627_ = _args[18];
_start:
{
uint8_t v___x_36380__boxed_628_; uint8_t v___x_36391__boxed_629_; uint8_t v___x_36392__boxed_630_; lean_object* v_res_631_; 
v___x_36380__boxed_628_ = lean_unbox(v___x_614_);
v___x_36391__boxed_629_ = lean_unbox(v___x_625_);
v___x_36392__boxed_630_ = lean_unbox(v___x_626_);
v_res_631_ = l_main___lam__1(v___x_609_, v___x_610_, v___x_611_, v_name_612_, v_a_613_, v___x_36380__boxed_628_, v___x_615_, v_head_616_, v___x_617_, v___x_618_, v___x_619_, v___x_620_, v___x_621_, v___x_622_, v___x_623_, v___x_624_, v___x_36391__boxed_629_, v___x_36392__boxed_630_);
lean_dec(v_a_613_);
lean_dec(v___x_610_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(lean_object* v_s_632_){
_start:
{
lean_object* v___x_634_; lean_object* v_putStr_635_; lean_object* v___x_636_; 
v___x_634_ = lean_get_stderr();
v_putStr_635_ = lean_ctor_get(v___x_634_, 4);
lean_inc_ref(v_putStr_635_);
lean_dec_ref(v___x_634_);
v___x_636_ = lean_apply_2(v_putStr_635_, v_s_632_, lean_box(0));
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8___boxed(lean_object* v_s_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v_s_637_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6(lean_object* v_s_640_){
_start:
{
uint32_t v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_642_ = 10;
v___x_643_ = lean_string_push(v_s_640_, v___x_642_);
v___x_644_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v___x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6___boxed(lean_object* v_s_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_IO_eprintln___at___00main_spec__6(v_s_645_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(lean_object* v_o_651_, lean_object* v_k_652_, lean_object* v_v_653_){
_start:
{
lean_object* v_map_654_; uint8_t v_hasTrace_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_669_; 
v_map_654_ = lean_ctor_get(v_o_651_, 0);
v_hasTrace_655_ = lean_ctor_get_uint8(v_o_651_, sizeof(void*)*1);
v_isSharedCheck_669_ = !lean_is_exclusive(v_o_651_);
if (v_isSharedCheck_669_ == 0)
{
v___x_657_ = v_o_651_;
v_isShared_658_ = v_isSharedCheck_669_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_map_654_);
lean_dec(v_o_651_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_669_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_659_, 0, v_v_653_);
lean_inc(v_k_652_);
v___x_660_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_652_, v___x_659_, v_map_654_);
if (v_hasTrace_655_ == 0)
{
lean_object* v___x_661_; uint8_t v___x_662_; lean_object* v___x_664_; 
v___x_661_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_662_ = l_Lean_Name_isPrefixOf(v___x_661_, v_k_652_);
lean_dec(v_k_652_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_660_);
v___x_664_ = v___x_657_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_660_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_ctor_set_uint8(v___x_664_, sizeof(void*)*1, v___x_662_);
return v___x_664_;
}
}
else
{
lean_object* v___x_667_; 
lean_dec(v_k_652_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_660_);
v___x_667_ = v___x_657_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_660_);
lean_ctor_set_uint8(v_reuseFailAlloc_668_, sizeof(void*)*1, v_hasTrace_655_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00main_spec__3(lean_object* v_opts_670_, lean_object* v_opt_671_, lean_object* v_val_672_){
_start:
{
lean_object* v_name_673_; lean_object* v___x_674_; 
v_name_673_ = lean_ctor_get(v_opt_671_, 0);
lean_inc(v_name_673_);
lean_dec_ref(v_opt_671_);
v___x_674_ = l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(v_opts_670_, v_name_673_, v_val_672_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object* v___y_676_, lean_object* v_as_677_, size_t v_i_678_, size_t v_stop_679_, lean_object* v_b_680_){
_start:
{
lean_object* v___y_682_; uint8_t v___x_686_; 
v___x_686_ = lean_usize_dec_eq(v_i_678_, v_stop_679_);
if (v___x_686_ == 0)
{
lean_object* v_fst_687_; lean_object* v_snd_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___y_692_; 
v_fst_687_ = lean_ctor_get(v_b_680_, 0);
v_snd_688_ = lean_ctor_get(v_b_680_, 1);
v___x_689_ = lean_array_uget_borrowed(v_as_677_, v_i_678_);
v___x_690_ = l_Lean_IR_Decl_name(v___x_689_);
if (lean_obj_tag(v___x_690_) == 1)
{
lean_object* v_pre_705_; lean_object* v_str_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v_pre_705_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_pre_705_);
v_str_706_ = lean_ctor_get(v___x_690_, 1);
lean_inc_ref(v_str_706_);
v___x_707_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___closed__0));
v___x_708_ = lean_string_dec_eq(v_str_706_, v___x_707_);
lean_dec_ref(v_str_706_);
if (v___x_708_ == 0)
{
lean_dec(v_pre_705_);
lean_inc_ref(v___x_690_);
v___y_692_ = v___x_690_;
goto v___jp_691_;
}
else
{
v___y_692_ = v_pre_705_;
goto v___jp_691_;
}
}
else
{
lean_inc(v___x_690_);
v___y_692_ = v___x_690_;
goto v___jp_691_;
}
v___jp_691_:
{
uint8_t v___x_693_; 
lean_inc_ref(v___y_676_);
v___x_693_ = l_Lean_isExtern(v___y_676_, v___y_692_);
if (v___x_693_ == 0)
{
lean_dec(v___x_690_);
v___y_682_ = v_b_680_;
goto v___jp_681_;
}
else
{
lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_702_; 
lean_inc(v_snd_688_);
lean_inc(v_fst_687_);
v_isSharedCheck_702_ = !lean_is_exclusive(v_b_680_);
if (v_isSharedCheck_702_ == 0)
{
lean_object* v_unused_703_; lean_object* v_unused_704_; 
v_unused_703_ = lean_ctor_get(v_b_680_, 1);
lean_dec(v_unused_703_);
v_unused_704_ = lean_ctor_get(v_b_680_, 0);
lean_dec(v_unused_704_);
v___x_695_ = v_b_680_;
v_isShared_696_ = v_isSharedCheck_702_;
goto v_resetjp_694_;
}
else
{
lean_dec(v_b_680_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_702_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_700_; 
lean_inc_n(v___x_689_, 2);
v___x_697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_689_);
lean_ctor_set(v___x_697_, 1, v_fst_687_);
v___x_698_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_688_, v___x_690_, v___x_689_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 1, v___x_698_);
lean_ctor_set(v___x_695_, 0, v___x_697_);
v___x_700_ = v___x_695_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
v___y_682_ = v___x_700_;
goto v___jp_681_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_676_);
return v_b_680_;
}
v___jp_681_:
{
size_t v___x_683_; size_t v___x_684_; 
v___x_683_ = ((size_t)1ULL);
v___x_684_ = lean_usize_add(v_i_678_, v___x_683_);
v_i_678_ = v___x_684_;
v_b_680_ = v___y_682_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object* v___y_709_, lean_object* v_as_710_, lean_object* v_i_711_, lean_object* v_stop_712_, lean_object* v_b_713_){
_start:
{
size_t v_i_boxed_714_; size_t v_stop_boxed_715_; lean_object* v_res_716_; 
v_i_boxed_714_ = lean_unbox_usize(v_i_711_);
lean_dec(v_i_711_);
v_stop_boxed_715_ = lean_unbox_usize(v_stop_712_);
lean_dec(v_stop_712_);
v_res_716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_709_, v_as_710_, v_i_boxed_714_, v_stop_boxed_715_, v_b_713_);
lean_dec_ref(v_as_710_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg(lean_object* v_as_x27_718_, lean_object* v_b_719_){
_start:
{
if (lean_obj_tag(v_as_x27_718_) == 0)
{
lean_object* v___x_721_; 
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v_b_719_);
return v___x_721_;
}
else
{
lean_object* v_head_722_; lean_object* v_tail_723_; lean_object* v_fst_724_; lean_object* v_snd_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_750_; 
v_head_722_ = lean_ctor_get(v_as_x27_718_, 0);
v_tail_723_ = lean_ctor_get(v_as_x27_718_, 1);
v_fst_724_ = lean_ctor_get(v_b_719_, 0);
v_snd_725_ = lean_ctor_get(v_b_719_, 1);
v_isSharedCheck_750_ = !lean_is_exclusive(v_b_719_);
if (v_isSharedCheck_750_ == 0)
{
v___x_727_ = v_b_719_;
v_isShared_728_ = v_isSharedCheck_750_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_snd_725_);
lean_inc(v_fst_724_);
lean_dec(v_b_719_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_750_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_729_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0));
v___x_730_ = lean_string_dec_eq(v_head_722_, v___x_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; 
lean_inc(v_head_722_);
v___x_731_ = l___private_LeanIR_0__setConfigOption(v_snd_725_, v_head_722_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_734_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_732_);
lean_dec_ref_known(v___x_731_, 1);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 1, v_a_732_);
v___x_734_ = v___x_727_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_fst_724_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_a_732_);
v___x_734_ = v_reuseFailAlloc_736_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
v_as_x27_718_ = v_tail_723_;
v_b_719_ = v___x_734_;
goto _start;
}
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_del_object(v___x_727_);
lean_dec(v_fst_724_);
v_a_737_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_731_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_731_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
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
else
{
lean_object* v___x_745_; lean_object* v___x_747_; 
lean_dec(v_fst_724_);
v___x_745_ = lean_box(v___x_730_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v___x_745_);
v___x_747_ = v___x_727_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_745_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_snd_725_);
v___x_747_ = v_reuseFailAlloc_749_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
v_as_x27_718_ = v_tail_723_;
v_b_719_ = v___x_747_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(lean_object* v_as_x27_751_, lean_object* v_b_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_751_, v_b_752_);
lean_dec(v_as_x27_751_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object* v_as_755_, size_t v_i_756_, size_t v_stop_757_, lean_object* v_b_758_){
_start:
{
uint8_t v___x_759_; 
v___x_759_ = lean_usize_dec_eq(v_i_756_, v_stop_757_);
if (v___x_759_ == 0)
{
lean_object* v___x_760_; lean_object* v_toEnvExtension_761_; lean_object* v_asyncMode_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; size_t v___x_766_; size_t v___x_767_; 
v___x_760_ = l_Lean_Compiler_LCNF_impureSigExt;
v_toEnvExtension_761_ = lean_ctor_get(v___x_760_, 0);
v_asyncMode_762_ = lean_ctor_get(v_toEnvExtension_761_, 2);
v___x_763_ = lean_box(0);
v___x_764_ = lean_array_uget_borrowed(v_as_755_, v_i_756_);
lean_inc(v___x_764_);
v___x_765_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_760_, v_b_758_, v___x_764_, v_asyncMode_762_, v___x_763_);
v___x_766_ = ((size_t)1ULL);
v___x_767_ = lean_usize_add(v_i_756_, v___x_766_);
v_i_756_ = v___x_767_;
v_b_758_ = v___x_765_;
goto _start;
}
else
{
return v_b_758_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object* v_as_769_, lean_object* v_i_770_, lean_object* v_stop_771_, lean_object* v_b_772_){
_start:
{
size_t v_i_boxed_773_; size_t v_stop_boxed_774_; lean_object* v_res_775_; 
v_i_boxed_773_ = lean_unbox_usize(v_i_770_);
lean_dec(v_i_770_);
v_stop_boxed_774_ = lean_unbox_usize(v_stop_771_);
lean_dec(v_stop_771_);
v_res_775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_as_769_, v_i_boxed_773_, v_stop_boxed_774_, v_b_772_);
lean_dec_ref(v_as_769_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(lean_object* v_as_779_, size_t v_sz_780_, size_t v_i_781_, lean_object* v_b_782_, lean_object* v___y_783_){
_start:
{
uint8_t v___x_785_; 
v___x_785_ = lean_usize_dec_lt(v_i_781_, v_sz_780_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; 
v___x_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_786_, 0, v_b_782_);
return v___x_786_;
}
else
{
uint8_t v___x_787_; lean_object* v_a_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
lean_dec_ref(v_b_782_);
v___x_787_ = 0;
v_a_788_ = lean_array_uget_borrowed(v_as_779_, v_i_781_);
lean_inc(v_a_788_);
v___x_789_ = l_Lean_Message_toString(v_a_788_, v___x_787_);
v___x_790_ = l_IO_eprintln___at___00main_spec__6(v___x_789_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v___x_791_; size_t v___x_792_; size_t v___x_793_; 
lean_dec_ref_known(v___x_790_, 1);
v___x_791_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_792_ = ((size_t)1ULL);
v___x_793_ = lean_usize_add(v_i_781_, v___x_792_);
v_i_781_ = v___x_793_;
v_b_782_ = v___x_791_;
goto _start;
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_807_; 
v_a_795_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_807_ == 0)
{
v___x_797_ = v___x_790_;
v_isShared_798_ = v_isSharedCheck_807_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_790_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_807_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v_ref_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_805_; 
v_ref_799_ = lean_ctor_get(v___y_783_, 5);
v___x_800_ = lean_io_error_to_string(v_a_795_);
v___x_801_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
v___x_802_ = l_Lean_MessageData_ofFormat(v___x_801_);
lean_inc(v_ref_799_);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v_ref_799_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_803_);
v___x_805_ = v___x_797_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___boxed(lean_object* v_as_808_, lean_object* v_sz_809_, lean_object* v_i_810_, lean_object* v_b_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
size_t v_sz_boxed_814_; size_t v_i_boxed_815_; lean_object* v_res_816_; 
v_sz_boxed_814_ = lean_unbox_usize(v_sz_809_);
lean_dec(v_sz_809_);
v_i_boxed_815_ = lean_unbox_usize(v_i_810_);
lean_dec(v_i_810_);
v_res_816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_808_, v_sz_boxed_814_, v_i_boxed_815_, v_b_811_, v___y_812_);
lean_dec_ref(v___y_812_);
lean_dec_ref(v_as_808_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(lean_object* v_as_817_, size_t v_sz_818_, size_t v_i_819_, lean_object* v_b_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
uint8_t v___x_824_; 
v___x_824_ = lean_usize_dec_lt(v_i_819_, v_sz_818_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; 
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v_b_820_);
return v___x_825_;
}
else
{
uint8_t v___x_826_; lean_object* v_a_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
lean_dec_ref(v_b_820_);
v___x_826_ = 0;
v_a_827_ = lean_array_uget_borrowed(v_as_817_, v_i_819_);
lean_inc(v_a_827_);
v___x_828_ = l_Lean_Message_toString(v_a_827_, v___x_826_);
v___x_829_ = l_IO_eprintln___at___00main_spec__6(v___x_828_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v___x_830_; size_t v___x_831_; size_t v___x_832_; lean_object* v___x_833_; 
lean_dec_ref_known(v___x_829_, 1);
v___x_830_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_831_ = ((size_t)1ULL);
v___x_832_ = lean_usize_add(v_i_819_, v___x_831_);
v___x_833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_817_, v_sz_818_, v___x_832_, v___x_830_, v___y_821_);
return v___x_833_;
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_846_; 
v_a_834_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_846_ == 0)
{
v___x_836_ = v___x_829_;
v_isShared_837_ = v_isSharedCheck_846_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_829_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_846_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v_ref_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_844_; 
v_ref_838_ = lean_ctor_get(v___y_821_, 5);
v___x_839_ = lean_io_error_to_string(v_a_834_);
v___x_840_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
v___x_841_ = l_Lean_MessageData_ofFormat(v___x_840_);
lean_inc(v_ref_838_);
v___x_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_842_, 0, v_ref_838_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_842_);
v___x_844_ = v___x_836_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27___boxed(lean_object* v_as_847_, lean_object* v_sz_848_, lean_object* v_i_849_, lean_object* v_b_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
size_t v_sz_boxed_854_; size_t v_i_boxed_855_; lean_object* v_res_856_; 
v_sz_boxed_854_ = lean_unbox_usize(v_sz_848_);
lean_dec(v_sz_848_);
v_i_boxed_855_ = lean_unbox_usize(v_i_849_);
lean_dec(v_i_849_);
v_res_856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(v_as_847_, v_sz_boxed_854_, v_i_boxed_855_, v_b_850_, v___y_851_, v___y_852_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec_ref(v_as_847_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(lean_object* v_as_860_, size_t v_sz_861_, size_t v_i_862_, lean_object* v_b_863_, lean_object* v___y_864_){
_start:
{
uint8_t v___x_866_; 
v___x_866_ = lean_usize_dec_lt(v_i_862_, v_sz_861_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; 
v___x_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_867_, 0, v_b_863_);
return v___x_867_;
}
else
{
uint8_t v___x_868_; lean_object* v_a_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
lean_dec_ref(v_b_863_);
v___x_868_ = 0;
v_a_869_ = lean_array_uget_borrowed(v_as_860_, v_i_862_);
lean_inc(v_a_869_);
v___x_870_ = l_Lean_Message_toString(v_a_869_, v___x_868_);
v___x_871_ = l_IO_eprintln___at___00main_spec__6(v___x_870_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v___x_872_; size_t v___x_873_; size_t v___x_874_; 
lean_dec_ref_known(v___x_871_, 1);
v___x_872_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_873_ = ((size_t)1ULL);
v___x_874_ = lean_usize_add(v_i_862_, v___x_873_);
v_i_862_ = v___x_874_;
v_b_863_ = v___x_872_;
goto _start;
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_888_; 
v_a_876_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_888_ == 0)
{
v___x_878_ = v___x_871_;
v_isShared_879_ = v_isSharedCheck_888_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_871_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_888_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v_ref_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_886_; 
v_ref_880_ = lean_ctor_get(v___y_864_, 5);
v___x_881_ = lean_io_error_to_string(v_a_876_);
v___x_882_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
v___x_883_ = l_Lean_MessageData_ofFormat(v___x_882_);
lean_inc(v_ref_880_);
v___x_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_884_, 0, v_ref_880_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v___x_884_);
v___x_886_ = v___x_878_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___boxed(lean_object* v_as_889_, lean_object* v_sz_890_, lean_object* v_i_891_, lean_object* v_b_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
size_t v_sz_boxed_895_; size_t v_i_boxed_896_; lean_object* v_res_897_; 
v_sz_boxed_895_ = lean_unbox_usize(v_sz_890_);
lean_dec(v_sz_890_);
v_i_boxed_896_ = lean_unbox_usize(v_i_891_);
lean_dec(v_i_891_);
v_res_897_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_889_, v_sz_boxed_895_, v_i_boxed_896_, v_b_892_, v___y_893_);
lean_dec_ref(v___y_893_);
lean_dec_ref(v_as_889_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(lean_object* v_as_898_, size_t v_sz_899_, size_t v_i_900_, lean_object* v_b_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
uint8_t v___x_905_; 
v___x_905_ = lean_usize_dec_lt(v_i_900_, v_sz_899_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; 
v___x_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_906_, 0, v_b_901_);
return v___x_906_;
}
else
{
uint8_t v___x_907_; lean_object* v_a_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
lean_dec_ref(v_b_901_);
v___x_907_ = 0;
v_a_908_ = lean_array_uget_borrowed(v_as_898_, v_i_900_);
lean_inc(v_a_908_);
v___x_909_ = l_Lean_Message_toString(v_a_908_, v___x_907_);
v___x_910_ = l_IO_eprintln___at___00main_spec__6(v___x_909_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v___x_911_; size_t v___x_912_; size_t v___x_913_; lean_object* v___x_914_; 
lean_dec_ref_known(v___x_910_, 1);
v___x_911_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_912_ = ((size_t)1ULL);
v___x_913_ = lean_usize_add(v_i_900_, v___x_912_);
v___x_914_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_898_, v_sz_899_, v___x_913_, v___x_911_, v___y_902_);
return v___x_914_;
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_927_; 
v_a_915_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_927_ == 0)
{
v___x_917_ = v___x_910_;
v_isShared_918_ = v_isSharedCheck_927_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_910_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_927_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v_ref_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_925_; 
v_ref_919_ = lean_ctor_get(v___y_902_, 5);
v___x_920_ = lean_io_error_to_string(v_a_915_);
v___x_921_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
v___x_922_ = l_Lean_MessageData_ofFormat(v___x_921_);
lean_inc(v_ref_919_);
v___x_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_923_, 0, v_ref_919_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_923_);
v___x_925_ = v___x_917_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38___boxed(lean_object* v_as_928_, lean_object* v_sz_929_, lean_object* v_i_930_, lean_object* v_b_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
size_t v_sz_boxed_935_; size_t v_i_boxed_936_; lean_object* v_res_937_; 
v_sz_boxed_935_ = lean_unbox_usize(v_sz_929_);
lean_dec(v_sz_929_);
v_i_boxed_936_ = lean_unbox_usize(v_i_930_);
lean_dec(v_i_930_);
v_res_937_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(v_as_928_, v_sz_boxed_935_, v_i_boxed_936_, v_b_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec_ref(v_as_928_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(lean_object* v_init_938_, lean_object* v_n_939_, lean_object* v_b_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
if (lean_obj_tag(v_n_939_) == 0)
{
lean_object* v_cs_944_; lean_object* v___x_945_; lean_object* v___x_946_; size_t v_sz_947_; size_t v___x_948_; lean_object* v___x_949_; 
v_cs_944_ = lean_ctor_get(v_n_939_, 0);
v___x_945_ = lean_box(0);
v___x_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v_b_940_);
v_sz_947_ = lean_array_size(v_cs_944_);
v___x_948_ = ((size_t)0ULL);
v___x_949_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_init_938_, v_cs_944_, v_sz_947_, v___x_948_, v___x_946_, v___y_941_, v___y_942_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_964_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_964_ == 0)
{
v___x_952_ = v___x_949_;
v_isShared_953_ = v_isSharedCheck_964_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_949_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_964_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v_fst_954_; 
v_fst_954_ = lean_ctor_get(v_a_950_, 0);
if (lean_obj_tag(v_fst_954_) == 0)
{
lean_object* v_snd_955_; lean_object* v___x_956_; lean_object* v___x_958_; 
v_snd_955_ = lean_ctor_get(v_a_950_, 1);
lean_inc(v_snd_955_);
lean_dec(v_a_950_);
v___x_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_956_, 0, v_snd_955_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v___x_956_);
v___x_958_ = v___x_952_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_956_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
else
{
lean_object* v_val_960_; lean_object* v___x_962_; 
lean_inc_ref(v_fst_954_);
lean_dec(v_a_950_);
v_val_960_ = lean_ctor_get(v_fst_954_, 0);
lean_inc(v_val_960_);
lean_dec_ref_known(v_fst_954_, 1);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v_val_960_);
v___x_962_ = v___x_952_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_val_960_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
else
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
v_a_965_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_972_ == 0)
{
v___x_967_ = v___x_949_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_949_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
else
{
lean_object* v_vs_973_; lean_object* v___x_974_; lean_object* v___x_975_; size_t v_sz_976_; size_t v___x_977_; lean_object* v___x_978_; 
v_vs_973_ = lean_ctor_get(v_n_939_, 0);
v___x_974_ = lean_box(0);
v___x_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set(v___x_975_, 1, v_b_940_);
v_sz_976_ = lean_array_size(v_vs_973_);
v___x_977_ = ((size_t)0ULL);
v___x_978_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(v_vs_973_, v_sz_976_, v___x_977_, v___x_975_, v___y_941_, v___y_942_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_993_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_993_ == 0)
{
v___x_981_ = v___x_978_;
v_isShared_982_ = v_isSharedCheck_993_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_978_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_993_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v_fst_983_; 
v_fst_983_ = lean_ctor_get(v_a_979_, 0);
if (lean_obj_tag(v_fst_983_) == 0)
{
lean_object* v_snd_984_; lean_object* v___x_985_; lean_object* v___x_987_; 
v_snd_984_ = lean_ctor_get(v_a_979_, 1);
lean_inc(v_snd_984_);
lean_dec(v_a_979_);
v___x_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_985_, 0, v_snd_984_);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 0, v___x_985_);
v___x_987_ = v___x_981_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
else
{
lean_object* v_val_989_; lean_object* v___x_991_; 
lean_inc_ref(v_fst_983_);
lean_dec(v_a_979_);
v_val_989_ = lean_ctor_get(v_fst_983_, 0);
lean_inc(v_val_989_);
lean_dec_ref_known(v_fst_983_, 1);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 0, v_val_989_);
v___x_991_ = v___x_981_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_val_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
v_a_994_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_978_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_978_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_994_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(lean_object* v_init_1002_, lean_object* v_as_1003_, size_t v_sz_1004_, size_t v_i_1005_, lean_object* v_b_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
uint8_t v___x_1010_; 
v___x_1010_ = lean_usize_dec_lt(v_i_1005_, v_sz_1004_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; 
v___x_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1011_, 0, v_b_1006_);
return v___x_1011_;
}
else
{
lean_object* v_snd_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1046_; 
v_snd_1012_ = lean_ctor_get(v_b_1006_, 1);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_b_1006_);
if (v_isSharedCheck_1046_ == 0)
{
lean_object* v_unused_1047_; 
v_unused_1047_ = lean_ctor_get(v_b_1006_, 0);
lean_dec(v_unused_1047_);
v___x_1014_ = v_b_1006_;
v_isShared_1015_ = v_isSharedCheck_1046_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_snd_1012_);
lean_dec(v_b_1006_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1046_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v_a_1016_; lean_object* v___x_1017_; 
v_a_1016_ = lean_array_uget_borrowed(v_as_1003_, v_i_1005_);
lean_inc(v_snd_1012_);
v___x_1017_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1002_, v_a_1016_, v_snd_1012_, v___y_1007_, v___y_1008_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1037_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1020_ = v___x_1017_;
v_isShared_1021_ = v_isSharedCheck_1037_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1017_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1037_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
if (lean_obj_tag(v_a_1018_) == 0)
{
lean_object* v___x_1022_; lean_object* v___x_1024_; 
v___x_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1022_, 0, v_a_1018_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v___x_1022_);
v___x_1024_ = v___x_1014_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1022_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_snd_1012_);
v___x_1024_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1026_; 
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 0, v___x_1024_);
v___x_1026_ = v___x_1020_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1030_; lean_object* v___x_1032_; 
lean_del_object(v___x_1020_);
lean_dec(v_snd_1012_);
v_a_1029_ = lean_ctor_get(v_a_1018_, 0);
lean_inc(v_a_1029_);
lean_dec_ref_known(v_a_1018_, 1);
v___x_1030_ = lean_box(0);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 1, v_a_1029_);
lean_ctor_set(v___x_1014_, 0, v___x_1030_);
v___x_1032_ = v___x_1014_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_a_1029_);
v___x_1032_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
size_t v___x_1033_; size_t v___x_1034_; 
v___x_1033_ = ((size_t)1ULL);
v___x_1034_ = lean_usize_add(v_i_1005_, v___x_1033_);
v_i_1005_ = v___x_1034_;
v_b_1006_ = v___x_1032_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_del_object(v___x_1014_);
lean_dec(v_snd_1012_);
v_a_1038_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1017_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1017_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37___boxed(lean_object* v_init_1048_, lean_object* v_as_1049_, lean_object* v_sz_1050_, lean_object* v_i_1051_, lean_object* v_b_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
size_t v_sz_boxed_1056_; size_t v_i_boxed_1057_; lean_object* v_res_1058_; 
v_sz_boxed_1056_ = lean_unbox_usize(v_sz_1050_);
lean_dec(v_sz_1050_);
v_i_boxed_1057_ = lean_unbox_usize(v_i_1051_);
lean_dec(v_i_1051_);
v_res_1058_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_init_1048_, v_as_1049_, v_sz_boxed_1056_, v_i_boxed_1057_, v_b_1052_, v___y_1053_, v___y_1054_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec_ref(v_as_1049_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26___boxed(lean_object* v_init_1059_, lean_object* v_n_1060_, lean_object* v_b_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1059_, v_n_1060_, v_b_1061_, v___y_1062_, v___y_1063_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec_ref(v_n_1060_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12(lean_object* v_t_1066_, lean_object* v_init_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v_root_1071_; lean_object* v_tail_1072_; lean_object* v___x_1073_; 
v_root_1071_ = lean_ctor_get(v_t_1066_, 0);
v_tail_1072_ = lean_ctor_get(v_t_1066_, 1);
v___x_1073_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1067_, v_root_1071_, v_init_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1110_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1076_ = v___x_1073_;
v_isShared_1077_ = v_isSharedCheck_1110_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1073_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1110_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
if (lean_obj_tag(v_a_1074_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1080_; 
v_a_1078_ = lean_ctor_get(v_a_1074_, 0);
lean_inc(v_a_1078_);
lean_dec_ref_known(v_a_1074_, 1);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v_a_1078_);
v___x_1080_ = v___x_1076_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; size_t v_sz_1085_; size_t v___x_1086_; lean_object* v___x_1087_; 
lean_del_object(v___x_1076_);
v_a_1082_ = lean_ctor_get(v_a_1074_, 0);
lean_inc(v_a_1082_);
lean_dec_ref_known(v_a_1074_, 1);
v___x_1083_ = lean_box(0);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v_a_1082_);
v_sz_1085_ = lean_array_size(v_tail_1072_);
v___x_1086_ = ((size_t)0ULL);
v___x_1087_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(v_tail_1072_, v_sz_1085_, v___x_1086_, v___x_1084_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1101_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1090_ = v___x_1087_;
v_isShared_1091_ = v_isSharedCheck_1101_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1087_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1101_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v_fst_1092_; 
v_fst_1092_ = lean_ctor_get(v_a_1088_, 0);
if (lean_obj_tag(v_fst_1092_) == 0)
{
lean_object* v_snd_1093_; lean_object* v___x_1095_; 
v_snd_1093_ = lean_ctor_get(v_a_1088_, 1);
lean_inc(v_snd_1093_);
lean_dec(v_a_1088_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v_snd_1093_);
v___x_1095_ = v___x_1090_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_snd_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
else
{
lean_object* v_val_1097_; lean_object* v___x_1099_; 
lean_inc_ref(v_fst_1092_);
lean_dec(v_a_1088_);
v_val_1097_ = lean_ctor_get(v_fst_1092_, 0);
lean_inc(v_val_1097_);
lean_dec_ref_known(v_fst_1092_, 1);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v_val_1097_);
v___x_1099_ = v___x_1090_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_val_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
v_a_1102_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1087_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1087_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
}
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
v_a_1111_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1073_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1073_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12___boxed(lean_object* v_t_1119_, lean_object* v_init_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(v_t_1119_, v_init_1120_, v___y_1121_, v___y_1122_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec_ref(v_t_1119_);
return v_res_1124_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(uint8_t v___x_1132_, uint8_t v_suppressElabErrors_1133_, lean_object* v___x_1134_, lean_object* v_x_1135_){
_start:
{
if (lean_obj_tag(v_x_1135_) == 1)
{
lean_object* v_pre_1136_; 
v_pre_1136_ = lean_ctor_get(v_x_1135_, 0);
switch(lean_obj_tag(v_pre_1136_))
{
case 1:
{
lean_object* v_pre_1137_; 
v_pre_1137_ = lean_ctor_get(v_pre_1136_, 0);
switch(lean_obj_tag(v_pre_1137_))
{
case 0:
{
lean_object* v_str_1138_; lean_object* v_str_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
v_str_1138_ = lean_ctor_get(v_x_1135_, 1);
v_str_1139_ = lean_ctor_get(v_pre_1136_, 1);
v___x_1140_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0));
v___x_1141_ = lean_string_dec_eq(v_str_1139_, v___x_1140_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1));
v___x_1143_ = lean_string_dec_eq(v_str_1139_, v___x_1142_);
if (v___x_1143_ == 0)
{
return v___x_1132_;
}
else
{
lean_object* v___x_1144_; uint8_t v___x_1145_; 
v___x_1144_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2));
v___x_1145_ = lean_string_dec_eq(v_str_1138_, v___x_1144_);
if (v___x_1145_ == 0)
{
return v___x_1132_;
}
else
{
return v_suppressElabErrors_1133_;
}
}
}
else
{
lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1146_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3));
v___x_1147_ = lean_string_dec_eq(v_str_1138_, v___x_1146_);
if (v___x_1147_ == 0)
{
return v___x_1132_;
}
else
{
return v_suppressElabErrors_1133_;
}
}
}
case 1:
{
lean_object* v_pre_1148_; 
v_pre_1148_ = lean_ctor_get(v_pre_1137_, 0);
if (lean_obj_tag(v_pre_1148_) == 0)
{
lean_object* v_str_1149_; lean_object* v_str_1150_; lean_object* v_str_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; 
v_str_1149_ = lean_ctor_get(v_x_1135_, 1);
v_str_1150_ = lean_ctor_get(v_pre_1136_, 1);
v_str_1151_ = lean_ctor_get(v_pre_1137_, 1);
v___x_1152_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4));
v___x_1153_ = lean_string_dec_eq(v_str_1151_, v___x_1152_);
if (v___x_1153_ == 0)
{
return v___x_1132_;
}
else
{
lean_object* v___x_1154_; uint8_t v___x_1155_; 
v___x_1154_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5));
v___x_1155_ = lean_string_dec_eq(v_str_1150_, v___x_1154_);
if (v___x_1155_ == 0)
{
return v___x_1132_;
}
else
{
lean_object* v___x_1156_; uint8_t v___x_1157_; 
v___x_1156_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6));
v___x_1157_ = lean_string_dec_eq(v_str_1149_, v___x_1156_);
if (v___x_1157_ == 0)
{
return v___x_1132_;
}
else
{
return v_suppressElabErrors_1133_;
}
}
}
}
else
{
return v___x_1132_;
}
}
default: 
{
return v___x_1132_;
}
}
}
case 0:
{
lean_object* v_str_1158_; uint8_t v___x_1159_; 
v_str_1158_ = lean_ctor_get(v_x_1135_, 1);
v___x_1159_ = lean_string_dec_eq(v_str_1158_, v___x_1134_);
if (v___x_1159_ == 0)
{
return v___x_1132_;
}
else
{
return v_suppressElabErrors_1133_;
}
}
default: 
{
return v___x_1132_;
}
}
}
else
{
return v___x_1132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed(lean_object* v___x_1160_, lean_object* v_suppressElabErrors_1161_, lean_object* v___x_1162_, lean_object* v_x_1163_){
_start:
{
uint8_t v___x_37277__boxed_1164_; uint8_t v_suppressElabErrors_boxed_1165_; uint8_t v_res_1166_; lean_object* v_r_1167_; 
v___x_37277__boxed_1164_ = lean_unbox(v___x_1160_);
v_suppressElabErrors_boxed_1165_ = lean_unbox(v_suppressElabErrors_1161_);
v_res_1166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(v___x_37277__boxed_1164_, v_suppressElabErrors_boxed_1165_, v___x_1162_, v_x_1163_);
lean_dec(v_x_1163_);
lean_dec_ref(v___x_1162_);
v_r_1167_ = lean_box(v_res_1166_);
return v_r_1167_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0(void){
_start:
{
lean_object* v___x_1168_; double v___x_1169_; 
v___x_1168_ = lean_unsigned_to_nat(0u);
v___x_1169_ = lean_float_of_nat(v___x_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(uint8_t v___x_1171_, lean_object* v_as_1172_, size_t v_sz_1173_, size_t v_i_1174_, lean_object* v_b_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v_a_1180_; uint8_t v___x_1184_; 
v___x_1184_ = lean_usize_dec_lt(v_i_1174_, v_sz_1173_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; 
v___x_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1185_, 0, v_b_1175_);
return v___x_1185_;
}
else
{
lean_object* v_a_1186_; lean_object* v_fst_1187_; lean_object* v_snd_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1264_; 
v_a_1186_ = lean_array_uget(v_as_1172_, v_i_1174_);
v_fst_1187_ = lean_ctor_get(v_a_1186_, 0);
v_snd_1188_ = lean_ctor_get(v_a_1186_, 1);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_a_1186_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1190_ = v_a_1186_;
v_isShared_1191_ = v_isSharedCheck_1264_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_snd_1188_);
lean_inc(v_fst_1187_);
lean_dec(v_a_1186_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1264_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v_fst_1192_; lean_object* v_snd_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1263_; 
v_fst_1192_ = lean_ctor_get(v_fst_1187_, 0);
v_snd_1193_ = lean_ctor_get(v_fst_1187_, 1);
v_isSharedCheck_1263_ = !lean_is_exclusive(v_fst_1187_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1195_ = v_fst_1187_;
v_isShared_1196_ = v_isSharedCheck_1263_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_snd_1193_);
lean_inc(v_fst_1192_);
lean_dec(v_fst_1187_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1263_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; double v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v_fileName_1202_; lean_object* v_fileMap_1203_; uint8_t v_suppressElabErrors_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1211_; 
v___x_1197_ = lean_box(0);
v___x_1198_ = lean_box(0);
v___x_1199_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0);
v___x_1200_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1));
v___x_1201_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1201_, 0, v___x_1197_);
lean_ctor_set(v___x_1201_, 1, v___x_1198_);
lean_ctor_set(v___x_1201_, 2, v___x_1200_);
lean_ctor_set_float(v___x_1201_, sizeof(void*)*3, v___x_1199_);
lean_ctor_set_float(v___x_1201_, sizeof(void*)*3 + 8, v___x_1199_);
lean_ctor_set_uint8(v___x_1201_, sizeof(void*)*3 + 16, v___x_1184_);
v_fileName_1202_ = lean_ctor_get(v___y_1176_, 0);
v_fileMap_1203_ = lean_ctor_get(v___y_1176_, 1);
v_suppressElabErrors_1204_ = lean_ctor_get_uint8(v___y_1176_, sizeof(void*)*14 + 1);
v___x_1205_ = lean_box(0);
v___x_1206_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_1207_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_1208_ = l_Lean_MessageData_nil;
v___x_1209_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1201_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
lean_ctor_set(v___x_1209_, 2, v_snd_1188_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set_tag(v___x_1195_, 8);
lean_ctor_set(v___x_1195_, 1, v___x_1209_);
lean_ctor_set(v___x_1195_, 0, v___x_1207_);
v___x_1211_ = v___x_1195_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v___x_1209_);
v___x_1211_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
uint8_t v___x_1212_; lean_object* v___x_1213_; lean_object* v___y_1215_; lean_object* v___y_1216_; 
v___x_1212_ = 0;
lean_inc_ref(v_fileMap_1203_);
lean_inc_ref(v_fileName_1202_);
v___x_1213_ = l_Lean_Elab_mkMessageCore(v_fileName_1202_, v_fileMap_1203_, v___x_1211_, v___x_1212_, v_fst_1192_, v_snd_1193_);
lean_dec(v_snd_1193_);
lean_dec(v_fst_1192_);
if (v_suppressElabErrors_1204_ == 0)
{
v___y_1215_ = v___y_1176_;
v___y_1216_ = v___y_1177_;
goto v___jp_1214_;
}
else
{
lean_object* v_data_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___f_1260_; uint8_t v___x_1261_; 
v_data_1257_ = lean_ctor_get(v___x_1213_, 4);
lean_inc(v_data_1257_);
v___x_1258_ = lean_box(v___x_1171_);
v___x_1259_ = lean_box(v_suppressElabErrors_1204_);
v___f_1260_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1260_, 0, v___x_1258_);
lean_closure_set(v___f_1260_, 1, v___x_1259_);
lean_closure_set(v___f_1260_, 2, v___x_1206_);
v___x_1261_ = l_Lean_MessageData_hasTag(v___f_1260_, v_data_1257_);
if (v___x_1261_ == 0)
{
lean_dec_ref(v___x_1213_);
lean_del_object(v___x_1190_);
v_a_1180_ = v___x_1205_;
goto v___jp_1179_;
}
else
{
v___y_1215_ = v___y_1176_;
v___y_1216_ = v___y_1177_;
goto v___jp_1214_;
}
}
v___jp_1214_:
{
lean_object* v___x_1217_; lean_object* v_fileName_1218_; lean_object* v_pos_1219_; lean_object* v_endPos_1220_; uint8_t v_keepFullRange_1221_; uint8_t v_severity_1222_; uint8_t v_isSilent_1223_; lean_object* v_caption_1224_; lean_object* v_data_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1256_; 
v___x_1217_ = lean_st_ref_take(v___y_1216_);
v_fileName_1218_ = lean_ctor_get(v___x_1213_, 0);
v_pos_1219_ = lean_ctor_get(v___x_1213_, 1);
v_endPos_1220_ = lean_ctor_get(v___x_1213_, 2);
v_keepFullRange_1221_ = lean_ctor_get_uint8(v___x_1213_, sizeof(void*)*5);
v_severity_1222_ = lean_ctor_get_uint8(v___x_1213_, sizeof(void*)*5 + 1);
v_isSilent_1223_ = lean_ctor_get_uint8(v___x_1213_, sizeof(void*)*5 + 2);
v_caption_1224_ = lean_ctor_get(v___x_1213_, 3);
v_data_1225_ = lean_ctor_get(v___x_1213_, 4);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1227_ = v___x_1213_;
v_isShared_1228_ = v_isSharedCheck_1256_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_data_1225_);
lean_inc(v_caption_1224_);
lean_inc(v_endPos_1220_);
lean_inc(v_pos_1219_);
lean_inc(v_fileName_1218_);
lean_dec(v___x_1213_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1256_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v_currNamespace_1229_; lean_object* v_openDecls_1230_; lean_object* v_env_1231_; lean_object* v_nextMacroScope_1232_; lean_object* v_ngen_1233_; lean_object* v_auxDeclNGen_1234_; lean_object* v_traceState_1235_; lean_object* v_cache_1236_; lean_object* v_messages_1237_; lean_object* v_infoState_1238_; lean_object* v_snapshotTasks_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1255_; 
v_currNamespace_1229_ = lean_ctor_get(v___y_1215_, 6);
v_openDecls_1230_ = lean_ctor_get(v___y_1215_, 7);
v_env_1231_ = lean_ctor_get(v___x_1217_, 0);
v_nextMacroScope_1232_ = lean_ctor_get(v___x_1217_, 1);
v_ngen_1233_ = lean_ctor_get(v___x_1217_, 2);
v_auxDeclNGen_1234_ = lean_ctor_get(v___x_1217_, 3);
v_traceState_1235_ = lean_ctor_get(v___x_1217_, 4);
v_cache_1236_ = lean_ctor_get(v___x_1217_, 5);
v_messages_1237_ = lean_ctor_get(v___x_1217_, 6);
v_infoState_1238_ = lean_ctor_get(v___x_1217_, 7);
v_snapshotTasks_1239_ = lean_ctor_get(v___x_1217_, 8);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1241_ = v___x_1217_;
v_isShared_1242_ = v_isSharedCheck_1255_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_snapshotTasks_1239_);
lean_inc(v_infoState_1238_);
lean_inc(v_messages_1237_);
lean_inc(v_cache_1236_);
lean_inc(v_traceState_1235_);
lean_inc(v_auxDeclNGen_1234_);
lean_inc(v_ngen_1233_);
lean_inc(v_nextMacroScope_1232_);
lean_inc(v_env_1231_);
lean_dec(v___x_1217_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1255_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
lean_inc(v_openDecls_1230_);
lean_inc(v_currNamespace_1229_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 1, v_openDecls_1230_);
lean_ctor_set(v___x_1190_, 0, v_currNamespace_1229_);
v___x_1244_ = v___x_1190_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_currNamespace_1229_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_openDecls_1230_);
v___x_1244_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1245_; lean_object* v___x_1247_; 
v___x_1245_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
lean_ctor_set(v___x_1245_, 1, v_data_1225_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 4, v___x_1245_);
v___x_1247_ = v___x_1227_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_fileName_1218_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v_pos_1219_);
lean_ctor_set(v_reuseFailAlloc_1253_, 2, v_endPos_1220_);
lean_ctor_set(v_reuseFailAlloc_1253_, 3, v_caption_1224_);
lean_ctor_set(v_reuseFailAlloc_1253_, 4, v___x_1245_);
lean_ctor_set_uint8(v_reuseFailAlloc_1253_, sizeof(void*)*5, v_keepFullRange_1221_);
lean_ctor_set_uint8(v_reuseFailAlloc_1253_, sizeof(void*)*5 + 1, v_severity_1222_);
lean_ctor_set_uint8(v_reuseFailAlloc_1253_, sizeof(void*)*5 + 2, v_isSilent_1223_);
v___x_1247_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
lean_object* v___x_1248_; lean_object* v___x_1250_; 
v___x_1248_ = l_Lean_MessageLog_add(v___x_1247_, v_messages_1237_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 6, v___x_1248_);
v___x_1250_ = v___x_1241_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_env_1231_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v_nextMacroScope_1232_);
lean_ctor_set(v_reuseFailAlloc_1252_, 2, v_ngen_1233_);
lean_ctor_set(v_reuseFailAlloc_1252_, 3, v_auxDeclNGen_1234_);
lean_ctor_set(v_reuseFailAlloc_1252_, 4, v_traceState_1235_);
lean_ctor_set(v_reuseFailAlloc_1252_, 5, v_cache_1236_);
lean_ctor_set(v_reuseFailAlloc_1252_, 6, v___x_1248_);
lean_ctor_set(v_reuseFailAlloc_1252_, 7, v_infoState_1238_);
lean_ctor_set(v_reuseFailAlloc_1252_, 8, v_snapshotTasks_1239_);
v___x_1250_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1251_; 
v___x_1251_ = lean_st_ref_set(v___y_1216_, v___x_1250_);
v_a_1180_ = v___x_1205_;
goto v___jp_1179_;
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
v___jp_1179_:
{
size_t v___x_1181_; size_t v___x_1182_; 
v___x_1181_ = ((size_t)1ULL);
v___x_1182_ = lean_usize_add(v_i_1174_, v___x_1181_);
v_i_1174_ = v___x_1182_;
v_b_1175_ = v_a_1180_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___boxed(lean_object* v___x_1265_, lean_object* v_as_1266_, lean_object* v_sz_1267_, lean_object* v_i_1268_, lean_object* v_b_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
uint8_t v___x_37350__boxed_1273_; size_t v_sz_boxed_1274_; size_t v_i_boxed_1275_; lean_object* v_res_1276_; 
v___x_37350__boxed_1273_ = lean_unbox(v___x_1265_);
v_sz_boxed_1274_ = lean_unbox_usize(v_sz_1267_);
lean_dec(v_sz_1267_);
v_i_boxed_1275_ = lean_unbox_usize(v_i_1268_);
lean_dec(v_i_1268_);
v_res_1276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_37350__boxed_1273_, v_as_1266_, v_sz_boxed_1274_, v_i_boxed_1275_, v_b_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec_ref(v_as_1266_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(lean_object* v_opts_1277_, lean_object* v_opt_1278_){
_start:
{
lean_object* v_name_1279_; lean_object* v_map_1280_; lean_object* v___x_1281_; 
v_name_1279_ = lean_ctor_get(v_opt_1278_, 0);
v_map_1280_ = lean_ctor_get(v_opts_1277_, 0);
v___x_1281_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1280_, v_name_1279_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v___x_1282_; 
v___x_1282_ = lean_box(0);
return v___x_1282_;
}
else
{
lean_object* v_val_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1292_; 
v_val_1283_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1285_ = v___x_1281_;
v_isShared_1286_ = v_isSharedCheck_1292_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_val_1283_);
lean_dec(v___x_1281_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1292_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
if (lean_obj_tag(v_val_1283_) == 0)
{
lean_object* v_v_1287_; lean_object* v___x_1289_; 
v_v_1287_ = lean_ctor_get(v_val_1283_, 0);
lean_inc_ref(v_v_1287_);
lean_dec_ref_known(v_val_1283_, 1);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v_v_1287_);
v___x_1289_ = v___x_1285_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_v_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
else
{
lean_object* v___x_1291_; 
lean_del_object(v___x_1285_);
lean_dec(v_val_1283_);
v___x_1291_ = lean_box(0);
return v___x_1291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15___boxed(lean_object* v_opts_1293_, lean_object* v_opt_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(v_opts_1293_, v_opt_1294_);
lean_dec_ref(v_opt_1294_);
lean_dec_ref(v_opts_1293_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(lean_object* v_a_1296_, lean_object* v_fallback_1297_, lean_object* v_x_1298_){
_start:
{
if (lean_obj_tag(v_x_1298_) == 0)
{
lean_inc(v_fallback_1297_);
return v_fallback_1297_;
}
else
{
lean_object* v_key_1299_; lean_object* v_value_1300_; lean_object* v_tail_1301_; uint8_t v___y_1303_; lean_object* v_fst_1305_; lean_object* v_snd_1306_; lean_object* v_fst_1307_; lean_object* v_snd_1308_; uint8_t v___x_1309_; 
v_key_1299_ = lean_ctor_get(v_x_1298_, 0);
v_value_1300_ = lean_ctor_get(v_x_1298_, 1);
v_tail_1301_ = lean_ctor_get(v_x_1298_, 2);
v_fst_1305_ = lean_ctor_get(v_key_1299_, 0);
v_snd_1306_ = lean_ctor_get(v_key_1299_, 1);
v_fst_1307_ = lean_ctor_get(v_a_1296_, 0);
v_snd_1308_ = lean_ctor_get(v_a_1296_, 1);
v___x_1309_ = lean_nat_dec_eq(v_fst_1305_, v_fst_1307_);
if (v___x_1309_ == 0)
{
v___y_1303_ = v___x_1309_;
goto v___jp_1302_;
}
else
{
uint8_t v___x_1310_; 
v___x_1310_ = lean_nat_dec_eq(v_snd_1306_, v_snd_1308_);
v___y_1303_ = v___x_1310_;
goto v___jp_1302_;
}
v___jp_1302_:
{
if (v___y_1303_ == 0)
{
v_x_1298_ = v_tail_1301_;
goto _start;
}
else
{
lean_inc(v_value_1300_);
return v_value_1300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg___boxed(lean_object* v_a_1311_, lean_object* v_fallback_1312_, lean_object* v_x_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_1311_, v_fallback_1312_, v_x_1313_);
lean_dec(v_x_1313_);
lean_dec(v_fallback_1312_);
lean_dec_ref(v_a_1311_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(lean_object* v_m_1315_, lean_object* v_a_1316_, lean_object* v_fallback_1317_){
_start:
{
lean_object* v_buckets_1318_; lean_object* v_fst_1319_; lean_object* v_snd_1320_; lean_object* v___x_1321_; uint64_t v___x_1322_; uint64_t v___x_1323_; uint64_t v___x_1324_; uint64_t v___x_1325_; uint64_t v___x_1326_; uint64_t v_fold_1327_; uint64_t v___x_1328_; uint64_t v___x_1329_; uint64_t v___x_1330_; size_t v___x_1331_; size_t v___x_1332_; size_t v___x_1333_; size_t v___x_1334_; size_t v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v_buckets_1318_ = lean_ctor_get(v_m_1315_, 1);
v_fst_1319_ = lean_ctor_get(v_a_1316_, 0);
v_snd_1320_ = lean_ctor_get(v_a_1316_, 1);
v___x_1321_ = lean_array_get_size(v_buckets_1318_);
v___x_1322_ = l_String_instHashableRaw_hash(v_fst_1319_);
v___x_1323_ = l_String_instHashableRaw_hash(v_snd_1320_);
v___x_1324_ = lean_uint64_mix_hash(v___x_1322_, v___x_1323_);
v___x_1325_ = 32ULL;
v___x_1326_ = lean_uint64_shift_right(v___x_1324_, v___x_1325_);
v_fold_1327_ = lean_uint64_xor(v___x_1324_, v___x_1326_);
v___x_1328_ = 16ULL;
v___x_1329_ = lean_uint64_shift_right(v_fold_1327_, v___x_1328_);
v___x_1330_ = lean_uint64_xor(v_fold_1327_, v___x_1329_);
v___x_1331_ = lean_uint64_to_usize(v___x_1330_);
v___x_1332_ = lean_usize_of_nat(v___x_1321_);
v___x_1333_ = ((size_t)1ULL);
v___x_1334_ = lean_usize_sub(v___x_1332_, v___x_1333_);
v___x_1335_ = lean_usize_land(v___x_1331_, v___x_1334_);
v___x_1336_ = lean_array_uget_borrowed(v_buckets_1318_, v___x_1335_);
v___x_1337_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_1316_, v_fallback_1317_, v___x_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg___boxed(lean_object* v_m_1338_, lean_object* v_a_1339_, lean_object* v_fallback_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_1338_, v_a_1339_, v_fallback_1340_);
lean_dec(v_fallback_1340_);
lean_dec_ref(v_a_1339_);
lean_dec_ref(v_m_1338_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(lean_object* v_x_1342_, lean_object* v_x_1343_){
_start:
{
if (lean_obj_tag(v_x_1343_) == 0)
{
return v_x_1342_;
}
else
{
lean_object* v_key_1344_; lean_object* v_value_1345_; lean_object* v_tail_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1373_; 
v_key_1344_ = lean_ctor_get(v_x_1343_, 0);
v_value_1345_ = lean_ctor_get(v_x_1343_, 1);
v_tail_1346_ = lean_ctor_get(v_x_1343_, 2);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_x_1343_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1348_ = v_x_1343_;
v_isShared_1349_ = v_isSharedCheck_1373_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_tail_1346_);
lean_inc(v_value_1345_);
lean_inc(v_key_1344_);
lean_dec(v_x_1343_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1373_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v_fst_1350_; lean_object* v_snd_1351_; lean_object* v___x_1352_; uint64_t v___x_1353_; uint64_t v___x_1354_; uint64_t v___x_1355_; uint64_t v___x_1356_; uint64_t v___x_1357_; uint64_t v_fold_1358_; uint64_t v___x_1359_; uint64_t v___x_1360_; uint64_t v___x_1361_; size_t v___x_1362_; size_t v___x_1363_; size_t v___x_1364_; size_t v___x_1365_; size_t v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1369_; 
v_fst_1350_ = lean_ctor_get(v_key_1344_, 0);
v_snd_1351_ = lean_ctor_get(v_key_1344_, 1);
v___x_1352_ = lean_array_get_size(v_x_1342_);
v___x_1353_ = l_String_instHashableRaw_hash(v_fst_1350_);
v___x_1354_ = l_String_instHashableRaw_hash(v_snd_1351_);
v___x_1355_ = lean_uint64_mix_hash(v___x_1353_, v___x_1354_);
v___x_1356_ = 32ULL;
v___x_1357_ = lean_uint64_shift_right(v___x_1355_, v___x_1356_);
v_fold_1358_ = lean_uint64_xor(v___x_1355_, v___x_1357_);
v___x_1359_ = 16ULL;
v___x_1360_ = lean_uint64_shift_right(v_fold_1358_, v___x_1359_);
v___x_1361_ = lean_uint64_xor(v_fold_1358_, v___x_1360_);
v___x_1362_ = lean_uint64_to_usize(v___x_1361_);
v___x_1363_ = lean_usize_of_nat(v___x_1352_);
v___x_1364_ = ((size_t)1ULL);
v___x_1365_ = lean_usize_sub(v___x_1363_, v___x_1364_);
v___x_1366_ = lean_usize_land(v___x_1362_, v___x_1365_);
v___x_1367_ = lean_array_uget_borrowed(v_x_1342_, v___x_1366_);
lean_inc(v___x_1367_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 2, v___x_1367_);
v___x_1369_ = v___x_1348_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_key_1344_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_value_1345_);
lean_ctor_set(v_reuseFailAlloc_1372_, 2, v___x_1367_);
v___x_1369_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_array_uset(v_x_1342_, v___x_1366_, v___x_1369_);
v_x_1342_ = v___x_1370_;
v_x_1343_ = v_tail_1346_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(lean_object* v_i_1374_, lean_object* v_source_1375_, lean_object* v_target_1376_){
_start:
{
lean_object* v___x_1377_; uint8_t v___x_1378_; 
v___x_1377_ = lean_array_get_size(v_source_1375_);
v___x_1378_ = lean_nat_dec_lt(v_i_1374_, v___x_1377_);
if (v___x_1378_ == 0)
{
lean_dec_ref(v_source_1375_);
lean_dec(v_i_1374_);
return v_target_1376_;
}
else
{
lean_object* v_es_1379_; lean_object* v___x_1380_; lean_object* v_source_1381_; lean_object* v_target_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_es_1379_ = lean_array_fget(v_source_1375_, v_i_1374_);
v___x_1380_ = lean_box(0);
v_source_1381_ = lean_array_fset(v_source_1375_, v_i_1374_, v___x_1380_);
v_target_1382_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_target_1376_, v_es_1379_);
v___x_1383_ = lean_unsigned_to_nat(1u);
v___x_1384_ = lean_nat_add(v_i_1374_, v___x_1383_);
lean_dec(v_i_1374_);
v_i_1374_ = v___x_1384_;
v_source_1375_ = v_source_1381_;
v_target_1376_ = v_target_1382_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(lean_object* v_data_1386_){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v_nbuckets_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1387_ = lean_array_get_size(v_data_1386_);
v___x_1388_ = lean_unsigned_to_nat(2u);
v_nbuckets_1389_ = lean_nat_mul(v___x_1387_, v___x_1388_);
v___x_1390_ = lean_unsigned_to_nat(0u);
v___x_1391_ = lean_box(0);
v___x_1392_ = lean_mk_array(v_nbuckets_1389_, v___x_1391_);
v___x_1393_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v___x_1390_, v_data_1386_, v___x_1392_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(lean_object* v_a_1394_, lean_object* v_b_1395_, lean_object* v_x_1396_){
_start:
{
if (lean_obj_tag(v_x_1396_) == 0)
{
lean_dec(v_b_1395_);
lean_dec_ref(v_a_1394_);
return v_x_1396_;
}
else
{
lean_object* v_key_1397_; lean_object* v_value_1398_; lean_object* v_tail_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1418_; 
v_key_1397_ = lean_ctor_get(v_x_1396_, 0);
v_value_1398_ = lean_ctor_get(v_x_1396_, 1);
v_tail_1399_ = lean_ctor_get(v_x_1396_, 2);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_x_1396_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1401_ = v_x_1396_;
v_isShared_1402_ = v_isSharedCheck_1418_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_tail_1399_);
lean_inc(v_value_1398_);
lean_inc(v_key_1397_);
lean_dec(v_x_1396_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1418_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
uint8_t v___y_1404_; lean_object* v_fst_1412_; lean_object* v_snd_1413_; lean_object* v_fst_1414_; lean_object* v_snd_1415_; uint8_t v___x_1416_; 
v_fst_1412_ = lean_ctor_get(v_key_1397_, 0);
v_snd_1413_ = lean_ctor_get(v_key_1397_, 1);
v_fst_1414_ = lean_ctor_get(v_a_1394_, 0);
v_snd_1415_ = lean_ctor_get(v_a_1394_, 1);
v___x_1416_ = lean_nat_dec_eq(v_fst_1412_, v_fst_1414_);
if (v___x_1416_ == 0)
{
v___y_1404_ = v___x_1416_;
goto v___jp_1403_;
}
else
{
uint8_t v___x_1417_; 
v___x_1417_ = lean_nat_dec_eq(v_snd_1413_, v_snd_1415_);
v___y_1404_ = v___x_1417_;
goto v___jp_1403_;
}
v___jp_1403_:
{
if (v___y_1404_ == 0)
{
lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1405_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_1394_, v_b_1395_, v_tail_1399_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 2, v___x_1405_);
v___x_1407_ = v___x_1401_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_key_1397_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_value_1398_);
lean_ctor_set(v_reuseFailAlloc_1408_, 2, v___x_1405_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
else
{
lean_object* v___x_1410_; 
lean_dec(v_value_1398_);
lean_dec(v_key_1397_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 1, v_b_1395_);
lean_ctor_set(v___x_1401_, 0, v_a_1394_);
v___x_1410_ = v___x_1401_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1394_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_b_1395_);
lean_ctor_set(v_reuseFailAlloc_1411_, 2, v_tail_1399_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(lean_object* v_a_1419_, lean_object* v_x_1420_){
_start:
{
if (lean_obj_tag(v_x_1420_) == 0)
{
uint8_t v___x_1421_; 
v___x_1421_ = 0;
return v___x_1421_;
}
else
{
lean_object* v_key_1422_; lean_object* v_tail_1423_; uint8_t v___y_1425_; lean_object* v_fst_1427_; lean_object* v_snd_1428_; lean_object* v_fst_1429_; lean_object* v_snd_1430_; uint8_t v___x_1431_; 
v_key_1422_ = lean_ctor_get(v_x_1420_, 0);
v_tail_1423_ = lean_ctor_get(v_x_1420_, 2);
v_fst_1427_ = lean_ctor_get(v_key_1422_, 0);
v_snd_1428_ = lean_ctor_get(v_key_1422_, 1);
v_fst_1429_ = lean_ctor_get(v_a_1419_, 0);
v_snd_1430_ = lean_ctor_get(v_a_1419_, 1);
v___x_1431_ = lean_nat_dec_eq(v_fst_1427_, v_fst_1429_);
if (v___x_1431_ == 0)
{
v___y_1425_ = v___x_1431_;
goto v___jp_1424_;
}
else
{
uint8_t v___x_1432_; 
v___x_1432_ = lean_nat_dec_eq(v_snd_1428_, v_snd_1430_);
v___y_1425_ = v___x_1432_;
goto v___jp_1424_;
}
v___jp_1424_:
{
if (v___y_1425_ == 0)
{
v_x_1420_ = v_tail_1423_;
goto _start;
}
else
{
return v___y_1425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg___boxed(lean_object* v_a_1433_, lean_object* v_x_1434_){
_start:
{
uint8_t v_res_1435_; lean_object* v_r_1436_; 
v_res_1435_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_1433_, v_x_1434_);
lean_dec(v_x_1434_);
lean_dec_ref(v_a_1433_);
v_r_1436_ = lean_box(v_res_1435_);
return v_r_1436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(lean_object* v_m_1437_, lean_object* v_a_1438_, lean_object* v_b_1439_){
_start:
{
lean_object* v_size_1440_; lean_object* v_buckets_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1488_; 
v_size_1440_ = lean_ctor_get(v_m_1437_, 0);
v_buckets_1441_ = lean_ctor_get(v_m_1437_, 1);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_m_1437_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1443_ = v_m_1437_;
v_isShared_1444_ = v_isSharedCheck_1488_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_buckets_1441_);
lean_inc(v_size_1440_);
lean_dec(v_m_1437_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1488_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v_fst_1445_; lean_object* v_snd_1446_; lean_object* v___x_1447_; uint64_t v___x_1448_; uint64_t v___x_1449_; uint64_t v___x_1450_; uint64_t v___x_1451_; uint64_t v___x_1452_; uint64_t v_fold_1453_; uint64_t v___x_1454_; uint64_t v___x_1455_; uint64_t v___x_1456_; size_t v___x_1457_; size_t v___x_1458_; size_t v___x_1459_; size_t v___x_1460_; size_t v___x_1461_; lean_object* v_bkt_1462_; uint8_t v___x_1463_; 
v_fst_1445_ = lean_ctor_get(v_a_1438_, 0);
v_snd_1446_ = lean_ctor_get(v_a_1438_, 1);
v___x_1447_ = lean_array_get_size(v_buckets_1441_);
v___x_1448_ = l_String_instHashableRaw_hash(v_fst_1445_);
v___x_1449_ = l_String_instHashableRaw_hash(v_snd_1446_);
v___x_1450_ = lean_uint64_mix_hash(v___x_1448_, v___x_1449_);
v___x_1451_ = 32ULL;
v___x_1452_ = lean_uint64_shift_right(v___x_1450_, v___x_1451_);
v_fold_1453_ = lean_uint64_xor(v___x_1450_, v___x_1452_);
v___x_1454_ = 16ULL;
v___x_1455_ = lean_uint64_shift_right(v_fold_1453_, v___x_1454_);
v___x_1456_ = lean_uint64_xor(v_fold_1453_, v___x_1455_);
v___x_1457_ = lean_uint64_to_usize(v___x_1456_);
v___x_1458_ = lean_usize_of_nat(v___x_1447_);
v___x_1459_ = ((size_t)1ULL);
v___x_1460_ = lean_usize_sub(v___x_1458_, v___x_1459_);
v___x_1461_ = lean_usize_land(v___x_1457_, v___x_1460_);
v_bkt_1462_ = lean_array_uget_borrowed(v_buckets_1441_, v___x_1461_);
v___x_1463_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_1438_, v_bkt_1462_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; lean_object* v_size_x27_1465_; lean_object* v___x_1466_; lean_object* v_buckets_x27_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; 
v___x_1464_ = lean_unsigned_to_nat(1u);
v_size_x27_1465_ = lean_nat_add(v_size_1440_, v___x_1464_);
lean_dec(v_size_1440_);
lean_inc(v_bkt_1462_);
v___x_1466_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1466_, 0, v_a_1438_);
lean_ctor_set(v___x_1466_, 1, v_b_1439_);
lean_ctor_set(v___x_1466_, 2, v_bkt_1462_);
v_buckets_x27_1467_ = lean_array_uset(v_buckets_1441_, v___x_1461_, v___x_1466_);
v___x_1468_ = lean_unsigned_to_nat(4u);
v___x_1469_ = lean_nat_mul(v_size_x27_1465_, v___x_1468_);
v___x_1470_ = lean_unsigned_to_nat(3u);
v___x_1471_ = lean_nat_div(v___x_1469_, v___x_1470_);
lean_dec(v___x_1469_);
v___x_1472_ = lean_array_get_size(v_buckets_x27_1467_);
v___x_1473_ = lean_nat_dec_le(v___x_1471_, v___x_1472_);
lean_dec(v___x_1471_);
if (v___x_1473_ == 0)
{
lean_object* v_val_1474_; lean_object* v___x_1476_; 
v_val_1474_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_buckets_x27_1467_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 1, v_val_1474_);
lean_ctor_set(v___x_1443_, 0, v_size_x27_1465_);
v___x_1476_ = v___x_1443_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_size_x27_1465_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v_val_1474_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
else
{
lean_object* v___x_1479_; 
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 1, v_buckets_x27_1467_);
lean_ctor_set(v___x_1443_, 0, v_size_x27_1465_);
v___x_1479_ = v___x_1443_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_size_x27_1465_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_buckets_x27_1467_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
else
{
lean_object* v___x_1481_; lean_object* v_buckets_x27_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1486_; 
lean_inc(v_bkt_1462_);
v___x_1481_ = lean_box(0);
v_buckets_x27_1482_ = lean_array_uset(v_buckets_1441_, v___x_1461_, v___x_1481_);
v___x_1483_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_1438_, v_b_1439_, v_bkt_1462_);
v___x_1484_ = lean_array_uset(v_buckets_x27_1482_, v___x_1461_, v___x_1483_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 1, v___x_1484_);
v___x_1486_ = v___x_1443_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_size_1440_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v___x_1484_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(uint8_t v___x_1491_, lean_object* v_as_1492_, size_t v_sz_1493_, size_t v_i_1494_, lean_object* v_b_1495_, lean_object* v___y_1496_){
_start:
{
uint8_t v___x_1498_; 
v___x_1498_ = lean_usize_dec_lt(v_i_1494_, v_sz_1493_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1499_, 0, v_b_1495_);
return v___x_1499_;
}
else
{
lean_object* v_snd_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1537_; 
v_snd_1500_ = lean_ctor_get(v_b_1495_, 1);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_b_1495_);
if (v_isSharedCheck_1537_ == 0)
{
lean_object* v_unused_1538_; 
v_unused_1538_ = lean_ctor_get(v_b_1495_, 0);
lean_dec(v_unused_1538_);
v___x_1502_ = v_b_1495_;
v_isShared_1503_ = v_isSharedCheck_1537_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_snd_1500_);
lean_dec(v_b_1495_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1537_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v_ref_1504_; lean_object* v_a_1505_; lean_object* v_ref_1506_; lean_object* v_msg_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1536_; 
v_ref_1504_ = lean_ctor_get(v___y_1496_, 5);
v_a_1505_ = lean_array_uget(v_as_1492_, v_i_1494_);
v_ref_1506_ = lean_ctor_get(v_a_1505_, 0);
v_msg_1507_ = lean_ctor_get(v_a_1505_, 1);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_a_1505_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1509_ = v_a_1505_;
v_isShared_1510_ = v_isSharedCheck_1536_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_msg_1507_);
lean_inc(v_ref_1506_);
lean_dec(v_a_1505_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1536_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1511_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v_ref_1528_; lean_object* v___y_1530_; lean_object* v___x_1533_; 
v___x_1511_ = lean_box(0);
v_ref_1528_ = l_Lean_replaceRef(v_ref_1506_, v_ref_1504_);
lean_dec(v_ref_1506_);
v___x_1533_ = l_Lean_Syntax_getPos_x3f(v_ref_1528_, v___x_1491_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_unsigned_to_nat(0u);
v___y_1530_ = v___x_1534_;
goto v___jp_1529_;
}
else
{
lean_object* v_val_1535_; 
v_val_1535_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_val_1535_);
lean_dec_ref_known(v___x_1533_, 1);
v___y_1530_ = v_val_1535_;
goto v___jp_1529_;
}
v___jp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 1, v___y_1514_);
lean_ctor_set(v___x_1502_, 0, v___y_1513_);
v___x_1516_ = v___x_1502_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___y_1513_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v___y_1514_);
v___x_1516_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v_pos2traces_1520_; lean_object* v___x_1522_; 
v___x_1517_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1518_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1500_, v___x_1516_, v___x_1517_);
v___x_1519_ = lean_array_push(v___x_1518_, v_msg_1507_);
v_pos2traces_1520_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1500_, v___x_1516_, v___x_1519_);
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 1, v_pos2traces_1520_);
lean_ctor_set(v___x_1509_, 0, v___x_1511_);
v___x_1522_ = v___x_1509_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1511_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v_pos2traces_1520_);
v___x_1522_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
size_t v___x_1523_; size_t v___x_1524_; 
v___x_1523_ = ((size_t)1ULL);
v___x_1524_ = lean_usize_add(v_i_1494_, v___x_1523_);
v_i_1494_ = v___x_1524_;
v_b_1495_ = v___x_1522_;
goto _start;
}
}
}
v___jp_1529_:
{
lean_object* v___x_1531_; 
v___x_1531_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1528_, v___x_1491_);
lean_dec(v_ref_1528_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_inc(v___y_1530_);
v___y_1513_ = v___y_1530_;
v___y_1514_ = v___y_1530_;
goto v___jp_1512_;
}
else
{
lean_object* v_val_1532_; 
v_val_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_val_1532_);
lean_dec_ref_known(v___x_1531_, 1);
v___y_1513_ = v___y_1530_;
v___y_1514_ = v_val_1532_;
goto v___jp_1512_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___boxed(lean_object* v___x_1539_, lean_object* v_as_1540_, lean_object* v_sz_1541_, lean_object* v_i_1542_, lean_object* v_b_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
uint8_t v___x_37830__boxed_1546_; size_t v_sz_boxed_1547_; size_t v_i_boxed_1548_; lean_object* v_res_1549_; 
v___x_37830__boxed_1546_ = lean_unbox(v___x_1539_);
v_sz_boxed_1547_ = lean_unbox_usize(v_sz_1541_);
lean_dec(v_sz_1541_);
v_i_boxed_1548_ = lean_unbox_usize(v_i_1542_);
lean_dec(v_i_1542_);
v_res_1549_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_37830__boxed_1546_, v_as_1540_, v_sz_boxed_1547_, v_i_boxed_1548_, v_b_1543_, v___y_1544_);
lean_dec_ref(v___y_1544_);
lean_dec_ref(v_as_1540_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(uint8_t v___x_1550_, lean_object* v_as_1551_, size_t v_sz_1552_, size_t v_i_1553_, lean_object* v_b_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
uint8_t v___x_1558_; 
v___x_1558_ = lean_usize_dec_lt(v_i_1553_, v_sz_1552_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1559_, 0, v_b_1554_);
return v___x_1559_;
}
else
{
lean_object* v_snd_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1597_; 
v_snd_1560_ = lean_ctor_get(v_b_1554_, 1);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_b_1554_);
if (v_isSharedCheck_1597_ == 0)
{
lean_object* v_unused_1598_; 
v_unused_1598_ = lean_ctor_get(v_b_1554_, 0);
lean_dec(v_unused_1598_);
v___x_1562_ = v_b_1554_;
v_isShared_1563_ = v_isSharedCheck_1597_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_snd_1560_);
lean_dec(v_b_1554_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1597_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v_ref_1564_; lean_object* v_a_1565_; lean_object* v_ref_1566_; lean_object* v_msg_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1596_; 
v_ref_1564_ = lean_ctor_get(v___y_1555_, 5);
v_a_1565_ = lean_array_uget(v_as_1551_, v_i_1553_);
v_ref_1566_ = lean_ctor_get(v_a_1565_, 0);
v_msg_1567_ = lean_ctor_get(v_a_1565_, 1);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_a_1565_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1569_ = v_a_1565_;
v_isShared_1570_ = v_isSharedCheck_1596_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_msg_1567_);
lean_inc(v_ref_1566_);
lean_dec(v_a_1565_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1596_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1571_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v_ref_1588_; lean_object* v___y_1590_; lean_object* v___x_1593_; 
v___x_1571_ = lean_box(0);
v_ref_1588_ = l_Lean_replaceRef(v_ref_1566_, v_ref_1564_);
lean_dec(v_ref_1566_);
v___x_1593_ = l_Lean_Syntax_getPos_x3f(v_ref_1588_, v___x_1550_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v___x_1594_; 
v___x_1594_ = lean_unsigned_to_nat(0u);
v___y_1590_ = v___x_1594_;
goto v___jp_1589_;
}
else
{
lean_object* v_val_1595_; 
v_val_1595_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_val_1595_);
lean_dec_ref_known(v___x_1593_, 1);
v___y_1590_ = v_val_1595_;
goto v___jp_1589_;
}
v___jp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 1, v___y_1574_);
lean_ctor_set(v___x_1562_, 0, v___y_1573_);
v___x_1576_ = v___x_1562_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___y_1573_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v___y_1574_);
v___x_1576_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v_pos2traces_1580_; lean_object* v___x_1582_; 
v___x_1577_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1578_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1560_, v___x_1576_, v___x_1577_);
v___x_1579_ = lean_array_push(v___x_1578_, v_msg_1567_);
v_pos2traces_1580_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1560_, v___x_1576_, v___x_1579_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 1, v_pos2traces_1580_);
lean_ctor_set(v___x_1569_, 0, v___x_1571_);
v___x_1582_ = v___x_1569_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1586_, 1, v_pos2traces_1580_);
v___x_1582_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
size_t v___x_1583_; size_t v___x_1584_; lean_object* v___x_1585_; 
v___x_1583_ = ((size_t)1ULL);
v___x_1584_ = lean_usize_add(v_i_1553_, v___x_1583_);
v___x_1585_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_1550_, v_as_1551_, v_sz_1552_, v___x_1584_, v___x_1582_, v___y_1555_);
return v___x_1585_;
}
}
}
v___jp_1589_:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1588_, v___x_1550_);
lean_dec(v_ref_1588_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_inc(v___y_1590_);
v___y_1573_ = v___y_1590_;
v___y_1574_ = v___y_1590_;
goto v___jp_1572_;
}
else
{
lean_object* v_val_1592_; 
v_val_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_val_1592_);
lean_dec_ref_known(v___x_1591_, 1);
v___y_1573_ = v___y_1590_;
v___y_1574_ = v_val_1592_;
goto v___jp_1572_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40___boxed(lean_object* v___x_1599_, lean_object* v_as_1600_, lean_object* v_sz_1601_, lean_object* v_i_1602_, lean_object* v_b_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
uint8_t v___x_37911__boxed_1607_; size_t v_sz_boxed_1608_; size_t v_i_boxed_1609_; lean_object* v_res_1610_; 
v___x_37911__boxed_1607_ = lean_unbox(v___x_1599_);
v_sz_boxed_1608_ = lean_unbox_usize(v_sz_1601_);
lean_dec(v_sz_1601_);
v_i_boxed_1609_ = lean_unbox_usize(v_i_1602_);
lean_dec(v_i_1602_);
v_res_1610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_37911__boxed_1607_, v_as_1600_, v_sz_boxed_1608_, v_i_boxed_1609_, v_b_1603_, v___y_1604_, v___y_1605_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec_ref(v_as_1600_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(lean_object* v_init_1611_, uint8_t v___x_1612_, lean_object* v_n_1613_, lean_object* v_b_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
if (lean_obj_tag(v_n_1613_) == 0)
{
lean_object* v_cs_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; size_t v_sz_1621_; size_t v___x_1622_; lean_object* v___x_1623_; 
v_cs_1618_ = lean_ctor_get(v_n_1613_, 0);
v___x_1619_ = lean_box(0);
v___x_1620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
lean_ctor_set(v___x_1620_, 1, v_b_1614_);
v_sz_1621_ = lean_array_size(v_cs_1618_);
v___x_1622_ = ((size_t)0ULL);
v___x_1623_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_1611_, v___x_1612_, v_cs_1618_, v_sz_1621_, v___x_1622_, v___x_1620_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1638_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1626_ = v___x_1623_;
v_isShared_1627_ = v_isSharedCheck_1638_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1623_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1638_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v_fst_1628_; 
v_fst_1628_ = lean_ctor_get(v_a_1624_, 0);
if (lean_obj_tag(v_fst_1628_) == 0)
{
lean_object* v_snd_1629_; lean_object* v___x_1630_; lean_object* v___x_1632_; 
v_snd_1629_ = lean_ctor_get(v_a_1624_, 1);
lean_inc(v_snd_1629_);
lean_dec(v_a_1624_);
v___x_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1630_, 0, v_snd_1629_);
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 0, v___x_1630_);
v___x_1632_ = v___x_1626_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1630_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
else
{
lean_object* v_val_1634_; lean_object* v___x_1636_; 
lean_inc_ref(v_fst_1628_);
lean_dec(v_a_1624_);
v_val_1634_ = lean_ctor_get(v_fst_1628_, 0);
lean_inc(v_val_1634_);
lean_dec_ref_known(v_fst_1628_, 1);
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 0, v_val_1634_);
v___x_1636_ = v___x_1626_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_val_1634_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
v_a_1639_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1623_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1623_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
else
{
lean_object* v_vs_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; size_t v_sz_1650_; size_t v___x_1651_; lean_object* v___x_1652_; 
v_vs_1647_ = lean_ctor_get(v_n_1613_, 0);
v___x_1648_ = lean_box(0);
v___x_1649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
lean_ctor_set(v___x_1649_, 1, v_b_1614_);
v_sz_1650_ = lean_array_size(v_vs_1647_);
v___x_1651_ = ((size_t)0ULL);
v___x_1652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_1612_, v_vs_1647_, v_sz_1650_, v___x_1651_, v___x_1649_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1667_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1655_ = v___x_1652_;
v_isShared_1656_ = v_isSharedCheck_1667_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1652_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1667_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v_fst_1657_; 
v_fst_1657_ = lean_ctor_get(v_a_1653_, 0);
if (lean_obj_tag(v_fst_1657_) == 0)
{
lean_object* v_snd_1658_; lean_object* v___x_1659_; lean_object* v___x_1661_; 
v_snd_1658_ = lean_ctor_get(v_a_1653_, 1);
lean_inc(v_snd_1658_);
lean_dec(v_a_1653_);
v___x_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1659_, 0, v_snd_1658_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1659_);
v___x_1661_ = v___x_1655_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
else
{
lean_object* v_val_1663_; lean_object* v___x_1665_; 
lean_inc_ref(v_fst_1657_);
lean_dec(v_a_1653_);
v_val_1663_ = lean_ctor_get(v_fst_1657_, 0);
lean_inc(v_val_1663_);
lean_dec_ref_known(v_fst_1657_, 1);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v_val_1663_);
v___x_1665_ = v___x_1655_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_val_1663_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
v_a_1668_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1652_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1652_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(lean_object* v_init_1676_, uint8_t v___x_1677_, lean_object* v_as_1678_, size_t v_sz_1679_, size_t v_i_1680_, lean_object* v_b_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
uint8_t v___x_1685_; 
v___x_1685_ = lean_usize_dec_lt(v_i_1680_, v_sz_1679_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; 
v___x_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1686_, 0, v_b_1681_);
return v___x_1686_;
}
else
{
lean_object* v_snd_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1721_; 
v_snd_1687_ = lean_ctor_get(v_b_1681_, 1);
v_isSharedCheck_1721_ = !lean_is_exclusive(v_b_1681_);
if (v_isSharedCheck_1721_ == 0)
{
lean_object* v_unused_1722_; 
v_unused_1722_ = lean_ctor_get(v_b_1681_, 0);
lean_dec(v_unused_1722_);
v___x_1689_ = v_b_1681_;
v_isShared_1690_ = v_isSharedCheck_1721_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_snd_1687_);
lean_dec(v_b_1681_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1721_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v_a_1691_; lean_object* v___x_1692_; 
v_a_1691_ = lean_array_uget_borrowed(v_as_1678_, v_i_1680_);
lean_inc(v_snd_1687_);
v___x_1692_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1676_, v___x_1677_, v_a_1691_, v_snd_1687_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1712_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1695_ = v___x_1692_;
v_isShared_1696_ = v_isSharedCheck_1712_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1692_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1712_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
if (lean_obj_tag(v_a_1693_) == 0)
{
lean_object* v___x_1697_; lean_object* v___x_1699_; 
v___x_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1697_, 0, v_a_1693_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 0, v___x_1697_);
v___x_1699_ = v___x_1689_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1697_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v_snd_1687_);
v___x_1699_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
lean_object* v___x_1701_; 
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 0, v___x_1699_);
v___x_1701_ = v___x_1695_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
else
{
lean_object* v_a_1704_; lean_object* v___x_1705_; lean_object* v___x_1707_; 
lean_del_object(v___x_1695_);
lean_dec(v_snd_1687_);
v_a_1704_ = lean_ctor_get(v_a_1693_, 0);
lean_inc(v_a_1704_);
lean_dec_ref_known(v_a_1693_, 1);
v___x_1705_ = lean_box(0);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 1, v_a_1704_);
lean_ctor_set(v___x_1689_, 0, v___x_1705_);
v___x_1707_ = v___x_1689_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1705_);
lean_ctor_set(v_reuseFailAlloc_1711_, 1, v_a_1704_);
v___x_1707_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
size_t v___x_1708_; size_t v___x_1709_; 
v___x_1708_ = ((size_t)1ULL);
v___x_1709_ = lean_usize_add(v_i_1680_, v___x_1708_);
v_i_1680_ = v___x_1709_;
v_b_1681_ = v___x_1707_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
lean_del_object(v___x_1689_);
lean_dec(v_snd_1687_);
v_a_1713_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1692_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1692_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39___boxed(lean_object* v_init_1723_, lean_object* v___x_1724_, lean_object* v_as_1725_, lean_object* v_sz_1726_, lean_object* v_i_1727_, lean_object* v_b_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
uint8_t v___x_37992__boxed_1732_; size_t v_sz_boxed_1733_; size_t v_i_boxed_1734_; lean_object* v_res_1735_; 
v___x_37992__boxed_1732_ = lean_unbox(v___x_1724_);
v_sz_boxed_1733_ = lean_unbox_usize(v_sz_1726_);
lean_dec(v_sz_1726_);
v_i_boxed_1734_ = lean_unbox_usize(v_i_1727_);
lean_dec(v_i_1727_);
v_res_1735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_1723_, v___x_37992__boxed_1732_, v_as_1725_, v_sz_boxed_1733_, v_i_boxed_1734_, v_b_1728_, v___y_1729_, v___y_1730_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec_ref(v_as_1725_);
lean_dec_ref(v_init_1723_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27___boxed(lean_object* v_init_1736_, lean_object* v___x_1737_, lean_object* v_n_1738_, lean_object* v_b_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
uint8_t v___x_38012__boxed_1743_; lean_object* v_res_1744_; 
v___x_38012__boxed_1743_ = lean_unbox(v___x_1737_);
v_res_1744_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1736_, v___x_38012__boxed_1743_, v_n_1738_, v_b_1739_, v___y_1740_, v___y_1741_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec_ref(v_n_1738_);
lean_dec_ref(v_init_1736_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(uint8_t v___x_1745_, lean_object* v_as_1746_, size_t v_sz_1747_, size_t v_i_1748_, lean_object* v_b_1749_, lean_object* v___y_1750_){
_start:
{
uint8_t v___x_1752_; 
v___x_1752_ = lean_usize_dec_lt(v_i_1748_, v_sz_1747_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; 
v___x_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1753_, 0, v_b_1749_);
return v___x_1753_;
}
else
{
lean_object* v_snd_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1791_; 
v_snd_1754_ = lean_ctor_get(v_b_1749_, 1);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_b_1749_);
if (v_isSharedCheck_1791_ == 0)
{
lean_object* v_unused_1792_; 
v_unused_1792_ = lean_ctor_get(v_b_1749_, 0);
lean_dec(v_unused_1792_);
v___x_1756_ = v_b_1749_;
v_isShared_1757_ = v_isSharedCheck_1791_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_snd_1754_);
lean_dec(v_b_1749_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1791_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v_ref_1758_; lean_object* v_a_1759_; lean_object* v_ref_1760_; lean_object* v_msg_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1790_; 
v_ref_1758_ = lean_ctor_get(v___y_1750_, 5);
v_a_1759_ = lean_array_uget(v_as_1746_, v_i_1748_);
v_ref_1760_ = lean_ctor_get(v_a_1759_, 0);
v_msg_1761_ = lean_ctor_get(v_a_1759_, 1);
v_isSharedCheck_1790_ = !lean_is_exclusive(v_a_1759_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1763_ = v_a_1759_;
v_isShared_1764_ = v_isSharedCheck_1790_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_msg_1761_);
lean_inc(v_ref_1760_);
lean_dec(v_a_1759_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1790_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1765_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v_ref_1782_; lean_object* v___y_1784_; lean_object* v___x_1787_; 
v___x_1765_ = lean_box(0);
v_ref_1782_ = l_Lean_replaceRef(v_ref_1760_, v_ref_1758_);
lean_dec(v_ref_1760_);
v___x_1787_ = l_Lean_Syntax_getPos_x3f(v_ref_1782_, v___x_1745_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v___x_1788_; 
v___x_1788_ = lean_unsigned_to_nat(0u);
v___y_1784_ = v___x_1788_;
goto v___jp_1783_;
}
else
{
lean_object* v_val_1789_; 
v_val_1789_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_val_1789_);
lean_dec_ref_known(v___x_1787_, 1);
v___y_1784_ = v_val_1789_;
goto v___jp_1783_;
}
v___jp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 1, v___y_1768_);
lean_ctor_set(v___x_1756_, 0, v___y_1767_);
v___x_1770_ = v___x_1756_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___y_1767_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v___y_1768_);
v___x_1770_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v_pos2traces_1774_; lean_object* v___x_1776_; 
v___x_1771_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1772_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1754_, v___x_1770_, v___x_1771_);
v___x_1773_ = lean_array_push(v___x_1772_, v_msg_1761_);
v_pos2traces_1774_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1754_, v___x_1770_, v___x_1773_);
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 1, v_pos2traces_1774_);
lean_ctor_set(v___x_1763_, 0, v___x_1765_);
v___x_1776_ = v___x_1763_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1765_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v_pos2traces_1774_);
v___x_1776_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
size_t v___x_1777_; size_t v___x_1778_; 
v___x_1777_ = ((size_t)1ULL);
v___x_1778_ = lean_usize_add(v_i_1748_, v___x_1777_);
v_i_1748_ = v___x_1778_;
v_b_1749_ = v___x_1776_;
goto _start;
}
}
}
v___jp_1783_:
{
lean_object* v___x_1785_; 
v___x_1785_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1782_, v___x_1745_);
lean_dec(v_ref_1782_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_inc(v___y_1784_);
v___y_1767_ = v___y_1784_;
v___y_1768_ = v___y_1784_;
goto v___jp_1766_;
}
else
{
lean_object* v_val_1786_; 
v_val_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_val_1786_);
lean_dec_ref_known(v___x_1785_, 1);
v___y_1767_ = v___y_1784_;
v___y_1768_ = v_val_1786_;
goto v___jp_1766_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg___boxed(lean_object* v___x_1793_, lean_object* v_as_1794_, lean_object* v_sz_1795_, lean_object* v_i_1796_, lean_object* v_b_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
uint8_t v___x_38195__boxed_1800_; size_t v_sz_boxed_1801_; size_t v_i_boxed_1802_; lean_object* v_res_1803_; 
v___x_38195__boxed_1800_ = lean_unbox(v___x_1793_);
v_sz_boxed_1801_ = lean_unbox_usize(v_sz_1795_);
lean_dec(v_sz_1795_);
v_i_boxed_1802_ = lean_unbox_usize(v_i_1796_);
lean_dec(v_i_1796_);
v_res_1803_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_38195__boxed_1800_, v_as_1794_, v_sz_boxed_1801_, v_i_boxed_1802_, v_b_1797_, v___y_1798_);
lean_dec_ref(v___y_1798_);
lean_dec_ref(v_as_1794_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(uint8_t v___x_1804_, lean_object* v_as_1805_, size_t v_sz_1806_, size_t v_i_1807_, lean_object* v_b_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
uint8_t v___x_1812_; 
v___x_1812_ = lean_usize_dec_lt(v_i_1807_, v_sz_1806_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; 
v___x_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1813_, 0, v_b_1808_);
return v___x_1813_;
}
else
{
lean_object* v_snd_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1851_; 
v_snd_1814_ = lean_ctor_get(v_b_1808_, 1);
v_isSharedCheck_1851_ = !lean_is_exclusive(v_b_1808_);
if (v_isSharedCheck_1851_ == 0)
{
lean_object* v_unused_1852_; 
v_unused_1852_ = lean_ctor_get(v_b_1808_, 0);
lean_dec(v_unused_1852_);
v___x_1816_ = v_b_1808_;
v_isShared_1817_ = v_isSharedCheck_1851_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_snd_1814_);
lean_dec(v_b_1808_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1851_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v_ref_1818_; lean_object* v_a_1819_; lean_object* v_ref_1820_; lean_object* v_msg_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1850_; 
v_ref_1818_ = lean_ctor_get(v___y_1809_, 5);
v_a_1819_ = lean_array_uget(v_as_1805_, v_i_1807_);
v_ref_1820_ = lean_ctor_get(v_a_1819_, 0);
v_msg_1821_ = lean_ctor_get(v_a_1819_, 1);
v_isSharedCheck_1850_ = !lean_is_exclusive(v_a_1819_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1823_ = v_a_1819_;
v_isShared_1824_ = v_isSharedCheck_1850_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_msg_1821_);
lean_inc(v_ref_1820_);
lean_dec(v_a_1819_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1850_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1825_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v_ref_1842_; lean_object* v___y_1844_; lean_object* v___x_1847_; 
v___x_1825_ = lean_box(0);
v_ref_1842_ = l_Lean_replaceRef(v_ref_1820_, v_ref_1818_);
lean_dec(v_ref_1820_);
v___x_1847_ = l_Lean_Syntax_getPos_x3f(v_ref_1842_, v___x_1804_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v___x_1848_; 
v___x_1848_ = lean_unsigned_to_nat(0u);
v___y_1844_ = v___x_1848_;
goto v___jp_1843_;
}
else
{
lean_object* v_val_1849_; 
v_val_1849_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_val_1849_);
lean_dec_ref_known(v___x_1847_, 1);
v___y_1844_ = v_val_1849_;
goto v___jp_1843_;
}
v___jp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 1, v___y_1828_);
lean_ctor_set(v___x_1816_, 0, v___y_1827_);
v___x_1830_ = v___x_1816_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___y_1827_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v___y_1828_);
v___x_1830_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v_pos2traces_1834_; lean_object* v___x_1836_; 
v___x_1831_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1832_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1814_, v___x_1830_, v___x_1831_);
v___x_1833_ = lean_array_push(v___x_1832_, v_msg_1821_);
v_pos2traces_1834_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1814_, v___x_1830_, v___x_1833_);
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 1, v_pos2traces_1834_);
lean_ctor_set(v___x_1823_, 0, v___x_1825_);
v___x_1836_ = v___x_1823_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1825_);
lean_ctor_set(v_reuseFailAlloc_1840_, 1, v_pos2traces_1834_);
v___x_1836_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
size_t v___x_1837_; size_t v___x_1838_; lean_object* v___x_1839_; 
v___x_1837_ = ((size_t)1ULL);
v___x_1838_ = lean_usize_add(v_i_1807_, v___x_1837_);
v___x_1839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_1804_, v_as_1805_, v_sz_1806_, v___x_1838_, v___x_1836_, v___y_1809_);
return v___x_1839_;
}
}
}
v___jp_1843_:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1842_, v___x_1804_);
lean_dec(v_ref_1842_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_inc(v___y_1844_);
v___y_1827_ = v___y_1844_;
v___y_1828_ = v___y_1844_;
goto v___jp_1826_;
}
else
{
lean_object* v_val_1846_; 
v_val_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_val_1846_);
lean_dec_ref_known(v___x_1845_, 1);
v___y_1827_ = v___y_1844_;
v___y_1828_ = v_val_1846_;
goto v___jp_1826_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28___boxed(lean_object* v___x_1853_, lean_object* v_as_1854_, lean_object* v_sz_1855_, lean_object* v_i_1856_, lean_object* v_b_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
uint8_t v___x_38275__boxed_1861_; size_t v_sz_boxed_1862_; size_t v_i_boxed_1863_; lean_object* v_res_1864_; 
v___x_38275__boxed_1861_ = lean_unbox(v___x_1853_);
v_sz_boxed_1862_ = lean_unbox_usize(v_sz_1855_);
lean_dec(v_sz_1855_);
v_i_boxed_1863_ = lean_unbox_usize(v_i_1856_);
lean_dec(v_i_1856_);
v_res_1864_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_38275__boxed_1861_, v_as_1854_, v_sz_boxed_1862_, v_i_boxed_1863_, v_b_1857_, v___y_1858_, v___y_1859_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec_ref(v_as_1854_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(uint8_t v___x_1865_, lean_object* v_t_1866_, lean_object* v_init_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v_root_1871_; lean_object* v_tail_1872_; lean_object* v___x_1873_; 
v_root_1871_ = lean_ctor_get(v_t_1866_, 0);
v_tail_1872_ = lean_ctor_get(v_t_1866_, 1);
lean_inc_ref(v_init_1867_);
v___x_1873_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1867_, v___x_1865_, v_root_1871_, v_init_1867_, v___y_1868_, v___y_1869_);
lean_dec_ref(v_init_1867_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1910_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1910_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1873_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1910_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
if (lean_obj_tag(v_a_1874_) == 0)
{
lean_object* v_a_1878_; lean_object* v___x_1880_; 
v_a_1878_ = lean_ctor_get(v_a_1874_, 0);
lean_inc(v_a_1878_);
lean_dec_ref_known(v_a_1874_, 1);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v_a_1878_);
v___x_1880_ = v___x_1876_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1878_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; size_t v_sz_1885_; size_t v___x_1886_; lean_object* v___x_1887_; 
lean_del_object(v___x_1876_);
v_a_1882_ = lean_ctor_get(v_a_1874_, 0);
lean_inc(v_a_1882_);
lean_dec_ref_known(v_a_1874_, 1);
v___x_1883_ = lean_box(0);
v___x_1884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
lean_ctor_set(v___x_1884_, 1, v_a_1882_);
v_sz_1885_ = lean_array_size(v_tail_1872_);
v___x_1886_ = ((size_t)0ULL);
v___x_1887_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_1865_, v_tail_1872_, v_sz_1885_, v___x_1886_, v___x_1884_, v___y_1868_, v___y_1869_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1901_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1890_ = v___x_1887_;
v_isShared_1891_ = v_isSharedCheck_1901_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1887_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1901_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v_fst_1892_; 
v_fst_1892_ = lean_ctor_get(v_a_1888_, 0);
if (lean_obj_tag(v_fst_1892_) == 0)
{
lean_object* v_snd_1893_; lean_object* v___x_1895_; 
v_snd_1893_ = lean_ctor_get(v_a_1888_, 1);
lean_inc(v_snd_1893_);
lean_dec(v_a_1888_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v_snd_1893_);
v___x_1895_ = v___x_1890_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_snd_1893_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
else
{
lean_object* v_val_1897_; lean_object* v___x_1899_; 
lean_inc_ref(v_fst_1892_);
lean_dec(v_a_1888_);
v_val_1897_ = lean_ctor_get(v_fst_1892_, 0);
lean_inc(v_val_1897_);
lean_dec_ref_known(v_fst_1892_, 1);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v_val_1897_);
v___x_1899_ = v___x_1890_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_val_1897_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
v_a_1902_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1887_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1887_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
}
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
v_a_1911_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1873_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1873_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19___boxed(lean_object* v___x_1919_, lean_object* v_t_1920_, lean_object* v_init_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
uint8_t v___x_38356__boxed_1925_; lean_object* v_res_1926_; 
v___x_38356__boxed_1925_ = lean_unbox(v___x_1919_);
v_res_1926_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_38356__boxed_1925_, v_t_1920_, v_init_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec_ref(v_t_1920_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(lean_object* v_x_1927_, lean_object* v_x_1928_){
_start:
{
if (lean_obj_tag(v_x_1928_) == 0)
{
return v_x_1927_;
}
else
{
lean_object* v_key_1929_; lean_object* v_value_1930_; lean_object* v_tail_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v_key_1929_ = lean_ctor_get(v_x_1928_, 0);
v_value_1930_ = lean_ctor_get(v_x_1928_, 1);
v_tail_1931_ = lean_ctor_get(v_x_1928_, 2);
lean_inc(v_value_1930_);
lean_inc(v_key_1929_);
v___x_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1932_, 0, v_key_1929_);
lean_ctor_set(v___x_1932_, 1, v_value_1930_);
v___x_1933_ = lean_array_push(v_x_1927_, v___x_1932_);
v_x_1927_ = v___x_1933_;
v_x_1928_ = v_tail_1931_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22___boxed(lean_object* v_x_1935_, lean_object* v_x_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_x_1935_, v_x_1936_);
lean_dec(v_x_1936_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(lean_object* v_as_1938_, size_t v_i_1939_, size_t v_stop_1940_, lean_object* v_b_1941_){
_start:
{
uint8_t v___x_1942_; 
v___x_1942_ = lean_usize_dec_eq(v_i_1939_, v_stop_1940_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; lean_object* v___x_1944_; size_t v___x_1945_; size_t v___x_1946_; 
v___x_1943_ = lean_array_uget_borrowed(v_as_1938_, v_i_1939_);
v___x_1944_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_b_1941_, v___x_1943_);
v___x_1945_ = ((size_t)1ULL);
v___x_1946_ = lean_usize_add(v_i_1939_, v___x_1945_);
v_i_1939_ = v___x_1946_;
v_b_1941_ = v___x_1944_;
goto _start;
}
else
{
return v_b_1941_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23___boxed(lean_object* v_as_1948_, lean_object* v_i_1949_, lean_object* v_stop_1950_, lean_object* v_b_1951_){
_start:
{
size_t v_i_boxed_1952_; size_t v_stop_boxed_1953_; lean_object* v_res_1954_; 
v_i_boxed_1952_ = lean_unbox_usize(v_i_1949_);
lean_dec(v_i_1949_);
v_stop_boxed_1953_ = lean_unbox_usize(v_stop_1950_);
lean_dec(v_stop_1950_);
v_res_1954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_as_1948_, v_i_boxed_1952_, v_stop_boxed_1953_, v_b_1951_);
lean_dec_ref(v_as_1948_);
return v_res_1954_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0(void){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1955_ = lean_unsigned_to_nat(32u);
v___x_1956_ = lean_mk_empty_array_with_capacity(v___x_1955_);
v___x_1957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1956_);
return v___x_1957_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1(void){
_start:
{
size_t v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1958_ = ((size_t)5ULL);
v___x_1959_ = lean_unsigned_to_nat(0u);
v___x_1960_ = lean_unsigned_to_nat(32u);
v___x_1961_ = lean_mk_empty_array_with_capacity(v___x_1960_);
v___x_1962_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0);
v___x_1963_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
lean_ctor_set(v___x_1963_, 1, v___x_1961_);
lean_ctor_set(v___x_1963_, 2, v___x_1959_);
lean_ctor_set(v___x_1963_, 3, v___x_1959_);
lean_ctor_set_usize(v___x_1963_, 4, v___x_1958_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(lean_object* v___y_1964_){
_start:
{
lean_object* v___x_1966_; lean_object* v_traceState_1967_; lean_object* v_traces_1968_; lean_object* v___x_1969_; lean_object* v_traceState_1970_; lean_object* v_env_1971_; lean_object* v_nextMacroScope_1972_; lean_object* v_ngen_1973_; lean_object* v_auxDeclNGen_1974_; lean_object* v_cache_1975_; lean_object* v_messages_1976_; lean_object* v_infoState_1977_; lean_object* v_snapshotTasks_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1997_; 
v___x_1966_ = lean_st_ref_get(v___y_1964_);
v_traceState_1967_ = lean_ctor_get(v___x_1966_, 4);
lean_inc_ref(v_traceState_1967_);
lean_dec(v___x_1966_);
v_traces_1968_ = lean_ctor_get(v_traceState_1967_, 0);
lean_inc_ref(v_traces_1968_);
lean_dec_ref(v_traceState_1967_);
v___x_1969_ = lean_st_ref_take(v___y_1964_);
v_traceState_1970_ = lean_ctor_get(v___x_1969_, 4);
v_env_1971_ = lean_ctor_get(v___x_1969_, 0);
v_nextMacroScope_1972_ = lean_ctor_get(v___x_1969_, 1);
v_ngen_1973_ = lean_ctor_get(v___x_1969_, 2);
v_auxDeclNGen_1974_ = lean_ctor_get(v___x_1969_, 3);
v_cache_1975_ = lean_ctor_get(v___x_1969_, 5);
v_messages_1976_ = lean_ctor_get(v___x_1969_, 6);
v_infoState_1977_ = lean_ctor_get(v___x_1969_, 7);
v_snapshotTasks_1978_ = lean_ctor_get(v___x_1969_, 8);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1980_ = v___x_1969_;
v_isShared_1981_ = v_isSharedCheck_1997_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_snapshotTasks_1978_);
lean_inc(v_infoState_1977_);
lean_inc(v_messages_1976_);
lean_inc(v_cache_1975_);
lean_inc(v_traceState_1970_);
lean_inc(v_auxDeclNGen_1974_);
lean_inc(v_ngen_1973_);
lean_inc(v_nextMacroScope_1972_);
lean_inc(v_env_1971_);
lean_dec(v___x_1969_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1997_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
uint64_t v_tid_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1995_; 
v_tid_1982_ = lean_ctor_get_uint64(v_traceState_1970_, sizeof(void*)*1);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_traceState_1970_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; 
v_unused_1996_ = lean_ctor_get(v_traceState_1970_, 0);
lean_dec(v_unused_1996_);
v___x_1984_ = v_traceState_1970_;
v_isShared_1985_ = v_isSharedCheck_1995_;
goto v_resetjp_1983_;
}
else
{
lean_dec(v_traceState_1970_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1995_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1986_; lean_object* v___x_1988_; 
v___x_1986_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v___x_1986_);
v___x_1988_ = v___x_1984_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1986_);
lean_ctor_set_uint64(v_reuseFailAlloc_1994_, sizeof(void*)*1, v_tid_1982_);
v___x_1988_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1990_; 
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 4, v___x_1988_);
v___x_1990_ = v___x_1980_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_env_1971_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_nextMacroScope_1972_);
lean_ctor_set(v_reuseFailAlloc_1993_, 2, v_ngen_1973_);
lean_ctor_set(v_reuseFailAlloc_1993_, 3, v_auxDeclNGen_1974_);
lean_ctor_set(v_reuseFailAlloc_1993_, 4, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_1993_, 5, v_cache_1975_);
lean_ctor_set(v_reuseFailAlloc_1993_, 6, v_messages_1976_);
lean_ctor_set(v_reuseFailAlloc_1993_, 7, v_infoState_1977_);
lean_ctor_set(v_reuseFailAlloc_1993_, 8, v_snapshotTasks_1978_);
v___x_1990_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1991_ = lean_st_ref_set(v___y_1964_, v___x_1990_);
v___x_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1992_, 0, v_traces_1968_);
return v___x_1992_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___boxed(lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_1998_);
lean_dec(v___y_1998_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(lean_object* v_hi_2001_, lean_object* v_pivot_2002_, lean_object* v_as_2003_, lean_object* v_i_2004_, lean_object* v_k_2005_){
_start:
{
uint8_t v___x_2006_; 
v___x_2006_ = lean_nat_dec_lt(v_k_2005_, v_hi_2001_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
lean_dec(v_k_2005_);
v___x_2007_ = lean_array_fswap(v_as_2003_, v_i_2004_, v_hi_2001_);
v___x_2008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2008_, 0, v_i_2004_);
lean_ctor_set(v___x_2008_, 1, v___x_2007_);
return v___x_2008_;
}
else
{
lean_object* v___x_2009_; lean_object* v_fst_2010_; lean_object* v_fst_2011_; lean_object* v_fst_2012_; lean_object* v_fst_2013_; uint8_t v___x_2014_; 
v___x_2009_ = lean_array_fget_borrowed(v_as_2003_, v_k_2005_);
v_fst_2010_ = lean_ctor_get(v___x_2009_, 0);
v_fst_2011_ = lean_ctor_get(v_pivot_2002_, 0);
v_fst_2012_ = lean_ctor_get(v_fst_2010_, 0);
v_fst_2013_ = lean_ctor_get(v_fst_2011_, 0);
v___x_2014_ = lean_nat_dec_lt(v_fst_2012_, v_fst_2013_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = lean_unsigned_to_nat(1u);
v___x_2016_ = lean_nat_add(v_k_2005_, v___x_2015_);
lean_dec(v_k_2005_);
v_k_2005_ = v___x_2016_;
goto _start;
}
else
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2018_ = lean_array_fswap(v_as_2003_, v_i_2004_, v_k_2005_);
v___x_2019_ = lean_unsigned_to_nat(1u);
v___x_2020_ = lean_nat_add(v_i_2004_, v___x_2019_);
lean_dec(v_i_2004_);
v___x_2021_ = lean_nat_add(v_k_2005_, v___x_2019_);
lean_dec(v_k_2005_);
v_as_2003_ = v___x_2018_;
v_i_2004_ = v___x_2020_;
v_k_2005_ = v___x_2021_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg___boxed(lean_object* v_hi_2023_, lean_object* v_pivot_2024_, lean_object* v_as_2025_, lean_object* v_i_2026_, lean_object* v_k_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_2023_, v_pivot_2024_, v_as_2025_, v_i_2026_, v_k_2027_);
lean_dec_ref(v_pivot_2024_);
lean_dec(v_hi_2023_);
return v_res_2028_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(lean_object* v_x_2029_, lean_object* v_x_2030_){
_start:
{
lean_object* v_fst_2031_; lean_object* v_fst_2032_; lean_object* v_fst_2033_; lean_object* v_fst_2034_; uint8_t v___x_2035_; 
v_fst_2031_ = lean_ctor_get(v_x_2029_, 0);
v_fst_2032_ = lean_ctor_get(v_x_2030_, 0);
v_fst_2033_ = lean_ctor_get(v_fst_2031_, 0);
v_fst_2034_ = lean_ctor_get(v_fst_2032_, 0);
v___x_2035_ = lean_nat_dec_lt(v_fst_2033_, v_fst_2034_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0___boxed(lean_object* v_x_2036_, lean_object* v_x_2037_){
_start:
{
uint8_t v_res_2038_; lean_object* v_r_2039_; 
v_res_2038_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v_x_2036_, v_x_2037_);
lean_dec_ref(v_x_2037_);
lean_dec_ref(v_x_2036_);
v_r_2039_ = lean_box(v_res_2038_);
return v_r_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(lean_object* v_n_2040_, lean_object* v_as_2041_, lean_object* v_lo_2042_, lean_object* v_hi_2043_){
_start:
{
lean_object* v___y_2045_; uint8_t v___x_2055_; 
v___x_2055_ = lean_nat_dec_lt(v_lo_2042_, v_hi_2043_);
if (v___x_2055_ == 0)
{
lean_dec(v_lo_2042_);
return v_as_2041_;
}
else
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v_mid_2058_; lean_object* v___y_2060_; lean_object* v___y_2066_; lean_object* v___x_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; 
v___x_2056_ = lean_nat_add(v_lo_2042_, v_hi_2043_);
v___x_2057_ = lean_unsigned_to_nat(1u);
v_mid_2058_ = lean_nat_shiftr(v___x_2056_, v___x_2057_);
lean_dec(v___x_2056_);
v___x_2071_ = lean_array_fget_borrowed(v_as_2041_, v_mid_2058_);
v___x_2072_ = lean_array_fget_borrowed(v_as_2041_, v_lo_2042_);
v___x_2073_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2071_, v___x_2072_);
if (v___x_2073_ == 0)
{
v___y_2066_ = v_as_2041_;
goto v___jp_2065_;
}
else
{
lean_object* v___x_2074_; 
v___x_2074_ = lean_array_fswap(v_as_2041_, v_lo_2042_, v_mid_2058_);
v___y_2066_ = v___x_2074_;
goto v___jp_2065_;
}
v___jp_2059_:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; 
v___x_2061_ = lean_array_fget_borrowed(v___y_2060_, v_mid_2058_);
v___x_2062_ = lean_array_fget_borrowed(v___y_2060_, v_hi_2043_);
v___x_2063_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2061_, v___x_2062_);
if (v___x_2063_ == 0)
{
lean_dec(v_mid_2058_);
v___y_2045_ = v___y_2060_;
goto v___jp_2044_;
}
else
{
lean_object* v___x_2064_; 
v___x_2064_ = lean_array_fswap(v___y_2060_, v_mid_2058_, v_hi_2043_);
lean_dec(v_mid_2058_);
v___y_2045_ = v___x_2064_;
goto v___jp_2044_;
}
}
v___jp_2065_:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; 
v___x_2067_ = lean_array_fget_borrowed(v___y_2066_, v_hi_2043_);
v___x_2068_ = lean_array_fget_borrowed(v___y_2066_, v_lo_2042_);
v___x_2069_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2067_, v___x_2068_);
if (v___x_2069_ == 0)
{
v___y_2060_ = v___y_2066_;
goto v___jp_2059_;
}
else
{
lean_object* v___x_2070_; 
v___x_2070_ = lean_array_fswap(v___y_2066_, v_lo_2042_, v_hi_2043_);
v___y_2060_ = v___x_2070_;
goto v___jp_2059_;
}
}
}
v___jp_2044_:
{
lean_object* v_pivot_2046_; lean_object* v___x_2047_; lean_object* v_fst_2048_; lean_object* v_snd_2049_; uint8_t v___x_2050_; 
v_pivot_2046_ = lean_array_fget(v___y_2045_, v_hi_2043_);
lean_inc_n(v_lo_2042_, 2);
v___x_2047_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_2043_, v_pivot_2046_, v___y_2045_, v_lo_2042_, v_lo_2042_);
lean_dec(v_pivot_2046_);
v_fst_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_fst_2048_);
v_snd_2049_ = lean_ctor_get(v___x_2047_, 1);
lean_inc(v_snd_2049_);
lean_dec_ref(v___x_2047_);
v___x_2050_ = lean_nat_dec_le(v_hi_2043_, v_fst_2048_);
if (v___x_2050_ == 0)
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2051_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_2040_, v_snd_2049_, v_lo_2042_, v_fst_2048_);
v___x_2052_ = lean_unsigned_to_nat(1u);
v___x_2053_ = lean_nat_add(v_fst_2048_, v___x_2052_);
lean_dec(v_fst_2048_);
v_as_2041_ = v___x_2051_;
v_lo_2042_ = v___x_2053_;
goto _start;
}
else
{
lean_dec(v_fst_2048_);
lean_dec(v_lo_2042_);
return v_snd_2049_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___boxed(lean_object* v_n_2075_, lean_object* v_as_2076_, lean_object* v_lo_2077_, lean_object* v_hi_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_2075_, v_as_2076_, v_lo_2077_, v_hi_2078_);
lean_dec(v_hi_2078_);
lean_dec(v_n_2075_);
return v_res_2079_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2080_ = lean_box(0);
v___x_2081_ = lean_unsigned_to_nat(16u);
v___x_2082_ = lean_mk_array(v___x_2081_, v___x_2080_);
return v___x_2082_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1(void){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v_pos2traces_2085_; 
v___x_2083_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0);
v___x_2084_ = lean_unsigned_to_nat(0u);
v_pos2traces_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_2085_, 0, v___x_2084_);
lean_ctor_set(v_pos2traces_2085_, 1, v___x_2083_);
return v_pos2traces_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10(lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v_options_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v_options_2092_ = lean_ctor_get(v___y_2086_, 2);
v___x_2093_ = l_Lean_trace_profiler_output;
v___x_2094_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(v_options_2092_, v___x_2093_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v___x_2095_; uint8_t v___x_2096_; 
v___x_2095_ = l_Lean_trace_profiler_serve;
v___x_2096_ = l_Lean_Option_get___at___00main_spec__8(v_options_2092_, v___x_2095_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2164_; 
v___x_2097_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_2087_);
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2100_ = v___x_2097_;
v_isShared_2101_ = v_isSharedCheck_2164_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2097_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2164_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
uint8_t v___x_2102_; 
v___x_2102_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_2098_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2103_; lean_object* v_pos2traces_2104_; lean_object* v___x_2105_; 
lean_del_object(v___x_2100_);
v___x_2103_ = lean_unsigned_to_nat(0u);
v_pos2traces_2104_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1);
v___x_2105_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_2102_, v_a_2098_, v_pos2traces_2104_, v___y_2086_, v___y_2087_);
lean_dec(v_a_2098_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v___y_2108_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2134_; lean_object* v_size_2140_; lean_object* v_buckets_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref_known(v___x_2105_, 1);
v_size_2140_ = lean_ctor_get(v_a_2106_, 0);
lean_inc(v_size_2140_);
v_buckets_2141_ = lean_ctor_get(v_a_2106_, 1);
lean_inc_ref(v_buckets_2141_);
lean_dec(v_a_2106_);
v___x_2142_ = lean_mk_empty_array_with_capacity(v_size_2140_);
lean_dec(v_size_2140_);
v___x_2143_ = lean_array_get_size(v_buckets_2141_);
v___x_2144_ = lean_nat_dec_lt(v___x_2103_, v___x_2143_);
if (v___x_2144_ == 0)
{
lean_dec_ref(v_buckets_2141_);
v___y_2134_ = v___x_2142_;
goto v___jp_2133_;
}
else
{
uint8_t v___x_2145_; 
v___x_2145_ = lean_nat_dec_le(v___x_2143_, v___x_2143_);
if (v___x_2145_ == 0)
{
if (v___x_2144_ == 0)
{
lean_dec_ref(v_buckets_2141_);
v___y_2134_ = v___x_2142_;
goto v___jp_2133_;
}
else
{
size_t v___x_2146_; size_t v___x_2147_; lean_object* v___x_2148_; 
v___x_2146_ = ((size_t)0ULL);
v___x_2147_ = lean_usize_of_nat(v___x_2143_);
v___x_2148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_buckets_2141_, v___x_2146_, v___x_2147_, v___x_2142_);
lean_dec_ref(v_buckets_2141_);
v___y_2134_ = v___x_2148_;
goto v___jp_2133_;
}
}
else
{
size_t v___x_2149_; size_t v___x_2150_; lean_object* v___x_2151_; 
v___x_2149_ = ((size_t)0ULL);
v___x_2150_ = lean_usize_of_nat(v___x_2143_);
v___x_2151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_buckets_2141_, v___x_2149_, v___x_2150_, v___x_2142_);
lean_dec_ref(v_buckets_2141_);
v___y_2134_ = v___x_2151_;
goto v___jp_2133_;
}
}
v___jp_2107_:
{
lean_object* v___x_2109_; size_t v_sz_2110_; size_t v___x_2111_; lean_object* v___x_2112_; 
v___x_2109_ = lean_box(0);
v_sz_2110_ = lean_array_size(v___y_2108_);
v___x_2111_ = ((size_t)0ULL);
v___x_2112_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_2096_, v___y_2108_, v_sz_2110_, v___x_2111_, v___x_2109_, v___y_2086_, v___y_2087_);
lean_dec_ref(v___y_2108_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2119_ == 0)
{
lean_object* v_unused_2120_; 
v_unused_2120_ = lean_ctor_get(v___x_2112_, 0);
lean_dec(v_unused_2120_);
v___x_2114_ = v___x_2112_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_dec(v___x_2112_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 0, v___x_2109_);
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2109_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
else
{
return v___x_2112_;
}
}
v___jp_2121_:
{
lean_object* v___x_2126_; 
v___x_2126_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
lean_dec(v___y_2125_);
lean_dec(v___y_2122_);
v___y_2108_ = v___x_2126_;
goto v___jp_2107_;
}
v___jp_2127_:
{
uint8_t v___x_2132_; 
v___x_2132_ = lean_nat_dec_le(v___y_2131_, v___y_2129_);
if (v___x_2132_ == 0)
{
lean_dec(v___y_2129_);
lean_inc(v___y_2131_);
v___y_2122_ = v___y_2128_;
v___y_2123_ = v___y_2130_;
v___y_2124_ = v___y_2131_;
v___y_2125_ = v___y_2131_;
goto v___jp_2121_;
}
else
{
v___y_2122_ = v___y_2128_;
v___y_2123_ = v___y_2130_;
v___y_2124_ = v___y_2131_;
v___y_2125_ = v___y_2129_;
goto v___jp_2121_;
}
}
v___jp_2133_:
{
lean_object* v___x_2135_; uint8_t v___x_2136_; 
v___x_2135_ = lean_array_get_size(v___y_2134_);
v___x_2136_ = lean_nat_dec_eq(v___x_2135_, v___x_2103_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; 
v___x_2137_ = lean_unsigned_to_nat(1u);
v___x_2138_ = lean_nat_sub(v___x_2135_, v___x_2137_);
v___x_2139_ = lean_nat_dec_le(v___x_2103_, v___x_2138_);
if (v___x_2139_ == 0)
{
lean_inc(v___x_2138_);
v___y_2128_ = v___x_2135_;
v___y_2129_ = v___x_2138_;
v___y_2130_ = v___y_2134_;
v___y_2131_ = v___x_2138_;
goto v___jp_2127_;
}
else
{
v___y_2128_ = v___x_2135_;
v___y_2129_ = v___x_2138_;
v___y_2130_ = v___y_2134_;
v___y_2131_ = v___x_2103_;
goto v___jp_2127_;
}
}
else
{
v___y_2108_ = v___y_2134_;
goto v___jp_2107_;
}
}
}
else
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
v_a_2152_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2105_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2105_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2152_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
else
{
lean_object* v___x_2160_; lean_object* v___x_2162_; 
lean_dec(v_a_2098_);
v___x_2160_ = lean_box(0);
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 0, v___x_2160_);
v___x_2162_ = v___x_2100_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
else
{
goto v___jp_2089_;
}
}
else
{
lean_dec_ref_known(v___x_2094_, 1);
goto v___jp_2089_;
}
v___jp_2089_:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2090_ = lean_box(0);
v___x_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
return v___x_2091_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10___boxed(lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2165_, v___y_2166_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(lean_object* v_as_2169_, size_t v_sz_2170_, size_t v_i_2171_, lean_object* v_b_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
uint8_t v___x_2176_; 
v___x_2176_ = lean_usize_dec_lt(v_i_2171_, v_sz_2170_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; 
v___x_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2177_, 0, v_b_2172_);
return v___x_2177_;
}
else
{
lean_object* v_options_2178_; lean_object* v_a_2179_; lean_object* v___x_2180_; 
v_options_2178_ = lean_ctor_get(v___y_2173_, 2);
v_a_2179_ = lean_array_uget_borrowed(v_as_2169_, v_i_2171_);
lean_inc_ref(v_options_2178_);
lean_inc(v_a_2179_);
v___x_2180_ = l_Lean_Compiler_LCNF_resumeCompilation(v_a_2179_, v_options_2178_, v___y_2173_, v___y_2174_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v___x_2181_; 
lean_dec_ref_known(v___x_2180_, 1);
v___x_2181_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2173_, v___y_2174_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v___x_2182_; size_t v___x_2183_; size_t v___x_2184_; 
lean_dec_ref_known(v___x_2181_, 1);
v___x_2182_ = lean_box(0);
v___x_2183_ = ((size_t)1ULL);
v___x_2184_ = lean_usize_add(v_i_2171_, v___x_2183_);
v_i_2171_ = v___x_2184_;
v_b_2172_ = v___x_2182_;
goto _start;
}
else
{
return v___x_2181_;
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2187_; 
v_a_2186_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2186_);
lean_dec_ref_known(v___x_2180_, 1);
v___x_2187_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2173_, v___y_2174_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2194_; 
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2194_ == 0)
{
lean_object* v_unused_2195_; 
v_unused_2195_ = lean_ctor_get(v___x_2187_, 0);
lean_dec(v_unused_2195_);
v___x_2189_ = v___x_2187_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_dec(v___x_2187_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2192_; 
if (v_isShared_2190_ == 0)
{
lean_ctor_set_tag(v___x_2189_, 1);
lean_ctor_set(v___x_2189_, 0, v_a_2186_);
v___x_2192_ = v___x_2189_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2186_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
else
{
lean_dec(v_a_2186_);
return v___x_2187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11___boxed(lean_object* v_as_2196_, lean_object* v_sz_2197_, lean_object* v_i_2198_, lean_object* v_b_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
size_t v_sz_boxed_2203_; size_t v_i_boxed_2204_; lean_object* v_res_2205_; 
v_sz_boxed_2203_ = lean_unbox_usize(v_sz_2197_);
lean_dec(v_sz_2197_);
v_i_boxed_2204_ = lean_unbox_usize(v_i_2198_);
lean_dec(v_i_2198_);
v_res_2205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_as_2196_, v_sz_boxed_2203_, v_i_boxed_2204_, v_b_2199_, v___y_2200_, v___y_2201_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec_ref(v_as_2196_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(lean_object* v_as_2206_, size_t v_sz_2207_, size_t v_i_2208_, lean_object* v_b_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
uint8_t v___x_2213_; 
v___x_2213_ = lean_usize_dec_lt(v_i_2208_, v_sz_2207_);
if (v___x_2213_ == 0)
{
lean_object* v___x_2214_; 
v___x_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2214_, 0, v_b_2209_);
return v___x_2214_;
}
else
{
lean_object* v_a_2215_; lean_object* v_declNames_2216_; lean_object* v___x_2217_; size_t v_sz_2218_; size_t v___x_2219_; lean_object* v___x_2220_; 
v_a_2215_ = lean_array_uget_borrowed(v_as_2206_, v_i_2208_);
v_declNames_2216_ = lean_ctor_get(v_a_2215_, 0);
v___x_2217_ = lean_box(0);
v_sz_2218_ = lean_array_size(v_declNames_2216_);
v___x_2219_ = ((size_t)0ULL);
v___x_2220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_declNames_2216_, v_sz_2218_, v___x_2219_, v___x_2217_, v___y_2210_, v___y_2211_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v___x_2221_; 
lean_dec_ref_known(v___x_2220_, 1);
v___x_2221_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v___y_2211_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v_unreported_2223_; lean_object* v___x_2224_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2222_);
lean_dec_ref_known(v___x_2221_, 1);
v_unreported_2223_ = lean_ctor_get(v_a_2222_, 1);
lean_inc_ref(v_unreported_2223_);
lean_dec(v_a_2222_);
v___x_2224_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(v_unreported_2223_, v___x_2217_, v___y_2210_, v___y_2211_);
lean_dec_ref(v_unreported_2223_);
if (lean_obj_tag(v___x_2224_) == 0)
{
size_t v___x_2225_; size_t v___x_2226_; 
lean_dec_ref_known(v___x_2224_, 1);
v___x_2225_ = ((size_t)1ULL);
v___x_2226_ = lean_usize_add(v_i_2208_, v___x_2225_);
v_i_2208_ = v___x_2226_;
v_b_2209_ = v___x_2217_;
goto _start;
}
else
{
return v___x_2224_;
}
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
v_a_2228_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2221_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2221_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
else
{
return v___x_2220_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13___boxed(lean_object* v_as_2236_, lean_object* v_sz_2237_, lean_object* v_i_2238_, lean_object* v_b_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
size_t v_sz_boxed_2243_; size_t v_i_boxed_2244_; lean_object* v_res_2245_; 
v_sz_boxed_2243_ = lean_unbox_usize(v_sz_2237_);
lean_dec(v_sz_2237_);
v_i_boxed_2244_ = lean_unbox_usize(v_i_2238_);
lean_dec(v_i_2238_);
v_res_2245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v_as_2236_, v_sz_boxed_2243_, v_i_boxed_2244_, v_b_2239_, v___y_2240_, v___y_2241_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec_ref(v_as_2236_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object* v_as_2246_, size_t v_i_2247_, size_t v_stop_2248_, lean_object* v_b_2249_){
_start:
{
uint8_t v___x_2250_; 
v___x_2250_ = lean_usize_dec_eq(v_i_2247_, v_stop_2248_);
if (v___x_2250_ == 0)
{
lean_object* v___x_2251_; lean_object* v_name_2252_; lean_object* v___x_2253_; size_t v___x_2254_; size_t v___x_2255_; 
v___x_2251_ = lean_array_uget_borrowed(v_as_2246_, v_i_2247_);
v_name_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_name_2252_);
v___x_2253_ = l_Lean_Compiler_LCNF_setDeclPublic(v_b_2249_, v_name_2252_);
v___x_2254_ = ((size_t)1ULL);
v___x_2255_ = lean_usize_add(v_i_2247_, v___x_2254_);
v_i_2247_ = v___x_2255_;
v_b_2249_ = v___x_2253_;
goto _start;
}
else
{
return v_b_2249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object* v_as_2257_, lean_object* v_i_2258_, lean_object* v_stop_2259_, lean_object* v_b_2260_){
_start:
{
size_t v_i_boxed_2261_; size_t v_stop_boxed_2262_; lean_object* v_res_2263_; 
v_i_boxed_2261_ = lean_unbox_usize(v_i_2258_);
lean_dec(v_i_2258_);
v_stop_boxed_2262_ = lean_unbox_usize(v_stop_2259_);
lean_dec(v_stop_2259_);
v_res_2263_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v_as_2257_, v_i_boxed_2261_, v_stop_boxed_2262_, v_b_2260_);
lean_dec_ref(v_as_2257_);
return v_res_2263_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0(uint8_t v___y_2264_, uint8_t v_suppressElabErrors_2265_, lean_object* v_x_2266_){
_start:
{
if (lean_obj_tag(v_x_2266_) == 1)
{
lean_object* v_pre_2267_; 
v_pre_2267_ = lean_ctor_get(v_x_2266_, 0);
switch(lean_obj_tag(v_pre_2267_))
{
case 1:
{
lean_object* v_pre_2268_; 
v_pre_2268_ = lean_ctor_get(v_pre_2267_, 0);
switch(lean_obj_tag(v_pre_2268_))
{
case 0:
{
lean_object* v_str_2269_; lean_object* v_str_2270_; lean_object* v___x_2271_; uint8_t v___x_2272_; 
v_str_2269_ = lean_ctor_get(v_x_2266_, 1);
v_str_2270_ = lean_ctor_get(v_pre_2267_, 1);
v___x_2271_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0));
v___x_2272_ = lean_string_dec_eq(v_str_2270_, v___x_2271_);
if (v___x_2272_ == 0)
{
lean_object* v___x_2273_; uint8_t v___x_2274_; 
v___x_2273_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1));
v___x_2274_ = lean_string_dec_eq(v_str_2270_, v___x_2273_);
if (v___x_2274_ == 0)
{
return v___y_2264_;
}
else
{
lean_object* v___x_2275_; uint8_t v___x_2276_; 
v___x_2275_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2));
v___x_2276_ = lean_string_dec_eq(v_str_2269_, v___x_2275_);
if (v___x_2276_ == 0)
{
return v___y_2264_;
}
else
{
return v_suppressElabErrors_2265_;
}
}
}
else
{
lean_object* v___x_2277_; uint8_t v___x_2278_; 
v___x_2277_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3));
v___x_2278_ = lean_string_dec_eq(v_str_2269_, v___x_2277_);
if (v___x_2278_ == 0)
{
return v___y_2264_;
}
else
{
return v_suppressElabErrors_2265_;
}
}
}
case 1:
{
lean_object* v_pre_2279_; 
v_pre_2279_ = lean_ctor_get(v_pre_2268_, 0);
if (lean_obj_tag(v_pre_2279_) == 0)
{
lean_object* v_str_2280_; lean_object* v_str_2281_; lean_object* v_str_2282_; lean_object* v___x_2283_; uint8_t v___x_2284_; 
v_str_2280_ = lean_ctor_get(v_x_2266_, 1);
v_str_2281_ = lean_ctor_get(v_pre_2267_, 1);
v_str_2282_ = lean_ctor_get(v_pre_2268_, 1);
v___x_2283_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4));
v___x_2284_ = lean_string_dec_eq(v_str_2282_, v___x_2283_);
if (v___x_2284_ == 0)
{
return v___y_2264_;
}
else
{
lean_object* v___x_2285_; uint8_t v___x_2286_; 
v___x_2285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5));
v___x_2286_ = lean_string_dec_eq(v_str_2281_, v___x_2285_);
if (v___x_2286_ == 0)
{
return v___y_2264_;
}
else
{
lean_object* v___x_2287_; uint8_t v___x_2288_; 
v___x_2287_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6));
v___x_2288_ = lean_string_dec_eq(v_str_2280_, v___x_2287_);
if (v___x_2288_ == 0)
{
return v___y_2264_;
}
else
{
return v_suppressElabErrors_2265_;
}
}
}
}
else
{
return v___y_2264_;
}
}
default: 
{
return v___y_2264_;
}
}
}
case 0:
{
lean_object* v_str_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; 
v_str_2289_ = lean_ctor_get(v_x_2266_, 1);
v___x_2290_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_2291_ = lean_string_dec_eq(v_str_2289_, v___x_2290_);
if (v___x_2291_ == 0)
{
return v___y_2264_;
}
else
{
return v_suppressElabErrors_2265_;
}
}
default: 
{
return v___y_2264_;
}
}
}
else
{
return v___y_2264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0___boxed(lean_object* v___y_2292_, lean_object* v_suppressElabErrors_2293_, lean_object* v_x_2294_){
_start:
{
uint8_t v___y_38960__boxed_2295_; uint8_t v_suppressElabErrors_boxed_2296_; uint8_t v_res_2297_; lean_object* v_r_2298_; 
v___y_38960__boxed_2295_ = lean_unbox(v___y_2292_);
v_suppressElabErrors_boxed_2296_ = lean_unbox(v_suppressElabErrors_2293_);
v_res_2297_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0(v___y_38960__boxed_2295_, v_suppressElabErrors_boxed_2296_, v_x_2294_);
lean_dec(v_x_2294_);
v_r_2298_ = lean_box(v_res_2297_);
return v_r_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(lean_object* v_ref_2299_, lean_object* v_msgData_2300_, uint8_t v_severity_2301_, uint8_t v_isSilent_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
uint8_t v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; uint8_t v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v___y_2343_; uint8_t v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; uint8_t v___y_2347_; uint8_t v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; lean_object* v___y_2368_; uint8_t v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; uint8_t v___y_2372_; uint8_t v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2379_; uint8_t v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; uint8_t v___y_2383_; lean_object* v___y_2384_; uint8_t v___y_2385_; uint8_t v___x_2390_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; uint8_t v___y_2395_; lean_object* v___y_2396_; uint8_t v___y_2397_; uint8_t v___y_2398_; uint8_t v___y_2400_; uint8_t v___x_2415_; 
v___x_2390_ = 2;
v___x_2415_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2301_, v___x_2390_);
if (v___x_2415_ == 0)
{
v___y_2400_ = v___x_2415_;
goto v___jp_2399_;
}
else
{
uint8_t v___x_2416_; 
lean_inc_ref(v_msgData_2300_);
v___x_2416_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2300_);
v___y_2400_ = v___x_2416_;
goto v___jp_2399_;
}
v___jp_2306_:
{
lean_object* v___x_2316_; lean_object* v_currNamespace_2317_; lean_object* v_openDecls_2318_; lean_object* v_env_2319_; lean_object* v_nextMacroScope_2320_; lean_object* v_ngen_2321_; lean_object* v_auxDeclNGen_2322_; lean_object* v_traceState_2323_; lean_object* v_cache_2324_; lean_object* v_messages_2325_; lean_object* v_infoState_2326_; lean_object* v_snapshotTasks_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2341_; 
v___x_2316_ = lean_st_ref_take(v___y_2315_);
v_currNamespace_2317_ = lean_ctor_get(v___y_2314_, 6);
v_openDecls_2318_ = lean_ctor_get(v___y_2314_, 7);
v_env_2319_ = lean_ctor_get(v___x_2316_, 0);
v_nextMacroScope_2320_ = lean_ctor_get(v___x_2316_, 1);
v_ngen_2321_ = lean_ctor_get(v___x_2316_, 2);
v_auxDeclNGen_2322_ = lean_ctor_get(v___x_2316_, 3);
v_traceState_2323_ = lean_ctor_get(v___x_2316_, 4);
v_cache_2324_ = lean_ctor_get(v___x_2316_, 5);
v_messages_2325_ = lean_ctor_get(v___x_2316_, 6);
v_infoState_2326_ = lean_ctor_get(v___x_2316_, 7);
v_snapshotTasks_2327_ = lean_ctor_get(v___x_2316_, 8);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2329_ = v___x_2316_;
v_isShared_2330_ = v_isSharedCheck_2341_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_snapshotTasks_2327_);
lean_inc(v_infoState_2326_);
lean_inc(v_messages_2325_);
lean_inc(v_cache_2324_);
lean_inc(v_traceState_2323_);
lean_inc(v_auxDeclNGen_2322_);
lean_inc(v_ngen_2321_);
lean_inc(v_nextMacroScope_2320_);
lean_inc(v_env_2319_);
lean_dec(v___x_2316_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2341_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2336_; 
lean_inc(v_openDecls_2318_);
lean_inc(v_currNamespace_2317_);
v___x_2331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2331_, 0, v_currNamespace_2317_);
lean_ctor_set(v___x_2331_, 1, v_openDecls_2318_);
v___x_2332_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
lean_ctor_set(v___x_2332_, 1, v___y_2308_);
lean_inc_ref(v___y_2313_);
lean_inc_ref(v___y_2310_);
v___x_2333_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2333_, 0, v___y_2310_);
lean_ctor_set(v___x_2333_, 1, v___y_2309_);
lean_ctor_set(v___x_2333_, 2, v___y_2312_);
lean_ctor_set(v___x_2333_, 3, v___y_2313_);
lean_ctor_set(v___x_2333_, 4, v___x_2332_);
lean_ctor_set_uint8(v___x_2333_, sizeof(void*)*5, v___y_2307_);
lean_ctor_set_uint8(v___x_2333_, sizeof(void*)*5 + 1, v___y_2311_);
lean_ctor_set_uint8(v___x_2333_, sizeof(void*)*5 + 2, v_isSilent_2302_);
v___x_2334_ = l_Lean_MessageLog_add(v___x_2333_, v_messages_2325_);
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 6, v___x_2334_);
v___x_2336_ = v___x_2329_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_env_2319_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_nextMacroScope_2320_);
lean_ctor_set(v_reuseFailAlloc_2340_, 2, v_ngen_2321_);
lean_ctor_set(v_reuseFailAlloc_2340_, 3, v_auxDeclNGen_2322_);
lean_ctor_set(v_reuseFailAlloc_2340_, 4, v_traceState_2323_);
lean_ctor_set(v_reuseFailAlloc_2340_, 5, v_cache_2324_);
lean_ctor_set(v_reuseFailAlloc_2340_, 6, v___x_2334_);
lean_ctor_set(v_reuseFailAlloc_2340_, 7, v_infoState_2326_);
lean_ctor_set(v_reuseFailAlloc_2340_, 8, v_snapshotTasks_2327_);
v___x_2336_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2337_ = lean_st_ref_set(v___y_2315_, v___x_2336_);
v___x_2338_ = lean_box(0);
v___x_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2338_);
return v___x_2339_;
}
}
}
v___jp_2342_:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2366_; 
v___x_2351_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2300_);
v___x_2352_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v___x_2351_, v___y_2303_, v___y_2304_);
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2355_ = v___x_2352_;
v_isShared_2356_ = v_isSharedCheck_2366_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2352_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2366_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
lean_inc_ref_n(v___y_2349_, 2);
v___x_2357_ = l_Lean_FileMap_toPosition(v___y_2349_, v___y_2345_);
lean_dec(v___y_2345_);
v___x_2358_ = l_Lean_FileMap_toPosition(v___y_2349_, v___y_2350_);
lean_dec(v___y_2350_);
v___x_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
v___x_2360_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1));
if (v___y_2348_ == 0)
{
lean_del_object(v___x_2355_);
lean_dec_ref(v___y_2343_);
v___y_2307_ = v___y_2344_;
v___y_2308_ = v_a_2353_;
v___y_2309_ = v___x_2357_;
v___y_2310_ = v___y_2346_;
v___y_2311_ = v___y_2347_;
v___y_2312_ = v___x_2359_;
v___y_2313_ = v___x_2360_;
v___y_2314_ = v___y_2303_;
v___y_2315_ = v___y_2304_;
goto v___jp_2306_;
}
else
{
uint8_t v___x_2361_; 
lean_inc(v_a_2353_);
v___x_2361_ = l_Lean_MessageData_hasTag(v___y_2343_, v_a_2353_);
if (v___x_2361_ == 0)
{
lean_object* v___x_2362_; lean_object* v___x_2364_; 
lean_dec_ref_known(v___x_2359_, 1);
lean_dec_ref(v___x_2357_);
lean_dec(v_a_2353_);
v___x_2362_ = lean_box(0);
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v___x_2362_);
v___x_2364_ = v___x_2355_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2362_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
else
{
lean_del_object(v___x_2355_);
v___y_2307_ = v___y_2344_;
v___y_2308_ = v_a_2353_;
v___y_2309_ = v___x_2357_;
v___y_2310_ = v___y_2346_;
v___y_2311_ = v___y_2347_;
v___y_2312_ = v___x_2359_;
v___y_2313_ = v___x_2360_;
v___y_2314_ = v___y_2303_;
v___y_2315_ = v___y_2304_;
goto v___jp_2306_;
}
}
}
}
v___jp_2367_:
{
lean_object* v___x_2376_; 
v___x_2376_ = l_Lean_Syntax_getTailPos_x3f(v___y_2371_, v___y_2369_);
lean_dec(v___y_2371_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_inc(v___y_2375_);
v___y_2343_ = v___y_2368_;
v___y_2344_ = v___y_2369_;
v___y_2345_ = v___y_2375_;
v___y_2346_ = v___y_2370_;
v___y_2347_ = v___y_2372_;
v___y_2348_ = v___y_2373_;
v___y_2349_ = v___y_2374_;
v___y_2350_ = v___y_2375_;
goto v___jp_2342_;
}
else
{
lean_object* v_val_2377_; 
v_val_2377_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_val_2377_);
lean_dec_ref_known(v___x_2376_, 1);
v___y_2343_ = v___y_2368_;
v___y_2344_ = v___y_2369_;
v___y_2345_ = v___y_2375_;
v___y_2346_ = v___y_2370_;
v___y_2347_ = v___y_2372_;
v___y_2348_ = v___y_2373_;
v___y_2349_ = v___y_2374_;
v___y_2350_ = v_val_2377_;
goto v___jp_2342_;
}
}
v___jp_2378_:
{
lean_object* v_ref_2386_; lean_object* v___x_2387_; 
v_ref_2386_ = l_Lean_replaceRef(v_ref_2299_, v___y_2382_);
v___x_2387_ = l_Lean_Syntax_getPos_x3f(v_ref_2386_, v___y_2380_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v___x_2388_; 
v___x_2388_ = lean_unsigned_to_nat(0u);
v___y_2368_ = v___y_2379_;
v___y_2369_ = v___y_2380_;
v___y_2370_ = v___y_2381_;
v___y_2371_ = v_ref_2386_;
v___y_2372_ = v___y_2385_;
v___y_2373_ = v___y_2383_;
v___y_2374_ = v___y_2384_;
v___y_2375_ = v___x_2388_;
goto v___jp_2367_;
}
else
{
lean_object* v_val_2389_; 
v_val_2389_ = lean_ctor_get(v___x_2387_, 0);
lean_inc(v_val_2389_);
lean_dec_ref_known(v___x_2387_, 1);
v___y_2368_ = v___y_2379_;
v___y_2369_ = v___y_2380_;
v___y_2370_ = v___y_2381_;
v___y_2371_ = v_ref_2386_;
v___y_2372_ = v___y_2385_;
v___y_2373_ = v___y_2383_;
v___y_2374_ = v___y_2384_;
v___y_2375_ = v_val_2389_;
goto v___jp_2367_;
}
}
v___jp_2391_:
{
if (v___y_2398_ == 0)
{
v___y_2379_ = v___y_2392_;
v___y_2380_ = v___y_2397_;
v___y_2381_ = v___y_2394_;
v___y_2382_ = v___y_2393_;
v___y_2383_ = v___y_2395_;
v___y_2384_ = v___y_2396_;
v___y_2385_ = v_severity_2301_;
goto v___jp_2378_;
}
else
{
v___y_2379_ = v___y_2392_;
v___y_2380_ = v___y_2397_;
v___y_2381_ = v___y_2394_;
v___y_2382_ = v___y_2393_;
v___y_2383_ = v___y_2395_;
v___y_2384_ = v___y_2396_;
v___y_2385_ = v___x_2390_;
goto v___jp_2378_;
}
}
v___jp_2399_:
{
if (v___y_2400_ == 0)
{
lean_object* v_fileName_2401_; lean_object* v_fileMap_2402_; lean_object* v_options_2403_; lean_object* v_ref_2404_; uint8_t v_suppressElabErrors_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___f_2408_; uint8_t v___x_2409_; uint8_t v___x_2410_; 
v_fileName_2401_ = lean_ctor_get(v___y_2303_, 0);
v_fileMap_2402_ = lean_ctor_get(v___y_2303_, 1);
v_options_2403_ = lean_ctor_get(v___y_2303_, 2);
v_ref_2404_ = lean_ctor_get(v___y_2303_, 5);
v_suppressElabErrors_2405_ = lean_ctor_get_uint8(v___y_2303_, sizeof(void*)*14 + 1);
v___x_2406_ = lean_box(v___y_2400_);
v___x_2407_ = lean_box(v_suppressElabErrors_2405_);
v___f_2408_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2408_, 0, v___x_2406_);
lean_closure_set(v___f_2408_, 1, v___x_2407_);
v___x_2409_ = 1;
v___x_2410_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2301_, v___x_2409_);
if (v___x_2410_ == 0)
{
v___y_2392_ = v___f_2408_;
v___y_2393_ = v_ref_2404_;
v___y_2394_ = v_fileName_2401_;
v___y_2395_ = v_suppressElabErrors_2405_;
v___y_2396_ = v_fileMap_2402_;
v___y_2397_ = v___y_2400_;
v___y_2398_ = v___x_2410_;
goto v___jp_2391_;
}
else
{
lean_object* v___x_2411_; uint8_t v___x_2412_; 
v___x_2411_ = l_Lean_warningAsError;
v___x_2412_ = l_Lean_Option_get___at___00main_spec__8(v_options_2403_, v___x_2411_);
v___y_2392_ = v___f_2408_;
v___y_2393_ = v_ref_2404_;
v___y_2394_ = v_fileName_2401_;
v___y_2395_ = v_suppressElabErrors_2405_;
v___y_2396_ = v_fileMap_2402_;
v___y_2397_ = v___y_2400_;
v___y_2398_ = v___x_2412_;
goto v___jp_2391_;
}
}
else
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
lean_dec_ref(v_msgData_2300_);
v___x_2413_ = lean_box(0);
v___x_2414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2413_);
return v___x_2414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___boxed(lean_object* v_ref_2417_, lean_object* v_msgData_2418_, lean_object* v_severity_2419_, lean_object* v_isSilent_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
uint8_t v_severity_boxed_2424_; uint8_t v_isSilent_boxed_2425_; lean_object* v_res_2426_; 
v_severity_boxed_2424_ = lean_unbox(v_severity_2419_);
v_isSilent_boxed_2425_ = lean_unbox(v_isSilent_2420_);
v_res_2426_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(v_ref_2417_, v_msgData_2418_, v_severity_boxed_2424_, v_isSilent_boxed_2425_, v___y_2421_, v___y_2422_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v_ref_2417_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(lean_object* v_msgData_2427_, uint8_t v_severity_2428_, uint8_t v_isSilent_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v_ref_2433_; lean_object* v___x_2434_; 
v_ref_2433_ = lean_ctor_get(v___y_2430_, 5);
v___x_2434_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(v_ref_2433_, v_msgData_2427_, v_severity_2428_, v_isSilent_2429_, v___y_2430_, v___y_2431_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30___boxed(lean_object* v_msgData_2435_, lean_object* v_severity_2436_, lean_object* v_isSilent_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
uint8_t v_severity_boxed_2441_; uint8_t v_isSilent_boxed_2442_; lean_object* v_res_2443_; 
v_severity_boxed_2441_ = lean_unbox(v_severity_2436_);
v_isSilent_boxed_2442_ = lean_unbox(v_isSilent_2437_);
v_res_2443_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2435_, v_severity_boxed_2441_, v_isSilent_boxed_2442_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14(lean_object* v_msgData_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
uint8_t v___x_2448_; uint8_t v___x_2449_; lean_object* v___x_2450_; 
v___x_2448_ = 2;
v___x_2449_ = 0;
v___x_2450_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2444_, v___x_2448_, v___x_2449_, v___y_2445_, v___y_2446_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14___boxed(lean_object* v_msgData_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l_Lean_logError___at___00main_spec__14(v_msgData_2451_, v___y_2452_, v___y_2453_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(lean_object* v_x2_2456_, lean_object* v_as_2457_, size_t v_i_2458_, size_t v_stop_2459_, lean_object* v_b_2460_){
_start:
{
uint8_t v___x_2461_; 
v___x_2461_ = lean_usize_dec_eq(v_i_2458_, v_stop_2459_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; lean_object* v___x_2463_; size_t v___x_2464_; size_t v___x_2465_; 
v___x_2462_ = lean_array_uget_borrowed(v_as_2457_, v_i_2458_);
lean_inc_ref(v_x2_2456_);
lean_inc(v___x_2462_);
v___x_2463_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2462_, v_x2_2456_, v_b_2460_);
v___x_2464_ = ((size_t)1ULL);
v___x_2465_ = lean_usize_add(v_i_2458_, v___x_2464_);
v_i_2458_ = v___x_2465_;
v_b_2460_ = v___x_2463_;
goto _start;
}
else
{
lean_dec_ref(v_x2_2456_);
return v_b_2460_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(lean_object* v_x2_2467_, lean_object* v_as_2468_, lean_object* v_i_2469_, lean_object* v_stop_2470_, lean_object* v_b_2471_){
_start:
{
size_t v_i_boxed_2472_; size_t v_stop_boxed_2473_; lean_object* v_res_2474_; 
v_i_boxed_2472_ = lean_unbox_usize(v_i_2469_);
lean_dec(v_i_2469_);
v_stop_boxed_2473_ = lean_unbox_usize(v_stop_2470_);
lean_dec(v_stop_2470_);
v_res_2474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v_x2_2467_, v_as_2468_, v_i_boxed_2472_, v_stop_boxed_2473_, v_b_2471_);
lean_dec_ref(v_as_2468_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object* v_as_2475_, size_t v_i_2476_, size_t v_stop_2477_, lean_object* v_b_2478_){
_start:
{
lean_object* v___y_2480_; uint8_t v___x_2484_; 
v___x_2484_ = lean_usize_dec_eq(v_i_2476_, v_stop_2477_);
if (v___x_2484_ == 0)
{
lean_object* v___x_2485_; lean_object* v_declNames_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; uint8_t v___x_2489_; 
v___x_2485_ = lean_array_uget_borrowed(v_as_2475_, v_i_2476_);
v_declNames_2486_ = lean_ctor_get(v___x_2485_, 0);
v___x_2487_ = lean_unsigned_to_nat(0u);
v___x_2488_ = lean_array_get_size(v_declNames_2486_);
v___x_2489_ = lean_nat_dec_lt(v___x_2487_, v___x_2488_);
if (v___x_2489_ == 0)
{
v___y_2480_ = v_b_2478_;
goto v___jp_2479_;
}
else
{
uint8_t v___x_2490_; 
v___x_2490_ = lean_nat_dec_le(v___x_2488_, v___x_2488_);
if (v___x_2490_ == 0)
{
if (v___x_2489_ == 0)
{
v___y_2480_ = v_b_2478_;
goto v___jp_2479_;
}
else
{
size_t v___x_2491_; size_t v___x_2492_; lean_object* v___x_2493_; 
v___x_2491_ = ((size_t)0ULL);
v___x_2492_ = lean_usize_of_nat(v___x_2488_);
lean_inc(v___x_2485_);
v___x_2493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2485_, v_declNames_2486_, v___x_2491_, v___x_2492_, v_b_2478_);
v___y_2480_ = v___x_2493_;
goto v___jp_2479_;
}
}
else
{
size_t v___x_2494_; size_t v___x_2495_; lean_object* v___x_2496_; 
v___x_2494_ = ((size_t)0ULL);
v___x_2495_ = lean_usize_of_nat(v___x_2488_);
lean_inc(v___x_2485_);
v___x_2496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2485_, v_declNames_2486_, v___x_2494_, v___x_2495_, v_b_2478_);
v___y_2480_ = v___x_2496_;
goto v___jp_2479_;
}
}
}
else
{
return v_b_2478_;
}
v___jp_2479_:
{
size_t v___x_2481_; size_t v___x_2482_; 
v___x_2481_ = ((size_t)1ULL);
v___x_2482_ = lean_usize_add(v_i_2476_, v___x_2481_);
v_i_2476_ = v___x_2482_;
v_b_2478_ = v___y_2480_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object* v_as_2497_, lean_object* v_i_2498_, lean_object* v_stop_2499_, lean_object* v_b_2500_){
_start:
{
size_t v_i_boxed_2501_; size_t v_stop_boxed_2502_; lean_object* v_res_2503_; 
v_i_boxed_2501_ = lean_unbox_usize(v_i_2498_);
lean_dec(v_i_2498_);
v_stop_boxed_2502_ = lean_unbox_usize(v_stop_2499_);
lean_dec(v_stop_2499_);
v_res_2503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v_as_2497_, v_i_boxed_2501_, v_stop_boxed_2502_, v_b_2500_);
lean_dec_ref(v_as_2497_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(lean_object* v_a_2504_, lean_object* v_as_2505_, size_t v_i_2506_, size_t v_stop_2507_, lean_object* v_b_2508_){
_start:
{
lean_object* v___y_2510_; uint8_t v___x_2514_; 
v___x_2514_ = lean_usize_dec_eq(v_i_2506_, v_stop_2507_);
if (v___x_2514_ == 0)
{
lean_object* v___x_2515_; lean_object* v_name_2516_; uint8_t v___x_2517_; 
v___x_2515_ = lean_array_uget_borrowed(v_as_2505_, v_i_2506_);
v_name_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_name_2516_);
lean_inc_ref(v_a_2504_);
v___x_2517_ = l_Lean_isExtern(v_a_2504_, v_name_2516_);
if (v___x_2517_ == 0)
{
v___y_2510_ = v_b_2508_;
goto v___jp_2509_;
}
else
{
lean_object* v___x_2518_; 
lean_inc(v___x_2515_);
v___x_2518_ = lean_array_push(v_b_2508_, v___x_2515_);
v___y_2510_ = v___x_2518_;
goto v___jp_2509_;
}
}
else
{
lean_dec_ref(v_a_2504_);
return v_b_2508_;
}
v___jp_2509_:
{
size_t v___x_2511_; size_t v___x_2512_; 
v___x_2511_ = ((size_t)1ULL);
v___x_2512_ = lean_usize_add(v_i_2506_, v___x_2511_);
v_i_2506_ = v___x_2512_;
v_b_2508_ = v___y_2510_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19___boxed(lean_object* v_a_2519_, lean_object* v_as_2520_, lean_object* v_i_2521_, lean_object* v_stop_2522_, lean_object* v_b_2523_){
_start:
{
size_t v_i_boxed_2524_; size_t v_stop_boxed_2525_; lean_object* v_res_2526_; 
v_i_boxed_2524_ = lean_unbox_usize(v_i_2521_);
lean_dec(v_i_2521_);
v_stop_boxed_2525_ = lean_unbox_usize(v_stop_2522_);
lean_dec(v_stop_2522_);
v_res_2526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_2519_, v_as_2520_, v_i_boxed_2524_, v_stop_boxed_2525_, v_b_2523_);
lean_dec_ref(v_as_2520_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(lean_object* v_as_2527_, size_t v_sz_2528_, size_t v_i_2529_, lean_object* v_b_2530_){
_start:
{
uint8_t v___x_2532_; 
v___x_2532_ = lean_usize_dec_lt(v_i_2529_, v_sz_2528_);
if (v___x_2532_ == 0)
{
lean_object* v___x_2533_; 
v___x_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2533_, 0, v_b_2530_);
return v___x_2533_;
}
else
{
uint8_t v___x_2534_; lean_object* v_a_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
lean_dec_ref(v_b_2530_);
v___x_2534_ = 0;
v_a_2535_ = lean_array_uget_borrowed(v_as_2527_, v_i_2529_);
lean_inc(v_a_2535_);
v___x_2536_ = l_Lean_Message_toString(v_a_2535_, v___x_2534_);
v___x_2537_ = l_IO_eprintln___at___00main_spec__6(v___x_2536_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v___x_2538_; size_t v___x_2539_; size_t v___x_2540_; 
lean_dec_ref_known(v___x_2537_, 1);
v___x_2538_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_2539_ = ((size_t)1ULL);
v___x_2540_ = lean_usize_add(v_i_2529_, v___x_2539_);
v_i_2529_ = v___x_2540_;
v_b_2530_ = v___x_2538_;
goto _start;
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
v_a_2542_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2537_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2537_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27___boxed(lean_object* v_as_2550_, lean_object* v_sz_2551_, lean_object* v_i_2552_, lean_object* v_b_2553_, lean_object* v___y_2554_){
_start:
{
size_t v_sz_boxed_2555_; size_t v_i_boxed_2556_; lean_object* v_res_2557_; 
v_sz_boxed_2555_ = lean_unbox_usize(v_sz_2551_);
lean_dec(v_sz_2551_);
v_i_boxed_2556_ = lean_unbox_usize(v_i_2552_);
lean_dec(v_i_2552_);
v_res_2557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2550_, v_sz_boxed_2555_, v_i_boxed_2556_, v_b_2553_);
lean_dec_ref(v_as_2550_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(lean_object* v_as_2558_, size_t v_sz_2559_, size_t v_i_2560_, lean_object* v_b_2561_){
_start:
{
uint8_t v___x_2563_; 
v___x_2563_ = lean_usize_dec_lt(v_i_2560_, v_sz_2559_);
if (v___x_2563_ == 0)
{
lean_object* v___x_2564_; 
v___x_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2564_, 0, v_b_2561_);
return v___x_2564_;
}
else
{
uint8_t v___x_2565_; lean_object* v_a_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
lean_dec_ref(v_b_2561_);
v___x_2565_ = 0;
v_a_2566_ = lean_array_uget_borrowed(v_as_2558_, v_i_2560_);
lean_inc(v_a_2566_);
v___x_2567_ = l_Lean_Message_toString(v_a_2566_, v___x_2565_);
v___x_2568_ = l_IO_eprintln___at___00main_spec__6(v___x_2567_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v___x_2569_; size_t v___x_2570_; size_t v___x_2571_; lean_object* v___x_2572_; 
lean_dec_ref_known(v___x_2568_, 1);
v___x_2569_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_2570_ = ((size_t)1ULL);
v___x_2571_ = lean_usize_add(v_i_2560_, v___x_2570_);
v___x_2572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2558_, v_sz_2559_, v___x_2571_, v___x_2569_);
return v___x_2572_;
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
v_a_2573_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2575_ = v___x_2568_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2568_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2573_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14___boxed(lean_object* v_as_2581_, lean_object* v_sz_2582_, lean_object* v_i_2583_, lean_object* v_b_2584_, lean_object* v___y_2585_){
_start:
{
size_t v_sz_boxed_2586_; size_t v_i_boxed_2587_; lean_object* v_res_2588_; 
v_sz_boxed_2586_ = lean_unbox_usize(v_sz_2582_);
lean_dec(v_sz_2582_);
v_i_boxed_2587_ = lean_unbox_usize(v_i_2583_);
lean_dec(v_i_2583_);
v_res_2588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_as_2581_, v_sz_boxed_2586_, v_i_boxed_2587_, v_b_2584_);
lean_dec_ref(v_as_2581_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(lean_object* v_init_2589_, lean_object* v_n_2590_, lean_object* v_b_2591_){
_start:
{
if (lean_obj_tag(v_n_2590_) == 0)
{
lean_object* v_cs_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; size_t v_sz_2596_; size_t v___x_2597_; lean_object* v___x_2598_; 
v_cs_2593_ = lean_ctor_get(v_n_2590_, 0);
v___x_2594_ = lean_box(0);
v___x_2595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
lean_ctor_set(v___x_2595_, 1, v_b_2591_);
v_sz_2596_ = lean_array_size(v_cs_2593_);
v___x_2597_ = ((size_t)0ULL);
v___x_2598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2589_, v_cs_2593_, v_sz_2596_, v___x_2597_, v___x_2595_);
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
else
{
lean_object* v_vs_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; size_t v_sz_2625_; size_t v___x_2626_; lean_object* v___x_2627_; 
v_vs_2622_ = lean_ctor_get(v_n_2590_, 0);
v___x_2623_ = lean_box(0);
v___x_2624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
lean_ctor_set(v___x_2624_, 1, v_b_2591_);
v_sz_2625_ = lean_array_size(v_vs_2622_);
v___x_2626_ = ((size_t)0ULL);
v___x_2627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_vs_2622_, v_sz_2625_, v___x_2626_, v___x_2624_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2642_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2630_ = v___x_2627_;
v_isShared_2631_ = v_isSharedCheck_2642_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2627_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2642_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v_fst_2632_; 
v_fst_2632_ = lean_ctor_get(v_a_2628_, 0);
if (lean_obj_tag(v_fst_2632_) == 0)
{
lean_object* v_snd_2633_; lean_object* v___x_2634_; lean_object* v___x_2636_; 
v_snd_2633_ = lean_ctor_get(v_a_2628_, 1);
lean_inc(v_snd_2633_);
lean_dec(v_a_2628_);
v___x_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2634_, 0, v_snd_2633_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 0, v___x_2634_);
v___x_2636_ = v___x_2630_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2634_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
else
{
lean_object* v_val_2638_; lean_object* v___x_2640_; 
lean_inc_ref(v_fst_2632_);
lean_dec(v_a_2628_);
v_val_2638_ = lean_ctor_get(v_fst_2632_, 0);
lean_inc(v_val_2638_);
lean_dec_ref_known(v_fst_2632_, 1);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 0, v_val_2638_);
v___x_2640_ = v___x_2630_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_val_2638_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
v_a_2643_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2627_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2627_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(lean_object* v_init_2651_, lean_object* v_as_2652_, size_t v_sz_2653_, size_t v_i_2654_, lean_object* v_b_2655_){
_start:
{
uint8_t v___x_2657_; 
v___x_2657_ = lean_usize_dec_lt(v_i_2654_, v_sz_2653_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2658_; 
v___x_2658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2658_, 0, v_b_2655_);
return v___x_2658_;
}
else
{
lean_object* v_snd_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2693_; 
v_snd_2659_ = lean_ctor_get(v_b_2655_, 1);
v_isSharedCheck_2693_ = !lean_is_exclusive(v_b_2655_);
if (v_isSharedCheck_2693_ == 0)
{
lean_object* v_unused_2694_; 
v_unused_2694_ = lean_ctor_get(v_b_2655_, 0);
lean_dec(v_unused_2694_);
v___x_2661_ = v_b_2655_;
v_isShared_2662_ = v_isSharedCheck_2693_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_snd_2659_);
lean_dec(v_b_2655_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2693_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v_a_2663_; lean_object* v___x_2664_; 
v_a_2663_ = lean_array_uget_borrowed(v_as_2652_, v_i_2654_);
lean_inc(v_snd_2659_);
v___x_2664_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2651_, v_a_2663_, v_snd_2659_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2684_; 
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2667_ = v___x_2664_;
v_isShared_2668_ = v_isSharedCheck_2684_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2664_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2684_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
if (lean_obj_tag(v_a_2665_) == 0)
{
lean_object* v___x_2669_; lean_object* v___x_2671_; 
v___x_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2669_, 0, v_a_2665_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v___x_2669_);
v___x_2671_ = v___x_2661_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2669_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v_snd_2659_);
v___x_2671_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
lean_object* v___x_2673_; 
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 0, v___x_2671_);
v___x_2673_ = v___x_2667_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2671_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2677_; lean_object* v___x_2679_; 
lean_del_object(v___x_2667_);
lean_dec(v_snd_2659_);
v_a_2676_ = lean_ctor_get(v_a_2665_, 0);
lean_inc(v_a_2676_);
lean_dec_ref_known(v_a_2665_, 1);
v___x_2677_ = lean_box(0);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 1, v_a_2676_);
lean_ctor_set(v___x_2661_, 0, v___x_2677_);
v___x_2679_ = v___x_2661_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2677_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v_a_2676_);
v___x_2679_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
size_t v___x_2680_; size_t v___x_2681_; 
v___x_2680_ = ((size_t)1ULL);
v___x_2681_ = lean_usize_add(v_i_2654_, v___x_2680_);
v_i_2654_ = v___x_2681_;
v_b_2655_ = v___x_2679_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
lean_del_object(v___x_2661_);
lean_dec(v_snd_2659_);
v_a_2685_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2664_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2664_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2685_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13___boxed(lean_object* v_init_2695_, lean_object* v_as_2696_, lean_object* v_sz_2697_, lean_object* v_i_2698_, lean_object* v_b_2699_, lean_object* v___y_2700_){
_start:
{
size_t v_sz_boxed_2701_; size_t v_i_boxed_2702_; lean_object* v_res_2703_; 
v_sz_boxed_2701_ = lean_unbox_usize(v_sz_2697_);
lean_dec(v_sz_2697_);
v_i_boxed_2702_ = lean_unbox_usize(v_i_2698_);
lean_dec(v_i_2698_);
v_res_2703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2695_, v_as_2696_, v_sz_boxed_2701_, v_i_boxed_2702_, v_b_2699_);
lean_dec_ref(v_as_2696_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10___boxed(lean_object* v_init_2704_, lean_object* v_n_2705_, lean_object* v_b_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2704_, v_n_2705_, v_b_2706_);
lean_dec_ref(v_n_2705_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(lean_object* v_as_2709_, size_t v_sz_2710_, size_t v_i_2711_, lean_object* v_b_2712_){
_start:
{
uint8_t v___x_2714_; 
v___x_2714_ = lean_usize_dec_lt(v_i_2711_, v_sz_2710_);
if (v___x_2714_ == 0)
{
lean_object* v___x_2715_; 
v___x_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2715_, 0, v_b_2712_);
return v___x_2715_;
}
else
{
uint8_t v___x_2716_; lean_object* v_a_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
lean_dec_ref(v_b_2712_);
v___x_2716_ = 0;
v_a_2717_ = lean_array_uget_borrowed(v_as_2709_, v_i_2711_);
lean_inc(v_a_2717_);
v___x_2718_ = l_Lean_Message_toString(v_a_2717_, v___x_2716_);
v___x_2719_ = l_IO_eprintln___at___00main_spec__6(v___x_2718_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_object* v___x_2720_; size_t v___x_2721_; size_t v___x_2722_; 
lean_dec_ref_known(v___x_2719_, 1);
v___x_2720_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_2721_ = ((size_t)1ULL);
v___x_2722_ = lean_usize_add(v_i_2711_, v___x_2721_);
v_i_2711_ = v___x_2722_;
v_b_2712_ = v___x_2720_;
goto _start;
}
else
{
lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
v_a_2724_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2726_ = v___x_2719_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___x_2719_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_a_2724_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16___boxed(lean_object* v_as_2732_, lean_object* v_sz_2733_, lean_object* v_i_2734_, lean_object* v_b_2735_, lean_object* v___y_2736_){
_start:
{
size_t v_sz_boxed_2737_; size_t v_i_boxed_2738_; lean_object* v_res_2739_; 
v_sz_boxed_2737_ = lean_unbox_usize(v_sz_2733_);
lean_dec(v_sz_2733_);
v_i_boxed_2738_ = lean_unbox_usize(v_i_2734_);
lean_dec(v_i_2734_);
v_res_2739_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2732_, v_sz_boxed_2737_, v_i_boxed_2738_, v_b_2735_);
lean_dec_ref(v_as_2732_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(lean_object* v_as_2740_, size_t v_sz_2741_, size_t v_i_2742_, lean_object* v_b_2743_){
_start:
{
uint8_t v___x_2745_; 
v___x_2745_ = lean_usize_dec_lt(v_i_2742_, v_sz_2741_);
if (v___x_2745_ == 0)
{
lean_object* v___x_2746_; 
v___x_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2746_, 0, v_b_2743_);
return v___x_2746_;
}
else
{
uint8_t v___x_2747_; lean_object* v_a_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
lean_dec_ref(v_b_2743_);
v___x_2747_ = 0;
v_a_2748_ = lean_array_uget_borrowed(v_as_2740_, v_i_2742_);
lean_inc(v_a_2748_);
v___x_2749_ = l_Lean_Message_toString(v_a_2748_, v___x_2747_);
v___x_2750_ = l_IO_eprintln___at___00main_spec__6(v___x_2749_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v___x_2751_; size_t v___x_2752_; size_t v___x_2753_; lean_object* v___x_2754_; 
lean_dec_ref_known(v___x_2750_, 1);
v___x_2751_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_2752_ = ((size_t)1ULL);
v___x_2753_ = lean_usize_add(v_i_2742_, v___x_2752_);
v___x_2754_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2740_, v_sz_2741_, v___x_2753_, v___x_2751_);
return v___x_2754_;
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
v_a_2755_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2750_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2750_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11___boxed(lean_object* v_as_2763_, lean_object* v_sz_2764_, lean_object* v_i_2765_, lean_object* v_b_2766_, lean_object* v___y_2767_){
_start:
{
size_t v_sz_boxed_2768_; size_t v_i_boxed_2769_; lean_object* v_res_2770_; 
v_sz_boxed_2768_ = lean_unbox_usize(v_sz_2764_);
lean_dec(v_sz_2764_);
v_i_boxed_2769_ = lean_unbox_usize(v_i_2765_);
lean_dec(v_i_2765_);
v_res_2770_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_as_2763_, v_sz_boxed_2768_, v_i_boxed_2769_, v_b_2766_);
lean_dec_ref(v_as_2763_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7(lean_object* v_t_2771_, lean_object* v_init_2772_){
_start:
{
lean_object* v_root_2774_; lean_object* v_tail_2775_; lean_object* v___x_2776_; 
v_root_2774_ = lean_ctor_get(v_t_2771_, 0);
v_tail_2775_ = lean_ctor_get(v_t_2771_, 1);
v___x_2776_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2772_, v_root_2774_, v_init_2772_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2813_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2779_ = v___x_2776_;
v_isShared_2780_ = v_isSharedCheck_2813_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2776_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2813_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
if (lean_obj_tag(v_a_2777_) == 0)
{
lean_object* v_a_2781_; lean_object* v___x_2783_; 
v_a_2781_ = lean_ctor_get(v_a_2777_, 0);
lean_inc(v_a_2781_);
lean_dec_ref_known(v_a_2777_, 1);
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 0, v_a_2781_);
v___x_2783_ = v___x_2779_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2781_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; size_t v_sz_2788_; size_t v___x_2789_; lean_object* v___x_2790_; 
lean_del_object(v___x_2779_);
v_a_2785_ = lean_ctor_get(v_a_2777_, 0);
lean_inc(v_a_2785_);
lean_dec_ref_known(v_a_2777_, 1);
v___x_2786_ = lean_box(0);
v___x_2787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2786_);
lean_ctor_set(v___x_2787_, 1, v_a_2785_);
v_sz_2788_ = lean_array_size(v_tail_2775_);
v___x_2789_ = ((size_t)0ULL);
v___x_2790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_tail_2775_, v_sz_2788_, v___x_2789_, v___x_2787_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2804_; 
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2793_ = v___x_2790_;
v_isShared_2794_ = v_isSharedCheck_2804_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2790_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2804_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v_fst_2795_; 
v_fst_2795_ = lean_ctor_get(v_a_2791_, 0);
if (lean_obj_tag(v_fst_2795_) == 0)
{
lean_object* v_snd_2796_; lean_object* v___x_2798_; 
v_snd_2796_ = lean_ctor_get(v_a_2791_, 1);
lean_inc(v_snd_2796_);
lean_dec(v_a_2791_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 0, v_snd_2796_);
v___x_2798_ = v___x_2793_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_snd_2796_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
else
{
lean_object* v_val_2800_; lean_object* v___x_2802_; 
lean_inc_ref(v_fst_2795_);
lean_dec(v_a_2791_);
v_val_2800_ = lean_ctor_get(v_fst_2795_, 0);
lean_inc(v_val_2800_);
lean_dec_ref_known(v_fst_2795_, 1);
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 0, v_val_2800_);
v___x_2802_ = v___x_2793_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_val_2800_);
v___x_2802_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
return v___x_2802_;
}
}
}
}
else
{
lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2812_; 
v_a_2805_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2807_ = v___x_2790_;
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_dec(v___x_2790_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2810_; 
if (v_isShared_2808_ == 0)
{
v___x_2810_ = v___x_2807_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_a_2805_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
}
}
}
else
{
lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2821_; 
v_a_2814_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2816_ = v___x_2776_;
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_dec(v___x_2776_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2819_; 
if (v_isShared_2817_ == 0)
{
v___x_2819_ = v___x_2816_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_a_2814_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7___boxed(lean_object* v_t_2822_, lean_object* v_init_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_t_2822_, v_init_2823_);
lean_dec_ref(v_t_2822_);
return v_res_2825_;
}
}
static lean_object* _init_l_main___closed__3(void){
_start:
{
lean_object* v___x_2829_; 
v___x_2829_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_box(0), lean_box(0), lean_box(0));
return v___x_2829_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2830_ = l_Lean_instInhabitedClassState_default;
v___x_2831_ = lean_box(0);
v___x_2832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2831_);
lean_ctor_set(v___x_2832_, 1, v___x_2830_);
return v___x_2832_;
}
}
static lean_object* _init_l_main___closed__5(void){
_start:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2833_ = l_Lean_Meta_Match_Extension_instInhabitedState;
v___x_2834_ = lean_box(0);
v___x_2835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2834_);
lean_ctor_set(v___x_2835_, 1, v___x_2833_);
return v___x_2835_;
}
}
static lean_object* _init_l_main___closed__6(void){
_start:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2836_ = ((lean_object*)(l_main___closed__2));
v___x_2837_ = ((lean_object*)(l_main___closed__1));
v___x_2838_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_2837_, v___x_2836_);
return v___x_2838_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2839_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2840_ = lean_box(0);
v___x_2841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2840_);
lean_ctor_set(v___x_2841_, 1, v___x_2839_);
return v___x_2841_;
}
}
static lean_object* _init_l_main___closed__8(void){
_start:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2842_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_2843_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2842_);
return v___x_2843_;
}
}
static lean_object* _init_l_main___closed__9(void){
_start:
{
lean_object* v___x_2844_; 
v___x_2844_ = l_Array_instInhabited(lean_box(0));
return v___x_2844_;
}
}
static lean_object* _init_l_main___closed__14(void){
_start:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2852_ = l_Lean_Options_empty;
v___x_2853_ = l_Lean_Core_getMaxHeartbeats(v___x_2852_);
return v___x_2853_;
}
}
static lean_object* _init_l_main___closed__19(void){
_start:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2858_ = ((lean_object*)(l_main___closed__18));
v___x_2859_ = lean_unsigned_to_nat(27u);
v___x_2860_ = lean_unsigned_to_nat(143u);
v___x_2861_ = ((lean_object*)(l_main___closed__17));
v___x_2862_ = ((lean_object*)(l_main___closed__16));
v___x_2863_ = l_mkPanicMessageWithDecl(v___x_2862_, v___x_2861_, v___x_2860_, v___x_2859_, v___x_2858_);
return v___x_2863_;
}
}
static lean_object* _init_l_main___closed__21(void){
_start:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2865_ = ((lean_object*)(l_main___closed__18));
v___x_2866_ = lean_unsigned_to_nat(51u);
v___x_2867_ = lean_unsigned_to_nat(116u);
v___x_2868_ = ((lean_object*)(l_main___closed__17));
v___x_2869_ = ((lean_object*)(l_main___closed__16));
v___x_2870_ = l_mkPanicMessageWithDecl(v___x_2869_, v___x_2868_, v___x_2867_, v___x_2866_, v___x_2865_);
return v___x_2870_;
}
}
static lean_object* _init_l_main___closed__22(void){
_start:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2871_ = lean_unsigned_to_nat(1u);
v___x_2872_ = l_Lean_firstFrontendMacroScope;
v___x_2873_ = lean_nat_add(v___x_2872_, v___x_2871_);
return v___x_2873_;
}
}
static lean_object* _init_l_main___closed__26(void){
_start:
{
lean_object* v___x_2880_; uint64_t v___x_2881_; lean_object* v___x_2882_; 
v___x_2880_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2881_ = 0ULL;
v___x_2882_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2882_, 0, v___x_2880_);
lean_ctor_set_uint64(v___x_2882_, sizeof(void*)*1, v___x_2881_);
return v___x_2882_;
}
}
static lean_object* _init_l_main___closed__27(void){
_start:
{
lean_object* v___x_2883_; 
v___x_2883_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2883_;
}
}
static lean_object* _init_l_main___closed__28(void){
_start:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2884_ = lean_obj_once(&l_main___closed__27, &l_main___closed__27_once, _init_l_main___closed__27);
v___x_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2884_);
return v___x_2885_;
}
}
static lean_object* _init_l_main___closed__29(void){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_2887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
lean_ctor_set(v___x_2887_, 1, v___x_2886_);
return v___x_2887_;
}
}
static lean_object* _init_l_main___closed__30(void){
_start:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2888_ = l_Lean_NameSet_empty;
v___x_2889_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2890_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2889_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
lean_ctor_set(v___x_2890_, 2, v___x_2888_);
return v___x_2890_;
}
}
static lean_object* _init_l_main___closed__31(void){
_start:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; uint8_t v___x_2893_; lean_object* v___x_2894_; 
v___x_2891_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2892_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_2893_ = 1;
v___x_2894_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2894_, 0, v___x_2892_);
lean_ctor_set(v___x_2894_, 1, v___x_2892_);
lean_ctor_set(v___x_2894_, 2, v___x_2891_);
lean_ctor_set_uint8(v___x_2894_, sizeof(void*)*3, v___x_2893_);
return v___x_2894_;
}
}
static uint8_t _init_l_main___closed__36(void){
_start:
{
uint8_t v___x_2901_; uint8_t v___x_2902_; 
v___x_2901_ = 2;
v___x_2902_ = l_Lean_instOrdOLeanLevel_ord(v___x_2901_, v___x_2901_);
return v___x_2902_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_2903_; lean_object* v___x_2904_; 
v___x_2903_ = 1;
v___x_2904_ = lean_box_uint32(v___x_2903_);
return v___x_2904_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_2905_; lean_object* v___x_2906_; 
v___x_2905_ = 0;
v___x_2906_ = lean_box_uint32(v___x_2905_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_2907_){
_start:
{
if (lean_obj_tag(v_args_2907_) == 1)
{
lean_object* v_tail_2932_; 
v_tail_2932_ = lean_ctor_get(v_args_2907_, 1);
lean_inc(v_tail_2932_);
if (lean_obj_tag(v_tail_2932_) == 1)
{
lean_object* v_tail_2933_; 
v_tail_2933_ = lean_ctor_get(v_tail_2932_, 1);
lean_inc(v_tail_2933_);
if (lean_obj_tag(v_tail_2933_) == 1)
{
lean_object* v_head_2934_; lean_object* v_head_2935_; lean_object* v_head_2936_; lean_object* v_tail_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_3561_; 
v_head_2934_ = lean_ctor_get(v_args_2907_, 0);
lean_inc(v_head_2934_);
lean_dec_ref_known(v_args_2907_, 2);
v_head_2935_ = lean_ctor_get(v_tail_2932_, 0);
lean_inc(v_head_2935_);
lean_dec_ref_known(v_tail_2932_, 2);
v_head_2936_ = lean_ctor_get(v_tail_2933_, 0);
v_tail_2937_ = lean_ctor_get(v_tail_2933_, 1);
v_isSharedCheck_3561_ = !lean_is_exclusive(v_tail_2933_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_2939_ = v_tail_2933_;
v_isShared_2940_ = v_isSharedCheck_3561_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_tail_2937_);
lean_inc(v_head_2936_);
lean_dec(v_tail_2933_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_3561_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2941_; 
v___x_2941_ = l_Lean_ModuleSetup_load(v_head_2934_);
lean_dec(v_head_2934_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v_a_2942_; lean_object* v_name_2943_; lean_object* v_options_2944_; uint8_t v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2949_; 
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_a_2942_);
lean_dec_ref_known(v___x_2941_, 1);
v_name_2943_ = lean_ctor_get(v_a_2942_, 0);
lean_inc(v_name_2943_);
v_options_2944_ = lean_ctor_get(v_a_2942_, 6);
lean_inc(v_options_2944_);
lean_dec(v_a_2942_);
v___x_2945_ = 0;
v___x_2946_ = l_Lean_LeanOptions_toOptions(v_options_2944_);
v___x_2947_ = lean_box(v___x_2945_);
if (v_isShared_2940_ == 0)
{
lean_ctor_set_tag(v___x_2939_, 0);
lean_ctor_set(v___x_2939_, 1, v___x_2946_);
lean_ctor_set(v___x_2939_, 0, v___x_2947_);
v___x_2949_ = v___x_2939_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v___x_2947_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v___x_2946_);
v___x_2949_ = v_reuseFailAlloc_3552_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
lean_object* v___x_2950_; 
v___x_2950_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_tail_2937_, v___x_2949_);
lean_dec(v_tail_2937_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v_a_2951_; lean_object* v___x_2952_; 
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
lean_inc(v_a_2951_);
lean_dec_ref_known(v___x_2950_, 1);
v___x_2952_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_a_2953_);
lean_dec_ref_known(v___x_2952_, 1);
v___x_2954_ = lean_box(0);
v___x_2955_ = l_Lean_initSearchPath(v_a_2953_, v___x_2954_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_fst_2956_; lean_object* v_snd_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_3527_; 
lean_dec_ref_known(v___x_2955_, 1);
v_fst_2956_ = lean_ctor_get(v_a_2951_, 0);
v_snd_2957_ = lean_ctor_get(v_a_2951_, 1);
v_isSharedCheck_3527_ = !lean_is_exclusive(v_a_2951_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_2959_ = v_a_2951_;
v_isShared_2960_ = v_isSharedCheck_3527_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_snd_2957_);
lean_inc(v_fst_2956_);
lean_dec(v_a_2951_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_3527_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; uint8_t v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; uint8_t v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_3108_; uint8_t v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v_nextMacroScope_3127_; lean_object* v_ngen_3128_; lean_object* v_auxDeclNGen_3129_; lean_object* v_traceState_3130_; lean_object* v_messages_3131_; lean_object* v_infoState_3132_; lean_object* v_snapshotTasks_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; uint8_t v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; uint8_t v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3222_; uint8_t v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; uint8_t v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; uint8_t v___y_3245_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___y_3269_; lean_object* v___y_3270_; uint8_t v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3375_; lean_object* v___y_3376_; uint8_t v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3397_; lean_object* v___y_3398_; uint8_t v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; uint8_t v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___x_3428_; lean_object* v___x_3429_; uint8_t v___x_3430_; uint8_t v___y_3432_; uint8_t v___x_3526_; 
v___x_2961_ = lean_obj_once(&l_main___closed__3, &l_main___closed__3_once, _init_l_main___closed__3);
v___x_2962_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2963_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_2964_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2965_ = lean_obj_once(&l_main___closed__8, &l_main___closed__8_once, _init_l_main___closed__8);
v___x_2966_ = lean_obj_once(&l_main___closed__9, &l_main___closed__9_once, _init_l_main___closed__9);
v___x_2967_ = lean_box(1);
v___x_2968_ = ((lean_object*)(l_main___closed__10));
v___x_2969_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_2970_ = 1;
v___x_2971_ = l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(v_snd_2957_, v___x_2969_, v___x_2970_);
v___x_2972_ = l_Lean_maxHeartbeats;
v___x_2973_ = lean_unsigned_to_nat(0u);
v___x_2974_ = l_Lean_Option_set___at___00main_spec__3(v___x_2971_, v___x_2972_, v___x_2973_);
v___x_3265_ = ((lean_object*)(l_main___closed__20));
lean_inc(v_name_2943_);
v___x_3266_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3266_, 0, v_name_2943_);
lean_ctor_set_uint8(v___x_3266_, sizeof(void*)*1, v___x_2970_);
lean_ctor_set_uint8(v___x_3266_, sizeof(void*)*1 + 1, v___x_2970_);
lean_ctor_set_uint8(v___x_3266_, sizeof(void*)*1 + 2, v___x_2970_);
v___x_3267_ = lean_unsigned_to_nat(1u);
v___x_3428_ = lean_mk_empty_array_with_capacity(v___x_3267_);
v___x_3429_ = lean_array_push(v___x_3428_, v___x_3266_);
v___x_3430_ = 2;
v___x_3526_ = lean_uint8_once(&l_main___closed__36, &l_main___closed__36_once, _init_l_main___closed__36);
if (v___x_3526_ == 0)
{
v___y_3432_ = v___x_2970_;
goto v___jp_3431_;
}
else
{
v___y_3432_ = v___x_2945_;
goto v___jp_3431_;
}
v___jp_2975_:
{
lean_object* v___x_2995_; lean_object* v_messages_2996_; lean_object* v_env_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3099_; 
v___x_2995_ = lean_st_ref_get(v___y_2990_);
lean_dec(v___y_2990_);
v_messages_2996_ = lean_ctor_get(v___x_2995_, 6);
v_env_2997_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3099_ == 0)
{
lean_object* v_unused_3100_; lean_object* v_unused_3101_; lean_object* v_unused_3102_; lean_object* v_unused_3103_; lean_object* v_unused_3104_; lean_object* v_unused_3105_; lean_object* v_unused_3106_; 
v_unused_3100_ = lean_ctor_get(v___x_2995_, 8);
lean_dec(v_unused_3100_);
v_unused_3101_ = lean_ctor_get(v___x_2995_, 7);
lean_dec(v_unused_3101_);
v_unused_3102_ = lean_ctor_get(v___x_2995_, 5);
lean_dec(v_unused_3102_);
v_unused_3103_ = lean_ctor_get(v___x_2995_, 4);
lean_dec(v_unused_3103_);
v_unused_3104_ = lean_ctor_get(v___x_2995_, 3);
lean_dec(v_unused_3104_);
v_unused_3105_ = lean_ctor_get(v___x_2995_, 2);
lean_dec(v_unused_3105_);
v_unused_3106_ = lean_ctor_get(v___x_2995_, 1);
lean_dec(v_unused_3106_);
v___x_2999_ = v___x_2995_;
v_isShared_3000_ = v_isSharedCheck_3099_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_messages_2996_);
lean_inc(v_env_2997_);
lean_dec(v___x_2995_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3099_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v_unreported_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v_unreported_3001_ = lean_ctor_get(v_messages_2996_, 1);
v___x_3002_ = lean_box(0);
v___x_3003_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_unreported_3001_, v___x_3002_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3089_; 
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3089_ == 0)
{
lean_object* v_unused_3090_; 
v_unused_3090_ = lean_ctor_get(v___x_3003_, 0);
lean_dec(v_unused_3090_);
v___x_3005_ = v___x_3003_;
v_isShared_3006_ = v_isSharedCheck_3089_;
goto v_resetjp_3004_;
}
else
{
lean_dec(v___x_3003_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3089_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
uint8_t v___x_3007_; 
v___x_3007_ = l_Lean_MessageLog_hasErrors(v_messages_2996_);
lean_dec_ref(v_messages_2996_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; 
lean_del_object(v___x_3005_);
lean_inc_ref(v_env_2997_);
v___x_3008_ = l___private_LeanIR_0__mkIRData(v_env_2997_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_a_3009_);
lean_dec_ref_known(v___x_3008_, 1);
v___x_3010_ = l_Lean_Environment_mainModule(v_env_2997_);
v___x_3011_ = ((lean_object*)(l_main___closed__12));
v___x_3012_ = l_Lean_Name_append(v___x_3010_, v___x_3011_);
v___x_3013_ = l_Lean_saveModuleData(v_head_2935_, v___x_3012_, v_a_3009_);
lean_dec(v_a_3009_);
lean_dec(v___x_3012_);
if (lean_obj_tag(v___x_3013_) == 0)
{
uint8_t v___x_3014_; lean_object* v___x_3015_; 
lean_dec_ref_known(v___x_3013_, 1);
v___x_3014_ = 1;
v___x_3015_ = lean_io_prim_handle_mk(v_head_2936_, v___x_3014_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3021_; 
lean_dec(v_head_2936_);
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3016_);
lean_dec_ref_known(v___x_3015_, 1);
v___x_3017_ = ((lean_object*)(l_main___closed__13));
v___x_3018_ = l_Lean_Options_empty;
v___x_3019_ = lean_obj_once(&l_main___closed__14, &l_main___closed__14_once, _init_l_main___closed__14);
lean_inc_ref(v___y_2986_);
lean_inc_ref(v___y_2987_);
lean_inc_ref(v___y_2991_);
lean_inc_ref(v___y_2988_);
lean_inc_ref(v___y_2994_);
lean_inc_ref(v___y_2993_);
lean_inc(v___y_2989_);
lean_inc_ref(v_env_2997_);
if (v_isShared_3000_ == 0)
{
lean_ctor_set(v___x_2999_, 8, v___y_2986_);
lean_ctor_set(v___x_2999_, 7, v___y_2987_);
lean_ctor_set(v___x_2999_, 6, v___y_2991_);
lean_ctor_set(v___x_2999_, 5, v___y_2988_);
lean_ctor_set(v___x_2999_, 4, v___y_2994_);
lean_ctor_set(v___x_2999_, 3, v___y_2992_);
lean_ctor_set(v___x_2999_, 2, v___y_2993_);
lean_ctor_set(v___x_2999_, 1, v___y_2989_);
v___x_3021_ = v___x_2999_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_env_2997_);
lean_ctor_set(v_reuseFailAlloc_3046_, 1, v___y_2989_);
lean_ctor_set(v_reuseFailAlloc_3046_, 2, v___y_2993_);
lean_ctor_set(v_reuseFailAlloc_3046_, 3, v___y_2992_);
lean_ctor_set(v_reuseFailAlloc_3046_, 4, v___y_2994_);
lean_ctor_set(v_reuseFailAlloc_3046_, 5, v___y_2988_);
lean_ctor_set(v_reuseFailAlloc_3046_, 6, v___y_2991_);
lean_ctor_set(v_reuseFailAlloc_3046_, 7, v___y_2987_);
lean_ctor_set(v_reuseFailAlloc_3046_, 8, v___y_2986_);
v___x_3021_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___f_3025_; lean_object* v___x_3026_; 
v___x_3022_ = lean_box(v___x_2970_);
v___x_3023_ = lean_box(v___x_2945_);
v___x_3024_ = lean_box(v___y_2976_);
lean_inc(v___y_2977_);
lean_inc(v___y_2983_);
lean_inc(v___y_2982_);
lean_inc_ref(v___y_2979_);
lean_inc_ref(v___y_2980_);
lean_inc(v___y_2984_);
v___f_3025_ = lean_alloc_closure((void*)(l_main___lam__1___boxed), 19, 18);
lean_closure_set(v___f_3025_, 0, v___x_3021_);
lean_closure_set(v___f_3025_, 1, v___y_2984_);
lean_closure_set(v___f_3025_, 2, v___x_3018_);
lean_closure_set(v___f_3025_, 3, v_name_2943_);
lean_closure_set(v___f_3025_, 4, v_a_3016_);
lean_closure_set(v___f_3025_, 5, v___x_3022_);
lean_closure_set(v___f_3025_, 6, v___y_2980_);
lean_closure_set(v___f_3025_, 7, v_head_2935_);
lean_closure_set(v___f_3025_, 8, v___y_2979_);
lean_closure_set(v___f_3025_, 9, v___x_2973_);
lean_closure_set(v___f_3025_, 10, v___y_2982_);
lean_closure_set(v___f_3025_, 11, v___y_2978_);
lean_closure_set(v___f_3025_, 12, v___y_2981_);
lean_closure_set(v___f_3025_, 13, v___x_3019_);
lean_closure_set(v___f_3025_, 14, v___y_2983_);
lean_closure_set(v___f_3025_, 15, v___y_2977_);
lean_closure_set(v___f_3025_, 16, v___x_3023_);
lean_closure_set(v___f_3025_, 17, v___x_3024_);
v___x_3026_ = l_Lean_profileitIOUnsafe___redArg(v___x_3017_, v___x_2974_, v___f_3025_, v___y_2985_);
lean_dec_ref(v___x_2974_);
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_object* v___x_3027_; uint8_t v___x_3028_; 
lean_dec_ref_known(v___x_3026_, 1);
v___x_3027_ = lean_display_cumulative_profiling_times();
v___x_3028_ = lean_unbox(v_fst_2956_);
lean_dec(v_fst_2956_);
if (v___x_3028_ == 0)
{
lean_dec_ref(v_env_2997_);
goto v___jp_2929_;
}
else
{
lean_object* v___x_3029_; 
v___x_3029_ = l_Lean_Environment_displayStats(v_env_2997_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_dec_ref_known(v___x_3029_, 1);
goto v___jp_2929_;
}
else
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3037_; 
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3032_ = v___x_3029_;
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_3029_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3035_; 
if (v_isShared_3033_ == 0)
{
v___x_3035_ = v___x_3032_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3030_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
}
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_dec_ref(v_env_2997_);
lean_dec(v_fst_2956_);
v_a_3038_ = lean_ctor_get(v___x_3026_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_3026_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3026_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
}
else
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
lean_dec_ref_known(v___x_3015_, 1);
lean_del_object(v___x_2999_);
lean_dec_ref(v_env_2997_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2985_);
lean_dec(v___y_2981_);
lean_dec(v___y_2978_);
lean_dec_ref(v___x_2974_);
lean_dec(v_fst_2956_);
lean_dec(v_name_2943_);
lean_dec(v_head_2935_);
v___x_3047_ = ((lean_object*)(l_main___closed__15));
v___x_3048_ = lean_string_append(v___x_3047_, v_head_2936_);
lean_dec(v_head_2936_);
v___x_3049_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__1));
v___x_3050_ = lean_string_append(v___x_3048_, v___x_3049_);
v___x_3051_ = l_IO_eprintln___at___00main_spec__6(v___x_3050_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3059_; 
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3059_ == 0)
{
lean_object* v_unused_3060_; 
v_unused_3060_ = lean_ctor_get(v___x_3051_, 0);
lean_dec(v_unused_3060_);
v___x_3053_ = v___x_3051_;
v_isShared_3054_ = v_isSharedCheck_3059_;
goto v_resetjp_3052_;
}
else
{
lean_dec(v___x_3051_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3059_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3055_; lean_object* v___x_3057_; 
v___x_3055_ = l_main___boxed__const__1;
if (v_isShared_3054_ == 0)
{
lean_ctor_set(v___x_3053_, 0, v___x_3055_);
v___x_3057_ = v___x_3053_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v___x_3055_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
v_a_3061_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3051_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3051_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
}
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
lean_del_object(v___x_2999_);
lean_dec_ref(v_env_2997_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2985_);
lean_dec(v___y_2981_);
lean_dec(v___y_2978_);
lean_dec_ref(v___x_2974_);
lean_dec(v_fst_2956_);
lean_dec(v_name_2943_);
lean_dec(v_head_2936_);
lean_dec(v_head_2935_);
v_a_3069_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_3013_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3013_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3069_);
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
lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3084_; 
lean_del_object(v___x_2999_);
lean_dec_ref(v_env_2997_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2985_);
lean_dec(v___y_2981_);
lean_dec(v___y_2978_);
lean_dec_ref(v___x_2974_);
lean_dec(v_fst_2956_);
lean_dec(v_name_2943_);
lean_dec(v_head_2936_);
lean_dec(v_head_2935_);
v_a_3077_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___x_3008_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_3008_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3077_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
else
{
lean_object* v___x_3085_; lean_object* v___x_3087_; 
lean_del_object(v___x_2999_);
lean_dec_ref(v_env_2997_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2985_);
lean_dec(v___y_2981_);
lean_dec(v___y_2978_);
lean_dec_ref(v___x_2974_);
lean_dec(v_fst_2956_);
lean_dec(v_name_2943_);
lean_dec(v_head_2936_);
lean_dec(v_head_2935_);
v___x_3085_ = l_main___boxed__const__1;
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 0, v___x_3085_);
v___x_3087_ = v___x_3005_;
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
}
else
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
lean_del_object(v___x_2999_);
lean_dec_ref(v_env_2997_);
lean_dec_ref(v_messages_2996_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2985_);
lean_dec(v___y_2981_);
lean_dec(v___y_2978_);
lean_dec_ref(v___x_2974_);
lean_dec(v_fst_2956_);
lean_dec(v_name_2943_);
lean_dec(v_head_2936_);
lean_dec(v_head_2935_);
v_a_3091_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_3003_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3003_);
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
v___jp_3107_:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; size_t v_sz_3141_; size_t v___x_3142_; lean_object* v___x_3143_; 
lean_inc_ref(v___y_3117_);
v___x_3138_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3138_, 0, v___y_3137_);
lean_ctor_set(v___x_3138_, 1, v_nextMacroScope_3127_);
lean_ctor_set(v___x_3138_, 2, v_ngen_3128_);
lean_ctor_set(v___x_3138_, 3, v_auxDeclNGen_3129_);
lean_ctor_set(v___x_3138_, 4, v_traceState_3130_);
lean_ctor_set(v___x_3138_, 5, v___y_3117_);
lean_ctor_set(v___x_3138_, 6, v_messages_3131_);
lean_ctor_set(v___x_3138_, 7, v_infoState_3132_);
lean_ctor_set(v___x_3138_, 8, v_snapshotTasks_3133_);
v___x_3139_ = lean_st_ref_set(v___y_3121_, v___x_3138_);
v___x_3140_ = lean_box(0);
v_sz_3141_ = lean_array_size(v___y_3123_);
v___x_3142_ = ((size_t)0ULL);
v___x_3143_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v___y_3123_, v_sz_3141_, v___x_3142_, v___x_3140_, v___y_3118_, v___y_3121_);
lean_dec_ref(v___y_3123_);
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_dec_ref_known(v___x_3143_, 1);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3118_);
v___y_2976_ = v___y_3109_;
v___y_2977_ = v___y_3108_;
v___y_2978_ = v___y_3110_;
v___y_2979_ = v___y_3111_;
v___y_2980_ = v___y_3112_;
v___y_2981_ = v___y_3113_;
v___y_2982_ = v___y_3114_;
v___y_2983_ = v___y_3115_;
v___y_2984_ = v___y_3116_;
v___y_2985_ = v___y_3125_;
v___y_2986_ = v___y_3126_;
v___y_2987_ = v___y_3119_;
v___y_2988_ = v___y_3117_;
v___y_2989_ = v___y_3120_;
v___y_2990_ = v___y_3122_;
v___y_2991_ = v___y_3134_;
v___y_2992_ = v___y_3124_;
v___y_2993_ = v___y_3135_;
v___y_2994_ = v___y_3136_;
goto v___jp_2975_;
}
else
{
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_dec_ref_known(v___x_3143_, 1);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3118_);
v___y_2976_ = v___y_3109_;
v___y_2977_ = v___y_3108_;
v___y_2978_ = v___y_3110_;
v___y_2979_ = v___y_3111_;
v___y_2980_ = v___y_3112_;
v___y_2981_ = v___y_3113_;
v___y_2982_ = v___y_3114_;
v___y_2983_ = v___y_3115_;
v___y_2984_ = v___y_3116_;
v___y_2985_ = v___y_3125_;
v___y_2986_ = v___y_3126_;
v___y_2987_ = v___y_3119_;
v___y_2988_ = v___y_3117_;
v___y_2989_ = v___y_3120_;
v___y_2990_ = v___y_3122_;
v___y_2991_ = v___y_3134_;
v___y_2992_ = v___y_3124_;
v___y_2993_ = v___y_3135_;
v___y_2994_ = v___y_3136_;
goto v___jp_2975_;
}
else
{
lean_object* v_a_3144_; uint8_t v___x_3145_; 
v_a_3144_ = lean_ctor_get(v___x_3143_, 0);
lean_inc(v_a_3144_);
lean_dec_ref_known(v___x_3143_, 1);
v___x_3145_ = l_Lean_Exception_isInterrupt(v_a_3144_);
if (v___x_3145_ == 0)
{
lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3146_ = l_Lean_Exception_toMessageData(v_a_3144_);
v___x_3147_ = l_Lean_logError___at___00main_spec__14(v___x_3146_, v___y_3118_, v___y_3121_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3118_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_dec_ref_known(v___x_3147_, 1);
v___y_2976_ = v___y_3109_;
v___y_2977_ = v___y_3108_;
v___y_2978_ = v___y_3110_;
v___y_2979_ = v___y_3111_;
v___y_2980_ = v___y_3112_;
v___y_2981_ = v___y_3113_;
v___y_2982_ = v___y_3114_;
v___y_2983_ = v___y_3115_;
v___y_2984_ = v___y_3116_;
v___y_2985_ = v___y_3125_;
v___y_2986_ = v___y_3126_;
v___y_2987_ = v___y_3119_;
v___y_2988_ = v___y_3117_;
v___y_2989_ = v___y_3120_;
v___y_2990_ = v___y_3122_;
v___y_2991_ = v___y_3134_;
v___y_2992_ = v___y_3124_;
v___y_2993_ = v___y_3135_;
v___y_2994_ = v___y_3136_;
goto v___jp_2975_;
}
else
{
lean_object* v___x_3148_; lean_object* v___x_3149_; 
lean_dec_ref_known(v___x_3147_, 1);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec(v___y_3122_);
lean_dec(v___y_3113_);
lean_dec(v___y_3110_);
lean_dec_ref(v___x_2974_);
lean_dec(v_fst_2956_);
lean_dec(v_name_2943_);
lean_dec(v_head_2936_);
lean_dec(v_head_2935_);
v___x_3148_ = lean_obj_once(&l_main___closed__19, &l_main___closed__19_once, _init_l_main___closed__19);
v___x_3149_ = l_panic___at___00main_spec__5(v___x_3148_);
return v___x_3149_;
}
}
else
{
lean_dec(v_a_3144_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3118_);
v___y_2976_ = v___y_3109_;
v___y_2977_ = v___y_3108_;
v___y_2978_ = v___y_3110_;
v___y_2979_ = v___y_3111_;
v___y_2980_ = v___y_3112_;
v___y_2981_ = v___y_3113_;
v___y_2982_ = v___y_3114_;
v___y_2983_ = v___y_3115_;
v___y_2984_ = v___y_3116_;
v___y_2985_ = v___y_3125_;
v___y_2986_ = v___y_3126_;
v___y_2987_ = v___y_3119_;
v___y_2988_ = v___y_3117_;
v___y_2989_ = v___y_3120_;
v___y_2990_ = v___y_3122_;
v___y_2991_ = v___y_3134_;
v___y_2992_ = v___y_3124_;
v___y_2993_ = v___y_3135_;
v___y_2994_ = v___y_3136_;
goto v___jp_2975_;
}
}
}
}
v___jp_3150_:
{
lean_object* v___x_3175_; lean_object* v_fileName_3176_; lean_object* v_fileMap_3177_; lean_object* v_currRecDepth_3178_; lean_object* v_ref_3179_; lean_object* v_currNamespace_3180_; lean_object* v_openDecls_3181_; lean_object* v_initHeartbeats_3182_; lean_object* v_maxHeartbeats_3183_; lean_object* v_quotContext_3184_; lean_object* v_currMacroScope_3185_; lean_object* v_cancelTk_x3f_3186_; uint8_t v_suppressElabErrors_3187_; lean_object* v_inheritedTraceOptions_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3218_; 
v___x_3175_ = lean_st_ref_take(v___y_3174_);
v_fileName_3176_ = lean_ctor_get(v___y_3173_, 0);
v_fileMap_3177_ = lean_ctor_get(v___y_3173_, 1);
v_currRecDepth_3178_ = lean_ctor_get(v___y_3173_, 3);
v_ref_3179_ = lean_ctor_get(v___y_3173_, 5);
v_currNamespace_3180_ = lean_ctor_get(v___y_3173_, 6);
v_openDecls_3181_ = lean_ctor_get(v___y_3173_, 7);
v_initHeartbeats_3182_ = lean_ctor_get(v___y_3173_, 8);
v_maxHeartbeats_3183_ = lean_ctor_get(v___y_3173_, 9);
v_quotContext_3184_ = lean_ctor_get(v___y_3173_, 10);
v_currMacroScope_3185_ = lean_ctor_get(v___y_3173_, 11);
v_cancelTk_x3f_3186_ = lean_ctor_get(v___y_3173_, 12);
v_suppressElabErrors_3187_ = lean_ctor_get_uint8(v___y_3173_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3188_ = lean_ctor_get(v___y_3173_, 13);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___y_3173_);
if (v_isSharedCheck_3218_ == 0)
{
lean_object* v_unused_3219_; lean_object* v_unused_3220_; 
v_unused_3219_ = lean_ctor_get(v___y_3173_, 4);
lean_dec(v_unused_3219_);
v_unused_3220_ = lean_ctor_get(v___y_3173_, 2);
lean_dec(v_unused_3220_);
v___x_3190_ = v___y_3173_;
v_isShared_3191_ = v_isSharedCheck_3218_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_inheritedTraceOptions_3188_);
lean_inc(v_cancelTk_x3f_3186_);
lean_inc(v_currMacroScope_3185_);
lean_inc(v_quotContext_3184_);
lean_inc(v_maxHeartbeats_3183_);
lean_inc(v_initHeartbeats_3182_);
lean_inc(v_openDecls_3181_);
lean_inc(v_currNamespace_3180_);
lean_inc(v_ref_3179_);
lean_inc(v_currRecDepth_3178_);
lean_inc(v_fileMap_3177_);
lean_inc(v_fileName_3176_);
lean_dec(v___y_3173_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3218_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v_env_3192_; lean_object* v_nextMacroScope_3193_; lean_object* v_ngen_3194_; lean_object* v_auxDeclNGen_3195_; lean_object* v_traceState_3196_; lean_object* v_messages_3197_; lean_object* v_infoState_3198_; lean_object* v_snapshotTasks_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3203_; 
v_env_3192_ = lean_ctor_get(v___x_3175_, 0);
lean_inc_ref(v_env_3192_);
v_nextMacroScope_3193_ = lean_ctor_get(v___x_3175_, 1);
lean_inc(v_nextMacroScope_3193_);
v_ngen_3194_ = lean_ctor_get(v___x_3175_, 2);
lean_inc_ref(v_ngen_3194_);
v_auxDeclNGen_3195_ = lean_ctor_get(v___x_3175_, 3);
lean_inc_ref(v_auxDeclNGen_3195_);
v_traceState_3196_ = lean_ctor_get(v___x_3175_, 4);
lean_inc_ref(v_traceState_3196_);
v_messages_3197_ = lean_ctor_get(v___x_3175_, 6);
lean_inc_ref(v_messages_3197_);
v_infoState_3198_ = lean_ctor_get(v___x_3175_, 7);
lean_inc_ref(v_infoState_3198_);
v_snapshotTasks_3199_ = lean_ctor_get(v___x_3175_, 8);
lean_inc_ref(v_snapshotTasks_3199_);
lean_dec(v___x_3175_);
v___x_3200_ = l_Lean_maxRecDepth;
v___x_3201_ = l_Lean_Option_get___at___00main_spec__9(v___x_2974_, v___x_3200_);
lean_inc_ref(v___x_2974_);
if (v_isShared_3191_ == 0)
{
lean_ctor_set(v___x_3190_, 4, v___x_3201_);
lean_ctor_set(v___x_3190_, 2, v___x_2974_);
v___x_3203_ = v___x_3190_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_fileName_3176_);
lean_ctor_set(v_reuseFailAlloc_3217_, 1, v_fileMap_3177_);
lean_ctor_set(v_reuseFailAlloc_3217_, 2, v___x_2974_);
lean_ctor_set(v_reuseFailAlloc_3217_, 3, v_currRecDepth_3178_);
lean_ctor_set(v_reuseFailAlloc_3217_, 4, v___x_3201_);
lean_ctor_set(v_reuseFailAlloc_3217_, 5, v_ref_3179_);
lean_ctor_set(v_reuseFailAlloc_3217_, 6, v_currNamespace_3180_);
lean_ctor_set(v_reuseFailAlloc_3217_, 7, v_openDecls_3181_);
lean_ctor_set(v_reuseFailAlloc_3217_, 8, v_initHeartbeats_3182_);
lean_ctor_set(v_reuseFailAlloc_3217_, 9, v_maxHeartbeats_3183_);
lean_ctor_set(v_reuseFailAlloc_3217_, 10, v_quotContext_3184_);
lean_ctor_set(v_reuseFailAlloc_3217_, 11, v_currMacroScope_3185_);
lean_ctor_set(v_reuseFailAlloc_3217_, 12, v_cancelTk_x3f_3186_);
lean_ctor_set(v_reuseFailAlloc_3217_, 13, v_inheritedTraceOptions_3188_);
lean_ctor_set_uint8(v_reuseFailAlloc_3217_, sizeof(void*)*14 + 1, v_suppressElabErrors_3187_);
v___x_3203_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
lean_object* v___x_3204_; uint8_t v___x_3205_; 
lean_ctor_set_uint8(v___x_3203_, sizeof(void*)*14, v___y_3169_);
v___x_3204_ = lean_array_get_size(v___y_3165_);
v___x_3205_ = lean_nat_dec_lt(v___x_2973_, v___x_3204_);
if (v___x_3205_ == 0)
{
lean_object* v___x_3206_; 
lean_inc_ref(v___y_3163_);
v___x_3206_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3163_, v_env_3192_, v___x_2967_);
v___y_3108_ = v___y_3152_;
v___y_3109_ = v___y_3151_;
v___y_3110_ = v___y_3153_;
v___y_3111_ = v___y_3154_;
v___y_3112_ = v___y_3155_;
v___y_3113_ = v___y_3156_;
v___y_3114_ = v___y_3157_;
v___y_3115_ = v___y_3158_;
v___y_3116_ = v___y_3159_;
v___y_3117_ = v___y_3160_;
v___y_3118_ = v___x_3203_;
v___y_3119_ = v___y_3161_;
v___y_3120_ = v___y_3162_;
v___y_3121_ = v___y_3174_;
v___y_3122_ = v___y_3164_;
v___y_3123_ = v___y_3165_;
v___y_3124_ = v___y_3166_;
v___y_3125_ = v___y_3167_;
v___y_3126_ = v___y_3168_;
v_nextMacroScope_3127_ = v_nextMacroScope_3193_;
v_ngen_3128_ = v_ngen_3194_;
v_auxDeclNGen_3129_ = v_auxDeclNGen_3195_;
v_traceState_3130_ = v_traceState_3196_;
v_messages_3131_ = v_messages_3197_;
v_infoState_3132_ = v_infoState_3198_;
v_snapshotTasks_3133_ = v_snapshotTasks_3199_;
v___y_3134_ = v___y_3170_;
v___y_3135_ = v___y_3171_;
v___y_3136_ = v___y_3172_;
v___y_3137_ = v___x_3206_;
goto v___jp_3107_;
}
else
{
uint8_t v___x_3207_; 
v___x_3207_ = lean_nat_dec_le(v___x_3204_, v___x_3204_);
if (v___x_3207_ == 0)
{
if (v___x_3205_ == 0)
{
lean_object* v___x_3208_; 
lean_inc_ref(v___y_3163_);
v___x_3208_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3163_, v_env_3192_, v___x_2967_);
v___y_3108_ = v___y_3152_;
v___y_3109_ = v___y_3151_;
v___y_3110_ = v___y_3153_;
v___y_3111_ = v___y_3154_;
v___y_3112_ = v___y_3155_;
v___y_3113_ = v___y_3156_;
v___y_3114_ = v___y_3157_;
v___y_3115_ = v___y_3158_;
v___y_3116_ = v___y_3159_;
v___y_3117_ = v___y_3160_;
v___y_3118_ = v___x_3203_;
v___y_3119_ = v___y_3161_;
v___y_3120_ = v___y_3162_;
v___y_3121_ = v___y_3174_;
v___y_3122_ = v___y_3164_;
v___y_3123_ = v___y_3165_;
v___y_3124_ = v___y_3166_;
v___y_3125_ = v___y_3167_;
v___y_3126_ = v___y_3168_;
v_nextMacroScope_3127_ = v_nextMacroScope_3193_;
v_ngen_3128_ = v_ngen_3194_;
v_auxDeclNGen_3129_ = v_auxDeclNGen_3195_;
v_traceState_3130_ = v_traceState_3196_;
v_messages_3131_ = v_messages_3197_;
v_infoState_3132_ = v_infoState_3198_;
v_snapshotTasks_3133_ = v_snapshotTasks_3199_;
v___y_3134_ = v___y_3170_;
v___y_3135_ = v___y_3171_;
v___y_3136_ = v___y_3172_;
v___y_3137_ = v___x_3208_;
goto v___jp_3107_;
}
else
{
size_t v___x_3209_; size_t v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3209_ = ((size_t)0ULL);
v___x_3210_ = lean_usize_of_nat(v___x_3204_);
v___x_3211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3165_, v___x_3209_, v___x_3210_, v___x_2967_);
lean_inc_ref(v___y_3163_);
v___x_3212_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3163_, v_env_3192_, v___x_3211_);
v___y_3108_ = v___y_3152_;
v___y_3109_ = v___y_3151_;
v___y_3110_ = v___y_3153_;
v___y_3111_ = v___y_3154_;
v___y_3112_ = v___y_3155_;
v___y_3113_ = v___y_3156_;
v___y_3114_ = v___y_3157_;
v___y_3115_ = v___y_3158_;
v___y_3116_ = v___y_3159_;
v___y_3117_ = v___y_3160_;
v___y_3118_ = v___x_3203_;
v___y_3119_ = v___y_3161_;
v___y_3120_ = v___y_3162_;
v___y_3121_ = v___y_3174_;
v___y_3122_ = v___y_3164_;
v___y_3123_ = v___y_3165_;
v___y_3124_ = v___y_3166_;
v___y_3125_ = v___y_3167_;
v___y_3126_ = v___y_3168_;
v_nextMacroScope_3127_ = v_nextMacroScope_3193_;
v_ngen_3128_ = v_ngen_3194_;
v_auxDeclNGen_3129_ = v_auxDeclNGen_3195_;
v_traceState_3130_ = v_traceState_3196_;
v_messages_3131_ = v_messages_3197_;
v_infoState_3132_ = v_infoState_3198_;
v_snapshotTasks_3133_ = v_snapshotTasks_3199_;
v___y_3134_ = v___y_3170_;
v___y_3135_ = v___y_3171_;
v___y_3136_ = v___y_3172_;
v___y_3137_ = v___x_3212_;
goto v___jp_3107_;
}
}
else
{
size_t v___x_3213_; size_t v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3213_ = ((size_t)0ULL);
v___x_3214_ = lean_usize_of_nat(v___x_3204_);
v___x_3215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3165_, v___x_3213_, v___x_3214_, v___x_2967_);
lean_inc_ref(v___y_3163_);
v___x_3216_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3163_, v_env_3192_, v___x_3215_);
v___y_3108_ = v___y_3152_;
v___y_3109_ = v___y_3151_;
v___y_3110_ = v___y_3153_;
v___y_3111_ = v___y_3154_;
v___y_3112_ = v___y_3155_;
v___y_3113_ = v___y_3156_;
v___y_3114_ = v___y_3157_;
v___y_3115_ = v___y_3158_;
v___y_3116_ = v___y_3159_;
v___y_3117_ = v___y_3160_;
v___y_3118_ = v___x_3203_;
v___y_3119_ = v___y_3161_;
v___y_3120_ = v___y_3162_;
v___y_3121_ = v___y_3174_;
v___y_3122_ = v___y_3164_;
v___y_3123_ = v___y_3165_;
v___y_3124_ = v___y_3166_;
v___y_3125_ = v___y_3167_;
v___y_3126_ = v___y_3168_;
v_nextMacroScope_3127_ = v_nextMacroScope_3193_;
v_ngen_3128_ = v_ngen_3194_;
v_auxDeclNGen_3129_ = v_auxDeclNGen_3195_;
v_traceState_3130_ = v_traceState_3196_;
v_messages_3131_ = v_messages_3197_;
v_infoState_3132_ = v_infoState_3198_;
v_snapshotTasks_3133_ = v_snapshotTasks_3199_;
v___y_3134_ = v___y_3170_;
v___y_3135_ = v___y_3171_;
v___y_3136_ = v___y_3172_;
v___y_3137_ = v___x_3216_;
goto v___jp_3107_;
}
}
}
}
}
v___jp_3221_:
{
if (v___y_3245_ == 0)
{
lean_object* v___x_3246_; lean_object* v_env_3247_; lean_object* v_nextMacroScope_3248_; lean_object* v_ngen_3249_; lean_object* v_auxDeclNGen_3250_; lean_object* v_traceState_3251_; lean_object* v_messages_3252_; lean_object* v_infoState_3253_; lean_object* v_snapshotTasks_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3263_; 
v___x_3246_ = lean_st_ref_take(v___y_3235_);
v_env_3247_ = lean_ctor_get(v___x_3246_, 0);
v_nextMacroScope_3248_ = lean_ctor_get(v___x_3246_, 1);
v_ngen_3249_ = lean_ctor_get(v___x_3246_, 2);
v_auxDeclNGen_3250_ = lean_ctor_get(v___x_3246_, 3);
v_traceState_3251_ = lean_ctor_get(v___x_3246_, 4);
v_messages_3252_ = lean_ctor_get(v___x_3246_, 6);
v_infoState_3253_ = lean_ctor_get(v___x_3246_, 7);
v_snapshotTasks_3254_ = lean_ctor_get(v___x_3246_, 8);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3263_ == 0)
{
lean_object* v_unused_3264_; 
v_unused_3264_ = lean_ctor_get(v___x_3246_, 5);
lean_dec(v_unused_3264_);
v___x_3256_ = v___x_3246_;
v_isShared_3257_ = v_isSharedCheck_3263_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_snapshotTasks_3254_);
lean_inc(v_infoState_3253_);
lean_inc(v_messages_3252_);
lean_inc(v_traceState_3251_);
lean_inc(v_auxDeclNGen_3250_);
lean_inc(v_ngen_3249_);
lean_inc(v_nextMacroScope_3248_);
lean_inc(v_env_3247_);
lean_dec(v___x_3246_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3263_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3258_; lean_object* v___x_3260_; 
v___x_3258_ = l_Lean_Kernel_enableDiag(v_env_3247_, v___y_3241_);
lean_inc_ref(v___y_3231_);
if (v_isShared_3257_ == 0)
{
lean_ctor_set(v___x_3256_, 5, v___y_3231_);
lean_ctor_set(v___x_3256_, 0, v___x_3258_);
v___x_3260_ = v___x_3256_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3258_);
lean_ctor_set(v_reuseFailAlloc_3262_, 1, v_nextMacroScope_3248_);
lean_ctor_set(v_reuseFailAlloc_3262_, 2, v_ngen_3249_);
lean_ctor_set(v_reuseFailAlloc_3262_, 3, v_auxDeclNGen_3250_);
lean_ctor_set(v_reuseFailAlloc_3262_, 4, v_traceState_3251_);
lean_ctor_set(v_reuseFailAlloc_3262_, 5, v___y_3231_);
lean_ctor_set(v_reuseFailAlloc_3262_, 6, v_messages_3252_);
lean_ctor_set(v_reuseFailAlloc_3262_, 7, v_infoState_3253_);
lean_ctor_set(v_reuseFailAlloc_3262_, 8, v_snapshotTasks_3254_);
v___x_3260_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
lean_object* v___x_3261_; 
v___x_3261_ = lean_st_ref_set(v___y_3235_, v___x_3260_);
lean_inc(v___y_3235_);
v___y_3151_ = v___y_3223_;
v___y_3152_ = v___y_3222_;
v___y_3153_ = v___y_3224_;
v___y_3154_ = v___y_3225_;
v___y_3155_ = v___y_3226_;
v___y_3156_ = v___y_3227_;
v___y_3157_ = v___y_3228_;
v___y_3158_ = v___y_3229_;
v___y_3159_ = v___y_3230_;
v___y_3160_ = v___y_3231_;
v___y_3161_ = v___y_3232_;
v___y_3162_ = v___y_3233_;
v___y_3163_ = v___y_3234_;
v___y_3164_ = v___y_3235_;
v___y_3165_ = v___y_3236_;
v___y_3166_ = v___y_3237_;
v___y_3167_ = v___y_3239_;
v___y_3168_ = v___y_3240_;
v___y_3169_ = v___y_3241_;
v___y_3170_ = v___y_3242_;
v___y_3171_ = v___y_3243_;
v___y_3172_ = v___y_3244_;
v___y_3173_ = v___y_3238_;
v___y_3174_ = v___y_3235_;
goto v___jp_3150_;
}
}
}
else
{
lean_inc(v___y_3235_);
v___y_3151_ = v___y_3223_;
v___y_3152_ = v___y_3222_;
v___y_3153_ = v___y_3224_;
v___y_3154_ = v___y_3225_;
v___y_3155_ = v___y_3226_;
v___y_3156_ = v___y_3227_;
v___y_3157_ = v___y_3228_;
v___y_3158_ = v___y_3229_;
v___y_3159_ = v___y_3230_;
v___y_3160_ = v___y_3231_;
v___y_3161_ = v___y_3232_;
v___y_3162_ = v___y_3233_;
v___y_3163_ = v___y_3234_;
v___y_3164_ = v___y_3235_;
v___y_3165_ = v___y_3236_;
v___y_3166_ = v___y_3237_;
v___y_3167_ = v___y_3239_;
v___y_3168_ = v___y_3240_;
v___y_3169_ = v___y_3241_;
v___y_3170_ = v___y_3242_;
v___y_3171_ = v___y_3243_;
v___y_3172_ = v___y_3244_;
v___y_3173_ = v___y_3238_;
v___y_3174_ = v___y_3235_;
goto v___jp_3150_;
}
}
v___jp_3268_:
{
lean_object* v___x_3278_; 
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 1, v___y_3276_);
lean_ctor_set(v___x_2959_, 0, v___y_3275_);
v___x_3278_ = v___x_2959_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___y_3275_);
lean_ctor_set(v_reuseFailAlloc_3373_, 1, v___y_3276_);
v___x_3278_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v_moduleData_3282_; lean_object* v___x_3283_; uint8_t v___x_3284_; 
v___x_3279_ = lean_box(0);
lean_inc_ref(v___y_3273_);
v___x_3280_ = l_Lean_EnvExtension_setState___redArg(v___y_3273_, v___y_3274_, v___x_3278_, v___x_3279_);
v___x_3281_ = l_Lean_Environment_header(v___x_3280_);
v_moduleData_3282_ = lean_ctor_get(v___x_3281_, 6);
lean_inc_ref(v_moduleData_3282_);
lean_dec_ref(v___x_3281_);
v___x_3283_ = lean_array_get_size(v_moduleData_3282_);
v___x_3284_ = lean_nat_dec_lt(v___y_3272_, v___x_3283_);
if (v___x_3284_ == 0)
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
lean_dec_ref(v_moduleData_3282_);
lean_dec_ref(v___x_3280_);
lean_dec(v___y_3272_);
lean_dec(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec_ref(v___x_2974_);
lean_dec(v_fst_2956_);
lean_dec(v_name_2943_);
lean_dec(v_head_2936_);
lean_dec(v_head_2935_);
v___x_3285_ = lean_obj_once(&l_main___closed__21, &l_main___closed__21_once, _init_l_main___closed__21);
v___x_3286_ = l_panic___at___00main_spec__5(v___x_3285_);
return v___x_3286_;
}
else
{
lean_object* v_base_3287_; lean_object* v_private_3288_; lean_object* v_header_3289_; lean_object* v_serverBaseExts_3290_; lean_object* v_checked_3291_; lean_object* v_asyncConstsMap_3292_; lean_object* v_asyncCtx_x3f_3293_; lean_object* v_importRealizationCtx_x3f_3294_; lean_object* v_localRealizationCtxMap_3295_; lean_object* v_allRealizations_3296_; uint8_t v_isExporting_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3371_; 
v_base_3287_ = lean_ctor_get(v___x_3280_, 0);
lean_inc_ref(v_base_3287_);
v_private_3288_ = lean_ctor_get(v_base_3287_, 0);
lean_inc(v_private_3288_);
v_header_3289_ = lean_ctor_get(v_private_3288_, 5);
lean_inc_ref(v_header_3289_);
v_serverBaseExts_3290_ = lean_ctor_get(v___x_3280_, 1);
v_checked_3291_ = lean_ctor_get(v___x_3280_, 2);
v_asyncConstsMap_3292_ = lean_ctor_get(v___x_3280_, 3);
v_asyncCtx_x3f_3293_ = lean_ctor_get(v___x_3280_, 4);
v_importRealizationCtx_x3f_3294_ = lean_ctor_get(v___x_3280_, 5);
v_localRealizationCtxMap_3295_ = lean_ctor_get(v___x_3280_, 6);
v_allRealizations_3296_ = lean_ctor_get(v___x_3280_, 7);
v_isExporting_3297_ = lean_ctor_get_uint8(v___x_3280_, sizeof(void*)*8);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3371_ == 0)
{
lean_object* v_unused_3372_; 
v_unused_3372_ = lean_ctor_get(v___x_3280_, 0);
lean_dec(v_unused_3372_);
v___x_3299_ = v___x_3280_;
v_isShared_3300_ = v_isSharedCheck_3371_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_allRealizations_3296_);
lean_inc(v_localRealizationCtxMap_3295_);
lean_inc(v_importRealizationCtx_x3f_3294_);
lean_inc(v_asyncCtx_x3f_3293_);
lean_inc(v_asyncConstsMap_3292_);
lean_inc(v_checked_3291_);
lean_inc(v_serverBaseExts_3290_);
lean_dec(v___x_3280_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3371_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v_public_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3369_; 
v_public_3301_ = lean_ctor_get(v_base_3287_, 1);
v_isSharedCheck_3369_ = !lean_is_exclusive(v_base_3287_);
if (v_isSharedCheck_3369_ == 0)
{
lean_object* v_unused_3370_; 
v_unused_3370_ = lean_ctor_get(v_base_3287_, 0);
lean_dec(v_unused_3370_);
v___x_3303_ = v_base_3287_;
v_isShared_3304_ = v_isSharedCheck_3369_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_public_3301_);
lean_dec(v_base_3287_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3369_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v_constants_3305_; uint8_t v_quotInit_3306_; lean_object* v_diagnostics_3307_; lean_object* v_const2ModIdx_3308_; lean_object* v_extensions_3309_; lean_object* v_irBaseExts_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3367_; 
v_constants_3305_ = lean_ctor_get(v_private_3288_, 0);
v_quotInit_3306_ = lean_ctor_get_uint8(v_private_3288_, sizeof(void*)*6);
v_diagnostics_3307_ = lean_ctor_get(v_private_3288_, 1);
v_const2ModIdx_3308_ = lean_ctor_get(v_private_3288_, 2);
v_extensions_3309_ = lean_ctor_get(v_private_3288_, 3);
v_irBaseExts_3310_ = lean_ctor_get(v_private_3288_, 4);
v_isSharedCheck_3367_ = !lean_is_exclusive(v_private_3288_);
if (v_isSharedCheck_3367_ == 0)
{
lean_object* v_unused_3368_; 
v_unused_3368_ = lean_ctor_get(v_private_3288_, 5);
lean_dec(v_unused_3368_);
v___x_3312_ = v_private_3288_;
v_isShared_3313_ = v_isSharedCheck_3367_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_irBaseExts_3310_);
lean_inc(v_extensions_3309_);
lean_inc(v_const2ModIdx_3308_);
lean_inc(v_diagnostics_3307_);
lean_inc(v_constants_3305_);
lean_dec(v_private_3288_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3367_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
uint32_t v_trustLevel_3314_; lean_object* v_mainModule_3315_; uint8_t v_isModule_3316_; lean_object* v_regions_3317_; lean_object* v_modules_3318_; lean_object* v_moduleName2Idx_3319_; lean_object* v_importAllModules_3320_; lean_object* v_moduleData_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3365_; 
v_trustLevel_3314_ = lean_ctor_get_uint32(v_header_3289_, sizeof(void*)*7);
v_mainModule_3315_ = lean_ctor_get(v_header_3289_, 0);
v_isModule_3316_ = lean_ctor_get_uint8(v_header_3289_, sizeof(void*)*7 + 4);
v_regions_3317_ = lean_ctor_get(v_header_3289_, 2);
v_modules_3318_ = lean_ctor_get(v_header_3289_, 3);
v_moduleName2Idx_3319_ = lean_ctor_get(v_header_3289_, 4);
v_importAllModules_3320_ = lean_ctor_get(v_header_3289_, 5);
v_moduleData_3321_ = lean_ctor_get(v_header_3289_, 6);
v_isSharedCheck_3365_ = !lean_is_exclusive(v_header_3289_);
if (v_isSharedCheck_3365_ == 0)
{
lean_object* v_unused_3366_; 
v_unused_3366_ = lean_ctor_get(v_header_3289_, 1);
lean_dec(v_unused_3366_);
v___x_3323_ = v_header_3289_;
v_isShared_3324_ = v_isSharedCheck_3365_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_moduleData_3321_);
lean_inc(v_importAllModules_3320_);
lean_inc(v_moduleName2Idx_3319_);
lean_inc(v_modules_3318_);
lean_inc(v_regions_3317_);
lean_inc(v_mainModule_3315_);
lean_dec(v_header_3289_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3365_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3325_; lean_object* v_imports_3326_; lean_object* v___x_3328_; 
v___x_3325_ = lean_array_fget(v_moduleData_3282_, v___y_3272_);
lean_dec_ref(v_moduleData_3282_);
v_imports_3326_ = lean_ctor_get(v___x_3325_, 0);
lean_inc_ref(v_imports_3326_);
lean_dec(v___x_3325_);
if (v_isShared_3324_ == 0)
{
lean_ctor_set(v___x_3323_, 1, v_imports_3326_);
v___x_3328_ = v___x_3323_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 7, 5);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_mainModule_3315_);
lean_ctor_set(v_reuseFailAlloc_3364_, 1, v_imports_3326_);
lean_ctor_set(v_reuseFailAlloc_3364_, 2, v_regions_3317_);
lean_ctor_set(v_reuseFailAlloc_3364_, 3, v_modules_3318_);
lean_ctor_set(v_reuseFailAlloc_3364_, 4, v_moduleName2Idx_3319_);
lean_ctor_set(v_reuseFailAlloc_3364_, 5, v_importAllModules_3320_);
lean_ctor_set(v_reuseFailAlloc_3364_, 6, v_moduleData_3321_);
lean_ctor_set_uint32(v_reuseFailAlloc_3364_, sizeof(void*)*7, v_trustLevel_3314_);
lean_ctor_set_uint8(v_reuseFailAlloc_3364_, sizeof(void*)*7 + 4, v_isModule_3316_);
v___x_3328_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
lean_object* v___x_3330_; 
if (v_isShared_3313_ == 0)
{
lean_ctor_set(v___x_3312_, 5, v___x_3328_);
v___x_3330_ = v___x_3312_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_constants_3305_);
lean_ctor_set(v_reuseFailAlloc_3363_, 1, v_diagnostics_3307_);
lean_ctor_set(v_reuseFailAlloc_3363_, 2, v_const2ModIdx_3308_);
lean_ctor_set(v_reuseFailAlloc_3363_, 3, v_extensions_3309_);
lean_ctor_set(v_reuseFailAlloc_3363_, 4, v_irBaseExts_3310_);
lean_ctor_set(v_reuseFailAlloc_3363_, 5, v___x_3328_);
lean_ctor_set_uint8(v_reuseFailAlloc_3363_, sizeof(void*)*6, v_quotInit_3306_);
v___x_3330_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
lean_object* v___x_3332_; 
if (v_isShared_3304_ == 0)
{
lean_ctor_set(v___x_3303_, 0, v___x_3330_);
v___x_3332_ = v___x_3303_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v___x_3330_);
lean_ctor_set(v_reuseFailAlloc_3362_, 1, v_public_3301_);
v___x_3332_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
lean_object* v___x_3334_; 
if (v_isShared_3300_ == 0)
{
lean_ctor_set(v___x_3299_, 0, v___x_3332_);
v___x_3334_ = v___x_3299_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3332_);
lean_ctor_set(v_reuseFailAlloc_3361_, 1, v_serverBaseExts_3290_);
lean_ctor_set(v_reuseFailAlloc_3361_, 2, v_checked_3291_);
lean_ctor_set(v_reuseFailAlloc_3361_, 3, v_asyncConstsMap_3292_);
lean_ctor_set(v_reuseFailAlloc_3361_, 4, v_asyncCtx_x3f_3293_);
lean_ctor_set(v_reuseFailAlloc_3361_, 5, v_importRealizationCtx_x3f_3294_);
lean_ctor_set(v_reuseFailAlloc_3361_, 6, v_localRealizationCtxMap_3295_);
lean_ctor_set(v_reuseFailAlloc_3361_, 7, v_allRealizations_3296_);
lean_ctor_set_uint8(v_reuseFailAlloc_3361_, sizeof(void*)*8, v_isExporting_3297_);
v___x_3334_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v_env_3357_; lean_object* v___x_3358_; uint8_t v___x_3359_; uint8_t v___x_3360_; 
v___x_3335_ = l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
v___x_3336_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2968_, v___x_3335_, v___x_3334_, v___y_3272_, v___y_3271_);
lean_dec(v___y_3272_);
v___x_3337_ = l_Lean_firstFrontendMacroScope;
v___x_3338_ = lean_obj_once(&l_main___closed__22, &l_main___closed__22_once, _init_l_main___closed__22);
v___x_3339_ = ((lean_object*)(l_main___closed__25));
lean_inc_n(v___y_3270_, 3);
v___x_3340_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3340_, 0, v___y_3270_);
lean_ctor_set(v___x_3340_, 1, v___x_3267_);
lean_ctor_set(v___x_3340_, 2, v___x_2954_);
v___x_3341_ = lean_obj_once(&l_main___closed__26, &l_main___closed__26_once, _init_l_main___closed__26);
v___x_3342_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_3343_ = lean_obj_once(&l_main___closed__30, &l_main___closed__30_once, _init_l_main___closed__30);
v___x_3344_ = lean_obj_once(&l_main___closed__31, &l_main___closed__31_once, _init_l_main___closed__31);
v___x_3345_ = ((lean_object*)(l_main___closed__32));
lean_inc_ref(v___x_3340_);
v___x_3346_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3334_);
lean_ctor_set(v___x_3346_, 1, v___x_3338_);
lean_ctor_set(v___x_3346_, 2, v___x_3339_);
lean_ctor_set(v___x_3346_, 3, v___x_3340_);
lean_ctor_set(v___x_3346_, 4, v___x_3341_);
lean_ctor_set(v___x_3346_, 5, v___x_3342_);
lean_ctor_set(v___x_3346_, 6, v___x_3343_);
lean_ctor_set(v___x_3346_, 7, v___x_3344_);
lean_ctor_set(v___x_3346_, 8, v___x_3345_);
v___x_3347_ = lean_st_mk_ref(v___x_3346_);
v___x_3348_ = l_Lean_inheritedTraceOptions;
v___x_3349_ = lean_st_ref_get(v___x_3348_);
v___x_3350_ = lean_st_ref_get(v___x_3347_);
v___x_3351_ = l_Lean_instInhabitedFileMap_default;
v___x_3352_ = lean_unsigned_to_nat(1000u);
v___x_3353_ = lean_box(0);
v___x_3354_ = l_Lean_Core_getMaxHeartbeats(v___x_2974_);
v___x_3355_ = lean_box(0);
lean_inc_ref(v___x_2974_);
lean_inc(v_head_2935_);
v___x_3356_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3356_, 0, v_head_2935_);
lean_ctor_set(v___x_3356_, 1, v___x_3351_);
lean_ctor_set(v___x_3356_, 2, v___x_2974_);
lean_ctor_set(v___x_3356_, 3, v___x_2973_);
lean_ctor_set(v___x_3356_, 4, v___x_3352_);
lean_ctor_set(v___x_3356_, 5, v___x_3353_);
lean_ctor_set(v___x_3356_, 6, v___y_3270_);
lean_ctor_set(v___x_3356_, 7, v___x_2954_);
lean_ctor_set(v___x_3356_, 8, v___x_2973_);
lean_ctor_set(v___x_3356_, 9, v___x_3354_);
lean_ctor_set(v___x_3356_, 10, v___y_3270_);
lean_ctor_set(v___x_3356_, 11, v___x_3337_);
lean_ctor_set(v___x_3356_, 12, v___x_3355_);
lean_ctor_set(v___x_3356_, 13, v___x_3349_);
lean_ctor_set_uint8(v___x_3356_, sizeof(void*)*14, v___x_2945_);
lean_ctor_set_uint8(v___x_3356_, sizeof(void*)*14 + 1, v___x_2945_);
v_env_3357_ = lean_ctor_get(v___x_3350_, 0);
lean_inc_ref(v_env_3357_);
lean_dec(v___x_3350_);
v___x_3358_ = l_Lean_diagnostics;
v___x_3359_ = l_Lean_Option_get___at___00main_spec__8(v___x_2974_, v___x_3358_);
v___x_3360_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3357_);
lean_dec_ref(v_env_3357_);
if (v___x_3360_ == 0)
{
if (v___x_3359_ == 0)
{
v___y_3222_ = v___x_3355_;
v___y_3223_ = v___x_3284_;
v___y_3224_ = v___y_3269_;
v___y_3225_ = v___x_3351_;
v___y_3226_ = v___x_3342_;
v___y_3227_ = v___x_2954_;
v___y_3228_ = v___x_3353_;
v___y_3229_ = v___x_3337_;
v___y_3230_ = v___x_3348_;
v___y_3231_ = v___x_3342_;
v___y_3232_ = v___x_3344_;
v___y_3233_ = v___x_3338_;
v___y_3234_ = v___x_3335_;
v___y_3235_ = v___x_3347_;
v___y_3236_ = v___x_3336_;
v___y_3237_ = v___x_3340_;
v___y_3238_ = v___x_3356_;
v___y_3239_ = v___y_3270_;
v___y_3240_ = v___x_3345_;
v___y_3241_ = v___x_3359_;
v___y_3242_ = v___x_3343_;
v___y_3243_ = v___x_3339_;
v___y_3244_ = v___x_3341_;
v___y_3245_ = v___x_3284_;
goto v___jp_3221_;
}
else
{
v___y_3222_ = v___x_3355_;
v___y_3223_ = v___x_3284_;
v___y_3224_ = v___y_3269_;
v___y_3225_ = v___x_3351_;
v___y_3226_ = v___x_3342_;
v___y_3227_ = v___x_2954_;
v___y_3228_ = v___x_3353_;
v___y_3229_ = v___x_3337_;
v___y_3230_ = v___x_3348_;
v___y_3231_ = v___x_3342_;
v___y_3232_ = v___x_3344_;
v___y_3233_ = v___x_3338_;
v___y_3234_ = v___x_3335_;
v___y_3235_ = v___x_3347_;
v___y_3236_ = v___x_3336_;
v___y_3237_ = v___x_3340_;
v___y_3238_ = v___x_3356_;
v___y_3239_ = v___y_3270_;
v___y_3240_ = v___x_3345_;
v___y_3241_ = v___x_3359_;
v___y_3242_ = v___x_3343_;
v___y_3243_ = v___x_3339_;
v___y_3244_ = v___x_3341_;
v___y_3245_ = v___x_3360_;
goto v___jp_3221_;
}
}
else
{
v___y_3222_ = v___x_3355_;
v___y_3223_ = v___x_3284_;
v___y_3224_ = v___y_3269_;
v___y_3225_ = v___x_3351_;
v___y_3226_ = v___x_3342_;
v___y_3227_ = v___x_2954_;
v___y_3228_ = v___x_3353_;
v___y_3229_ = v___x_3337_;
v___y_3230_ = v___x_3348_;
v___y_3231_ = v___x_3342_;
v___y_3232_ = v___x_3344_;
v___y_3233_ = v___x_3338_;
v___y_3234_ = v___x_3335_;
v___y_3235_ = v___x_3347_;
v___y_3236_ = v___x_3336_;
v___y_3237_ = v___x_3340_;
v___y_3238_ = v___x_3356_;
v___y_3239_ = v___y_3270_;
v___y_3240_ = v___x_3345_;
v___y_3241_ = v___x_3359_;
v___y_3242_ = v___x_3343_;
v___y_3243_ = v___x_3339_;
v___y_3244_ = v___x_3341_;
v___y_3245_ = v___x_3359_;
goto v___jp_3221_;
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
v___jp_3374_:
{
lean_object* v___x_3380_; lean_object* v_toEnvExtension_3381_; lean_object* v_asyncMode_3382_; lean_object* v___x_3383_; lean_object* v_importedEntries_3384_; lean_object* v_state_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; uint8_t v___x_3388_; 
v___x_3380_ = l_Lean_IR_declMapExt;
v_toEnvExtension_3381_ = lean_ctor_get(v___x_3380_, 0);
v_asyncMode_3382_ = lean_ctor_get(v_toEnvExtension_3381_, 2);
lean_inc(v___y_3376_);
lean_inc_ref(v___y_3379_);
v___x_3383_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2965_, v_toEnvExtension_3381_, v___y_3379_, v_asyncMode_3382_, v___y_3376_);
v_importedEntries_3384_ = lean_ctor_get(v___x_3383_, 0);
lean_inc_ref(v_importedEntries_3384_);
v_state_3385_ = lean_ctor_get(v___x_3383_, 1);
lean_inc(v_state_3385_);
lean_dec(v___x_3383_);
v___x_3386_ = lean_array_get_borrowed(v___x_2966_, v_importedEntries_3384_, v___y_3378_);
v___x_3387_ = lean_array_get_size(v___x_3386_);
v___x_3388_ = lean_nat_dec_lt(v___x_2973_, v___x_3387_);
if (v___x_3388_ == 0)
{
v___y_3269_ = v___y_3375_;
v___y_3270_ = v___y_3376_;
v___y_3271_ = v___y_3377_;
v___y_3272_ = v___y_3378_;
v___y_3273_ = v_toEnvExtension_3381_;
v___y_3274_ = v___y_3379_;
v___y_3275_ = v_importedEntries_3384_;
v___y_3276_ = v_state_3385_;
goto v___jp_3268_;
}
else
{
uint8_t v___x_3389_; 
v___x_3389_ = lean_nat_dec_le(v___x_3387_, v___x_3387_);
if (v___x_3389_ == 0)
{
if (v___x_3388_ == 0)
{
v___y_3269_ = v___y_3375_;
v___y_3270_ = v___y_3376_;
v___y_3271_ = v___y_3377_;
v___y_3272_ = v___y_3378_;
v___y_3273_ = v_toEnvExtension_3381_;
v___y_3274_ = v___y_3379_;
v___y_3275_ = v_importedEntries_3384_;
v___y_3276_ = v_state_3385_;
goto v___jp_3268_;
}
else
{
size_t v___x_3390_; size_t v___x_3391_; lean_object* v___x_3392_; 
v___x_3390_ = ((size_t)0ULL);
v___x_3391_ = lean_usize_of_nat(v___x_3387_);
lean_inc_ref(v___y_3379_);
v___x_3392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3379_, v___x_3386_, v___x_3390_, v___x_3391_, v_state_3385_);
v___y_3269_ = v___y_3375_;
v___y_3270_ = v___y_3376_;
v___y_3271_ = v___y_3377_;
v___y_3272_ = v___y_3378_;
v___y_3273_ = v_toEnvExtension_3381_;
v___y_3274_ = v___y_3379_;
v___y_3275_ = v_importedEntries_3384_;
v___y_3276_ = v___x_3392_;
goto v___jp_3268_;
}
}
else
{
size_t v___x_3393_; size_t v___x_3394_; lean_object* v___x_3395_; 
v___x_3393_ = ((size_t)0ULL);
v___x_3394_ = lean_usize_of_nat(v___x_3387_);
lean_inc_ref(v___y_3379_);
v___x_3395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3379_, v___x_3386_, v___x_3393_, v___x_3394_, v_state_3385_);
v___y_3269_ = v___y_3375_;
v___y_3270_ = v___y_3376_;
v___y_3271_ = v___y_3377_;
v___y_3272_ = v___y_3378_;
v___y_3273_ = v_toEnvExtension_3381_;
v___y_3274_ = v___y_3379_;
v___y_3275_ = v_importedEntries_3384_;
v___y_3276_ = v___x_3395_;
goto v___jp_3268_;
}
}
}
v___jp_3396_:
{
uint8_t v___x_3404_; 
v___x_3404_ = lean_nat_dec_lt(v___x_2973_, v___y_3401_);
if (v___x_3404_ == 0)
{
lean_dec_ref(v___y_3402_);
lean_dec(v___y_3401_);
v___y_3375_ = v___y_3397_;
v___y_3376_ = v___y_3398_;
v___y_3377_ = v___y_3399_;
v___y_3378_ = v___y_3400_;
v___y_3379_ = v___y_3403_;
goto v___jp_3374_;
}
else
{
uint8_t v___x_3405_; 
v___x_3405_ = lean_nat_dec_le(v___y_3401_, v___y_3401_);
if (v___x_3405_ == 0)
{
if (v___x_3404_ == 0)
{
lean_dec_ref(v___y_3402_);
lean_dec(v___y_3401_);
v___y_3375_ = v___y_3397_;
v___y_3376_ = v___y_3398_;
v___y_3377_ = v___y_3399_;
v___y_3378_ = v___y_3400_;
v___y_3379_ = v___y_3403_;
goto v___jp_3374_;
}
else
{
size_t v___x_3406_; size_t v___x_3407_; lean_object* v___x_3408_; 
v___x_3406_ = ((size_t)0ULL);
v___x_3407_ = lean_usize_of_nat(v___y_3401_);
lean_dec(v___y_3401_);
v___x_3408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3402_, v___x_3406_, v___x_3407_, v___y_3403_);
lean_dec_ref(v___y_3402_);
v___y_3375_ = v___y_3397_;
v___y_3376_ = v___y_3398_;
v___y_3377_ = v___y_3399_;
v___y_3378_ = v___y_3400_;
v___y_3379_ = v___x_3408_;
goto v___jp_3374_;
}
}
else
{
size_t v___x_3409_; size_t v___x_3410_; lean_object* v___x_3411_; 
v___x_3409_ = ((size_t)0ULL);
v___x_3410_ = lean_usize_of_nat(v___y_3401_);
lean_dec(v___y_3401_);
v___x_3411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3402_, v___x_3409_, v___x_3410_, v___y_3403_);
lean_dec_ref(v___y_3402_);
v___y_3375_ = v___y_3397_;
v___y_3376_ = v___y_3398_;
v___y_3377_ = v___y_3399_;
v___y_3378_ = v___y_3400_;
v___y_3379_ = v___x_3411_;
goto v___jp_3374_;
}
}
}
v___jp_3412_:
{
lean_object* v___x_3419_; uint8_t v___x_3420_; 
v___x_3419_ = lean_array_get_size(v___y_3418_);
v___x_3420_ = lean_nat_dec_lt(v___x_2973_, v___x_3419_);
if (v___x_3420_ == 0)
{
v___y_3397_ = v___y_3413_;
v___y_3398_ = v___y_3415_;
v___y_3399_ = v___y_3416_;
v___y_3400_ = v___y_3414_;
v___y_3401_ = v___x_3419_;
v___y_3402_ = v___y_3418_;
v___y_3403_ = v___y_3417_;
goto v___jp_3396_;
}
else
{
uint8_t v___x_3421_; 
v___x_3421_ = lean_nat_dec_le(v___x_3419_, v___x_3419_);
if (v___x_3421_ == 0)
{
if (v___x_3420_ == 0)
{
v___y_3397_ = v___y_3413_;
v___y_3398_ = v___y_3415_;
v___y_3399_ = v___y_3416_;
v___y_3400_ = v___y_3414_;
v___y_3401_ = v___x_3419_;
v___y_3402_ = v___y_3418_;
v___y_3403_ = v___y_3417_;
goto v___jp_3396_;
}
else
{
size_t v___x_3422_; size_t v___x_3423_; lean_object* v___x_3424_; 
v___x_3422_ = ((size_t)0ULL);
v___x_3423_ = lean_usize_of_nat(v___x_3419_);
v___x_3424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3418_, v___x_3422_, v___x_3423_, v___y_3417_);
v___y_3397_ = v___y_3413_;
v___y_3398_ = v___y_3415_;
v___y_3399_ = v___y_3416_;
v___y_3400_ = v___y_3414_;
v___y_3401_ = v___x_3419_;
v___y_3402_ = v___y_3418_;
v___y_3403_ = v___x_3424_;
goto v___jp_3396_;
}
}
else
{
size_t v___x_3425_; size_t v___x_3426_; lean_object* v___x_3427_; 
v___x_3425_ = ((size_t)0ULL);
v___x_3426_ = lean_usize_of_nat(v___x_3419_);
v___x_3427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3418_, v___x_3425_, v___x_3426_, v___y_3417_);
v___y_3397_ = v___y_3413_;
v___y_3398_ = v___y_3415_;
v___y_3399_ = v___y_3416_;
v___y_3400_ = v___y_3414_;
v___y_3401_ = v___x_3419_;
v___y_3402_ = v___y_3418_;
v___y_3403_ = v___x_3427_;
goto v___jp_3396_;
}
}
}
v___jp_3431_:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___f_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3433_ = l_Lean_instInhabitedImportState_default;
v___x_3434_ = lean_box(v___x_3430_);
v___x_3435_ = lean_box(v___y_3432_);
v___x_3436_ = lean_box(v___x_2970_);
v___x_3437_ = lean_box(v___x_2945_);
lean_inc_ref(v___x_2974_);
lean_inc(v_name_2943_);
v___f_3438_ = lean_alloc_closure((void*)(l_main___lam__0___boxed), 10, 9);
lean_closure_set(v___f_3438_, 0, v___x_3433_);
lean_closure_set(v___f_3438_, 1, v___x_3429_);
lean_closure_set(v___f_3438_, 2, v___x_3434_);
lean_closure_set(v___f_3438_, 3, v___x_2967_);
lean_closure_set(v___f_3438_, 4, v___x_3435_);
lean_closure_set(v___f_3438_, 5, v_name_2943_);
lean_closure_set(v___f_3438_, 6, v___x_2974_);
lean_closure_set(v___f_3438_, 7, v___x_3436_);
lean_closure_set(v___f_3438_, 8, v___x_3437_);
v___x_3439_ = lean_alloc_closure((void*)(l_Lean_withImporting___boxed), 3, 2);
lean_closure_set(v___x_3439_, 0, lean_box(0));
lean_closure_set(v___x_3439_, 1, v___f_3438_);
v___x_3440_ = lean_box(0);
v___x_3441_ = l_Lean_profileitIOUnsafe___redArg(v___x_3265_, v___x_2974_, v___x_3439_, v___x_3440_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v_a_3442_; lean_object* v___x_3443_; lean_object* v_ext_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_a_3442_);
lean_dec_ref_known(v___x_3441_, 1);
v___x_3443_ = l_Lean_Compiler_CSimp_ext;
v_ext_3444_ = lean_ctor_get(v___x_3443_, 1);
lean_inc(v_name_2943_);
v___x_3445_ = l_Lean_Environment_setMainModule(v_a_3442_, v_name_2943_);
lean_inc_ref(v_ext_3444_);
v___x_3446_ = l_main___elam__0___redArg(v___x_3440_, v___x_2961_, v_ext_3444_, v___x_3445_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v_a_3447_; lean_object* v___x_3448_; lean_object* v_ext_3449_; lean_object* v___x_3450_; 
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_a_3447_);
lean_dec_ref_known(v___x_3446_, 1);
v___x_3448_ = l_Lean_Meta_instanceExtension;
v_ext_3449_ = lean_ctor_get(v___x_3448_, 1);
lean_inc_ref(v_ext_3449_);
v___x_3450_ = l_main___elam__0___redArg(v___x_3440_, v___x_2961_, v_ext_3449_, v_a_3447_);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_object* v_a_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v_a_3451_ = lean_ctor_get(v___x_3450_, 0);
lean_inc(v_a_3451_);
lean_dec_ref_known(v___x_3450_, 1);
v___x_3452_ = l_Lean_classExtension;
v___x_3453_ = l_main___elam__0___redArg(v___x_3440_, v___x_2962_, v___x_3452_, v_a_3451_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref_known(v___x_3453_, 1);
v___x_3455_ = l_Lean_Meta_Match_Extension_extension;
v___x_3456_ = l_main___elam__0___redArg(v___x_3440_, v___x_2963_, v___x_3455_, v_a_3454_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3485_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3459_ = v___x_3456_;
v_isShared_3460_ = v_isSharedCheck_3485_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3456_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3485_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3461_; 
v___x_3461_ = l_Lean_Environment_getModuleIdx_x3f(v_a_3457_, v_name_2943_);
if (lean_obj_tag(v___x_3461_) == 1)
{
lean_object* v_val_3462_; lean_object* v___x_3463_; uint8_t v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; uint8_t v___x_3468_; 
lean_del_object(v___x_3459_);
v_val_3462_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_val_3462_);
lean_dec_ref_known(v___x_3461_, 1);
v___x_3463_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_3464_ = 0;
v___x_3465_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2964_, v___x_3463_, v_a_3457_, v_val_3462_, v___x_3464_);
v___x_3466_ = lean_array_get_size(v___x_3465_);
v___x_3467_ = ((lean_object*)(l_main___closed__33));
v___x_3468_ = lean_nat_dec_lt(v___x_2973_, v___x_3466_);
if (v___x_3468_ == 0)
{
lean_dec_ref(v___x_3465_);
v___y_3413_ = v___x_3440_;
v___y_3414_ = v_val_3462_;
v___y_3415_ = v___x_3440_;
v___y_3416_ = v___x_3464_;
v___y_3417_ = v_a_3457_;
v___y_3418_ = v___x_3467_;
goto v___jp_3412_;
}
else
{
uint8_t v___x_3469_; 
v___x_3469_ = lean_nat_dec_le(v___x_3466_, v___x_3466_);
if (v___x_3469_ == 0)
{
if (v___x_3468_ == 0)
{
lean_dec_ref(v___x_3465_);
v___y_3413_ = v___x_3440_;
v___y_3414_ = v_val_3462_;
v___y_3415_ = v___x_3440_;
v___y_3416_ = v___x_3464_;
v___y_3417_ = v_a_3457_;
v___y_3418_ = v___x_3467_;
goto v___jp_3412_;
}
else
{
size_t v___x_3470_; size_t v___x_3471_; lean_object* v___x_3472_; 
v___x_3470_ = ((size_t)0ULL);
v___x_3471_ = lean_usize_of_nat(v___x_3466_);
lean_inc(v_a_3457_);
v___x_3472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3457_, v___x_3465_, v___x_3470_, v___x_3471_, v___x_3467_);
lean_dec_ref(v___x_3465_);
v___y_3413_ = v___x_3440_;
v___y_3414_ = v_val_3462_;
v___y_3415_ = v___x_3440_;
v___y_3416_ = v___x_3464_;
v___y_3417_ = v_a_3457_;
v___y_3418_ = v___x_3472_;
goto v___jp_3412_;
}
}
else
{
size_t v___x_3473_; size_t v___x_3474_; lean_object* v___x_3475_; 
v___x_3473_ = ((size_t)0ULL);
v___x_3474_ = lean_usize_of_nat(v___x_3466_);
lean_inc(v_a_3457_);
v___x_3475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3457_, v___x_3465_, v___x_3473_, v___x_3474_, v___x_3467_);
lean_dec_ref(v___x_3465_);
v___y_3413_ = v___x_3440_;
v___y_3414_ = v_val_3462_;
v___y_3415_ = v___x_3440_;
v___y_3416_ = v___x_3464_;
v___y_3417_ = v_a_3457_;
v___y_3418_ = v___x_3475_;
goto v___jp_3412_;
}
}
}
else
{
lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3483_; 
lean_dec(v___x_3461_);
lean_dec(v_a_3457_);
lean_dec_ref(v___x_2974_);
lean_del_object(v___x_2959_);
lean_dec(v_fst_2956_);
lean_dec(v_head_2936_);
lean_dec(v_head_2935_);
v___x_3476_ = ((lean_object*)(l_main___closed__34));
v___x_3477_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2943_, v___x_2970_);
v___x_3478_ = lean_string_append(v___x_3476_, v___x_3477_);
lean_dec_ref(v___x_3477_);
v___x_3479_ = ((lean_object*)(l_main___closed__35));
v___x_3480_ = lean_string_append(v___x_3478_, v___x_3479_);
v___x_3481_ = lean_mk_io_user_error(v___x_3480_);
if (v_isShared_3460_ == 0)
{
lean_ctor_set_tag(v___x_3459_, 1);
lean_ctor_set(v___x_3459_, 0, v___x_3481_);
v___x_3483_ = v___x_3459_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v___x_3481_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
}
}
else
{
lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3493_; 
lean_dec_ref(v___x_2974_);
lean_del_object(v___x_2959_);
lean_dec(v_fst_2956_);
lean_dec(v_name_2943_);
lean_dec(v_head_2936_);
lean_dec(v_head_2935_);
v_a_3486_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3488_ = v___x_3456_;
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___x_3456_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3491_; 
if (v_isShared_3489_ == 0)
{
v___x_3491_ = v___x_3488_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_a_3486_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
}
else
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3501_; 
lean_dec_ref(v___x_2974_);
lean_del_object(v___x_2959_);
lean_dec(v_fst_2956_);
lean_dec(v_name_2943_);
lean_dec(v_head_2936_);
lean_dec(v_head_2935_);
v_a_3494_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3496_ = v___x_3453_;
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3453_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3499_; 
if (v_isShared_3497_ == 0)
{
v___x_3499_ = v___x_3496_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_a_3494_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
else
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3509_; 
lean_dec_ref(v___x_2974_);
lean_del_object(v___x_2959_);
lean_dec(v_fst_2956_);
lean_dec(v_name_2943_);
lean_dec(v_head_2936_);
lean_dec(v_head_2935_);
v_a_3502_ = lean_ctor_get(v___x_3450_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3504_ = v___x_3450_;
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3450_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3507_; 
if (v_isShared_3505_ == 0)
{
v___x_3507_ = v___x_3504_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_a_3502_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
else
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3517_; 
lean_dec_ref(v___x_2974_);
lean_del_object(v___x_2959_);
lean_dec(v_fst_2956_);
lean_dec(v_name_2943_);
lean_dec(v_head_2936_);
lean_dec(v_head_2935_);
v_a_3510_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3446_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3446_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3515_; 
if (v_isShared_3513_ == 0)
{
v___x_3515_ = v___x_3512_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
lean_dec_ref(v___x_2974_);
lean_del_object(v___x_2959_);
lean_dec(v_fst_2956_);
lean_dec(v_name_2943_);
lean_dec(v_head_2936_);
lean_dec(v_head_2935_);
v_a_3518_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3441_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3441_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
}
}
else
{
lean_object* v_a_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3535_; 
lean_dec(v_a_2951_);
lean_dec(v_name_2943_);
lean_dec(v_head_2936_);
lean_dec(v_head_2935_);
v_a_3528_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3530_ = v___x_2955_;
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_a_3528_);
lean_dec(v___x_2955_);
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
else
{
lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3543_; 
lean_dec(v_a_2951_);
lean_dec(v_name_2943_);
lean_dec(v_head_2936_);
lean_dec(v_head_2935_);
v_a_3536_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3538_ = v___x_2952_;
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___x_2952_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3541_; 
if (v_isShared_3539_ == 0)
{
v___x_3541_ = v___x_3538_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3536_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
}
else
{
lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3551_; 
lean_dec(v_name_2943_);
lean_dec(v_head_2936_);
lean_dec(v_head_2935_);
v_a_3544_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3546_ = v___x_2950_;
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_2950_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3549_; 
if (v_isShared_3547_ == 0)
{
v___x_3549_ = v___x_3546_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_a_3544_);
v___x_3549_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
return v___x_3549_;
}
}
}
}
}
else
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
lean_del_object(v___x_2939_);
lean_dec(v_tail_2937_);
lean_dec(v_head_2936_);
lean_dec(v_head_2935_);
v_a_3553_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___x_2941_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_2941_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
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
}
else
{
lean_dec(v_tail_2933_);
lean_dec_ref_known(v_tail_2932_, 2);
lean_dec_ref_known(v_args_2907_, 2);
goto v___jp_2909_;
}
}
else
{
lean_dec_ref_known(v_args_2907_, 2);
lean_dec(v_tail_2932_);
goto v___jp_2909_;
}
}
else
{
lean_dec(v_args_2907_);
goto v___jp_2909_;
}
v___jp_2909_:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2910_ = ((lean_object*)(l_main___closed__0));
v___x_2911_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_2910_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2919_; 
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2919_ == 0)
{
lean_object* v_unused_2920_; 
v_unused_2920_ = lean_ctor_get(v___x_2911_, 0);
lean_dec(v_unused_2920_);
v___x_2913_ = v___x_2911_;
v_isShared_2914_ = v_isSharedCheck_2919_;
goto v_resetjp_2912_;
}
else
{
lean_dec(v___x_2911_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2919_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2915_; lean_object* v___x_2917_; 
v___x_2915_ = l_main___boxed__const__1;
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 0, v___x_2915_);
v___x_2917_ = v___x_2913_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2915_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
v_a_2921_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2911_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2911_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
v___jp_2929_:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2930_ = l_main___boxed__const__2;
v___x_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2930_);
return v___x_2931_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_3562_, lean_object* v_a_3563_){
_start:
{
lean_object* v_res_3564_; 
v_res_3564_ = _lean_main(v_args_3562_);
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object* v_as_3565_, lean_object* v_as_x27_3566_, lean_object* v_b_3567_, lean_object* v_a_3568_){
_start:
{
lean_object* v___x_3570_; 
v___x_3570_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_3566_, v_b_3567_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object* v_as_3571_, lean_object* v_as_x27_3572_, lean_object* v_b_3573_, lean_object* v_a_3574_, lean_object* v___y_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l_List_forIn_x27_loop___at___00main_spec__1(v_as_3571_, v_as_x27_3572_, v_b_3573_, v_a_3574_);
lean_dec(v_as_x27_3572_);
lean_dec(v_as_3571_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(lean_object* v___y_3577_, lean_object* v___y_3578_){
_start:
{
lean_object* v___x_3580_; 
v___x_3580_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_3578_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___boxed(lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_){
_start:
{
lean_object* v_res_3584_; 
v_res_3584_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(v___y_3581_, v___y_3582_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
return v_res_3584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(lean_object* v_00_u03b2_3585_, lean_object* v_m_3586_, lean_object* v_a_3587_, lean_object* v_fallback_3588_){
_start:
{
lean_object* v___x_3589_; 
v___x_3589_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_3586_, v_a_3587_, v_fallback_3588_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___boxed(lean_object* v_00_u03b2_3590_, lean_object* v_m_3591_, lean_object* v_a_3592_, lean_object* v_fallback_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(v_00_u03b2_3590_, v_m_3591_, v_a_3592_, v_fallback_3593_);
lean_dec(v_fallback_3593_);
lean_dec_ref(v_a_3592_);
lean_dec_ref(v_m_3591_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18(lean_object* v_00_u03b2_3595_, lean_object* v_m_3596_, lean_object* v_a_3597_, lean_object* v_b_3598_){
_start:
{
lean_object* v___x_3599_; 
v___x_3599_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_m_3596_, v_a_3597_, v_b_3598_);
return v___x_3599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(lean_object* v_n_3600_, lean_object* v_as_3601_, lean_object* v_lo_3602_, lean_object* v_hi_3603_, lean_object* v_w_3604_, lean_object* v_hlo_3605_, lean_object* v_hhi_3606_){
_start:
{
lean_object* v___x_3607_; 
v___x_3607_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_3600_, v_as_3601_, v_lo_3602_, v_hi_3603_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___boxed(lean_object* v_n_3608_, lean_object* v_as_3609_, lean_object* v_lo_3610_, lean_object* v_hi_3611_, lean_object* v_w_3612_, lean_object* v_hlo_3613_, lean_object* v_hhi_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(v_n_3608_, v_as_3609_, v_lo_3610_, v_hi_3611_, v_w_3612_, v_hlo_3613_, v_hhi_3614_);
lean_dec(v_hi_3611_);
lean_dec(v_n_3608_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(lean_object* v_00_u03b2_3616_, lean_object* v_a_3617_, lean_object* v_fallback_3618_, lean_object* v_x_3619_){
_start:
{
lean_object* v___x_3620_; 
v___x_3620_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_3617_, v_fallback_3618_, v_x_3619_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3621_, lean_object* v_a_3622_, lean_object* v_fallback_3623_, lean_object* v_x_3624_){
_start:
{
lean_object* v_res_3625_; 
v_res_3625_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(v_00_u03b2_3621_, v_a_3622_, v_fallback_3623_, v_x_3624_);
lean_dec(v_x_3624_);
lean_dec(v_fallback_3623_);
lean_dec_ref(v_a_3622_);
return v_res_3625_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(lean_object* v_00_u03b2_3626_, lean_object* v_a_3627_, lean_object* v_x_3628_){
_start:
{
uint8_t v___x_3629_; 
v___x_3629_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_3627_, v_x_3628_);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___boxed(lean_object* v_00_u03b2_3630_, lean_object* v_a_3631_, lean_object* v_x_3632_){
_start:
{
uint8_t v_res_3633_; lean_object* v_r_3634_; 
v_res_3633_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(v_00_u03b2_3630_, v_a_3631_, v_x_3632_);
lean_dec(v_x_3632_);
lean_dec_ref(v_a_3631_);
v_r_3634_ = lean_box(v_res_3633_);
return v_r_3634_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24(lean_object* v_00_u03b2_3635_, lean_object* v_data_3636_){
_start:
{
lean_object* v___x_3637_; 
v___x_3637_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_data_3636_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25(lean_object* v_00_u03b2_3638_, lean_object* v_a_3639_, lean_object* v_b_3640_, lean_object* v_x_3641_){
_start:
{
lean_object* v___x_3642_; 
v___x_3642_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_3639_, v_b_3640_, v_x_3641_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(lean_object* v_n_3643_, lean_object* v_lo_3644_, lean_object* v_hi_3645_, lean_object* v_hhi_3646_, lean_object* v_pivot_3647_, lean_object* v_as_3648_, lean_object* v_i_3649_, lean_object* v_k_3650_, lean_object* v_ilo_3651_, lean_object* v_ik_3652_, lean_object* v_w_3653_){
_start:
{
lean_object* v___x_3654_; 
v___x_3654_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_3645_, v_pivot_3647_, v_as_3648_, v_i_3649_, v_k_3650_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___boxed(lean_object* v_n_3655_, lean_object* v_lo_3656_, lean_object* v_hi_3657_, lean_object* v_hhi_3658_, lean_object* v_pivot_3659_, lean_object* v_as_3660_, lean_object* v_i_3661_, lean_object* v_k_3662_, lean_object* v_ilo_3663_, lean_object* v_ik_3664_, lean_object* v_w_3665_){
_start:
{
lean_object* v_res_3666_; 
v_res_3666_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(v_n_3655_, v_lo_3656_, v_hi_3657_, v_hhi_3658_, v_pivot_3659_, v_as_3660_, v_i_3661_, v_k_3662_, v_ilo_3663_, v_ik_3664_, v_w_3665_);
lean_dec_ref(v_pivot_3659_);
lean_dec(v_hi_3657_);
lean_dec(v_lo_3656_);
lean_dec(v_n_3655_);
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(lean_object* v_as_3667_, size_t v_sz_3668_, size_t v_i_3669_, lean_object* v_b_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
lean_object* v___x_3674_; 
v___x_3674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_3667_, v_sz_3668_, v_i_3669_, v_b_3670_, v___y_3671_);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___boxed(lean_object* v_as_3675_, lean_object* v_sz_3676_, lean_object* v_i_3677_, lean_object* v_b_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
size_t v_sz_boxed_3682_; size_t v_i_boxed_3683_; lean_object* v_res_3684_; 
v_sz_boxed_3682_ = lean_unbox_usize(v_sz_3676_);
lean_dec(v_sz_3676_);
v_i_boxed_3683_ = lean_unbox_usize(v_i_3677_);
lean_dec(v_i_3677_);
v_res_3684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(v_as_3675_, v_sz_boxed_3682_, v_i_boxed_3683_, v_b_3678_, v___y_3679_, v___y_3680_);
lean_dec(v___y_3680_);
lean_dec_ref(v___y_3679_);
lean_dec_ref(v_as_3675_);
return v_res_3684_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35(lean_object* v_00_u03b2_3685_, lean_object* v_i_3686_, lean_object* v_source_3687_, lean_object* v_target_3688_){
_start:
{
lean_object* v___x_3689_; 
v___x_3689_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v_i_3686_, v_source_3687_, v_target_3688_);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(uint8_t v___x_3690_, lean_object* v_as_3691_, size_t v_sz_3692_, size_t v_i_3693_, lean_object* v_b_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
lean_object* v___x_3698_; 
v___x_3698_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_3690_, v_as_3691_, v_sz_3692_, v_i_3693_, v_b_3694_, v___y_3695_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___boxed(lean_object* v___x_3699_, lean_object* v_as_3700_, lean_object* v_sz_3701_, lean_object* v_i_3702_, lean_object* v_b_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
uint8_t v___x_41291__boxed_3707_; size_t v_sz_boxed_3708_; size_t v_i_boxed_3709_; lean_object* v_res_3710_; 
v___x_41291__boxed_3707_ = lean_unbox(v___x_3699_);
v_sz_boxed_3708_ = lean_unbox_usize(v_sz_3701_);
lean_dec(v_sz_3701_);
v_i_boxed_3709_ = lean_unbox_usize(v_i_3702_);
lean_dec(v_i_3702_);
v_res_3710_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(v___x_41291__boxed_3707_, v_as_3700_, v_sz_boxed_3708_, v_i_boxed_3709_, v_b_3703_, v___y_3704_, v___y_3705_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec_ref(v_as_3700_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(lean_object* v_as_3711_, size_t v_sz_3712_, size_t v_i_3713_, lean_object* v_b_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
lean_object* v___x_3718_; 
v___x_3718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_3711_, v_sz_3712_, v_i_3713_, v_b_3714_, v___y_3715_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___boxed(lean_object* v_as_3719_, lean_object* v_sz_3720_, lean_object* v_i_3721_, lean_object* v_b_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_){
_start:
{
size_t v_sz_boxed_3726_; size_t v_i_boxed_3727_; lean_object* v_res_3728_; 
v_sz_boxed_3726_ = lean_unbox_usize(v_sz_3720_);
lean_dec(v_sz_3720_);
v_i_boxed_3727_ = lean_unbox_usize(v_i_3721_);
lean_dec(v_i_3721_);
v_res_3728_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(v_as_3719_, v_sz_boxed_3726_, v_i_boxed_3727_, v_b_3722_, v___y_3723_, v___y_3724_);
lean_dec(v___y_3724_);
lean_dec_ref(v___y_3723_);
lean_dec_ref(v_as_3719_);
return v_res_3728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44(lean_object* v_00_u03b2_3729_, lean_object* v_x_3730_, lean_object* v_x_3731_){
_start:
{
lean_object* v___x_3732_; 
v___x_3732_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_x_3730_, v_x_3731_);
return v___x_3732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(uint8_t v___x_3733_, lean_object* v_as_3734_, size_t v_sz_3735_, size_t v_i_3736_, lean_object* v_b_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v___x_3741_; 
v___x_3741_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_3733_, v_as_3734_, v_sz_3735_, v_i_3736_, v_b_3737_, v___y_3738_);
return v___x_3741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___boxed(lean_object* v___x_3742_, lean_object* v_as_3743_, lean_object* v_sz_3744_, lean_object* v_i_3745_, lean_object* v_b_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_){
_start:
{
uint8_t v___x_41322__boxed_3750_; size_t v_sz_boxed_3751_; size_t v_i_boxed_3752_; lean_object* v_res_3753_; 
v___x_41322__boxed_3750_ = lean_unbox(v___x_3742_);
v_sz_boxed_3751_ = lean_unbox_usize(v_sz_3744_);
lean_dec(v_sz_3744_);
v_i_boxed_3752_ = lean_unbox_usize(v_i_3745_);
lean_dec(v_i_3745_);
v_res_3753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(v___x_41322__boxed_3750_, v_as_3743_, v_sz_boxed_3751_, v_i_boxed_3752_, v_b_3746_, v___y_3747_, v___y_3748_);
lean_dec(v___y_3748_);
lean_dec_ref(v___y_3747_);
lean_dec_ref(v_as_3743_);
return v_res_3753_;
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
