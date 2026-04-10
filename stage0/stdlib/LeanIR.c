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
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
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
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
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
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
double lean_float_of_nat(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_getAndEmptyMessageLog___redArg(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__39___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__39___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__39___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__39___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__39___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37_spec__50___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37_spec__50___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37_spec__50___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37_spec__50___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37_spec__50___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__36(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__43___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__43___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__43(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__43___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__39(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__39___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37_spec__50(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37_spec__50___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_304_; lean_object* v___x_20094__overap_305_; lean_object* v___x_306_; 
v___x_304_ = lean_obj_once(&l_panic___at___00main_spec__5___closed__0, &l_panic___at___00main_spec__5___closed__0_once, _init_l_panic___at___00main_spec__5___closed__0);
v___x_20094__overap_305_ = lean_panic_fn_borrowed(v___x_304_, v_msg_302_);
v___x_306_ = lean_apply_1(v___x_20094__overap_305_, lean_box(0));
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
lean_object* v_key_338_; lean_object* v_value_339_; lean_object* v_tail_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_386_; 
v_key_338_ = lean_ctor_get(v_x_337_, 0);
v_value_339_ = lean_ctor_get(v_x_337_, 1);
v_tail_340_ = lean_ctor_get(v_x_337_, 2);
v_isSharedCheck_386_ = !lean_is_exclusive(v_x_337_);
if (v_isSharedCheck_386_ == 0)
{
v___x_342_ = v_x_337_;
v_isShared_343_ = v_isSharedCheck_386_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_tail_340_);
lean_inc(v_value_339_);
lean_inc(v_key_338_);
lean_dec(v_x_337_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_386_;
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
lean_object* v_toEffectiveImport_349_; lean_object* v_toImport_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_385_; 
lean_dec(v_key_338_);
v_toEffectiveImport_349_ = lean_ctor_get(v_value_339_, 0);
lean_inc_ref(v_toEffectiveImport_349_);
v_toImport_350_ = lean_ctor_get(v_toEffectiveImport_349_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v_toEffectiveImport_349_);
if (v_isSharedCheck_385_ == 0)
{
v___x_352_ = v_toEffectiveImport_349_;
v_isShared_353_ = v_isSharedCheck_385_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_toImport_350_);
lean_dec(v_toEffectiveImport_349_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_385_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v_parts_354_; lean_object* v_irData_x3f_355_; uint8_t v_needsData_356_; uint8_t v_needsIRTrans_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_383_; 
v_parts_354_ = lean_ctor_get(v_value_339_, 1);
v_irData_x3f_355_ = lean_ctor_get(v_value_339_, 2);
v_needsData_356_ = lean_ctor_get_uint8(v_value_339_, sizeof(void*)*3);
v_needsIRTrans_357_ = lean_ctor_get_uint8(v_value_339_, sizeof(void*)*3 + 1);
v_isSharedCheck_383_ = !lean_is_exclusive(v_value_339_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; 
v_unused_384_ = lean_ctor_get(v_value_339_, 0);
lean_dec(v_unused_384_);
v___x_359_ = v_value_339_;
v_isShared_360_ = v_isSharedCheck_383_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_irData_x3f_355_);
lean_inc(v_parts_354_);
lean_dec(v_value_339_);
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
if (v_isShared_353_ == 0)
{
v___x_365_ = v___x_352_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_toImport_350_);
v___x_365_ = v_reuseFailAlloc_372_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_367_; 
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*1, v___x_363_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_365_);
v___x_367_ = v___x_359_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_365_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_parts_354_);
lean_ctor_set(v_reuseFailAlloc_371_, 2, v_irData_x3f_355_);
lean_ctor_set_uint8(v_reuseFailAlloc_371_, sizeof(void*)*3, v_needsData_356_);
lean_ctor_set_uint8(v_reuseFailAlloc_371_, sizeof(void*)*3 + 1, v_needsIRTrans_357_);
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
if (v_isShared_353_ == 0)
{
v___x_375_ = v___x_352_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_toImport_350_);
v___x_375_ = v_reuseFailAlloc_382_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_377_; 
lean_ctor_set_uint8(v___x_375_, sizeof(void*)*1, v___x_373_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_375_);
v___x_377_ = v___x_359_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_parts_354_);
lean_ctor_set(v_reuseFailAlloc_381_, 2, v_irData_x3f_355_);
lean_ctor_set_uint8(v_reuseFailAlloc_381_, sizeof(void*)*3, v_needsData_356_);
lean_ctor_set_uint8(v_reuseFailAlloc_381_, sizeof(void*)*3 + 1, v_needsIRTrans_357_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5___boxed(lean_object* v___x_387_, lean_object* v_a_388_, lean_object* v_x_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v___x_387_, v_a_388_, v_x_389_);
lean_dec(v___x_387_);
return v_res_390_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0(void){
_start:
{
lean_object* v___x_391_; uint64_t v___x_392_; 
v___x_391_ = lean_unsigned_to_nat(1723u);
v___x_392_ = lean_uint64_of_nat(v___x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(lean_object* v___x_393_, lean_object* v_m_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_size_396_; lean_object* v_buckets_397_; lean_object* v___x_398_; uint64_t v___y_400_; 
v_size_396_ = lean_ctor_get(v_m_394_, 0);
v_buckets_397_ = lean_ctor_get(v_m_394_, 1);
v___x_398_ = lean_array_get_size(v_buckets_397_);
if (lean_obj_tag(v_a_395_) == 0)
{
uint64_t v___x_427_; 
v___x_427_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0);
v___y_400_ = v___x_427_;
goto v___jp_399_;
}
else
{
uint64_t v_hash_428_; 
v_hash_428_ = lean_ctor_get_uint64(v_a_395_, sizeof(void*)*2);
v___y_400_ = v_hash_428_;
goto v___jp_399_;
}
v___jp_399_:
{
uint64_t v___x_401_; uint64_t v___x_402_; uint64_t v_fold_403_; uint64_t v___x_404_; uint64_t v___x_405_; uint64_t v___x_406_; size_t v___x_407_; size_t v___x_408_; size_t v___x_409_; size_t v___x_410_; size_t v___x_411_; lean_object* v_bucket_412_; uint8_t v___x_413_; 
v___x_401_ = 32ULL;
v___x_402_ = lean_uint64_shift_right(v___y_400_, v___x_401_);
v_fold_403_ = lean_uint64_xor(v___y_400_, v___x_402_);
v___x_404_ = 16ULL;
v___x_405_ = lean_uint64_shift_right(v_fold_403_, v___x_404_);
v___x_406_ = lean_uint64_xor(v_fold_403_, v___x_405_);
v___x_407_ = lean_uint64_to_usize(v___x_406_);
v___x_408_ = lean_usize_of_nat(v___x_398_);
v___x_409_ = ((size_t)1ULL);
v___x_410_ = lean_usize_sub(v___x_408_, v___x_409_);
v___x_411_ = lean_usize_land(v___x_407_, v___x_410_);
v_bucket_412_ = lean_array_uget_borrowed(v_buckets_397_, v___x_411_);
v___x_413_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_a_395_, v_bucket_412_);
if (v___x_413_ == 0)
{
lean_dec(v_a_395_);
return v_m_394_;
}
else
{
lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_424_; 
lean_inc(v_bucket_412_);
lean_inc_ref(v_buckets_397_);
lean_inc(v_size_396_);
v_isSharedCheck_424_ = !lean_is_exclusive(v_m_394_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; lean_object* v_unused_426_; 
v_unused_425_ = lean_ctor_get(v_m_394_, 1);
lean_dec(v_unused_425_);
v_unused_426_ = lean_ctor_get(v_m_394_, 0);
lean_dec(v_unused_426_);
v___x_415_ = v_m_394_;
v_isShared_416_ = v_isSharedCheck_424_;
goto v_resetjp_414_;
}
else
{
lean_dec(v_m_394_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_424_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; lean_object* v_buckets_418_; lean_object* v_bucket_419_; lean_object* v___x_420_; lean_object* v___x_422_; 
v___x_417_ = lean_box(0);
v_buckets_418_ = lean_array_uset(v_buckets_397_, v___x_411_, v___x_417_);
v_bucket_419_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v___x_393_, v_a_395_, v_bucket_412_);
v___x_420_ = lean_array_uset(v_buckets_418_, v___x_411_, v_bucket_419_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 1, v___x_420_);
v___x_422_ = v___x_415_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_size_396_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v___x_420_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___boxed(lean_object* v___x_429_, lean_object* v_m_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(v___x_429_, v_m_430_, v_a_431_);
lean_dec(v___x_429_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_main___lam__0(lean_object* v___x_433_, lean_object* v___x_434_, uint8_t v___x_435_, lean_object* v___x_436_, uint8_t v___y_437_, lean_object* v_name_438_, lean_object* v___x_439_, uint8_t v___x_440_, uint8_t v___x_441_){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = lean_st_mk_ref(v___x_433_);
v___x_444_ = l_Lean_importModulesCore(v___x_434_, v___x_435_, v___x_436_, v___y_437_, v___x_443_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v___x_445_; lean_object* v_moduleNameMap_446_; lean_object* v_moduleNames_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_460_; 
lean_dec_ref(v___x_444_);
v___x_445_ = lean_st_ref_get(v___x_443_);
lean_dec(v___x_443_);
v_moduleNameMap_446_ = lean_ctor_get(v___x_445_, 0);
v_moduleNames_447_ = lean_ctor_get(v___x_445_, 1);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_460_ == 0)
{
v___x_449_ = v___x_445_;
v_isShared_450_ = v_isSharedCheck_460_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_moduleNames_447_);
lean_inc(v_moduleNameMap_446_);
lean_dec(v___x_445_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_460_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v___x_453_; 
lean_inc(v_name_438_);
v___x_451_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(v_name_438_, v_moduleNameMap_446_, v_name_438_);
lean_dec(v_name_438_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_451_);
v___x_453_ = v___x_449_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_451_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_moduleNames_447_);
v___x_453_ = v_reuseFailAlloc_459_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
uint32_t v___x_454_; uint8_t v___x_455_; uint8_t v___x_456_; 
v___x_454_ = 0;
v___x_455_ = 0;
v___x_456_ = l_Lean_instDecidableEqOLeanLevel(v___x_455_, v___x_435_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_finalizeImport(v___x_453_, v___x_434_, v___x_439_, v___x_454_, v___x_440_, v___x_441_, v___x_455_, v___x_440_);
lean_dec_ref(v___x_453_);
return v___x_457_;
}
else
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_finalizeImport(v___x_453_, v___x_434_, v___x_439_, v___x_454_, v___x_440_, v___x_441_, v___x_455_, v___x_441_);
lean_dec_ref(v___x_453_);
return v___x_458_;
}
}
}
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
lean_dec(v___x_443_);
lean_dec_ref(v___x_439_);
lean_dec(v_name_438_);
lean_dec_ref(v___x_434_);
v_a_461_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_444_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_444_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__0___boxed(lean_object* v___x_469_, lean_object* v___x_470_, lean_object* v___x_471_, lean_object* v___x_472_, lean_object* v___y_473_, lean_object* v_name_474_, lean_object* v___x_475_, lean_object* v___x_476_, lean_object* v___x_477_, lean_object* v___y_478_){
_start:
{
uint8_t v___x_36190__boxed_479_; uint8_t v___y_36192__boxed_480_; uint8_t v___x_36194__boxed_481_; uint8_t v___x_36195__boxed_482_; lean_object* v_res_483_; 
v___x_36190__boxed_479_ = lean_unbox(v___x_471_);
v___y_36192__boxed_480_ = lean_unbox(v___y_473_);
v___x_36194__boxed_481_ = lean_unbox(v___x_476_);
v___x_36195__boxed_482_ = lean_unbox(v___x_477_);
v_res_483_ = l_main___lam__0(v___x_469_, v___x_470_, v___x_36190__boxed_479_, v___x_472_, v___y_36192__boxed_480_, v_name_474_, v___x_475_, v___x_36194__boxed_481_, v___x_36195__boxed_482_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_main___lam__1(lean_object* v___x_485_, lean_object* v___x_486_, lean_object* v___x_487_, lean_object* v_name_488_, lean_object* v_a_489_, lean_object* v___x_490_, lean_object* v_head_491_, lean_object* v___x_492_, lean_object* v___x_493_, lean_object* v___x_494_, lean_object* v___x_495_, lean_object* v___x_496_, lean_object* v___x_497_, lean_object* v___x_498_, lean_object* v___x_499_, uint8_t v___x_500_, uint8_t v___x_501_){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v_env_507_; lean_object* v___x_508_; uint8_t v___x_509_; lean_object* v_fileName_511_; lean_object* v_fileMap_512_; lean_object* v_currRecDepth_513_; lean_object* v_ref_514_; lean_object* v_currNamespace_515_; lean_object* v_openDecls_516_; lean_object* v_initHeartbeats_517_; lean_object* v_maxHeartbeats_518_; lean_object* v_quotContext_519_; lean_object* v_currMacroScope_520_; lean_object* v_cancelTk_x3f_521_; uint8_t v_suppressElabErrors_522_; lean_object* v_inheritedTraceOptions_523_; lean_object* v___y_524_; uint8_t v___y_553_; uint8_t v___x_573_; 
v___x_503_ = lean_io_get_num_heartbeats();
v___x_504_ = lean_st_mk_ref(v___x_485_);
v___x_505_ = lean_st_ref_get(v___x_486_);
v___x_506_ = lean_st_ref_get(v___x_504_);
v_env_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc_ref(v_env_507_);
lean_dec(v___x_506_);
v___x_508_ = l_Lean_diagnostics;
v___x_509_ = l_Lean_Option_get___at___00main_spec__8(v___x_487_, v___x_508_);
v___x_573_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_507_);
lean_dec_ref(v_env_507_);
if (v___x_573_ == 0)
{
if (v___x_509_ == 0)
{
v___y_553_ = v___x_501_;
goto v___jp_552_;
}
else
{
v___y_553_ = v___x_573_;
goto v___jp_552_;
}
}
else
{
v___y_553_ = v___x_509_;
goto v___jp_552_;
}
v___jp_510_:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_525_ = l_Lean_maxRecDepth;
v___x_526_ = l_Lean_Option_get___at___00main_spec__9(v___x_487_, v___x_525_);
v___x_527_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_527_, 0, v_fileName_511_);
lean_ctor_set(v___x_527_, 1, v_fileMap_512_);
lean_ctor_set(v___x_527_, 2, v___x_487_);
lean_ctor_set(v___x_527_, 3, v_currRecDepth_513_);
lean_ctor_set(v___x_527_, 4, v___x_526_);
lean_ctor_set(v___x_527_, 5, v_ref_514_);
lean_ctor_set(v___x_527_, 6, v_currNamespace_515_);
lean_ctor_set(v___x_527_, 7, v_openDecls_516_);
lean_ctor_set(v___x_527_, 8, v_initHeartbeats_517_);
lean_ctor_set(v___x_527_, 9, v_maxHeartbeats_518_);
lean_ctor_set(v___x_527_, 10, v_quotContext_519_);
lean_ctor_set(v___x_527_, 11, v_currMacroScope_520_);
lean_ctor_set(v___x_527_, 12, v_cancelTk_x3f_521_);
lean_ctor_set(v___x_527_, 13, v_inheritedTraceOptions_523_);
lean_ctor_set_uint8(v___x_527_, sizeof(void*)*14, v___x_509_);
lean_ctor_set_uint8(v___x_527_, sizeof(void*)*14 + 1, v_suppressElabErrors_522_);
v___x_528_ = l_Lean_Compiler_LCNF_emitC(v_name_488_, v___x_527_, v___y_524_);
lean_dec(v___y_524_);
lean_dec_ref(v___x_527_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_a_529_);
lean_dec_ref(v___x_528_);
v___x_530_ = lean_st_ref_get(v___x_504_);
lean_dec(v___x_504_);
lean_dec(v___x_530_);
v___x_531_ = lean_string_to_utf8(v_a_529_);
lean_dec(v_a_529_);
v___x_532_ = lean_io_prim_handle_write(v_a_489_, v___x_531_);
lean_dec_ref(v___x_531_);
return v___x_532_;
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_551_; 
lean_dec(v___x_504_);
v_a_533_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_551_ == 0)
{
v___x_535_ = v___x_528_;
v_isShared_536_ = v_isSharedCheck_551_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_528_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_551_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
if (lean_obj_tag(v_a_533_) == 0)
{
lean_object* v_msg_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_541_; 
v_msg_537_ = lean_ctor_get(v_a_533_, 1);
lean_inc_ref(v_msg_537_);
lean_dec_ref(v_a_533_);
v___x_538_ = l_Lean_MessageData_toString(v_msg_537_);
v___x_539_ = lean_mk_io_user_error(v___x_538_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v___x_539_);
v___x_541_ = v___x_535_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_539_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
else
{
lean_object* v_id_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
v_id_543_ = lean_ctor_get(v_a_533_, 0);
lean_inc(v_id_543_);
lean_dec_ref(v_a_533_);
v___x_544_ = ((lean_object*)(l_main___lam__1___closed__0));
v___x_545_ = l_Nat_reprFast(v_id_543_);
v___x_546_ = lean_string_append(v___x_544_, v___x_545_);
lean_dec_ref(v___x_545_);
v___x_547_ = lean_mk_io_user_error(v___x_546_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v___x_547_);
v___x_549_ = v___x_535_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
v___jp_552_:
{
if (v___y_553_ == 0)
{
lean_object* v___x_554_; lean_object* v_env_555_; lean_object* v_nextMacroScope_556_; lean_object* v_ngen_557_; lean_object* v_auxDeclNGen_558_; lean_object* v_traceState_559_; lean_object* v_messages_560_; lean_object* v_infoState_561_; lean_object* v_snapshotTasks_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_571_; 
v___x_554_ = lean_st_ref_take(v___x_504_);
v_env_555_ = lean_ctor_get(v___x_554_, 0);
v_nextMacroScope_556_ = lean_ctor_get(v___x_554_, 1);
v_ngen_557_ = lean_ctor_get(v___x_554_, 2);
v_auxDeclNGen_558_ = lean_ctor_get(v___x_554_, 3);
v_traceState_559_ = lean_ctor_get(v___x_554_, 4);
v_messages_560_ = lean_ctor_get(v___x_554_, 6);
v_infoState_561_ = lean_ctor_get(v___x_554_, 7);
v_snapshotTasks_562_ = lean_ctor_get(v___x_554_, 8);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_571_ == 0)
{
lean_object* v_unused_572_; 
v_unused_572_ = lean_ctor_get(v___x_554_, 5);
lean_dec(v_unused_572_);
v___x_564_ = v___x_554_;
v_isShared_565_ = v_isSharedCheck_571_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_snapshotTasks_562_);
lean_inc(v_infoState_561_);
lean_inc(v_messages_560_);
lean_inc(v_traceState_559_);
lean_inc(v_auxDeclNGen_558_);
lean_inc(v_ngen_557_);
lean_inc(v_nextMacroScope_556_);
lean_inc(v_env_555_);
lean_dec(v___x_554_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_571_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_566_ = l_Lean_Kernel_enableDiag(v_env_555_, v___x_509_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 5, v___x_490_);
lean_ctor_set(v___x_564_, 0, v___x_566_);
v___x_568_ = v___x_564_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_nextMacroScope_556_);
lean_ctor_set(v_reuseFailAlloc_570_, 2, v_ngen_557_);
lean_ctor_set(v_reuseFailAlloc_570_, 3, v_auxDeclNGen_558_);
lean_ctor_set(v_reuseFailAlloc_570_, 4, v_traceState_559_);
lean_ctor_set(v_reuseFailAlloc_570_, 5, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_570_, 6, v_messages_560_);
lean_ctor_set(v_reuseFailAlloc_570_, 7, v_infoState_561_);
lean_ctor_set(v_reuseFailAlloc_570_, 8, v_snapshotTasks_562_);
v___x_568_ = v_reuseFailAlloc_570_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_569_; 
v___x_569_ = lean_st_ref_set(v___x_504_, v___x_568_);
lean_inc(v___x_504_);
lean_inc(v___x_495_);
v_fileName_511_ = v_head_491_;
v_fileMap_512_ = v___x_492_;
v_currRecDepth_513_ = v___x_493_;
v_ref_514_ = v___x_494_;
v_currNamespace_515_ = v___x_495_;
v_openDecls_516_ = v___x_496_;
v_initHeartbeats_517_ = v___x_503_;
v_maxHeartbeats_518_ = v___x_497_;
v_quotContext_519_ = v___x_495_;
v_currMacroScope_520_ = v___x_498_;
v_cancelTk_x3f_521_ = v___x_499_;
v_suppressElabErrors_522_ = v___x_500_;
v_inheritedTraceOptions_523_ = v___x_505_;
v___y_524_ = v___x_504_;
goto v___jp_510_;
}
}
}
else
{
lean_dec_ref(v___x_490_);
lean_inc(v___x_504_);
lean_inc(v___x_495_);
v_fileName_511_ = v_head_491_;
v_fileMap_512_ = v___x_492_;
v_currRecDepth_513_ = v___x_493_;
v_ref_514_ = v___x_494_;
v_currNamespace_515_ = v___x_495_;
v_openDecls_516_ = v___x_496_;
v_initHeartbeats_517_ = v___x_503_;
v_maxHeartbeats_518_ = v___x_497_;
v_quotContext_519_ = v___x_495_;
v_currMacroScope_520_ = v___x_498_;
v_cancelTk_x3f_521_ = v___x_499_;
v_suppressElabErrors_522_ = v___x_500_;
v_inheritedTraceOptions_523_ = v___x_505_;
v___y_524_ = v___x_504_;
goto v___jp_510_;
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__1___boxed(lean_object** _args){
lean_object* v___x_574_ = _args[0];
lean_object* v___x_575_ = _args[1];
lean_object* v___x_576_ = _args[2];
lean_object* v_name_577_ = _args[3];
lean_object* v_a_578_ = _args[4];
lean_object* v___x_579_ = _args[5];
lean_object* v_head_580_ = _args[6];
lean_object* v___x_581_ = _args[7];
lean_object* v___x_582_ = _args[8];
lean_object* v___x_583_ = _args[9];
lean_object* v___x_584_ = _args[10];
lean_object* v___x_585_ = _args[11];
lean_object* v___x_586_ = _args[12];
lean_object* v___x_587_ = _args[13];
lean_object* v___x_588_ = _args[14];
lean_object* v___x_589_ = _args[15];
lean_object* v___x_590_ = _args[16];
lean_object* v___y_591_ = _args[17];
_start:
{
uint8_t v___x_36280__boxed_592_; uint8_t v___x_36281__boxed_593_; lean_object* v_res_594_; 
v___x_36280__boxed_592_ = lean_unbox(v___x_589_);
v___x_36281__boxed_593_ = lean_unbox(v___x_590_);
v_res_594_ = l_main___lam__1(v___x_574_, v___x_575_, v___x_576_, v_name_577_, v_a_578_, v___x_579_, v_head_580_, v___x_581_, v___x_582_, v___x_583_, v___x_584_, v___x_585_, v___x_586_, v___x_587_, v___x_588_, v___x_36280__boxed_592_, v___x_36281__boxed_593_);
lean_dec(v_a_578_);
lean_dec(v___x_575_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(lean_object* v_s_595_){
_start:
{
lean_object* v___x_597_; lean_object* v_putStr_598_; lean_object* v___x_599_; 
v___x_597_ = lean_get_stderr();
v_putStr_598_ = lean_ctor_get(v___x_597_, 4);
lean_inc_ref(v_putStr_598_);
lean_dec_ref(v___x_597_);
v___x_599_ = lean_apply_2(v_putStr_598_, v_s_595_, lean_box(0));
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8___boxed(lean_object* v_s_600_, lean_object* v_a_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v_s_600_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6(lean_object* v_s_603_){
_start:
{
uint32_t v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_605_ = 10;
v___x_606_ = lean_string_push(v_s_603_, v___x_605_);
v___x_607_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6___boxed(lean_object* v_s_608_, lean_object* v_a_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_IO_eprintln___at___00main_spec__6(v_s_608_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(lean_object* v_o_614_, lean_object* v_k_615_, lean_object* v_v_616_){
_start:
{
lean_object* v_map_617_; uint8_t v_hasTrace_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_632_; 
v_map_617_ = lean_ctor_get(v_o_614_, 0);
v_hasTrace_618_ = lean_ctor_get_uint8(v_o_614_, sizeof(void*)*1);
v_isSharedCheck_632_ = !lean_is_exclusive(v_o_614_);
if (v_isSharedCheck_632_ == 0)
{
v___x_620_ = v_o_614_;
v_isShared_621_ = v_isSharedCheck_632_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_map_617_);
lean_dec(v_o_614_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_632_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_622_, 0, v_v_616_);
lean_inc(v_k_615_);
v___x_623_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_615_, v___x_622_, v_map_617_);
if (v_hasTrace_618_ == 0)
{
lean_object* v___x_624_; uint8_t v___x_625_; lean_object* v___x_627_; 
v___x_624_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_625_ = l_Lean_Name_isPrefixOf(v___x_624_, v_k_615_);
lean_dec(v_k_615_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_623_);
v___x_627_ = v___x_620_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_623_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_ctor_set_uint8(v___x_627_, sizeof(void*)*1, v___x_625_);
return v___x_627_;
}
}
else
{
lean_object* v___x_630_; 
lean_dec(v_k_615_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_623_);
v___x_630_ = v___x_620_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_623_);
lean_ctor_set_uint8(v_reuseFailAlloc_631_, sizeof(void*)*1, v_hasTrace_618_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00main_spec__3(lean_object* v_opts_633_, lean_object* v_opt_634_, lean_object* v_val_635_){
_start:
{
lean_object* v_name_636_; lean_object* v___x_637_; 
v_name_636_ = lean_ctor_get(v_opt_634_, 0);
lean_inc(v_name_636_);
lean_dec_ref(v_opt_634_);
v___x_637_ = l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(v_opts_633_, v_name_636_, v_val_635_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object* v___y_639_, lean_object* v_as_640_, size_t v_i_641_, size_t v_stop_642_, lean_object* v_b_643_){
_start:
{
lean_object* v___y_645_; uint8_t v___x_649_; 
v___x_649_ = lean_usize_dec_eq(v_i_641_, v_stop_642_);
if (v___x_649_ == 0)
{
lean_object* v_fst_650_; lean_object* v_snd_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___y_655_; 
v_fst_650_ = lean_ctor_get(v_b_643_, 0);
v_snd_651_ = lean_ctor_get(v_b_643_, 1);
v___x_652_ = lean_array_uget_borrowed(v_as_640_, v_i_641_);
v___x_653_ = l_Lean_IR_Decl_name(v___x_652_);
if (lean_obj_tag(v___x_653_) == 1)
{
lean_object* v_pre_668_; lean_object* v_str_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v_pre_668_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_pre_668_);
v_str_669_ = lean_ctor_get(v___x_653_, 1);
lean_inc_ref(v_str_669_);
v___x_670_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___closed__0));
v___x_671_ = lean_string_dec_eq(v_str_669_, v___x_670_);
lean_dec_ref(v_str_669_);
if (v___x_671_ == 0)
{
lean_dec(v_pre_668_);
lean_inc_ref(v___x_653_);
v___y_655_ = v___x_653_;
goto v___jp_654_;
}
else
{
v___y_655_ = v_pre_668_;
goto v___jp_654_;
}
}
else
{
lean_inc(v___x_653_);
v___y_655_ = v___x_653_;
goto v___jp_654_;
}
v___jp_654_:
{
uint8_t v___x_656_; 
lean_inc_ref(v___y_639_);
v___x_656_ = l_Lean_isExtern(v___y_639_, v___y_655_);
if (v___x_656_ == 0)
{
lean_dec(v___x_653_);
v___y_645_ = v_b_643_;
goto v___jp_644_;
}
else
{
lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_665_; 
lean_inc(v_snd_651_);
lean_inc(v_fst_650_);
v_isSharedCheck_665_ = !lean_is_exclusive(v_b_643_);
if (v_isSharedCheck_665_ == 0)
{
lean_object* v_unused_666_; lean_object* v_unused_667_; 
v_unused_666_ = lean_ctor_get(v_b_643_, 1);
lean_dec(v_unused_666_);
v_unused_667_ = lean_ctor_get(v_b_643_, 0);
lean_dec(v_unused_667_);
v___x_658_ = v_b_643_;
v_isShared_659_ = v_isSharedCheck_665_;
goto v_resetjp_657_;
}
else
{
lean_dec(v_b_643_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_665_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
lean_inc_n(v___x_652_, 2);
v___x_660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_652_);
lean_ctor_set(v___x_660_, 1, v_fst_650_);
v___x_661_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_651_, v___x_653_, v___x_652_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 1, v___x_661_);
lean_ctor_set(v___x_658_, 0, v___x_660_);
v___x_663_ = v___x_658_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
v___y_645_ = v___x_663_;
goto v___jp_644_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_639_);
return v_b_643_;
}
v___jp_644_:
{
size_t v___x_646_; size_t v___x_647_; 
v___x_646_ = ((size_t)1ULL);
v___x_647_ = lean_usize_add(v_i_641_, v___x_646_);
v_i_641_ = v___x_647_;
v_b_643_ = v___y_645_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object* v___y_672_, lean_object* v_as_673_, lean_object* v_i_674_, lean_object* v_stop_675_, lean_object* v_b_676_){
_start:
{
size_t v_i_boxed_677_; size_t v_stop_boxed_678_; lean_object* v_res_679_; 
v_i_boxed_677_ = lean_unbox_usize(v_i_674_);
lean_dec(v_i_674_);
v_stop_boxed_678_ = lean_unbox_usize(v_stop_675_);
lean_dec(v_stop_675_);
v_res_679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_672_, v_as_673_, v_i_boxed_677_, v_stop_boxed_678_, v_b_676_);
lean_dec_ref(v_as_673_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg(lean_object* v_as_x27_681_, lean_object* v_b_682_){
_start:
{
if (lean_obj_tag(v_as_x27_681_) == 0)
{
lean_object* v___x_684_; 
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v_b_682_);
return v___x_684_;
}
else
{
lean_object* v_head_685_; lean_object* v_tail_686_; lean_object* v_fst_687_; lean_object* v_snd_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_713_; 
v_head_685_ = lean_ctor_get(v_as_x27_681_, 0);
lean_inc(v_head_685_);
v_tail_686_ = lean_ctor_get(v_as_x27_681_, 1);
lean_inc(v_tail_686_);
lean_dec_ref(v_as_x27_681_);
v_fst_687_ = lean_ctor_get(v_b_682_, 0);
v_snd_688_ = lean_ctor_get(v_b_682_, 1);
v_isSharedCheck_713_ = !lean_is_exclusive(v_b_682_);
if (v_isSharedCheck_713_ == 0)
{
v___x_690_ = v_b_682_;
v_isShared_691_ = v_isSharedCheck_713_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_snd_688_);
lean_inc(v_fst_687_);
lean_dec(v_b_682_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_713_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_692_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0));
v___x_693_ = lean_string_dec_eq(v_head_685_, v___x_692_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; 
v___x_694_ = l___private_LeanIR_0__setConfigOption(v_snd_688_, v_head_685_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_697_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref(v___x_694_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v_a_695_);
v___x_697_ = v___x_690_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_fst_687_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_a_695_);
v___x_697_ = v_reuseFailAlloc_699_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
v_as_x27_681_ = v_tail_686_;
v_b_682_ = v___x_697_;
goto _start;
}
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_del_object(v___x_690_);
lean_dec(v_fst_687_);
lean_dec(v_tail_686_);
v_a_700_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_694_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_694_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
else
{
lean_object* v___x_708_; lean_object* v___x_710_; 
lean_dec(v_fst_687_);
lean_dec(v_head_685_);
v___x_708_ = lean_box(v___x_693_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v___x_708_);
v___x_710_ = v___x_690_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_708_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_snd_688_);
v___x_710_ = v_reuseFailAlloc_712_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
v_as_x27_681_ = v_tail_686_;
v_b_682_ = v___x_710_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(lean_object* v_as_x27_714_, lean_object* v_b_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_714_, v_b_715_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object* v_as_718_, size_t v_i_719_, size_t v_stop_720_, lean_object* v_b_721_){
_start:
{
uint8_t v___x_722_; 
v___x_722_ = lean_usize_dec_eq(v_i_719_, v_stop_720_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; lean_object* v_toEnvExtension_724_; lean_object* v_asyncMode_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; size_t v___x_729_; size_t v___x_730_; 
v___x_723_ = l_Lean_Compiler_LCNF_impureSigExt;
v_toEnvExtension_724_ = lean_ctor_get(v___x_723_, 0);
v_asyncMode_725_ = lean_ctor_get(v_toEnvExtension_724_, 2);
v___x_726_ = lean_box(0);
v___x_727_ = lean_array_uget_borrowed(v_as_718_, v_i_719_);
lean_inc(v___x_727_);
v___x_728_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_723_, v_b_721_, v___x_727_, v_asyncMode_725_, v___x_726_);
v___x_729_ = ((size_t)1ULL);
v___x_730_ = lean_usize_add(v_i_719_, v___x_729_);
v_i_719_ = v___x_730_;
v_b_721_ = v___x_728_;
goto _start;
}
else
{
return v_b_721_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object* v_as_732_, lean_object* v_i_733_, lean_object* v_stop_734_, lean_object* v_b_735_){
_start:
{
size_t v_i_boxed_736_; size_t v_stop_boxed_737_; lean_object* v_res_738_; 
v_i_boxed_736_ = lean_unbox_usize(v_i_733_);
lean_dec(v_i_733_);
v_stop_boxed_737_ = lean_unbox_usize(v_stop_734_);
lean_dec(v_stop_734_);
v_res_738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_as_732_, v_i_boxed_736_, v_stop_boxed_737_, v_b_735_);
lean_dec_ref(v_as_732_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__39___redArg(lean_object* v_as_742_, size_t v_sz_743_, size_t v_i_744_, lean_object* v_b_745_, lean_object* v___y_746_){
_start:
{
uint8_t v___x_748_; 
v___x_748_ = lean_usize_dec_lt(v_i_744_, v_sz_743_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; 
v___x_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_749_, 0, v_b_745_);
return v___x_749_;
}
else
{
uint8_t v___x_750_; lean_object* v_a_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
lean_dec_ref(v_b_745_);
v___x_750_ = 0;
v_a_751_ = lean_array_uget_borrowed(v_as_742_, v_i_744_);
lean_inc(v_a_751_);
v___x_752_ = l_Lean_Message_toString(v_a_751_, v___x_750_);
v___x_753_ = l_IO_eprintln___at___00main_spec__6(v___x_752_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v___x_754_; size_t v___x_755_; size_t v___x_756_; 
lean_dec_ref(v___x_753_);
v___x_754_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__39___redArg___closed__0));
v___x_755_ = ((size_t)1ULL);
v___x_756_ = lean_usize_add(v_i_744_, v___x_755_);
v_i_744_ = v___x_756_;
v_b_745_ = v___x_754_;
goto _start;
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_770_; 
v_a_758_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_770_ == 0)
{
v___x_760_ = v___x_753_;
v_isShared_761_ = v_isSharedCheck_770_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_753_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_770_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v_ref_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_768_; 
v_ref_762_ = lean_ctor_get(v___y_746_, 5);
v___x_763_ = lean_io_error_to_string(v_a_758_);
v___x_764_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
v___x_765_ = l_Lean_MessageData_ofFormat(v___x_764_);
lean_inc(v_ref_762_);
v___x_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_766_, 0, v_ref_762_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 0, v___x_766_);
v___x_768_ = v___x_760_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__39___redArg___boxed(lean_object* v_as_771_, lean_object* v_sz_772_, lean_object* v_i_773_, lean_object* v_b_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
size_t v_sz_boxed_777_; size_t v_i_boxed_778_; lean_object* v_res_779_; 
v_sz_boxed_777_ = lean_unbox_usize(v_sz_772_);
lean_dec(v_sz_772_);
v_i_boxed_778_ = lean_unbox_usize(v_i_773_);
lean_dec(v_i_773_);
v_res_779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__39___redArg(v_as_771_, v_sz_boxed_777_, v_i_boxed_778_, v_b_774_, v___y_775_);
lean_dec_ref(v___y_775_);
lean_dec_ref(v_as_771_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(lean_object* v_as_780_, size_t v_sz_781_, size_t v_i_782_, lean_object* v_b_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
uint8_t v___x_787_; 
v___x_787_ = lean_usize_dec_lt(v_i_782_, v_sz_781_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; 
v___x_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_788_, 0, v_b_783_);
return v___x_788_;
}
else
{
uint8_t v___x_789_; lean_object* v_a_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
lean_dec_ref(v_b_783_);
v___x_789_ = 0;
v_a_790_ = lean_array_uget_borrowed(v_as_780_, v_i_782_);
lean_inc(v_a_790_);
v___x_791_ = l_Lean_Message_toString(v_a_790_, v___x_789_);
v___x_792_ = l_IO_eprintln___at___00main_spec__6(v___x_791_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v___x_793_; size_t v___x_794_; size_t v___x_795_; lean_object* v___x_796_; 
lean_dec_ref(v___x_792_);
v___x_793_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__39___redArg___closed__0));
v___x_794_ = ((size_t)1ULL);
v___x_795_ = lean_usize_add(v_i_782_, v___x_794_);
v___x_796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__39___redArg(v_as_780_, v_sz_781_, v___x_795_, v___x_793_, v___y_784_);
return v___x_796_;
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_809_; 
v_a_797_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_809_ == 0)
{
v___x_799_ = v___x_792_;
v_isShared_800_ = v_isSharedCheck_809_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_792_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_809_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v_ref_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_807_; 
v_ref_801_ = lean_ctor_get(v___y_784_, 5);
v___x_802_ = lean_io_error_to_string(v_a_797_);
v___x_803_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
v___x_804_ = l_Lean_MessageData_ofFormat(v___x_803_);
lean_inc(v_ref_801_);
v___x_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_805_, 0, v_ref_801_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_805_);
v___x_807_ = v___x_799_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27___boxed(lean_object* v_as_810_, lean_object* v_sz_811_, lean_object* v_i_812_, lean_object* v_b_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
size_t v_sz_boxed_817_; size_t v_i_boxed_818_; lean_object* v_res_819_; 
v_sz_boxed_817_ = lean_unbox_usize(v_sz_811_);
lean_dec(v_sz_811_);
v_i_boxed_818_ = lean_unbox_usize(v_i_812_);
lean_dec(v_i_812_);
v_res_819_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(v_as_810_, v_sz_boxed_817_, v_i_boxed_818_, v_b_813_, v___y_814_, v___y_815_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec_ref(v_as_810_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37_spec__50___redArg(lean_object* v_as_823_, size_t v_sz_824_, size_t v_i_825_, lean_object* v_b_826_, lean_object* v___y_827_){
_start:
{
uint8_t v___x_829_; 
v___x_829_ = lean_usize_dec_lt(v_i_825_, v_sz_824_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; 
v___x_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_830_, 0, v_b_826_);
return v___x_830_;
}
else
{
uint8_t v___x_831_; lean_object* v_a_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
lean_dec_ref(v_b_826_);
v___x_831_ = 0;
v_a_832_ = lean_array_uget_borrowed(v_as_823_, v_i_825_);
lean_inc(v_a_832_);
v___x_833_ = l_Lean_Message_toString(v_a_832_, v___x_831_);
v___x_834_ = l_IO_eprintln___at___00main_spec__6(v___x_833_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v___x_835_; size_t v___x_836_; size_t v___x_837_; 
lean_dec_ref(v___x_834_);
v___x_835_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37_spec__50___redArg___closed__0));
v___x_836_ = ((size_t)1ULL);
v___x_837_ = lean_usize_add(v_i_825_, v___x_836_);
v_i_825_ = v___x_837_;
v_b_826_ = v___x_835_;
goto _start;
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_851_; 
v_a_839_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_851_ == 0)
{
v___x_841_ = v___x_834_;
v_isShared_842_ = v_isSharedCheck_851_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_834_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_851_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v_ref_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
v_ref_843_ = lean_ctor_get(v___y_827_, 5);
v___x_844_ = lean_io_error_to_string(v_a_839_);
v___x_845_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
v___x_846_ = l_Lean_MessageData_ofFormat(v___x_845_);
lean_inc(v_ref_843_);
v___x_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_847_, 0, v_ref_843_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_847_);
v___x_849_ = v___x_841_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37_spec__50___redArg___boxed(lean_object* v_as_852_, lean_object* v_sz_853_, lean_object* v_i_854_, lean_object* v_b_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
size_t v_sz_boxed_858_; size_t v_i_boxed_859_; lean_object* v_res_860_; 
v_sz_boxed_858_ = lean_unbox_usize(v_sz_853_);
lean_dec(v_sz_853_);
v_i_boxed_859_ = lean_unbox_usize(v_i_854_);
lean_dec(v_i_854_);
v_res_860_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37_spec__50___redArg(v_as_852_, v_sz_boxed_858_, v_i_boxed_859_, v_b_855_, v___y_856_);
lean_dec_ref(v___y_856_);
lean_dec_ref(v_as_852_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(lean_object* v_as_861_, size_t v_sz_862_, size_t v_i_863_, lean_object* v_b_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
uint8_t v___x_868_; 
v___x_868_ = lean_usize_dec_lt(v_i_863_, v_sz_862_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; 
v___x_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_869_, 0, v_b_864_);
return v___x_869_;
}
else
{
uint8_t v___x_870_; lean_object* v_a_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
lean_dec_ref(v_b_864_);
v___x_870_ = 0;
v_a_871_ = lean_array_uget_borrowed(v_as_861_, v_i_863_);
lean_inc(v_a_871_);
v___x_872_ = l_Lean_Message_toString(v_a_871_, v___x_870_);
v___x_873_ = l_IO_eprintln___at___00main_spec__6(v___x_872_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v___x_874_; size_t v___x_875_; size_t v___x_876_; lean_object* v___x_877_; 
lean_dec_ref(v___x_873_);
v___x_874_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37_spec__50___redArg___closed__0));
v___x_875_ = ((size_t)1ULL);
v___x_876_ = lean_usize_add(v_i_863_, v___x_875_);
v___x_877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37_spec__50___redArg(v_as_861_, v_sz_862_, v___x_876_, v___x_874_, v___y_865_);
return v___x_877_;
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_890_; 
v_a_878_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_890_ == 0)
{
v___x_880_ = v___x_873_;
v_isShared_881_ = v_isSharedCheck_890_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_873_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_890_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v_ref_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_888_; 
v_ref_882_ = lean_ctor_get(v___y_865_, 5);
v___x_883_ = lean_io_error_to_string(v_a_878_);
v___x_884_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
v___x_885_ = l_Lean_MessageData_ofFormat(v___x_884_);
lean_inc(v_ref_882_);
v___x_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_886_, 0, v_ref_882_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v___x_886_);
v___x_888_ = v___x_880_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37___boxed(lean_object* v_as_891_, lean_object* v_sz_892_, lean_object* v_i_893_, lean_object* v_b_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
size_t v_sz_boxed_898_; size_t v_i_boxed_899_; lean_object* v_res_900_; 
v_sz_boxed_898_ = lean_unbox_usize(v_sz_892_);
lean_dec(v_sz_892_);
v_i_boxed_899_ = lean_unbox_usize(v_i_893_);
lean_dec(v_i_893_);
v_res_900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_as_891_, v_sz_boxed_898_, v_i_boxed_899_, v_b_894_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec_ref(v_as_891_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(lean_object* v_init_901_, lean_object* v_n_902_, lean_object* v_b_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
if (lean_obj_tag(v_n_902_) == 0)
{
lean_object* v_cs_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_941_; 
v_cs_907_ = lean_ctor_get(v_n_902_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v_n_902_);
if (v_isSharedCheck_941_ == 0)
{
v___x_909_ = v_n_902_;
v_isShared_910_ = v_isSharedCheck_941_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_cs_907_);
lean_dec(v_n_902_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_941_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; lean_object* v___x_912_; size_t v_sz_913_; size_t v___x_914_; lean_object* v___x_915_; 
v___x_911_ = lean_box(0);
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set(v___x_912_, 1, v_b_903_);
v_sz_913_ = lean_array_size(v_cs_907_);
v___x_914_ = ((size_t)0ULL);
v___x_915_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__36(v_init_901_, v_cs_907_, v_sz_913_, v___x_914_, v___x_912_, v___y_904_, v___y_905_);
lean_dec_ref(v_cs_907_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_932_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_932_ == 0)
{
v___x_918_ = v___x_915_;
v_isShared_919_ = v_isSharedCheck_932_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_932_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v_fst_920_; 
v_fst_920_ = lean_ctor_get(v_a_916_, 0);
if (lean_obj_tag(v_fst_920_) == 0)
{
lean_object* v_snd_921_; lean_object* v___x_923_; 
v_snd_921_ = lean_ctor_get(v_a_916_, 1);
lean_inc(v_snd_921_);
lean_dec(v_a_916_);
if (v_isShared_910_ == 0)
{
lean_ctor_set_tag(v___x_909_, 1);
lean_ctor_set(v___x_909_, 0, v_snd_921_);
v___x_923_ = v___x_909_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_snd_921_);
v___x_923_ = v_reuseFailAlloc_927_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
lean_object* v___x_925_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_923_);
v___x_925_ = v___x_918_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_val_928_; lean_object* v___x_930_; 
lean_inc_ref(v_fst_920_);
lean_dec(v_a_916_);
lean_del_object(v___x_909_);
v_val_928_ = lean_ctor_get(v_fst_920_, 0);
lean_inc(v_val_928_);
lean_dec_ref(v_fst_920_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v_val_928_);
v___x_930_ = v___x_918_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_val_928_);
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
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_del_object(v___x_909_);
v_a_933_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_915_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_915_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
}
else
{
lean_object* v_vs_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_976_; 
v_vs_942_ = lean_ctor_get(v_n_902_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v_n_902_);
if (v_isSharedCheck_976_ == 0)
{
v___x_944_ = v_n_902_;
v_isShared_945_ = v_isSharedCheck_976_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_vs_942_);
lean_dec(v_n_902_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_976_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; lean_object* v___x_947_; size_t v_sz_948_; size_t v___x_949_; lean_object* v___x_950_; 
v___x_946_ = lean_box(0);
v___x_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v_b_903_);
v_sz_948_ = lean_array_size(v_vs_942_);
v___x_949_ = ((size_t)0ULL);
v___x_950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_vs_942_, v_sz_948_, v___x_949_, v___x_947_, v___y_904_, v___y_905_);
lean_dec_ref(v_vs_942_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_967_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_967_ == 0)
{
v___x_953_ = v___x_950_;
v_isShared_954_ = v_isSharedCheck_967_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_950_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_967_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v_fst_955_; 
v_fst_955_ = lean_ctor_get(v_a_951_, 0);
if (lean_obj_tag(v_fst_955_) == 0)
{
lean_object* v_snd_956_; lean_object* v___x_958_; 
v_snd_956_ = lean_ctor_get(v_a_951_, 1);
lean_inc(v_snd_956_);
lean_dec(v_a_951_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v_snd_956_);
v___x_958_ = v___x_944_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_snd_956_);
v___x_958_ = v_reuseFailAlloc_962_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
lean_object* v___x_960_; 
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 0, v___x_958_);
v___x_960_ = v___x_953_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_958_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
else
{
lean_object* v_val_963_; lean_object* v___x_965_; 
lean_inc_ref(v_fst_955_);
lean_dec(v_a_951_);
lean_del_object(v___x_944_);
v_val_963_ = lean_ctor_get(v_fst_955_, 0);
lean_inc(v_val_963_);
lean_dec_ref(v_fst_955_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 0, v_val_963_);
v___x_965_ = v___x_953_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_val_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
lean_del_object(v___x_944_);
v_a_968_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_950_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_950_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__36(lean_object* v_init_977_, lean_object* v_as_978_, size_t v_sz_979_, size_t v_i_980_, lean_object* v_b_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
uint8_t v___x_985_; 
v___x_985_ = lean_usize_dec_lt(v_i_980_, v_sz_979_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; 
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v_b_981_);
return v___x_986_;
}
else
{
lean_object* v_snd_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1021_; 
v_snd_987_ = lean_ctor_get(v_b_981_, 1);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_b_981_);
if (v_isSharedCheck_1021_ == 0)
{
lean_object* v_unused_1022_; 
v_unused_1022_ = lean_ctor_get(v_b_981_, 0);
lean_dec(v_unused_1022_);
v___x_989_ = v_b_981_;
v_isShared_990_ = v_isSharedCheck_1021_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_snd_987_);
lean_dec(v_b_981_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1021_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v_a_991_; lean_object* v___x_992_; 
v_a_991_ = lean_array_uget_borrowed(v_as_978_, v_i_980_);
lean_inc(v_snd_987_);
lean_inc(v_a_991_);
v___x_992_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_977_, v_a_991_, v_snd_987_, v___y_982_, v___y_983_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1012_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1012_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1012_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
if (lean_obj_tag(v_a_993_) == 0)
{
lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_997_, 0, v_a_993_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 0, v___x_997_);
v___x_999_ = v___x_989_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_997_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v_snd_987_);
v___x_999_ = v_reuseFailAlloc_1003_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1001_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_999_);
v___x_1001_ = v___x_995_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1005_; lean_object* v___x_1007_; 
lean_del_object(v___x_995_);
lean_dec(v_snd_987_);
v_a_1004_ = lean_ctor_get(v_a_993_, 0);
lean_inc(v_a_1004_);
lean_dec_ref(v_a_993_);
v___x_1005_ = lean_box(0);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 1, v_a_1004_);
lean_ctor_set(v___x_989_, 0, v___x_1005_);
v___x_1007_ = v___x_989_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_a_1004_);
v___x_1007_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
size_t v___x_1008_; size_t v___x_1009_; 
v___x_1008_ = ((size_t)1ULL);
v___x_1009_ = lean_usize_add(v_i_980_, v___x_1008_);
v_i_980_ = v___x_1009_;
v_b_981_ = v___x_1007_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_del_object(v___x_989_);
lean_dec(v_snd_987_);
v_a_1013_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_992_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_992_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__36___boxed(lean_object* v_init_1023_, lean_object* v_as_1024_, lean_object* v_sz_1025_, lean_object* v_i_1026_, lean_object* v_b_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
size_t v_sz_boxed_1031_; size_t v_i_boxed_1032_; lean_object* v_res_1033_; 
v_sz_boxed_1031_ = lean_unbox_usize(v_sz_1025_);
lean_dec(v_sz_1025_);
v_i_boxed_1032_ = lean_unbox_usize(v_i_1026_);
lean_dec(v_i_1026_);
v_res_1033_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__36(v_init_1023_, v_as_1024_, v_sz_boxed_1031_, v_i_boxed_1032_, v_b_1027_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec_ref(v_as_1024_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26___boxed(lean_object* v_init_1034_, lean_object* v_n_1035_, lean_object* v_b_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1034_, v_n_1035_, v_b_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12(lean_object* v_t_1041_, lean_object* v_init_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v_root_1046_; lean_object* v_tail_1047_; lean_object* v___x_1048_; 
v_root_1046_ = lean_ctor_get(v_t_1041_, 0);
lean_inc_ref(v_root_1046_);
v_tail_1047_ = lean_ctor_get(v_t_1041_, 1);
lean_inc_ref(v_tail_1047_);
lean_dec_ref(v_t_1041_);
v___x_1048_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1042_, v_root_1046_, v_init_1042_, v___y_1043_, v___y_1044_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1085_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1051_ = v___x_1048_;
v_isShared_1052_ = v_isSharedCheck_1085_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1048_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1085_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
if (lean_obj_tag(v_a_1049_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1055_; 
lean_dec_ref(v_tail_1047_);
v_a_1053_ = lean_ctor_get(v_a_1049_, 0);
lean_inc(v_a_1053_);
lean_dec_ref(v_a_1049_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 0, v_a_1053_);
v___x_1055_ = v___x_1051_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1053_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; size_t v_sz_1060_; size_t v___x_1061_; lean_object* v___x_1062_; 
lean_del_object(v___x_1051_);
v_a_1057_ = lean_ctor_get(v_a_1049_, 0);
lean_inc(v_a_1057_);
lean_dec_ref(v_a_1049_);
v___x_1058_ = lean_box(0);
v___x_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
lean_ctor_set(v___x_1059_, 1, v_a_1057_);
v_sz_1060_ = lean_array_size(v_tail_1047_);
v___x_1061_ = ((size_t)0ULL);
v___x_1062_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(v_tail_1047_, v_sz_1060_, v___x_1061_, v___x_1059_, v___y_1043_, v___y_1044_);
lean_dec_ref(v_tail_1047_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1076_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1065_ = v___x_1062_;
v_isShared_1066_ = v_isSharedCheck_1076_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1062_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1076_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v_fst_1067_; 
v_fst_1067_ = lean_ctor_get(v_a_1063_, 0);
if (lean_obj_tag(v_fst_1067_) == 0)
{
lean_object* v_snd_1068_; lean_object* v___x_1070_; 
v_snd_1068_ = lean_ctor_get(v_a_1063_, 1);
lean_inc(v_snd_1068_);
lean_dec(v_a_1063_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v_snd_1068_);
v___x_1070_ = v___x_1065_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_snd_1068_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
else
{
lean_object* v_val_1072_; lean_object* v___x_1074_; 
lean_inc_ref(v_fst_1067_);
lean_dec(v_a_1063_);
v_val_1072_ = lean_ctor_get(v_fst_1067_, 0);
lean_inc(v_val_1072_);
lean_dec_ref(v_fst_1067_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v_val_1072_);
v___x_1074_ = v___x_1065_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_val_1072_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
v_a_1077_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1062_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1062_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
}
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
lean_dec_ref(v_tail_1047_);
v_a_1086_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1048_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1048_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12___boxed(lean_object* v_t_1094_, lean_object* v_init_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(v_t_1094_, v_init_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
return v_res_1099_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(uint8_t v___x_1107_, uint8_t v_suppressElabErrors_1108_, lean_object* v___x_1109_, lean_object* v_x_1110_){
_start:
{
if (lean_obj_tag(v_x_1110_) == 1)
{
lean_object* v_pre_1111_; 
v_pre_1111_ = lean_ctor_get(v_x_1110_, 0);
switch(lean_obj_tag(v_pre_1111_))
{
case 1:
{
lean_object* v_pre_1112_; 
v_pre_1112_ = lean_ctor_get(v_pre_1111_, 0);
switch(lean_obj_tag(v_pre_1112_))
{
case 0:
{
lean_object* v_str_1113_; lean_object* v_str_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v_str_1113_ = lean_ctor_get(v_x_1110_, 1);
v_str_1114_ = lean_ctor_get(v_pre_1111_, 1);
v___x_1115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0));
v___x_1116_ = lean_string_dec_eq(v_str_1114_, v___x_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; uint8_t v___x_1118_; 
v___x_1117_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1));
v___x_1118_ = lean_string_dec_eq(v_str_1114_, v___x_1117_);
if (v___x_1118_ == 0)
{
return v___x_1107_;
}
else
{
lean_object* v___x_1119_; uint8_t v___x_1120_; 
v___x_1119_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2));
v___x_1120_ = lean_string_dec_eq(v_str_1113_, v___x_1119_);
if (v___x_1120_ == 0)
{
return v___x_1107_;
}
else
{
return v_suppressElabErrors_1108_;
}
}
}
else
{
lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1121_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3));
v___x_1122_ = lean_string_dec_eq(v_str_1113_, v___x_1121_);
if (v___x_1122_ == 0)
{
return v___x_1107_;
}
else
{
return v_suppressElabErrors_1108_;
}
}
}
case 1:
{
lean_object* v_pre_1123_; 
v_pre_1123_ = lean_ctor_get(v_pre_1112_, 0);
if (lean_obj_tag(v_pre_1123_) == 0)
{
lean_object* v_str_1124_; lean_object* v_str_1125_; lean_object* v_str_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; 
v_str_1124_ = lean_ctor_get(v_x_1110_, 1);
v_str_1125_ = lean_ctor_get(v_pre_1111_, 1);
v_str_1126_ = lean_ctor_get(v_pre_1112_, 1);
v___x_1127_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4));
v___x_1128_ = lean_string_dec_eq(v_str_1126_, v___x_1127_);
if (v___x_1128_ == 0)
{
return v___x_1107_;
}
else
{
lean_object* v___x_1129_; uint8_t v___x_1130_; 
v___x_1129_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5));
v___x_1130_ = lean_string_dec_eq(v_str_1125_, v___x_1129_);
if (v___x_1130_ == 0)
{
return v___x_1107_;
}
else
{
lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1131_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6));
v___x_1132_ = lean_string_dec_eq(v_str_1124_, v___x_1131_);
if (v___x_1132_ == 0)
{
return v___x_1107_;
}
else
{
return v_suppressElabErrors_1108_;
}
}
}
}
else
{
return v___x_1107_;
}
}
default: 
{
return v___x_1107_;
}
}
}
case 0:
{
lean_object* v_str_1133_; uint8_t v___x_1134_; 
v_str_1133_ = lean_ctor_get(v_x_1110_, 1);
v___x_1134_ = lean_string_dec_eq(v_str_1133_, v___x_1109_);
if (v___x_1134_ == 0)
{
return v___x_1107_;
}
else
{
return v_suppressElabErrors_1108_;
}
}
default: 
{
return v___x_1107_;
}
}
}
else
{
return v___x_1107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed(lean_object* v___x_1135_, lean_object* v_suppressElabErrors_1136_, lean_object* v___x_1137_, lean_object* v_x_1138_){
_start:
{
uint8_t v___x_37171__boxed_1139_; uint8_t v_suppressElabErrors_boxed_1140_; uint8_t v_res_1141_; lean_object* v_r_1142_; 
v___x_37171__boxed_1139_ = lean_unbox(v___x_1135_);
v_suppressElabErrors_boxed_1140_ = lean_unbox(v_suppressElabErrors_1136_);
v_res_1141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(v___x_37171__boxed_1139_, v_suppressElabErrors_boxed_1140_, v___x_1137_, v_x_1138_);
lean_dec(v_x_1138_);
lean_dec_ref(v___x_1137_);
v_r_1142_ = lean_box(v_res_1141_);
return v_r_1142_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0(void){
_start:
{
lean_object* v___x_1143_; double v___x_1144_; 
v___x_1143_ = lean_unsigned_to_nat(0u);
v___x_1144_ = lean_float_of_nat(v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(uint8_t v___x_1146_, lean_object* v_as_1147_, size_t v_sz_1148_, size_t v_i_1149_, lean_object* v_b_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_a_1155_; uint8_t v___x_1159_; 
v___x_1159_ = lean_usize_dec_lt(v_i_1149_, v_sz_1148_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; 
v___x_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1160_, 0, v_b_1150_);
return v___x_1160_;
}
else
{
lean_object* v_a_1161_; lean_object* v_fst_1162_; lean_object* v_snd_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1239_; 
v_a_1161_ = lean_array_uget(v_as_1147_, v_i_1149_);
v_fst_1162_ = lean_ctor_get(v_a_1161_, 0);
v_snd_1163_ = lean_ctor_get(v_a_1161_, 1);
v_isSharedCheck_1239_ = !lean_is_exclusive(v_a_1161_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1165_ = v_a_1161_;
v_isShared_1166_ = v_isSharedCheck_1239_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_snd_1163_);
lean_inc(v_fst_1162_);
lean_dec(v_a_1161_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1239_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v_fst_1167_; lean_object* v_snd_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1238_; 
v_fst_1167_ = lean_ctor_get(v_fst_1162_, 0);
v_snd_1168_ = lean_ctor_get(v_fst_1162_, 1);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_fst_1162_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1170_ = v_fst_1162_;
v_isShared_1171_ = v_isSharedCheck_1238_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_snd_1168_);
lean_inc(v_fst_1167_);
lean_dec(v_fst_1162_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1238_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; double v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v_fileName_1177_; lean_object* v_fileMap_1178_; uint8_t v_suppressElabErrors_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1172_ = lean_box(0);
v___x_1173_ = lean_box(0);
v___x_1174_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0);
v___x_1175_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1));
v___x_1176_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1176_, 0, v___x_1172_);
lean_ctor_set(v___x_1176_, 1, v___x_1173_);
lean_ctor_set(v___x_1176_, 2, v___x_1175_);
lean_ctor_set_float(v___x_1176_, sizeof(void*)*3, v___x_1174_);
lean_ctor_set_float(v___x_1176_, sizeof(void*)*3 + 8, v___x_1174_);
lean_ctor_set_uint8(v___x_1176_, sizeof(void*)*3 + 16, v___x_1159_);
v_fileName_1177_ = lean_ctor_get(v___y_1151_, 0);
v_fileMap_1178_ = lean_ctor_get(v___y_1151_, 1);
v_suppressElabErrors_1179_ = lean_ctor_get_uint8(v___y_1151_, sizeof(void*)*14 + 1);
v___x_1180_ = lean_box(0);
v___x_1181_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_1182_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_1183_ = l_Lean_MessageData_nil;
v___x_1184_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1176_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
lean_ctor_set(v___x_1184_, 2, v_snd_1163_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set_tag(v___x_1170_, 8);
lean_ctor_set(v___x_1170_, 1, v___x_1184_);
lean_ctor_set(v___x_1170_, 0, v___x_1182_);
v___x_1186_ = v___x_1170_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1182_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
uint8_t v___x_1187_; lean_object* v___x_1188_; lean_object* v___y_1190_; lean_object* v___y_1191_; 
v___x_1187_ = 0;
lean_inc_ref(v_fileMap_1178_);
lean_inc_ref(v_fileName_1177_);
v___x_1188_ = l_Lean_Elab_mkMessageCore(v_fileName_1177_, v_fileMap_1178_, v___x_1186_, v___x_1187_, v_fst_1167_, v_snd_1168_);
lean_dec(v_snd_1168_);
lean_dec(v_fst_1167_);
if (v_suppressElabErrors_1179_ == 0)
{
v___y_1190_ = v___y_1151_;
v___y_1191_ = v___y_1152_;
goto v___jp_1189_;
}
else
{
lean_object* v_data_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___f_1235_; uint8_t v___x_1236_; 
v_data_1232_ = lean_ctor_get(v___x_1188_, 4);
lean_inc(v_data_1232_);
v___x_1233_ = lean_box(v___x_1146_);
v___x_1234_ = lean_box(v_suppressElabErrors_1179_);
v___f_1235_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1235_, 0, v___x_1233_);
lean_closure_set(v___f_1235_, 1, v___x_1234_);
lean_closure_set(v___f_1235_, 2, v___x_1181_);
v___x_1236_ = l_Lean_MessageData_hasTag(v___f_1235_, v_data_1232_);
if (v___x_1236_ == 0)
{
lean_dec_ref(v___x_1188_);
lean_del_object(v___x_1165_);
v_a_1155_ = v___x_1180_;
goto v___jp_1154_;
}
else
{
v___y_1190_ = v___y_1151_;
v___y_1191_ = v___y_1152_;
goto v___jp_1189_;
}
}
v___jp_1189_:
{
lean_object* v___x_1192_; lean_object* v_fileName_1193_; lean_object* v_pos_1194_; lean_object* v_endPos_1195_; uint8_t v_keepFullRange_1196_; uint8_t v_severity_1197_; uint8_t v_isSilent_1198_; lean_object* v_caption_1199_; lean_object* v_data_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1231_; 
v___x_1192_ = lean_st_ref_take(v___y_1191_);
v_fileName_1193_ = lean_ctor_get(v___x_1188_, 0);
v_pos_1194_ = lean_ctor_get(v___x_1188_, 1);
v_endPos_1195_ = lean_ctor_get(v___x_1188_, 2);
v_keepFullRange_1196_ = lean_ctor_get_uint8(v___x_1188_, sizeof(void*)*5);
v_severity_1197_ = lean_ctor_get_uint8(v___x_1188_, sizeof(void*)*5 + 1);
v_isSilent_1198_ = lean_ctor_get_uint8(v___x_1188_, sizeof(void*)*5 + 2);
v_caption_1199_ = lean_ctor_get(v___x_1188_, 3);
v_data_1200_ = lean_ctor_get(v___x_1188_, 4);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1202_ = v___x_1188_;
v_isShared_1203_ = v_isSharedCheck_1231_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_data_1200_);
lean_inc(v_caption_1199_);
lean_inc(v_endPos_1195_);
lean_inc(v_pos_1194_);
lean_inc(v_fileName_1193_);
lean_dec(v___x_1188_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1231_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v_currNamespace_1204_; lean_object* v_openDecls_1205_; lean_object* v_env_1206_; lean_object* v_nextMacroScope_1207_; lean_object* v_ngen_1208_; lean_object* v_auxDeclNGen_1209_; lean_object* v_traceState_1210_; lean_object* v_cache_1211_; lean_object* v_messages_1212_; lean_object* v_infoState_1213_; lean_object* v_snapshotTasks_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1230_; 
v_currNamespace_1204_ = lean_ctor_get(v___y_1190_, 6);
v_openDecls_1205_ = lean_ctor_get(v___y_1190_, 7);
v_env_1206_ = lean_ctor_get(v___x_1192_, 0);
v_nextMacroScope_1207_ = lean_ctor_get(v___x_1192_, 1);
v_ngen_1208_ = lean_ctor_get(v___x_1192_, 2);
v_auxDeclNGen_1209_ = lean_ctor_get(v___x_1192_, 3);
v_traceState_1210_ = lean_ctor_get(v___x_1192_, 4);
v_cache_1211_ = lean_ctor_get(v___x_1192_, 5);
v_messages_1212_ = lean_ctor_get(v___x_1192_, 6);
v_infoState_1213_ = lean_ctor_get(v___x_1192_, 7);
v_snapshotTasks_1214_ = lean_ctor_get(v___x_1192_, 8);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1216_ = v___x_1192_;
v_isShared_1217_ = v_isSharedCheck_1230_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_snapshotTasks_1214_);
lean_inc(v_infoState_1213_);
lean_inc(v_messages_1212_);
lean_inc(v_cache_1211_);
lean_inc(v_traceState_1210_);
lean_inc(v_auxDeclNGen_1209_);
lean_inc(v_ngen_1208_);
lean_inc(v_nextMacroScope_1207_);
lean_inc(v_env_1206_);
lean_dec(v___x_1192_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1230_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
lean_inc(v_openDecls_1205_);
lean_inc(v_currNamespace_1204_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 1, v_openDecls_1205_);
lean_ctor_set(v___x_1165_, 0, v_currNamespace_1204_);
v___x_1219_ = v___x_1165_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_currNamespace_1204_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_openDecls_1205_);
v___x_1219_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v___x_1220_; lean_object* v___x_1222_; 
v___x_1220_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
lean_ctor_set(v___x_1220_, 1, v_data_1200_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 4, v___x_1220_);
v___x_1222_ = v___x_1202_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_fileName_1193_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_pos_1194_);
lean_ctor_set(v_reuseFailAlloc_1228_, 2, v_endPos_1195_);
lean_ctor_set(v_reuseFailAlloc_1228_, 3, v_caption_1199_);
lean_ctor_set(v_reuseFailAlloc_1228_, 4, v___x_1220_);
lean_ctor_set_uint8(v_reuseFailAlloc_1228_, sizeof(void*)*5, v_keepFullRange_1196_);
lean_ctor_set_uint8(v_reuseFailAlloc_1228_, sizeof(void*)*5 + 1, v_severity_1197_);
lean_ctor_set_uint8(v_reuseFailAlloc_1228_, sizeof(void*)*5 + 2, v_isSilent_1198_);
v___x_1222_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1223_ = l_Lean_MessageLog_add(v___x_1222_, v_messages_1212_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 6, v___x_1223_);
v___x_1225_ = v___x_1216_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_env_1206_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_nextMacroScope_1207_);
lean_ctor_set(v_reuseFailAlloc_1227_, 2, v_ngen_1208_);
lean_ctor_set(v_reuseFailAlloc_1227_, 3, v_auxDeclNGen_1209_);
lean_ctor_set(v_reuseFailAlloc_1227_, 4, v_traceState_1210_);
lean_ctor_set(v_reuseFailAlloc_1227_, 5, v_cache_1211_);
lean_ctor_set(v_reuseFailAlloc_1227_, 6, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1227_, 7, v_infoState_1213_);
lean_ctor_set(v_reuseFailAlloc_1227_, 8, v_snapshotTasks_1214_);
v___x_1225_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1226_; 
v___x_1226_ = lean_st_ref_set(v___y_1191_, v___x_1225_);
v_a_1155_ = v___x_1180_;
goto v___jp_1154_;
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
v___jp_1154_:
{
size_t v___x_1156_; size_t v___x_1157_; 
v___x_1156_ = ((size_t)1ULL);
v___x_1157_ = lean_usize_add(v_i_1149_, v___x_1156_);
v_i_1149_ = v___x_1157_;
v_b_1150_ = v_a_1155_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___boxed(lean_object* v___x_1240_, lean_object* v_as_1241_, lean_object* v_sz_1242_, lean_object* v_i_1243_, lean_object* v_b_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
uint8_t v___x_37244__boxed_1248_; size_t v_sz_boxed_1249_; size_t v_i_boxed_1250_; lean_object* v_res_1251_; 
v___x_37244__boxed_1248_ = lean_unbox(v___x_1240_);
v_sz_boxed_1249_ = lean_unbox_usize(v_sz_1242_);
lean_dec(v_sz_1242_);
v_i_boxed_1250_ = lean_unbox_usize(v_i_1243_);
lean_dec(v_i_1243_);
v_res_1251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_37244__boxed_1248_, v_as_1241_, v_sz_boxed_1249_, v_i_boxed_1250_, v_b_1244_, v___y_1245_, v___y_1246_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec_ref(v_as_1241_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(lean_object* v_opts_1252_, lean_object* v_opt_1253_){
_start:
{
lean_object* v_name_1254_; lean_object* v_map_1255_; lean_object* v___x_1256_; 
v_name_1254_ = lean_ctor_get(v_opt_1253_, 0);
v_map_1255_ = lean_ctor_get(v_opts_1252_, 0);
v___x_1256_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1255_, v_name_1254_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v___x_1257_; 
v___x_1257_ = lean_box(0);
return v___x_1257_;
}
else
{
lean_object* v_val_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1267_; 
v_val_1258_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1260_ = v___x_1256_;
v_isShared_1261_ = v_isSharedCheck_1267_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_val_1258_);
lean_dec(v___x_1256_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1267_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
if (lean_obj_tag(v_val_1258_) == 0)
{
lean_object* v_v_1262_; lean_object* v___x_1264_; 
v_v_1262_ = lean_ctor_get(v_val_1258_, 0);
lean_inc_ref(v_v_1262_);
lean_dec_ref(v_val_1258_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 0, v_v_1262_);
v___x_1264_ = v___x_1260_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_v_1262_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
else
{
lean_object* v___x_1266_; 
lean_del_object(v___x_1260_);
lean_dec(v_val_1258_);
v___x_1266_ = lean_box(0);
return v___x_1266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15___boxed(lean_object* v_opts_1268_, lean_object* v_opt_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(v_opts_1268_, v_opt_1269_);
lean_dec_ref(v_opt_1269_);
lean_dec_ref(v_opts_1268_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(lean_object* v_a_1271_, lean_object* v_fallback_1272_, lean_object* v_x_1273_){
_start:
{
if (lean_obj_tag(v_x_1273_) == 0)
{
lean_inc(v_fallback_1272_);
return v_fallback_1272_;
}
else
{
lean_object* v_key_1274_; lean_object* v_value_1275_; lean_object* v_tail_1276_; uint8_t v___y_1278_; lean_object* v_fst_1280_; lean_object* v_snd_1281_; lean_object* v_fst_1282_; lean_object* v_snd_1283_; uint8_t v___x_1284_; 
v_key_1274_ = lean_ctor_get(v_x_1273_, 0);
v_value_1275_ = lean_ctor_get(v_x_1273_, 1);
v_tail_1276_ = lean_ctor_get(v_x_1273_, 2);
v_fst_1280_ = lean_ctor_get(v_key_1274_, 0);
v_snd_1281_ = lean_ctor_get(v_key_1274_, 1);
v_fst_1282_ = lean_ctor_get(v_a_1271_, 0);
v_snd_1283_ = lean_ctor_get(v_a_1271_, 1);
v___x_1284_ = lean_nat_dec_eq(v_fst_1280_, v_fst_1282_);
if (v___x_1284_ == 0)
{
v___y_1278_ = v___x_1284_;
goto v___jp_1277_;
}
else
{
uint8_t v___x_1285_; 
v___x_1285_ = lean_nat_dec_eq(v_snd_1281_, v_snd_1283_);
v___y_1278_ = v___x_1285_;
goto v___jp_1277_;
}
v___jp_1277_:
{
if (v___y_1278_ == 0)
{
v_x_1273_ = v_tail_1276_;
goto _start;
}
else
{
lean_inc(v_value_1275_);
return v_value_1275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg___boxed(lean_object* v_a_1286_, lean_object* v_fallback_1287_, lean_object* v_x_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_1286_, v_fallback_1287_, v_x_1288_);
lean_dec(v_x_1288_);
lean_dec(v_fallback_1287_);
lean_dec_ref(v_a_1286_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(lean_object* v_m_1290_, lean_object* v_a_1291_, lean_object* v_fallback_1292_){
_start:
{
lean_object* v_buckets_1293_; lean_object* v_fst_1294_; lean_object* v_snd_1295_; lean_object* v___x_1296_; uint64_t v___x_1297_; uint64_t v___x_1298_; uint64_t v___x_1299_; uint64_t v___x_1300_; uint64_t v___x_1301_; uint64_t v_fold_1302_; uint64_t v___x_1303_; uint64_t v___x_1304_; uint64_t v___x_1305_; size_t v___x_1306_; size_t v___x_1307_; size_t v___x_1308_; size_t v___x_1309_; size_t v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v_buckets_1293_ = lean_ctor_get(v_m_1290_, 1);
v_fst_1294_ = lean_ctor_get(v_a_1291_, 0);
v_snd_1295_ = lean_ctor_get(v_a_1291_, 1);
v___x_1296_ = lean_array_get_size(v_buckets_1293_);
v___x_1297_ = l_String_instHashableRaw_hash(v_fst_1294_);
v___x_1298_ = l_String_instHashableRaw_hash(v_snd_1295_);
v___x_1299_ = lean_uint64_mix_hash(v___x_1297_, v___x_1298_);
v___x_1300_ = 32ULL;
v___x_1301_ = lean_uint64_shift_right(v___x_1299_, v___x_1300_);
v_fold_1302_ = lean_uint64_xor(v___x_1299_, v___x_1301_);
v___x_1303_ = 16ULL;
v___x_1304_ = lean_uint64_shift_right(v_fold_1302_, v___x_1303_);
v___x_1305_ = lean_uint64_xor(v_fold_1302_, v___x_1304_);
v___x_1306_ = lean_uint64_to_usize(v___x_1305_);
v___x_1307_ = lean_usize_of_nat(v___x_1296_);
v___x_1308_ = ((size_t)1ULL);
v___x_1309_ = lean_usize_sub(v___x_1307_, v___x_1308_);
v___x_1310_ = lean_usize_land(v___x_1306_, v___x_1309_);
v___x_1311_ = lean_array_uget_borrowed(v_buckets_1293_, v___x_1310_);
v___x_1312_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_1291_, v_fallback_1292_, v___x_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg___boxed(lean_object* v_m_1313_, lean_object* v_a_1314_, lean_object* v_fallback_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_1313_, v_a_1314_, v_fallback_1315_);
lean_dec(v_fallback_1315_);
lean_dec_ref(v_a_1314_);
lean_dec_ref(v_m_1313_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(lean_object* v_x_1317_, lean_object* v_x_1318_){
_start:
{
if (lean_obj_tag(v_x_1318_) == 0)
{
return v_x_1317_;
}
else
{
lean_object* v_key_1319_; lean_object* v_value_1320_; lean_object* v_tail_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1348_; 
v_key_1319_ = lean_ctor_get(v_x_1318_, 0);
v_value_1320_ = lean_ctor_get(v_x_1318_, 1);
v_tail_1321_ = lean_ctor_get(v_x_1318_, 2);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_x_1318_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1323_ = v_x_1318_;
v_isShared_1324_ = v_isSharedCheck_1348_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_tail_1321_);
lean_inc(v_value_1320_);
lean_inc(v_key_1319_);
lean_dec(v_x_1318_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1348_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v_fst_1325_; lean_object* v_snd_1326_; lean_object* v___x_1327_; uint64_t v___x_1328_; uint64_t v___x_1329_; uint64_t v___x_1330_; uint64_t v___x_1331_; uint64_t v___x_1332_; uint64_t v_fold_1333_; uint64_t v___x_1334_; uint64_t v___x_1335_; uint64_t v___x_1336_; size_t v___x_1337_; size_t v___x_1338_; size_t v___x_1339_; size_t v___x_1340_; size_t v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1344_; 
v_fst_1325_ = lean_ctor_get(v_key_1319_, 0);
v_snd_1326_ = lean_ctor_get(v_key_1319_, 1);
v___x_1327_ = lean_array_get_size(v_x_1317_);
v___x_1328_ = l_String_instHashableRaw_hash(v_fst_1325_);
v___x_1329_ = l_String_instHashableRaw_hash(v_snd_1326_);
v___x_1330_ = lean_uint64_mix_hash(v___x_1328_, v___x_1329_);
v___x_1331_ = 32ULL;
v___x_1332_ = lean_uint64_shift_right(v___x_1330_, v___x_1331_);
v_fold_1333_ = lean_uint64_xor(v___x_1330_, v___x_1332_);
v___x_1334_ = 16ULL;
v___x_1335_ = lean_uint64_shift_right(v_fold_1333_, v___x_1334_);
v___x_1336_ = lean_uint64_xor(v_fold_1333_, v___x_1335_);
v___x_1337_ = lean_uint64_to_usize(v___x_1336_);
v___x_1338_ = lean_usize_of_nat(v___x_1327_);
v___x_1339_ = ((size_t)1ULL);
v___x_1340_ = lean_usize_sub(v___x_1338_, v___x_1339_);
v___x_1341_ = lean_usize_land(v___x_1337_, v___x_1340_);
v___x_1342_ = lean_array_uget_borrowed(v_x_1317_, v___x_1341_);
lean_inc(v___x_1342_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 2, v___x_1342_);
v___x_1344_ = v___x_1323_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_key_1319_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v_value_1320_);
lean_ctor_set(v_reuseFailAlloc_1347_, 2, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
lean_object* v___x_1345_; 
v___x_1345_ = lean_array_uset(v_x_1317_, v___x_1341_, v___x_1344_);
v_x_1317_ = v___x_1345_;
v_x_1318_ = v_tail_1321_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(lean_object* v_i_1349_, lean_object* v_source_1350_, lean_object* v_target_1351_){
_start:
{
lean_object* v___x_1352_; uint8_t v___x_1353_; 
v___x_1352_ = lean_array_get_size(v_source_1350_);
v___x_1353_ = lean_nat_dec_lt(v_i_1349_, v___x_1352_);
if (v___x_1353_ == 0)
{
lean_dec_ref(v_source_1350_);
lean_dec(v_i_1349_);
return v_target_1351_;
}
else
{
lean_object* v_es_1354_; lean_object* v___x_1355_; lean_object* v_source_1356_; lean_object* v_target_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v_es_1354_ = lean_array_fget(v_source_1350_, v_i_1349_);
v___x_1355_ = lean_box(0);
v_source_1356_ = lean_array_fset(v_source_1350_, v_i_1349_, v___x_1355_);
v_target_1357_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_target_1351_, v_es_1354_);
v___x_1358_ = lean_unsigned_to_nat(1u);
v___x_1359_ = lean_nat_add(v_i_1349_, v___x_1358_);
lean_dec(v_i_1349_);
v_i_1349_ = v___x_1359_;
v_source_1350_ = v_source_1356_;
v_target_1351_ = v_target_1357_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(lean_object* v_data_1361_){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v_nbuckets_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1362_ = lean_array_get_size(v_data_1361_);
v___x_1363_ = lean_unsigned_to_nat(2u);
v_nbuckets_1364_ = lean_nat_mul(v___x_1362_, v___x_1363_);
v___x_1365_ = lean_unsigned_to_nat(0u);
v___x_1366_ = lean_box(0);
v___x_1367_ = lean_mk_array(v_nbuckets_1364_, v___x_1366_);
v___x_1368_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v___x_1365_, v_data_1361_, v___x_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(lean_object* v_a_1369_, lean_object* v_b_1370_, lean_object* v_x_1371_){
_start:
{
if (lean_obj_tag(v_x_1371_) == 0)
{
lean_dec(v_b_1370_);
lean_dec_ref(v_a_1369_);
return v_x_1371_;
}
else
{
lean_object* v_key_1372_; lean_object* v_value_1373_; lean_object* v_tail_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1393_; 
v_key_1372_ = lean_ctor_get(v_x_1371_, 0);
v_value_1373_ = lean_ctor_get(v_x_1371_, 1);
v_tail_1374_ = lean_ctor_get(v_x_1371_, 2);
v_isSharedCheck_1393_ = !lean_is_exclusive(v_x_1371_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1376_ = v_x_1371_;
v_isShared_1377_ = v_isSharedCheck_1393_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_tail_1374_);
lean_inc(v_value_1373_);
lean_inc(v_key_1372_);
lean_dec(v_x_1371_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1393_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
uint8_t v___y_1379_; lean_object* v_fst_1387_; lean_object* v_snd_1388_; lean_object* v_fst_1389_; lean_object* v_snd_1390_; uint8_t v___x_1391_; 
v_fst_1387_ = lean_ctor_get(v_key_1372_, 0);
v_snd_1388_ = lean_ctor_get(v_key_1372_, 1);
v_fst_1389_ = lean_ctor_get(v_a_1369_, 0);
v_snd_1390_ = lean_ctor_get(v_a_1369_, 1);
v___x_1391_ = lean_nat_dec_eq(v_fst_1387_, v_fst_1389_);
if (v___x_1391_ == 0)
{
v___y_1379_ = v___x_1391_;
goto v___jp_1378_;
}
else
{
uint8_t v___x_1392_; 
v___x_1392_ = lean_nat_dec_eq(v_snd_1388_, v_snd_1390_);
v___y_1379_ = v___x_1392_;
goto v___jp_1378_;
}
v___jp_1378_:
{
if (v___y_1379_ == 0)
{
lean_object* v___x_1380_; lean_object* v___x_1382_; 
v___x_1380_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_1369_, v_b_1370_, v_tail_1374_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 2, v___x_1380_);
v___x_1382_ = v___x_1376_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_key_1372_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_value_1373_);
lean_ctor_set(v_reuseFailAlloc_1383_, 2, v___x_1380_);
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
lean_object* v___x_1385_; 
lean_dec(v_value_1373_);
lean_dec(v_key_1372_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 1, v_b_1370_);
lean_ctor_set(v___x_1376_, 0, v_a_1369_);
v___x_1385_ = v___x_1376_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1369_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_b_1370_);
lean_ctor_set(v_reuseFailAlloc_1386_, 2, v_tail_1374_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(lean_object* v_a_1394_, lean_object* v_x_1395_){
_start:
{
if (lean_obj_tag(v_x_1395_) == 0)
{
uint8_t v___x_1396_; 
v___x_1396_ = 0;
return v___x_1396_;
}
else
{
lean_object* v_key_1397_; lean_object* v_tail_1398_; uint8_t v___y_1400_; lean_object* v_fst_1402_; lean_object* v_snd_1403_; lean_object* v_fst_1404_; lean_object* v_snd_1405_; uint8_t v___x_1406_; 
v_key_1397_ = lean_ctor_get(v_x_1395_, 0);
v_tail_1398_ = lean_ctor_get(v_x_1395_, 2);
v_fst_1402_ = lean_ctor_get(v_key_1397_, 0);
v_snd_1403_ = lean_ctor_get(v_key_1397_, 1);
v_fst_1404_ = lean_ctor_get(v_a_1394_, 0);
v_snd_1405_ = lean_ctor_get(v_a_1394_, 1);
v___x_1406_ = lean_nat_dec_eq(v_fst_1402_, v_fst_1404_);
if (v___x_1406_ == 0)
{
v___y_1400_ = v___x_1406_;
goto v___jp_1399_;
}
else
{
uint8_t v___x_1407_; 
v___x_1407_ = lean_nat_dec_eq(v_snd_1403_, v_snd_1405_);
v___y_1400_ = v___x_1407_;
goto v___jp_1399_;
}
v___jp_1399_:
{
if (v___y_1400_ == 0)
{
v_x_1395_ = v_tail_1398_;
goto _start;
}
else
{
return v___y_1400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg___boxed(lean_object* v_a_1408_, lean_object* v_x_1409_){
_start:
{
uint8_t v_res_1410_; lean_object* v_r_1411_; 
v_res_1410_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_1408_, v_x_1409_);
lean_dec(v_x_1409_);
lean_dec_ref(v_a_1408_);
v_r_1411_ = lean_box(v_res_1410_);
return v_r_1411_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(lean_object* v_m_1412_, lean_object* v_a_1413_, lean_object* v_b_1414_){
_start:
{
lean_object* v_size_1415_; lean_object* v_buckets_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1463_; 
v_size_1415_ = lean_ctor_get(v_m_1412_, 0);
v_buckets_1416_ = lean_ctor_get(v_m_1412_, 1);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_m_1412_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1418_ = v_m_1412_;
v_isShared_1419_ = v_isSharedCheck_1463_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_buckets_1416_);
lean_inc(v_size_1415_);
lean_dec(v_m_1412_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1463_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v_fst_1420_; lean_object* v_snd_1421_; lean_object* v___x_1422_; uint64_t v___x_1423_; uint64_t v___x_1424_; uint64_t v___x_1425_; uint64_t v___x_1426_; uint64_t v___x_1427_; uint64_t v_fold_1428_; uint64_t v___x_1429_; uint64_t v___x_1430_; uint64_t v___x_1431_; size_t v___x_1432_; size_t v___x_1433_; size_t v___x_1434_; size_t v___x_1435_; size_t v___x_1436_; lean_object* v_bkt_1437_; uint8_t v___x_1438_; 
v_fst_1420_ = lean_ctor_get(v_a_1413_, 0);
v_snd_1421_ = lean_ctor_get(v_a_1413_, 1);
v___x_1422_ = lean_array_get_size(v_buckets_1416_);
v___x_1423_ = l_String_instHashableRaw_hash(v_fst_1420_);
v___x_1424_ = l_String_instHashableRaw_hash(v_snd_1421_);
v___x_1425_ = lean_uint64_mix_hash(v___x_1423_, v___x_1424_);
v___x_1426_ = 32ULL;
v___x_1427_ = lean_uint64_shift_right(v___x_1425_, v___x_1426_);
v_fold_1428_ = lean_uint64_xor(v___x_1425_, v___x_1427_);
v___x_1429_ = 16ULL;
v___x_1430_ = lean_uint64_shift_right(v_fold_1428_, v___x_1429_);
v___x_1431_ = lean_uint64_xor(v_fold_1428_, v___x_1430_);
v___x_1432_ = lean_uint64_to_usize(v___x_1431_);
v___x_1433_ = lean_usize_of_nat(v___x_1422_);
v___x_1434_ = ((size_t)1ULL);
v___x_1435_ = lean_usize_sub(v___x_1433_, v___x_1434_);
v___x_1436_ = lean_usize_land(v___x_1432_, v___x_1435_);
v_bkt_1437_ = lean_array_uget_borrowed(v_buckets_1416_, v___x_1436_);
v___x_1438_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_1413_, v_bkt_1437_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; lean_object* v_size_x27_1440_; lean_object* v___x_1441_; lean_object* v_buckets_x27_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1439_ = lean_unsigned_to_nat(1u);
v_size_x27_1440_ = lean_nat_add(v_size_1415_, v___x_1439_);
lean_dec(v_size_1415_);
lean_inc(v_bkt_1437_);
v___x_1441_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1441_, 0, v_a_1413_);
lean_ctor_set(v___x_1441_, 1, v_b_1414_);
lean_ctor_set(v___x_1441_, 2, v_bkt_1437_);
v_buckets_x27_1442_ = lean_array_uset(v_buckets_1416_, v___x_1436_, v___x_1441_);
v___x_1443_ = lean_unsigned_to_nat(4u);
v___x_1444_ = lean_nat_mul(v_size_x27_1440_, v___x_1443_);
v___x_1445_ = lean_unsigned_to_nat(3u);
v___x_1446_ = lean_nat_div(v___x_1444_, v___x_1445_);
lean_dec(v___x_1444_);
v___x_1447_ = lean_array_get_size(v_buckets_x27_1442_);
v___x_1448_ = lean_nat_dec_le(v___x_1446_, v___x_1447_);
lean_dec(v___x_1446_);
if (v___x_1448_ == 0)
{
lean_object* v_val_1449_; lean_object* v___x_1451_; 
v_val_1449_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_buckets_x27_1442_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 1, v_val_1449_);
lean_ctor_set(v___x_1418_, 0, v_size_x27_1440_);
v___x_1451_ = v___x_1418_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_size_x27_1440_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_val_1449_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
else
{
lean_object* v___x_1454_; 
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 1, v_buckets_x27_1442_);
lean_ctor_set(v___x_1418_, 0, v_size_x27_1440_);
v___x_1454_ = v___x_1418_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_size_x27_1440_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_buckets_x27_1442_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
else
{
lean_object* v___x_1456_; lean_object* v_buckets_x27_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1461_; 
lean_inc(v_bkt_1437_);
v___x_1456_ = lean_box(0);
v_buckets_x27_1457_ = lean_array_uset(v_buckets_1416_, v___x_1436_, v___x_1456_);
v___x_1458_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_1413_, v_b_1414_, v_bkt_1437_);
v___x_1459_ = lean_array_uset(v_buckets_x27_1457_, v___x_1436_, v___x_1458_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 1, v___x_1459_);
v___x_1461_ = v___x_1418_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_size_1415_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v___x_1459_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(uint8_t v___x_1466_, lean_object* v_as_1467_, size_t v_sz_1468_, size_t v_i_1469_, lean_object* v_b_1470_, lean_object* v___y_1471_){
_start:
{
uint8_t v___x_1473_; 
v___x_1473_ = lean_usize_dec_lt(v_i_1469_, v_sz_1468_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; 
v___x_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1474_, 0, v_b_1470_);
return v___x_1474_;
}
else
{
lean_object* v_snd_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1512_; 
v_snd_1475_ = lean_ctor_get(v_b_1470_, 1);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_b_1470_);
if (v_isSharedCheck_1512_ == 0)
{
lean_object* v_unused_1513_; 
v_unused_1513_ = lean_ctor_get(v_b_1470_, 0);
lean_dec(v_unused_1513_);
v___x_1477_ = v_b_1470_;
v_isShared_1478_ = v_isSharedCheck_1512_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_snd_1475_);
lean_dec(v_b_1470_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1512_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v_ref_1479_; lean_object* v_a_1480_; lean_object* v_ref_1481_; lean_object* v_msg_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1511_; 
v_ref_1479_ = lean_ctor_get(v___y_1471_, 5);
v_a_1480_ = lean_array_uget(v_as_1467_, v_i_1469_);
v_ref_1481_ = lean_ctor_get(v_a_1480_, 0);
v_msg_1482_ = lean_ctor_get(v_a_1480_, 1);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_a_1480_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1484_ = v_a_1480_;
v_isShared_1485_ = v_isSharedCheck_1511_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_msg_1482_);
lean_inc(v_ref_1481_);
lean_dec(v_a_1480_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1511_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1486_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v_ref_1503_; lean_object* v___y_1505_; lean_object* v___x_1508_; 
v___x_1486_ = lean_box(0);
v_ref_1503_ = l_Lean_replaceRef(v_ref_1481_, v_ref_1479_);
lean_dec(v_ref_1481_);
v___x_1508_ = l_Lean_Syntax_getPos_x3f(v_ref_1503_, v___x_1466_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_unsigned_to_nat(0u);
v___y_1505_ = v___x_1509_;
goto v___jp_1504_;
}
else
{
lean_object* v_val_1510_; 
v_val_1510_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_val_1510_);
lean_dec_ref(v___x_1508_);
v___y_1505_ = v_val_1510_;
goto v___jp_1504_;
}
v___jp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 1, v___y_1489_);
lean_ctor_set(v___x_1477_, 0, v___y_1488_);
v___x_1491_ = v___x_1477_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___y_1488_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v___y_1489_);
v___x_1491_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v_pos2traces_1495_; lean_object* v___x_1497_; 
v___x_1492_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1493_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1475_, v___x_1491_, v___x_1492_);
v___x_1494_ = lean_array_push(v___x_1493_, v_msg_1482_);
v_pos2traces_1495_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1475_, v___x_1491_, v___x_1494_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 1, v_pos2traces_1495_);
lean_ctor_set(v___x_1484_, 0, v___x_1486_);
v___x_1497_ = v___x_1484_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_pos2traces_1495_);
v___x_1497_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
size_t v___x_1498_; size_t v___x_1499_; 
v___x_1498_ = ((size_t)1ULL);
v___x_1499_ = lean_usize_add(v_i_1469_, v___x_1498_);
v_i_1469_ = v___x_1499_;
v_b_1470_ = v___x_1497_;
goto _start;
}
}
}
v___jp_1504_:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1503_, v___x_1466_);
lean_dec(v_ref_1503_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_inc(v___y_1505_);
v___y_1488_ = v___y_1505_;
v___y_1489_ = v___y_1505_;
goto v___jp_1487_;
}
else
{
lean_object* v_val_1507_; 
v_val_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_val_1507_);
lean_dec_ref(v___x_1506_);
v___y_1488_ = v___y_1505_;
v___y_1489_ = v_val_1507_;
goto v___jp_1487_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___boxed(lean_object* v___x_1514_, lean_object* v_as_1515_, lean_object* v_sz_1516_, lean_object* v_i_1517_, lean_object* v_b_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
uint8_t v___x_37724__boxed_1521_; size_t v_sz_boxed_1522_; size_t v_i_boxed_1523_; lean_object* v_res_1524_; 
v___x_37724__boxed_1521_ = lean_unbox(v___x_1514_);
v_sz_boxed_1522_ = lean_unbox_usize(v_sz_1516_);
lean_dec(v_sz_1516_);
v_i_boxed_1523_ = lean_unbox_usize(v_i_1517_);
lean_dec(v_i_1517_);
v_res_1524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_37724__boxed_1521_, v_as_1515_, v_sz_boxed_1522_, v_i_boxed_1523_, v_b_1518_, v___y_1519_);
lean_dec_ref(v___y_1519_);
lean_dec_ref(v_as_1515_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(uint8_t v___x_1525_, lean_object* v_as_1526_, size_t v_sz_1527_, size_t v_i_1528_, lean_object* v_b_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
uint8_t v___x_1533_; 
v___x_1533_ = lean_usize_dec_lt(v_i_1528_, v_sz_1527_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1534_, 0, v_b_1529_);
return v___x_1534_;
}
else
{
lean_object* v_snd_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1572_; 
v_snd_1535_ = lean_ctor_get(v_b_1529_, 1);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_b_1529_);
if (v_isSharedCheck_1572_ == 0)
{
lean_object* v_unused_1573_; 
v_unused_1573_ = lean_ctor_get(v_b_1529_, 0);
lean_dec(v_unused_1573_);
v___x_1537_ = v_b_1529_;
v_isShared_1538_ = v_isSharedCheck_1572_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_snd_1535_);
lean_dec(v_b_1529_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1572_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v_ref_1539_; lean_object* v_a_1540_; lean_object* v_ref_1541_; lean_object* v_msg_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1571_; 
v_ref_1539_ = lean_ctor_get(v___y_1530_, 5);
v_a_1540_ = lean_array_uget(v_as_1526_, v_i_1528_);
v_ref_1541_ = lean_ctor_get(v_a_1540_, 0);
v_msg_1542_ = lean_ctor_get(v_a_1540_, 1);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_a_1540_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1544_ = v_a_1540_;
v_isShared_1545_ = v_isSharedCheck_1571_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_msg_1542_);
lean_inc(v_ref_1541_);
lean_dec(v_a_1540_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1571_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1546_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v_ref_1563_; lean_object* v___y_1565_; lean_object* v___x_1568_; 
v___x_1546_ = lean_box(0);
v_ref_1563_ = l_Lean_replaceRef(v_ref_1541_, v_ref_1539_);
lean_dec(v_ref_1541_);
v___x_1568_ = l_Lean_Syntax_getPos_x3f(v_ref_1563_, v___x_1525_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v___x_1569_; 
v___x_1569_ = lean_unsigned_to_nat(0u);
v___y_1565_ = v___x_1569_;
goto v___jp_1564_;
}
else
{
lean_object* v_val_1570_; 
v_val_1570_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_val_1570_);
lean_dec_ref(v___x_1568_);
v___y_1565_ = v_val_1570_;
goto v___jp_1564_;
}
v___jp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 1, v___y_1549_);
lean_ctor_set(v___x_1537_, 0, v___y_1548_);
v___x_1551_ = v___x_1537_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___y_1548_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v___y_1549_);
v___x_1551_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v_pos2traces_1555_; lean_object* v___x_1557_; 
v___x_1552_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1553_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1535_, v___x_1551_, v___x_1552_);
v___x_1554_ = lean_array_push(v___x_1553_, v_msg_1542_);
v_pos2traces_1555_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1535_, v___x_1551_, v___x_1554_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 1, v_pos2traces_1555_);
lean_ctor_set(v___x_1544_, 0, v___x_1546_);
v___x_1557_ = v___x_1544_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1546_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v_pos2traces_1555_);
v___x_1557_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
size_t v___x_1558_; size_t v___x_1559_; lean_object* v___x_1560_; 
v___x_1558_ = ((size_t)1ULL);
v___x_1559_ = lean_usize_add(v_i_1528_, v___x_1558_);
v___x_1560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_1525_, v_as_1526_, v_sz_1527_, v___x_1559_, v___x_1557_, v___y_1530_);
return v___x_1560_;
}
}
}
v___jp_1564_:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1563_, v___x_1525_);
lean_dec(v_ref_1563_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_inc(v___y_1565_);
v___y_1548_ = v___y_1565_;
v___y_1549_ = v___y_1565_;
goto v___jp_1547_;
}
else
{
lean_object* v_val_1567_; 
v_val_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_val_1567_);
lean_dec_ref(v___x_1566_);
v___y_1548_ = v___y_1565_;
v___y_1549_ = v_val_1567_;
goto v___jp_1547_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40___boxed(lean_object* v___x_1574_, lean_object* v_as_1575_, lean_object* v_sz_1576_, lean_object* v_i_1577_, lean_object* v_b_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
uint8_t v___x_37805__boxed_1582_; size_t v_sz_boxed_1583_; size_t v_i_boxed_1584_; lean_object* v_res_1585_; 
v___x_37805__boxed_1582_ = lean_unbox(v___x_1574_);
v_sz_boxed_1583_ = lean_unbox_usize(v_sz_1576_);
lean_dec(v_sz_1576_);
v_i_boxed_1584_ = lean_unbox_usize(v_i_1577_);
lean_dec(v_i_1577_);
v_res_1585_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_37805__boxed_1582_, v_as_1575_, v_sz_boxed_1583_, v_i_boxed_1584_, v_b_1578_, v___y_1579_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec_ref(v_as_1575_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(lean_object* v_init_1586_, uint8_t v___x_1587_, lean_object* v_n_1588_, lean_object* v_b_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
if (lean_obj_tag(v_n_1588_) == 0)
{
lean_object* v_cs_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1627_; 
v_cs_1593_ = lean_ctor_get(v_n_1588_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v_n_1588_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1595_ = v_n_1588_;
v_isShared_1596_ = v_isSharedCheck_1627_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_cs_1593_);
lean_dec(v_n_1588_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1627_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; size_t v_sz_1599_; size_t v___x_1600_; lean_object* v___x_1601_; 
v___x_1597_ = lean_box(0);
v___x_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
lean_ctor_set(v___x_1598_, 1, v_b_1589_);
v_sz_1599_ = lean_array_size(v_cs_1593_);
v___x_1600_ = ((size_t)0ULL);
v___x_1601_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_1586_, v___x_1587_, v_cs_1593_, v_sz_1599_, v___x_1600_, v___x_1598_, v___y_1590_, v___y_1591_);
lean_dec_ref(v_cs_1593_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1618_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1604_ = v___x_1601_;
v_isShared_1605_ = v_isSharedCheck_1618_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1601_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1618_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v_fst_1606_; 
v_fst_1606_ = lean_ctor_get(v_a_1602_, 0);
if (lean_obj_tag(v_fst_1606_) == 0)
{
lean_object* v_snd_1607_; lean_object* v___x_1609_; 
v_snd_1607_ = lean_ctor_get(v_a_1602_, 1);
lean_inc(v_snd_1607_);
lean_dec(v_a_1602_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set_tag(v___x_1595_, 1);
lean_ctor_set(v___x_1595_, 0, v_snd_1607_);
v___x_1609_ = v___x_1595_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_snd_1607_);
v___x_1609_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1611_; 
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___x_1609_);
v___x_1611_ = v___x_1604_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1609_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
else
{
lean_object* v_val_1614_; lean_object* v___x_1616_; 
lean_inc_ref(v_fst_1606_);
lean_dec(v_a_1602_);
lean_del_object(v___x_1595_);
v_val_1614_ = lean_ctor_get(v_fst_1606_, 0);
lean_inc(v_val_1614_);
lean_dec_ref(v_fst_1606_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v_val_1614_);
v___x_1616_ = v___x_1604_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_val_1614_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_del_object(v___x_1595_);
v_a_1619_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1601_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1601_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
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
}
else
{
lean_object* v_vs_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1662_; 
v_vs_1628_ = lean_ctor_get(v_n_1588_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v_n_1588_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1630_ = v_n_1588_;
v_isShared_1631_ = v_isSharedCheck_1662_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_vs_1628_);
lean_dec(v_n_1588_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1662_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; size_t v_sz_1634_; size_t v___x_1635_; lean_object* v___x_1636_; 
v___x_1632_ = lean_box(0);
v___x_1633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
lean_ctor_set(v___x_1633_, 1, v_b_1589_);
v_sz_1634_ = lean_array_size(v_vs_1628_);
v___x_1635_ = ((size_t)0ULL);
v___x_1636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_1587_, v_vs_1628_, v_sz_1634_, v___x_1635_, v___x_1633_, v___y_1590_, v___y_1591_);
lean_dec_ref(v_vs_1628_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1653_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1639_ = v___x_1636_;
v_isShared_1640_ = v_isSharedCheck_1653_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1636_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1653_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v_fst_1641_; 
v_fst_1641_ = lean_ctor_get(v_a_1637_, 0);
if (lean_obj_tag(v_fst_1641_) == 0)
{
lean_object* v_snd_1642_; lean_object* v___x_1644_; 
v_snd_1642_ = lean_ctor_get(v_a_1637_, 1);
lean_inc(v_snd_1642_);
lean_dec(v_a_1637_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 0, v_snd_1642_);
v___x_1644_ = v___x_1630_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_snd_1642_);
v___x_1644_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
lean_object* v___x_1646_; 
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 0, v___x_1644_);
v___x_1646_ = v___x_1639_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
else
{
lean_object* v_val_1649_; lean_object* v___x_1651_; 
lean_inc_ref(v_fst_1641_);
lean_dec(v_a_1637_);
lean_del_object(v___x_1630_);
v_val_1649_ = lean_ctor_get(v_fst_1641_, 0);
lean_inc(v_val_1649_);
lean_dec_ref(v_fst_1641_);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 0, v_val_1649_);
v___x_1651_ = v___x_1639_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_val_1649_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
lean_del_object(v___x_1630_);
v_a_1654_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v___x_1636_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1636_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(lean_object* v_init_1663_, uint8_t v___x_1664_, lean_object* v_as_1665_, size_t v_sz_1666_, size_t v_i_1667_, lean_object* v_b_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
uint8_t v___x_1672_; 
v___x_1672_ = lean_usize_dec_lt(v_i_1667_, v_sz_1666_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1673_; 
v___x_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1673_, 0, v_b_1668_);
return v___x_1673_;
}
else
{
lean_object* v_snd_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1708_; 
v_snd_1674_ = lean_ctor_get(v_b_1668_, 1);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_b_1668_);
if (v_isSharedCheck_1708_ == 0)
{
lean_object* v_unused_1709_; 
v_unused_1709_ = lean_ctor_get(v_b_1668_, 0);
lean_dec(v_unused_1709_);
v___x_1676_ = v_b_1668_;
v_isShared_1677_ = v_isSharedCheck_1708_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_snd_1674_);
lean_dec(v_b_1668_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1708_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v_a_1678_; lean_object* v___x_1679_; 
v_a_1678_ = lean_array_uget_borrowed(v_as_1665_, v_i_1667_);
lean_inc(v_snd_1674_);
lean_inc(v_a_1678_);
v___x_1679_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1663_, v___x_1664_, v_a_1678_, v_snd_1674_, v___y_1669_, v___y_1670_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1699_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1682_ = v___x_1679_;
v_isShared_1683_ = v_isSharedCheck_1699_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1679_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1699_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
if (lean_obj_tag(v_a_1680_) == 0)
{
lean_object* v___x_1684_; lean_object* v___x_1686_; 
v___x_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1684_, 0, v_a_1680_);
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 0, v___x_1684_);
v___x_1686_ = v___x_1676_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v_snd_1674_);
v___x_1686_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
lean_object* v___x_1688_; 
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 0, v___x_1686_);
v___x_1688_ = v___x_1682_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1692_; lean_object* v___x_1694_; 
lean_del_object(v___x_1682_);
lean_dec(v_snd_1674_);
v_a_1691_ = lean_ctor_get(v_a_1680_, 0);
lean_inc(v_a_1691_);
lean_dec_ref(v_a_1680_);
v___x_1692_ = lean_box(0);
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 1, v_a_1691_);
lean_ctor_set(v___x_1676_, 0, v___x_1692_);
v___x_1694_ = v___x_1676_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1692_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_a_1691_);
v___x_1694_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
size_t v___x_1695_; size_t v___x_1696_; 
v___x_1695_ = ((size_t)1ULL);
v___x_1696_ = lean_usize_add(v_i_1667_, v___x_1695_);
v_i_1667_ = v___x_1696_;
v_b_1668_ = v___x_1694_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
lean_del_object(v___x_1676_);
lean_dec(v_snd_1674_);
v_a_1700_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v___x_1679_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1679_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1700_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39___boxed(lean_object* v_init_1710_, lean_object* v___x_1711_, lean_object* v_as_1712_, lean_object* v_sz_1713_, lean_object* v_i_1714_, lean_object* v_b_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
uint8_t v___x_37886__boxed_1719_; size_t v_sz_boxed_1720_; size_t v_i_boxed_1721_; lean_object* v_res_1722_; 
v___x_37886__boxed_1719_ = lean_unbox(v___x_1711_);
v_sz_boxed_1720_ = lean_unbox_usize(v_sz_1713_);
lean_dec(v_sz_1713_);
v_i_boxed_1721_ = lean_unbox_usize(v_i_1714_);
lean_dec(v_i_1714_);
v_res_1722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_1710_, v___x_37886__boxed_1719_, v_as_1712_, v_sz_boxed_1720_, v_i_boxed_1721_, v_b_1715_, v___y_1716_, v___y_1717_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec_ref(v_as_1712_);
lean_dec_ref(v_init_1710_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27___boxed(lean_object* v_init_1723_, lean_object* v___x_1724_, lean_object* v_n_1725_, lean_object* v_b_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
uint8_t v___x_37906__boxed_1730_; lean_object* v_res_1731_; 
v___x_37906__boxed_1730_ = lean_unbox(v___x_1724_);
v_res_1731_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1723_, v___x_37906__boxed_1730_, v_n_1725_, v_b_1726_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec_ref(v_init_1723_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(uint8_t v___x_1732_, lean_object* v_as_1733_, size_t v_sz_1734_, size_t v_i_1735_, lean_object* v_b_1736_, lean_object* v___y_1737_){
_start:
{
uint8_t v___x_1739_; 
v___x_1739_ = lean_usize_dec_lt(v_i_1735_, v_sz_1734_);
if (v___x_1739_ == 0)
{
lean_object* v___x_1740_; 
v___x_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1740_, 0, v_b_1736_);
return v___x_1740_;
}
else
{
lean_object* v_snd_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1778_; 
v_snd_1741_ = lean_ctor_get(v_b_1736_, 1);
v_isSharedCheck_1778_ = !lean_is_exclusive(v_b_1736_);
if (v_isSharedCheck_1778_ == 0)
{
lean_object* v_unused_1779_; 
v_unused_1779_ = lean_ctor_get(v_b_1736_, 0);
lean_dec(v_unused_1779_);
v___x_1743_ = v_b_1736_;
v_isShared_1744_ = v_isSharedCheck_1778_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_snd_1741_);
lean_dec(v_b_1736_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1778_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v_ref_1745_; lean_object* v_a_1746_; lean_object* v_ref_1747_; lean_object* v_msg_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1777_; 
v_ref_1745_ = lean_ctor_get(v___y_1737_, 5);
v_a_1746_ = lean_array_uget(v_as_1733_, v_i_1735_);
v_ref_1747_ = lean_ctor_get(v_a_1746_, 0);
v_msg_1748_ = lean_ctor_get(v_a_1746_, 1);
v_isSharedCheck_1777_ = !lean_is_exclusive(v_a_1746_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1750_ = v_a_1746_;
v_isShared_1751_ = v_isSharedCheck_1777_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_msg_1748_);
lean_inc(v_ref_1747_);
lean_dec(v_a_1746_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1777_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1752_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v_ref_1769_; lean_object* v___y_1771_; lean_object* v___x_1774_; 
v___x_1752_ = lean_box(0);
v_ref_1769_ = l_Lean_replaceRef(v_ref_1747_, v_ref_1745_);
lean_dec(v_ref_1747_);
v___x_1774_ = l_Lean_Syntax_getPos_x3f(v_ref_1769_, v___x_1732_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v___x_1775_; 
v___x_1775_ = lean_unsigned_to_nat(0u);
v___y_1771_ = v___x_1775_;
goto v___jp_1770_;
}
else
{
lean_object* v_val_1776_; 
v_val_1776_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_val_1776_);
lean_dec_ref(v___x_1774_);
v___y_1771_ = v_val_1776_;
goto v___jp_1770_;
}
v___jp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 1, v___y_1755_);
lean_ctor_set(v___x_1743_, 0, v___y_1754_);
v___x_1757_ = v___x_1743_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___y_1754_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v___y_1755_);
v___x_1757_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v_pos2traces_1761_; lean_object* v___x_1763_; 
v___x_1758_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1759_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1741_, v___x_1757_, v___x_1758_);
v___x_1760_ = lean_array_push(v___x_1759_, v_msg_1748_);
v_pos2traces_1761_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1741_, v___x_1757_, v___x_1760_);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 1, v_pos2traces_1761_);
lean_ctor_set(v___x_1750_, 0, v___x_1752_);
v___x_1763_ = v___x_1750_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1752_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_pos2traces_1761_);
v___x_1763_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
size_t v___x_1764_; size_t v___x_1765_; 
v___x_1764_ = ((size_t)1ULL);
v___x_1765_ = lean_usize_add(v_i_1735_, v___x_1764_);
v_i_1735_ = v___x_1765_;
v_b_1736_ = v___x_1763_;
goto _start;
}
}
}
v___jp_1770_:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1769_, v___x_1732_);
lean_dec(v_ref_1769_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_inc(v___y_1771_);
v___y_1754_ = v___y_1771_;
v___y_1755_ = v___y_1771_;
goto v___jp_1753_;
}
else
{
lean_object* v_val_1773_; 
v_val_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_val_1773_);
lean_dec_ref(v___x_1772_);
v___y_1754_ = v___y_1771_;
v___y_1755_ = v_val_1773_;
goto v___jp_1753_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg___boxed(lean_object* v___x_1780_, lean_object* v_as_1781_, lean_object* v_sz_1782_, lean_object* v_i_1783_, lean_object* v_b_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
uint8_t v___x_38113__boxed_1787_; size_t v_sz_boxed_1788_; size_t v_i_boxed_1789_; lean_object* v_res_1790_; 
v___x_38113__boxed_1787_ = lean_unbox(v___x_1780_);
v_sz_boxed_1788_ = lean_unbox_usize(v_sz_1782_);
lean_dec(v_sz_1782_);
v_i_boxed_1789_ = lean_unbox_usize(v_i_1783_);
lean_dec(v_i_1783_);
v_res_1790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_38113__boxed_1787_, v_as_1781_, v_sz_boxed_1788_, v_i_boxed_1789_, v_b_1784_, v___y_1785_);
lean_dec_ref(v___y_1785_);
lean_dec_ref(v_as_1781_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(uint8_t v___x_1791_, lean_object* v_as_1792_, size_t v_sz_1793_, size_t v_i_1794_, lean_object* v_b_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
uint8_t v___x_1799_; 
v___x_1799_ = lean_usize_dec_lt(v_i_1794_, v_sz_1793_);
if (v___x_1799_ == 0)
{
lean_object* v___x_1800_; 
v___x_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1800_, 0, v_b_1795_);
return v___x_1800_;
}
else
{
lean_object* v_snd_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1838_; 
v_snd_1801_ = lean_ctor_get(v_b_1795_, 1);
v_isSharedCheck_1838_ = !lean_is_exclusive(v_b_1795_);
if (v_isSharedCheck_1838_ == 0)
{
lean_object* v_unused_1839_; 
v_unused_1839_ = lean_ctor_get(v_b_1795_, 0);
lean_dec(v_unused_1839_);
v___x_1803_ = v_b_1795_;
v_isShared_1804_ = v_isSharedCheck_1838_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_snd_1801_);
lean_dec(v_b_1795_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1838_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v_ref_1805_; lean_object* v_a_1806_; lean_object* v_ref_1807_; lean_object* v_msg_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1837_; 
v_ref_1805_ = lean_ctor_get(v___y_1796_, 5);
v_a_1806_ = lean_array_uget(v_as_1792_, v_i_1794_);
v_ref_1807_ = lean_ctor_get(v_a_1806_, 0);
v_msg_1808_ = lean_ctor_get(v_a_1806_, 1);
v_isSharedCheck_1837_ = !lean_is_exclusive(v_a_1806_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1810_ = v_a_1806_;
v_isShared_1811_ = v_isSharedCheck_1837_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_msg_1808_);
lean_inc(v_ref_1807_);
lean_dec(v_a_1806_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1837_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1812_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v_ref_1829_; lean_object* v___y_1831_; lean_object* v___x_1834_; 
v___x_1812_ = lean_box(0);
v_ref_1829_ = l_Lean_replaceRef(v_ref_1807_, v_ref_1805_);
lean_dec(v_ref_1807_);
v___x_1834_ = l_Lean_Syntax_getPos_x3f(v_ref_1829_, v___x_1791_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v___x_1835_; 
v___x_1835_ = lean_unsigned_to_nat(0u);
v___y_1831_ = v___x_1835_;
goto v___jp_1830_;
}
else
{
lean_object* v_val_1836_; 
v_val_1836_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_val_1836_);
lean_dec_ref(v___x_1834_);
v___y_1831_ = v_val_1836_;
goto v___jp_1830_;
}
v___jp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 1, v___y_1815_);
lean_ctor_set(v___x_1803_, 0, v___y_1814_);
v___x_1817_ = v___x_1803_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___y_1814_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v___y_1815_);
v___x_1817_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v_pos2traces_1821_; lean_object* v___x_1823_; 
v___x_1818_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1819_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1801_, v___x_1817_, v___x_1818_);
v___x_1820_ = lean_array_push(v___x_1819_, v_msg_1808_);
v_pos2traces_1821_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1801_, v___x_1817_, v___x_1820_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 1, v_pos2traces_1821_);
lean_ctor_set(v___x_1810_, 0, v___x_1812_);
v___x_1823_ = v___x_1810_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1812_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_pos2traces_1821_);
v___x_1823_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
size_t v___x_1824_; size_t v___x_1825_; lean_object* v___x_1826_; 
v___x_1824_ = ((size_t)1ULL);
v___x_1825_ = lean_usize_add(v_i_1794_, v___x_1824_);
v___x_1826_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_1791_, v_as_1792_, v_sz_1793_, v___x_1825_, v___x_1823_, v___y_1796_);
return v___x_1826_;
}
}
}
v___jp_1830_:
{
lean_object* v___x_1832_; 
v___x_1832_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1829_, v___x_1791_);
lean_dec(v_ref_1829_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_inc(v___y_1831_);
v___y_1814_ = v___y_1831_;
v___y_1815_ = v___y_1831_;
goto v___jp_1813_;
}
else
{
lean_object* v_val_1833_; 
v_val_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_val_1833_);
lean_dec_ref(v___x_1832_);
v___y_1814_ = v___y_1831_;
v___y_1815_ = v_val_1833_;
goto v___jp_1813_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28___boxed(lean_object* v___x_1840_, lean_object* v_as_1841_, lean_object* v_sz_1842_, lean_object* v_i_1843_, lean_object* v_b_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
uint8_t v___x_38193__boxed_1848_; size_t v_sz_boxed_1849_; size_t v_i_boxed_1850_; lean_object* v_res_1851_; 
v___x_38193__boxed_1848_ = lean_unbox(v___x_1840_);
v_sz_boxed_1849_ = lean_unbox_usize(v_sz_1842_);
lean_dec(v_sz_1842_);
v_i_boxed_1850_ = lean_unbox_usize(v_i_1843_);
lean_dec(v_i_1843_);
v_res_1851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_38193__boxed_1848_, v_as_1841_, v_sz_boxed_1849_, v_i_boxed_1850_, v_b_1844_, v___y_1845_, v___y_1846_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec_ref(v_as_1841_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(uint8_t v___x_1852_, lean_object* v_t_1853_, lean_object* v_init_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v_root_1858_; lean_object* v_tail_1859_; lean_object* v___x_1860_; 
v_root_1858_ = lean_ctor_get(v_t_1853_, 0);
lean_inc_ref(v_root_1858_);
v_tail_1859_ = lean_ctor_get(v_t_1853_, 1);
lean_inc_ref(v_tail_1859_);
lean_dec_ref(v_t_1853_);
lean_inc_ref(v_init_1854_);
v___x_1860_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1854_, v___x_1852_, v_root_1858_, v_init_1854_, v___y_1855_, v___y_1856_);
lean_dec_ref(v_init_1854_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1897_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1897_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1897_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
if (lean_obj_tag(v_a_1861_) == 0)
{
lean_object* v_a_1865_; lean_object* v___x_1867_; 
lean_dec_ref(v_tail_1859_);
v_a_1865_ = lean_ctor_get(v_a_1861_, 0);
lean_inc(v_a_1865_);
lean_dec_ref(v_a_1861_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v_a_1865_);
v___x_1867_ = v___x_1863_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; size_t v_sz_1872_; size_t v___x_1873_; lean_object* v___x_1874_; 
lean_del_object(v___x_1863_);
v_a_1869_ = lean_ctor_get(v_a_1861_, 0);
lean_inc(v_a_1869_);
lean_dec_ref(v_a_1861_);
v___x_1870_ = lean_box(0);
v___x_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
lean_ctor_set(v___x_1871_, 1, v_a_1869_);
v_sz_1872_ = lean_array_size(v_tail_1859_);
v___x_1873_ = ((size_t)0ULL);
v___x_1874_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_1852_, v_tail_1859_, v_sz_1872_, v___x_1873_, v___x_1871_, v___y_1855_, v___y_1856_);
lean_dec_ref(v_tail_1859_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1888_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1877_ = v___x_1874_;
v_isShared_1878_ = v_isSharedCheck_1888_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1874_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1888_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v_fst_1879_; 
v_fst_1879_ = lean_ctor_get(v_a_1875_, 0);
if (lean_obj_tag(v_fst_1879_) == 0)
{
lean_object* v_snd_1880_; lean_object* v___x_1882_; 
v_snd_1880_ = lean_ctor_get(v_a_1875_, 1);
lean_inc(v_snd_1880_);
lean_dec(v_a_1875_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v_snd_1880_);
v___x_1882_ = v___x_1877_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_snd_1880_);
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
lean_object* v_val_1884_; lean_object* v___x_1886_; 
lean_inc_ref(v_fst_1879_);
lean_dec(v_a_1875_);
v_val_1884_ = lean_ctor_get(v_fst_1879_, 0);
lean_inc(v_val_1884_);
lean_dec_ref(v_fst_1879_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v_val_1884_);
v___x_1886_ = v___x_1877_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_val_1884_);
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
else
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
v_a_1889_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1891_ = v___x_1874_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1874_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1889_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec_ref(v_tail_1859_);
v_a_1898_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1860_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1860_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19___boxed(lean_object* v___x_1906_, lean_object* v_t_1907_, lean_object* v_init_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
uint8_t v___x_38274__boxed_1912_; lean_object* v_res_1913_; 
v___x_38274__boxed_1912_ = lean_unbox(v___x_1906_);
v_res_1913_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_38274__boxed_1912_, v_t_1907_, v_init_1908_, v___y_1909_, v___y_1910_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(lean_object* v_x_1914_, lean_object* v_x_1915_){
_start:
{
if (lean_obj_tag(v_x_1915_) == 0)
{
return v_x_1914_;
}
else
{
lean_object* v_key_1916_; lean_object* v_value_1917_; lean_object* v_tail_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v_key_1916_ = lean_ctor_get(v_x_1915_, 0);
v_value_1917_ = lean_ctor_get(v_x_1915_, 1);
v_tail_1918_ = lean_ctor_get(v_x_1915_, 2);
lean_inc(v_value_1917_);
lean_inc(v_key_1916_);
v___x_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1919_, 0, v_key_1916_);
lean_ctor_set(v___x_1919_, 1, v_value_1917_);
v___x_1920_ = lean_array_push(v_x_1914_, v___x_1919_);
v_x_1914_ = v___x_1920_;
v_x_1915_ = v_tail_1918_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22___boxed(lean_object* v_x_1922_, lean_object* v_x_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_x_1922_, v_x_1923_);
lean_dec(v_x_1923_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(lean_object* v_as_1925_, size_t v_i_1926_, size_t v_stop_1927_, lean_object* v_b_1928_){
_start:
{
uint8_t v___x_1929_; 
v___x_1929_ = lean_usize_dec_eq(v_i_1926_, v_stop_1927_);
if (v___x_1929_ == 0)
{
lean_object* v___x_1930_; lean_object* v___x_1931_; size_t v___x_1932_; size_t v___x_1933_; 
v___x_1930_ = lean_array_uget_borrowed(v_as_1925_, v_i_1926_);
v___x_1931_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_b_1928_, v___x_1930_);
v___x_1932_ = ((size_t)1ULL);
v___x_1933_ = lean_usize_add(v_i_1926_, v___x_1932_);
v_i_1926_ = v___x_1933_;
v_b_1928_ = v___x_1931_;
goto _start;
}
else
{
return v_b_1928_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23___boxed(lean_object* v_as_1935_, lean_object* v_i_1936_, lean_object* v_stop_1937_, lean_object* v_b_1938_){
_start:
{
size_t v_i_boxed_1939_; size_t v_stop_boxed_1940_; lean_object* v_res_1941_; 
v_i_boxed_1939_ = lean_unbox_usize(v_i_1936_);
lean_dec(v_i_1936_);
v_stop_boxed_1940_ = lean_unbox_usize(v_stop_1937_);
lean_dec(v_stop_1937_);
v_res_1941_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_as_1935_, v_i_boxed_1939_, v_stop_boxed_1940_, v_b_1938_);
lean_dec_ref(v_as_1935_);
return v_res_1941_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0(void){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1942_ = lean_unsigned_to_nat(32u);
v___x_1943_ = lean_mk_empty_array_with_capacity(v___x_1942_);
v___x_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
return v___x_1944_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1(void){
_start:
{
size_t v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1945_ = ((size_t)5ULL);
v___x_1946_ = lean_unsigned_to_nat(0u);
v___x_1947_ = lean_unsigned_to_nat(32u);
v___x_1948_ = lean_mk_empty_array_with_capacity(v___x_1947_);
v___x_1949_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0);
v___x_1950_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
lean_ctor_set(v___x_1950_, 1, v___x_1948_);
lean_ctor_set(v___x_1950_, 2, v___x_1946_);
lean_ctor_set(v___x_1950_, 3, v___x_1946_);
lean_ctor_set_usize(v___x_1950_, 4, v___x_1945_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(lean_object* v___y_1951_){
_start:
{
lean_object* v___x_1953_; lean_object* v_traceState_1954_; lean_object* v_traces_1955_; lean_object* v___x_1956_; lean_object* v_traceState_1957_; lean_object* v_env_1958_; lean_object* v_nextMacroScope_1959_; lean_object* v_ngen_1960_; lean_object* v_auxDeclNGen_1961_; lean_object* v_cache_1962_; lean_object* v_messages_1963_; lean_object* v_infoState_1964_; lean_object* v_snapshotTasks_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1984_; 
v___x_1953_ = lean_st_ref_get(v___y_1951_);
v_traceState_1954_ = lean_ctor_get(v___x_1953_, 4);
lean_inc_ref(v_traceState_1954_);
lean_dec(v___x_1953_);
v_traces_1955_ = lean_ctor_get(v_traceState_1954_, 0);
lean_inc_ref(v_traces_1955_);
lean_dec_ref(v_traceState_1954_);
v___x_1956_ = lean_st_ref_take(v___y_1951_);
v_traceState_1957_ = lean_ctor_get(v___x_1956_, 4);
v_env_1958_ = lean_ctor_get(v___x_1956_, 0);
v_nextMacroScope_1959_ = lean_ctor_get(v___x_1956_, 1);
v_ngen_1960_ = lean_ctor_get(v___x_1956_, 2);
v_auxDeclNGen_1961_ = lean_ctor_get(v___x_1956_, 3);
v_cache_1962_ = lean_ctor_get(v___x_1956_, 5);
v_messages_1963_ = lean_ctor_get(v___x_1956_, 6);
v_infoState_1964_ = lean_ctor_get(v___x_1956_, 7);
v_snapshotTasks_1965_ = lean_ctor_get(v___x_1956_, 8);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1967_ = v___x_1956_;
v_isShared_1968_ = v_isSharedCheck_1984_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_snapshotTasks_1965_);
lean_inc(v_infoState_1964_);
lean_inc(v_messages_1963_);
lean_inc(v_cache_1962_);
lean_inc(v_traceState_1957_);
lean_inc(v_auxDeclNGen_1961_);
lean_inc(v_ngen_1960_);
lean_inc(v_nextMacroScope_1959_);
lean_inc(v_env_1958_);
lean_dec(v___x_1956_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1984_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
uint64_t v_tid_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1982_; 
v_tid_1969_ = lean_ctor_get_uint64(v_traceState_1957_, sizeof(void*)*1);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_traceState_1957_);
if (v_isSharedCheck_1982_ == 0)
{
lean_object* v_unused_1983_; 
v_unused_1983_ = lean_ctor_get(v_traceState_1957_, 0);
lean_dec(v_unused_1983_);
v___x_1971_ = v_traceState_1957_;
v_isShared_1972_ = v_isSharedCheck_1982_;
goto v_resetjp_1970_;
}
else
{
lean_dec(v_traceState_1957_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1982_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1973_; lean_object* v___x_1975_; 
v___x_1973_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 0, v___x_1973_);
v___x_1975_ = v___x_1971_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1973_);
lean_ctor_set_uint64(v_reuseFailAlloc_1981_, sizeof(void*)*1, v_tid_1969_);
v___x_1975_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
lean_object* v___x_1977_; 
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 4, v___x_1975_);
v___x_1977_ = v___x_1967_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_env_1958_);
lean_ctor_set(v_reuseFailAlloc_1980_, 1, v_nextMacroScope_1959_);
lean_ctor_set(v_reuseFailAlloc_1980_, 2, v_ngen_1960_);
lean_ctor_set(v_reuseFailAlloc_1980_, 3, v_auxDeclNGen_1961_);
lean_ctor_set(v_reuseFailAlloc_1980_, 4, v___x_1975_);
lean_ctor_set(v_reuseFailAlloc_1980_, 5, v_cache_1962_);
lean_ctor_set(v_reuseFailAlloc_1980_, 6, v_messages_1963_);
lean_ctor_set(v_reuseFailAlloc_1980_, 7, v_infoState_1964_);
lean_ctor_set(v_reuseFailAlloc_1980_, 8, v_snapshotTasks_1965_);
v___x_1977_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = lean_st_ref_set(v___y_1951_, v___x_1977_);
v___x_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1979_, 0, v_traces_1955_);
return v___x_1979_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___boxed(lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_1985_);
lean_dec(v___y_1985_);
return v_res_1987_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(lean_object* v_x_1988_, lean_object* v_x_1989_){
_start:
{
lean_object* v_fst_1990_; lean_object* v_fst_1991_; lean_object* v_fst_1992_; lean_object* v_fst_1993_; uint8_t v___x_1994_; 
v_fst_1990_ = lean_ctor_get(v_x_1988_, 0);
v_fst_1991_ = lean_ctor_get(v_x_1989_, 0);
v_fst_1992_ = lean_ctor_get(v_fst_1990_, 0);
v_fst_1993_ = lean_ctor_get(v_fst_1991_, 0);
v___x_1994_ = lean_nat_dec_lt(v_fst_1992_, v_fst_1993_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0___boxed(lean_object* v_x_1995_, lean_object* v_x_1996_){
_start:
{
uint8_t v_res_1997_; lean_object* v_r_1998_; 
v_res_1997_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v_x_1995_, v_x_1996_);
lean_dec_ref(v_x_1996_);
lean_dec_ref(v_x_1995_);
v_r_1998_ = lean_box(v_res_1997_);
return v_r_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(lean_object* v_as_2000_, lean_object* v_lo_2001_, lean_object* v_hi_2002_){
_start:
{
uint8_t v___x_2003_; 
v___x_2003_ = lean_nat_dec_lt(v_lo_2001_, v_hi_2002_);
if (v___x_2003_ == 0)
{
lean_dec(v_lo_2001_);
return v_as_2000_;
}
else
{
lean_object* v___f_2004_; lean_object* v___x_2005_; lean_object* v_fst_2006_; lean_object* v_snd_2007_; uint8_t v___x_2008_; 
v___f_2004_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___closed__0));
lean_inc(v_lo_2001_);
v___x_2005_ = l_Array_qpartition___redArg(v_as_2000_, v___f_2004_, v_lo_2001_, v_hi_2002_);
v_fst_2006_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_fst_2006_);
v_snd_2007_ = lean_ctor_get(v___x_2005_, 1);
lean_inc(v_snd_2007_);
lean_dec_ref(v___x_2005_);
v___x_2008_ = lean_nat_dec_le(v_hi_2002_, v_fst_2006_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2009_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_snd_2007_, v_lo_2001_, v_fst_2006_);
v___x_2010_ = lean_unsigned_to_nat(1u);
v___x_2011_ = lean_nat_add(v_fst_2006_, v___x_2010_);
lean_dec(v_fst_2006_);
v_as_2000_ = v___x_2009_;
v_lo_2001_ = v___x_2011_;
goto _start;
}
else
{
lean_dec(v_fst_2006_);
lean_dec(v_lo_2001_);
return v_snd_2007_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___boxed(lean_object* v_as_2013_, lean_object* v_lo_2014_, lean_object* v_hi_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_as_2013_, v_lo_2014_, v_hi_2015_);
lean_dec(v_hi_2015_);
return v_res_2016_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2017_ = lean_box(0);
v___x_2018_ = lean_unsigned_to_nat(16u);
v___x_2019_ = lean_mk_array(v___x_2018_, v___x_2017_);
return v___x_2019_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1(void){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v_pos2traces_2022_; 
v___x_2020_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0);
v___x_2021_ = lean_unsigned_to_nat(0u);
v_pos2traces_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_2022_, 0, v___x_2021_);
lean_ctor_set(v_pos2traces_2022_, 1, v___x_2020_);
return v_pos2traces_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10(lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_options_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v_options_2026_ = lean_ctor_get(v___y_2023_, 2);
v___x_2027_ = l_Lean_trace_profiler_output;
v___x_2028_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(v_options_2026_, v___x_2027_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v___x_2029_; lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2096_; 
v___x_2029_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_2024_);
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2032_ = v___x_2029_;
v_isShared_2033_ = v_isSharedCheck_2096_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2029_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2096_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
uint8_t v___x_2034_; 
v___x_2034_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_2030_);
if (v___x_2034_ == 0)
{
lean_object* v___x_2035_; lean_object* v_pos2traces_2036_; lean_object* v___x_2037_; 
lean_del_object(v___x_2032_);
v___x_2035_ = lean_unsigned_to_nat(0u);
v_pos2traces_2036_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1);
v___x_2037_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_2034_, v_a_2030_, v_pos2traces_2036_, v___y_2023_, v___y_2024_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v___y_2040_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v___y_2066_; lean_object* v_size_2072_; lean_object* v_buckets_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2038_);
lean_dec_ref(v___x_2037_);
v_size_2072_ = lean_ctor_get(v_a_2038_, 0);
lean_inc(v_size_2072_);
v_buckets_2073_ = lean_ctor_get(v_a_2038_, 1);
lean_inc_ref(v_buckets_2073_);
lean_dec(v_a_2038_);
v___x_2074_ = lean_mk_empty_array_with_capacity(v_size_2072_);
lean_dec(v_size_2072_);
v___x_2075_ = lean_array_get_size(v_buckets_2073_);
v___x_2076_ = lean_nat_dec_lt(v___x_2035_, v___x_2075_);
if (v___x_2076_ == 0)
{
lean_dec_ref(v_buckets_2073_);
v___y_2066_ = v___x_2074_;
goto v___jp_2065_;
}
else
{
uint8_t v___x_2077_; 
v___x_2077_ = lean_nat_dec_le(v___x_2075_, v___x_2075_);
if (v___x_2077_ == 0)
{
if (v___x_2076_ == 0)
{
lean_dec_ref(v_buckets_2073_);
v___y_2066_ = v___x_2074_;
goto v___jp_2065_;
}
else
{
size_t v___x_2078_; size_t v___x_2079_; lean_object* v___x_2080_; 
v___x_2078_ = ((size_t)0ULL);
v___x_2079_ = lean_usize_of_nat(v___x_2075_);
v___x_2080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_buckets_2073_, v___x_2078_, v___x_2079_, v___x_2074_);
lean_dec_ref(v_buckets_2073_);
v___y_2066_ = v___x_2080_;
goto v___jp_2065_;
}
}
else
{
size_t v___x_2081_; size_t v___x_2082_; lean_object* v___x_2083_; 
v___x_2081_ = ((size_t)0ULL);
v___x_2082_ = lean_usize_of_nat(v___x_2075_);
v___x_2083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_buckets_2073_, v___x_2081_, v___x_2082_, v___x_2074_);
lean_dec_ref(v_buckets_2073_);
v___y_2066_ = v___x_2083_;
goto v___jp_2065_;
}
}
v___jp_2039_:
{
lean_object* v___x_2041_; size_t v_sz_2042_; size_t v___x_2043_; lean_object* v___x_2044_; 
v___x_2041_ = lean_box(0);
v_sz_2042_ = lean_array_size(v___y_2040_);
v___x_2043_ = ((size_t)0ULL);
v___x_2044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_2034_, v___y_2040_, v_sz_2042_, v___x_2043_, v___x_2041_, v___y_2023_, v___y_2024_);
lean_dec_ref(v___y_2040_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; 
v_unused_2052_ = lean_ctor_get(v___x_2044_, 0);
lean_dec(v_unused_2052_);
v___x_2046_ = v___x_2044_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_dec(v___x_2044_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 0, v___x_2041_);
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2041_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
else
{
return v___x_2044_;
}
}
v___jp_2053_:
{
lean_object* v___x_2058_; 
lean_dec(v___y_2055_);
v___x_2058_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v___y_2056_, v___y_2054_, v___y_2057_);
lean_dec(v___y_2057_);
v___y_2040_ = v___x_2058_;
goto v___jp_2039_;
}
v___jp_2059_:
{
uint8_t v___x_2064_; 
v___x_2064_ = lean_nat_dec_le(v___y_2063_, v___y_2060_);
if (v___x_2064_ == 0)
{
lean_dec(v___y_2060_);
lean_inc(v___y_2063_);
v___y_2054_ = v___y_2063_;
v___y_2055_ = v___y_2061_;
v___y_2056_ = v___y_2062_;
v___y_2057_ = v___y_2063_;
goto v___jp_2053_;
}
else
{
v___y_2054_ = v___y_2063_;
v___y_2055_ = v___y_2061_;
v___y_2056_ = v___y_2062_;
v___y_2057_ = v___y_2060_;
goto v___jp_2053_;
}
}
v___jp_2065_:
{
lean_object* v___x_2067_; uint8_t v___x_2068_; 
v___x_2067_ = lean_array_get_size(v___y_2066_);
v___x_2068_ = lean_nat_dec_eq(v___x_2067_, v___x_2035_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; 
v___x_2069_ = lean_unsigned_to_nat(1u);
v___x_2070_ = lean_nat_sub(v___x_2067_, v___x_2069_);
v___x_2071_ = lean_nat_dec_le(v___x_2035_, v___x_2070_);
if (v___x_2071_ == 0)
{
lean_inc(v___x_2070_);
v___y_2060_ = v___x_2070_;
v___y_2061_ = v___x_2067_;
v___y_2062_ = v___y_2066_;
v___y_2063_ = v___x_2070_;
goto v___jp_2059_;
}
else
{
v___y_2060_ = v___x_2070_;
v___y_2061_ = v___x_2067_;
v___y_2062_ = v___y_2066_;
v___y_2063_ = v___x_2035_;
goto v___jp_2059_;
}
}
else
{
v___y_2040_ = v___y_2066_;
goto v___jp_2039_;
}
}
}
else
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
v_a_2084_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2086_ = v___x_2037_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_2037_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2084_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
else
{
lean_object* v___x_2092_; lean_object* v___x_2094_; 
lean_dec(v_a_2030_);
v___x_2092_ = lean_box(0);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 0, v___x_2092_);
v___x_2094_ = v___x_2032_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2092_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
else
{
lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2104_; 
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2104_ == 0)
{
lean_object* v_unused_2105_; 
v_unused_2105_ = lean_ctor_get(v___x_2028_, 0);
lean_dec(v_unused_2105_);
v___x_2098_ = v___x_2028_;
v_isShared_2099_ = v_isSharedCheck_2104_;
goto v_resetjp_2097_;
}
else
{
lean_dec(v___x_2028_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2104_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2100_; lean_object* v___x_2102_; 
v___x_2100_ = lean_box(0);
if (v_isShared_2099_ == 0)
{
lean_ctor_set_tag(v___x_2098_, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2100_);
v___x_2102_ = v___x_2098_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10___boxed(lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2106_, v___y_2107_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(lean_object* v_as_2110_, size_t v_sz_2111_, size_t v_i_2112_, lean_object* v_b_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
uint8_t v___x_2117_; 
v___x_2117_ = lean_usize_dec_lt(v_i_2112_, v_sz_2111_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; 
v___x_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2118_, 0, v_b_2113_);
return v___x_2118_;
}
else
{
lean_object* v_options_2119_; lean_object* v_a_2120_; lean_object* v___x_2121_; 
v_options_2119_ = lean_ctor_get(v___y_2114_, 2);
v_a_2120_ = lean_array_uget_borrowed(v_as_2110_, v_i_2112_);
lean_inc_ref(v_options_2119_);
lean_inc(v_a_2120_);
v___x_2121_ = l_Lean_Compiler_LCNF_resumeCompilation(v_a_2120_, v_options_2119_, v___y_2114_, v___y_2115_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v___x_2122_; 
lean_dec_ref(v___x_2121_);
v___x_2122_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2114_, v___y_2115_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v___x_2123_; size_t v___x_2124_; size_t v___x_2125_; 
lean_dec_ref(v___x_2122_);
v___x_2123_ = lean_box(0);
v___x_2124_ = ((size_t)1ULL);
v___x_2125_ = lean_usize_add(v_i_2112_, v___x_2124_);
v_i_2112_ = v___x_2125_;
v_b_2113_ = v___x_2123_;
goto _start;
}
else
{
return v___x_2122_;
}
}
else
{
lean_object* v_a_2127_; lean_object* v___x_2128_; 
v_a_2127_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2127_);
lean_dec_ref(v___x_2121_);
v___x_2128_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2114_, v___y_2115_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2135_ == 0)
{
lean_object* v_unused_2136_; 
v_unused_2136_ = lean_ctor_get(v___x_2128_, 0);
lean_dec(v_unused_2136_);
v___x_2130_ = v___x_2128_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_dec(v___x_2128_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
lean_ctor_set_tag(v___x_2130_, 1);
lean_ctor_set(v___x_2130_, 0, v_a_2127_);
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2127_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
else
{
lean_dec(v_a_2127_);
return v___x_2128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11___boxed(lean_object* v_as_2137_, lean_object* v_sz_2138_, lean_object* v_i_2139_, lean_object* v_b_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
size_t v_sz_boxed_2144_; size_t v_i_boxed_2145_; lean_object* v_res_2146_; 
v_sz_boxed_2144_ = lean_unbox_usize(v_sz_2138_);
lean_dec(v_sz_2138_);
v_i_boxed_2145_ = lean_unbox_usize(v_i_2139_);
lean_dec(v_i_2139_);
v_res_2146_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_as_2137_, v_sz_boxed_2144_, v_i_boxed_2145_, v_b_2140_, v___y_2141_, v___y_2142_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec_ref(v_as_2137_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(lean_object* v_as_2147_, size_t v_sz_2148_, size_t v_i_2149_, lean_object* v_b_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
uint8_t v___x_2154_; 
v___x_2154_ = lean_usize_dec_lt(v_i_2149_, v_sz_2148_);
if (v___x_2154_ == 0)
{
lean_object* v___x_2155_; 
v___x_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2155_, 0, v_b_2150_);
return v___x_2155_;
}
else
{
lean_object* v_a_2156_; lean_object* v_declNames_2157_; lean_object* v___x_2158_; size_t v_sz_2159_; size_t v___x_2160_; lean_object* v___x_2161_; 
v_a_2156_ = lean_array_uget_borrowed(v_as_2147_, v_i_2149_);
v_declNames_2157_ = lean_ctor_get(v_a_2156_, 0);
v___x_2158_ = lean_box(0);
v_sz_2159_ = lean_array_size(v_declNames_2157_);
v___x_2160_ = ((size_t)0ULL);
v___x_2161_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_declNames_2157_, v_sz_2159_, v___x_2160_, v___x_2158_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v___x_2162_; 
lean_dec_ref(v___x_2161_);
v___x_2162_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v___y_2152_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; lean_object* v_unreported_2164_; lean_object* v___x_2165_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2163_);
lean_dec_ref(v___x_2162_);
v_unreported_2164_ = lean_ctor_get(v_a_2163_, 1);
lean_inc_ref(v_unreported_2164_);
lean_dec(v_a_2163_);
v___x_2165_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(v_unreported_2164_, v___x_2158_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2165_) == 0)
{
size_t v___x_2166_; size_t v___x_2167_; 
lean_dec_ref(v___x_2165_);
v___x_2166_ = ((size_t)1ULL);
v___x_2167_ = lean_usize_add(v_i_2149_, v___x_2166_);
v_i_2149_ = v___x_2167_;
v_b_2150_ = v___x_2158_;
goto _start;
}
else
{
return v___x_2165_;
}
}
else
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
v_a_2169_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2162_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2162_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
else
{
return v___x_2161_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13___boxed(lean_object* v_as_2177_, lean_object* v_sz_2178_, lean_object* v_i_2179_, lean_object* v_b_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
size_t v_sz_boxed_2184_; size_t v_i_boxed_2185_; lean_object* v_res_2186_; 
v_sz_boxed_2184_ = lean_unbox_usize(v_sz_2178_);
lean_dec(v_sz_2178_);
v_i_boxed_2185_ = lean_unbox_usize(v_i_2179_);
lean_dec(v_i_2179_);
v_res_2186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v_as_2177_, v_sz_boxed_2184_, v_i_boxed_2185_, v_b_2180_, v___y_2181_, v___y_2182_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec_ref(v_as_2177_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object* v_as_2187_, size_t v_i_2188_, size_t v_stop_2189_, lean_object* v_b_2190_){
_start:
{
uint8_t v___x_2191_; 
v___x_2191_ = lean_usize_dec_eq(v_i_2188_, v_stop_2189_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2192_; lean_object* v_name_2193_; lean_object* v___x_2194_; size_t v___x_2195_; size_t v___x_2196_; 
v___x_2192_ = lean_array_uget_borrowed(v_as_2187_, v_i_2188_);
v_name_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_name_2193_);
v___x_2194_ = l_Lean_Compiler_LCNF_setDeclPublic(v_b_2190_, v_name_2193_);
v___x_2195_ = ((size_t)1ULL);
v___x_2196_ = lean_usize_add(v_i_2188_, v___x_2195_);
v_i_2188_ = v___x_2196_;
v_b_2190_ = v___x_2194_;
goto _start;
}
else
{
return v_b_2190_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object* v_as_2198_, lean_object* v_i_2199_, lean_object* v_stop_2200_, lean_object* v_b_2201_){
_start:
{
size_t v_i_boxed_2202_; size_t v_stop_boxed_2203_; lean_object* v_res_2204_; 
v_i_boxed_2202_ = lean_unbox_usize(v_i_2199_);
lean_dec(v_i_2199_);
v_stop_boxed_2203_ = lean_unbox_usize(v_stop_2200_);
lean_dec(v_stop_2200_);
v_res_2204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v_as_2198_, v_i_boxed_2202_, v_stop_boxed_2203_, v_b_2201_);
lean_dec_ref(v_as_2198_);
return v_res_2204_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__43___lam__0(uint8_t v___y_2205_, uint8_t v_suppressElabErrors_2206_, lean_object* v_x_2207_){
_start:
{
if (lean_obj_tag(v_x_2207_) == 1)
{
lean_object* v_pre_2208_; 
v_pre_2208_ = lean_ctor_get(v_x_2207_, 0);
switch(lean_obj_tag(v_pre_2208_))
{
case 1:
{
lean_object* v_pre_2209_; 
v_pre_2209_ = lean_ctor_get(v_pre_2208_, 0);
switch(lean_obj_tag(v_pre_2209_))
{
case 0:
{
lean_object* v_str_2210_; lean_object* v_str_2211_; lean_object* v___x_2212_; uint8_t v___x_2213_; 
v_str_2210_ = lean_ctor_get(v_x_2207_, 1);
v_str_2211_ = lean_ctor_get(v_pre_2208_, 1);
v___x_2212_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0));
v___x_2213_ = lean_string_dec_eq(v_str_2211_, v___x_2212_);
if (v___x_2213_ == 0)
{
lean_object* v___x_2214_; uint8_t v___x_2215_; 
v___x_2214_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1));
v___x_2215_ = lean_string_dec_eq(v_str_2211_, v___x_2214_);
if (v___x_2215_ == 0)
{
return v___y_2205_;
}
else
{
lean_object* v___x_2216_; uint8_t v___x_2217_; 
v___x_2216_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2));
v___x_2217_ = lean_string_dec_eq(v_str_2210_, v___x_2216_);
if (v___x_2217_ == 0)
{
return v___y_2205_;
}
else
{
return v_suppressElabErrors_2206_;
}
}
}
else
{
lean_object* v___x_2218_; uint8_t v___x_2219_; 
v___x_2218_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3));
v___x_2219_ = lean_string_dec_eq(v_str_2210_, v___x_2218_);
if (v___x_2219_ == 0)
{
return v___y_2205_;
}
else
{
return v_suppressElabErrors_2206_;
}
}
}
case 1:
{
lean_object* v_pre_2220_; 
v_pre_2220_ = lean_ctor_get(v_pre_2209_, 0);
if (lean_obj_tag(v_pre_2220_) == 0)
{
lean_object* v_str_2221_; lean_object* v_str_2222_; lean_object* v_str_2223_; lean_object* v___x_2224_; uint8_t v___x_2225_; 
v_str_2221_ = lean_ctor_get(v_x_2207_, 1);
v_str_2222_ = lean_ctor_get(v_pre_2208_, 1);
v_str_2223_ = lean_ctor_get(v_pre_2209_, 1);
v___x_2224_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4));
v___x_2225_ = lean_string_dec_eq(v_str_2223_, v___x_2224_);
if (v___x_2225_ == 0)
{
return v___y_2205_;
}
else
{
lean_object* v___x_2226_; uint8_t v___x_2227_; 
v___x_2226_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5));
v___x_2227_ = lean_string_dec_eq(v_str_2222_, v___x_2226_);
if (v___x_2227_ == 0)
{
return v___y_2205_;
}
else
{
lean_object* v___x_2228_; uint8_t v___x_2229_; 
v___x_2228_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6));
v___x_2229_ = lean_string_dec_eq(v_str_2221_, v___x_2228_);
if (v___x_2229_ == 0)
{
return v___y_2205_;
}
else
{
return v_suppressElabErrors_2206_;
}
}
}
}
else
{
return v___y_2205_;
}
}
default: 
{
return v___y_2205_;
}
}
}
case 0:
{
lean_object* v_str_2230_; lean_object* v___x_2231_; uint8_t v___x_2232_; 
v_str_2230_ = lean_ctor_get(v_x_2207_, 1);
v___x_2231_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_2232_ = lean_string_dec_eq(v_str_2230_, v___x_2231_);
if (v___x_2232_ == 0)
{
return v___y_2205_;
}
else
{
return v_suppressElabErrors_2206_;
}
}
default: 
{
return v___y_2205_;
}
}
}
else
{
return v___y_2205_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__43___lam__0___boxed(lean_object* v___y_2233_, lean_object* v_suppressElabErrors_2234_, lean_object* v_x_2235_){
_start:
{
uint8_t v___y_38816__boxed_2236_; uint8_t v_suppressElabErrors_boxed_2237_; uint8_t v_res_2238_; lean_object* v_r_2239_; 
v___y_38816__boxed_2236_ = lean_unbox(v___y_2233_);
v_suppressElabErrors_boxed_2237_ = lean_unbox(v_suppressElabErrors_2234_);
v_res_2238_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__43___lam__0(v___y_38816__boxed_2236_, v_suppressElabErrors_boxed_2237_, v_x_2235_);
lean_dec(v_x_2235_);
v_r_2239_ = lean_box(v_res_2238_);
return v_r_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__43(lean_object* v_ref_2240_, lean_object* v_msgData_2241_, uint8_t v_severity_2242_, uint8_t v_isSilent_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; uint8_t v___y_2251_; uint8_t v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2284_; uint8_t v___y_2285_; lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2288_; uint8_t v___y_2289_; uint8_t v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2309_; lean_object* v___y_2310_; uint8_t v___y_2311_; lean_object* v___y_2312_; uint8_t v___y_2313_; uint8_t v___y_2314_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___y_2320_; uint8_t v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; uint8_t v___y_2324_; lean_object* v___y_2325_; uint8_t v___y_2326_; uint8_t v___x_2331_; lean_object* v___y_2333_; uint8_t v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; uint8_t v___y_2338_; uint8_t v___y_2339_; uint8_t v___y_2341_; uint8_t v___x_2356_; 
v___x_2331_ = 2;
v___x_2356_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2242_, v___x_2331_);
if (v___x_2356_ == 0)
{
v___y_2341_ = v___x_2356_;
goto v___jp_2340_;
}
else
{
uint8_t v___x_2357_; 
lean_inc_ref(v_msgData_2241_);
v___x_2357_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2241_);
v___y_2341_ = v___x_2357_;
goto v___jp_2340_;
}
v___jp_2247_:
{
lean_object* v___x_2257_; lean_object* v_currNamespace_2258_; lean_object* v_openDecls_2259_; lean_object* v_env_2260_; lean_object* v_nextMacroScope_2261_; lean_object* v_ngen_2262_; lean_object* v_auxDeclNGen_2263_; lean_object* v_traceState_2264_; lean_object* v_cache_2265_; lean_object* v_messages_2266_; lean_object* v_infoState_2267_; lean_object* v_snapshotTasks_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2282_; 
v___x_2257_ = lean_st_ref_take(v___y_2256_);
v_currNamespace_2258_ = lean_ctor_get(v___y_2255_, 6);
v_openDecls_2259_ = lean_ctor_get(v___y_2255_, 7);
v_env_2260_ = lean_ctor_get(v___x_2257_, 0);
v_nextMacroScope_2261_ = lean_ctor_get(v___x_2257_, 1);
v_ngen_2262_ = lean_ctor_get(v___x_2257_, 2);
v_auxDeclNGen_2263_ = lean_ctor_get(v___x_2257_, 3);
v_traceState_2264_ = lean_ctor_get(v___x_2257_, 4);
v_cache_2265_ = lean_ctor_get(v___x_2257_, 5);
v_messages_2266_ = lean_ctor_get(v___x_2257_, 6);
v_infoState_2267_ = lean_ctor_get(v___x_2257_, 7);
v_snapshotTasks_2268_ = lean_ctor_get(v___x_2257_, 8);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2270_ = v___x_2257_;
v_isShared_2271_ = v_isSharedCheck_2282_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_snapshotTasks_2268_);
lean_inc(v_infoState_2267_);
lean_inc(v_messages_2266_);
lean_inc(v_cache_2265_);
lean_inc(v_traceState_2264_);
lean_inc(v_auxDeclNGen_2263_);
lean_inc(v_ngen_2262_);
lean_inc(v_nextMacroScope_2261_);
lean_inc(v_env_2260_);
lean_dec(v___x_2257_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2282_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2277_; 
lean_inc(v_openDecls_2259_);
lean_inc(v_currNamespace_2258_);
v___x_2272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2272_, 0, v_currNamespace_2258_);
lean_ctor_set(v___x_2272_, 1, v_openDecls_2259_);
v___x_2273_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
lean_ctor_set(v___x_2273_, 1, v___y_2253_);
lean_inc_ref(v___y_2248_);
lean_inc_ref(v___y_2249_);
v___x_2274_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2274_, 0, v___y_2249_);
lean_ctor_set(v___x_2274_, 1, v___y_2250_);
lean_ctor_set(v___x_2274_, 2, v___y_2254_);
lean_ctor_set(v___x_2274_, 3, v___y_2248_);
lean_ctor_set(v___x_2274_, 4, v___x_2273_);
lean_ctor_set_uint8(v___x_2274_, sizeof(void*)*5, v___y_2252_);
lean_ctor_set_uint8(v___x_2274_, sizeof(void*)*5 + 1, v___y_2251_);
lean_ctor_set_uint8(v___x_2274_, sizeof(void*)*5 + 2, v_isSilent_2243_);
v___x_2275_ = l_Lean_MessageLog_add(v___x_2274_, v_messages_2266_);
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 6, v___x_2275_);
v___x_2277_ = v___x_2270_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_env_2260_);
lean_ctor_set(v_reuseFailAlloc_2281_, 1, v_nextMacroScope_2261_);
lean_ctor_set(v_reuseFailAlloc_2281_, 2, v_ngen_2262_);
lean_ctor_set(v_reuseFailAlloc_2281_, 3, v_auxDeclNGen_2263_);
lean_ctor_set(v_reuseFailAlloc_2281_, 4, v_traceState_2264_);
lean_ctor_set(v_reuseFailAlloc_2281_, 5, v_cache_2265_);
lean_ctor_set(v_reuseFailAlloc_2281_, 6, v___x_2275_);
lean_ctor_set(v_reuseFailAlloc_2281_, 7, v_infoState_2267_);
lean_ctor_set(v_reuseFailAlloc_2281_, 8, v_snapshotTasks_2268_);
v___x_2277_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2278_ = lean_st_ref_set(v___y_2256_, v___x_2277_);
v___x_2279_ = lean_box(0);
v___x_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
return v___x_2280_;
}
}
}
v___jp_2283_:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2307_; 
v___x_2292_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2241_);
v___x_2293_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v___x_2292_, v___y_2244_, v___y_2245_);
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
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
lean_inc_ref_n(v___y_2286_, 2);
v___x_2298_ = l_Lean_FileMap_toPosition(v___y_2286_, v___y_2288_);
lean_dec(v___y_2288_);
v___x_2299_ = l_Lean_FileMap_toPosition(v___y_2286_, v___y_2291_);
lean_dec(v___y_2291_);
v___x_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
v___x_2301_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1));
if (v___y_2285_ == 0)
{
lean_del_object(v___x_2296_);
lean_dec_ref(v___y_2284_);
v___y_2248_ = v___x_2301_;
v___y_2249_ = v___y_2287_;
v___y_2250_ = v___x_2298_;
v___y_2251_ = v___y_2289_;
v___y_2252_ = v___y_2290_;
v___y_2253_ = v_a_2294_;
v___y_2254_ = v___x_2300_;
v___y_2255_ = v___y_2244_;
v___y_2256_ = v___y_2245_;
goto v___jp_2247_;
}
else
{
uint8_t v___x_2302_; 
lean_inc(v_a_2294_);
v___x_2302_ = l_Lean_MessageData_hasTag(v___y_2284_, v_a_2294_);
if (v___x_2302_ == 0)
{
lean_object* v___x_2303_; lean_object* v___x_2305_; 
lean_dec_ref(v___x_2300_);
lean_dec_ref(v___x_2298_);
lean_dec(v_a_2294_);
v___x_2303_ = lean_box(0);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v___x_2303_);
v___x_2305_ = v___x_2296_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2303_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
else
{
lean_del_object(v___x_2296_);
v___y_2248_ = v___x_2301_;
v___y_2249_ = v___y_2287_;
v___y_2250_ = v___x_2298_;
v___y_2251_ = v___y_2289_;
v___y_2252_ = v___y_2290_;
v___y_2253_ = v_a_2294_;
v___y_2254_ = v___x_2300_;
v___y_2255_ = v___y_2244_;
v___y_2256_ = v___y_2245_;
goto v___jp_2247_;
}
}
}
}
v___jp_2308_:
{
lean_object* v___x_2317_; 
v___x_2317_ = l_Lean_Syntax_getTailPos_x3f(v___y_2315_, v___y_2314_);
lean_dec(v___y_2315_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_inc(v___y_2316_);
v___y_2284_ = v___y_2309_;
v___y_2285_ = v___y_2311_;
v___y_2286_ = v___y_2310_;
v___y_2287_ = v___y_2312_;
v___y_2288_ = v___y_2316_;
v___y_2289_ = v___y_2313_;
v___y_2290_ = v___y_2314_;
v___y_2291_ = v___y_2316_;
goto v___jp_2283_;
}
else
{
lean_object* v_val_2318_; 
v_val_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_val_2318_);
lean_dec_ref(v___x_2317_);
v___y_2284_ = v___y_2309_;
v___y_2285_ = v___y_2311_;
v___y_2286_ = v___y_2310_;
v___y_2287_ = v___y_2312_;
v___y_2288_ = v___y_2316_;
v___y_2289_ = v___y_2313_;
v___y_2290_ = v___y_2314_;
v___y_2291_ = v_val_2318_;
goto v___jp_2283_;
}
}
v___jp_2319_:
{
lean_object* v_ref_2327_; lean_object* v___x_2328_; 
v_ref_2327_ = l_Lean_replaceRef(v_ref_2240_, v___y_2325_);
v___x_2328_ = l_Lean_Syntax_getPos_x3f(v_ref_2327_, v___y_2324_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v___x_2329_; 
v___x_2329_ = lean_unsigned_to_nat(0u);
v___y_2309_ = v___y_2320_;
v___y_2310_ = v___y_2322_;
v___y_2311_ = v___y_2321_;
v___y_2312_ = v___y_2323_;
v___y_2313_ = v___y_2326_;
v___y_2314_ = v___y_2324_;
v___y_2315_ = v_ref_2327_;
v___y_2316_ = v___x_2329_;
goto v___jp_2308_;
}
else
{
lean_object* v_val_2330_; 
v_val_2330_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_val_2330_);
lean_dec_ref(v___x_2328_);
v___y_2309_ = v___y_2320_;
v___y_2310_ = v___y_2322_;
v___y_2311_ = v___y_2321_;
v___y_2312_ = v___y_2323_;
v___y_2313_ = v___y_2326_;
v___y_2314_ = v___y_2324_;
v___y_2315_ = v_ref_2327_;
v___y_2316_ = v_val_2330_;
goto v___jp_2308_;
}
}
v___jp_2332_:
{
if (v___y_2339_ == 0)
{
v___y_2320_ = v___y_2336_;
v___y_2321_ = v___y_2334_;
v___y_2322_ = v___y_2333_;
v___y_2323_ = v___y_2335_;
v___y_2324_ = v___y_2338_;
v___y_2325_ = v___y_2337_;
v___y_2326_ = v_severity_2242_;
goto v___jp_2319_;
}
else
{
v___y_2320_ = v___y_2336_;
v___y_2321_ = v___y_2334_;
v___y_2322_ = v___y_2333_;
v___y_2323_ = v___y_2335_;
v___y_2324_ = v___y_2338_;
v___y_2325_ = v___y_2337_;
v___y_2326_ = v___x_2331_;
goto v___jp_2319_;
}
}
v___jp_2340_:
{
if (v___y_2341_ == 0)
{
lean_object* v_fileName_2342_; lean_object* v_fileMap_2343_; lean_object* v_options_2344_; lean_object* v_ref_2345_; uint8_t v_suppressElabErrors_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___f_2349_; uint8_t v___x_2350_; uint8_t v___x_2351_; 
v_fileName_2342_ = lean_ctor_get(v___y_2244_, 0);
v_fileMap_2343_ = lean_ctor_get(v___y_2244_, 1);
v_options_2344_ = lean_ctor_get(v___y_2244_, 2);
v_ref_2345_ = lean_ctor_get(v___y_2244_, 5);
v_suppressElabErrors_2346_ = lean_ctor_get_uint8(v___y_2244_, sizeof(void*)*14 + 1);
v___x_2347_ = lean_box(v___y_2341_);
v___x_2348_ = lean_box(v_suppressElabErrors_2346_);
v___f_2349_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__43___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2349_, 0, v___x_2347_);
lean_closure_set(v___f_2349_, 1, v___x_2348_);
v___x_2350_ = 1;
v___x_2351_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2242_, v___x_2350_);
if (v___x_2351_ == 0)
{
v___y_2333_ = v_fileMap_2343_;
v___y_2334_ = v_suppressElabErrors_2346_;
v___y_2335_ = v_fileName_2342_;
v___y_2336_ = v___f_2349_;
v___y_2337_ = v_ref_2345_;
v___y_2338_ = v___y_2341_;
v___y_2339_ = v___x_2351_;
goto v___jp_2332_;
}
else
{
lean_object* v___x_2352_; uint8_t v___x_2353_; 
v___x_2352_ = l_Lean_warningAsError;
v___x_2353_ = l_Lean_Option_get___at___00main_spec__8(v_options_2344_, v___x_2352_);
v___y_2333_ = v_fileMap_2343_;
v___y_2334_ = v_suppressElabErrors_2346_;
v___y_2335_ = v_fileName_2342_;
v___y_2336_ = v___f_2349_;
v___y_2337_ = v_ref_2345_;
v___y_2338_ = v___y_2341_;
v___y_2339_ = v___x_2353_;
goto v___jp_2332_;
}
}
else
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
lean_dec_ref(v_msgData_2241_);
v___x_2354_ = lean_box(0);
v___x_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2354_);
return v___x_2355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__43___boxed(lean_object* v_ref_2358_, lean_object* v_msgData_2359_, lean_object* v_severity_2360_, lean_object* v_isSilent_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
uint8_t v_severity_boxed_2365_; uint8_t v_isSilent_boxed_2366_; lean_object* v_res_2367_; 
v_severity_boxed_2365_ = lean_unbox(v_severity_2360_);
v_isSilent_boxed_2366_ = lean_unbox(v_isSilent_2361_);
v_res_2367_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__43(v_ref_2358_, v_msgData_2359_, v_severity_boxed_2365_, v_isSilent_boxed_2366_, v___y_2362_, v___y_2363_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v_ref_2358_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(lean_object* v_msgData_2368_, uint8_t v_severity_2369_, uint8_t v_isSilent_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v_ref_2374_; lean_object* v___x_2375_; 
v_ref_2374_ = lean_ctor_get(v___y_2371_, 5);
v___x_2375_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__43(v_ref_2374_, v_msgData_2368_, v_severity_2369_, v_isSilent_2370_, v___y_2371_, v___y_2372_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30___boxed(lean_object* v_msgData_2376_, lean_object* v_severity_2377_, lean_object* v_isSilent_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
uint8_t v_severity_boxed_2382_; uint8_t v_isSilent_boxed_2383_; lean_object* v_res_2384_; 
v_severity_boxed_2382_ = lean_unbox(v_severity_2377_);
v_isSilent_boxed_2383_ = lean_unbox(v_isSilent_2378_);
v_res_2384_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2376_, v_severity_boxed_2382_, v_isSilent_boxed_2383_, v___y_2379_, v___y_2380_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14(lean_object* v_msgData_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
uint8_t v___x_2389_; uint8_t v___x_2390_; lean_object* v___x_2391_; 
v___x_2389_ = 2;
v___x_2390_ = 0;
v___x_2391_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2385_, v___x_2389_, v___x_2390_, v___y_2386_, v___y_2387_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14___boxed(lean_object* v_msgData_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Lean_logError___at___00main_spec__14(v_msgData_2392_, v___y_2393_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(lean_object* v_x2_2397_, lean_object* v_as_2398_, size_t v_i_2399_, size_t v_stop_2400_, lean_object* v_b_2401_){
_start:
{
uint8_t v___x_2402_; 
v___x_2402_ = lean_usize_dec_eq(v_i_2399_, v_stop_2400_);
if (v___x_2402_ == 0)
{
lean_object* v___x_2403_; lean_object* v___x_2404_; size_t v___x_2405_; size_t v___x_2406_; 
v___x_2403_ = lean_array_uget_borrowed(v_as_2398_, v_i_2399_);
lean_inc_ref(v_x2_2397_);
lean_inc(v___x_2403_);
v___x_2404_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2403_, v_x2_2397_, v_b_2401_);
v___x_2405_ = ((size_t)1ULL);
v___x_2406_ = lean_usize_add(v_i_2399_, v___x_2405_);
v_i_2399_ = v___x_2406_;
v_b_2401_ = v___x_2404_;
goto _start;
}
else
{
lean_dec_ref(v_x2_2397_);
return v_b_2401_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(lean_object* v_x2_2408_, lean_object* v_as_2409_, lean_object* v_i_2410_, lean_object* v_stop_2411_, lean_object* v_b_2412_){
_start:
{
size_t v_i_boxed_2413_; size_t v_stop_boxed_2414_; lean_object* v_res_2415_; 
v_i_boxed_2413_ = lean_unbox_usize(v_i_2410_);
lean_dec(v_i_2410_);
v_stop_boxed_2414_ = lean_unbox_usize(v_stop_2411_);
lean_dec(v_stop_2411_);
v_res_2415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v_x2_2408_, v_as_2409_, v_i_boxed_2413_, v_stop_boxed_2414_, v_b_2412_);
lean_dec_ref(v_as_2409_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object* v_as_2416_, size_t v_i_2417_, size_t v_stop_2418_, lean_object* v_b_2419_){
_start:
{
lean_object* v___y_2421_; uint8_t v___x_2425_; 
v___x_2425_ = lean_usize_dec_eq(v_i_2417_, v_stop_2418_);
if (v___x_2425_ == 0)
{
lean_object* v___x_2426_; lean_object* v_declNames_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; uint8_t v___x_2430_; 
v___x_2426_ = lean_array_uget_borrowed(v_as_2416_, v_i_2417_);
v_declNames_2427_ = lean_ctor_get(v___x_2426_, 0);
v___x_2428_ = lean_unsigned_to_nat(0u);
v___x_2429_ = lean_array_get_size(v_declNames_2427_);
v___x_2430_ = lean_nat_dec_lt(v___x_2428_, v___x_2429_);
if (v___x_2430_ == 0)
{
v___y_2421_ = v_b_2419_;
goto v___jp_2420_;
}
else
{
uint8_t v___x_2431_; 
v___x_2431_ = lean_nat_dec_le(v___x_2429_, v___x_2429_);
if (v___x_2431_ == 0)
{
if (v___x_2430_ == 0)
{
v___y_2421_ = v_b_2419_;
goto v___jp_2420_;
}
else
{
size_t v___x_2432_; size_t v___x_2433_; lean_object* v___x_2434_; 
v___x_2432_ = ((size_t)0ULL);
v___x_2433_ = lean_usize_of_nat(v___x_2429_);
lean_inc(v___x_2426_);
v___x_2434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2426_, v_declNames_2427_, v___x_2432_, v___x_2433_, v_b_2419_);
v___y_2421_ = v___x_2434_;
goto v___jp_2420_;
}
}
else
{
size_t v___x_2435_; size_t v___x_2436_; lean_object* v___x_2437_; 
v___x_2435_ = ((size_t)0ULL);
v___x_2436_ = lean_usize_of_nat(v___x_2429_);
lean_inc(v___x_2426_);
v___x_2437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2426_, v_declNames_2427_, v___x_2435_, v___x_2436_, v_b_2419_);
v___y_2421_ = v___x_2437_;
goto v___jp_2420_;
}
}
}
else
{
return v_b_2419_;
}
v___jp_2420_:
{
size_t v___x_2422_; size_t v___x_2423_; 
v___x_2422_ = ((size_t)1ULL);
v___x_2423_ = lean_usize_add(v_i_2417_, v___x_2422_);
v_i_2417_ = v___x_2423_;
v_b_2419_ = v___y_2421_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object* v_as_2438_, lean_object* v_i_2439_, lean_object* v_stop_2440_, lean_object* v_b_2441_){
_start:
{
size_t v_i_boxed_2442_; size_t v_stop_boxed_2443_; lean_object* v_res_2444_; 
v_i_boxed_2442_ = lean_unbox_usize(v_i_2439_);
lean_dec(v_i_2439_);
v_stop_boxed_2443_ = lean_unbox_usize(v_stop_2440_);
lean_dec(v_stop_2440_);
v_res_2444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v_as_2438_, v_i_boxed_2442_, v_stop_boxed_2443_, v_b_2441_);
lean_dec_ref(v_as_2438_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(lean_object* v_a_2445_, lean_object* v_as_2446_, size_t v_i_2447_, size_t v_stop_2448_, lean_object* v_b_2449_){
_start:
{
lean_object* v___y_2451_; uint8_t v___x_2455_; 
v___x_2455_ = lean_usize_dec_eq(v_i_2447_, v_stop_2448_);
if (v___x_2455_ == 0)
{
lean_object* v___x_2456_; lean_object* v_name_2457_; uint8_t v___x_2458_; 
v___x_2456_ = lean_array_uget_borrowed(v_as_2446_, v_i_2447_);
v_name_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_name_2457_);
lean_inc_ref(v_a_2445_);
v___x_2458_ = l_Lean_isExtern(v_a_2445_, v_name_2457_);
if (v___x_2458_ == 0)
{
v___y_2451_ = v_b_2449_;
goto v___jp_2450_;
}
else
{
lean_object* v___x_2459_; 
lean_inc(v___x_2456_);
v___x_2459_ = lean_array_push(v_b_2449_, v___x_2456_);
v___y_2451_ = v___x_2459_;
goto v___jp_2450_;
}
}
else
{
lean_dec_ref(v_a_2445_);
return v_b_2449_;
}
v___jp_2450_:
{
size_t v___x_2452_; size_t v___x_2453_; 
v___x_2452_ = ((size_t)1ULL);
v___x_2453_ = lean_usize_add(v_i_2447_, v___x_2452_);
v_i_2447_ = v___x_2453_;
v_b_2449_ = v___y_2451_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19___boxed(lean_object* v_a_2460_, lean_object* v_as_2461_, lean_object* v_i_2462_, lean_object* v_stop_2463_, lean_object* v_b_2464_){
_start:
{
size_t v_i_boxed_2465_; size_t v_stop_boxed_2466_; lean_object* v_res_2467_; 
v_i_boxed_2465_ = lean_unbox_usize(v_i_2462_);
lean_dec(v_i_2462_);
v_stop_boxed_2466_ = lean_unbox_usize(v_stop_2463_);
lean_dec(v_stop_2463_);
v_res_2467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_2460_, v_as_2461_, v_i_boxed_2465_, v_stop_boxed_2466_, v_b_2464_);
lean_dec_ref(v_as_2461_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(lean_object* v_as_2468_, size_t v_sz_2469_, size_t v_i_2470_, lean_object* v_b_2471_){
_start:
{
uint8_t v___x_2473_; 
v___x_2473_ = lean_usize_dec_lt(v_i_2470_, v_sz_2469_);
if (v___x_2473_ == 0)
{
lean_object* v___x_2474_; 
v___x_2474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2474_, 0, v_b_2471_);
return v___x_2474_;
}
else
{
uint8_t v___x_2475_; lean_object* v_a_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
lean_dec_ref(v_b_2471_);
v___x_2475_ = 0;
v_a_2476_ = lean_array_uget_borrowed(v_as_2468_, v_i_2470_);
lean_inc(v_a_2476_);
v___x_2477_ = l_Lean_Message_toString(v_a_2476_, v___x_2475_);
v___x_2478_ = l_IO_eprintln___at___00main_spec__6(v___x_2477_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v___x_2479_; size_t v___x_2480_; size_t v___x_2481_; 
lean_dec_ref(v___x_2478_);
v___x_2479_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37_spec__50___redArg___closed__0));
v___x_2480_ = ((size_t)1ULL);
v___x_2481_ = lean_usize_add(v_i_2470_, v___x_2480_);
v_i_2470_ = v___x_2481_;
v_b_2471_ = v___x_2479_;
goto _start;
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
v_a_2483_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2478_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2478_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27___boxed(lean_object* v_as_2491_, lean_object* v_sz_2492_, lean_object* v_i_2493_, lean_object* v_b_2494_, lean_object* v___y_2495_){
_start:
{
size_t v_sz_boxed_2496_; size_t v_i_boxed_2497_; lean_object* v_res_2498_; 
v_sz_boxed_2496_ = lean_unbox_usize(v_sz_2492_);
lean_dec(v_sz_2492_);
v_i_boxed_2497_ = lean_unbox_usize(v_i_2493_);
lean_dec(v_i_2493_);
v_res_2498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2491_, v_sz_boxed_2496_, v_i_boxed_2497_, v_b_2494_);
lean_dec_ref(v_as_2491_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(lean_object* v_as_2499_, size_t v_sz_2500_, size_t v_i_2501_, lean_object* v_b_2502_){
_start:
{
uint8_t v___x_2504_; 
v___x_2504_ = lean_usize_dec_lt(v_i_2501_, v_sz_2500_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2505_; 
v___x_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2505_, 0, v_b_2502_);
return v___x_2505_;
}
else
{
uint8_t v___x_2506_; lean_object* v_a_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
lean_dec_ref(v_b_2502_);
v___x_2506_ = 0;
v_a_2507_ = lean_array_uget_borrowed(v_as_2499_, v_i_2501_);
lean_inc(v_a_2507_);
v___x_2508_ = l_Lean_Message_toString(v_a_2507_, v___x_2506_);
v___x_2509_ = l_IO_eprintln___at___00main_spec__6(v___x_2508_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v___x_2510_; size_t v___x_2511_; size_t v___x_2512_; lean_object* v___x_2513_; 
lean_dec_ref(v___x_2509_);
v___x_2510_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37_spec__50___redArg___closed__0));
v___x_2511_ = ((size_t)1ULL);
v___x_2512_ = lean_usize_add(v_i_2501_, v___x_2511_);
v___x_2513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2499_, v_sz_2500_, v___x_2512_, v___x_2510_);
return v___x_2513_;
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
v_a_2514_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2509_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2509_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14___boxed(lean_object* v_as_2522_, lean_object* v_sz_2523_, lean_object* v_i_2524_, lean_object* v_b_2525_, lean_object* v___y_2526_){
_start:
{
size_t v_sz_boxed_2527_; size_t v_i_boxed_2528_; lean_object* v_res_2529_; 
v_sz_boxed_2527_ = lean_unbox_usize(v_sz_2523_);
lean_dec(v_sz_2523_);
v_i_boxed_2528_ = lean_unbox_usize(v_i_2524_);
lean_dec(v_i_2524_);
v_res_2529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_as_2522_, v_sz_boxed_2527_, v_i_boxed_2528_, v_b_2525_);
lean_dec_ref(v_as_2522_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(lean_object* v_init_2530_, lean_object* v_n_2531_, lean_object* v_b_2532_){
_start:
{
if (lean_obj_tag(v_n_2531_) == 0)
{
lean_object* v_cs_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2568_; 
v_cs_2534_ = lean_ctor_get(v_n_2531_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v_n_2531_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2536_ = v_n_2531_;
v_isShared_2537_ = v_isSharedCheck_2568_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_cs_2534_);
lean_dec(v_n_2531_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2568_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; size_t v_sz_2540_; size_t v___x_2541_; lean_object* v___x_2542_; 
v___x_2538_ = lean_box(0);
v___x_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2538_);
lean_ctor_set(v___x_2539_, 1, v_b_2532_);
v_sz_2540_ = lean_array_size(v_cs_2534_);
v___x_2541_ = ((size_t)0ULL);
v___x_2542_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2530_, v_cs_2534_, v_sz_2540_, v___x_2541_, v___x_2539_);
lean_dec_ref(v_cs_2534_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2559_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2545_ = v___x_2542_;
v_isShared_2546_ = v_isSharedCheck_2559_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2542_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2559_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v_fst_2547_; 
v_fst_2547_ = lean_ctor_get(v_a_2543_, 0);
if (lean_obj_tag(v_fst_2547_) == 0)
{
lean_object* v_snd_2548_; lean_object* v___x_2550_; 
v_snd_2548_ = lean_ctor_get(v_a_2543_, 1);
lean_inc(v_snd_2548_);
lean_dec(v_a_2543_);
if (v_isShared_2537_ == 0)
{
lean_ctor_set_tag(v___x_2536_, 1);
lean_ctor_set(v___x_2536_, 0, v_snd_2548_);
v___x_2550_ = v___x_2536_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_snd_2548_);
v___x_2550_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
lean_object* v___x_2552_; 
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 0, v___x_2550_);
v___x_2552_ = v___x_2545_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2550_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
else
{
lean_object* v_val_2555_; lean_object* v___x_2557_; 
lean_inc_ref(v_fst_2547_);
lean_dec(v_a_2543_);
lean_del_object(v___x_2536_);
v_val_2555_ = lean_ctor_get(v_fst_2547_, 0);
lean_inc(v_val_2555_);
lean_dec_ref(v_fst_2547_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 0, v_val_2555_);
v___x_2557_ = v___x_2545_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_val_2555_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
else
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
lean_del_object(v___x_2536_);
v_a_2560_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2542_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2542_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2560_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
}
}
else
{
lean_object* v_vs_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2603_; 
v_vs_2569_ = lean_ctor_get(v_n_2531_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v_n_2531_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2571_ = v_n_2531_;
v_isShared_2572_ = v_isSharedCheck_2603_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_vs_2569_);
lean_dec(v_n_2531_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2603_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; size_t v_sz_2575_; size_t v___x_2576_; lean_object* v___x_2577_; 
v___x_2573_ = lean_box(0);
v___x_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2573_);
lean_ctor_set(v___x_2574_, 1, v_b_2532_);
v_sz_2575_ = lean_array_size(v_vs_2569_);
v___x_2576_ = ((size_t)0ULL);
v___x_2577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_vs_2569_, v_sz_2575_, v___x_2576_, v___x_2574_);
lean_dec_ref(v_vs_2569_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2594_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2580_ = v___x_2577_;
v_isShared_2581_ = v_isSharedCheck_2594_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2594_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v_fst_2582_; 
v_fst_2582_ = lean_ctor_get(v_a_2578_, 0);
if (lean_obj_tag(v_fst_2582_) == 0)
{
lean_object* v_snd_2583_; lean_object* v___x_2585_; 
v_snd_2583_ = lean_ctor_get(v_a_2578_, 1);
lean_inc(v_snd_2583_);
lean_dec(v_a_2578_);
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 0, v_snd_2583_);
v___x_2585_ = v___x_2571_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_snd_2583_);
v___x_2585_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
lean_object* v___x_2587_; 
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2585_);
v___x_2587_ = v___x_2580_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2585_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
else
{
lean_object* v_val_2590_; lean_object* v___x_2592_; 
lean_inc_ref(v_fst_2582_);
lean_dec(v_a_2578_);
lean_del_object(v___x_2571_);
v_val_2590_ = lean_ctor_get(v_fst_2582_, 0);
lean_inc(v_val_2590_);
lean_dec_ref(v_fst_2582_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v_val_2590_);
v___x_2592_ = v___x_2580_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_val_2590_);
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
else
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_del_object(v___x_2571_);
v_a_2595_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2577_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2577_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(lean_object* v_init_2604_, lean_object* v_as_2605_, size_t v_sz_2606_, size_t v_i_2607_, lean_object* v_b_2608_){
_start:
{
uint8_t v___x_2610_; 
v___x_2610_ = lean_usize_dec_lt(v_i_2607_, v_sz_2606_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; 
v___x_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2611_, 0, v_b_2608_);
return v___x_2611_;
}
else
{
lean_object* v_snd_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2646_; 
v_snd_2612_ = lean_ctor_get(v_b_2608_, 1);
v_isSharedCheck_2646_ = !lean_is_exclusive(v_b_2608_);
if (v_isSharedCheck_2646_ == 0)
{
lean_object* v_unused_2647_; 
v_unused_2647_ = lean_ctor_get(v_b_2608_, 0);
lean_dec(v_unused_2647_);
v___x_2614_ = v_b_2608_;
v_isShared_2615_ = v_isSharedCheck_2646_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_snd_2612_);
lean_dec(v_b_2608_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2646_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v_a_2616_; lean_object* v___x_2617_; 
v_a_2616_ = lean_array_uget_borrowed(v_as_2605_, v_i_2607_);
lean_inc(v_snd_2612_);
lean_inc(v_a_2616_);
v___x_2617_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2604_, v_a_2616_, v_snd_2612_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2637_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2620_ = v___x_2617_;
v_isShared_2621_ = v_isSharedCheck_2637_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2617_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2637_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
if (lean_obj_tag(v_a_2618_) == 0)
{
lean_object* v___x_2622_; lean_object* v___x_2624_; 
v___x_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2622_, 0, v_a_2618_);
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 0, v___x_2622_);
v___x_2624_ = v___x_2614_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2622_);
lean_ctor_set(v_reuseFailAlloc_2628_, 1, v_snd_2612_);
v___x_2624_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
lean_object* v___x_2626_; 
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 0, v___x_2624_);
v___x_2626_ = v___x_2620_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2624_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2630_; lean_object* v___x_2632_; 
lean_del_object(v___x_2620_);
lean_dec(v_snd_2612_);
v_a_2629_ = lean_ctor_get(v_a_2618_, 0);
lean_inc(v_a_2629_);
lean_dec_ref(v_a_2618_);
v___x_2630_ = lean_box(0);
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 1, v_a_2629_);
lean_ctor_set(v___x_2614_, 0, v___x_2630_);
v___x_2632_ = v___x_2614_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2630_);
lean_ctor_set(v_reuseFailAlloc_2636_, 1, v_a_2629_);
v___x_2632_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
size_t v___x_2633_; size_t v___x_2634_; 
v___x_2633_ = ((size_t)1ULL);
v___x_2634_ = lean_usize_add(v_i_2607_, v___x_2633_);
v_i_2607_ = v___x_2634_;
v_b_2608_ = v___x_2632_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_del_object(v___x_2614_);
lean_dec(v_snd_2612_);
v_a_2638_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2617_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2617_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13___boxed(lean_object* v_init_2648_, lean_object* v_as_2649_, lean_object* v_sz_2650_, lean_object* v_i_2651_, lean_object* v_b_2652_, lean_object* v___y_2653_){
_start:
{
size_t v_sz_boxed_2654_; size_t v_i_boxed_2655_; lean_object* v_res_2656_; 
v_sz_boxed_2654_ = lean_unbox_usize(v_sz_2650_);
lean_dec(v_sz_2650_);
v_i_boxed_2655_ = lean_unbox_usize(v_i_2651_);
lean_dec(v_i_2651_);
v_res_2656_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2648_, v_as_2649_, v_sz_boxed_2654_, v_i_boxed_2655_, v_b_2652_);
lean_dec_ref(v_as_2649_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10___boxed(lean_object* v_init_2657_, lean_object* v_n_2658_, lean_object* v_b_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2657_, v_n_2658_, v_b_2659_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(lean_object* v_as_2662_, size_t v_sz_2663_, size_t v_i_2664_, lean_object* v_b_2665_){
_start:
{
uint8_t v___x_2667_; 
v___x_2667_ = lean_usize_dec_lt(v_i_2664_, v_sz_2663_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; 
v___x_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2668_, 0, v_b_2665_);
return v___x_2668_;
}
else
{
uint8_t v___x_2669_; lean_object* v_a_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
lean_dec_ref(v_b_2665_);
v___x_2669_ = 0;
v_a_2670_ = lean_array_uget_borrowed(v_as_2662_, v_i_2664_);
lean_inc(v_a_2670_);
v___x_2671_ = l_Lean_Message_toString(v_a_2670_, v___x_2669_);
v___x_2672_ = l_IO_eprintln___at___00main_spec__6(v___x_2671_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v___x_2673_; size_t v___x_2674_; size_t v___x_2675_; 
lean_dec_ref(v___x_2672_);
v___x_2673_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__39___redArg___closed__0));
v___x_2674_ = ((size_t)1ULL);
v___x_2675_ = lean_usize_add(v_i_2664_, v___x_2674_);
v_i_2664_ = v___x_2675_;
v_b_2665_ = v___x_2673_;
goto _start;
}
else
{
lean_object* v_a_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2684_; 
v_a_2677_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2679_ = v___x_2672_;
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_a_2677_);
lean_dec(v___x_2672_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2682_; 
if (v_isShared_2680_ == 0)
{
v___x_2682_ = v___x_2679_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2677_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16___boxed(lean_object* v_as_2685_, lean_object* v_sz_2686_, lean_object* v_i_2687_, lean_object* v_b_2688_, lean_object* v___y_2689_){
_start:
{
size_t v_sz_boxed_2690_; size_t v_i_boxed_2691_; lean_object* v_res_2692_; 
v_sz_boxed_2690_ = lean_unbox_usize(v_sz_2686_);
lean_dec(v_sz_2686_);
v_i_boxed_2691_ = lean_unbox_usize(v_i_2687_);
lean_dec(v_i_2687_);
v_res_2692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2685_, v_sz_boxed_2690_, v_i_boxed_2691_, v_b_2688_);
lean_dec_ref(v_as_2685_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(lean_object* v_as_2693_, size_t v_sz_2694_, size_t v_i_2695_, lean_object* v_b_2696_){
_start:
{
uint8_t v___x_2698_; 
v___x_2698_ = lean_usize_dec_lt(v_i_2695_, v_sz_2694_);
if (v___x_2698_ == 0)
{
lean_object* v___x_2699_; 
v___x_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2699_, 0, v_b_2696_);
return v___x_2699_;
}
else
{
uint8_t v___x_2700_; lean_object* v_a_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
lean_dec_ref(v_b_2696_);
v___x_2700_ = 0;
v_a_2701_ = lean_array_uget_borrowed(v_as_2693_, v_i_2695_);
lean_inc(v_a_2701_);
v___x_2702_ = l_Lean_Message_toString(v_a_2701_, v___x_2700_);
v___x_2703_ = l_IO_eprintln___at___00main_spec__6(v___x_2702_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v___x_2704_; size_t v___x_2705_; size_t v___x_2706_; lean_object* v___x_2707_; 
lean_dec_ref(v___x_2703_);
v___x_2704_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__39___redArg___closed__0));
v___x_2705_ = ((size_t)1ULL);
v___x_2706_ = lean_usize_add(v_i_2695_, v___x_2705_);
v___x_2707_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2693_, v_sz_2694_, v___x_2706_, v___x_2704_);
return v___x_2707_;
}
else
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2715_; 
v_a_2708_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2710_ = v___x_2703_;
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2703_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
if (v_isShared_2711_ == 0)
{
v___x_2713_ = v___x_2710_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11___boxed(lean_object* v_as_2716_, lean_object* v_sz_2717_, lean_object* v_i_2718_, lean_object* v_b_2719_, lean_object* v___y_2720_){
_start:
{
size_t v_sz_boxed_2721_; size_t v_i_boxed_2722_; lean_object* v_res_2723_; 
v_sz_boxed_2721_ = lean_unbox_usize(v_sz_2717_);
lean_dec(v_sz_2717_);
v_i_boxed_2722_ = lean_unbox_usize(v_i_2718_);
lean_dec(v_i_2718_);
v_res_2723_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_as_2716_, v_sz_boxed_2721_, v_i_boxed_2722_, v_b_2719_);
lean_dec_ref(v_as_2716_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7(lean_object* v_t_2724_, lean_object* v_init_2725_){
_start:
{
lean_object* v_root_2727_; lean_object* v_tail_2728_; lean_object* v___x_2729_; 
v_root_2727_ = lean_ctor_get(v_t_2724_, 0);
lean_inc_ref(v_root_2727_);
v_tail_2728_ = lean_ctor_get(v_t_2724_, 1);
lean_inc_ref(v_tail_2728_);
lean_dec_ref(v_t_2724_);
v___x_2729_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2725_, v_root_2727_, v_init_2725_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2766_; 
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2732_ = v___x_2729_;
v_isShared_2733_ = v_isSharedCheck_2766_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2729_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2766_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
if (lean_obj_tag(v_a_2730_) == 0)
{
lean_object* v_a_2734_; lean_object* v___x_2736_; 
lean_dec_ref(v_tail_2728_);
v_a_2734_ = lean_ctor_get(v_a_2730_, 0);
lean_inc(v_a_2734_);
lean_dec_ref(v_a_2730_);
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 0, v_a_2734_);
v___x_2736_ = v___x_2732_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_a_2734_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
else
{
lean_object* v_a_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; size_t v_sz_2741_; size_t v___x_2742_; lean_object* v___x_2743_; 
lean_del_object(v___x_2732_);
v_a_2738_ = lean_ctor_get(v_a_2730_, 0);
lean_inc(v_a_2738_);
lean_dec_ref(v_a_2730_);
v___x_2739_ = lean_box(0);
v___x_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2739_);
lean_ctor_set(v___x_2740_, 1, v_a_2738_);
v_sz_2741_ = lean_array_size(v_tail_2728_);
v___x_2742_ = ((size_t)0ULL);
v___x_2743_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_tail_2728_, v_sz_2741_, v___x_2742_, v___x_2740_);
lean_dec_ref(v_tail_2728_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2757_; 
v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2746_ = v___x_2743_;
v_isShared_2747_ = v_isSharedCheck_2757_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2743_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2757_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v_fst_2748_; 
v_fst_2748_ = lean_ctor_get(v_a_2744_, 0);
if (lean_obj_tag(v_fst_2748_) == 0)
{
lean_object* v_snd_2749_; lean_object* v___x_2751_; 
v_snd_2749_ = lean_ctor_get(v_a_2744_, 1);
lean_inc(v_snd_2749_);
lean_dec(v_a_2744_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 0, v_snd_2749_);
v___x_2751_ = v___x_2746_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_snd_2749_);
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
lean_object* v_val_2753_; lean_object* v___x_2755_; 
lean_inc_ref(v_fst_2748_);
lean_dec(v_a_2744_);
v_val_2753_ = lean_ctor_get(v_fst_2748_, 0);
lean_inc(v_val_2753_);
lean_dec_ref(v_fst_2748_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 0, v_val_2753_);
v___x_2755_ = v___x_2746_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_val_2753_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
else
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
v_a_2758_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v___x_2743_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2743_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
lean_dec_ref(v_tail_2728_);
v_a_2767_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2729_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2729_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2770_ == 0)
{
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7___boxed(lean_object* v_t_2775_, lean_object* v_init_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_t_2775_, v_init_2776_);
return v_res_2778_;
}
}
static lean_object* _init_l_main___closed__3(void){
_start:
{
lean_object* v___x_2782_; 
v___x_2782_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_box(0), lean_box(0), lean_box(0));
return v___x_2782_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2783_ = l_Lean_instInhabitedClassState_default;
v___x_2784_ = lean_box(0);
v___x_2785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2784_);
lean_ctor_set(v___x_2785_, 1, v___x_2783_);
return v___x_2785_;
}
}
static lean_object* _init_l_main___closed__5(void){
_start:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2786_ = l_Lean_Meta_Match_Extension_instInhabitedState;
v___x_2787_ = lean_box(0);
v___x_2788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2787_);
lean_ctor_set(v___x_2788_, 1, v___x_2786_);
return v___x_2788_;
}
}
static lean_object* _init_l_main___closed__6(void){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2789_ = ((lean_object*)(l_main___closed__2));
v___x_2790_ = ((lean_object*)(l_main___closed__1));
v___x_2791_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_2790_, v___x_2789_);
return v___x_2791_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2792_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2793_ = lean_box(0);
v___x_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2793_);
lean_ctor_set(v___x_2794_, 1, v___x_2792_);
return v___x_2794_;
}
}
static lean_object* _init_l_main___closed__8(void){
_start:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2795_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_2796_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2795_);
return v___x_2796_;
}
}
static lean_object* _init_l_main___closed__9(void){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = l_Array_instInhabited(lean_box(0));
return v___x_2797_;
}
}
static lean_object* _init_l_main___closed__14(void){
_start:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2805_ = l_Lean_Options_empty;
v___x_2806_ = l_Lean_Core_getMaxHeartbeats(v___x_2805_);
return v___x_2806_;
}
}
static lean_object* _init_l_main___closed__19(void){
_start:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2811_ = ((lean_object*)(l_main___closed__18));
v___x_2812_ = lean_unsigned_to_nat(27u);
v___x_2813_ = lean_unsigned_to_nat(144u);
v___x_2814_ = ((lean_object*)(l_main___closed__17));
v___x_2815_ = ((lean_object*)(l_main___closed__16));
v___x_2816_ = l_mkPanicMessageWithDecl(v___x_2815_, v___x_2814_, v___x_2813_, v___x_2812_, v___x_2811_);
return v___x_2816_;
}
}
static lean_object* _init_l_main___closed__21(void){
_start:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2818_ = ((lean_object*)(l_main___closed__18));
v___x_2819_ = lean_unsigned_to_nat(51u);
v___x_2820_ = lean_unsigned_to_nat(117u);
v___x_2821_ = ((lean_object*)(l_main___closed__17));
v___x_2822_ = ((lean_object*)(l_main___closed__16));
v___x_2823_ = l_mkPanicMessageWithDecl(v___x_2822_, v___x_2821_, v___x_2820_, v___x_2819_, v___x_2818_);
return v___x_2823_;
}
}
static lean_object* _init_l_main___closed__22(void){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2824_ = lean_unsigned_to_nat(1u);
v___x_2825_ = l_Lean_firstFrontendMacroScope;
v___x_2826_ = lean_nat_add(v___x_2825_, v___x_2824_);
return v___x_2826_;
}
}
static lean_object* _init_l_main___closed__26(void){
_start:
{
lean_object* v___x_2833_; uint64_t v___x_2834_; lean_object* v___x_2835_; 
v___x_2833_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2834_ = 0ULL;
v___x_2835_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2835_, 0, v___x_2833_);
lean_ctor_set_uint64(v___x_2835_, sizeof(void*)*1, v___x_2834_);
return v___x_2835_;
}
}
static lean_object* _init_l_main___closed__27(void){
_start:
{
lean_object* v___x_2836_; 
v___x_2836_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2836_;
}
}
static lean_object* _init_l_main___closed__28(void){
_start:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2837_ = lean_obj_once(&l_main___closed__27, &l_main___closed__27_once, _init_l_main___closed__27);
v___x_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2837_);
return v___x_2838_;
}
}
static lean_object* _init_l_main___closed__29(void){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2839_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_2840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2839_);
lean_ctor_set(v___x_2840_, 1, v___x_2839_);
return v___x_2840_;
}
}
static lean_object* _init_l_main___closed__30(void){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2841_ = l_Lean_NameSet_empty;
v___x_2842_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2843_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2842_);
lean_ctor_set(v___x_2843_, 1, v___x_2842_);
lean_ctor_set(v___x_2843_, 2, v___x_2841_);
return v___x_2843_;
}
}
static lean_object* _init_l_main___closed__31(void){
_start:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; uint8_t v___x_2846_; lean_object* v___x_2847_; 
v___x_2844_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2845_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_2846_ = 1;
v___x_2847_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2847_, 0, v___x_2845_);
lean_ctor_set(v___x_2847_, 1, v___x_2845_);
lean_ctor_set(v___x_2847_, 2, v___x_2844_);
lean_ctor_set_uint8(v___x_2847_, sizeof(void*)*3, v___x_2846_);
return v___x_2847_;
}
}
static uint8_t _init_l_main___closed__36(void){
_start:
{
uint8_t v___x_2854_; uint8_t v___x_2855_; 
v___x_2854_ = 2;
v___x_2855_ = l_Lean_instOrdOLeanLevel_ord(v___x_2854_, v___x_2854_);
return v___x_2855_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_2856_; lean_object* v___x_2857_; 
v___x_2856_ = 1;
v___x_2857_ = lean_box_uint32(v___x_2856_);
return v___x_2857_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_2858_; lean_object* v___x_2859_; 
v___x_2858_ = 0;
v___x_2859_ = lean_box_uint32(v___x_2858_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_2860_){
_start:
{
if (lean_obj_tag(v_args_2860_) == 1)
{
lean_object* v_tail_2885_; 
v_tail_2885_ = lean_ctor_get(v_args_2860_, 1);
lean_inc(v_tail_2885_);
if (lean_obj_tag(v_tail_2885_) == 1)
{
lean_object* v_tail_2886_; 
v_tail_2886_ = lean_ctor_get(v_tail_2885_, 1);
lean_inc(v_tail_2886_);
if (lean_obj_tag(v_tail_2886_) == 1)
{
lean_object* v_head_2887_; lean_object* v_head_2888_; lean_object* v_head_2889_; lean_object* v_tail_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_3513_; 
v_head_2887_ = lean_ctor_get(v_args_2860_, 0);
lean_inc(v_head_2887_);
lean_dec_ref(v_args_2860_);
v_head_2888_ = lean_ctor_get(v_tail_2885_, 0);
lean_inc(v_head_2888_);
lean_dec_ref(v_tail_2885_);
v_head_2889_ = lean_ctor_get(v_tail_2886_, 0);
v_tail_2890_ = lean_ctor_get(v_tail_2886_, 1);
v_isSharedCheck_3513_ = !lean_is_exclusive(v_tail_2886_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_2892_ = v_tail_2886_;
v_isShared_2893_ = v_isSharedCheck_3513_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_tail_2890_);
lean_inc(v_head_2889_);
lean_dec(v_tail_2886_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_3513_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2894_; 
v___x_2894_ = l_Lean_ModuleSetup_load(v_head_2887_);
lean_dec(v_head_2887_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; lean_object* v_name_2896_; lean_object* v_options_2897_; uint8_t v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2902_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
lean_inc(v_a_2895_);
lean_dec_ref(v___x_2894_);
v_name_2896_ = lean_ctor_get(v_a_2895_, 0);
lean_inc(v_name_2896_);
v_options_2897_ = lean_ctor_get(v_a_2895_, 6);
lean_inc(v_options_2897_);
lean_dec(v_a_2895_);
v___x_2898_ = 0;
v___x_2899_ = l_Lean_LeanOptions_toOptions(v_options_2897_);
v___x_2900_ = lean_box(v___x_2898_);
if (v_isShared_2893_ == 0)
{
lean_ctor_set_tag(v___x_2892_, 0);
lean_ctor_set(v___x_2892_, 1, v___x_2899_);
lean_ctor_set(v___x_2892_, 0, v___x_2900_);
v___x_2902_ = v___x_2892_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v___x_2900_);
lean_ctor_set(v_reuseFailAlloc_3504_, 1, v___x_2899_);
v___x_2902_ = v_reuseFailAlloc_3504_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
lean_object* v___x_2903_; 
v___x_2903_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_tail_2890_, v___x_2902_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2905_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref(v___x_2903_);
v___x_2905_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_a_2906_);
lean_dec_ref(v___x_2905_);
v___x_2907_ = lean_box(0);
v___x_2908_ = l_Lean_initSearchPath(v_a_2906_, v___x_2907_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v_fst_2909_; lean_object* v_snd_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_3479_; 
lean_dec_ref(v___x_2908_);
v_fst_2909_ = lean_ctor_get(v_a_2904_, 0);
v_snd_2910_ = lean_ctor_get(v_a_2904_, 1);
v_isSharedCheck_3479_ = !lean_is_exclusive(v_a_2904_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_2912_ = v_a_2904_;
v_isShared_2913_ = v_isSharedCheck_3479_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_snd_2910_);
lean_inc(v_fst_2909_);
lean_dec(v_a_2904_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_3479_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; uint8_t v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; uint8_t v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; uint8_t v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v_nextMacroScope_3075_; lean_object* v_ngen_3076_; lean_object* v_auxDeclNGen_3077_; lean_object* v_traceState_3078_; lean_object* v_messages_3079_; lean_object* v_infoState_3080_; lean_object* v_snapshotTasks_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; uint8_t v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; uint8_t v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; uint8_t v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; uint8_t v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; uint8_t v___y_3197_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___y_3221_; uint8_t v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3327_; uint8_t v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3349_; uint8_t v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3365_; lean_object* v___y_3366_; uint8_t v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___x_3380_; lean_object* v___x_3381_; uint8_t v___x_3382_; uint8_t v___y_3384_; uint8_t v___x_3478_; 
v___x_2914_ = lean_obj_once(&l_main___closed__3, &l_main___closed__3_once, _init_l_main___closed__3);
v___x_2915_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2916_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_2917_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2918_ = lean_obj_once(&l_main___closed__8, &l_main___closed__8_once, _init_l_main___closed__8);
v___x_2919_ = lean_obj_once(&l_main___closed__9, &l_main___closed__9_once, _init_l_main___closed__9);
v___x_2920_ = lean_box(1);
v___x_2921_ = ((lean_object*)(l_main___closed__10));
v___x_2922_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_2923_ = 1;
v___x_2924_ = l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(v_snd_2910_, v___x_2922_, v___x_2923_);
v___x_2925_ = l_Lean_maxHeartbeats;
v___x_2926_ = lean_unsigned_to_nat(0u);
v___x_2927_ = l_Lean_Option_set___at___00main_spec__3(v___x_2924_, v___x_2925_, v___x_2926_);
v___x_3217_ = ((lean_object*)(l_main___closed__20));
lean_inc(v_name_2896_);
v___x_3218_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3218_, 0, v_name_2896_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*1, v___x_2923_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*1 + 1, v___x_2923_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*1 + 2, v___x_2923_);
v___x_3219_ = lean_unsigned_to_nat(1u);
v___x_3380_ = lean_mk_empty_array_with_capacity(v___x_3219_);
v___x_3381_ = lean_array_push(v___x_3380_, v___x_3218_);
v___x_3382_ = 2;
v___x_3478_ = lean_uint8_once(&l_main___closed__36, &l_main___closed__36_once, _init_l_main___closed__36);
if (v___x_3478_ == 0)
{
v___y_3384_ = v___x_2923_;
goto v___jp_3383_;
}
else
{
v___y_3384_ = v___x_2898_;
goto v___jp_3383_;
}
v___jp_2928_:
{
lean_object* v___x_2948_; lean_object* v_messages_2949_; lean_object* v_env_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_3051_; 
v___x_2948_ = lean_st_ref_get(v___y_2943_);
lean_dec(v___y_2943_);
v_messages_2949_ = lean_ctor_get(v___x_2948_, 6);
v_env_2950_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_3051_ == 0)
{
lean_object* v_unused_3052_; lean_object* v_unused_3053_; lean_object* v_unused_3054_; lean_object* v_unused_3055_; lean_object* v_unused_3056_; lean_object* v_unused_3057_; lean_object* v_unused_3058_; 
v_unused_3052_ = lean_ctor_get(v___x_2948_, 8);
lean_dec(v_unused_3052_);
v_unused_3053_ = lean_ctor_get(v___x_2948_, 7);
lean_dec(v_unused_3053_);
v_unused_3054_ = lean_ctor_get(v___x_2948_, 5);
lean_dec(v_unused_3054_);
v_unused_3055_ = lean_ctor_get(v___x_2948_, 4);
lean_dec(v_unused_3055_);
v_unused_3056_ = lean_ctor_get(v___x_2948_, 3);
lean_dec(v_unused_3056_);
v_unused_3057_ = lean_ctor_get(v___x_2948_, 2);
lean_dec(v_unused_3057_);
v_unused_3058_ = lean_ctor_get(v___x_2948_, 1);
lean_dec(v_unused_3058_);
v___x_2952_ = v___x_2948_;
v_isShared_2953_ = v_isSharedCheck_3051_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_messages_2949_);
lean_inc(v_env_2950_);
lean_dec(v___x_2948_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_3051_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v_unreported_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v_unreported_2954_ = lean_ctor_get(v_messages_2949_, 1);
v___x_2955_ = lean_box(0);
lean_inc_ref(v_unreported_2954_);
v___x_2956_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_unreported_2954_, v___x_2955_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_3041_; 
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_3041_ == 0)
{
lean_object* v_unused_3042_; 
v_unused_3042_ = lean_ctor_get(v___x_2956_, 0);
lean_dec(v_unused_3042_);
v___x_2958_ = v___x_2956_;
v_isShared_2959_ = v_isSharedCheck_3041_;
goto v_resetjp_2957_;
}
else
{
lean_dec(v___x_2956_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_3041_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
uint8_t v___x_2960_; 
v___x_2960_ = l_Lean_MessageLog_hasErrors(v_messages_2949_);
lean_dec_ref(v_messages_2949_);
if (v___x_2960_ == 0)
{
lean_object* v___x_2961_; 
lean_del_object(v___x_2958_);
lean_inc_ref(v_env_2950_);
v___x_2961_ = l___private_LeanIR_0__mkIRData(v_env_2950_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_a_2962_);
lean_dec_ref(v___x_2961_);
v___x_2963_ = l_Lean_Environment_mainModule(v_env_2950_);
v___x_2964_ = ((lean_object*)(l_main___closed__12));
v___x_2965_ = l_Lean_Name_append(v___x_2963_, v___x_2964_);
lean_inc(v_head_2888_);
v___x_2966_ = l_Lean_saveModuleData(v_head_2888_, v___x_2965_, v_a_2962_);
lean_dec(v___x_2965_);
if (lean_obj_tag(v___x_2966_) == 0)
{
uint8_t v___x_2967_; lean_object* v___x_2968_; 
lean_dec_ref(v___x_2966_);
v___x_2967_ = 1;
v___x_2968_ = lean_io_prim_handle_mk(v_head_2889_, v___x_2967_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2974_; 
lean_dec(v_head_2889_);
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
lean_inc(v_a_2969_);
lean_dec_ref(v___x_2968_);
v___x_2970_ = ((lean_object*)(l_main___closed__13));
v___x_2971_ = l_Lean_Options_empty;
v___x_2972_ = lean_obj_once(&l_main___closed__14, &l_main___closed__14_once, _init_l_main___closed__14);
lean_inc_ref(v___y_2941_);
lean_inc_ref(v___y_2944_);
lean_inc_ref(v___y_2942_);
lean_inc_ref(v___y_2938_);
lean_inc_ref(v___y_2945_);
lean_inc_ref(v___y_2946_);
lean_inc(v___y_2939_);
lean_inc_ref(v_env_2950_);
if (v_isShared_2953_ == 0)
{
lean_ctor_set(v___x_2952_, 8, v___y_2941_);
lean_ctor_set(v___x_2952_, 7, v___y_2944_);
lean_ctor_set(v___x_2952_, 6, v___y_2942_);
lean_ctor_set(v___x_2952_, 5, v___y_2938_);
lean_ctor_set(v___x_2952_, 4, v___y_2945_);
lean_ctor_set(v___x_2952_, 3, v___y_2940_);
lean_ctor_set(v___x_2952_, 2, v___y_2946_);
lean_ctor_set(v___x_2952_, 1, v___y_2939_);
v___x_2974_ = v___x_2952_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_env_2950_);
lean_ctor_set(v_reuseFailAlloc_2998_, 1, v___y_2939_);
lean_ctor_set(v_reuseFailAlloc_2998_, 2, v___y_2946_);
lean_ctor_set(v_reuseFailAlloc_2998_, 3, v___y_2940_);
lean_ctor_set(v_reuseFailAlloc_2998_, 4, v___y_2945_);
lean_ctor_set(v_reuseFailAlloc_2998_, 5, v___y_2938_);
lean_ctor_set(v_reuseFailAlloc_2998_, 6, v___y_2942_);
lean_ctor_set(v_reuseFailAlloc_2998_, 7, v___y_2944_);
lean_ctor_set(v_reuseFailAlloc_2998_, 8, v___y_2941_);
v___x_2974_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___f_2977_; lean_object* v___x_2978_; 
v___x_2975_ = lean_box(v___x_2898_);
v___x_2976_ = lean_box(v___y_2935_);
lean_inc(v___y_2931_);
lean_inc(v___y_2934_);
lean_inc(v___y_2932_);
lean_inc_ref(v___y_2933_);
lean_inc_ref(v___y_2930_);
lean_inc(v___y_2936_);
v___f_2977_ = lean_alloc_closure((void*)(l_main___lam__1___boxed), 18, 17);
lean_closure_set(v___f_2977_, 0, v___x_2974_);
lean_closure_set(v___f_2977_, 1, v___y_2936_);
lean_closure_set(v___f_2977_, 2, v___x_2971_);
lean_closure_set(v___f_2977_, 3, v_name_2896_);
lean_closure_set(v___f_2977_, 4, v_a_2969_);
lean_closure_set(v___f_2977_, 5, v___y_2930_);
lean_closure_set(v___f_2977_, 6, v_head_2888_);
lean_closure_set(v___f_2977_, 7, v___y_2933_);
lean_closure_set(v___f_2977_, 8, v___x_2926_);
lean_closure_set(v___f_2977_, 9, v___y_2932_);
lean_closure_set(v___f_2977_, 10, v___y_2937_);
lean_closure_set(v___f_2977_, 11, v___y_2929_);
lean_closure_set(v___f_2977_, 12, v___x_2972_);
lean_closure_set(v___f_2977_, 13, v___y_2934_);
lean_closure_set(v___f_2977_, 14, v___y_2931_);
lean_closure_set(v___f_2977_, 15, v___x_2975_);
lean_closure_set(v___f_2977_, 16, v___x_2976_);
v___x_2978_ = l_Lean_profileitIOUnsafe___redArg(v___x_2970_, v___x_2927_, v___f_2977_, v___y_2947_);
lean_dec_ref(v___x_2927_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v___x_2979_; uint8_t v___x_2980_; 
lean_dec_ref(v___x_2978_);
v___x_2979_ = lean_display_cumulative_profiling_times();
v___x_2980_ = lean_unbox(v_fst_2909_);
lean_dec(v_fst_2909_);
if (v___x_2980_ == 0)
{
lean_dec_ref(v_env_2950_);
goto v___jp_2882_;
}
else
{
lean_object* v___x_2981_; 
v___x_2981_ = l_Lean_Environment_displayStats(v_env_2950_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_dec_ref(v___x_2981_);
goto v___jp_2882_;
}
else
{
lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2989_; 
v_a_2982_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2984_ = v___x_2981_;
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_dec(v___x_2981_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2987_; 
if (v_isShared_2985_ == 0)
{
v___x_2987_ = v___x_2984_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_a_2982_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
}
}
else
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
lean_dec_ref(v_env_2950_);
lean_dec(v_fst_2909_);
v_a_2990_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2992_ = v___x_2978_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2978_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2990_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
}
}
else
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
lean_dec_ref(v___x_2968_);
lean_del_object(v___x_2952_);
lean_dec_ref(v_env_2950_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2937_);
lean_dec(v___y_2929_);
lean_dec_ref(v___x_2927_);
lean_dec(v_fst_2909_);
lean_dec(v_name_2896_);
lean_dec(v_head_2888_);
v___x_2999_ = ((lean_object*)(l_main___closed__15));
v___x_3000_ = lean_string_append(v___x_2999_, v_head_2889_);
lean_dec(v_head_2889_);
v___x_3001_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__5));
v___x_3002_ = lean_string_append(v___x_3000_, v___x_3001_);
v___x_3003_ = l_IO_eprintln___at___00main_spec__6(v___x_3002_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3011_; 
v_isSharedCheck_3011_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3011_ == 0)
{
lean_object* v_unused_3012_; 
v_unused_3012_ = lean_ctor_get(v___x_3003_, 0);
lean_dec(v_unused_3012_);
v___x_3005_ = v___x_3003_;
v_isShared_3006_ = v_isSharedCheck_3011_;
goto v_resetjp_3004_;
}
else
{
lean_dec(v___x_3003_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3011_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3007_; lean_object* v___x_3009_; 
v___x_3007_ = l_main___boxed__const__1;
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 0, v___x_3007_);
v___x_3009_ = v___x_3005_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_3007_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
}
else
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3020_; 
v_a_3013_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3015_ = v___x_3003_;
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_3003_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3018_; 
if (v_isShared_3016_ == 0)
{
v___x_3018_ = v___x_3015_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_3013_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
}
}
else
{
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
lean_del_object(v___x_2952_);
lean_dec_ref(v_env_2950_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2937_);
lean_dec(v___y_2929_);
lean_dec_ref(v___x_2927_);
lean_dec(v_fst_2909_);
lean_dec(v_name_2896_);
lean_dec(v_head_2889_);
lean_dec(v_head_2888_);
v_a_3021_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3023_ = v___x_2966_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_2966_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3026_; 
if (v_isShared_3024_ == 0)
{
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_a_3021_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
else
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
lean_del_object(v___x_2952_);
lean_dec_ref(v_env_2950_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2937_);
lean_dec(v___y_2929_);
lean_dec_ref(v___x_2927_);
lean_dec(v_fst_2909_);
lean_dec(v_name_2896_);
lean_dec(v_head_2889_);
lean_dec(v_head_2888_);
v_a_3029_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_2961_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_2961_);
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
else
{
lean_object* v___x_3037_; lean_object* v___x_3039_; 
lean_del_object(v___x_2952_);
lean_dec_ref(v_env_2950_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2937_);
lean_dec(v___y_2929_);
lean_dec_ref(v___x_2927_);
lean_dec(v_fst_2909_);
lean_dec(v_name_2896_);
lean_dec(v_head_2889_);
lean_dec(v_head_2888_);
v___x_3037_ = l_main___boxed__const__1;
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 0, v___x_3037_);
v___x_3039_ = v___x_2958_;
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
}
else
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
lean_del_object(v___x_2952_);
lean_dec_ref(v_env_2950_);
lean_dec_ref(v_messages_2949_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2937_);
lean_dec(v___y_2929_);
lean_dec_ref(v___x_2927_);
lean_dec(v_fst_2909_);
lean_dec(v_name_2896_);
lean_dec(v_head_2889_);
lean_dec(v_head_2888_);
v_a_3043_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_2956_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_2956_);
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
v___jp_3059_:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; size_t v_sz_3093_; size_t v___x_3094_; lean_object* v___x_3095_; 
lean_inc_ref(v___y_3070_);
v___x_3090_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3090_, 0, v___y_3089_);
lean_ctor_set(v___x_3090_, 1, v_nextMacroScope_3075_);
lean_ctor_set(v___x_3090_, 2, v_ngen_3076_);
lean_ctor_set(v___x_3090_, 3, v_auxDeclNGen_3077_);
lean_ctor_set(v___x_3090_, 4, v_traceState_3078_);
lean_ctor_set(v___x_3090_, 5, v___y_3070_);
lean_ctor_set(v___x_3090_, 6, v_messages_3079_);
lean_ctor_set(v___x_3090_, 7, v_infoState_3080_);
lean_ctor_set(v___x_3090_, 8, v_snapshotTasks_3081_);
v___x_3091_ = lean_st_ref_set(v___y_3082_, v___x_3090_);
v___x_3092_ = lean_box(0);
v_sz_3093_ = lean_array_size(v___y_3088_);
v___x_3094_ = ((size_t)0ULL);
v___x_3095_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v___y_3088_, v_sz_3093_, v___x_3094_, v___x_3092_, v___y_3069_, v___y_3082_);
lean_dec_ref(v___y_3088_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_dec_ref(v___x_3095_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3069_);
v___y_2929_ = v___y_3060_;
v___y_2930_ = v___y_3061_;
v___y_2931_ = v___y_3062_;
v___y_2932_ = v___y_3064_;
v___y_2933_ = v___y_3063_;
v___y_2934_ = v___y_3065_;
v___y_2935_ = v___y_3067_;
v___y_2936_ = v___y_3066_;
v___y_2937_ = v___y_3068_;
v___y_2938_ = v___y_3070_;
v___y_2939_ = v___y_3074_;
v___y_2940_ = v___y_3071_;
v___y_2941_ = v___y_3083_;
v___y_2942_ = v___y_3084_;
v___y_2943_ = v___y_3085_;
v___y_2944_ = v___y_3086_;
v___y_2945_ = v___y_3073_;
v___y_2946_ = v___y_3072_;
v___y_2947_ = v___y_3087_;
goto v___jp_2928_;
}
else
{
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_dec_ref(v___x_3095_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3069_);
v___y_2929_ = v___y_3060_;
v___y_2930_ = v___y_3061_;
v___y_2931_ = v___y_3062_;
v___y_2932_ = v___y_3064_;
v___y_2933_ = v___y_3063_;
v___y_2934_ = v___y_3065_;
v___y_2935_ = v___y_3067_;
v___y_2936_ = v___y_3066_;
v___y_2937_ = v___y_3068_;
v___y_2938_ = v___y_3070_;
v___y_2939_ = v___y_3074_;
v___y_2940_ = v___y_3071_;
v___y_2941_ = v___y_3083_;
v___y_2942_ = v___y_3084_;
v___y_2943_ = v___y_3085_;
v___y_2944_ = v___y_3086_;
v___y_2945_ = v___y_3073_;
v___y_2946_ = v___y_3072_;
v___y_2947_ = v___y_3087_;
goto v___jp_2928_;
}
else
{
lean_object* v_a_3096_; uint8_t v___x_3097_; 
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
lean_inc(v_a_3096_);
lean_dec_ref(v___x_3095_);
v___x_3097_ = l_Lean_Exception_isInterrupt(v_a_3096_);
if (v___x_3097_ == 0)
{
lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3098_ = l_Lean_Exception_toMessageData(v_a_3096_);
v___x_3099_ = l_Lean_logError___at___00main_spec__14(v___x_3098_, v___y_3069_, v___y_3082_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3069_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_dec_ref(v___x_3099_);
v___y_2929_ = v___y_3060_;
v___y_2930_ = v___y_3061_;
v___y_2931_ = v___y_3062_;
v___y_2932_ = v___y_3064_;
v___y_2933_ = v___y_3063_;
v___y_2934_ = v___y_3065_;
v___y_2935_ = v___y_3067_;
v___y_2936_ = v___y_3066_;
v___y_2937_ = v___y_3068_;
v___y_2938_ = v___y_3070_;
v___y_2939_ = v___y_3074_;
v___y_2940_ = v___y_3071_;
v___y_2941_ = v___y_3083_;
v___y_2942_ = v___y_3084_;
v___y_2943_ = v___y_3085_;
v___y_2944_ = v___y_3086_;
v___y_2945_ = v___y_3073_;
v___y_2946_ = v___y_3072_;
v___y_2947_ = v___y_3087_;
goto v___jp_2928_;
}
else
{
lean_object* v___x_3100_; lean_object* v___x_3101_; 
lean_dec_ref(v___x_3099_);
lean_dec(v___y_3087_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3068_);
lean_dec(v___y_3060_);
lean_dec_ref(v___x_2927_);
lean_dec(v_fst_2909_);
lean_dec(v_name_2896_);
lean_dec(v_head_2889_);
lean_dec(v_head_2888_);
v___x_3100_ = lean_obj_once(&l_main___closed__19, &l_main___closed__19_once, _init_l_main___closed__19);
v___x_3101_ = l_panic___at___00main_spec__5(v___x_3100_);
return v___x_3101_;
}
}
else
{
lean_dec(v_a_3096_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3069_);
v___y_2929_ = v___y_3060_;
v___y_2930_ = v___y_3061_;
v___y_2931_ = v___y_3062_;
v___y_2932_ = v___y_3064_;
v___y_2933_ = v___y_3063_;
v___y_2934_ = v___y_3065_;
v___y_2935_ = v___y_3067_;
v___y_2936_ = v___y_3066_;
v___y_2937_ = v___y_3068_;
v___y_2938_ = v___y_3070_;
v___y_2939_ = v___y_3074_;
v___y_2940_ = v___y_3071_;
v___y_2941_ = v___y_3083_;
v___y_2942_ = v___y_3084_;
v___y_2943_ = v___y_3085_;
v___y_2944_ = v___y_3086_;
v___y_2945_ = v___y_3073_;
v___y_2946_ = v___y_3072_;
v___y_2947_ = v___y_3087_;
goto v___jp_2928_;
}
}
}
}
v___jp_3102_:
{
lean_object* v___x_3127_; lean_object* v_fileName_3128_; lean_object* v_fileMap_3129_; lean_object* v_currRecDepth_3130_; lean_object* v_ref_3131_; lean_object* v_currNamespace_3132_; lean_object* v_openDecls_3133_; lean_object* v_initHeartbeats_3134_; lean_object* v_maxHeartbeats_3135_; lean_object* v_quotContext_3136_; lean_object* v_currMacroScope_3137_; lean_object* v_cancelTk_x3f_3138_; uint8_t v_suppressElabErrors_3139_; lean_object* v_inheritedTraceOptions_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3170_; 
v___x_3127_ = lean_st_ref_take(v___y_3126_);
v_fileName_3128_ = lean_ctor_get(v___y_3125_, 0);
v_fileMap_3129_ = lean_ctor_get(v___y_3125_, 1);
v_currRecDepth_3130_ = lean_ctor_get(v___y_3125_, 3);
v_ref_3131_ = lean_ctor_get(v___y_3125_, 5);
v_currNamespace_3132_ = lean_ctor_get(v___y_3125_, 6);
v_openDecls_3133_ = lean_ctor_get(v___y_3125_, 7);
v_initHeartbeats_3134_ = lean_ctor_get(v___y_3125_, 8);
v_maxHeartbeats_3135_ = lean_ctor_get(v___y_3125_, 9);
v_quotContext_3136_ = lean_ctor_get(v___y_3125_, 10);
v_currMacroScope_3137_ = lean_ctor_get(v___y_3125_, 11);
v_cancelTk_x3f_3138_ = lean_ctor_get(v___y_3125_, 12);
v_suppressElabErrors_3139_ = lean_ctor_get_uint8(v___y_3125_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3140_ = lean_ctor_get(v___y_3125_, 13);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___y_3125_);
if (v_isSharedCheck_3170_ == 0)
{
lean_object* v_unused_3171_; lean_object* v_unused_3172_; 
v_unused_3171_ = lean_ctor_get(v___y_3125_, 4);
lean_dec(v_unused_3171_);
v_unused_3172_ = lean_ctor_get(v___y_3125_, 2);
lean_dec(v_unused_3172_);
v___x_3142_ = v___y_3125_;
v_isShared_3143_ = v_isSharedCheck_3170_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_inheritedTraceOptions_3140_);
lean_inc(v_cancelTk_x3f_3138_);
lean_inc(v_currMacroScope_3137_);
lean_inc(v_quotContext_3136_);
lean_inc(v_maxHeartbeats_3135_);
lean_inc(v_initHeartbeats_3134_);
lean_inc(v_openDecls_3133_);
lean_inc(v_currNamespace_3132_);
lean_inc(v_ref_3131_);
lean_inc(v_currRecDepth_3130_);
lean_inc(v_fileMap_3129_);
lean_inc(v_fileName_3128_);
lean_dec(v___y_3125_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3170_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v_env_3144_; lean_object* v_nextMacroScope_3145_; lean_object* v_ngen_3146_; lean_object* v_auxDeclNGen_3147_; lean_object* v_traceState_3148_; lean_object* v_messages_3149_; lean_object* v_infoState_3150_; lean_object* v_snapshotTasks_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3155_; 
v_env_3144_ = lean_ctor_get(v___x_3127_, 0);
lean_inc_ref(v_env_3144_);
v_nextMacroScope_3145_ = lean_ctor_get(v___x_3127_, 1);
lean_inc(v_nextMacroScope_3145_);
v_ngen_3146_ = lean_ctor_get(v___x_3127_, 2);
lean_inc_ref(v_ngen_3146_);
v_auxDeclNGen_3147_ = lean_ctor_get(v___x_3127_, 3);
lean_inc_ref(v_auxDeclNGen_3147_);
v_traceState_3148_ = lean_ctor_get(v___x_3127_, 4);
lean_inc_ref(v_traceState_3148_);
v_messages_3149_ = lean_ctor_get(v___x_3127_, 6);
lean_inc_ref(v_messages_3149_);
v_infoState_3150_ = lean_ctor_get(v___x_3127_, 7);
lean_inc_ref(v_infoState_3150_);
v_snapshotTasks_3151_ = lean_ctor_get(v___x_3127_, 8);
lean_inc_ref(v_snapshotTasks_3151_);
lean_dec(v___x_3127_);
v___x_3152_ = l_Lean_maxRecDepth;
v___x_3153_ = l_Lean_Option_get___at___00main_spec__9(v___x_2927_, v___x_3152_);
lean_inc_ref(v___x_2927_);
if (v_isShared_3143_ == 0)
{
lean_ctor_set(v___x_3142_, 4, v___x_3153_);
lean_ctor_set(v___x_3142_, 2, v___x_2927_);
v___x_3155_ = v___x_3142_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_fileName_3128_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v_fileMap_3129_);
lean_ctor_set(v_reuseFailAlloc_3169_, 2, v___x_2927_);
lean_ctor_set(v_reuseFailAlloc_3169_, 3, v_currRecDepth_3130_);
lean_ctor_set(v_reuseFailAlloc_3169_, 4, v___x_3153_);
lean_ctor_set(v_reuseFailAlloc_3169_, 5, v_ref_3131_);
lean_ctor_set(v_reuseFailAlloc_3169_, 6, v_currNamespace_3132_);
lean_ctor_set(v_reuseFailAlloc_3169_, 7, v_openDecls_3133_);
lean_ctor_set(v_reuseFailAlloc_3169_, 8, v_initHeartbeats_3134_);
lean_ctor_set(v_reuseFailAlloc_3169_, 9, v_maxHeartbeats_3135_);
lean_ctor_set(v_reuseFailAlloc_3169_, 10, v_quotContext_3136_);
lean_ctor_set(v_reuseFailAlloc_3169_, 11, v_currMacroScope_3137_);
lean_ctor_set(v_reuseFailAlloc_3169_, 12, v_cancelTk_x3f_3138_);
lean_ctor_set(v_reuseFailAlloc_3169_, 13, v_inheritedTraceOptions_3140_);
lean_ctor_set_uint8(v_reuseFailAlloc_3169_, sizeof(void*)*14 + 1, v_suppressElabErrors_3139_);
v___x_3155_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
lean_object* v___x_3156_; uint8_t v___x_3157_; 
lean_ctor_set_uint8(v___x_3155_, sizeof(void*)*14, v___y_3112_);
v___x_3156_ = lean_array_get_size(v___y_3124_);
v___x_3157_ = lean_nat_dec_lt(v___x_2926_, v___x_3156_);
if (v___x_3157_ == 0)
{
lean_object* v___x_3158_; 
lean_inc_ref(v___y_3117_);
v___x_3158_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3117_, v_env_3144_, v___x_2920_);
v___y_3060_ = v___y_3103_;
v___y_3061_ = v___y_3104_;
v___y_3062_ = v___y_3105_;
v___y_3063_ = v___y_3107_;
v___y_3064_ = v___y_3106_;
v___y_3065_ = v___y_3108_;
v___y_3066_ = v___y_3110_;
v___y_3067_ = v___y_3109_;
v___y_3068_ = v___y_3111_;
v___y_3069_ = v___x_3155_;
v___y_3070_ = v___y_3113_;
v___y_3071_ = v___y_3114_;
v___y_3072_ = v___y_3115_;
v___y_3073_ = v___y_3116_;
v___y_3074_ = v___y_3118_;
v_nextMacroScope_3075_ = v_nextMacroScope_3145_;
v_ngen_3076_ = v_ngen_3146_;
v_auxDeclNGen_3077_ = v_auxDeclNGen_3147_;
v_traceState_3078_ = v_traceState_3148_;
v_messages_3079_ = v_messages_3149_;
v_infoState_3080_ = v_infoState_3150_;
v_snapshotTasks_3081_ = v_snapshotTasks_3151_;
v___y_3082_ = v___y_3126_;
v___y_3083_ = v___y_3119_;
v___y_3084_ = v___y_3120_;
v___y_3085_ = v___y_3121_;
v___y_3086_ = v___y_3122_;
v___y_3087_ = v___y_3123_;
v___y_3088_ = v___y_3124_;
v___y_3089_ = v___x_3158_;
goto v___jp_3059_;
}
else
{
uint8_t v___x_3159_; 
v___x_3159_ = lean_nat_dec_le(v___x_3156_, v___x_3156_);
if (v___x_3159_ == 0)
{
if (v___x_3157_ == 0)
{
lean_object* v___x_3160_; 
lean_inc_ref(v___y_3117_);
v___x_3160_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3117_, v_env_3144_, v___x_2920_);
v___y_3060_ = v___y_3103_;
v___y_3061_ = v___y_3104_;
v___y_3062_ = v___y_3105_;
v___y_3063_ = v___y_3107_;
v___y_3064_ = v___y_3106_;
v___y_3065_ = v___y_3108_;
v___y_3066_ = v___y_3110_;
v___y_3067_ = v___y_3109_;
v___y_3068_ = v___y_3111_;
v___y_3069_ = v___x_3155_;
v___y_3070_ = v___y_3113_;
v___y_3071_ = v___y_3114_;
v___y_3072_ = v___y_3115_;
v___y_3073_ = v___y_3116_;
v___y_3074_ = v___y_3118_;
v_nextMacroScope_3075_ = v_nextMacroScope_3145_;
v_ngen_3076_ = v_ngen_3146_;
v_auxDeclNGen_3077_ = v_auxDeclNGen_3147_;
v_traceState_3078_ = v_traceState_3148_;
v_messages_3079_ = v_messages_3149_;
v_infoState_3080_ = v_infoState_3150_;
v_snapshotTasks_3081_ = v_snapshotTasks_3151_;
v___y_3082_ = v___y_3126_;
v___y_3083_ = v___y_3119_;
v___y_3084_ = v___y_3120_;
v___y_3085_ = v___y_3121_;
v___y_3086_ = v___y_3122_;
v___y_3087_ = v___y_3123_;
v___y_3088_ = v___y_3124_;
v___y_3089_ = v___x_3160_;
goto v___jp_3059_;
}
else
{
size_t v___x_3161_; size_t v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3161_ = ((size_t)0ULL);
v___x_3162_ = lean_usize_of_nat(v___x_3156_);
v___x_3163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3124_, v___x_3161_, v___x_3162_, v___x_2920_);
lean_inc_ref(v___y_3117_);
v___x_3164_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3117_, v_env_3144_, v___x_3163_);
v___y_3060_ = v___y_3103_;
v___y_3061_ = v___y_3104_;
v___y_3062_ = v___y_3105_;
v___y_3063_ = v___y_3107_;
v___y_3064_ = v___y_3106_;
v___y_3065_ = v___y_3108_;
v___y_3066_ = v___y_3110_;
v___y_3067_ = v___y_3109_;
v___y_3068_ = v___y_3111_;
v___y_3069_ = v___x_3155_;
v___y_3070_ = v___y_3113_;
v___y_3071_ = v___y_3114_;
v___y_3072_ = v___y_3115_;
v___y_3073_ = v___y_3116_;
v___y_3074_ = v___y_3118_;
v_nextMacroScope_3075_ = v_nextMacroScope_3145_;
v_ngen_3076_ = v_ngen_3146_;
v_auxDeclNGen_3077_ = v_auxDeclNGen_3147_;
v_traceState_3078_ = v_traceState_3148_;
v_messages_3079_ = v_messages_3149_;
v_infoState_3080_ = v_infoState_3150_;
v_snapshotTasks_3081_ = v_snapshotTasks_3151_;
v___y_3082_ = v___y_3126_;
v___y_3083_ = v___y_3119_;
v___y_3084_ = v___y_3120_;
v___y_3085_ = v___y_3121_;
v___y_3086_ = v___y_3122_;
v___y_3087_ = v___y_3123_;
v___y_3088_ = v___y_3124_;
v___y_3089_ = v___x_3164_;
goto v___jp_3059_;
}
}
else
{
size_t v___x_3165_; size_t v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3165_ = ((size_t)0ULL);
v___x_3166_ = lean_usize_of_nat(v___x_3156_);
v___x_3167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3124_, v___x_3165_, v___x_3166_, v___x_2920_);
lean_inc_ref(v___y_3117_);
v___x_3168_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3117_, v_env_3144_, v___x_3167_);
v___y_3060_ = v___y_3103_;
v___y_3061_ = v___y_3104_;
v___y_3062_ = v___y_3105_;
v___y_3063_ = v___y_3107_;
v___y_3064_ = v___y_3106_;
v___y_3065_ = v___y_3108_;
v___y_3066_ = v___y_3110_;
v___y_3067_ = v___y_3109_;
v___y_3068_ = v___y_3111_;
v___y_3069_ = v___x_3155_;
v___y_3070_ = v___y_3113_;
v___y_3071_ = v___y_3114_;
v___y_3072_ = v___y_3115_;
v___y_3073_ = v___y_3116_;
v___y_3074_ = v___y_3118_;
v_nextMacroScope_3075_ = v_nextMacroScope_3145_;
v_ngen_3076_ = v_ngen_3146_;
v_auxDeclNGen_3077_ = v_auxDeclNGen_3147_;
v_traceState_3078_ = v_traceState_3148_;
v_messages_3079_ = v_messages_3149_;
v_infoState_3080_ = v_infoState_3150_;
v_snapshotTasks_3081_ = v_snapshotTasks_3151_;
v___y_3082_ = v___y_3126_;
v___y_3083_ = v___y_3119_;
v___y_3084_ = v___y_3120_;
v___y_3085_ = v___y_3121_;
v___y_3086_ = v___y_3122_;
v___y_3087_ = v___y_3123_;
v___y_3088_ = v___y_3124_;
v___y_3089_ = v___x_3168_;
goto v___jp_3059_;
}
}
}
}
}
v___jp_3173_:
{
if (v___y_3197_ == 0)
{
lean_object* v___x_3198_; lean_object* v_env_3199_; lean_object* v_nextMacroScope_3200_; lean_object* v_ngen_3201_; lean_object* v_auxDeclNGen_3202_; lean_object* v_traceState_3203_; lean_object* v_messages_3204_; lean_object* v_infoState_3205_; lean_object* v_snapshotTasks_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3215_; 
v___x_3198_ = lean_st_ref_take(v___y_3193_);
v_env_3199_ = lean_ctor_get(v___x_3198_, 0);
v_nextMacroScope_3200_ = lean_ctor_get(v___x_3198_, 1);
v_ngen_3201_ = lean_ctor_get(v___x_3198_, 2);
v_auxDeclNGen_3202_ = lean_ctor_get(v___x_3198_, 3);
v_traceState_3203_ = lean_ctor_get(v___x_3198_, 4);
v_messages_3204_ = lean_ctor_get(v___x_3198_, 6);
v_infoState_3205_ = lean_ctor_get(v___x_3198_, 7);
v_snapshotTasks_3206_ = lean_ctor_get(v___x_3198_, 8);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3215_ == 0)
{
lean_object* v_unused_3216_; 
v_unused_3216_ = lean_ctor_get(v___x_3198_, 5);
lean_dec(v_unused_3216_);
v___x_3208_ = v___x_3198_;
v_isShared_3209_ = v_isSharedCheck_3215_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_snapshotTasks_3206_);
lean_inc(v_infoState_3205_);
lean_inc(v_messages_3204_);
lean_inc(v_traceState_3203_);
lean_inc(v_auxDeclNGen_3202_);
lean_inc(v_ngen_3201_);
lean_inc(v_nextMacroScope_3200_);
lean_inc(v_env_3199_);
lean_dec(v___x_3198_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3215_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3210_; lean_object* v___x_3212_; 
v___x_3210_ = l_Lean_Kernel_enableDiag(v_env_3199_, v___y_3184_);
lean_inc_ref(v___y_3185_);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 5, v___y_3185_);
lean_ctor_set(v___x_3208_, 0, v___x_3210_);
v___x_3212_ = v___x_3208_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3210_);
lean_ctor_set(v_reuseFailAlloc_3214_, 1, v_nextMacroScope_3200_);
lean_ctor_set(v_reuseFailAlloc_3214_, 2, v_ngen_3201_);
lean_ctor_set(v_reuseFailAlloc_3214_, 3, v_auxDeclNGen_3202_);
lean_ctor_set(v_reuseFailAlloc_3214_, 4, v_traceState_3203_);
lean_ctor_set(v_reuseFailAlloc_3214_, 5, v___y_3185_);
lean_ctor_set(v_reuseFailAlloc_3214_, 6, v_messages_3204_);
lean_ctor_set(v_reuseFailAlloc_3214_, 7, v_infoState_3205_);
lean_ctor_set(v_reuseFailAlloc_3214_, 8, v_snapshotTasks_3206_);
v___x_3212_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
lean_object* v___x_3213_; 
v___x_3213_ = lean_st_ref_set(v___y_3193_, v___x_3212_);
lean_inc(v___y_3193_);
v___y_3103_ = v___y_3174_;
v___y_3104_ = v___y_3175_;
v___y_3105_ = v___y_3176_;
v___y_3106_ = v___y_3178_;
v___y_3107_ = v___y_3177_;
v___y_3108_ = v___y_3179_;
v___y_3109_ = v___y_3181_;
v___y_3110_ = v___y_3180_;
v___y_3111_ = v___y_3182_;
v___y_3112_ = v___y_3184_;
v___y_3113_ = v___y_3185_;
v___y_3114_ = v___y_3186_;
v___y_3115_ = v___y_3187_;
v___y_3116_ = v___y_3188_;
v___y_3117_ = v___y_3189_;
v___y_3118_ = v___y_3190_;
v___y_3119_ = v___y_3191_;
v___y_3120_ = v___y_3192_;
v___y_3121_ = v___y_3193_;
v___y_3122_ = v___y_3194_;
v___y_3123_ = v___y_3196_;
v___y_3124_ = v___y_3195_;
v___y_3125_ = v___y_3183_;
v___y_3126_ = v___y_3193_;
goto v___jp_3102_;
}
}
}
else
{
lean_inc(v___y_3193_);
v___y_3103_ = v___y_3174_;
v___y_3104_ = v___y_3175_;
v___y_3105_ = v___y_3176_;
v___y_3106_ = v___y_3178_;
v___y_3107_ = v___y_3177_;
v___y_3108_ = v___y_3179_;
v___y_3109_ = v___y_3181_;
v___y_3110_ = v___y_3180_;
v___y_3111_ = v___y_3182_;
v___y_3112_ = v___y_3184_;
v___y_3113_ = v___y_3185_;
v___y_3114_ = v___y_3186_;
v___y_3115_ = v___y_3187_;
v___y_3116_ = v___y_3188_;
v___y_3117_ = v___y_3189_;
v___y_3118_ = v___y_3190_;
v___y_3119_ = v___y_3191_;
v___y_3120_ = v___y_3192_;
v___y_3121_ = v___y_3193_;
v___y_3122_ = v___y_3194_;
v___y_3123_ = v___y_3196_;
v___y_3124_ = v___y_3195_;
v___y_3125_ = v___y_3183_;
v___y_3126_ = v___y_3193_;
goto v___jp_3102_;
}
}
v___jp_3220_:
{
lean_object* v___x_3230_; 
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 1, v___y_3228_);
lean_ctor_set(v___x_2912_, 0, v___y_3223_);
v___x_3230_ = v___x_2912_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___y_3223_);
lean_ctor_set(v_reuseFailAlloc_3325_, 1, v___y_3228_);
v___x_3230_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v_moduleData_3234_; lean_object* v___x_3235_; uint8_t v___x_3236_; 
v___x_3231_ = lean_box(0);
lean_inc_ref(v___y_3225_);
v___x_3232_ = l_Lean_EnvExtension_setState___redArg(v___y_3225_, v___y_3226_, v___x_3230_, v___x_3231_);
v___x_3233_ = l_Lean_Environment_header(v___x_3232_);
v_moduleData_3234_ = lean_ctor_get(v___x_3233_, 6);
lean_inc_ref(v_moduleData_3234_);
lean_dec_ref(v___x_3233_);
v___x_3235_ = lean_array_get_size(v_moduleData_3234_);
v___x_3236_ = lean_nat_dec_lt(v___y_3224_, v___x_3235_);
if (v___x_3236_ == 0)
{
lean_object* v___x_3237_; lean_object* v___x_3238_; 
lean_dec_ref(v_moduleData_3234_);
lean_dec_ref(v___x_3232_);
lean_dec(v___y_3227_);
lean_dec(v___y_3224_);
lean_dec(v___y_3221_);
lean_dec_ref(v___x_2927_);
lean_dec(v_fst_2909_);
lean_dec(v_name_2896_);
lean_dec(v_head_2889_);
lean_dec(v_head_2888_);
v___x_3237_ = lean_obj_once(&l_main___closed__21, &l_main___closed__21_once, _init_l_main___closed__21);
v___x_3238_ = l_panic___at___00main_spec__5(v___x_3237_);
return v___x_3238_;
}
else
{
lean_object* v_base_3239_; lean_object* v_private_3240_; lean_object* v_header_3241_; lean_object* v_serverBaseExts_3242_; lean_object* v_checked_3243_; lean_object* v_asyncConstsMap_3244_; lean_object* v_asyncCtx_x3f_3245_; lean_object* v_importRealizationCtx_x3f_3246_; lean_object* v_localRealizationCtxMap_3247_; lean_object* v_allRealizations_3248_; uint8_t v_isExporting_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3323_; 
v_base_3239_ = lean_ctor_get(v___x_3232_, 0);
lean_inc_ref(v_base_3239_);
v_private_3240_ = lean_ctor_get(v_base_3239_, 0);
lean_inc(v_private_3240_);
v_header_3241_ = lean_ctor_get(v_private_3240_, 5);
lean_inc_ref(v_header_3241_);
v_serverBaseExts_3242_ = lean_ctor_get(v___x_3232_, 1);
v_checked_3243_ = lean_ctor_get(v___x_3232_, 2);
v_asyncConstsMap_3244_ = lean_ctor_get(v___x_3232_, 3);
v_asyncCtx_x3f_3245_ = lean_ctor_get(v___x_3232_, 4);
v_importRealizationCtx_x3f_3246_ = lean_ctor_get(v___x_3232_, 5);
v_localRealizationCtxMap_3247_ = lean_ctor_get(v___x_3232_, 6);
v_allRealizations_3248_ = lean_ctor_get(v___x_3232_, 7);
v_isExporting_3249_ = lean_ctor_get_uint8(v___x_3232_, sizeof(void*)*8);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3323_ == 0)
{
lean_object* v_unused_3324_; 
v_unused_3324_ = lean_ctor_get(v___x_3232_, 0);
lean_dec(v_unused_3324_);
v___x_3251_ = v___x_3232_;
v_isShared_3252_ = v_isSharedCheck_3323_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_allRealizations_3248_);
lean_inc(v_localRealizationCtxMap_3247_);
lean_inc(v_importRealizationCtx_x3f_3246_);
lean_inc(v_asyncCtx_x3f_3245_);
lean_inc(v_asyncConstsMap_3244_);
lean_inc(v_checked_3243_);
lean_inc(v_serverBaseExts_3242_);
lean_dec(v___x_3232_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3323_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v_public_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3321_; 
v_public_3253_ = lean_ctor_get(v_base_3239_, 1);
v_isSharedCheck_3321_ = !lean_is_exclusive(v_base_3239_);
if (v_isSharedCheck_3321_ == 0)
{
lean_object* v_unused_3322_; 
v_unused_3322_ = lean_ctor_get(v_base_3239_, 0);
lean_dec(v_unused_3322_);
v___x_3255_ = v_base_3239_;
v_isShared_3256_ = v_isSharedCheck_3321_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_public_3253_);
lean_dec(v_base_3239_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3321_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v_constants_3257_; uint8_t v_quotInit_3258_; lean_object* v_diagnostics_3259_; lean_object* v_const2ModIdx_3260_; lean_object* v_extensions_3261_; lean_object* v_irBaseExts_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3319_; 
v_constants_3257_ = lean_ctor_get(v_private_3240_, 0);
v_quotInit_3258_ = lean_ctor_get_uint8(v_private_3240_, sizeof(void*)*6);
v_diagnostics_3259_ = lean_ctor_get(v_private_3240_, 1);
v_const2ModIdx_3260_ = lean_ctor_get(v_private_3240_, 2);
v_extensions_3261_ = lean_ctor_get(v_private_3240_, 3);
v_irBaseExts_3262_ = lean_ctor_get(v_private_3240_, 4);
v_isSharedCheck_3319_ = !lean_is_exclusive(v_private_3240_);
if (v_isSharedCheck_3319_ == 0)
{
lean_object* v_unused_3320_; 
v_unused_3320_ = lean_ctor_get(v_private_3240_, 5);
lean_dec(v_unused_3320_);
v___x_3264_ = v_private_3240_;
v_isShared_3265_ = v_isSharedCheck_3319_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_irBaseExts_3262_);
lean_inc(v_extensions_3261_);
lean_inc(v_const2ModIdx_3260_);
lean_inc(v_diagnostics_3259_);
lean_inc(v_constants_3257_);
lean_dec(v_private_3240_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3319_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
uint32_t v_trustLevel_3266_; lean_object* v_mainModule_3267_; uint8_t v_isModule_3268_; lean_object* v_regions_3269_; lean_object* v_modules_3270_; lean_object* v_moduleName2Idx_3271_; lean_object* v_importAllModules_3272_; lean_object* v_moduleData_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3317_; 
v_trustLevel_3266_ = lean_ctor_get_uint32(v_header_3241_, sizeof(void*)*7);
v_mainModule_3267_ = lean_ctor_get(v_header_3241_, 0);
v_isModule_3268_ = lean_ctor_get_uint8(v_header_3241_, sizeof(void*)*7 + 4);
v_regions_3269_ = lean_ctor_get(v_header_3241_, 2);
v_modules_3270_ = lean_ctor_get(v_header_3241_, 3);
v_moduleName2Idx_3271_ = lean_ctor_get(v_header_3241_, 4);
v_importAllModules_3272_ = lean_ctor_get(v_header_3241_, 5);
v_moduleData_3273_ = lean_ctor_get(v_header_3241_, 6);
v_isSharedCheck_3317_ = !lean_is_exclusive(v_header_3241_);
if (v_isSharedCheck_3317_ == 0)
{
lean_object* v_unused_3318_; 
v_unused_3318_ = lean_ctor_get(v_header_3241_, 1);
lean_dec(v_unused_3318_);
v___x_3275_ = v_header_3241_;
v_isShared_3276_ = v_isSharedCheck_3317_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_moduleData_3273_);
lean_inc(v_importAllModules_3272_);
lean_inc(v_moduleName2Idx_3271_);
lean_inc(v_modules_3270_);
lean_inc(v_regions_3269_);
lean_inc(v_mainModule_3267_);
lean_dec(v_header_3241_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3317_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3277_; lean_object* v_imports_3278_; lean_object* v___x_3280_; 
v___x_3277_ = lean_array_fget(v_moduleData_3234_, v___y_3224_);
lean_dec_ref(v_moduleData_3234_);
v_imports_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc_ref(v_imports_3278_);
lean_dec(v___x_3277_);
if (v_isShared_3276_ == 0)
{
lean_ctor_set(v___x_3275_, 1, v_imports_3278_);
v___x_3280_ = v___x_3275_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 7, 5);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_mainModule_3267_);
lean_ctor_set(v_reuseFailAlloc_3316_, 1, v_imports_3278_);
lean_ctor_set(v_reuseFailAlloc_3316_, 2, v_regions_3269_);
lean_ctor_set(v_reuseFailAlloc_3316_, 3, v_modules_3270_);
lean_ctor_set(v_reuseFailAlloc_3316_, 4, v_moduleName2Idx_3271_);
lean_ctor_set(v_reuseFailAlloc_3316_, 5, v_importAllModules_3272_);
lean_ctor_set(v_reuseFailAlloc_3316_, 6, v_moduleData_3273_);
lean_ctor_set_uint32(v_reuseFailAlloc_3316_, sizeof(void*)*7, v_trustLevel_3266_);
lean_ctor_set_uint8(v_reuseFailAlloc_3316_, sizeof(void*)*7 + 4, v_isModule_3268_);
v___x_3280_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
lean_object* v___x_3282_; 
if (v_isShared_3265_ == 0)
{
lean_ctor_set(v___x_3264_, 5, v___x_3280_);
v___x_3282_ = v___x_3264_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_constants_3257_);
lean_ctor_set(v_reuseFailAlloc_3315_, 1, v_diagnostics_3259_);
lean_ctor_set(v_reuseFailAlloc_3315_, 2, v_const2ModIdx_3260_);
lean_ctor_set(v_reuseFailAlloc_3315_, 3, v_extensions_3261_);
lean_ctor_set(v_reuseFailAlloc_3315_, 4, v_irBaseExts_3262_);
lean_ctor_set(v_reuseFailAlloc_3315_, 5, v___x_3280_);
lean_ctor_set_uint8(v_reuseFailAlloc_3315_, sizeof(void*)*6, v_quotInit_3258_);
v___x_3282_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
lean_object* v___x_3284_; 
if (v_isShared_3256_ == 0)
{
lean_ctor_set(v___x_3255_, 0, v___x_3282_);
v___x_3284_ = v___x_3255_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3282_);
lean_ctor_set(v_reuseFailAlloc_3314_, 1, v_public_3253_);
v___x_3284_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
lean_object* v___x_3286_; 
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 0, v___x_3284_);
v___x_3286_ = v___x_3251_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3284_);
lean_ctor_set(v_reuseFailAlloc_3313_, 1, v_serverBaseExts_3242_);
lean_ctor_set(v_reuseFailAlloc_3313_, 2, v_checked_3243_);
lean_ctor_set(v_reuseFailAlloc_3313_, 3, v_asyncConstsMap_3244_);
lean_ctor_set(v_reuseFailAlloc_3313_, 4, v_asyncCtx_x3f_3245_);
lean_ctor_set(v_reuseFailAlloc_3313_, 5, v_importRealizationCtx_x3f_3246_);
lean_ctor_set(v_reuseFailAlloc_3313_, 6, v_localRealizationCtxMap_3247_);
lean_ctor_set(v_reuseFailAlloc_3313_, 7, v_allRealizations_3248_);
lean_ctor_set_uint8(v_reuseFailAlloc_3313_, sizeof(void*)*8, v_isExporting_3249_);
v___x_3286_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v_env_3309_; lean_object* v___x_3310_; uint8_t v___x_3311_; uint8_t v___x_3312_; 
v___x_3287_ = l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
v___x_3288_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2921_, v___x_3287_, v___x_3286_, v___y_3224_, v___y_3222_);
lean_dec(v___y_3224_);
v___x_3289_ = l_Lean_firstFrontendMacroScope;
v___x_3290_ = lean_obj_once(&l_main___closed__22, &l_main___closed__22_once, _init_l_main___closed__22);
v___x_3291_ = ((lean_object*)(l_main___closed__25));
lean_inc_n(v___y_3227_, 3);
v___x_3292_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3292_, 0, v___y_3227_);
lean_ctor_set(v___x_3292_, 1, v___x_3219_);
lean_ctor_set(v___x_3292_, 2, v___x_2907_);
v___x_3293_ = lean_obj_once(&l_main___closed__26, &l_main___closed__26_once, _init_l_main___closed__26);
v___x_3294_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_3295_ = lean_obj_once(&l_main___closed__30, &l_main___closed__30_once, _init_l_main___closed__30);
v___x_3296_ = lean_obj_once(&l_main___closed__31, &l_main___closed__31_once, _init_l_main___closed__31);
v___x_3297_ = ((lean_object*)(l_main___closed__32));
lean_inc_ref(v___x_3292_);
v___x_3298_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3286_);
lean_ctor_set(v___x_3298_, 1, v___x_3290_);
lean_ctor_set(v___x_3298_, 2, v___x_3291_);
lean_ctor_set(v___x_3298_, 3, v___x_3292_);
lean_ctor_set(v___x_3298_, 4, v___x_3293_);
lean_ctor_set(v___x_3298_, 5, v___x_3294_);
lean_ctor_set(v___x_3298_, 6, v___x_3295_);
lean_ctor_set(v___x_3298_, 7, v___x_3296_);
lean_ctor_set(v___x_3298_, 8, v___x_3297_);
v___x_3299_ = lean_st_mk_ref(v___x_3298_);
v___x_3300_ = l_Lean_inheritedTraceOptions;
v___x_3301_ = lean_st_ref_get(v___x_3300_);
v___x_3302_ = lean_st_ref_get(v___x_3299_);
v___x_3303_ = l_Lean_instInhabitedFileMap_default;
v___x_3304_ = lean_unsigned_to_nat(1000u);
v___x_3305_ = lean_box(0);
v___x_3306_ = l_Lean_Core_getMaxHeartbeats(v___x_2927_);
v___x_3307_ = lean_box(0);
lean_inc_ref(v___x_2927_);
lean_inc(v_head_2888_);
v___x_3308_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3308_, 0, v_head_2888_);
lean_ctor_set(v___x_3308_, 1, v___x_3303_);
lean_ctor_set(v___x_3308_, 2, v___x_2927_);
lean_ctor_set(v___x_3308_, 3, v___x_2926_);
lean_ctor_set(v___x_3308_, 4, v___x_3304_);
lean_ctor_set(v___x_3308_, 5, v___x_3305_);
lean_ctor_set(v___x_3308_, 6, v___y_3227_);
lean_ctor_set(v___x_3308_, 7, v___x_2907_);
lean_ctor_set(v___x_3308_, 8, v___x_2926_);
lean_ctor_set(v___x_3308_, 9, v___x_3306_);
lean_ctor_set(v___x_3308_, 10, v___y_3227_);
lean_ctor_set(v___x_3308_, 11, v___x_3289_);
lean_ctor_set(v___x_3308_, 12, v___x_3307_);
lean_ctor_set(v___x_3308_, 13, v___x_3301_);
lean_ctor_set_uint8(v___x_3308_, sizeof(void*)*14, v___x_2898_);
lean_ctor_set_uint8(v___x_3308_, sizeof(void*)*14 + 1, v___x_2898_);
v_env_3309_ = lean_ctor_get(v___x_3302_, 0);
lean_inc_ref(v_env_3309_);
lean_dec(v___x_3302_);
v___x_3310_ = l_Lean_diagnostics;
v___x_3311_ = l_Lean_Option_get___at___00main_spec__8(v___x_2927_, v___x_3310_);
v___x_3312_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3309_);
lean_dec_ref(v_env_3309_);
if (v___x_3312_ == 0)
{
if (v___x_3311_ == 0)
{
v___y_3174_ = v___x_2907_;
v___y_3175_ = v___x_3294_;
v___y_3176_ = v___x_3307_;
v___y_3177_ = v___x_3303_;
v___y_3178_ = v___x_3305_;
v___y_3179_ = v___x_3289_;
v___y_3180_ = v___x_3300_;
v___y_3181_ = v___x_3236_;
v___y_3182_ = v___y_3221_;
v___y_3183_ = v___x_3308_;
v___y_3184_ = v___x_3311_;
v___y_3185_ = v___x_3294_;
v___y_3186_ = v___x_3292_;
v___y_3187_ = v___x_3291_;
v___y_3188_ = v___x_3293_;
v___y_3189_ = v___x_3287_;
v___y_3190_ = v___x_3290_;
v___y_3191_ = v___x_3297_;
v___y_3192_ = v___x_3295_;
v___y_3193_ = v___x_3299_;
v___y_3194_ = v___x_3296_;
v___y_3195_ = v___x_3288_;
v___y_3196_ = v___y_3227_;
v___y_3197_ = v___x_3236_;
goto v___jp_3173_;
}
else
{
v___y_3174_ = v___x_2907_;
v___y_3175_ = v___x_3294_;
v___y_3176_ = v___x_3307_;
v___y_3177_ = v___x_3303_;
v___y_3178_ = v___x_3305_;
v___y_3179_ = v___x_3289_;
v___y_3180_ = v___x_3300_;
v___y_3181_ = v___x_3236_;
v___y_3182_ = v___y_3221_;
v___y_3183_ = v___x_3308_;
v___y_3184_ = v___x_3311_;
v___y_3185_ = v___x_3294_;
v___y_3186_ = v___x_3292_;
v___y_3187_ = v___x_3291_;
v___y_3188_ = v___x_3293_;
v___y_3189_ = v___x_3287_;
v___y_3190_ = v___x_3290_;
v___y_3191_ = v___x_3297_;
v___y_3192_ = v___x_3295_;
v___y_3193_ = v___x_3299_;
v___y_3194_ = v___x_3296_;
v___y_3195_ = v___x_3288_;
v___y_3196_ = v___y_3227_;
v___y_3197_ = v___x_3312_;
goto v___jp_3173_;
}
}
else
{
v___y_3174_ = v___x_2907_;
v___y_3175_ = v___x_3294_;
v___y_3176_ = v___x_3307_;
v___y_3177_ = v___x_3303_;
v___y_3178_ = v___x_3305_;
v___y_3179_ = v___x_3289_;
v___y_3180_ = v___x_3300_;
v___y_3181_ = v___x_3236_;
v___y_3182_ = v___y_3221_;
v___y_3183_ = v___x_3308_;
v___y_3184_ = v___x_3311_;
v___y_3185_ = v___x_3294_;
v___y_3186_ = v___x_3292_;
v___y_3187_ = v___x_3291_;
v___y_3188_ = v___x_3293_;
v___y_3189_ = v___x_3287_;
v___y_3190_ = v___x_3290_;
v___y_3191_ = v___x_3297_;
v___y_3192_ = v___x_3295_;
v___y_3193_ = v___x_3299_;
v___y_3194_ = v___x_3296_;
v___y_3195_ = v___x_3288_;
v___y_3196_ = v___y_3227_;
v___y_3197_ = v___x_3311_;
goto v___jp_3173_;
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
v___jp_3326_:
{
lean_object* v___x_3332_; lean_object* v_toEnvExtension_3333_; lean_object* v_asyncMode_3334_; lean_object* v___x_3335_; lean_object* v_importedEntries_3336_; lean_object* v_state_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; uint8_t v___x_3340_; 
v___x_3332_ = l_Lean_IR_declMapExt;
v_toEnvExtension_3333_ = lean_ctor_get(v___x_3332_, 0);
v_asyncMode_3334_ = lean_ctor_get(v_toEnvExtension_3333_, 2);
lean_inc(v___y_3330_);
lean_inc_ref(v___y_3331_);
v___x_3335_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2918_, v_toEnvExtension_3333_, v___y_3331_, v_asyncMode_3334_, v___y_3330_);
v_importedEntries_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc_ref(v_importedEntries_3336_);
v_state_3337_ = lean_ctor_get(v___x_3335_, 1);
lean_inc(v_state_3337_);
lean_dec(v___x_3335_);
v___x_3338_ = lean_array_get_borrowed(v___x_2919_, v_importedEntries_3336_, v___y_3329_);
v___x_3339_ = lean_array_get_size(v___x_3338_);
v___x_3340_ = lean_nat_dec_lt(v___x_2926_, v___x_3339_);
if (v___x_3340_ == 0)
{
v___y_3221_ = v___y_3327_;
v___y_3222_ = v___y_3328_;
v___y_3223_ = v_importedEntries_3336_;
v___y_3224_ = v___y_3329_;
v___y_3225_ = v_toEnvExtension_3333_;
v___y_3226_ = v___y_3331_;
v___y_3227_ = v___y_3330_;
v___y_3228_ = v_state_3337_;
goto v___jp_3220_;
}
else
{
uint8_t v___x_3341_; 
v___x_3341_ = lean_nat_dec_le(v___x_3339_, v___x_3339_);
if (v___x_3341_ == 0)
{
if (v___x_3340_ == 0)
{
v___y_3221_ = v___y_3327_;
v___y_3222_ = v___y_3328_;
v___y_3223_ = v_importedEntries_3336_;
v___y_3224_ = v___y_3329_;
v___y_3225_ = v_toEnvExtension_3333_;
v___y_3226_ = v___y_3331_;
v___y_3227_ = v___y_3330_;
v___y_3228_ = v_state_3337_;
goto v___jp_3220_;
}
else
{
size_t v___x_3342_; size_t v___x_3343_; lean_object* v___x_3344_; 
v___x_3342_ = ((size_t)0ULL);
v___x_3343_ = lean_usize_of_nat(v___x_3339_);
lean_inc_ref(v___y_3331_);
v___x_3344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3331_, v___x_3338_, v___x_3342_, v___x_3343_, v_state_3337_);
v___y_3221_ = v___y_3327_;
v___y_3222_ = v___y_3328_;
v___y_3223_ = v_importedEntries_3336_;
v___y_3224_ = v___y_3329_;
v___y_3225_ = v_toEnvExtension_3333_;
v___y_3226_ = v___y_3331_;
v___y_3227_ = v___y_3330_;
v___y_3228_ = v___x_3344_;
goto v___jp_3220_;
}
}
else
{
size_t v___x_3345_; size_t v___x_3346_; lean_object* v___x_3347_; 
v___x_3345_ = ((size_t)0ULL);
v___x_3346_ = lean_usize_of_nat(v___x_3339_);
lean_inc_ref(v___y_3331_);
v___x_3347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3331_, v___x_3338_, v___x_3345_, v___x_3346_, v_state_3337_);
v___y_3221_ = v___y_3327_;
v___y_3222_ = v___y_3328_;
v___y_3223_ = v_importedEntries_3336_;
v___y_3224_ = v___y_3329_;
v___y_3225_ = v_toEnvExtension_3333_;
v___y_3226_ = v___y_3331_;
v___y_3227_ = v___y_3330_;
v___y_3228_ = v___x_3347_;
goto v___jp_3220_;
}
}
}
v___jp_3348_:
{
uint8_t v___x_3356_; 
v___x_3356_ = lean_nat_dec_lt(v___x_2926_, v___y_3351_);
if (v___x_3356_ == 0)
{
lean_dec_ref(v___y_3352_);
lean_dec(v___y_3351_);
v___y_3327_ = v___y_3349_;
v___y_3328_ = v___y_3350_;
v___y_3329_ = v___y_3353_;
v___y_3330_ = v___y_3354_;
v___y_3331_ = v___y_3355_;
goto v___jp_3326_;
}
else
{
uint8_t v___x_3357_; 
v___x_3357_ = lean_nat_dec_le(v___y_3351_, v___y_3351_);
if (v___x_3357_ == 0)
{
if (v___x_3356_ == 0)
{
lean_dec_ref(v___y_3352_);
lean_dec(v___y_3351_);
v___y_3327_ = v___y_3349_;
v___y_3328_ = v___y_3350_;
v___y_3329_ = v___y_3353_;
v___y_3330_ = v___y_3354_;
v___y_3331_ = v___y_3355_;
goto v___jp_3326_;
}
else
{
size_t v___x_3358_; size_t v___x_3359_; lean_object* v___x_3360_; 
v___x_3358_ = ((size_t)0ULL);
v___x_3359_ = lean_usize_of_nat(v___y_3351_);
lean_dec(v___y_3351_);
v___x_3360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3352_, v___x_3358_, v___x_3359_, v___y_3355_);
lean_dec_ref(v___y_3352_);
v___y_3327_ = v___y_3349_;
v___y_3328_ = v___y_3350_;
v___y_3329_ = v___y_3353_;
v___y_3330_ = v___y_3354_;
v___y_3331_ = v___x_3360_;
goto v___jp_3326_;
}
}
else
{
size_t v___x_3361_; size_t v___x_3362_; lean_object* v___x_3363_; 
v___x_3361_ = ((size_t)0ULL);
v___x_3362_ = lean_usize_of_nat(v___y_3351_);
lean_dec(v___y_3351_);
v___x_3363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3352_, v___x_3361_, v___x_3362_, v___y_3355_);
lean_dec_ref(v___y_3352_);
v___y_3327_ = v___y_3349_;
v___y_3328_ = v___y_3350_;
v___y_3329_ = v___y_3353_;
v___y_3330_ = v___y_3354_;
v___y_3331_ = v___x_3363_;
goto v___jp_3326_;
}
}
}
v___jp_3364_:
{
lean_object* v___x_3371_; uint8_t v___x_3372_; 
v___x_3371_ = lean_array_get_size(v___y_3370_);
v___x_3372_ = lean_nat_dec_lt(v___x_2926_, v___x_3371_);
if (v___x_3372_ == 0)
{
v___y_3349_ = v___y_3366_;
v___y_3350_ = v___y_3367_;
v___y_3351_ = v___x_3371_;
v___y_3352_ = v___y_3370_;
v___y_3353_ = v___y_3365_;
v___y_3354_ = v___y_3369_;
v___y_3355_ = v___y_3368_;
goto v___jp_3348_;
}
else
{
uint8_t v___x_3373_; 
v___x_3373_ = lean_nat_dec_le(v___x_3371_, v___x_3371_);
if (v___x_3373_ == 0)
{
if (v___x_3372_ == 0)
{
v___y_3349_ = v___y_3366_;
v___y_3350_ = v___y_3367_;
v___y_3351_ = v___x_3371_;
v___y_3352_ = v___y_3370_;
v___y_3353_ = v___y_3365_;
v___y_3354_ = v___y_3369_;
v___y_3355_ = v___y_3368_;
goto v___jp_3348_;
}
else
{
size_t v___x_3374_; size_t v___x_3375_; lean_object* v___x_3376_; 
v___x_3374_ = ((size_t)0ULL);
v___x_3375_ = lean_usize_of_nat(v___x_3371_);
v___x_3376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3370_, v___x_3374_, v___x_3375_, v___y_3368_);
v___y_3349_ = v___y_3366_;
v___y_3350_ = v___y_3367_;
v___y_3351_ = v___x_3371_;
v___y_3352_ = v___y_3370_;
v___y_3353_ = v___y_3365_;
v___y_3354_ = v___y_3369_;
v___y_3355_ = v___x_3376_;
goto v___jp_3348_;
}
}
else
{
size_t v___x_3377_; size_t v___x_3378_; lean_object* v___x_3379_; 
v___x_3377_ = ((size_t)0ULL);
v___x_3378_ = lean_usize_of_nat(v___x_3371_);
v___x_3379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3370_, v___x_3377_, v___x_3378_, v___y_3368_);
v___y_3349_ = v___y_3366_;
v___y_3350_ = v___y_3367_;
v___y_3351_ = v___x_3371_;
v___y_3352_ = v___y_3370_;
v___y_3353_ = v___y_3365_;
v___y_3354_ = v___y_3369_;
v___y_3355_ = v___x_3379_;
goto v___jp_3348_;
}
}
}
v___jp_3383_:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___f_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3385_ = l_Lean_instInhabitedImportState_default;
v___x_3386_ = lean_box(v___x_3382_);
v___x_3387_ = lean_box(v___y_3384_);
v___x_3388_ = lean_box(v___x_2923_);
v___x_3389_ = lean_box(v___x_2898_);
lean_inc_ref(v___x_2927_);
lean_inc(v_name_2896_);
v___f_3390_ = lean_alloc_closure((void*)(l_main___lam__0___boxed), 10, 9);
lean_closure_set(v___f_3390_, 0, v___x_3385_);
lean_closure_set(v___f_3390_, 1, v___x_3381_);
lean_closure_set(v___f_3390_, 2, v___x_3386_);
lean_closure_set(v___f_3390_, 3, v___x_2920_);
lean_closure_set(v___f_3390_, 4, v___x_3387_);
lean_closure_set(v___f_3390_, 5, v_name_2896_);
lean_closure_set(v___f_3390_, 6, v___x_2927_);
lean_closure_set(v___f_3390_, 7, v___x_3388_);
lean_closure_set(v___f_3390_, 8, v___x_3389_);
v___x_3391_ = lean_alloc_closure((void*)(l_Lean_withImporting___boxed), 3, 2);
lean_closure_set(v___x_3391_, 0, lean_box(0));
lean_closure_set(v___x_3391_, 1, v___f_3390_);
v___x_3392_ = lean_box(0);
v___x_3393_ = l_Lean_profileitIOUnsafe___redArg(v___x_3217_, v___x_2927_, v___x_3391_, v___x_3392_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_a_3394_; lean_object* v___x_3395_; lean_object* v_ext_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
lean_inc(v_a_3394_);
lean_dec_ref(v___x_3393_);
v___x_3395_ = l_Lean_Compiler_CSimp_ext;
v_ext_3396_ = lean_ctor_get(v___x_3395_, 1);
lean_inc(v_name_2896_);
v___x_3397_ = l_Lean_Environment_setMainModule(v_a_3394_, v_name_2896_);
lean_inc_ref(v_ext_3396_);
v___x_3398_ = l_main___elam__0___redArg(v___x_3392_, v___x_2914_, v_ext_3396_, v___x_3397_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v___x_3400_; lean_object* v_ext_3401_; lean_object* v___x_3402_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3399_);
lean_dec_ref(v___x_3398_);
v___x_3400_ = l_Lean_Meta_instanceExtension;
v_ext_3401_ = lean_ctor_get(v___x_3400_, 1);
lean_inc_ref(v_ext_3401_);
v___x_3402_ = l_main___elam__0___redArg(v___x_3392_, v___x_2914_, v_ext_3401_, v_a_3399_);
if (lean_obj_tag(v___x_3402_) == 0)
{
lean_object* v_a_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v_a_3403_ = lean_ctor_get(v___x_3402_, 0);
lean_inc(v_a_3403_);
lean_dec_ref(v___x_3402_);
v___x_3404_ = l_Lean_classExtension;
v___x_3405_ = l_main___elam__0___redArg(v___x_3392_, v___x_2915_, v___x_3404_, v_a_3403_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
lean_dec_ref(v___x_3405_);
v___x_3407_ = l_Lean_Meta_Match_Extension_extension;
v___x_3408_ = l_main___elam__0___redArg(v___x_3392_, v___x_2916_, v___x_3407_, v_a_3406_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3437_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3411_ = v___x_3408_;
v_isShared_3412_ = v_isSharedCheck_3437_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3408_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3437_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3413_; 
v___x_3413_ = l_Lean_Environment_getModuleIdx_x3f(v_a_3409_, v_name_2896_);
if (lean_obj_tag(v___x_3413_) == 1)
{
lean_object* v_val_3414_; lean_object* v___x_3415_; uint8_t v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; uint8_t v___x_3420_; 
lean_del_object(v___x_3411_);
v_val_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_val_3414_);
lean_dec_ref(v___x_3413_);
v___x_3415_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_3416_ = 0;
v___x_3417_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2917_, v___x_3415_, v_a_3409_, v_val_3414_, v___x_3416_);
v___x_3418_ = lean_array_get_size(v___x_3417_);
v___x_3419_ = ((lean_object*)(l_main___closed__33));
v___x_3420_ = lean_nat_dec_lt(v___x_2926_, v___x_3418_);
if (v___x_3420_ == 0)
{
lean_dec_ref(v___x_3417_);
v___y_3365_ = v_val_3414_;
v___y_3366_ = v___x_3392_;
v___y_3367_ = v___x_3416_;
v___y_3368_ = v_a_3409_;
v___y_3369_ = v___x_3392_;
v___y_3370_ = v___x_3419_;
goto v___jp_3364_;
}
else
{
uint8_t v___x_3421_; 
v___x_3421_ = lean_nat_dec_le(v___x_3418_, v___x_3418_);
if (v___x_3421_ == 0)
{
if (v___x_3420_ == 0)
{
lean_dec_ref(v___x_3417_);
v___y_3365_ = v_val_3414_;
v___y_3366_ = v___x_3392_;
v___y_3367_ = v___x_3416_;
v___y_3368_ = v_a_3409_;
v___y_3369_ = v___x_3392_;
v___y_3370_ = v___x_3419_;
goto v___jp_3364_;
}
else
{
size_t v___x_3422_; size_t v___x_3423_; lean_object* v___x_3424_; 
v___x_3422_ = ((size_t)0ULL);
v___x_3423_ = lean_usize_of_nat(v___x_3418_);
lean_inc(v_a_3409_);
v___x_3424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3409_, v___x_3417_, v___x_3422_, v___x_3423_, v___x_3419_);
lean_dec_ref(v___x_3417_);
v___y_3365_ = v_val_3414_;
v___y_3366_ = v___x_3392_;
v___y_3367_ = v___x_3416_;
v___y_3368_ = v_a_3409_;
v___y_3369_ = v___x_3392_;
v___y_3370_ = v___x_3424_;
goto v___jp_3364_;
}
}
else
{
size_t v___x_3425_; size_t v___x_3426_; lean_object* v___x_3427_; 
v___x_3425_ = ((size_t)0ULL);
v___x_3426_ = lean_usize_of_nat(v___x_3418_);
lean_inc(v_a_3409_);
v___x_3427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3409_, v___x_3417_, v___x_3425_, v___x_3426_, v___x_3419_);
lean_dec_ref(v___x_3417_);
v___y_3365_ = v_val_3414_;
v___y_3366_ = v___x_3392_;
v___y_3367_ = v___x_3416_;
v___y_3368_ = v_a_3409_;
v___y_3369_ = v___x_3392_;
v___y_3370_ = v___x_3427_;
goto v___jp_3364_;
}
}
}
else
{
lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3435_; 
lean_dec(v___x_3413_);
lean_dec(v_a_3409_);
lean_dec_ref(v___x_2927_);
lean_del_object(v___x_2912_);
lean_dec(v_fst_2909_);
lean_dec(v_head_2889_);
lean_dec(v_head_2888_);
v___x_3428_ = ((lean_object*)(l_main___closed__34));
v___x_3429_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2896_, v___x_2923_);
v___x_3430_ = lean_string_append(v___x_3428_, v___x_3429_);
lean_dec_ref(v___x_3429_);
v___x_3431_ = ((lean_object*)(l_main___closed__35));
v___x_3432_ = lean_string_append(v___x_3430_, v___x_3431_);
v___x_3433_ = lean_mk_io_user_error(v___x_3432_);
if (v_isShared_3412_ == 0)
{
lean_ctor_set_tag(v___x_3411_, 1);
lean_ctor_set(v___x_3411_, 0, v___x_3433_);
v___x_3435_ = v___x_3411_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v___x_3433_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
else
{
lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
lean_dec_ref(v___x_2927_);
lean_del_object(v___x_2912_);
lean_dec(v_fst_2909_);
lean_dec(v_name_2896_);
lean_dec(v_head_2889_);
lean_dec(v_head_2888_);
v_a_3438_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3440_ = v___x_3408_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v___x_3408_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3438_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
}
else
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3453_; 
lean_dec_ref(v___x_2927_);
lean_del_object(v___x_2912_);
lean_dec(v_fst_2909_);
lean_dec(v_name_2896_);
lean_dec(v_head_2889_);
lean_dec(v_head_2888_);
v_a_3446_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3448_ = v___x_3405_;
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3405_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3451_; 
if (v_isShared_3449_ == 0)
{
v___x_3451_ = v___x_3448_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3446_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
}
else
{
lean_object* v_a_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3461_; 
lean_dec_ref(v___x_2927_);
lean_del_object(v___x_2912_);
lean_dec(v_fst_2909_);
lean_dec(v_name_2896_);
lean_dec(v_head_2889_);
lean_dec(v_head_2888_);
v_a_3454_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3456_ = v___x_3402_;
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_a_3454_);
lean_dec(v___x_3402_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3459_; 
if (v_isShared_3457_ == 0)
{
v___x_3459_ = v___x_3456_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_a_3454_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
return v___x_3459_;
}
}
}
}
else
{
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3469_; 
lean_dec_ref(v___x_2927_);
lean_del_object(v___x_2912_);
lean_dec(v_fst_2909_);
lean_dec(v_name_2896_);
lean_dec(v_head_2889_);
lean_dec(v_head_2888_);
v_a_3462_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3464_ = v___x_3398_;
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3398_);
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
else
{
lean_object* v_a_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3477_; 
lean_dec_ref(v___x_2927_);
lean_del_object(v___x_2912_);
lean_dec(v_fst_2909_);
lean_dec(v_name_2896_);
lean_dec(v_head_2889_);
lean_dec(v_head_2888_);
v_a_3470_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3472_ = v___x_3393_;
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_a_3470_);
lean_dec(v___x_3393_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3475_; 
if (v_isShared_3473_ == 0)
{
v___x_3475_ = v___x_3472_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3470_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
}
}
else
{
lean_object* v_a_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3487_; 
lean_dec(v_a_2904_);
lean_dec(v_name_2896_);
lean_dec(v_head_2889_);
lean_dec(v_head_2888_);
v_a_3480_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3482_ = v___x_2908_;
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_a_3480_);
lean_dec(v___x_2908_);
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
else
{
lean_object* v_a_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3495_; 
lean_dec(v_a_2904_);
lean_dec(v_name_2896_);
lean_dec(v_head_2889_);
lean_dec(v_head_2888_);
v_a_3488_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3490_ = v___x_2905_;
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_a_3488_);
lean_dec(v___x_2905_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3493_; 
if (v_isShared_3491_ == 0)
{
v___x_3493_ = v___x_3490_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_a_3488_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
}
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3503_; 
lean_dec(v_name_2896_);
lean_dec(v_head_2889_);
lean_dec(v_head_2888_);
v_a_3496_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3498_ = v___x_2903_;
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_2903_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3501_; 
if (v_isShared_3499_ == 0)
{
v___x_3501_ = v___x_3498_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3496_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_del_object(v___x_2892_);
lean_dec(v_tail_2890_);
lean_dec(v_head_2889_);
lean_dec(v_head_2888_);
v_a_3505_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_2894_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_2894_);
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
else
{
lean_dec_ref(v_tail_2885_);
lean_dec(v_tail_2886_);
lean_dec_ref(v_args_2860_);
goto v___jp_2862_;
}
}
else
{
lean_dec_ref(v_args_2860_);
lean_dec(v_tail_2885_);
goto v___jp_2862_;
}
}
else
{
lean_dec(v_args_2860_);
goto v___jp_2862_;
}
v___jp_2862_:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2863_ = ((lean_object*)(l_main___closed__0));
v___x_2864_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_2863_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2872_; 
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2872_ == 0)
{
lean_object* v_unused_2873_; 
v_unused_2873_ = lean_ctor_get(v___x_2864_, 0);
lean_dec(v_unused_2873_);
v___x_2866_ = v___x_2864_;
v_isShared_2867_ = v_isSharedCheck_2872_;
goto v_resetjp_2865_;
}
else
{
lean_dec(v___x_2864_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2872_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2868_; lean_object* v___x_2870_; 
v___x_2868_ = l_main___boxed__const__1;
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 0, v___x_2868_);
v___x_2870_ = v___x_2866_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2868_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
else
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
v_a_2874_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2864_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2864_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
v___jp_2882_:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2883_ = l_main___boxed__const__2;
v___x_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2883_);
return v___x_2884_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_3514_, lean_object* v_a_3515_){
_start:
{
lean_object* v_res_3516_; 
v_res_3516_ = _lean_main(v_args_3514_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object* v_as_3517_, lean_object* v_as_x27_3518_, lean_object* v_b_3519_, lean_object* v_a_3520_){
_start:
{
lean_object* v___x_3522_; 
v___x_3522_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_3518_, v_b_3519_);
return v___x_3522_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object* v_as_3523_, lean_object* v_as_x27_3524_, lean_object* v_b_3525_, lean_object* v_a_3526_, lean_object* v___y_3527_){
_start:
{
lean_object* v_res_3528_; 
v_res_3528_ = l_List_forIn_x27_loop___at___00main_spec__1(v_as_3523_, v_as_x27_3524_, v_b_3525_, v_a_3526_);
lean_dec(v_as_3523_);
return v_res_3528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(lean_object* v___y_3529_, lean_object* v___y_3530_){
_start:
{
lean_object* v___x_3532_; 
v___x_3532_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_3530_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___boxed(lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(v___y_3533_, v___y_3534_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(lean_object* v_00_u03b2_3537_, lean_object* v_m_3538_, lean_object* v_a_3539_, lean_object* v_fallback_3540_){
_start:
{
lean_object* v___x_3541_; 
v___x_3541_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_3538_, v_a_3539_, v_fallback_3540_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___boxed(lean_object* v_00_u03b2_3542_, lean_object* v_m_3543_, lean_object* v_a_3544_, lean_object* v_fallback_3545_){
_start:
{
lean_object* v_res_3546_; 
v_res_3546_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(v_00_u03b2_3542_, v_m_3543_, v_a_3544_, v_fallback_3545_);
lean_dec(v_fallback_3545_);
lean_dec_ref(v_a_3544_);
lean_dec_ref(v_m_3543_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18(lean_object* v_00_u03b2_3547_, lean_object* v_m_3548_, lean_object* v_a_3549_, lean_object* v_b_3550_){
_start:
{
lean_object* v___x_3551_; 
v___x_3551_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_m_3548_, v_a_3549_, v_b_3550_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(lean_object* v_n_3552_, lean_object* v_as_3553_, lean_object* v_lo_3554_, lean_object* v_hi_3555_, lean_object* v_w_3556_, lean_object* v_hlo_3557_, lean_object* v_hhi_3558_){
_start:
{
lean_object* v___x_3559_; 
v___x_3559_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_as_3553_, v_lo_3554_, v_hi_3555_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___boxed(lean_object* v_n_3560_, lean_object* v_as_3561_, lean_object* v_lo_3562_, lean_object* v_hi_3563_, lean_object* v_w_3564_, lean_object* v_hlo_3565_, lean_object* v_hhi_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(v_n_3560_, v_as_3561_, v_lo_3562_, v_hi_3563_, v_w_3564_, v_hlo_3565_, v_hhi_3566_);
lean_dec(v_hi_3563_);
lean_dec(v_n_3560_);
return v_res_3567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(lean_object* v_00_u03b2_3568_, lean_object* v_a_3569_, lean_object* v_fallback_3570_, lean_object* v_x_3571_){
_start:
{
lean_object* v___x_3572_; 
v___x_3572_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_3569_, v_fallback_3570_, v_x_3571_);
return v___x_3572_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3573_, lean_object* v_a_3574_, lean_object* v_fallback_3575_, lean_object* v_x_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(v_00_u03b2_3573_, v_a_3574_, v_fallback_3575_, v_x_3576_);
lean_dec(v_x_3576_);
lean_dec(v_fallback_3575_);
lean_dec_ref(v_a_3574_);
return v_res_3577_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(lean_object* v_00_u03b2_3578_, lean_object* v_a_3579_, lean_object* v_x_3580_){
_start:
{
uint8_t v___x_3581_; 
v___x_3581_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_3579_, v_x_3580_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___boxed(lean_object* v_00_u03b2_3582_, lean_object* v_a_3583_, lean_object* v_x_3584_){
_start:
{
uint8_t v_res_3585_; lean_object* v_r_3586_; 
v_res_3585_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(v_00_u03b2_3582_, v_a_3583_, v_x_3584_);
lean_dec(v_x_3584_);
lean_dec_ref(v_a_3583_);
v_r_3586_ = lean_box(v_res_3585_);
return v_r_3586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24(lean_object* v_00_u03b2_3587_, lean_object* v_data_3588_){
_start:
{
lean_object* v___x_3589_; 
v___x_3589_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_data_3588_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25(lean_object* v_00_u03b2_3590_, lean_object* v_a_3591_, lean_object* v_b_3592_, lean_object* v_x_3593_){
_start:
{
lean_object* v___x_3594_; 
v___x_3594_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_3591_, v_b_3592_, v_x_3593_);
return v___x_3594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__39(lean_object* v_as_3595_, size_t v_sz_3596_, size_t v_i_3597_, lean_object* v_b_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
lean_object* v___x_3602_; 
v___x_3602_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__39___redArg(v_as_3595_, v_sz_3596_, v_i_3597_, v_b_3598_, v___y_3599_);
return v___x_3602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__39___boxed(lean_object* v_as_3603_, lean_object* v_sz_3604_, lean_object* v_i_3605_, lean_object* v_b_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_){
_start:
{
size_t v_sz_boxed_3610_; size_t v_i_boxed_3611_; lean_object* v_res_3612_; 
v_sz_boxed_3610_ = lean_unbox_usize(v_sz_3604_);
lean_dec(v_sz_3604_);
v_i_boxed_3611_ = lean_unbox_usize(v_i_3605_);
lean_dec(v_i_3605_);
v_res_3612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__39(v_as_3603_, v_sz_boxed_3610_, v_i_boxed_3611_, v_b_3606_, v___y_3607_, v___y_3608_);
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec_ref(v_as_3603_);
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35(lean_object* v_00_u03b2_3613_, lean_object* v_i_3614_, lean_object* v_source_3615_, lean_object* v_target_3616_){
_start:
{
lean_object* v___x_3617_; 
v___x_3617_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v_i_3614_, v_source_3615_, v_target_3616_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(uint8_t v___x_3618_, lean_object* v_as_3619_, size_t v_sz_3620_, size_t v_i_3621_, lean_object* v_b_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
lean_object* v___x_3626_; 
v___x_3626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_3618_, v_as_3619_, v_sz_3620_, v_i_3621_, v_b_3622_, v___y_3623_);
return v___x_3626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___boxed(lean_object* v___x_3627_, lean_object* v_as_3628_, lean_object* v_sz_3629_, lean_object* v_i_3630_, lean_object* v_b_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
uint8_t v___x_41167__boxed_3635_; size_t v_sz_boxed_3636_; size_t v_i_boxed_3637_; lean_object* v_res_3638_; 
v___x_41167__boxed_3635_ = lean_unbox(v___x_3627_);
v_sz_boxed_3636_ = lean_unbox_usize(v_sz_3629_);
lean_dec(v_sz_3629_);
v_i_boxed_3637_ = lean_unbox_usize(v_i_3630_);
lean_dec(v_i_3630_);
v_res_3638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(v___x_41167__boxed_3635_, v_as_3628_, v_sz_boxed_3636_, v_i_boxed_3637_, v_b_3631_, v___y_3632_, v___y_3633_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec_ref(v_as_3628_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37_spec__50(lean_object* v_as_3639_, size_t v_sz_3640_, size_t v_i_3641_, lean_object* v_b_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
lean_object* v___x_3646_; 
v___x_3646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37_spec__50___redArg(v_as_3639_, v_sz_3640_, v_i_3641_, v_b_3642_, v___y_3643_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37_spec__50___boxed(lean_object* v_as_3647_, lean_object* v_sz_3648_, lean_object* v_i_3649_, lean_object* v_b_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
size_t v_sz_boxed_3654_; size_t v_i_boxed_3655_; lean_object* v_res_3656_; 
v_sz_boxed_3654_ = lean_unbox_usize(v_sz_3648_);
lean_dec(v_sz_3648_);
v_i_boxed_3655_ = lean_unbox_usize(v_i_3649_);
lean_dec(v_i_3649_);
v_res_3656_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37_spec__50(v_as_3647_, v_sz_boxed_3654_, v_i_boxed_3655_, v_b_3650_, v___y_3651_, v___y_3652_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec_ref(v_as_3647_);
return v_res_3656_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44(lean_object* v_00_u03b2_3657_, lean_object* v_x_3658_, lean_object* v_x_3659_){
_start:
{
lean_object* v___x_3660_; 
v___x_3660_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_x_3658_, v_x_3659_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(uint8_t v___x_3661_, lean_object* v_as_3662_, size_t v_sz_3663_, size_t v_i_3664_, lean_object* v_b_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_){
_start:
{
lean_object* v___x_3669_; 
v___x_3669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_3661_, v_as_3662_, v_sz_3663_, v_i_3664_, v_b_3665_, v___y_3666_);
return v___x_3669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___boxed(lean_object* v___x_3670_, lean_object* v_as_3671_, lean_object* v_sz_3672_, lean_object* v_i_3673_, lean_object* v_b_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
uint8_t v___x_41198__boxed_3678_; size_t v_sz_boxed_3679_; size_t v_i_boxed_3680_; lean_object* v_res_3681_; 
v___x_41198__boxed_3678_ = lean_unbox(v___x_3670_);
v_sz_boxed_3679_ = lean_unbox_usize(v_sz_3672_);
lean_dec(v_sz_3672_);
v_i_boxed_3680_ = lean_unbox_usize(v_i_3673_);
lean_dec(v_i_3673_);
v_res_3681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(v___x_41198__boxed_3678_, v_as_3671_, v_sz_boxed_3679_, v_i_boxed_3680_, v_b_3674_, v___y_3675_, v___y_3676_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec_ref(v_as_3671_);
return v_res_3681_;
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
