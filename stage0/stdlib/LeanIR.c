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
lean_object* v___x_304_; lean_object* v___x_20096__overap_305_; lean_object* v___x_306_; 
v___x_304_ = lean_obj_once(&l_panic___at___00main_spec__5___closed__0, &l_panic___at___00main_spec__5___closed__0_once, _init_l_panic___at___00main_spec__5___closed__0);
v___x_20096__overap_305_ = lean_panic_fn_borrowed(v___x_304_, v_msg_302_);
v___x_306_ = lean_apply_1(v___x_20096__overap_305_, lean_box(0));
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
uint8_t v___x_36192__boxed_479_; uint8_t v___y_36194__boxed_480_; uint8_t v___x_36196__boxed_481_; uint8_t v___x_36197__boxed_482_; lean_object* v_res_483_; 
v___x_36192__boxed_479_ = lean_unbox(v___x_471_);
v___y_36194__boxed_480_ = lean_unbox(v___y_473_);
v___x_36196__boxed_481_ = lean_unbox(v___x_476_);
v___x_36197__boxed_482_ = lean_unbox(v___x_477_);
v_res_483_ = l_main___lam__0(v___x_469_, v___x_470_, v___x_36192__boxed_479_, v___x_472_, v___y_36194__boxed_480_, v_name_474_, v___x_475_, v___x_36196__boxed_481_, v___x_36197__boxed_482_);
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
uint8_t v___x_36282__boxed_592_; uint8_t v___x_36283__boxed_593_; lean_object* v_res_594_; 
v___x_36282__boxed_592_ = lean_unbox(v___x_589_);
v___x_36283__boxed_593_ = lean_unbox(v___x_590_);
v_res_594_ = l_main___lam__1(v___x_574_, v___x_575_, v___x_576_, v_name_577_, v_a_578_, v___x_579_, v_head_580_, v___x_581_, v___x_582_, v___x_583_, v___x_584_, v___x_585_, v___x_586_, v___x_587_, v___x_588_, v___x_36282__boxed_592_, v___x_36283__boxed_593_);
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
v_tail_686_ = lean_ctor_get(v_as_x27_681_, 1);
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
lean_inc(v_head_685_);
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
lean_dec(v_as_x27_714_);
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
lean_object* v_cs_907_; lean_object* v___x_908_; lean_object* v___x_909_; size_t v_sz_910_; size_t v___x_911_; lean_object* v___x_912_; 
v_cs_907_ = lean_ctor_get(v_n_902_, 0);
v___x_908_ = lean_box(0);
v___x_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
lean_ctor_set(v___x_909_, 1, v_b_903_);
v_sz_910_ = lean_array_size(v_cs_907_);
v___x_911_ = ((size_t)0ULL);
v___x_912_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__36(v_init_901_, v_cs_907_, v_sz_910_, v___x_911_, v___x_909_, v___y_904_, v___y_905_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_927_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_927_ == 0)
{
v___x_915_ = v___x_912_;
v_isShared_916_ = v_isSharedCheck_927_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_912_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_927_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v_fst_917_; 
v_fst_917_ = lean_ctor_get(v_a_913_, 0);
if (lean_obj_tag(v_fst_917_) == 0)
{
lean_object* v_snd_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
v_snd_918_ = lean_ctor_get(v_a_913_, 1);
lean_inc(v_snd_918_);
lean_dec(v_a_913_);
v___x_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_919_, 0, v_snd_918_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_919_);
v___x_921_ = v___x_915_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_919_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
else
{
lean_object* v_val_923_; lean_object* v___x_925_; 
lean_inc_ref(v_fst_917_);
lean_dec(v_a_913_);
v_val_923_ = lean_ctor_get(v_fst_917_, 0);
lean_inc(v_val_923_);
lean_dec_ref(v_fst_917_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v_val_923_);
v___x_925_ = v___x_915_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_val_923_);
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
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
v_a_928_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_912_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_912_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
else
{
lean_object* v_vs_936_; lean_object* v___x_937_; lean_object* v___x_938_; size_t v_sz_939_; size_t v___x_940_; lean_object* v___x_941_; 
v_vs_936_ = lean_ctor_get(v_n_902_, 0);
v___x_937_ = lean_box(0);
v___x_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v_b_903_);
v_sz_939_ = lean_array_size(v_vs_936_);
v___x_940_ = ((size_t)0ULL);
v___x_941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_vs_936_, v_sz_939_, v___x_940_, v___x_938_, v___y_904_, v___y_905_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_956_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_956_ == 0)
{
v___x_944_ = v___x_941_;
v_isShared_945_ = v_isSharedCheck_956_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_941_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_956_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v_fst_946_; 
v_fst_946_ = lean_ctor_get(v_a_942_, 0);
if (lean_obj_tag(v_fst_946_) == 0)
{
lean_object* v_snd_947_; lean_object* v___x_948_; lean_object* v___x_950_; 
v_snd_947_ = lean_ctor_get(v_a_942_, 1);
lean_inc(v_snd_947_);
lean_dec(v_a_942_);
v___x_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_948_, 0, v_snd_947_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v___x_948_);
v___x_950_ = v___x_944_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_948_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
else
{
lean_object* v_val_952_; lean_object* v___x_954_; 
lean_inc_ref(v_fst_946_);
lean_dec(v_a_942_);
v_val_952_ = lean_ctor_get(v_fst_946_, 0);
lean_inc(v_val_952_);
lean_dec_ref(v_fst_946_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v_val_952_);
v___x_954_ = v___x_944_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_val_952_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
v_a_957_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_941_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_941_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__36(lean_object* v_init_965_, lean_object* v_as_966_, size_t v_sz_967_, size_t v_i_968_, lean_object* v_b_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
uint8_t v___x_973_; 
v___x_973_ = lean_usize_dec_lt(v_i_968_, v_sz_967_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; 
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v_b_969_);
return v___x_974_;
}
else
{
lean_object* v_snd_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_1009_; 
v_snd_975_ = lean_ctor_get(v_b_969_, 1);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_b_969_);
if (v_isSharedCheck_1009_ == 0)
{
lean_object* v_unused_1010_; 
v_unused_1010_ = lean_ctor_get(v_b_969_, 0);
lean_dec(v_unused_1010_);
v___x_977_ = v_b_969_;
v_isShared_978_ = v_isSharedCheck_1009_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_snd_975_);
lean_dec(v_b_969_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_1009_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v_a_979_; lean_object* v___x_980_; 
v_a_979_ = lean_array_uget_borrowed(v_as_966_, v_i_968_);
lean_inc(v_snd_975_);
v___x_980_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_965_, v_a_979_, v_snd_975_, v___y_970_, v___y_971_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_1000_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_983_ = v___x_980_;
v_isShared_984_ = v_isSharedCheck_1000_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_980_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_1000_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
if (lean_obj_tag(v_a_981_) == 0)
{
lean_object* v___x_985_; lean_object* v___x_987_; 
v___x_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_985_, 0, v_a_981_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_985_);
v___x_987_ = v___x_977_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_snd_975_);
v___x_987_ = v_reuseFailAlloc_991_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
lean_object* v___x_989_; 
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_987_);
v___x_989_ = v___x_983_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_987_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
else
{
lean_object* v_a_992_; lean_object* v___x_993_; lean_object* v___x_995_; 
lean_del_object(v___x_983_);
lean_dec(v_snd_975_);
v_a_992_ = lean_ctor_get(v_a_981_, 0);
lean_inc(v_a_992_);
lean_dec_ref(v_a_981_);
v___x_993_ = lean_box(0);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 1, v_a_992_);
lean_ctor_set(v___x_977_, 0, v___x_993_);
v___x_995_ = v___x_977_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_a_992_);
v___x_995_ = v_reuseFailAlloc_999_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
size_t v___x_996_; size_t v___x_997_; 
v___x_996_ = ((size_t)1ULL);
v___x_997_ = lean_usize_add(v_i_968_, v___x_996_);
v_i_968_ = v___x_997_;
v_b_969_ = v___x_995_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_del_object(v___x_977_);
lean_dec(v_snd_975_);
v_a_1001_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_980_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_980_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__36___boxed(lean_object* v_init_1011_, lean_object* v_as_1012_, lean_object* v_sz_1013_, lean_object* v_i_1014_, lean_object* v_b_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
size_t v_sz_boxed_1019_; size_t v_i_boxed_1020_; lean_object* v_res_1021_; 
v_sz_boxed_1019_ = lean_unbox_usize(v_sz_1013_);
lean_dec(v_sz_1013_);
v_i_boxed_1020_ = lean_unbox_usize(v_i_1014_);
lean_dec(v_i_1014_);
v_res_1021_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__36(v_init_1011_, v_as_1012_, v_sz_boxed_1019_, v_i_boxed_1020_, v_b_1015_, v___y_1016_, v___y_1017_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec_ref(v_as_1012_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26___boxed(lean_object* v_init_1022_, lean_object* v_n_1023_, lean_object* v_b_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1022_, v_n_1023_, v_b_1024_, v___y_1025_, v___y_1026_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec_ref(v_n_1023_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12(lean_object* v_t_1029_, lean_object* v_init_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_root_1034_; lean_object* v_tail_1035_; lean_object* v___x_1036_; 
v_root_1034_ = lean_ctor_get(v_t_1029_, 0);
v_tail_1035_ = lean_ctor_get(v_t_1029_, 1);
v___x_1036_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1030_, v_root_1034_, v_init_1030_, v___y_1031_, v___y_1032_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1073_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1039_ = v___x_1036_;
v_isShared_1040_ = v_isSharedCheck_1073_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1036_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1073_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
if (lean_obj_tag(v_a_1037_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1043_; 
v_a_1041_ = lean_ctor_get(v_a_1037_, 0);
lean_inc(v_a_1041_);
lean_dec_ref(v_a_1037_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 0, v_a_1041_);
v___x_1043_ = v___x_1039_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; size_t v_sz_1048_; size_t v___x_1049_; lean_object* v___x_1050_; 
lean_del_object(v___x_1039_);
v_a_1045_ = lean_ctor_get(v_a_1037_, 0);
lean_inc(v_a_1045_);
lean_dec_ref(v_a_1037_);
v___x_1046_ = lean_box(0);
v___x_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set(v___x_1047_, 1, v_a_1045_);
v_sz_1048_ = lean_array_size(v_tail_1035_);
v___x_1049_ = ((size_t)0ULL);
v___x_1050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(v_tail_1035_, v_sz_1048_, v___x_1049_, v___x_1047_, v___y_1031_, v___y_1032_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1064_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1053_ = v___x_1050_;
v_isShared_1054_ = v_isSharedCheck_1064_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1050_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1064_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v_fst_1055_; 
v_fst_1055_ = lean_ctor_get(v_a_1051_, 0);
if (lean_obj_tag(v_fst_1055_) == 0)
{
lean_object* v_snd_1056_; lean_object* v___x_1058_; 
v_snd_1056_ = lean_ctor_get(v_a_1051_, 1);
lean_inc(v_snd_1056_);
lean_dec(v_a_1051_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v_snd_1056_);
v___x_1058_ = v___x_1053_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_snd_1056_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
else
{
lean_object* v_val_1060_; lean_object* v___x_1062_; 
lean_inc_ref(v_fst_1055_);
lean_dec(v_a_1051_);
v_val_1060_ = lean_ctor_get(v_fst_1055_, 0);
lean_inc(v_val_1060_);
lean_dec_ref(v_fst_1055_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v_val_1060_);
v___x_1062_ = v___x_1053_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_val_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
v_a_1065_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1050_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1050_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
}
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
v_a_1074_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1036_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1036_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12___boxed(lean_object* v_t_1082_, lean_object* v_init_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(v_t_1082_, v_init_1083_, v___y_1084_, v___y_1085_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec_ref(v_t_1082_);
return v_res_1087_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(uint8_t v___x_1095_, uint8_t v_suppressElabErrors_1096_, lean_object* v___x_1097_, lean_object* v_x_1098_){
_start:
{
if (lean_obj_tag(v_x_1098_) == 1)
{
lean_object* v_pre_1099_; 
v_pre_1099_ = lean_ctor_get(v_x_1098_, 0);
switch(lean_obj_tag(v_pre_1099_))
{
case 1:
{
lean_object* v_pre_1100_; 
v_pre_1100_ = lean_ctor_get(v_pre_1099_, 0);
switch(lean_obj_tag(v_pre_1100_))
{
case 0:
{
lean_object* v_str_1101_; lean_object* v_str_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; 
v_str_1101_ = lean_ctor_get(v_x_1098_, 1);
v_str_1102_ = lean_ctor_get(v_pre_1099_, 1);
v___x_1103_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0));
v___x_1104_ = lean_string_dec_eq(v_str_1102_, v___x_1103_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1105_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1));
v___x_1106_ = lean_string_dec_eq(v_str_1102_, v___x_1105_);
if (v___x_1106_ == 0)
{
return v___x_1095_;
}
else
{
lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1107_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2));
v___x_1108_ = lean_string_dec_eq(v_str_1101_, v___x_1107_);
if (v___x_1108_ == 0)
{
return v___x_1095_;
}
else
{
return v_suppressElabErrors_1096_;
}
}
}
else
{
lean_object* v___x_1109_; uint8_t v___x_1110_; 
v___x_1109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3));
v___x_1110_ = lean_string_dec_eq(v_str_1101_, v___x_1109_);
if (v___x_1110_ == 0)
{
return v___x_1095_;
}
else
{
return v_suppressElabErrors_1096_;
}
}
}
case 1:
{
lean_object* v_pre_1111_; 
v_pre_1111_ = lean_ctor_get(v_pre_1100_, 0);
if (lean_obj_tag(v_pre_1111_) == 0)
{
lean_object* v_str_1112_; lean_object* v_str_1113_; lean_object* v_str_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v_str_1112_ = lean_ctor_get(v_x_1098_, 1);
v_str_1113_ = lean_ctor_get(v_pre_1099_, 1);
v_str_1114_ = lean_ctor_get(v_pre_1100_, 1);
v___x_1115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4));
v___x_1116_ = lean_string_dec_eq(v_str_1114_, v___x_1115_);
if (v___x_1116_ == 0)
{
return v___x_1095_;
}
else
{
lean_object* v___x_1117_; uint8_t v___x_1118_; 
v___x_1117_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5));
v___x_1118_ = lean_string_dec_eq(v_str_1113_, v___x_1117_);
if (v___x_1118_ == 0)
{
return v___x_1095_;
}
else
{
lean_object* v___x_1119_; uint8_t v___x_1120_; 
v___x_1119_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6));
v___x_1120_ = lean_string_dec_eq(v_str_1112_, v___x_1119_);
if (v___x_1120_ == 0)
{
return v___x_1095_;
}
else
{
return v_suppressElabErrors_1096_;
}
}
}
}
else
{
return v___x_1095_;
}
}
default: 
{
return v___x_1095_;
}
}
}
case 0:
{
lean_object* v_str_1121_; uint8_t v___x_1122_; 
v_str_1121_ = lean_ctor_get(v_x_1098_, 1);
v___x_1122_ = lean_string_dec_eq(v_str_1121_, v___x_1097_);
if (v___x_1122_ == 0)
{
return v___x_1095_;
}
else
{
return v_suppressElabErrors_1096_;
}
}
default: 
{
return v___x_1095_;
}
}
}
else
{
return v___x_1095_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed(lean_object* v___x_1123_, lean_object* v_suppressElabErrors_1124_, lean_object* v___x_1125_, lean_object* v_x_1126_){
_start:
{
uint8_t v___x_37149__boxed_1127_; uint8_t v_suppressElabErrors_boxed_1128_; uint8_t v_res_1129_; lean_object* v_r_1130_; 
v___x_37149__boxed_1127_ = lean_unbox(v___x_1123_);
v_suppressElabErrors_boxed_1128_ = lean_unbox(v_suppressElabErrors_1124_);
v_res_1129_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(v___x_37149__boxed_1127_, v_suppressElabErrors_boxed_1128_, v___x_1125_, v_x_1126_);
lean_dec(v_x_1126_);
lean_dec_ref(v___x_1125_);
v_r_1130_ = lean_box(v_res_1129_);
return v_r_1130_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0(void){
_start:
{
lean_object* v___x_1131_; double v___x_1132_; 
v___x_1131_ = lean_unsigned_to_nat(0u);
v___x_1132_ = lean_float_of_nat(v___x_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(uint8_t v___x_1134_, lean_object* v_as_1135_, size_t v_sz_1136_, size_t v_i_1137_, lean_object* v_b_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_a_1143_; uint8_t v___x_1147_; 
v___x_1147_ = lean_usize_dec_lt(v_i_1137_, v_sz_1136_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; 
v___x_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1148_, 0, v_b_1138_);
return v___x_1148_;
}
else
{
lean_object* v_a_1149_; lean_object* v_fst_1150_; lean_object* v_snd_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1227_; 
v_a_1149_ = lean_array_uget(v_as_1135_, v_i_1137_);
v_fst_1150_ = lean_ctor_get(v_a_1149_, 0);
v_snd_1151_ = lean_ctor_get(v_a_1149_, 1);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_a_1149_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1153_ = v_a_1149_;
v_isShared_1154_ = v_isSharedCheck_1227_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_snd_1151_);
lean_inc(v_fst_1150_);
lean_dec(v_a_1149_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1227_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v_fst_1155_; lean_object* v_snd_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1226_; 
v_fst_1155_ = lean_ctor_get(v_fst_1150_, 0);
v_snd_1156_ = lean_ctor_get(v_fst_1150_, 1);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_fst_1150_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1158_ = v_fst_1150_;
v_isShared_1159_ = v_isSharedCheck_1226_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_snd_1156_);
lean_inc(v_fst_1155_);
lean_dec(v_fst_1150_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1226_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; double v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v_fileName_1165_; lean_object* v_fileMap_1166_; uint8_t v_suppressElabErrors_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1174_; 
v___x_1160_ = lean_box(0);
v___x_1161_ = lean_box(0);
v___x_1162_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0);
v___x_1163_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1));
v___x_1164_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1164_, 0, v___x_1160_);
lean_ctor_set(v___x_1164_, 1, v___x_1161_);
lean_ctor_set(v___x_1164_, 2, v___x_1163_);
lean_ctor_set_float(v___x_1164_, sizeof(void*)*3, v___x_1162_);
lean_ctor_set_float(v___x_1164_, sizeof(void*)*3 + 8, v___x_1162_);
lean_ctor_set_uint8(v___x_1164_, sizeof(void*)*3 + 16, v___x_1147_);
v_fileName_1165_ = lean_ctor_get(v___y_1139_, 0);
v_fileMap_1166_ = lean_ctor_get(v___y_1139_, 1);
v_suppressElabErrors_1167_ = lean_ctor_get_uint8(v___y_1139_, sizeof(void*)*14 + 1);
v___x_1168_ = lean_box(0);
v___x_1169_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_1170_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_1171_ = l_Lean_MessageData_nil;
v___x_1172_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1164_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
lean_ctor_set(v___x_1172_, 2, v_snd_1151_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set_tag(v___x_1158_, 8);
lean_ctor_set(v___x_1158_, 1, v___x_1172_);
lean_ctor_set(v___x_1158_, 0, v___x_1170_);
v___x_1174_ = v___x_1158_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
uint8_t v___x_1175_; lean_object* v___x_1176_; lean_object* v___y_1178_; lean_object* v___y_1179_; 
v___x_1175_ = 0;
lean_inc_ref(v_fileMap_1166_);
lean_inc_ref(v_fileName_1165_);
v___x_1176_ = l_Lean_Elab_mkMessageCore(v_fileName_1165_, v_fileMap_1166_, v___x_1174_, v___x_1175_, v_fst_1155_, v_snd_1156_);
lean_dec(v_snd_1156_);
lean_dec(v_fst_1155_);
if (v_suppressElabErrors_1167_ == 0)
{
v___y_1178_ = v___y_1139_;
v___y_1179_ = v___y_1140_;
goto v___jp_1177_;
}
else
{
lean_object* v_data_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___f_1223_; uint8_t v___x_1224_; 
v_data_1220_ = lean_ctor_get(v___x_1176_, 4);
lean_inc(v_data_1220_);
v___x_1221_ = lean_box(v___x_1134_);
v___x_1222_ = lean_box(v_suppressElabErrors_1167_);
v___f_1223_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1223_, 0, v___x_1221_);
lean_closure_set(v___f_1223_, 1, v___x_1222_);
lean_closure_set(v___f_1223_, 2, v___x_1169_);
v___x_1224_ = l_Lean_MessageData_hasTag(v___f_1223_, v_data_1220_);
if (v___x_1224_ == 0)
{
lean_dec_ref(v___x_1176_);
lean_del_object(v___x_1153_);
v_a_1143_ = v___x_1168_;
goto v___jp_1142_;
}
else
{
v___y_1178_ = v___y_1139_;
v___y_1179_ = v___y_1140_;
goto v___jp_1177_;
}
}
v___jp_1177_:
{
lean_object* v___x_1180_; lean_object* v_fileName_1181_; lean_object* v_pos_1182_; lean_object* v_endPos_1183_; uint8_t v_keepFullRange_1184_; uint8_t v_severity_1185_; uint8_t v_isSilent_1186_; lean_object* v_caption_1187_; lean_object* v_data_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1219_; 
v___x_1180_ = lean_st_ref_take(v___y_1179_);
v_fileName_1181_ = lean_ctor_get(v___x_1176_, 0);
v_pos_1182_ = lean_ctor_get(v___x_1176_, 1);
v_endPos_1183_ = lean_ctor_get(v___x_1176_, 2);
v_keepFullRange_1184_ = lean_ctor_get_uint8(v___x_1176_, sizeof(void*)*5);
v_severity_1185_ = lean_ctor_get_uint8(v___x_1176_, sizeof(void*)*5 + 1);
v_isSilent_1186_ = lean_ctor_get_uint8(v___x_1176_, sizeof(void*)*5 + 2);
v_caption_1187_ = lean_ctor_get(v___x_1176_, 3);
v_data_1188_ = lean_ctor_get(v___x_1176_, 4);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1190_ = v___x_1176_;
v_isShared_1191_ = v_isSharedCheck_1219_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_data_1188_);
lean_inc(v_caption_1187_);
lean_inc(v_endPos_1183_);
lean_inc(v_pos_1182_);
lean_inc(v_fileName_1181_);
lean_dec(v___x_1176_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1219_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v_currNamespace_1192_; lean_object* v_openDecls_1193_; lean_object* v_env_1194_; lean_object* v_nextMacroScope_1195_; lean_object* v_ngen_1196_; lean_object* v_auxDeclNGen_1197_; lean_object* v_traceState_1198_; lean_object* v_cache_1199_; lean_object* v_messages_1200_; lean_object* v_infoState_1201_; lean_object* v_snapshotTasks_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1218_; 
v_currNamespace_1192_ = lean_ctor_get(v___y_1178_, 6);
v_openDecls_1193_ = lean_ctor_get(v___y_1178_, 7);
v_env_1194_ = lean_ctor_get(v___x_1180_, 0);
v_nextMacroScope_1195_ = lean_ctor_get(v___x_1180_, 1);
v_ngen_1196_ = lean_ctor_get(v___x_1180_, 2);
v_auxDeclNGen_1197_ = lean_ctor_get(v___x_1180_, 3);
v_traceState_1198_ = lean_ctor_get(v___x_1180_, 4);
v_cache_1199_ = lean_ctor_get(v___x_1180_, 5);
v_messages_1200_ = lean_ctor_get(v___x_1180_, 6);
v_infoState_1201_ = lean_ctor_get(v___x_1180_, 7);
v_snapshotTasks_1202_ = lean_ctor_get(v___x_1180_, 8);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1204_ = v___x_1180_;
v_isShared_1205_ = v_isSharedCheck_1218_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_snapshotTasks_1202_);
lean_inc(v_infoState_1201_);
lean_inc(v_messages_1200_);
lean_inc(v_cache_1199_);
lean_inc(v_traceState_1198_);
lean_inc(v_auxDeclNGen_1197_);
lean_inc(v_ngen_1196_);
lean_inc(v_nextMacroScope_1195_);
lean_inc(v_env_1194_);
lean_dec(v___x_1180_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1218_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
lean_inc(v_openDecls_1193_);
lean_inc(v_currNamespace_1192_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 1, v_openDecls_1193_);
lean_ctor_set(v___x_1153_, 0, v_currNamespace_1192_);
v___x_1207_ = v___x_1153_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_currNamespace_1192_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_openDecls_1193_);
v___x_1207_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v___x_1208_; lean_object* v___x_1210_; 
v___x_1208_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
lean_ctor_set(v___x_1208_, 1, v_data_1188_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 4, v___x_1208_);
v___x_1210_ = v___x_1190_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_fileName_1181_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_pos_1182_);
lean_ctor_set(v_reuseFailAlloc_1216_, 2, v_endPos_1183_);
lean_ctor_set(v_reuseFailAlloc_1216_, 3, v_caption_1187_);
lean_ctor_set(v_reuseFailAlloc_1216_, 4, v___x_1208_);
lean_ctor_set_uint8(v_reuseFailAlloc_1216_, sizeof(void*)*5, v_keepFullRange_1184_);
lean_ctor_set_uint8(v_reuseFailAlloc_1216_, sizeof(void*)*5 + 1, v_severity_1185_);
lean_ctor_set_uint8(v_reuseFailAlloc_1216_, sizeof(void*)*5 + 2, v_isSilent_1186_);
v___x_1210_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
lean_object* v___x_1211_; lean_object* v___x_1213_; 
v___x_1211_ = l_Lean_MessageLog_add(v___x_1210_, v_messages_1200_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 6, v___x_1211_);
v___x_1213_ = v___x_1204_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_env_1194_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v_nextMacroScope_1195_);
lean_ctor_set(v_reuseFailAlloc_1215_, 2, v_ngen_1196_);
lean_ctor_set(v_reuseFailAlloc_1215_, 3, v_auxDeclNGen_1197_);
lean_ctor_set(v_reuseFailAlloc_1215_, 4, v_traceState_1198_);
lean_ctor_set(v_reuseFailAlloc_1215_, 5, v_cache_1199_);
lean_ctor_set(v_reuseFailAlloc_1215_, 6, v___x_1211_);
lean_ctor_set(v_reuseFailAlloc_1215_, 7, v_infoState_1201_);
lean_ctor_set(v_reuseFailAlloc_1215_, 8, v_snapshotTasks_1202_);
v___x_1213_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
lean_object* v___x_1214_; 
v___x_1214_ = lean_st_ref_set(v___y_1179_, v___x_1213_);
v_a_1143_ = v___x_1168_;
goto v___jp_1142_;
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
v___jp_1142_:
{
size_t v___x_1144_; size_t v___x_1145_; 
v___x_1144_ = ((size_t)1ULL);
v___x_1145_ = lean_usize_add(v_i_1137_, v___x_1144_);
v_i_1137_ = v___x_1145_;
v_b_1138_ = v_a_1143_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___boxed(lean_object* v___x_1228_, lean_object* v_as_1229_, lean_object* v_sz_1230_, lean_object* v_i_1231_, lean_object* v_b_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
uint8_t v___x_37222__boxed_1236_; size_t v_sz_boxed_1237_; size_t v_i_boxed_1238_; lean_object* v_res_1239_; 
v___x_37222__boxed_1236_ = lean_unbox(v___x_1228_);
v_sz_boxed_1237_ = lean_unbox_usize(v_sz_1230_);
lean_dec(v_sz_1230_);
v_i_boxed_1238_ = lean_unbox_usize(v_i_1231_);
lean_dec(v_i_1231_);
v_res_1239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_37222__boxed_1236_, v_as_1229_, v_sz_boxed_1237_, v_i_boxed_1238_, v_b_1232_, v___y_1233_, v___y_1234_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec_ref(v_as_1229_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(lean_object* v_opts_1240_, lean_object* v_opt_1241_){
_start:
{
lean_object* v_name_1242_; lean_object* v_map_1243_; lean_object* v___x_1244_; 
v_name_1242_ = lean_ctor_get(v_opt_1241_, 0);
v_map_1243_ = lean_ctor_get(v_opts_1240_, 0);
v___x_1244_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1243_, v_name_1242_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v___x_1245_; 
v___x_1245_ = lean_box(0);
return v___x_1245_;
}
else
{
lean_object* v_val_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1255_; 
v_val_1246_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1248_ = v___x_1244_;
v_isShared_1249_ = v_isSharedCheck_1255_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_val_1246_);
lean_dec(v___x_1244_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1255_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
if (lean_obj_tag(v_val_1246_) == 0)
{
lean_object* v_v_1250_; lean_object* v___x_1252_; 
v_v_1250_ = lean_ctor_get(v_val_1246_, 0);
lean_inc_ref(v_v_1250_);
lean_dec_ref(v_val_1246_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 0, v_v_1250_);
v___x_1252_ = v___x_1248_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_v_1250_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
else
{
lean_object* v___x_1254_; 
lean_del_object(v___x_1248_);
lean_dec(v_val_1246_);
v___x_1254_ = lean_box(0);
return v___x_1254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15___boxed(lean_object* v_opts_1256_, lean_object* v_opt_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(v_opts_1256_, v_opt_1257_);
lean_dec_ref(v_opt_1257_);
lean_dec_ref(v_opts_1256_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(lean_object* v_a_1259_, lean_object* v_fallback_1260_, lean_object* v_x_1261_){
_start:
{
if (lean_obj_tag(v_x_1261_) == 0)
{
lean_inc(v_fallback_1260_);
return v_fallback_1260_;
}
else
{
lean_object* v_key_1262_; lean_object* v_value_1263_; lean_object* v_tail_1264_; uint8_t v___y_1266_; lean_object* v_fst_1268_; lean_object* v_snd_1269_; lean_object* v_fst_1270_; lean_object* v_snd_1271_; uint8_t v___x_1272_; 
v_key_1262_ = lean_ctor_get(v_x_1261_, 0);
v_value_1263_ = lean_ctor_get(v_x_1261_, 1);
v_tail_1264_ = lean_ctor_get(v_x_1261_, 2);
v_fst_1268_ = lean_ctor_get(v_key_1262_, 0);
v_snd_1269_ = lean_ctor_get(v_key_1262_, 1);
v_fst_1270_ = lean_ctor_get(v_a_1259_, 0);
v_snd_1271_ = lean_ctor_get(v_a_1259_, 1);
v___x_1272_ = lean_nat_dec_eq(v_fst_1268_, v_fst_1270_);
if (v___x_1272_ == 0)
{
v___y_1266_ = v___x_1272_;
goto v___jp_1265_;
}
else
{
uint8_t v___x_1273_; 
v___x_1273_ = lean_nat_dec_eq(v_snd_1269_, v_snd_1271_);
v___y_1266_ = v___x_1273_;
goto v___jp_1265_;
}
v___jp_1265_:
{
if (v___y_1266_ == 0)
{
v_x_1261_ = v_tail_1264_;
goto _start;
}
else
{
lean_inc(v_value_1263_);
return v_value_1263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg___boxed(lean_object* v_a_1274_, lean_object* v_fallback_1275_, lean_object* v_x_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_1274_, v_fallback_1275_, v_x_1276_);
lean_dec(v_x_1276_);
lean_dec(v_fallback_1275_);
lean_dec_ref(v_a_1274_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(lean_object* v_m_1278_, lean_object* v_a_1279_, lean_object* v_fallback_1280_){
_start:
{
lean_object* v_buckets_1281_; lean_object* v_fst_1282_; lean_object* v_snd_1283_; lean_object* v___x_1284_; uint64_t v___x_1285_; uint64_t v___x_1286_; uint64_t v___x_1287_; uint64_t v___x_1288_; uint64_t v___x_1289_; uint64_t v_fold_1290_; uint64_t v___x_1291_; uint64_t v___x_1292_; uint64_t v___x_1293_; size_t v___x_1294_; size_t v___x_1295_; size_t v___x_1296_; size_t v___x_1297_; size_t v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v_buckets_1281_ = lean_ctor_get(v_m_1278_, 1);
v_fst_1282_ = lean_ctor_get(v_a_1279_, 0);
v_snd_1283_ = lean_ctor_get(v_a_1279_, 1);
v___x_1284_ = lean_array_get_size(v_buckets_1281_);
v___x_1285_ = l_String_instHashableRaw_hash(v_fst_1282_);
v___x_1286_ = l_String_instHashableRaw_hash(v_snd_1283_);
v___x_1287_ = lean_uint64_mix_hash(v___x_1285_, v___x_1286_);
v___x_1288_ = 32ULL;
v___x_1289_ = lean_uint64_shift_right(v___x_1287_, v___x_1288_);
v_fold_1290_ = lean_uint64_xor(v___x_1287_, v___x_1289_);
v___x_1291_ = 16ULL;
v___x_1292_ = lean_uint64_shift_right(v_fold_1290_, v___x_1291_);
v___x_1293_ = lean_uint64_xor(v_fold_1290_, v___x_1292_);
v___x_1294_ = lean_uint64_to_usize(v___x_1293_);
v___x_1295_ = lean_usize_of_nat(v___x_1284_);
v___x_1296_ = ((size_t)1ULL);
v___x_1297_ = lean_usize_sub(v___x_1295_, v___x_1296_);
v___x_1298_ = lean_usize_land(v___x_1294_, v___x_1297_);
v___x_1299_ = lean_array_uget_borrowed(v_buckets_1281_, v___x_1298_);
v___x_1300_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_1279_, v_fallback_1280_, v___x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg___boxed(lean_object* v_m_1301_, lean_object* v_a_1302_, lean_object* v_fallback_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_1301_, v_a_1302_, v_fallback_1303_);
lean_dec(v_fallback_1303_);
lean_dec_ref(v_a_1302_);
lean_dec_ref(v_m_1301_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(lean_object* v_x_1305_, lean_object* v_x_1306_){
_start:
{
if (lean_obj_tag(v_x_1306_) == 0)
{
return v_x_1305_;
}
else
{
lean_object* v_key_1307_; lean_object* v_value_1308_; lean_object* v_tail_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1336_; 
v_key_1307_ = lean_ctor_get(v_x_1306_, 0);
v_value_1308_ = lean_ctor_get(v_x_1306_, 1);
v_tail_1309_ = lean_ctor_get(v_x_1306_, 2);
v_isSharedCheck_1336_ = !lean_is_exclusive(v_x_1306_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1311_ = v_x_1306_;
v_isShared_1312_ = v_isSharedCheck_1336_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_tail_1309_);
lean_inc(v_value_1308_);
lean_inc(v_key_1307_);
lean_dec(v_x_1306_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1336_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v_fst_1313_; lean_object* v_snd_1314_; lean_object* v___x_1315_; uint64_t v___x_1316_; uint64_t v___x_1317_; uint64_t v___x_1318_; uint64_t v___x_1319_; uint64_t v___x_1320_; uint64_t v_fold_1321_; uint64_t v___x_1322_; uint64_t v___x_1323_; uint64_t v___x_1324_; size_t v___x_1325_; size_t v___x_1326_; size_t v___x_1327_; size_t v___x_1328_; size_t v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1332_; 
v_fst_1313_ = lean_ctor_get(v_key_1307_, 0);
v_snd_1314_ = lean_ctor_get(v_key_1307_, 1);
v___x_1315_ = lean_array_get_size(v_x_1305_);
v___x_1316_ = l_String_instHashableRaw_hash(v_fst_1313_);
v___x_1317_ = l_String_instHashableRaw_hash(v_snd_1314_);
v___x_1318_ = lean_uint64_mix_hash(v___x_1316_, v___x_1317_);
v___x_1319_ = 32ULL;
v___x_1320_ = lean_uint64_shift_right(v___x_1318_, v___x_1319_);
v_fold_1321_ = lean_uint64_xor(v___x_1318_, v___x_1320_);
v___x_1322_ = 16ULL;
v___x_1323_ = lean_uint64_shift_right(v_fold_1321_, v___x_1322_);
v___x_1324_ = lean_uint64_xor(v_fold_1321_, v___x_1323_);
v___x_1325_ = lean_uint64_to_usize(v___x_1324_);
v___x_1326_ = lean_usize_of_nat(v___x_1315_);
v___x_1327_ = ((size_t)1ULL);
v___x_1328_ = lean_usize_sub(v___x_1326_, v___x_1327_);
v___x_1329_ = lean_usize_land(v___x_1325_, v___x_1328_);
v___x_1330_ = lean_array_uget_borrowed(v_x_1305_, v___x_1329_);
lean_inc(v___x_1330_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 2, v___x_1330_);
v___x_1332_ = v___x_1311_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_key_1307_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v_value_1308_);
lean_ctor_set(v_reuseFailAlloc_1335_, 2, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
lean_object* v___x_1333_; 
v___x_1333_ = lean_array_uset(v_x_1305_, v___x_1329_, v___x_1332_);
v_x_1305_ = v___x_1333_;
v_x_1306_ = v_tail_1309_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(lean_object* v_i_1337_, lean_object* v_source_1338_, lean_object* v_target_1339_){
_start:
{
lean_object* v___x_1340_; uint8_t v___x_1341_; 
v___x_1340_ = lean_array_get_size(v_source_1338_);
v___x_1341_ = lean_nat_dec_lt(v_i_1337_, v___x_1340_);
if (v___x_1341_ == 0)
{
lean_dec_ref(v_source_1338_);
lean_dec(v_i_1337_);
return v_target_1339_;
}
else
{
lean_object* v_es_1342_; lean_object* v___x_1343_; lean_object* v_source_1344_; lean_object* v_target_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v_es_1342_ = lean_array_fget(v_source_1338_, v_i_1337_);
v___x_1343_ = lean_box(0);
v_source_1344_ = lean_array_fset(v_source_1338_, v_i_1337_, v___x_1343_);
v_target_1345_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_target_1339_, v_es_1342_);
v___x_1346_ = lean_unsigned_to_nat(1u);
v___x_1347_ = lean_nat_add(v_i_1337_, v___x_1346_);
lean_dec(v_i_1337_);
v_i_1337_ = v___x_1347_;
v_source_1338_ = v_source_1344_;
v_target_1339_ = v_target_1345_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(lean_object* v_data_1349_){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v_nbuckets_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1350_ = lean_array_get_size(v_data_1349_);
v___x_1351_ = lean_unsigned_to_nat(2u);
v_nbuckets_1352_ = lean_nat_mul(v___x_1350_, v___x_1351_);
v___x_1353_ = lean_unsigned_to_nat(0u);
v___x_1354_ = lean_box(0);
v___x_1355_ = lean_mk_array(v_nbuckets_1352_, v___x_1354_);
v___x_1356_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v___x_1353_, v_data_1349_, v___x_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(lean_object* v_a_1357_, lean_object* v_b_1358_, lean_object* v_x_1359_){
_start:
{
if (lean_obj_tag(v_x_1359_) == 0)
{
lean_dec(v_b_1358_);
lean_dec_ref(v_a_1357_);
return v_x_1359_;
}
else
{
lean_object* v_key_1360_; lean_object* v_value_1361_; lean_object* v_tail_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1381_; 
v_key_1360_ = lean_ctor_get(v_x_1359_, 0);
v_value_1361_ = lean_ctor_get(v_x_1359_, 1);
v_tail_1362_ = lean_ctor_get(v_x_1359_, 2);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_x_1359_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1364_ = v_x_1359_;
v_isShared_1365_ = v_isSharedCheck_1381_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_tail_1362_);
lean_inc(v_value_1361_);
lean_inc(v_key_1360_);
lean_dec(v_x_1359_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1381_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
uint8_t v___y_1367_; lean_object* v_fst_1375_; lean_object* v_snd_1376_; lean_object* v_fst_1377_; lean_object* v_snd_1378_; uint8_t v___x_1379_; 
v_fst_1375_ = lean_ctor_get(v_key_1360_, 0);
v_snd_1376_ = lean_ctor_get(v_key_1360_, 1);
v_fst_1377_ = lean_ctor_get(v_a_1357_, 0);
v_snd_1378_ = lean_ctor_get(v_a_1357_, 1);
v___x_1379_ = lean_nat_dec_eq(v_fst_1375_, v_fst_1377_);
if (v___x_1379_ == 0)
{
v___y_1367_ = v___x_1379_;
goto v___jp_1366_;
}
else
{
uint8_t v___x_1380_; 
v___x_1380_ = lean_nat_dec_eq(v_snd_1376_, v_snd_1378_);
v___y_1367_ = v___x_1380_;
goto v___jp_1366_;
}
v___jp_1366_:
{
if (v___y_1367_ == 0)
{
lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1368_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_1357_, v_b_1358_, v_tail_1362_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 2, v___x_1368_);
v___x_1370_ = v___x_1364_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_key_1360_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_value_1361_);
lean_ctor_set(v_reuseFailAlloc_1371_, 2, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
else
{
lean_object* v___x_1373_; 
lean_dec(v_value_1361_);
lean_dec(v_key_1360_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 1, v_b_1358_);
lean_ctor_set(v___x_1364_, 0, v_a_1357_);
v___x_1373_ = v___x_1364_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1357_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_b_1358_);
lean_ctor_set(v_reuseFailAlloc_1374_, 2, v_tail_1362_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(lean_object* v_a_1382_, lean_object* v_x_1383_){
_start:
{
if (lean_obj_tag(v_x_1383_) == 0)
{
uint8_t v___x_1384_; 
v___x_1384_ = 0;
return v___x_1384_;
}
else
{
lean_object* v_key_1385_; lean_object* v_tail_1386_; uint8_t v___y_1388_; lean_object* v_fst_1390_; lean_object* v_snd_1391_; lean_object* v_fst_1392_; lean_object* v_snd_1393_; uint8_t v___x_1394_; 
v_key_1385_ = lean_ctor_get(v_x_1383_, 0);
v_tail_1386_ = lean_ctor_get(v_x_1383_, 2);
v_fst_1390_ = lean_ctor_get(v_key_1385_, 0);
v_snd_1391_ = lean_ctor_get(v_key_1385_, 1);
v_fst_1392_ = lean_ctor_get(v_a_1382_, 0);
v_snd_1393_ = lean_ctor_get(v_a_1382_, 1);
v___x_1394_ = lean_nat_dec_eq(v_fst_1390_, v_fst_1392_);
if (v___x_1394_ == 0)
{
v___y_1388_ = v___x_1394_;
goto v___jp_1387_;
}
else
{
uint8_t v___x_1395_; 
v___x_1395_ = lean_nat_dec_eq(v_snd_1391_, v_snd_1393_);
v___y_1388_ = v___x_1395_;
goto v___jp_1387_;
}
v___jp_1387_:
{
if (v___y_1388_ == 0)
{
v_x_1383_ = v_tail_1386_;
goto _start;
}
else
{
return v___y_1388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg___boxed(lean_object* v_a_1396_, lean_object* v_x_1397_){
_start:
{
uint8_t v_res_1398_; lean_object* v_r_1399_; 
v_res_1398_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_1396_, v_x_1397_);
lean_dec(v_x_1397_);
lean_dec_ref(v_a_1396_);
v_r_1399_ = lean_box(v_res_1398_);
return v_r_1399_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(lean_object* v_m_1400_, lean_object* v_a_1401_, lean_object* v_b_1402_){
_start:
{
lean_object* v_size_1403_; lean_object* v_buckets_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1451_; 
v_size_1403_ = lean_ctor_get(v_m_1400_, 0);
v_buckets_1404_ = lean_ctor_get(v_m_1400_, 1);
v_isSharedCheck_1451_ = !lean_is_exclusive(v_m_1400_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1406_ = v_m_1400_;
v_isShared_1407_ = v_isSharedCheck_1451_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_buckets_1404_);
lean_inc(v_size_1403_);
lean_dec(v_m_1400_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1451_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v_fst_1408_; lean_object* v_snd_1409_; lean_object* v___x_1410_; uint64_t v___x_1411_; uint64_t v___x_1412_; uint64_t v___x_1413_; uint64_t v___x_1414_; uint64_t v___x_1415_; uint64_t v_fold_1416_; uint64_t v___x_1417_; uint64_t v___x_1418_; uint64_t v___x_1419_; size_t v___x_1420_; size_t v___x_1421_; size_t v___x_1422_; size_t v___x_1423_; size_t v___x_1424_; lean_object* v_bkt_1425_; uint8_t v___x_1426_; 
v_fst_1408_ = lean_ctor_get(v_a_1401_, 0);
v_snd_1409_ = lean_ctor_get(v_a_1401_, 1);
v___x_1410_ = lean_array_get_size(v_buckets_1404_);
v___x_1411_ = l_String_instHashableRaw_hash(v_fst_1408_);
v___x_1412_ = l_String_instHashableRaw_hash(v_snd_1409_);
v___x_1413_ = lean_uint64_mix_hash(v___x_1411_, v___x_1412_);
v___x_1414_ = 32ULL;
v___x_1415_ = lean_uint64_shift_right(v___x_1413_, v___x_1414_);
v_fold_1416_ = lean_uint64_xor(v___x_1413_, v___x_1415_);
v___x_1417_ = 16ULL;
v___x_1418_ = lean_uint64_shift_right(v_fold_1416_, v___x_1417_);
v___x_1419_ = lean_uint64_xor(v_fold_1416_, v___x_1418_);
v___x_1420_ = lean_uint64_to_usize(v___x_1419_);
v___x_1421_ = lean_usize_of_nat(v___x_1410_);
v___x_1422_ = ((size_t)1ULL);
v___x_1423_ = lean_usize_sub(v___x_1421_, v___x_1422_);
v___x_1424_ = lean_usize_land(v___x_1420_, v___x_1423_);
v_bkt_1425_ = lean_array_uget_borrowed(v_buckets_1404_, v___x_1424_);
v___x_1426_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_1401_, v_bkt_1425_);
if (v___x_1426_ == 0)
{
lean_object* v___x_1427_; lean_object* v_size_x27_1428_; lean_object* v___x_1429_; lean_object* v_buckets_x27_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1427_ = lean_unsigned_to_nat(1u);
v_size_x27_1428_ = lean_nat_add(v_size_1403_, v___x_1427_);
lean_dec(v_size_1403_);
lean_inc(v_bkt_1425_);
v___x_1429_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1429_, 0, v_a_1401_);
lean_ctor_set(v___x_1429_, 1, v_b_1402_);
lean_ctor_set(v___x_1429_, 2, v_bkt_1425_);
v_buckets_x27_1430_ = lean_array_uset(v_buckets_1404_, v___x_1424_, v___x_1429_);
v___x_1431_ = lean_unsigned_to_nat(4u);
v___x_1432_ = lean_nat_mul(v_size_x27_1428_, v___x_1431_);
v___x_1433_ = lean_unsigned_to_nat(3u);
v___x_1434_ = lean_nat_div(v___x_1432_, v___x_1433_);
lean_dec(v___x_1432_);
v___x_1435_ = lean_array_get_size(v_buckets_x27_1430_);
v___x_1436_ = lean_nat_dec_le(v___x_1434_, v___x_1435_);
lean_dec(v___x_1434_);
if (v___x_1436_ == 0)
{
lean_object* v_val_1437_; lean_object* v___x_1439_; 
v_val_1437_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_buckets_x27_1430_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 1, v_val_1437_);
lean_ctor_set(v___x_1406_, 0, v_size_x27_1428_);
v___x_1439_ = v___x_1406_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_size_x27_1428_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_val_1437_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
else
{
lean_object* v___x_1442_; 
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 1, v_buckets_x27_1430_);
lean_ctor_set(v___x_1406_, 0, v_size_x27_1428_);
v___x_1442_ = v___x_1406_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_size_x27_1428_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_buckets_x27_1430_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
else
{
lean_object* v___x_1444_; lean_object* v_buckets_x27_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1449_; 
lean_inc(v_bkt_1425_);
v___x_1444_ = lean_box(0);
v_buckets_x27_1445_ = lean_array_uset(v_buckets_1404_, v___x_1424_, v___x_1444_);
v___x_1446_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_1401_, v_b_1402_, v_bkt_1425_);
v___x_1447_ = lean_array_uset(v_buckets_x27_1445_, v___x_1424_, v___x_1446_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 1, v___x_1447_);
v___x_1449_ = v___x_1406_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_size_1403_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v___x_1447_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(uint8_t v___x_1454_, lean_object* v_as_1455_, size_t v_sz_1456_, size_t v_i_1457_, lean_object* v_b_1458_, lean_object* v___y_1459_){
_start:
{
uint8_t v___x_1461_; 
v___x_1461_ = lean_usize_dec_lt(v_i_1457_, v_sz_1456_);
if (v___x_1461_ == 0)
{
lean_object* v___x_1462_; 
v___x_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1462_, 0, v_b_1458_);
return v___x_1462_;
}
else
{
lean_object* v_snd_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1500_; 
v_snd_1463_ = lean_ctor_get(v_b_1458_, 1);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_b_1458_);
if (v_isSharedCheck_1500_ == 0)
{
lean_object* v_unused_1501_; 
v_unused_1501_ = lean_ctor_get(v_b_1458_, 0);
lean_dec(v_unused_1501_);
v___x_1465_ = v_b_1458_;
v_isShared_1466_ = v_isSharedCheck_1500_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_snd_1463_);
lean_dec(v_b_1458_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1500_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v_ref_1467_; lean_object* v_a_1468_; lean_object* v_ref_1469_; lean_object* v_msg_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1499_; 
v_ref_1467_ = lean_ctor_get(v___y_1459_, 5);
v_a_1468_ = lean_array_uget(v_as_1455_, v_i_1457_);
v_ref_1469_ = lean_ctor_get(v_a_1468_, 0);
v_msg_1470_ = lean_ctor_get(v_a_1468_, 1);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_a_1468_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1472_ = v_a_1468_;
v_isShared_1473_ = v_isSharedCheck_1499_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_msg_1470_);
lean_inc(v_ref_1469_);
lean_dec(v_a_1468_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1499_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1474_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v_ref_1491_; lean_object* v___y_1493_; lean_object* v___x_1496_; 
v___x_1474_ = lean_box(0);
v_ref_1491_ = l_Lean_replaceRef(v_ref_1469_, v_ref_1467_);
lean_dec(v_ref_1469_);
v___x_1496_ = l_Lean_Syntax_getPos_x3f(v_ref_1491_, v___x_1454_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_unsigned_to_nat(0u);
v___y_1493_ = v___x_1497_;
goto v___jp_1492_;
}
else
{
lean_object* v_val_1498_; 
v_val_1498_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_val_1498_);
lean_dec_ref(v___x_1496_);
v___y_1493_ = v_val_1498_;
goto v___jp_1492_;
}
v___jp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 1, v___y_1477_);
lean_ctor_set(v___x_1465_, 0, v___y_1476_);
v___x_1479_ = v___x_1465_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___y_1476_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v___y_1477_);
v___x_1479_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v_pos2traces_1483_; lean_object* v___x_1485_; 
v___x_1480_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1481_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1463_, v___x_1479_, v___x_1480_);
v___x_1482_ = lean_array_push(v___x_1481_, v_msg_1470_);
v_pos2traces_1483_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1463_, v___x_1479_, v___x_1482_);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 1, v_pos2traces_1483_);
lean_ctor_set(v___x_1472_, 0, v___x_1474_);
v___x_1485_ = v___x_1472_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_pos2traces_1483_);
v___x_1485_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
size_t v___x_1486_; size_t v___x_1487_; 
v___x_1486_ = ((size_t)1ULL);
v___x_1487_ = lean_usize_add(v_i_1457_, v___x_1486_);
v_i_1457_ = v___x_1487_;
v_b_1458_ = v___x_1485_;
goto _start;
}
}
}
v___jp_1492_:
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1491_, v___x_1454_);
lean_dec(v_ref_1491_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_inc(v___y_1493_);
v___y_1476_ = v___y_1493_;
v___y_1477_ = v___y_1493_;
goto v___jp_1475_;
}
else
{
lean_object* v_val_1495_; 
v_val_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_val_1495_);
lean_dec_ref(v___x_1494_);
v___y_1476_ = v___y_1493_;
v___y_1477_ = v_val_1495_;
goto v___jp_1475_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___boxed(lean_object* v___x_1502_, lean_object* v_as_1503_, lean_object* v_sz_1504_, lean_object* v_i_1505_, lean_object* v_b_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
uint8_t v___x_37702__boxed_1509_; size_t v_sz_boxed_1510_; size_t v_i_boxed_1511_; lean_object* v_res_1512_; 
v___x_37702__boxed_1509_ = lean_unbox(v___x_1502_);
v_sz_boxed_1510_ = lean_unbox_usize(v_sz_1504_);
lean_dec(v_sz_1504_);
v_i_boxed_1511_ = lean_unbox_usize(v_i_1505_);
lean_dec(v_i_1505_);
v_res_1512_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_37702__boxed_1509_, v_as_1503_, v_sz_boxed_1510_, v_i_boxed_1511_, v_b_1506_, v___y_1507_);
lean_dec_ref(v___y_1507_);
lean_dec_ref(v_as_1503_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(uint8_t v___x_1513_, lean_object* v_as_1514_, size_t v_sz_1515_, size_t v_i_1516_, lean_object* v_b_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
uint8_t v___x_1521_; 
v___x_1521_ = lean_usize_dec_lt(v_i_1516_, v_sz_1515_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1522_, 0, v_b_1517_);
return v___x_1522_;
}
else
{
lean_object* v_snd_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1560_; 
v_snd_1523_ = lean_ctor_get(v_b_1517_, 1);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_b_1517_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; 
v_unused_1561_ = lean_ctor_get(v_b_1517_, 0);
lean_dec(v_unused_1561_);
v___x_1525_ = v_b_1517_;
v_isShared_1526_ = v_isSharedCheck_1560_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_snd_1523_);
lean_dec(v_b_1517_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1560_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v_ref_1527_; lean_object* v_a_1528_; lean_object* v_ref_1529_; lean_object* v_msg_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1559_; 
v_ref_1527_ = lean_ctor_get(v___y_1518_, 5);
v_a_1528_ = lean_array_uget(v_as_1514_, v_i_1516_);
v_ref_1529_ = lean_ctor_get(v_a_1528_, 0);
v_msg_1530_ = lean_ctor_get(v_a_1528_, 1);
v_isSharedCheck_1559_ = !lean_is_exclusive(v_a_1528_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1532_ = v_a_1528_;
v_isShared_1533_ = v_isSharedCheck_1559_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_msg_1530_);
lean_inc(v_ref_1529_);
lean_dec(v_a_1528_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1559_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v_ref_1551_; lean_object* v___y_1553_; lean_object* v___x_1556_; 
v___x_1534_ = lean_box(0);
v_ref_1551_ = l_Lean_replaceRef(v_ref_1529_, v_ref_1527_);
lean_dec(v_ref_1529_);
v___x_1556_ = l_Lean_Syntax_getPos_x3f(v_ref_1551_, v___x_1513_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v___x_1557_; 
v___x_1557_ = lean_unsigned_to_nat(0u);
v___y_1553_ = v___x_1557_;
goto v___jp_1552_;
}
else
{
lean_object* v_val_1558_; 
v_val_1558_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_val_1558_);
lean_dec_ref(v___x_1556_);
v___y_1553_ = v_val_1558_;
goto v___jp_1552_;
}
v___jp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 1, v___y_1537_);
lean_ctor_set(v___x_1525_, 0, v___y_1536_);
v___x_1539_ = v___x_1525_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___y_1536_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v___y_1537_);
v___x_1539_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v_pos2traces_1543_; lean_object* v___x_1545_; 
v___x_1540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1541_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1523_, v___x_1539_, v___x_1540_);
v___x_1542_ = lean_array_push(v___x_1541_, v_msg_1530_);
v_pos2traces_1543_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1523_, v___x_1539_, v___x_1542_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 1, v_pos2traces_1543_);
lean_ctor_set(v___x_1532_, 0, v___x_1534_);
v___x_1545_ = v___x_1532_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1534_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_pos2traces_1543_);
v___x_1545_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
size_t v___x_1546_; size_t v___x_1547_; lean_object* v___x_1548_; 
v___x_1546_ = ((size_t)1ULL);
v___x_1547_ = lean_usize_add(v_i_1516_, v___x_1546_);
v___x_1548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_1513_, v_as_1514_, v_sz_1515_, v___x_1547_, v___x_1545_, v___y_1518_);
return v___x_1548_;
}
}
}
v___jp_1552_:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1551_, v___x_1513_);
lean_dec(v_ref_1551_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_inc(v___y_1553_);
v___y_1536_ = v___y_1553_;
v___y_1537_ = v___y_1553_;
goto v___jp_1535_;
}
else
{
lean_object* v_val_1555_; 
v_val_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_val_1555_);
lean_dec_ref(v___x_1554_);
v___y_1536_ = v___y_1553_;
v___y_1537_ = v_val_1555_;
goto v___jp_1535_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40___boxed(lean_object* v___x_1562_, lean_object* v_as_1563_, lean_object* v_sz_1564_, lean_object* v_i_1565_, lean_object* v_b_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
uint8_t v___x_37783__boxed_1570_; size_t v_sz_boxed_1571_; size_t v_i_boxed_1572_; lean_object* v_res_1573_; 
v___x_37783__boxed_1570_ = lean_unbox(v___x_1562_);
v_sz_boxed_1571_ = lean_unbox_usize(v_sz_1564_);
lean_dec(v_sz_1564_);
v_i_boxed_1572_ = lean_unbox_usize(v_i_1565_);
lean_dec(v_i_1565_);
v_res_1573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_37783__boxed_1570_, v_as_1563_, v_sz_boxed_1571_, v_i_boxed_1572_, v_b_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec_ref(v_as_1563_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(lean_object* v_init_1574_, uint8_t v___x_1575_, lean_object* v_n_1576_, lean_object* v_b_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
if (lean_obj_tag(v_n_1576_) == 0)
{
lean_object* v_cs_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; size_t v_sz_1584_; size_t v___x_1585_; lean_object* v___x_1586_; 
v_cs_1581_ = lean_ctor_get(v_n_1576_, 0);
v___x_1582_ = lean_box(0);
v___x_1583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
lean_ctor_set(v___x_1583_, 1, v_b_1577_);
v_sz_1584_ = lean_array_size(v_cs_1581_);
v___x_1585_ = ((size_t)0ULL);
v___x_1586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_1574_, v___x_1575_, v_cs_1581_, v_sz_1584_, v___x_1585_, v___x_1583_, v___y_1578_, v___y_1579_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1601_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1589_ = v___x_1586_;
v_isShared_1590_ = v_isSharedCheck_1601_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1586_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1601_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v_fst_1591_; 
v_fst_1591_ = lean_ctor_get(v_a_1587_, 0);
if (lean_obj_tag(v_fst_1591_) == 0)
{
lean_object* v_snd_1592_; lean_object* v___x_1593_; lean_object* v___x_1595_; 
v_snd_1592_ = lean_ctor_get(v_a_1587_, 1);
lean_inc(v_snd_1592_);
lean_dec(v_a_1587_);
v___x_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1593_, 0, v_snd_1592_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 0, v___x_1593_);
v___x_1595_ = v___x_1589_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1593_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
else
{
lean_object* v_val_1597_; lean_object* v___x_1599_; 
lean_inc_ref(v_fst_1591_);
lean_dec(v_a_1587_);
v_val_1597_ = lean_ctor_get(v_fst_1591_, 0);
lean_inc(v_val_1597_);
lean_dec_ref(v_fst_1591_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 0, v_val_1597_);
v___x_1599_ = v___x_1589_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_val_1597_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
v_a_1602_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1586_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1586_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
else
{
lean_object* v_vs_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; size_t v_sz_1613_; size_t v___x_1614_; lean_object* v___x_1615_; 
v_vs_1610_ = lean_ctor_get(v_n_1576_, 0);
v___x_1611_ = lean_box(0);
v___x_1612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1611_);
lean_ctor_set(v___x_1612_, 1, v_b_1577_);
v_sz_1613_ = lean_array_size(v_vs_1610_);
v___x_1614_ = ((size_t)0ULL);
v___x_1615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_1575_, v_vs_1610_, v_sz_1613_, v___x_1614_, v___x_1612_, v___y_1578_, v___y_1579_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1630_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1618_ = v___x_1615_;
v_isShared_1619_ = v_isSharedCheck_1630_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1615_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1630_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v_fst_1620_; 
v_fst_1620_ = lean_ctor_get(v_a_1616_, 0);
if (lean_obj_tag(v_fst_1620_) == 0)
{
lean_object* v_snd_1621_; lean_object* v___x_1622_; lean_object* v___x_1624_; 
v_snd_1621_ = lean_ctor_get(v_a_1616_, 1);
lean_inc(v_snd_1621_);
lean_dec(v_a_1616_);
v___x_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1622_, 0, v_snd_1621_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v___x_1622_);
v___x_1624_ = v___x_1618_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1622_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
else
{
lean_object* v_val_1626_; lean_object* v___x_1628_; 
lean_inc_ref(v_fst_1620_);
lean_dec(v_a_1616_);
v_val_1626_ = lean_ctor_get(v_fst_1620_, 0);
lean_inc(v_val_1626_);
lean_dec_ref(v_fst_1620_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v_val_1626_);
v___x_1628_ = v___x_1618_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_val_1626_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
v_a_1631_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1615_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1615_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(lean_object* v_init_1639_, uint8_t v___x_1640_, lean_object* v_as_1641_, size_t v_sz_1642_, size_t v_i_1643_, lean_object* v_b_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
uint8_t v___x_1648_; 
v___x_1648_ = lean_usize_dec_lt(v_i_1643_, v_sz_1642_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; 
v___x_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1649_, 0, v_b_1644_);
return v___x_1649_;
}
else
{
lean_object* v_snd_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1684_; 
v_snd_1650_ = lean_ctor_get(v_b_1644_, 1);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_b_1644_);
if (v_isSharedCheck_1684_ == 0)
{
lean_object* v_unused_1685_; 
v_unused_1685_ = lean_ctor_get(v_b_1644_, 0);
lean_dec(v_unused_1685_);
v___x_1652_ = v_b_1644_;
v_isShared_1653_ = v_isSharedCheck_1684_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_snd_1650_);
lean_dec(v_b_1644_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1684_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v_a_1654_; lean_object* v___x_1655_; 
v_a_1654_ = lean_array_uget_borrowed(v_as_1641_, v_i_1643_);
lean_inc(v_snd_1650_);
v___x_1655_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1639_, v___x_1640_, v_a_1654_, v_snd_1650_, v___y_1645_, v___y_1646_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1675_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1658_ = v___x_1655_;
v_isShared_1659_ = v_isSharedCheck_1675_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1655_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1675_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
if (lean_obj_tag(v_a_1656_) == 0)
{
lean_object* v___x_1660_; lean_object* v___x_1662_; 
v___x_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1660_, 0, v_a_1656_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 0, v___x_1660_);
v___x_1662_ = v___x_1652_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1660_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_snd_1650_);
v___x_1662_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1664_; 
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v___x_1662_);
v___x_1664_ = v___x_1658_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1662_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
else
{
lean_object* v_a_1667_; lean_object* v___x_1668_; lean_object* v___x_1670_; 
lean_del_object(v___x_1658_);
lean_dec(v_snd_1650_);
v_a_1667_ = lean_ctor_get(v_a_1656_, 0);
lean_inc(v_a_1667_);
lean_dec_ref(v_a_1656_);
v___x_1668_ = lean_box(0);
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 1, v_a_1667_);
lean_ctor_set(v___x_1652_, 0, v___x_1668_);
v___x_1670_ = v___x_1652_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1668_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v_a_1667_);
v___x_1670_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
size_t v___x_1671_; size_t v___x_1672_; 
v___x_1671_ = ((size_t)1ULL);
v___x_1672_ = lean_usize_add(v_i_1643_, v___x_1671_);
v_i_1643_ = v___x_1672_;
v_b_1644_ = v___x_1670_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_del_object(v___x_1652_);
lean_dec(v_snd_1650_);
v_a_1676_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1655_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1655_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39___boxed(lean_object* v_init_1686_, lean_object* v___x_1687_, lean_object* v_as_1688_, lean_object* v_sz_1689_, lean_object* v_i_1690_, lean_object* v_b_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
uint8_t v___x_37864__boxed_1695_; size_t v_sz_boxed_1696_; size_t v_i_boxed_1697_; lean_object* v_res_1698_; 
v___x_37864__boxed_1695_ = lean_unbox(v___x_1687_);
v_sz_boxed_1696_ = lean_unbox_usize(v_sz_1689_);
lean_dec(v_sz_1689_);
v_i_boxed_1697_ = lean_unbox_usize(v_i_1690_);
lean_dec(v_i_1690_);
v_res_1698_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_1686_, v___x_37864__boxed_1695_, v_as_1688_, v_sz_boxed_1696_, v_i_boxed_1697_, v_b_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec_ref(v_as_1688_);
lean_dec_ref(v_init_1686_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27___boxed(lean_object* v_init_1699_, lean_object* v___x_1700_, lean_object* v_n_1701_, lean_object* v_b_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
uint8_t v___x_37884__boxed_1706_; lean_object* v_res_1707_; 
v___x_37884__boxed_1706_ = lean_unbox(v___x_1700_);
v_res_1707_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1699_, v___x_37884__boxed_1706_, v_n_1701_, v_b_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec_ref(v_n_1701_);
lean_dec_ref(v_init_1699_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(uint8_t v___x_1708_, lean_object* v_as_1709_, size_t v_sz_1710_, size_t v_i_1711_, lean_object* v_b_1712_, lean_object* v___y_1713_){
_start:
{
uint8_t v___x_1715_; 
v___x_1715_ = lean_usize_dec_lt(v_i_1711_, v_sz_1710_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; 
v___x_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1716_, 0, v_b_1712_);
return v___x_1716_;
}
else
{
lean_object* v_snd_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1754_; 
v_snd_1717_ = lean_ctor_get(v_b_1712_, 1);
v_isSharedCheck_1754_ = !lean_is_exclusive(v_b_1712_);
if (v_isSharedCheck_1754_ == 0)
{
lean_object* v_unused_1755_; 
v_unused_1755_ = lean_ctor_get(v_b_1712_, 0);
lean_dec(v_unused_1755_);
v___x_1719_ = v_b_1712_;
v_isShared_1720_ = v_isSharedCheck_1754_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_snd_1717_);
lean_dec(v_b_1712_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1754_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v_ref_1721_; lean_object* v_a_1722_; lean_object* v_ref_1723_; lean_object* v_msg_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1753_; 
v_ref_1721_ = lean_ctor_get(v___y_1713_, 5);
v_a_1722_ = lean_array_uget(v_as_1709_, v_i_1711_);
v_ref_1723_ = lean_ctor_get(v_a_1722_, 0);
v_msg_1724_ = lean_ctor_get(v_a_1722_, 1);
v_isSharedCheck_1753_ = !lean_is_exclusive(v_a_1722_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1726_ = v_a_1722_;
v_isShared_1727_ = v_isSharedCheck_1753_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_msg_1724_);
lean_inc(v_ref_1723_);
lean_dec(v_a_1722_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1753_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1728_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v_ref_1745_; lean_object* v___y_1747_; lean_object* v___x_1750_; 
v___x_1728_ = lean_box(0);
v_ref_1745_ = l_Lean_replaceRef(v_ref_1723_, v_ref_1721_);
lean_dec(v_ref_1723_);
v___x_1750_ = l_Lean_Syntax_getPos_x3f(v_ref_1745_, v___x_1708_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v___x_1751_; 
v___x_1751_ = lean_unsigned_to_nat(0u);
v___y_1747_ = v___x_1751_;
goto v___jp_1746_;
}
else
{
lean_object* v_val_1752_; 
v_val_1752_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_val_1752_);
lean_dec_ref(v___x_1750_);
v___y_1747_ = v_val_1752_;
goto v___jp_1746_;
}
v___jp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 1, v___y_1731_);
lean_ctor_set(v___x_1719_, 0, v___y_1730_);
v___x_1733_ = v___x_1719_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___y_1730_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v___y_1731_);
v___x_1733_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v_pos2traces_1737_; lean_object* v___x_1739_; 
v___x_1734_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1735_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1717_, v___x_1733_, v___x_1734_);
v___x_1736_ = lean_array_push(v___x_1735_, v_msg_1724_);
v_pos2traces_1737_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1717_, v___x_1733_, v___x_1736_);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 1, v_pos2traces_1737_);
lean_ctor_set(v___x_1726_, 0, v___x_1728_);
v___x_1739_ = v___x_1726_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1728_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v_pos2traces_1737_);
v___x_1739_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
size_t v___x_1740_; size_t v___x_1741_; 
v___x_1740_ = ((size_t)1ULL);
v___x_1741_ = lean_usize_add(v_i_1711_, v___x_1740_);
v_i_1711_ = v___x_1741_;
v_b_1712_ = v___x_1739_;
goto _start;
}
}
}
v___jp_1746_:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1745_, v___x_1708_);
lean_dec(v_ref_1745_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_inc(v___y_1747_);
v___y_1730_ = v___y_1747_;
v___y_1731_ = v___y_1747_;
goto v___jp_1729_;
}
else
{
lean_object* v_val_1749_; 
v_val_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_val_1749_);
lean_dec_ref(v___x_1748_);
v___y_1730_ = v___y_1747_;
v___y_1731_ = v_val_1749_;
goto v___jp_1729_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg___boxed(lean_object* v___x_1756_, lean_object* v_as_1757_, lean_object* v_sz_1758_, lean_object* v_i_1759_, lean_object* v_b_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
uint8_t v___x_38067__boxed_1763_; size_t v_sz_boxed_1764_; size_t v_i_boxed_1765_; lean_object* v_res_1766_; 
v___x_38067__boxed_1763_ = lean_unbox(v___x_1756_);
v_sz_boxed_1764_ = lean_unbox_usize(v_sz_1758_);
lean_dec(v_sz_1758_);
v_i_boxed_1765_ = lean_unbox_usize(v_i_1759_);
lean_dec(v_i_1759_);
v_res_1766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_38067__boxed_1763_, v_as_1757_, v_sz_boxed_1764_, v_i_boxed_1765_, v_b_1760_, v___y_1761_);
lean_dec_ref(v___y_1761_);
lean_dec_ref(v_as_1757_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(uint8_t v___x_1767_, lean_object* v_as_1768_, size_t v_sz_1769_, size_t v_i_1770_, lean_object* v_b_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
uint8_t v___x_1775_; 
v___x_1775_ = lean_usize_dec_lt(v_i_1770_, v_sz_1769_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; 
v___x_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1776_, 0, v_b_1771_);
return v___x_1776_;
}
else
{
lean_object* v_snd_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1814_; 
v_snd_1777_ = lean_ctor_get(v_b_1771_, 1);
v_isSharedCheck_1814_ = !lean_is_exclusive(v_b_1771_);
if (v_isSharedCheck_1814_ == 0)
{
lean_object* v_unused_1815_; 
v_unused_1815_ = lean_ctor_get(v_b_1771_, 0);
lean_dec(v_unused_1815_);
v___x_1779_ = v_b_1771_;
v_isShared_1780_ = v_isSharedCheck_1814_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_snd_1777_);
lean_dec(v_b_1771_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1814_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v_ref_1781_; lean_object* v_a_1782_; lean_object* v_ref_1783_; lean_object* v_msg_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1813_; 
v_ref_1781_ = lean_ctor_get(v___y_1772_, 5);
v_a_1782_ = lean_array_uget(v_as_1768_, v_i_1770_);
v_ref_1783_ = lean_ctor_get(v_a_1782_, 0);
v_msg_1784_ = lean_ctor_get(v_a_1782_, 1);
v_isSharedCheck_1813_ = !lean_is_exclusive(v_a_1782_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1786_ = v_a_1782_;
v_isShared_1787_ = v_isSharedCheck_1813_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_msg_1784_);
lean_inc(v_ref_1783_);
lean_dec(v_a_1782_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1813_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1788_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v_ref_1805_; lean_object* v___y_1807_; lean_object* v___x_1810_; 
v___x_1788_ = lean_box(0);
v_ref_1805_ = l_Lean_replaceRef(v_ref_1783_, v_ref_1781_);
lean_dec(v_ref_1783_);
v___x_1810_ = l_Lean_Syntax_getPos_x3f(v_ref_1805_, v___x_1767_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v___x_1811_; 
v___x_1811_ = lean_unsigned_to_nat(0u);
v___y_1807_ = v___x_1811_;
goto v___jp_1806_;
}
else
{
lean_object* v_val_1812_; 
v_val_1812_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_val_1812_);
lean_dec_ref(v___x_1810_);
v___y_1807_ = v_val_1812_;
goto v___jp_1806_;
}
v___jp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 1, v___y_1791_);
lean_ctor_set(v___x_1779_, 0, v___y_1790_);
v___x_1793_ = v___x_1779_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___y_1790_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v___y_1791_);
v___x_1793_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v_pos2traces_1797_; lean_object* v___x_1799_; 
v___x_1794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1795_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1777_, v___x_1793_, v___x_1794_);
v___x_1796_ = lean_array_push(v___x_1795_, v_msg_1784_);
v_pos2traces_1797_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1777_, v___x_1793_, v___x_1796_);
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 1, v_pos2traces_1797_);
lean_ctor_set(v___x_1786_, 0, v___x_1788_);
v___x_1799_ = v___x_1786_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1788_);
lean_ctor_set(v_reuseFailAlloc_1803_, 1, v_pos2traces_1797_);
v___x_1799_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
size_t v___x_1800_; size_t v___x_1801_; lean_object* v___x_1802_; 
v___x_1800_ = ((size_t)1ULL);
v___x_1801_ = lean_usize_add(v_i_1770_, v___x_1800_);
v___x_1802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_1767_, v_as_1768_, v_sz_1769_, v___x_1801_, v___x_1799_, v___y_1772_);
return v___x_1802_;
}
}
}
v___jp_1806_:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1805_, v___x_1767_);
lean_dec(v_ref_1805_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_inc(v___y_1807_);
v___y_1790_ = v___y_1807_;
v___y_1791_ = v___y_1807_;
goto v___jp_1789_;
}
else
{
lean_object* v_val_1809_; 
v_val_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_val_1809_);
lean_dec_ref(v___x_1808_);
v___y_1790_ = v___y_1807_;
v___y_1791_ = v_val_1809_;
goto v___jp_1789_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28___boxed(lean_object* v___x_1816_, lean_object* v_as_1817_, lean_object* v_sz_1818_, lean_object* v_i_1819_, lean_object* v_b_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
uint8_t v___x_38147__boxed_1824_; size_t v_sz_boxed_1825_; size_t v_i_boxed_1826_; lean_object* v_res_1827_; 
v___x_38147__boxed_1824_ = lean_unbox(v___x_1816_);
v_sz_boxed_1825_ = lean_unbox_usize(v_sz_1818_);
lean_dec(v_sz_1818_);
v_i_boxed_1826_ = lean_unbox_usize(v_i_1819_);
lean_dec(v_i_1819_);
v_res_1827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_38147__boxed_1824_, v_as_1817_, v_sz_boxed_1825_, v_i_boxed_1826_, v_b_1820_, v___y_1821_, v___y_1822_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec_ref(v_as_1817_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(uint8_t v___x_1828_, lean_object* v_t_1829_, lean_object* v_init_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_root_1834_; lean_object* v_tail_1835_; lean_object* v___x_1836_; 
v_root_1834_ = lean_ctor_get(v_t_1829_, 0);
v_tail_1835_ = lean_ctor_get(v_t_1829_, 1);
lean_inc_ref(v_init_1830_);
v___x_1836_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1830_, v___x_1828_, v_root_1834_, v_init_1830_, v___y_1831_, v___y_1832_);
lean_dec_ref(v_init_1830_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1873_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1873_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1873_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
if (lean_obj_tag(v_a_1837_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1843_; 
v_a_1841_ = lean_ctor_get(v_a_1837_, 0);
lean_inc(v_a_1841_);
lean_dec_ref(v_a_1837_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v_a_1841_);
v___x_1843_ = v___x_1839_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; size_t v_sz_1848_; size_t v___x_1849_; lean_object* v___x_1850_; 
lean_del_object(v___x_1839_);
v_a_1845_ = lean_ctor_get(v_a_1837_, 0);
lean_inc(v_a_1845_);
lean_dec_ref(v_a_1837_);
v___x_1846_ = lean_box(0);
v___x_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
lean_ctor_set(v___x_1847_, 1, v_a_1845_);
v_sz_1848_ = lean_array_size(v_tail_1835_);
v___x_1849_ = ((size_t)0ULL);
v___x_1850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_1828_, v_tail_1835_, v_sz_1848_, v___x_1849_, v___x_1847_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1864_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1853_ = v___x_1850_;
v_isShared_1854_ = v_isSharedCheck_1864_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1850_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1864_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v_fst_1855_; 
v_fst_1855_ = lean_ctor_get(v_a_1851_, 0);
if (lean_obj_tag(v_fst_1855_) == 0)
{
lean_object* v_snd_1856_; lean_object* v___x_1858_; 
v_snd_1856_ = lean_ctor_get(v_a_1851_, 1);
lean_inc(v_snd_1856_);
lean_dec(v_a_1851_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v_snd_1856_);
v___x_1858_ = v___x_1853_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_snd_1856_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
else
{
lean_object* v_val_1860_; lean_object* v___x_1862_; 
lean_inc_ref(v_fst_1855_);
lean_dec(v_a_1851_);
v_val_1860_ = lean_ctor_get(v_fst_1855_, 0);
lean_inc(v_val_1860_);
lean_dec_ref(v_fst_1855_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v_val_1860_);
v___x_1862_ = v___x_1853_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_val_1860_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
else
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
v_a_1865_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1850_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1850_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1865_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
v_a_1874_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1836_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1836_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19___boxed(lean_object* v___x_1882_, lean_object* v_t_1883_, lean_object* v_init_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
uint8_t v___x_38228__boxed_1888_; lean_object* v_res_1889_; 
v___x_38228__boxed_1888_ = lean_unbox(v___x_1882_);
v_res_1889_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_38228__boxed_1888_, v_t_1883_, v_init_1884_, v___y_1885_, v___y_1886_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec_ref(v_t_1883_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(lean_object* v_x_1890_, lean_object* v_x_1891_){
_start:
{
if (lean_obj_tag(v_x_1891_) == 0)
{
return v_x_1890_;
}
else
{
lean_object* v_key_1892_; lean_object* v_value_1893_; lean_object* v_tail_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v_key_1892_ = lean_ctor_get(v_x_1891_, 0);
v_value_1893_ = lean_ctor_get(v_x_1891_, 1);
v_tail_1894_ = lean_ctor_get(v_x_1891_, 2);
lean_inc(v_value_1893_);
lean_inc(v_key_1892_);
v___x_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1895_, 0, v_key_1892_);
lean_ctor_set(v___x_1895_, 1, v_value_1893_);
v___x_1896_ = lean_array_push(v_x_1890_, v___x_1895_);
v_x_1890_ = v___x_1896_;
v_x_1891_ = v_tail_1894_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22___boxed(lean_object* v_x_1898_, lean_object* v_x_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_x_1898_, v_x_1899_);
lean_dec(v_x_1899_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(lean_object* v_as_1901_, size_t v_i_1902_, size_t v_stop_1903_, lean_object* v_b_1904_){
_start:
{
uint8_t v___x_1905_; 
v___x_1905_ = lean_usize_dec_eq(v_i_1902_, v_stop_1903_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; lean_object* v___x_1907_; size_t v___x_1908_; size_t v___x_1909_; 
v___x_1906_ = lean_array_uget_borrowed(v_as_1901_, v_i_1902_);
v___x_1907_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_b_1904_, v___x_1906_);
v___x_1908_ = ((size_t)1ULL);
v___x_1909_ = lean_usize_add(v_i_1902_, v___x_1908_);
v_i_1902_ = v___x_1909_;
v_b_1904_ = v___x_1907_;
goto _start;
}
else
{
return v_b_1904_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23___boxed(lean_object* v_as_1911_, lean_object* v_i_1912_, lean_object* v_stop_1913_, lean_object* v_b_1914_){
_start:
{
size_t v_i_boxed_1915_; size_t v_stop_boxed_1916_; lean_object* v_res_1917_; 
v_i_boxed_1915_ = lean_unbox_usize(v_i_1912_);
lean_dec(v_i_1912_);
v_stop_boxed_1916_ = lean_unbox_usize(v_stop_1913_);
lean_dec(v_stop_1913_);
v_res_1917_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_as_1911_, v_i_boxed_1915_, v_stop_boxed_1916_, v_b_1914_);
lean_dec_ref(v_as_1911_);
return v_res_1917_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0(void){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1918_ = lean_unsigned_to_nat(32u);
v___x_1919_ = lean_mk_empty_array_with_capacity(v___x_1918_);
v___x_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
return v___x_1920_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1(void){
_start:
{
size_t v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1921_ = ((size_t)5ULL);
v___x_1922_ = lean_unsigned_to_nat(0u);
v___x_1923_ = lean_unsigned_to_nat(32u);
v___x_1924_ = lean_mk_empty_array_with_capacity(v___x_1923_);
v___x_1925_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0);
v___x_1926_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
lean_ctor_set(v___x_1926_, 1, v___x_1924_);
lean_ctor_set(v___x_1926_, 2, v___x_1922_);
lean_ctor_set(v___x_1926_, 3, v___x_1922_);
lean_ctor_set_usize(v___x_1926_, 4, v___x_1921_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(lean_object* v___y_1927_){
_start:
{
lean_object* v___x_1929_; lean_object* v_traceState_1930_; lean_object* v_traces_1931_; lean_object* v___x_1932_; lean_object* v_traceState_1933_; lean_object* v_env_1934_; lean_object* v_nextMacroScope_1935_; lean_object* v_ngen_1936_; lean_object* v_auxDeclNGen_1937_; lean_object* v_cache_1938_; lean_object* v_messages_1939_; lean_object* v_infoState_1940_; lean_object* v_snapshotTasks_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1960_; 
v___x_1929_ = lean_st_ref_get(v___y_1927_);
v_traceState_1930_ = lean_ctor_get(v___x_1929_, 4);
lean_inc_ref(v_traceState_1930_);
lean_dec(v___x_1929_);
v_traces_1931_ = lean_ctor_get(v_traceState_1930_, 0);
lean_inc_ref(v_traces_1931_);
lean_dec_ref(v_traceState_1930_);
v___x_1932_ = lean_st_ref_take(v___y_1927_);
v_traceState_1933_ = lean_ctor_get(v___x_1932_, 4);
v_env_1934_ = lean_ctor_get(v___x_1932_, 0);
v_nextMacroScope_1935_ = lean_ctor_get(v___x_1932_, 1);
v_ngen_1936_ = lean_ctor_get(v___x_1932_, 2);
v_auxDeclNGen_1937_ = lean_ctor_get(v___x_1932_, 3);
v_cache_1938_ = lean_ctor_get(v___x_1932_, 5);
v_messages_1939_ = lean_ctor_get(v___x_1932_, 6);
v_infoState_1940_ = lean_ctor_get(v___x_1932_, 7);
v_snapshotTasks_1941_ = lean_ctor_get(v___x_1932_, 8);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1943_ = v___x_1932_;
v_isShared_1944_ = v_isSharedCheck_1960_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_snapshotTasks_1941_);
lean_inc(v_infoState_1940_);
lean_inc(v_messages_1939_);
lean_inc(v_cache_1938_);
lean_inc(v_traceState_1933_);
lean_inc(v_auxDeclNGen_1937_);
lean_inc(v_ngen_1936_);
lean_inc(v_nextMacroScope_1935_);
lean_inc(v_env_1934_);
lean_dec(v___x_1932_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1960_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
uint64_t v_tid_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1958_; 
v_tid_1945_ = lean_ctor_get_uint64(v_traceState_1933_, sizeof(void*)*1);
v_isSharedCheck_1958_ = !lean_is_exclusive(v_traceState_1933_);
if (v_isSharedCheck_1958_ == 0)
{
lean_object* v_unused_1959_; 
v_unused_1959_ = lean_ctor_get(v_traceState_1933_, 0);
lean_dec(v_unused_1959_);
v___x_1947_ = v_traceState_1933_;
v_isShared_1948_ = v_isSharedCheck_1958_;
goto v_resetjp_1946_;
}
else
{
lean_dec(v_traceState_1933_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1958_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1949_; lean_object* v___x_1951_; 
v___x_1949_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 0, v___x_1949_);
v___x_1951_ = v___x_1947_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1949_);
lean_ctor_set_uint64(v_reuseFailAlloc_1957_, sizeof(void*)*1, v_tid_1945_);
v___x_1951_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
lean_object* v___x_1953_; 
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 4, v___x_1951_);
v___x_1953_ = v___x_1943_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_env_1934_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v_nextMacroScope_1935_);
lean_ctor_set(v_reuseFailAlloc_1956_, 2, v_ngen_1936_);
lean_ctor_set(v_reuseFailAlloc_1956_, 3, v_auxDeclNGen_1937_);
lean_ctor_set(v_reuseFailAlloc_1956_, 4, v___x_1951_);
lean_ctor_set(v_reuseFailAlloc_1956_, 5, v_cache_1938_);
lean_ctor_set(v_reuseFailAlloc_1956_, 6, v_messages_1939_);
lean_ctor_set(v_reuseFailAlloc_1956_, 7, v_infoState_1940_);
lean_ctor_set(v_reuseFailAlloc_1956_, 8, v_snapshotTasks_1941_);
v___x_1953_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1954_ = lean_st_ref_set(v___y_1927_, v___x_1953_);
v___x_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1955_, 0, v_traces_1931_);
return v___x_1955_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___boxed(lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_1961_);
lean_dec(v___y_1961_);
return v_res_1963_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(lean_object* v_x_1964_, lean_object* v_x_1965_){
_start:
{
lean_object* v_fst_1966_; lean_object* v_fst_1967_; lean_object* v_fst_1968_; lean_object* v_fst_1969_; uint8_t v___x_1970_; 
v_fst_1966_ = lean_ctor_get(v_x_1964_, 0);
v_fst_1967_ = lean_ctor_get(v_x_1965_, 0);
v_fst_1968_ = lean_ctor_get(v_fst_1966_, 0);
v_fst_1969_ = lean_ctor_get(v_fst_1967_, 0);
v___x_1970_ = lean_nat_dec_lt(v_fst_1968_, v_fst_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0___boxed(lean_object* v_x_1971_, lean_object* v_x_1972_){
_start:
{
uint8_t v_res_1973_; lean_object* v_r_1974_; 
v_res_1973_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v_x_1971_, v_x_1972_);
lean_dec_ref(v_x_1972_);
lean_dec_ref(v_x_1971_);
v_r_1974_ = lean_box(v_res_1973_);
return v_r_1974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(lean_object* v_as_1976_, lean_object* v_lo_1977_, lean_object* v_hi_1978_){
_start:
{
uint8_t v___x_1979_; 
v___x_1979_ = lean_nat_dec_lt(v_lo_1977_, v_hi_1978_);
if (v___x_1979_ == 0)
{
lean_dec(v_lo_1977_);
return v_as_1976_;
}
else
{
lean_object* v___f_1980_; lean_object* v___x_1981_; lean_object* v_fst_1982_; lean_object* v_snd_1983_; uint8_t v___x_1984_; 
v___f_1980_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___closed__0));
lean_inc(v_lo_1977_);
v___x_1981_ = l_Array_qpartition___redArg(v_as_1976_, v___f_1980_, v_lo_1977_, v_hi_1978_);
v_fst_1982_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_fst_1982_);
v_snd_1983_ = lean_ctor_get(v___x_1981_, 1);
lean_inc(v_snd_1983_);
lean_dec_ref(v___x_1981_);
v___x_1984_ = lean_nat_dec_le(v_hi_1978_, v_fst_1982_);
if (v___x_1984_ == 0)
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1985_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_snd_1983_, v_lo_1977_, v_fst_1982_);
v___x_1986_ = lean_unsigned_to_nat(1u);
v___x_1987_ = lean_nat_add(v_fst_1982_, v___x_1986_);
lean_dec(v_fst_1982_);
v_as_1976_ = v___x_1985_;
v_lo_1977_ = v___x_1987_;
goto _start;
}
else
{
lean_dec(v_fst_1982_);
lean_dec(v_lo_1977_);
return v_snd_1983_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___boxed(lean_object* v_as_1989_, lean_object* v_lo_1990_, lean_object* v_hi_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_as_1989_, v_lo_1990_, v_hi_1991_);
lean_dec(v_hi_1991_);
return v_res_1992_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0(void){
_start:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1993_ = lean_box(0);
v___x_1994_ = lean_unsigned_to_nat(16u);
v___x_1995_ = lean_mk_array(v___x_1994_, v___x_1993_);
return v___x_1995_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1(void){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v_pos2traces_1998_; 
v___x_1996_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0);
v___x_1997_ = lean_unsigned_to_nat(0u);
v_pos2traces_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_1998_, 0, v___x_1997_);
lean_ctor_set(v_pos2traces_1998_, 1, v___x_1996_);
return v_pos2traces_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10(lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v_options_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v_options_2002_ = lean_ctor_get(v___y_1999_, 2);
v___x_2003_ = l_Lean_trace_profiler_output;
v___x_2004_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(v_options_2002_, v___x_2003_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v___x_2005_; lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2072_; 
v___x_2005_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_2000_);
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2008_ = v___x_2005_;
v_isShared_2009_ = v_isSharedCheck_2072_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_2005_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2072_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
uint8_t v___x_2010_; 
v___x_2010_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_2006_);
if (v___x_2010_ == 0)
{
lean_object* v___x_2011_; lean_object* v_pos2traces_2012_; lean_object* v___x_2013_; 
lean_del_object(v___x_2008_);
v___x_2011_ = lean_unsigned_to_nat(0u);
v_pos2traces_2012_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1);
v___x_2013_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_2010_, v_a_2006_, v_pos2traces_2012_, v___y_1999_, v___y_2000_);
lean_dec(v_a_2006_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v___y_2016_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2042_; lean_object* v_size_2048_; lean_object* v_buckets_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; uint8_t v___x_2052_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref(v___x_2013_);
v_size_2048_ = lean_ctor_get(v_a_2014_, 0);
lean_inc(v_size_2048_);
v_buckets_2049_ = lean_ctor_get(v_a_2014_, 1);
lean_inc_ref(v_buckets_2049_);
lean_dec(v_a_2014_);
v___x_2050_ = lean_mk_empty_array_with_capacity(v_size_2048_);
lean_dec(v_size_2048_);
v___x_2051_ = lean_array_get_size(v_buckets_2049_);
v___x_2052_ = lean_nat_dec_lt(v___x_2011_, v___x_2051_);
if (v___x_2052_ == 0)
{
lean_dec_ref(v_buckets_2049_);
v___y_2042_ = v___x_2050_;
goto v___jp_2041_;
}
else
{
uint8_t v___x_2053_; 
v___x_2053_ = lean_nat_dec_le(v___x_2051_, v___x_2051_);
if (v___x_2053_ == 0)
{
if (v___x_2052_ == 0)
{
lean_dec_ref(v_buckets_2049_);
v___y_2042_ = v___x_2050_;
goto v___jp_2041_;
}
else
{
size_t v___x_2054_; size_t v___x_2055_; lean_object* v___x_2056_; 
v___x_2054_ = ((size_t)0ULL);
v___x_2055_ = lean_usize_of_nat(v___x_2051_);
v___x_2056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_buckets_2049_, v___x_2054_, v___x_2055_, v___x_2050_);
lean_dec_ref(v_buckets_2049_);
v___y_2042_ = v___x_2056_;
goto v___jp_2041_;
}
}
else
{
size_t v___x_2057_; size_t v___x_2058_; lean_object* v___x_2059_; 
v___x_2057_ = ((size_t)0ULL);
v___x_2058_ = lean_usize_of_nat(v___x_2051_);
v___x_2059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_buckets_2049_, v___x_2057_, v___x_2058_, v___x_2050_);
lean_dec_ref(v_buckets_2049_);
v___y_2042_ = v___x_2059_;
goto v___jp_2041_;
}
}
v___jp_2015_:
{
lean_object* v___x_2017_; size_t v_sz_2018_; size_t v___x_2019_; lean_object* v___x_2020_; 
v___x_2017_ = lean_box(0);
v_sz_2018_ = lean_array_size(v___y_2016_);
v___x_2019_ = ((size_t)0ULL);
v___x_2020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_2010_, v___y_2016_, v_sz_2018_, v___x_2019_, v___x_2017_, v___y_1999_, v___y_2000_);
lean_dec_ref(v___y_2016_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2027_ == 0)
{
lean_object* v_unused_2028_; 
v_unused_2028_ = lean_ctor_get(v___x_2020_, 0);
lean_dec(v_unused_2028_);
v___x_2022_ = v___x_2020_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_dec(v___x_2020_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 0, v___x_2017_);
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2017_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
else
{
return v___x_2020_;
}
}
v___jp_2029_:
{
lean_object* v___x_2034_; 
lean_dec(v___y_2032_);
v___x_2034_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v___y_2030_, v___y_2031_, v___y_2033_);
lean_dec(v___y_2033_);
v___y_2016_ = v___x_2034_;
goto v___jp_2015_;
}
v___jp_2035_:
{
uint8_t v___x_2040_; 
v___x_2040_ = lean_nat_dec_le(v___y_2039_, v___y_2037_);
if (v___x_2040_ == 0)
{
lean_dec(v___y_2037_);
lean_inc(v___y_2039_);
v___y_2030_ = v___y_2036_;
v___y_2031_ = v___y_2039_;
v___y_2032_ = v___y_2038_;
v___y_2033_ = v___y_2039_;
goto v___jp_2029_;
}
else
{
v___y_2030_ = v___y_2036_;
v___y_2031_ = v___y_2039_;
v___y_2032_ = v___y_2038_;
v___y_2033_ = v___y_2037_;
goto v___jp_2029_;
}
}
v___jp_2041_:
{
lean_object* v___x_2043_; uint8_t v___x_2044_; 
v___x_2043_ = lean_array_get_size(v___y_2042_);
v___x_2044_ = lean_nat_dec_eq(v___x_2043_, v___x_2011_);
if (v___x_2044_ == 0)
{
lean_object* v___x_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; 
v___x_2045_ = lean_unsigned_to_nat(1u);
v___x_2046_ = lean_nat_sub(v___x_2043_, v___x_2045_);
v___x_2047_ = lean_nat_dec_le(v___x_2011_, v___x_2046_);
if (v___x_2047_ == 0)
{
lean_inc(v___x_2046_);
v___y_2036_ = v___y_2042_;
v___y_2037_ = v___x_2046_;
v___y_2038_ = v___x_2043_;
v___y_2039_ = v___x_2046_;
goto v___jp_2035_;
}
else
{
v___y_2036_ = v___y_2042_;
v___y_2037_ = v___x_2046_;
v___y_2038_ = v___x_2043_;
v___y_2039_ = v___x_2011_;
goto v___jp_2035_;
}
}
else
{
v___y_2016_ = v___y_2042_;
goto v___jp_2015_;
}
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
v_a_2060_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2013_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2013_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
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
lean_object* v___x_2068_; lean_object* v___x_2070_; 
lean_dec(v_a_2006_);
v___x_2068_ = lean_box(0);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 0, v___x_2068_);
v___x_2070_ = v___x_2008_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2068_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
else
{
lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2080_; 
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2080_ == 0)
{
lean_object* v_unused_2081_; 
v_unused_2081_ = lean_ctor_get(v___x_2004_, 0);
lean_dec(v_unused_2081_);
v___x_2074_ = v___x_2004_;
v_isShared_2075_ = v_isSharedCheck_2080_;
goto v_resetjp_2073_;
}
else
{
lean_dec(v___x_2004_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2080_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2076_; lean_object* v___x_2078_; 
v___x_2076_ = lean_box(0);
if (v_isShared_2075_ == 0)
{
lean_ctor_set_tag(v___x_2074_, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2076_);
v___x_2078_ = v___x_2074_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2076_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10___boxed(lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2082_, v___y_2083_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(lean_object* v_as_2086_, size_t v_sz_2087_, size_t v_i_2088_, lean_object* v_b_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
uint8_t v___x_2093_; 
v___x_2093_ = lean_usize_dec_lt(v_i_2088_, v_sz_2087_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; 
v___x_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2094_, 0, v_b_2089_);
return v___x_2094_;
}
else
{
lean_object* v_options_2095_; lean_object* v_a_2096_; lean_object* v___x_2097_; 
v_options_2095_ = lean_ctor_get(v___y_2090_, 2);
v_a_2096_ = lean_array_uget_borrowed(v_as_2086_, v_i_2088_);
lean_inc_ref(v_options_2095_);
lean_inc(v_a_2096_);
v___x_2097_ = l_Lean_Compiler_LCNF_resumeCompilation(v_a_2096_, v_options_2095_, v___y_2090_, v___y_2091_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v___x_2098_; 
lean_dec_ref(v___x_2097_);
v___x_2098_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2090_, v___y_2091_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v___x_2099_; size_t v___x_2100_; size_t v___x_2101_; 
lean_dec_ref(v___x_2098_);
v___x_2099_ = lean_box(0);
v___x_2100_ = ((size_t)1ULL);
v___x_2101_ = lean_usize_add(v_i_2088_, v___x_2100_);
v_i_2088_ = v___x_2101_;
v_b_2089_ = v___x_2099_;
goto _start;
}
else
{
return v___x_2098_;
}
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2104_; 
v_a_2103_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2103_);
lean_dec_ref(v___x_2097_);
v___x_2104_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2090_, v___y_2091_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2111_ == 0)
{
lean_object* v_unused_2112_; 
v_unused_2112_ = lean_ctor_get(v___x_2104_, 0);
lean_dec(v_unused_2112_);
v___x_2106_ = v___x_2104_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_dec(v___x_2104_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
lean_ctor_set_tag(v___x_2106_, 1);
lean_ctor_set(v___x_2106_, 0, v_a_2103_);
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2103_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
else
{
lean_dec(v_a_2103_);
return v___x_2104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11___boxed(lean_object* v_as_2113_, lean_object* v_sz_2114_, lean_object* v_i_2115_, lean_object* v_b_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
size_t v_sz_boxed_2120_; size_t v_i_boxed_2121_; lean_object* v_res_2122_; 
v_sz_boxed_2120_ = lean_unbox_usize(v_sz_2114_);
lean_dec(v_sz_2114_);
v_i_boxed_2121_ = lean_unbox_usize(v_i_2115_);
lean_dec(v_i_2115_);
v_res_2122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_as_2113_, v_sz_boxed_2120_, v_i_boxed_2121_, v_b_2116_, v___y_2117_, v___y_2118_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec_ref(v_as_2113_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(lean_object* v_as_2123_, size_t v_sz_2124_, size_t v_i_2125_, lean_object* v_b_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
uint8_t v___x_2130_; 
v___x_2130_ = lean_usize_dec_lt(v_i_2125_, v_sz_2124_);
if (v___x_2130_ == 0)
{
lean_object* v___x_2131_; 
v___x_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2131_, 0, v_b_2126_);
return v___x_2131_;
}
else
{
lean_object* v_a_2132_; lean_object* v_declNames_2133_; lean_object* v___x_2134_; size_t v_sz_2135_; size_t v___x_2136_; lean_object* v___x_2137_; 
v_a_2132_ = lean_array_uget_borrowed(v_as_2123_, v_i_2125_);
v_declNames_2133_ = lean_ctor_get(v_a_2132_, 0);
v___x_2134_ = lean_box(0);
v_sz_2135_ = lean_array_size(v_declNames_2133_);
v___x_2136_ = ((size_t)0ULL);
v___x_2137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_declNames_2133_, v_sz_2135_, v___x_2136_, v___x_2134_, v___y_2127_, v___y_2128_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v___x_2138_; 
lean_dec_ref(v___x_2137_);
v___x_2138_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v___y_2128_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v_unreported_2140_; lean_object* v___x_2141_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref(v___x_2138_);
v_unreported_2140_ = lean_ctor_get(v_a_2139_, 1);
lean_inc_ref(v_unreported_2140_);
lean_dec(v_a_2139_);
v___x_2141_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(v_unreported_2140_, v___x_2134_, v___y_2127_, v___y_2128_);
lean_dec_ref(v_unreported_2140_);
if (lean_obj_tag(v___x_2141_) == 0)
{
size_t v___x_2142_; size_t v___x_2143_; 
lean_dec_ref(v___x_2141_);
v___x_2142_ = ((size_t)1ULL);
v___x_2143_ = lean_usize_add(v_i_2125_, v___x_2142_);
v_i_2125_ = v___x_2143_;
v_b_2126_ = v___x_2134_;
goto _start;
}
else
{
return v___x_2141_;
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
v_a_2145_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2138_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2138_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2145_);
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
return v___x_2137_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13___boxed(lean_object* v_as_2153_, lean_object* v_sz_2154_, lean_object* v_i_2155_, lean_object* v_b_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
size_t v_sz_boxed_2160_; size_t v_i_boxed_2161_; lean_object* v_res_2162_; 
v_sz_boxed_2160_ = lean_unbox_usize(v_sz_2154_);
lean_dec(v_sz_2154_);
v_i_boxed_2161_ = lean_unbox_usize(v_i_2155_);
lean_dec(v_i_2155_);
v_res_2162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v_as_2153_, v_sz_boxed_2160_, v_i_boxed_2161_, v_b_2156_, v___y_2157_, v___y_2158_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec_ref(v_as_2153_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object* v_as_2163_, size_t v_i_2164_, size_t v_stop_2165_, lean_object* v_b_2166_){
_start:
{
uint8_t v___x_2167_; 
v___x_2167_ = lean_usize_dec_eq(v_i_2164_, v_stop_2165_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; lean_object* v_name_2169_; lean_object* v___x_2170_; size_t v___x_2171_; size_t v___x_2172_; 
v___x_2168_ = lean_array_uget_borrowed(v_as_2163_, v_i_2164_);
v_name_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_name_2169_);
v___x_2170_ = l_Lean_Compiler_LCNF_setDeclPublic(v_b_2166_, v_name_2169_);
v___x_2171_ = ((size_t)1ULL);
v___x_2172_ = lean_usize_add(v_i_2164_, v___x_2171_);
v_i_2164_ = v___x_2172_;
v_b_2166_ = v___x_2170_;
goto _start;
}
else
{
return v_b_2166_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object* v_as_2174_, lean_object* v_i_2175_, lean_object* v_stop_2176_, lean_object* v_b_2177_){
_start:
{
size_t v_i_boxed_2178_; size_t v_stop_boxed_2179_; lean_object* v_res_2180_; 
v_i_boxed_2178_ = lean_unbox_usize(v_i_2175_);
lean_dec(v_i_2175_);
v_stop_boxed_2179_ = lean_unbox_usize(v_stop_2176_);
lean_dec(v_stop_2176_);
v_res_2180_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v_as_2174_, v_i_boxed_2178_, v_stop_boxed_2179_, v_b_2177_);
lean_dec_ref(v_as_2174_);
return v_res_2180_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__43___lam__0(uint8_t v___y_2181_, uint8_t v_suppressElabErrors_2182_, lean_object* v_x_2183_){
_start:
{
if (lean_obj_tag(v_x_2183_) == 1)
{
lean_object* v_pre_2184_; 
v_pre_2184_ = lean_ctor_get(v_x_2183_, 0);
switch(lean_obj_tag(v_pre_2184_))
{
case 1:
{
lean_object* v_pre_2185_; 
v_pre_2185_ = lean_ctor_get(v_pre_2184_, 0);
switch(lean_obj_tag(v_pre_2185_))
{
case 0:
{
lean_object* v_str_2186_; lean_object* v_str_2187_; lean_object* v___x_2188_; uint8_t v___x_2189_; 
v_str_2186_ = lean_ctor_get(v_x_2183_, 1);
v_str_2187_ = lean_ctor_get(v_pre_2184_, 1);
v___x_2188_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0));
v___x_2189_ = lean_string_dec_eq(v_str_2187_, v___x_2188_);
if (v___x_2189_ == 0)
{
lean_object* v___x_2190_; uint8_t v___x_2191_; 
v___x_2190_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1));
v___x_2191_ = lean_string_dec_eq(v_str_2187_, v___x_2190_);
if (v___x_2191_ == 0)
{
return v___y_2181_;
}
else
{
lean_object* v___x_2192_; uint8_t v___x_2193_; 
v___x_2192_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2));
v___x_2193_ = lean_string_dec_eq(v_str_2186_, v___x_2192_);
if (v___x_2193_ == 0)
{
return v___y_2181_;
}
else
{
return v_suppressElabErrors_2182_;
}
}
}
else
{
lean_object* v___x_2194_; uint8_t v___x_2195_; 
v___x_2194_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3));
v___x_2195_ = lean_string_dec_eq(v_str_2186_, v___x_2194_);
if (v___x_2195_ == 0)
{
return v___y_2181_;
}
else
{
return v_suppressElabErrors_2182_;
}
}
}
case 1:
{
lean_object* v_pre_2196_; 
v_pre_2196_ = lean_ctor_get(v_pre_2185_, 0);
if (lean_obj_tag(v_pre_2196_) == 0)
{
lean_object* v_str_2197_; lean_object* v_str_2198_; lean_object* v_str_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; 
v_str_2197_ = lean_ctor_get(v_x_2183_, 1);
v_str_2198_ = lean_ctor_get(v_pre_2184_, 1);
v_str_2199_ = lean_ctor_get(v_pre_2185_, 1);
v___x_2200_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4));
v___x_2201_ = lean_string_dec_eq(v_str_2199_, v___x_2200_);
if (v___x_2201_ == 0)
{
return v___y_2181_;
}
else
{
lean_object* v___x_2202_; uint8_t v___x_2203_; 
v___x_2202_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5));
v___x_2203_ = lean_string_dec_eq(v_str_2198_, v___x_2202_);
if (v___x_2203_ == 0)
{
return v___y_2181_;
}
else
{
lean_object* v___x_2204_; uint8_t v___x_2205_; 
v___x_2204_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6));
v___x_2205_ = lean_string_dec_eq(v_str_2197_, v___x_2204_);
if (v___x_2205_ == 0)
{
return v___y_2181_;
}
else
{
return v_suppressElabErrors_2182_;
}
}
}
}
else
{
return v___y_2181_;
}
}
default: 
{
return v___y_2181_;
}
}
}
case 0:
{
lean_object* v_str_2206_; lean_object* v___x_2207_; uint8_t v___x_2208_; 
v_str_2206_ = lean_ctor_get(v_x_2183_, 1);
v___x_2207_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_2208_ = lean_string_dec_eq(v_str_2206_, v___x_2207_);
if (v___x_2208_ == 0)
{
return v___y_2181_;
}
else
{
return v_suppressElabErrors_2182_;
}
}
default: 
{
return v___y_2181_;
}
}
}
else
{
return v___y_2181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__43___lam__0___boxed(lean_object* v___y_2209_, lean_object* v_suppressElabErrors_2210_, lean_object* v_x_2211_){
_start:
{
uint8_t v___y_38770__boxed_2212_; uint8_t v_suppressElabErrors_boxed_2213_; uint8_t v_res_2214_; lean_object* v_r_2215_; 
v___y_38770__boxed_2212_ = lean_unbox(v___y_2209_);
v_suppressElabErrors_boxed_2213_ = lean_unbox(v_suppressElabErrors_2210_);
v_res_2214_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__43___lam__0(v___y_38770__boxed_2212_, v_suppressElabErrors_boxed_2213_, v_x_2211_);
lean_dec(v_x_2211_);
v_r_2215_ = lean_box(v_res_2214_);
return v_r_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__43(lean_object* v_ref_2216_, lean_object* v_msgData_2217_, uint8_t v_severity_2218_, uint8_t v_isSilent_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
lean_object* v___y_2224_; lean_object* v___y_2225_; uint8_t v___y_2226_; lean_object* v___y_2227_; uint8_t v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; uint8_t v___y_2264_; uint8_t v___y_2265_; uint8_t v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2285_; lean_object* v___y_2286_; lean_object* v___y_2287_; uint8_t v___y_2288_; uint8_t v___y_2289_; uint8_t v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; uint8_t v___y_2300_; uint8_t v___y_2301_; uint8_t v___y_2302_; uint8_t v___x_2307_; lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___y_2311_; uint8_t v___y_2312_; lean_object* v___y_2313_; uint8_t v___y_2314_; uint8_t v___y_2315_; uint8_t v___y_2317_; uint8_t v___x_2332_; 
v___x_2307_ = 2;
v___x_2332_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2218_, v___x_2307_);
if (v___x_2332_ == 0)
{
v___y_2317_ = v___x_2332_;
goto v___jp_2316_;
}
else
{
uint8_t v___x_2333_; 
lean_inc_ref(v_msgData_2217_);
v___x_2333_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2217_);
v___y_2317_ = v___x_2333_;
goto v___jp_2316_;
}
v___jp_2223_:
{
lean_object* v___x_2233_; lean_object* v_currNamespace_2234_; lean_object* v_openDecls_2235_; lean_object* v_env_2236_; lean_object* v_nextMacroScope_2237_; lean_object* v_ngen_2238_; lean_object* v_auxDeclNGen_2239_; lean_object* v_traceState_2240_; lean_object* v_cache_2241_; lean_object* v_messages_2242_; lean_object* v_infoState_2243_; lean_object* v_snapshotTasks_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2258_; 
v___x_2233_ = lean_st_ref_take(v___y_2232_);
v_currNamespace_2234_ = lean_ctor_get(v___y_2231_, 6);
v_openDecls_2235_ = lean_ctor_get(v___y_2231_, 7);
v_env_2236_ = lean_ctor_get(v___x_2233_, 0);
v_nextMacroScope_2237_ = lean_ctor_get(v___x_2233_, 1);
v_ngen_2238_ = lean_ctor_get(v___x_2233_, 2);
v_auxDeclNGen_2239_ = lean_ctor_get(v___x_2233_, 3);
v_traceState_2240_ = lean_ctor_get(v___x_2233_, 4);
v_cache_2241_ = lean_ctor_get(v___x_2233_, 5);
v_messages_2242_ = lean_ctor_get(v___x_2233_, 6);
v_infoState_2243_ = lean_ctor_get(v___x_2233_, 7);
v_snapshotTasks_2244_ = lean_ctor_get(v___x_2233_, 8);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2246_ = v___x_2233_;
v_isShared_2247_ = v_isSharedCheck_2258_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_snapshotTasks_2244_);
lean_inc(v_infoState_2243_);
lean_inc(v_messages_2242_);
lean_inc(v_cache_2241_);
lean_inc(v_traceState_2240_);
lean_inc(v_auxDeclNGen_2239_);
lean_inc(v_ngen_2238_);
lean_inc(v_nextMacroScope_2237_);
lean_inc(v_env_2236_);
lean_dec(v___x_2233_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2258_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2253_; 
lean_inc(v_openDecls_2235_);
lean_inc(v_currNamespace_2234_);
v___x_2248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2248_, 0, v_currNamespace_2234_);
lean_ctor_set(v___x_2248_, 1, v_openDecls_2235_);
v___x_2249_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
lean_ctor_set(v___x_2249_, 1, v___y_2227_);
lean_inc_ref(v___y_2225_);
lean_inc_ref(v___y_2224_);
v___x_2250_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2250_, 0, v___y_2224_);
lean_ctor_set(v___x_2250_, 1, v___y_2230_);
lean_ctor_set(v___x_2250_, 2, v___y_2229_);
lean_ctor_set(v___x_2250_, 3, v___y_2225_);
lean_ctor_set(v___x_2250_, 4, v___x_2249_);
lean_ctor_set_uint8(v___x_2250_, sizeof(void*)*5, v___y_2226_);
lean_ctor_set_uint8(v___x_2250_, sizeof(void*)*5 + 1, v___y_2228_);
lean_ctor_set_uint8(v___x_2250_, sizeof(void*)*5 + 2, v_isSilent_2219_);
v___x_2251_ = l_Lean_MessageLog_add(v___x_2250_, v_messages_2242_);
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 6, v___x_2251_);
v___x_2253_ = v___x_2246_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_env_2236_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v_nextMacroScope_2237_);
lean_ctor_set(v_reuseFailAlloc_2257_, 2, v_ngen_2238_);
lean_ctor_set(v_reuseFailAlloc_2257_, 3, v_auxDeclNGen_2239_);
lean_ctor_set(v_reuseFailAlloc_2257_, 4, v_traceState_2240_);
lean_ctor_set(v_reuseFailAlloc_2257_, 5, v_cache_2241_);
lean_ctor_set(v_reuseFailAlloc_2257_, 6, v___x_2251_);
lean_ctor_set(v_reuseFailAlloc_2257_, 7, v_infoState_2243_);
lean_ctor_set(v_reuseFailAlloc_2257_, 8, v_snapshotTasks_2244_);
v___x_2253_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2254_ = lean_st_ref_set(v___y_2232_, v___x_2253_);
v___x_2255_ = lean_box(0);
v___x_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
return v___x_2256_;
}
}
}
v___jp_2259_:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2283_; 
v___x_2268_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2217_);
v___x_2269_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v___x_2268_, v___y_2220_, v___y_2221_);
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2272_ = v___x_2269_;
v_isShared_2273_ = v_isSharedCheck_2283_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2269_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2283_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
lean_inc_ref_n(v___y_2262_, 2);
v___x_2274_ = l_Lean_FileMap_toPosition(v___y_2262_, v___y_2261_);
lean_dec(v___y_2261_);
v___x_2275_ = l_Lean_FileMap_toPosition(v___y_2262_, v___y_2267_);
lean_dec(v___y_2267_);
v___x_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2275_);
v___x_2277_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1));
if (v___y_2264_ == 0)
{
lean_del_object(v___x_2272_);
lean_dec_ref(v___y_2260_);
v___y_2224_ = v___y_2263_;
v___y_2225_ = v___x_2277_;
v___y_2226_ = v___y_2265_;
v___y_2227_ = v_a_2270_;
v___y_2228_ = v___y_2266_;
v___y_2229_ = v___x_2276_;
v___y_2230_ = v___x_2274_;
v___y_2231_ = v___y_2220_;
v___y_2232_ = v___y_2221_;
goto v___jp_2223_;
}
else
{
uint8_t v___x_2278_; 
lean_inc(v_a_2270_);
v___x_2278_ = l_Lean_MessageData_hasTag(v___y_2260_, v_a_2270_);
if (v___x_2278_ == 0)
{
lean_object* v___x_2279_; lean_object* v___x_2281_; 
lean_dec_ref(v___x_2276_);
lean_dec_ref(v___x_2274_);
lean_dec(v_a_2270_);
v___x_2279_ = lean_box(0);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 0, v___x_2279_);
v___x_2281_ = v___x_2272_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2279_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
else
{
lean_del_object(v___x_2272_);
v___y_2224_ = v___y_2263_;
v___y_2225_ = v___x_2277_;
v___y_2226_ = v___y_2265_;
v___y_2227_ = v_a_2270_;
v___y_2228_ = v___y_2266_;
v___y_2229_ = v___x_2276_;
v___y_2230_ = v___x_2274_;
v___y_2231_ = v___y_2220_;
v___y_2232_ = v___y_2221_;
goto v___jp_2223_;
}
}
}
}
v___jp_2284_:
{
lean_object* v___x_2293_; 
v___x_2293_ = l_Lean_Syntax_getTailPos_x3f(v___y_2291_, v___y_2288_);
lean_dec(v___y_2291_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_inc(v___y_2292_);
v___y_2260_ = v___y_2285_;
v___y_2261_ = v___y_2292_;
v___y_2262_ = v___y_2286_;
v___y_2263_ = v___y_2287_;
v___y_2264_ = v___y_2289_;
v___y_2265_ = v___y_2288_;
v___y_2266_ = v___y_2290_;
v___y_2267_ = v___y_2292_;
goto v___jp_2259_;
}
else
{
lean_object* v_val_2294_; 
v_val_2294_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_val_2294_);
lean_dec_ref(v___x_2293_);
v___y_2260_ = v___y_2285_;
v___y_2261_ = v___y_2292_;
v___y_2262_ = v___y_2286_;
v___y_2263_ = v___y_2287_;
v___y_2264_ = v___y_2289_;
v___y_2265_ = v___y_2288_;
v___y_2266_ = v___y_2290_;
v___y_2267_ = v_val_2294_;
goto v___jp_2259_;
}
}
v___jp_2295_:
{
lean_object* v_ref_2303_; lean_object* v___x_2304_; 
v_ref_2303_ = l_Lean_replaceRef(v_ref_2216_, v___y_2297_);
v___x_2304_ = l_Lean_Syntax_getPos_x3f(v_ref_2303_, v___y_2301_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v___x_2305_; 
v___x_2305_ = lean_unsigned_to_nat(0u);
v___y_2285_ = v___y_2296_;
v___y_2286_ = v___y_2298_;
v___y_2287_ = v___y_2299_;
v___y_2288_ = v___y_2301_;
v___y_2289_ = v___y_2300_;
v___y_2290_ = v___y_2302_;
v___y_2291_ = v_ref_2303_;
v___y_2292_ = v___x_2305_;
goto v___jp_2284_;
}
else
{
lean_object* v_val_2306_; 
v_val_2306_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_val_2306_);
lean_dec_ref(v___x_2304_);
v___y_2285_ = v___y_2296_;
v___y_2286_ = v___y_2298_;
v___y_2287_ = v___y_2299_;
v___y_2288_ = v___y_2301_;
v___y_2289_ = v___y_2300_;
v___y_2290_ = v___y_2302_;
v___y_2291_ = v_ref_2303_;
v___y_2292_ = v_val_2306_;
goto v___jp_2284_;
}
}
v___jp_2308_:
{
if (v___y_2315_ == 0)
{
v___y_2296_ = v___y_2313_;
v___y_2297_ = v___y_2309_;
v___y_2298_ = v___y_2310_;
v___y_2299_ = v___y_2311_;
v___y_2300_ = v___y_2312_;
v___y_2301_ = v___y_2314_;
v___y_2302_ = v_severity_2218_;
goto v___jp_2295_;
}
else
{
v___y_2296_ = v___y_2313_;
v___y_2297_ = v___y_2309_;
v___y_2298_ = v___y_2310_;
v___y_2299_ = v___y_2311_;
v___y_2300_ = v___y_2312_;
v___y_2301_ = v___y_2314_;
v___y_2302_ = v___x_2307_;
goto v___jp_2295_;
}
}
v___jp_2316_:
{
if (v___y_2317_ == 0)
{
lean_object* v_fileName_2318_; lean_object* v_fileMap_2319_; lean_object* v_options_2320_; lean_object* v_ref_2321_; uint8_t v_suppressElabErrors_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___f_2325_; uint8_t v___x_2326_; uint8_t v___x_2327_; 
v_fileName_2318_ = lean_ctor_get(v___y_2220_, 0);
v_fileMap_2319_ = lean_ctor_get(v___y_2220_, 1);
v_options_2320_ = lean_ctor_get(v___y_2220_, 2);
v_ref_2321_ = lean_ctor_get(v___y_2220_, 5);
v_suppressElabErrors_2322_ = lean_ctor_get_uint8(v___y_2220_, sizeof(void*)*14 + 1);
v___x_2323_ = lean_box(v___y_2317_);
v___x_2324_ = lean_box(v_suppressElabErrors_2322_);
v___f_2325_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__43___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2325_, 0, v___x_2323_);
lean_closure_set(v___f_2325_, 1, v___x_2324_);
v___x_2326_ = 1;
v___x_2327_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2218_, v___x_2326_);
if (v___x_2327_ == 0)
{
v___y_2309_ = v_ref_2321_;
v___y_2310_ = v_fileMap_2319_;
v___y_2311_ = v_fileName_2318_;
v___y_2312_ = v_suppressElabErrors_2322_;
v___y_2313_ = v___f_2325_;
v___y_2314_ = v___y_2317_;
v___y_2315_ = v___x_2327_;
goto v___jp_2308_;
}
else
{
lean_object* v___x_2328_; uint8_t v___x_2329_; 
v___x_2328_ = l_Lean_warningAsError;
v___x_2329_ = l_Lean_Option_get___at___00main_spec__8(v_options_2320_, v___x_2328_);
v___y_2309_ = v_ref_2321_;
v___y_2310_ = v_fileMap_2319_;
v___y_2311_ = v_fileName_2318_;
v___y_2312_ = v_suppressElabErrors_2322_;
v___y_2313_ = v___f_2325_;
v___y_2314_ = v___y_2317_;
v___y_2315_ = v___x_2329_;
goto v___jp_2308_;
}
}
else
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
lean_dec_ref(v_msgData_2217_);
v___x_2330_ = lean_box(0);
v___x_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2330_);
return v___x_2331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__43___boxed(lean_object* v_ref_2334_, lean_object* v_msgData_2335_, lean_object* v_severity_2336_, lean_object* v_isSilent_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
uint8_t v_severity_boxed_2341_; uint8_t v_isSilent_boxed_2342_; lean_object* v_res_2343_; 
v_severity_boxed_2341_ = lean_unbox(v_severity_2336_);
v_isSilent_boxed_2342_ = lean_unbox(v_isSilent_2337_);
v_res_2343_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__43(v_ref_2334_, v_msgData_2335_, v_severity_boxed_2341_, v_isSilent_boxed_2342_, v___y_2338_, v___y_2339_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v_ref_2334_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(lean_object* v_msgData_2344_, uint8_t v_severity_2345_, uint8_t v_isSilent_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v_ref_2350_; lean_object* v___x_2351_; 
v_ref_2350_ = lean_ctor_get(v___y_2347_, 5);
v___x_2351_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__43(v_ref_2350_, v_msgData_2344_, v_severity_2345_, v_isSilent_2346_, v___y_2347_, v___y_2348_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30___boxed(lean_object* v_msgData_2352_, lean_object* v_severity_2353_, lean_object* v_isSilent_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
uint8_t v_severity_boxed_2358_; uint8_t v_isSilent_boxed_2359_; lean_object* v_res_2360_; 
v_severity_boxed_2358_ = lean_unbox(v_severity_2353_);
v_isSilent_boxed_2359_ = lean_unbox(v_isSilent_2354_);
v_res_2360_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2352_, v_severity_boxed_2358_, v_isSilent_boxed_2359_, v___y_2355_, v___y_2356_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14(lean_object* v_msgData_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
uint8_t v___x_2365_; uint8_t v___x_2366_; lean_object* v___x_2367_; 
v___x_2365_ = 2;
v___x_2366_ = 0;
v___x_2367_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2361_, v___x_2365_, v___x_2366_, v___y_2362_, v___y_2363_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14___boxed(lean_object* v_msgData_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_Lean_logError___at___00main_spec__14(v_msgData_2368_, v___y_2369_, v___y_2370_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(lean_object* v_x2_2373_, lean_object* v_as_2374_, size_t v_i_2375_, size_t v_stop_2376_, lean_object* v_b_2377_){
_start:
{
uint8_t v___x_2378_; 
v___x_2378_ = lean_usize_dec_eq(v_i_2375_, v_stop_2376_);
if (v___x_2378_ == 0)
{
lean_object* v___x_2379_; lean_object* v___x_2380_; size_t v___x_2381_; size_t v___x_2382_; 
v___x_2379_ = lean_array_uget_borrowed(v_as_2374_, v_i_2375_);
lean_inc_ref(v_x2_2373_);
lean_inc(v___x_2379_);
v___x_2380_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2379_, v_x2_2373_, v_b_2377_);
v___x_2381_ = ((size_t)1ULL);
v___x_2382_ = lean_usize_add(v_i_2375_, v___x_2381_);
v_i_2375_ = v___x_2382_;
v_b_2377_ = v___x_2380_;
goto _start;
}
else
{
lean_dec_ref(v_x2_2373_);
return v_b_2377_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(lean_object* v_x2_2384_, lean_object* v_as_2385_, lean_object* v_i_2386_, lean_object* v_stop_2387_, lean_object* v_b_2388_){
_start:
{
size_t v_i_boxed_2389_; size_t v_stop_boxed_2390_; lean_object* v_res_2391_; 
v_i_boxed_2389_ = lean_unbox_usize(v_i_2386_);
lean_dec(v_i_2386_);
v_stop_boxed_2390_ = lean_unbox_usize(v_stop_2387_);
lean_dec(v_stop_2387_);
v_res_2391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v_x2_2384_, v_as_2385_, v_i_boxed_2389_, v_stop_boxed_2390_, v_b_2388_);
lean_dec_ref(v_as_2385_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object* v_as_2392_, size_t v_i_2393_, size_t v_stop_2394_, lean_object* v_b_2395_){
_start:
{
lean_object* v___y_2397_; uint8_t v___x_2401_; 
v___x_2401_ = lean_usize_dec_eq(v_i_2393_, v_stop_2394_);
if (v___x_2401_ == 0)
{
lean_object* v___x_2402_; lean_object* v_declNames_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; uint8_t v___x_2406_; 
v___x_2402_ = lean_array_uget_borrowed(v_as_2392_, v_i_2393_);
v_declNames_2403_ = lean_ctor_get(v___x_2402_, 0);
v___x_2404_ = lean_unsigned_to_nat(0u);
v___x_2405_ = lean_array_get_size(v_declNames_2403_);
v___x_2406_ = lean_nat_dec_lt(v___x_2404_, v___x_2405_);
if (v___x_2406_ == 0)
{
v___y_2397_ = v_b_2395_;
goto v___jp_2396_;
}
else
{
uint8_t v___x_2407_; 
v___x_2407_ = lean_nat_dec_le(v___x_2405_, v___x_2405_);
if (v___x_2407_ == 0)
{
if (v___x_2406_ == 0)
{
v___y_2397_ = v_b_2395_;
goto v___jp_2396_;
}
else
{
size_t v___x_2408_; size_t v___x_2409_; lean_object* v___x_2410_; 
v___x_2408_ = ((size_t)0ULL);
v___x_2409_ = lean_usize_of_nat(v___x_2405_);
lean_inc(v___x_2402_);
v___x_2410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2402_, v_declNames_2403_, v___x_2408_, v___x_2409_, v_b_2395_);
v___y_2397_ = v___x_2410_;
goto v___jp_2396_;
}
}
else
{
size_t v___x_2411_; size_t v___x_2412_; lean_object* v___x_2413_; 
v___x_2411_ = ((size_t)0ULL);
v___x_2412_ = lean_usize_of_nat(v___x_2405_);
lean_inc(v___x_2402_);
v___x_2413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2402_, v_declNames_2403_, v___x_2411_, v___x_2412_, v_b_2395_);
v___y_2397_ = v___x_2413_;
goto v___jp_2396_;
}
}
}
else
{
return v_b_2395_;
}
v___jp_2396_:
{
size_t v___x_2398_; size_t v___x_2399_; 
v___x_2398_ = ((size_t)1ULL);
v___x_2399_ = lean_usize_add(v_i_2393_, v___x_2398_);
v_i_2393_ = v___x_2399_;
v_b_2395_ = v___y_2397_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object* v_as_2414_, lean_object* v_i_2415_, lean_object* v_stop_2416_, lean_object* v_b_2417_){
_start:
{
size_t v_i_boxed_2418_; size_t v_stop_boxed_2419_; lean_object* v_res_2420_; 
v_i_boxed_2418_ = lean_unbox_usize(v_i_2415_);
lean_dec(v_i_2415_);
v_stop_boxed_2419_ = lean_unbox_usize(v_stop_2416_);
lean_dec(v_stop_2416_);
v_res_2420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v_as_2414_, v_i_boxed_2418_, v_stop_boxed_2419_, v_b_2417_);
lean_dec_ref(v_as_2414_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(lean_object* v_a_2421_, lean_object* v_as_2422_, size_t v_i_2423_, size_t v_stop_2424_, lean_object* v_b_2425_){
_start:
{
lean_object* v___y_2427_; uint8_t v___x_2431_; 
v___x_2431_ = lean_usize_dec_eq(v_i_2423_, v_stop_2424_);
if (v___x_2431_ == 0)
{
lean_object* v___x_2432_; lean_object* v_name_2433_; uint8_t v___x_2434_; 
v___x_2432_ = lean_array_uget_borrowed(v_as_2422_, v_i_2423_);
v_name_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_name_2433_);
lean_inc_ref(v_a_2421_);
v___x_2434_ = l_Lean_isExtern(v_a_2421_, v_name_2433_);
if (v___x_2434_ == 0)
{
v___y_2427_ = v_b_2425_;
goto v___jp_2426_;
}
else
{
lean_object* v___x_2435_; 
lean_inc(v___x_2432_);
v___x_2435_ = lean_array_push(v_b_2425_, v___x_2432_);
v___y_2427_ = v___x_2435_;
goto v___jp_2426_;
}
}
else
{
lean_dec_ref(v_a_2421_);
return v_b_2425_;
}
v___jp_2426_:
{
size_t v___x_2428_; size_t v___x_2429_; 
v___x_2428_ = ((size_t)1ULL);
v___x_2429_ = lean_usize_add(v_i_2423_, v___x_2428_);
v_i_2423_ = v___x_2429_;
v_b_2425_ = v___y_2427_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19___boxed(lean_object* v_a_2436_, lean_object* v_as_2437_, lean_object* v_i_2438_, lean_object* v_stop_2439_, lean_object* v_b_2440_){
_start:
{
size_t v_i_boxed_2441_; size_t v_stop_boxed_2442_; lean_object* v_res_2443_; 
v_i_boxed_2441_ = lean_unbox_usize(v_i_2438_);
lean_dec(v_i_2438_);
v_stop_boxed_2442_ = lean_unbox_usize(v_stop_2439_);
lean_dec(v_stop_2439_);
v_res_2443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_2436_, v_as_2437_, v_i_boxed_2441_, v_stop_boxed_2442_, v_b_2440_);
lean_dec_ref(v_as_2437_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(lean_object* v_as_2444_, size_t v_sz_2445_, size_t v_i_2446_, lean_object* v_b_2447_){
_start:
{
uint8_t v___x_2449_; 
v___x_2449_ = lean_usize_dec_lt(v_i_2446_, v_sz_2445_);
if (v___x_2449_ == 0)
{
lean_object* v___x_2450_; 
v___x_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2450_, 0, v_b_2447_);
return v___x_2450_;
}
else
{
uint8_t v___x_2451_; lean_object* v_a_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
lean_dec_ref(v_b_2447_);
v___x_2451_ = 0;
v_a_2452_ = lean_array_uget_borrowed(v_as_2444_, v_i_2446_);
lean_inc(v_a_2452_);
v___x_2453_ = l_Lean_Message_toString(v_a_2452_, v___x_2451_);
v___x_2454_ = l_IO_eprintln___at___00main_spec__6(v___x_2453_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v___x_2455_; size_t v___x_2456_; size_t v___x_2457_; 
lean_dec_ref(v___x_2454_);
v___x_2455_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37_spec__50___redArg___closed__0));
v___x_2456_ = ((size_t)1ULL);
v___x_2457_ = lean_usize_add(v_i_2446_, v___x_2456_);
v_i_2446_ = v___x_2457_;
v_b_2447_ = v___x_2455_;
goto _start;
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
v_a_2459_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2454_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2454_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27___boxed(lean_object* v_as_2467_, lean_object* v_sz_2468_, lean_object* v_i_2469_, lean_object* v_b_2470_, lean_object* v___y_2471_){
_start:
{
size_t v_sz_boxed_2472_; size_t v_i_boxed_2473_; lean_object* v_res_2474_; 
v_sz_boxed_2472_ = lean_unbox_usize(v_sz_2468_);
lean_dec(v_sz_2468_);
v_i_boxed_2473_ = lean_unbox_usize(v_i_2469_);
lean_dec(v_i_2469_);
v_res_2474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2467_, v_sz_boxed_2472_, v_i_boxed_2473_, v_b_2470_);
lean_dec_ref(v_as_2467_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(lean_object* v_as_2475_, size_t v_sz_2476_, size_t v_i_2477_, lean_object* v_b_2478_){
_start:
{
uint8_t v___x_2480_; 
v___x_2480_ = lean_usize_dec_lt(v_i_2477_, v_sz_2476_);
if (v___x_2480_ == 0)
{
lean_object* v___x_2481_; 
v___x_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2481_, 0, v_b_2478_);
return v___x_2481_;
}
else
{
uint8_t v___x_2482_; lean_object* v_a_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
lean_dec_ref(v_b_2478_);
v___x_2482_ = 0;
v_a_2483_ = lean_array_uget_borrowed(v_as_2475_, v_i_2477_);
lean_inc(v_a_2483_);
v___x_2484_ = l_Lean_Message_toString(v_a_2483_, v___x_2482_);
v___x_2485_ = l_IO_eprintln___at___00main_spec__6(v___x_2484_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v___x_2486_; size_t v___x_2487_; size_t v___x_2488_; lean_object* v___x_2489_; 
lean_dec_ref(v___x_2485_);
v___x_2486_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37_spec__50___redArg___closed__0));
v___x_2487_ = ((size_t)1ULL);
v___x_2488_ = lean_usize_add(v_i_2477_, v___x_2487_);
v___x_2489_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2475_, v_sz_2476_, v___x_2488_, v___x_2486_);
return v___x_2489_;
}
else
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2497_; 
v_a_2490_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2492_ = v___x_2485_;
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2485_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2493_ == 0)
{
v___x_2495_ = v___x_2492_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2490_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14___boxed(lean_object* v_as_2498_, lean_object* v_sz_2499_, lean_object* v_i_2500_, lean_object* v_b_2501_, lean_object* v___y_2502_){
_start:
{
size_t v_sz_boxed_2503_; size_t v_i_boxed_2504_; lean_object* v_res_2505_; 
v_sz_boxed_2503_ = lean_unbox_usize(v_sz_2499_);
lean_dec(v_sz_2499_);
v_i_boxed_2504_ = lean_unbox_usize(v_i_2500_);
lean_dec(v_i_2500_);
v_res_2505_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_as_2498_, v_sz_boxed_2503_, v_i_boxed_2504_, v_b_2501_);
lean_dec_ref(v_as_2498_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(lean_object* v_init_2506_, lean_object* v_n_2507_, lean_object* v_b_2508_){
_start:
{
if (lean_obj_tag(v_n_2507_) == 0)
{
lean_object* v_cs_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; size_t v_sz_2513_; size_t v___x_2514_; lean_object* v___x_2515_; 
v_cs_2510_ = lean_ctor_get(v_n_2507_, 0);
v___x_2511_ = lean_box(0);
v___x_2512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2511_);
lean_ctor_set(v___x_2512_, 1, v_b_2508_);
v_sz_2513_ = lean_array_size(v_cs_2510_);
v___x_2514_ = ((size_t)0ULL);
v___x_2515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2506_, v_cs_2510_, v_sz_2513_, v___x_2514_, v___x_2512_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2530_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2518_ = v___x_2515_;
v_isShared_2519_ = v_isSharedCheck_2530_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2515_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2530_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v_fst_2520_; 
v_fst_2520_ = lean_ctor_get(v_a_2516_, 0);
if (lean_obj_tag(v_fst_2520_) == 0)
{
lean_object* v_snd_2521_; lean_object* v___x_2522_; lean_object* v___x_2524_; 
v_snd_2521_ = lean_ctor_get(v_a_2516_, 1);
lean_inc(v_snd_2521_);
lean_dec(v_a_2516_);
v___x_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2522_, 0, v_snd_2521_);
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v___x_2522_);
v___x_2524_ = v___x_2518_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2522_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
else
{
lean_object* v_val_2526_; lean_object* v___x_2528_; 
lean_inc_ref(v_fst_2520_);
lean_dec(v_a_2516_);
v_val_2526_ = lean_ctor_get(v_fst_2520_, 0);
lean_inc(v_val_2526_);
lean_dec_ref(v_fst_2520_);
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v_val_2526_);
v___x_2528_ = v___x_2518_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_val_2526_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
v_a_2531_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2515_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2515_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
else
{
lean_object* v_vs_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; size_t v_sz_2542_; size_t v___x_2543_; lean_object* v___x_2544_; 
v_vs_2539_ = lean_ctor_get(v_n_2507_, 0);
v___x_2540_ = lean_box(0);
v___x_2541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
lean_ctor_set(v___x_2541_, 1, v_b_2508_);
v_sz_2542_ = lean_array_size(v_vs_2539_);
v___x_2543_ = ((size_t)0ULL);
v___x_2544_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_vs_2539_, v_sz_2542_, v___x_2543_, v___x_2541_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2559_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2547_ = v___x_2544_;
v_isShared_2548_ = v_isSharedCheck_2559_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2544_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2559_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v_fst_2549_; 
v_fst_2549_ = lean_ctor_get(v_a_2545_, 0);
if (lean_obj_tag(v_fst_2549_) == 0)
{
lean_object* v_snd_2550_; lean_object* v___x_2551_; lean_object* v___x_2553_; 
v_snd_2550_ = lean_ctor_get(v_a_2545_, 1);
lean_inc(v_snd_2550_);
lean_dec(v_a_2545_);
v___x_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2551_, 0, v_snd_2550_);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 0, v___x_2551_);
v___x_2553_ = v___x_2547_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2551_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
else
{
lean_object* v_val_2555_; lean_object* v___x_2557_; 
lean_inc_ref(v_fst_2549_);
lean_dec(v_a_2545_);
v_val_2555_ = lean_ctor_get(v_fst_2549_, 0);
lean_inc(v_val_2555_);
lean_dec_ref(v_fst_2549_);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 0, v_val_2555_);
v___x_2557_ = v___x_2547_;
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
v_a_2560_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2544_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2544_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(lean_object* v_init_2568_, lean_object* v_as_2569_, size_t v_sz_2570_, size_t v_i_2571_, lean_object* v_b_2572_){
_start:
{
uint8_t v___x_2574_; 
v___x_2574_ = lean_usize_dec_lt(v_i_2571_, v_sz_2570_);
if (v___x_2574_ == 0)
{
lean_object* v___x_2575_; 
v___x_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2575_, 0, v_b_2572_);
return v___x_2575_;
}
else
{
lean_object* v_snd_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2610_; 
v_snd_2576_ = lean_ctor_get(v_b_2572_, 1);
v_isSharedCheck_2610_ = !lean_is_exclusive(v_b_2572_);
if (v_isSharedCheck_2610_ == 0)
{
lean_object* v_unused_2611_; 
v_unused_2611_ = lean_ctor_get(v_b_2572_, 0);
lean_dec(v_unused_2611_);
v___x_2578_ = v_b_2572_;
v_isShared_2579_ = v_isSharedCheck_2610_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_snd_2576_);
lean_dec(v_b_2572_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2610_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v_a_2580_; lean_object* v___x_2581_; 
v_a_2580_ = lean_array_uget_borrowed(v_as_2569_, v_i_2571_);
lean_inc(v_snd_2576_);
v___x_2581_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2568_, v_a_2580_, v_snd_2576_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2601_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2584_ = v___x_2581_;
v_isShared_2585_ = v_isSharedCheck_2601_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2581_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2601_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
if (lean_obj_tag(v_a_2582_) == 0)
{
lean_object* v___x_2586_; lean_object* v___x_2588_; 
v___x_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2586_, 0, v_a_2582_);
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 0, v___x_2586_);
v___x_2588_ = v___x_2578_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v___x_2586_);
lean_ctor_set(v_reuseFailAlloc_2592_, 1, v_snd_2576_);
v___x_2588_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
lean_object* v___x_2590_; 
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 0, v___x_2588_);
v___x_2590_ = v___x_2584_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v___x_2588_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
else
{
lean_object* v_a_2593_; lean_object* v___x_2594_; lean_object* v___x_2596_; 
lean_del_object(v___x_2584_);
lean_dec(v_snd_2576_);
v_a_2593_ = lean_ctor_get(v_a_2582_, 0);
lean_inc(v_a_2593_);
lean_dec_ref(v_a_2582_);
v___x_2594_ = lean_box(0);
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 1, v_a_2593_);
lean_ctor_set(v___x_2578_, 0, v___x_2594_);
v___x_2596_ = v___x_2578_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2594_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v_a_2593_);
v___x_2596_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
size_t v___x_2597_; size_t v___x_2598_; 
v___x_2597_ = ((size_t)1ULL);
v___x_2598_ = lean_usize_add(v_i_2571_, v___x_2597_);
v_i_2571_ = v___x_2598_;
v_b_2572_ = v___x_2596_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
lean_del_object(v___x_2578_);
lean_dec(v_snd_2576_);
v_a_2602_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___x_2581_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2581_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13___boxed(lean_object* v_init_2612_, lean_object* v_as_2613_, lean_object* v_sz_2614_, lean_object* v_i_2615_, lean_object* v_b_2616_, lean_object* v___y_2617_){
_start:
{
size_t v_sz_boxed_2618_; size_t v_i_boxed_2619_; lean_object* v_res_2620_; 
v_sz_boxed_2618_ = lean_unbox_usize(v_sz_2614_);
lean_dec(v_sz_2614_);
v_i_boxed_2619_ = lean_unbox_usize(v_i_2615_);
lean_dec(v_i_2615_);
v_res_2620_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2612_, v_as_2613_, v_sz_boxed_2618_, v_i_boxed_2619_, v_b_2616_);
lean_dec_ref(v_as_2613_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10___boxed(lean_object* v_init_2621_, lean_object* v_n_2622_, lean_object* v_b_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2621_, v_n_2622_, v_b_2623_);
lean_dec_ref(v_n_2622_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(lean_object* v_as_2626_, size_t v_sz_2627_, size_t v_i_2628_, lean_object* v_b_2629_){
_start:
{
uint8_t v___x_2631_; 
v___x_2631_ = lean_usize_dec_lt(v_i_2628_, v_sz_2627_);
if (v___x_2631_ == 0)
{
lean_object* v___x_2632_; 
v___x_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2632_, 0, v_b_2629_);
return v___x_2632_;
}
else
{
uint8_t v___x_2633_; lean_object* v_a_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
lean_dec_ref(v_b_2629_);
v___x_2633_ = 0;
v_a_2634_ = lean_array_uget_borrowed(v_as_2626_, v_i_2628_);
lean_inc(v_a_2634_);
v___x_2635_ = l_Lean_Message_toString(v_a_2634_, v___x_2633_);
v___x_2636_ = l_IO_eprintln___at___00main_spec__6(v___x_2635_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v___x_2637_; size_t v___x_2638_; size_t v___x_2639_; 
lean_dec_ref(v___x_2636_);
v___x_2637_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__39___redArg___closed__0));
v___x_2638_ = ((size_t)1ULL);
v___x_2639_ = lean_usize_add(v_i_2628_, v___x_2638_);
v_i_2628_ = v___x_2639_;
v_b_2629_ = v___x_2637_;
goto _start;
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
v_a_2641_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2636_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2636_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16___boxed(lean_object* v_as_2649_, lean_object* v_sz_2650_, lean_object* v_i_2651_, lean_object* v_b_2652_, lean_object* v___y_2653_){
_start:
{
size_t v_sz_boxed_2654_; size_t v_i_boxed_2655_; lean_object* v_res_2656_; 
v_sz_boxed_2654_ = lean_unbox_usize(v_sz_2650_);
lean_dec(v_sz_2650_);
v_i_boxed_2655_ = lean_unbox_usize(v_i_2651_);
lean_dec(v_i_2651_);
v_res_2656_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2649_, v_sz_boxed_2654_, v_i_boxed_2655_, v_b_2652_);
lean_dec_ref(v_as_2649_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(lean_object* v_as_2657_, size_t v_sz_2658_, size_t v_i_2659_, lean_object* v_b_2660_){
_start:
{
uint8_t v___x_2662_; 
v___x_2662_ = lean_usize_dec_lt(v_i_2659_, v_sz_2658_);
if (v___x_2662_ == 0)
{
lean_object* v___x_2663_; 
v___x_2663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2663_, 0, v_b_2660_);
return v___x_2663_;
}
else
{
uint8_t v___x_2664_; lean_object* v_a_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
lean_dec_ref(v_b_2660_);
v___x_2664_ = 0;
v_a_2665_ = lean_array_uget_borrowed(v_as_2657_, v_i_2659_);
lean_inc(v_a_2665_);
v___x_2666_ = l_Lean_Message_toString(v_a_2665_, v___x_2664_);
v___x_2667_ = l_IO_eprintln___at___00main_spec__6(v___x_2666_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v___x_2668_; size_t v___x_2669_; size_t v___x_2670_; lean_object* v___x_2671_; 
lean_dec_ref(v___x_2667_);
v___x_2668_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__39___redArg___closed__0));
v___x_2669_ = ((size_t)1ULL);
v___x_2670_ = lean_usize_add(v_i_2659_, v___x_2669_);
v___x_2671_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2657_, v_sz_2658_, v___x_2670_, v___x_2668_);
return v___x_2671_;
}
else
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2679_; 
v_a_2672_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2674_ = v___x_2667_;
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2667_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2677_; 
if (v_isShared_2675_ == 0)
{
v___x_2677_ = v___x_2674_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2672_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11___boxed(lean_object* v_as_2680_, lean_object* v_sz_2681_, lean_object* v_i_2682_, lean_object* v_b_2683_, lean_object* v___y_2684_){
_start:
{
size_t v_sz_boxed_2685_; size_t v_i_boxed_2686_; lean_object* v_res_2687_; 
v_sz_boxed_2685_ = lean_unbox_usize(v_sz_2681_);
lean_dec(v_sz_2681_);
v_i_boxed_2686_ = lean_unbox_usize(v_i_2682_);
lean_dec(v_i_2682_);
v_res_2687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_as_2680_, v_sz_boxed_2685_, v_i_boxed_2686_, v_b_2683_);
lean_dec_ref(v_as_2680_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7(lean_object* v_t_2688_, lean_object* v_init_2689_){
_start:
{
lean_object* v_root_2691_; lean_object* v_tail_2692_; lean_object* v___x_2693_; 
v_root_2691_ = lean_ctor_get(v_t_2688_, 0);
v_tail_2692_ = lean_ctor_get(v_t_2688_, 1);
v___x_2693_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2689_, v_root_2691_, v_init_2689_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2730_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2696_ = v___x_2693_;
v_isShared_2697_ = v_isSharedCheck_2730_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2693_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2730_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
if (lean_obj_tag(v_a_2694_) == 0)
{
lean_object* v_a_2698_; lean_object* v___x_2700_; 
v_a_2698_ = lean_ctor_get(v_a_2694_, 0);
lean_inc(v_a_2698_);
lean_dec_ref(v_a_2694_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 0, v_a_2698_);
v___x_2700_ = v___x_2696_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2698_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
else
{
lean_object* v_a_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; size_t v_sz_2705_; size_t v___x_2706_; lean_object* v___x_2707_; 
lean_del_object(v___x_2696_);
v_a_2702_ = lean_ctor_get(v_a_2694_, 0);
lean_inc(v_a_2702_);
lean_dec_ref(v_a_2694_);
v___x_2703_ = lean_box(0);
v___x_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
lean_ctor_set(v___x_2704_, 1, v_a_2702_);
v_sz_2705_ = lean_array_size(v_tail_2692_);
v___x_2706_ = ((size_t)0ULL);
v___x_2707_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_tail_2692_, v_sz_2705_, v___x_2706_, v___x_2704_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2721_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2710_ = v___x_2707_;
v_isShared_2711_ = v_isSharedCheck_2721_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2707_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2721_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v_fst_2712_; 
v_fst_2712_ = lean_ctor_get(v_a_2708_, 0);
if (lean_obj_tag(v_fst_2712_) == 0)
{
lean_object* v_snd_2713_; lean_object* v___x_2715_; 
v_snd_2713_ = lean_ctor_get(v_a_2708_, 1);
lean_inc(v_snd_2713_);
lean_dec(v_a_2708_);
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 0, v_snd_2713_);
v___x_2715_ = v___x_2710_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_snd_2713_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
else
{
lean_object* v_val_2717_; lean_object* v___x_2719_; 
lean_inc_ref(v_fst_2712_);
lean_dec(v_a_2708_);
v_val_2717_ = lean_ctor_get(v_fst_2712_, 0);
lean_inc(v_val_2717_);
lean_dec_ref(v_fst_2712_);
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 0, v_val_2717_);
v___x_2719_ = v___x_2710_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_val_2717_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
v_a_2722_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___x_2707_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2707_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2722_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
}
}
else
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2738_; 
v_a_2731_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2733_ = v___x_2693_;
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2693_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2736_; 
if (v_isShared_2734_ == 0)
{
v___x_2736_ = v___x_2733_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_a_2731_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7___boxed(lean_object* v_t_2739_, lean_object* v_init_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_t_2739_, v_init_2740_);
lean_dec_ref(v_t_2739_);
return v_res_2742_;
}
}
static lean_object* _init_l_main___closed__3(void){
_start:
{
lean_object* v___x_2746_; 
v___x_2746_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_box(0), lean_box(0), lean_box(0));
return v___x_2746_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2747_ = l_Lean_instInhabitedClassState_default;
v___x_2748_ = lean_box(0);
v___x_2749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2748_);
lean_ctor_set(v___x_2749_, 1, v___x_2747_);
return v___x_2749_;
}
}
static lean_object* _init_l_main___closed__5(void){
_start:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2750_ = l_Lean_Meta_Match_Extension_instInhabitedState;
v___x_2751_ = lean_box(0);
v___x_2752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2751_);
lean_ctor_set(v___x_2752_, 1, v___x_2750_);
return v___x_2752_;
}
}
static lean_object* _init_l_main___closed__6(void){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2753_ = ((lean_object*)(l_main___closed__2));
v___x_2754_ = ((lean_object*)(l_main___closed__1));
v___x_2755_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_2754_, v___x_2753_);
return v___x_2755_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2756_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2757_ = lean_box(0);
v___x_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2757_);
lean_ctor_set(v___x_2758_, 1, v___x_2756_);
return v___x_2758_;
}
}
static lean_object* _init_l_main___closed__8(void){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_2760_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2759_);
return v___x_2760_;
}
}
static lean_object* _init_l_main___closed__9(void){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Array_instInhabited(lean_box(0));
return v___x_2761_;
}
}
static lean_object* _init_l_main___closed__14(void){
_start:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2769_ = l_Lean_Options_empty;
v___x_2770_ = l_Lean_Core_getMaxHeartbeats(v___x_2769_);
return v___x_2770_;
}
}
static lean_object* _init_l_main___closed__19(void){
_start:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2775_ = ((lean_object*)(l_main___closed__18));
v___x_2776_ = lean_unsigned_to_nat(27u);
v___x_2777_ = lean_unsigned_to_nat(144u);
v___x_2778_ = ((lean_object*)(l_main___closed__17));
v___x_2779_ = ((lean_object*)(l_main___closed__16));
v___x_2780_ = l_mkPanicMessageWithDecl(v___x_2779_, v___x_2778_, v___x_2777_, v___x_2776_, v___x_2775_);
return v___x_2780_;
}
}
static lean_object* _init_l_main___closed__21(void){
_start:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2782_ = ((lean_object*)(l_main___closed__18));
v___x_2783_ = lean_unsigned_to_nat(51u);
v___x_2784_ = lean_unsigned_to_nat(117u);
v___x_2785_ = ((lean_object*)(l_main___closed__17));
v___x_2786_ = ((lean_object*)(l_main___closed__16));
v___x_2787_ = l_mkPanicMessageWithDecl(v___x_2786_, v___x_2785_, v___x_2784_, v___x_2783_, v___x_2782_);
return v___x_2787_;
}
}
static lean_object* _init_l_main___closed__22(void){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2788_ = lean_unsigned_to_nat(1u);
v___x_2789_ = l_Lean_firstFrontendMacroScope;
v___x_2790_ = lean_nat_add(v___x_2789_, v___x_2788_);
return v___x_2790_;
}
}
static lean_object* _init_l_main___closed__26(void){
_start:
{
lean_object* v___x_2797_; uint64_t v___x_2798_; lean_object* v___x_2799_; 
v___x_2797_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2798_ = 0ULL;
v___x_2799_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2799_, 0, v___x_2797_);
lean_ctor_set_uint64(v___x_2799_, sizeof(void*)*1, v___x_2798_);
return v___x_2799_;
}
}
static lean_object* _init_l_main___closed__27(void){
_start:
{
lean_object* v___x_2800_; 
v___x_2800_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2800_;
}
}
static lean_object* _init_l_main___closed__28(void){
_start:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2801_ = lean_obj_once(&l_main___closed__27, &l_main___closed__27_once, _init_l_main___closed__27);
v___x_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
return v___x_2802_;
}
}
static lean_object* _init_l_main___closed__29(void){
_start:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2803_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_2804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2803_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
return v___x_2804_;
}
}
static lean_object* _init_l_main___closed__30(void){
_start:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2805_ = l_Lean_NameSet_empty;
v___x_2806_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2807_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2806_);
lean_ctor_set(v___x_2807_, 1, v___x_2806_);
lean_ctor_set(v___x_2807_, 2, v___x_2805_);
return v___x_2807_;
}
}
static lean_object* _init_l_main___closed__31(void){
_start:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; uint8_t v___x_2810_; lean_object* v___x_2811_; 
v___x_2808_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2809_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_2810_ = 1;
v___x_2811_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2811_, 0, v___x_2809_);
lean_ctor_set(v___x_2811_, 1, v___x_2809_);
lean_ctor_set(v___x_2811_, 2, v___x_2808_);
lean_ctor_set_uint8(v___x_2811_, sizeof(void*)*3, v___x_2810_);
return v___x_2811_;
}
}
static uint8_t _init_l_main___closed__36(void){
_start:
{
uint8_t v___x_2818_; uint8_t v___x_2819_; 
v___x_2818_ = 2;
v___x_2819_ = l_Lean_instOrdOLeanLevel_ord(v___x_2818_, v___x_2818_);
return v___x_2819_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = 1;
v___x_2821_ = lean_box_uint32(v___x_2820_);
return v___x_2821_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_2822_; lean_object* v___x_2823_; 
v___x_2822_ = 0;
v___x_2823_ = lean_box_uint32(v___x_2822_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_2824_){
_start:
{
if (lean_obj_tag(v_args_2824_) == 1)
{
lean_object* v_tail_2849_; 
v_tail_2849_ = lean_ctor_get(v_args_2824_, 1);
lean_inc(v_tail_2849_);
if (lean_obj_tag(v_tail_2849_) == 1)
{
lean_object* v_tail_2850_; 
v_tail_2850_ = lean_ctor_get(v_tail_2849_, 1);
lean_inc(v_tail_2850_);
if (lean_obj_tag(v_tail_2850_) == 1)
{
lean_object* v_head_2851_; lean_object* v_head_2852_; lean_object* v_head_2853_; lean_object* v_tail_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_3477_; 
v_head_2851_ = lean_ctor_get(v_args_2824_, 0);
lean_inc(v_head_2851_);
lean_dec_ref(v_args_2824_);
v_head_2852_ = lean_ctor_get(v_tail_2849_, 0);
lean_inc(v_head_2852_);
lean_dec_ref(v_tail_2849_);
v_head_2853_ = lean_ctor_get(v_tail_2850_, 0);
v_tail_2854_ = lean_ctor_get(v_tail_2850_, 1);
v_isSharedCheck_3477_ = !lean_is_exclusive(v_tail_2850_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_2856_ = v_tail_2850_;
v_isShared_2857_ = v_isSharedCheck_3477_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_tail_2854_);
lean_inc(v_head_2853_);
lean_dec(v_tail_2850_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_3477_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2858_; 
v___x_2858_ = l_Lean_ModuleSetup_load(v_head_2851_);
lean_dec(v_head_2851_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v_a_2859_; lean_object* v_name_2860_; lean_object* v_options_2861_; uint8_t v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2866_; 
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_a_2859_);
lean_dec_ref(v___x_2858_);
v_name_2860_ = lean_ctor_get(v_a_2859_, 0);
lean_inc(v_name_2860_);
v_options_2861_ = lean_ctor_get(v_a_2859_, 6);
lean_inc(v_options_2861_);
lean_dec(v_a_2859_);
v___x_2862_ = 0;
v___x_2863_ = l_Lean_LeanOptions_toOptions(v_options_2861_);
v___x_2864_ = lean_box(v___x_2862_);
if (v_isShared_2857_ == 0)
{
lean_ctor_set_tag(v___x_2856_, 0);
lean_ctor_set(v___x_2856_, 1, v___x_2863_);
lean_ctor_set(v___x_2856_, 0, v___x_2864_);
v___x_2866_ = v___x_2856_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_2864_);
lean_ctor_set(v_reuseFailAlloc_3468_, 1, v___x_2863_);
v___x_2866_ = v_reuseFailAlloc_3468_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
lean_object* v___x_2867_; 
v___x_2867_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_tail_2854_, v___x_2866_);
lean_dec(v_tail_2854_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; lean_object* v___x_2869_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_a_2868_);
lean_dec_ref(v___x_2867_);
v___x_2869_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref(v___x_2869_);
v___x_2871_ = lean_box(0);
v___x_2872_ = l_Lean_initSearchPath(v_a_2870_, v___x_2871_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_fst_2873_; lean_object* v_snd_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_3443_; 
lean_dec_ref(v___x_2872_);
v_fst_2873_ = lean_ctor_get(v_a_2868_, 0);
v_snd_2874_ = lean_ctor_get(v_a_2868_, 1);
v_isSharedCheck_3443_ = !lean_is_exclusive(v_a_2868_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_2876_ = v_a_2868_;
v_isShared_2877_ = v_isSharedCheck_3443_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_snd_2874_);
lean_inc(v_fst_2873_);
lean_dec(v_a_2868_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_3443_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; uint8_t v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; uint8_t v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; uint8_t v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v_nextMacroScope_3040_; lean_object* v_ngen_3041_; lean_object* v_auxDeclNGen_3042_; lean_object* v_traceState_3043_; lean_object* v_messages_3044_; lean_object* v_infoState_3045_; lean_object* v_snapshotTasks_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; uint8_t v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; uint8_t v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; uint8_t v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; uint8_t v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; uint8_t v___y_3161_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; uint8_t v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; uint8_t v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; uint8_t v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; uint8_t v___y_3333_; lean_object* v___y_3334_; lean_object* v___x_3344_; lean_object* v___x_3345_; uint8_t v___x_3346_; uint8_t v___y_3348_; uint8_t v___x_3442_; 
v___x_2878_ = lean_obj_once(&l_main___closed__3, &l_main___closed__3_once, _init_l_main___closed__3);
v___x_2879_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2880_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_2881_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2882_ = lean_obj_once(&l_main___closed__8, &l_main___closed__8_once, _init_l_main___closed__8);
v___x_2883_ = lean_obj_once(&l_main___closed__9, &l_main___closed__9_once, _init_l_main___closed__9);
v___x_2884_ = lean_box(1);
v___x_2885_ = ((lean_object*)(l_main___closed__10));
v___x_2886_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_2887_ = 1;
v___x_2888_ = l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(v_snd_2874_, v___x_2886_, v___x_2887_);
v___x_2889_ = l_Lean_maxHeartbeats;
v___x_2890_ = lean_unsigned_to_nat(0u);
v___x_2891_ = l_Lean_Option_set___at___00main_spec__3(v___x_2888_, v___x_2889_, v___x_2890_);
v___x_3181_ = ((lean_object*)(l_main___closed__20));
lean_inc(v_name_2860_);
v___x_3182_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3182_, 0, v_name_2860_);
lean_ctor_set_uint8(v___x_3182_, sizeof(void*)*1, v___x_2887_);
lean_ctor_set_uint8(v___x_3182_, sizeof(void*)*1 + 1, v___x_2887_);
lean_ctor_set_uint8(v___x_3182_, sizeof(void*)*1 + 2, v___x_2887_);
v___x_3183_ = lean_unsigned_to_nat(1u);
v___x_3344_ = lean_mk_empty_array_with_capacity(v___x_3183_);
v___x_3345_ = lean_array_push(v___x_3344_, v___x_3182_);
v___x_3346_ = 2;
v___x_3442_ = lean_uint8_once(&l_main___closed__36, &l_main___closed__36_once, _init_l_main___closed__36);
if (v___x_3442_ == 0)
{
v___y_3348_ = v___x_2887_;
goto v___jp_3347_;
}
else
{
v___y_3348_ = v___x_2862_;
goto v___jp_3347_;
}
v___jp_2892_:
{
lean_object* v___x_2912_; lean_object* v_messages_2913_; lean_object* v_env_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_3015_; 
v___x_2912_ = lean_st_ref_get(v___y_2911_);
lean_dec(v___y_2911_);
v_messages_2913_ = lean_ctor_get(v___x_2912_, 6);
v_env_2914_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_3015_ == 0)
{
lean_object* v_unused_3016_; lean_object* v_unused_3017_; lean_object* v_unused_3018_; lean_object* v_unused_3019_; lean_object* v_unused_3020_; lean_object* v_unused_3021_; lean_object* v_unused_3022_; 
v_unused_3016_ = lean_ctor_get(v___x_2912_, 8);
lean_dec(v_unused_3016_);
v_unused_3017_ = lean_ctor_get(v___x_2912_, 7);
lean_dec(v_unused_3017_);
v_unused_3018_ = lean_ctor_get(v___x_2912_, 5);
lean_dec(v_unused_3018_);
v_unused_3019_ = lean_ctor_get(v___x_2912_, 4);
lean_dec(v_unused_3019_);
v_unused_3020_ = lean_ctor_get(v___x_2912_, 3);
lean_dec(v_unused_3020_);
v_unused_3021_ = lean_ctor_get(v___x_2912_, 2);
lean_dec(v_unused_3021_);
v_unused_3022_ = lean_ctor_get(v___x_2912_, 1);
lean_dec(v_unused_3022_);
v___x_2916_ = v___x_2912_;
v_isShared_2917_ = v_isSharedCheck_3015_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_messages_2913_);
lean_inc(v_env_2914_);
lean_dec(v___x_2912_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_3015_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v_unreported_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
v_unreported_2918_ = lean_ctor_get(v_messages_2913_, 1);
v___x_2919_ = lean_box(0);
v___x_2920_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_unreported_2918_, v___x_2919_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_3005_; 
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_3005_ == 0)
{
lean_object* v_unused_3006_; 
v_unused_3006_ = lean_ctor_get(v___x_2920_, 0);
lean_dec(v_unused_3006_);
v___x_2922_ = v___x_2920_;
v_isShared_2923_ = v_isSharedCheck_3005_;
goto v_resetjp_2921_;
}
else
{
lean_dec(v___x_2920_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_3005_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
uint8_t v___x_2924_; 
v___x_2924_ = l_Lean_MessageLog_hasErrors(v_messages_2913_);
lean_dec_ref(v_messages_2913_);
if (v___x_2924_ == 0)
{
lean_object* v___x_2925_; 
lean_del_object(v___x_2922_);
lean_inc_ref(v_env_2914_);
v___x_2925_ = l___private_LeanIR_0__mkIRData(v_env_2914_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_a_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc(v_a_2926_);
lean_dec_ref(v___x_2925_);
v___x_2927_ = l_Lean_Environment_mainModule(v_env_2914_);
v___x_2928_ = ((lean_object*)(l_main___closed__12));
v___x_2929_ = l_Lean_Name_append(v___x_2927_, v___x_2928_);
lean_inc(v_head_2852_);
v___x_2930_ = l_Lean_saveModuleData(v_head_2852_, v___x_2929_, v_a_2926_);
lean_dec(v___x_2929_);
if (lean_obj_tag(v___x_2930_) == 0)
{
uint8_t v___x_2931_; lean_object* v___x_2932_; 
lean_dec_ref(v___x_2930_);
v___x_2931_ = 1;
v___x_2932_ = lean_io_prim_handle_mk(v_head_2853_, v___x_2931_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2938_; 
lean_dec(v_head_2853_);
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
lean_inc(v_a_2933_);
lean_dec_ref(v___x_2932_);
v___x_2934_ = ((lean_object*)(l_main___closed__13));
v___x_2935_ = l_Lean_Options_empty;
v___x_2936_ = lean_obj_once(&l_main___closed__14, &l_main___closed__14_once, _init_l_main___closed__14);
lean_inc_ref(v___y_2903_);
lean_inc_ref(v___y_2905_);
lean_inc_ref(v___y_2908_);
lean_inc_ref(v___y_2902_);
lean_inc_ref(v___y_2909_);
lean_inc_ref(v___y_2904_);
lean_inc(v___y_2906_);
lean_inc_ref(v_env_2914_);
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 8, v___y_2903_);
lean_ctor_set(v___x_2916_, 7, v___y_2905_);
lean_ctor_set(v___x_2916_, 6, v___y_2908_);
lean_ctor_set(v___x_2916_, 5, v___y_2902_);
lean_ctor_set(v___x_2916_, 4, v___y_2909_);
lean_ctor_set(v___x_2916_, 3, v___y_2910_);
lean_ctor_set(v___x_2916_, 2, v___y_2904_);
lean_ctor_set(v___x_2916_, 1, v___y_2906_);
v___x_2938_ = v___x_2916_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_env_2914_);
lean_ctor_set(v_reuseFailAlloc_2962_, 1, v___y_2906_);
lean_ctor_set(v_reuseFailAlloc_2962_, 2, v___y_2904_);
lean_ctor_set(v_reuseFailAlloc_2962_, 3, v___y_2910_);
lean_ctor_set(v_reuseFailAlloc_2962_, 4, v___y_2909_);
lean_ctor_set(v_reuseFailAlloc_2962_, 5, v___y_2902_);
lean_ctor_set(v_reuseFailAlloc_2962_, 6, v___y_2908_);
lean_ctor_set(v_reuseFailAlloc_2962_, 7, v___y_2905_);
lean_ctor_set(v_reuseFailAlloc_2962_, 8, v___y_2903_);
v___x_2938_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___f_2941_; lean_object* v___x_2942_; 
v___x_2939_ = lean_box(v___x_2862_);
v___x_2940_ = lean_box(v___y_2896_);
lean_inc(v___y_2898_);
lean_inc(v___y_2895_);
lean_inc(v___y_2901_);
lean_inc_ref(v___y_2897_);
lean_inc_ref(v___y_2893_);
lean_inc(v___y_2894_);
v___f_2941_ = lean_alloc_closure((void*)(l_main___lam__1___boxed), 18, 17);
lean_closure_set(v___f_2941_, 0, v___x_2938_);
lean_closure_set(v___f_2941_, 1, v___y_2894_);
lean_closure_set(v___f_2941_, 2, v___x_2935_);
lean_closure_set(v___f_2941_, 3, v_name_2860_);
lean_closure_set(v___f_2941_, 4, v_a_2933_);
lean_closure_set(v___f_2941_, 5, v___y_2893_);
lean_closure_set(v___f_2941_, 6, v_head_2852_);
lean_closure_set(v___f_2941_, 7, v___y_2897_);
lean_closure_set(v___f_2941_, 8, v___x_2890_);
lean_closure_set(v___f_2941_, 9, v___y_2901_);
lean_closure_set(v___f_2941_, 10, v___y_2899_);
lean_closure_set(v___f_2941_, 11, v___y_2900_);
lean_closure_set(v___f_2941_, 12, v___x_2936_);
lean_closure_set(v___f_2941_, 13, v___y_2895_);
lean_closure_set(v___f_2941_, 14, v___y_2898_);
lean_closure_set(v___f_2941_, 15, v___x_2939_);
lean_closure_set(v___f_2941_, 16, v___x_2940_);
v___x_2942_ = l_Lean_profileitIOUnsafe___redArg(v___x_2934_, v___x_2891_, v___f_2941_, v___y_2907_);
lean_dec_ref(v___x_2891_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v___x_2943_; uint8_t v___x_2944_; 
lean_dec_ref(v___x_2942_);
v___x_2943_ = lean_display_cumulative_profiling_times();
v___x_2944_ = lean_unbox(v_fst_2873_);
lean_dec(v_fst_2873_);
if (v___x_2944_ == 0)
{
lean_dec_ref(v_env_2914_);
goto v___jp_2846_;
}
else
{
lean_object* v___x_2945_; 
v___x_2945_ = l_Lean_Environment_displayStats(v_env_2914_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_dec_ref(v___x_2945_);
goto v___jp_2846_;
}
else
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2953_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2948_ = v___x_2945_;
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2945_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2951_; 
if (v_isShared_2949_ == 0)
{
v___x_2951_ = v___x_2948_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2946_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
}
}
else
{
lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2961_; 
lean_dec_ref(v_env_2914_);
lean_dec(v_fst_2873_);
v_a_2954_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2956_ = v___x_2942_;
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2942_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2957_ == 0)
{
v___x_2959_ = v___x_2956_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
}
}
else
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
lean_dec_ref(v___x_2932_);
lean_del_object(v___x_2916_);
lean_dec_ref(v_env_2914_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2907_);
lean_dec(v___y_2900_);
lean_dec(v___y_2899_);
lean_dec_ref(v___x_2891_);
lean_dec(v_fst_2873_);
lean_dec(v_name_2860_);
lean_dec(v_head_2852_);
v___x_2963_ = ((lean_object*)(l_main___closed__15));
v___x_2964_ = lean_string_append(v___x_2963_, v_head_2853_);
lean_dec(v_head_2853_);
v___x_2965_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__5));
v___x_2966_ = lean_string_append(v___x_2964_, v___x_2965_);
v___x_2967_ = l_IO_eprintln___at___00main_spec__6(v___x_2966_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2975_; 
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2975_ == 0)
{
lean_object* v_unused_2976_; 
v_unused_2976_ = lean_ctor_get(v___x_2967_, 0);
lean_dec(v_unused_2976_);
v___x_2969_ = v___x_2967_;
v_isShared_2970_ = v_isSharedCheck_2975_;
goto v_resetjp_2968_;
}
else
{
lean_dec(v___x_2967_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2975_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2971_; lean_object* v___x_2973_; 
v___x_2971_ = l_main___boxed__const__1;
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 0, v___x_2971_);
v___x_2973_ = v___x_2969_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v___x_2971_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
else
{
lean_object* v_a_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2984_; 
v_a_2977_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2979_ = v___x_2967_;
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_a_2977_);
lean_dec(v___x_2967_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2982_; 
if (v_isShared_2980_ == 0)
{
v___x_2982_ = v___x_2979_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_a_2977_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
}
}
else
{
lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2992_; 
lean_del_object(v___x_2916_);
lean_dec_ref(v_env_2914_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2907_);
lean_dec(v___y_2900_);
lean_dec(v___y_2899_);
lean_dec_ref(v___x_2891_);
lean_dec(v_fst_2873_);
lean_dec(v_name_2860_);
lean_dec(v_head_2853_);
lean_dec(v_head_2852_);
v_a_2985_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2987_ = v___x_2930_;
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_dec(v___x_2930_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2990_; 
if (v_isShared_2988_ == 0)
{
v___x_2990_ = v___x_2987_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_a_2985_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
}
else
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
lean_del_object(v___x_2916_);
lean_dec_ref(v_env_2914_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2907_);
lean_dec(v___y_2900_);
lean_dec(v___y_2899_);
lean_dec_ref(v___x_2891_);
lean_dec(v_fst_2873_);
lean_dec(v_name_2860_);
lean_dec(v_head_2853_);
lean_dec(v_head_2852_);
v_a_2993_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v___x_2925_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2925_);
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
else
{
lean_object* v___x_3001_; lean_object* v___x_3003_; 
lean_del_object(v___x_2916_);
lean_dec_ref(v_env_2914_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2907_);
lean_dec(v___y_2900_);
lean_dec(v___y_2899_);
lean_dec_ref(v___x_2891_);
lean_dec(v_fst_2873_);
lean_dec(v_name_2860_);
lean_dec(v_head_2853_);
lean_dec(v_head_2852_);
v___x_3001_ = l_main___boxed__const__1;
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 0, v___x_3001_);
v___x_3003_ = v___x_2922_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v___x_3001_);
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
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
lean_del_object(v___x_2916_);
lean_dec_ref(v_env_2914_);
lean_dec_ref(v_messages_2913_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2907_);
lean_dec(v___y_2900_);
lean_dec(v___y_2899_);
lean_dec_ref(v___x_2891_);
lean_dec(v_fst_2873_);
lean_dec(v_name_2860_);
lean_dec(v_head_2853_);
lean_dec(v_head_2852_);
v_a_3007_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_2920_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_2920_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
}
v___jp_3023_:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; size_t v_sz_3057_; size_t v___x_3058_; lean_object* v___x_3059_; 
lean_inc_ref(v___y_3033_);
v___x_3054_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3054_, 0, v___y_3053_);
lean_ctor_set(v___x_3054_, 1, v_nextMacroScope_3040_);
lean_ctor_set(v___x_3054_, 2, v_ngen_3041_);
lean_ctor_set(v___x_3054_, 3, v_auxDeclNGen_3042_);
lean_ctor_set(v___x_3054_, 4, v_traceState_3043_);
lean_ctor_set(v___x_3054_, 5, v___y_3033_);
lean_ctor_set(v___x_3054_, 6, v_messages_3044_);
lean_ctor_set(v___x_3054_, 7, v_infoState_3045_);
lean_ctor_set(v___x_3054_, 8, v_snapshotTasks_3046_);
v___x_3055_ = lean_st_ref_set(v___y_3050_, v___x_3054_);
v___x_3056_ = lean_box(0);
v_sz_3057_ = lean_array_size(v___y_3051_);
v___x_3058_ = ((size_t)0ULL);
v___x_3059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v___y_3051_, v_sz_3057_, v___x_3058_, v___x_3056_, v___y_3035_, v___y_3050_);
lean_dec_ref(v___y_3051_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_dec_ref(v___x_3059_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3035_);
v___y_2893_ = v___y_3024_;
v___y_2894_ = v___y_3025_;
v___y_2895_ = v___y_3026_;
v___y_2896_ = v___y_3027_;
v___y_2897_ = v___y_3028_;
v___y_2898_ = v___y_3030_;
v___y_2899_ = v___y_3029_;
v___y_2900_ = v___y_3031_;
v___y_2901_ = v___y_3032_;
v___y_2902_ = v___y_3033_;
v___y_2903_ = v___y_3047_;
v___y_2904_ = v___y_3034_;
v___y_2905_ = v___y_3048_;
v___y_2906_ = v___y_3036_;
v___y_2907_ = v___y_3049_;
v___y_2908_ = v___y_3037_;
v___y_2909_ = v___y_3038_;
v___y_2910_ = v___y_3039_;
v___y_2911_ = v___y_3052_;
goto v___jp_2892_;
}
else
{
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_dec_ref(v___x_3059_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3035_);
v___y_2893_ = v___y_3024_;
v___y_2894_ = v___y_3025_;
v___y_2895_ = v___y_3026_;
v___y_2896_ = v___y_3027_;
v___y_2897_ = v___y_3028_;
v___y_2898_ = v___y_3030_;
v___y_2899_ = v___y_3029_;
v___y_2900_ = v___y_3031_;
v___y_2901_ = v___y_3032_;
v___y_2902_ = v___y_3033_;
v___y_2903_ = v___y_3047_;
v___y_2904_ = v___y_3034_;
v___y_2905_ = v___y_3048_;
v___y_2906_ = v___y_3036_;
v___y_2907_ = v___y_3049_;
v___y_2908_ = v___y_3037_;
v___y_2909_ = v___y_3038_;
v___y_2910_ = v___y_3039_;
v___y_2911_ = v___y_3052_;
goto v___jp_2892_;
}
else
{
lean_object* v_a_3060_; uint8_t v___x_3061_; 
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_a_3060_);
lean_dec_ref(v___x_3059_);
v___x_3061_ = l_Lean_Exception_isInterrupt(v_a_3060_);
if (v___x_3061_ == 0)
{
lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3062_ = l_Lean_Exception_toMessageData(v_a_3060_);
v___x_3063_ = l_Lean_logError___at___00main_spec__14(v___x_3062_, v___y_3035_, v___y_3050_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3035_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_dec_ref(v___x_3063_);
v___y_2893_ = v___y_3024_;
v___y_2894_ = v___y_3025_;
v___y_2895_ = v___y_3026_;
v___y_2896_ = v___y_3027_;
v___y_2897_ = v___y_3028_;
v___y_2898_ = v___y_3030_;
v___y_2899_ = v___y_3029_;
v___y_2900_ = v___y_3031_;
v___y_2901_ = v___y_3032_;
v___y_2902_ = v___y_3033_;
v___y_2903_ = v___y_3047_;
v___y_2904_ = v___y_3034_;
v___y_2905_ = v___y_3048_;
v___y_2906_ = v___y_3036_;
v___y_2907_ = v___y_3049_;
v___y_2908_ = v___y_3037_;
v___y_2909_ = v___y_3038_;
v___y_2910_ = v___y_3039_;
v___y_2911_ = v___y_3052_;
goto v___jp_2892_;
}
else
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
lean_dec_ref(v___x_3063_);
lean_dec(v___y_3052_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3031_);
lean_dec(v___y_3029_);
lean_dec_ref(v___x_2891_);
lean_dec(v_fst_2873_);
lean_dec(v_name_2860_);
lean_dec(v_head_2853_);
lean_dec(v_head_2852_);
v___x_3064_ = lean_obj_once(&l_main___closed__19, &l_main___closed__19_once, _init_l_main___closed__19);
v___x_3065_ = l_panic___at___00main_spec__5(v___x_3064_);
return v___x_3065_;
}
}
else
{
lean_dec(v_a_3060_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3035_);
v___y_2893_ = v___y_3024_;
v___y_2894_ = v___y_3025_;
v___y_2895_ = v___y_3026_;
v___y_2896_ = v___y_3027_;
v___y_2897_ = v___y_3028_;
v___y_2898_ = v___y_3030_;
v___y_2899_ = v___y_3029_;
v___y_2900_ = v___y_3031_;
v___y_2901_ = v___y_3032_;
v___y_2902_ = v___y_3033_;
v___y_2903_ = v___y_3047_;
v___y_2904_ = v___y_3034_;
v___y_2905_ = v___y_3048_;
v___y_2906_ = v___y_3036_;
v___y_2907_ = v___y_3049_;
v___y_2908_ = v___y_3037_;
v___y_2909_ = v___y_3038_;
v___y_2910_ = v___y_3039_;
v___y_2911_ = v___y_3052_;
goto v___jp_2892_;
}
}
}
}
v___jp_3066_:
{
lean_object* v___x_3091_; lean_object* v_fileName_3092_; lean_object* v_fileMap_3093_; lean_object* v_currRecDepth_3094_; lean_object* v_ref_3095_; lean_object* v_currNamespace_3096_; lean_object* v_openDecls_3097_; lean_object* v_initHeartbeats_3098_; lean_object* v_maxHeartbeats_3099_; lean_object* v_quotContext_3100_; lean_object* v_currMacroScope_3101_; lean_object* v_cancelTk_x3f_3102_; uint8_t v_suppressElabErrors_3103_; lean_object* v_inheritedTraceOptions_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3134_; 
v___x_3091_ = lean_st_ref_take(v___y_3090_);
v_fileName_3092_ = lean_ctor_get(v___y_3089_, 0);
v_fileMap_3093_ = lean_ctor_get(v___y_3089_, 1);
v_currRecDepth_3094_ = lean_ctor_get(v___y_3089_, 3);
v_ref_3095_ = lean_ctor_get(v___y_3089_, 5);
v_currNamespace_3096_ = lean_ctor_get(v___y_3089_, 6);
v_openDecls_3097_ = lean_ctor_get(v___y_3089_, 7);
v_initHeartbeats_3098_ = lean_ctor_get(v___y_3089_, 8);
v_maxHeartbeats_3099_ = lean_ctor_get(v___y_3089_, 9);
v_quotContext_3100_ = lean_ctor_get(v___y_3089_, 10);
v_currMacroScope_3101_ = lean_ctor_get(v___y_3089_, 11);
v_cancelTk_x3f_3102_ = lean_ctor_get(v___y_3089_, 12);
v_suppressElabErrors_3103_ = lean_ctor_get_uint8(v___y_3089_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3104_ = lean_ctor_get(v___y_3089_, 13);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___y_3089_);
if (v_isSharedCheck_3134_ == 0)
{
lean_object* v_unused_3135_; lean_object* v_unused_3136_; 
v_unused_3135_ = lean_ctor_get(v___y_3089_, 4);
lean_dec(v_unused_3135_);
v_unused_3136_ = lean_ctor_get(v___y_3089_, 2);
lean_dec(v_unused_3136_);
v___x_3106_ = v___y_3089_;
v_isShared_3107_ = v_isSharedCheck_3134_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_inheritedTraceOptions_3104_);
lean_inc(v_cancelTk_x3f_3102_);
lean_inc(v_currMacroScope_3101_);
lean_inc(v_quotContext_3100_);
lean_inc(v_maxHeartbeats_3099_);
lean_inc(v_initHeartbeats_3098_);
lean_inc(v_openDecls_3097_);
lean_inc(v_currNamespace_3096_);
lean_inc(v_ref_3095_);
lean_inc(v_currRecDepth_3094_);
lean_inc(v_fileMap_3093_);
lean_inc(v_fileName_3092_);
lean_dec(v___y_3089_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3134_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v_env_3108_; lean_object* v_nextMacroScope_3109_; lean_object* v_ngen_3110_; lean_object* v_auxDeclNGen_3111_; lean_object* v_traceState_3112_; lean_object* v_messages_3113_; lean_object* v_infoState_3114_; lean_object* v_snapshotTasks_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3119_; 
v_env_3108_ = lean_ctor_get(v___x_3091_, 0);
lean_inc_ref(v_env_3108_);
v_nextMacroScope_3109_ = lean_ctor_get(v___x_3091_, 1);
lean_inc(v_nextMacroScope_3109_);
v_ngen_3110_ = lean_ctor_get(v___x_3091_, 2);
lean_inc_ref(v_ngen_3110_);
v_auxDeclNGen_3111_ = lean_ctor_get(v___x_3091_, 3);
lean_inc_ref(v_auxDeclNGen_3111_);
v_traceState_3112_ = lean_ctor_get(v___x_3091_, 4);
lean_inc_ref(v_traceState_3112_);
v_messages_3113_ = lean_ctor_get(v___x_3091_, 6);
lean_inc_ref(v_messages_3113_);
v_infoState_3114_ = lean_ctor_get(v___x_3091_, 7);
lean_inc_ref(v_infoState_3114_);
v_snapshotTasks_3115_ = lean_ctor_get(v___x_3091_, 8);
lean_inc_ref(v_snapshotTasks_3115_);
lean_dec(v___x_3091_);
v___x_3116_ = l_Lean_maxRecDepth;
v___x_3117_ = l_Lean_Option_get___at___00main_spec__9(v___x_2891_, v___x_3116_);
lean_inc_ref(v___x_2891_);
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 4, v___x_3117_);
lean_ctor_set(v___x_3106_, 2, v___x_2891_);
v___x_3119_ = v___x_3106_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_fileName_3092_);
lean_ctor_set(v_reuseFailAlloc_3133_, 1, v_fileMap_3093_);
lean_ctor_set(v_reuseFailAlloc_3133_, 2, v___x_2891_);
lean_ctor_set(v_reuseFailAlloc_3133_, 3, v_currRecDepth_3094_);
lean_ctor_set(v_reuseFailAlloc_3133_, 4, v___x_3117_);
lean_ctor_set(v_reuseFailAlloc_3133_, 5, v_ref_3095_);
lean_ctor_set(v_reuseFailAlloc_3133_, 6, v_currNamespace_3096_);
lean_ctor_set(v_reuseFailAlloc_3133_, 7, v_openDecls_3097_);
lean_ctor_set(v_reuseFailAlloc_3133_, 8, v_initHeartbeats_3098_);
lean_ctor_set(v_reuseFailAlloc_3133_, 9, v_maxHeartbeats_3099_);
lean_ctor_set(v_reuseFailAlloc_3133_, 10, v_quotContext_3100_);
lean_ctor_set(v_reuseFailAlloc_3133_, 11, v_currMacroScope_3101_);
lean_ctor_set(v_reuseFailAlloc_3133_, 12, v_cancelTk_x3f_3102_);
lean_ctor_set(v_reuseFailAlloc_3133_, 13, v_inheritedTraceOptions_3104_);
lean_ctor_set_uint8(v_reuseFailAlloc_3133_, sizeof(void*)*14 + 1, v_suppressElabErrors_3103_);
v___x_3119_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
lean_object* v___x_3120_; uint8_t v___x_3121_; 
lean_ctor_set_uint8(v___x_3119_, sizeof(void*)*14, v___y_3084_);
v___x_3120_ = lean_array_get_size(v___y_3087_);
v___x_3121_ = lean_nat_dec_lt(v___x_2890_, v___x_3120_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; 
lean_inc_ref(v___y_3083_);
v___x_3122_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3083_, v_env_3108_, v___x_2884_);
v___y_3024_ = v___y_3067_;
v___y_3025_ = v___y_3068_;
v___y_3026_ = v___y_3069_;
v___y_3027_ = v___y_3070_;
v___y_3028_ = v___y_3071_;
v___y_3029_ = v___y_3073_;
v___y_3030_ = v___y_3072_;
v___y_3031_ = v___y_3074_;
v___y_3032_ = v___y_3075_;
v___y_3033_ = v___y_3076_;
v___y_3034_ = v___y_3077_;
v___y_3035_ = v___x_3119_;
v___y_3036_ = v___y_3078_;
v___y_3037_ = v___y_3079_;
v___y_3038_ = v___y_3080_;
v___y_3039_ = v___y_3081_;
v_nextMacroScope_3040_ = v_nextMacroScope_3109_;
v_ngen_3041_ = v_ngen_3110_;
v_auxDeclNGen_3042_ = v_auxDeclNGen_3111_;
v_traceState_3043_ = v_traceState_3112_;
v_messages_3044_ = v_messages_3113_;
v_infoState_3045_ = v_infoState_3114_;
v_snapshotTasks_3046_ = v_snapshotTasks_3115_;
v___y_3047_ = v___y_3082_;
v___y_3048_ = v___y_3085_;
v___y_3049_ = v___y_3086_;
v___y_3050_ = v___y_3090_;
v___y_3051_ = v___y_3087_;
v___y_3052_ = v___y_3088_;
v___y_3053_ = v___x_3122_;
goto v___jp_3023_;
}
else
{
uint8_t v___x_3123_; 
v___x_3123_ = lean_nat_dec_le(v___x_3120_, v___x_3120_);
if (v___x_3123_ == 0)
{
if (v___x_3121_ == 0)
{
lean_object* v___x_3124_; 
lean_inc_ref(v___y_3083_);
v___x_3124_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3083_, v_env_3108_, v___x_2884_);
v___y_3024_ = v___y_3067_;
v___y_3025_ = v___y_3068_;
v___y_3026_ = v___y_3069_;
v___y_3027_ = v___y_3070_;
v___y_3028_ = v___y_3071_;
v___y_3029_ = v___y_3073_;
v___y_3030_ = v___y_3072_;
v___y_3031_ = v___y_3074_;
v___y_3032_ = v___y_3075_;
v___y_3033_ = v___y_3076_;
v___y_3034_ = v___y_3077_;
v___y_3035_ = v___x_3119_;
v___y_3036_ = v___y_3078_;
v___y_3037_ = v___y_3079_;
v___y_3038_ = v___y_3080_;
v___y_3039_ = v___y_3081_;
v_nextMacroScope_3040_ = v_nextMacroScope_3109_;
v_ngen_3041_ = v_ngen_3110_;
v_auxDeclNGen_3042_ = v_auxDeclNGen_3111_;
v_traceState_3043_ = v_traceState_3112_;
v_messages_3044_ = v_messages_3113_;
v_infoState_3045_ = v_infoState_3114_;
v_snapshotTasks_3046_ = v_snapshotTasks_3115_;
v___y_3047_ = v___y_3082_;
v___y_3048_ = v___y_3085_;
v___y_3049_ = v___y_3086_;
v___y_3050_ = v___y_3090_;
v___y_3051_ = v___y_3087_;
v___y_3052_ = v___y_3088_;
v___y_3053_ = v___x_3124_;
goto v___jp_3023_;
}
else
{
size_t v___x_3125_; size_t v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3125_ = ((size_t)0ULL);
v___x_3126_ = lean_usize_of_nat(v___x_3120_);
v___x_3127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3087_, v___x_3125_, v___x_3126_, v___x_2884_);
lean_inc_ref(v___y_3083_);
v___x_3128_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3083_, v_env_3108_, v___x_3127_);
v___y_3024_ = v___y_3067_;
v___y_3025_ = v___y_3068_;
v___y_3026_ = v___y_3069_;
v___y_3027_ = v___y_3070_;
v___y_3028_ = v___y_3071_;
v___y_3029_ = v___y_3073_;
v___y_3030_ = v___y_3072_;
v___y_3031_ = v___y_3074_;
v___y_3032_ = v___y_3075_;
v___y_3033_ = v___y_3076_;
v___y_3034_ = v___y_3077_;
v___y_3035_ = v___x_3119_;
v___y_3036_ = v___y_3078_;
v___y_3037_ = v___y_3079_;
v___y_3038_ = v___y_3080_;
v___y_3039_ = v___y_3081_;
v_nextMacroScope_3040_ = v_nextMacroScope_3109_;
v_ngen_3041_ = v_ngen_3110_;
v_auxDeclNGen_3042_ = v_auxDeclNGen_3111_;
v_traceState_3043_ = v_traceState_3112_;
v_messages_3044_ = v_messages_3113_;
v_infoState_3045_ = v_infoState_3114_;
v_snapshotTasks_3046_ = v_snapshotTasks_3115_;
v___y_3047_ = v___y_3082_;
v___y_3048_ = v___y_3085_;
v___y_3049_ = v___y_3086_;
v___y_3050_ = v___y_3090_;
v___y_3051_ = v___y_3087_;
v___y_3052_ = v___y_3088_;
v___y_3053_ = v___x_3128_;
goto v___jp_3023_;
}
}
else
{
size_t v___x_3129_; size_t v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3129_ = ((size_t)0ULL);
v___x_3130_ = lean_usize_of_nat(v___x_3120_);
v___x_3131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3087_, v___x_3129_, v___x_3130_, v___x_2884_);
lean_inc_ref(v___y_3083_);
v___x_3132_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3083_, v_env_3108_, v___x_3131_);
v___y_3024_ = v___y_3067_;
v___y_3025_ = v___y_3068_;
v___y_3026_ = v___y_3069_;
v___y_3027_ = v___y_3070_;
v___y_3028_ = v___y_3071_;
v___y_3029_ = v___y_3073_;
v___y_3030_ = v___y_3072_;
v___y_3031_ = v___y_3074_;
v___y_3032_ = v___y_3075_;
v___y_3033_ = v___y_3076_;
v___y_3034_ = v___y_3077_;
v___y_3035_ = v___x_3119_;
v___y_3036_ = v___y_3078_;
v___y_3037_ = v___y_3079_;
v___y_3038_ = v___y_3080_;
v___y_3039_ = v___y_3081_;
v_nextMacroScope_3040_ = v_nextMacroScope_3109_;
v_ngen_3041_ = v_ngen_3110_;
v_auxDeclNGen_3042_ = v_auxDeclNGen_3111_;
v_traceState_3043_ = v_traceState_3112_;
v_messages_3044_ = v_messages_3113_;
v_infoState_3045_ = v_infoState_3114_;
v_snapshotTasks_3046_ = v_snapshotTasks_3115_;
v___y_3047_ = v___y_3082_;
v___y_3048_ = v___y_3085_;
v___y_3049_ = v___y_3086_;
v___y_3050_ = v___y_3090_;
v___y_3051_ = v___y_3087_;
v___y_3052_ = v___y_3088_;
v___y_3053_ = v___x_3132_;
goto v___jp_3023_;
}
}
}
}
}
v___jp_3137_:
{
if (v___y_3161_ == 0)
{
lean_object* v___x_3162_; lean_object* v_env_3163_; lean_object* v_nextMacroScope_3164_; lean_object* v_ngen_3165_; lean_object* v_auxDeclNGen_3166_; lean_object* v_traceState_3167_; lean_object* v_messages_3168_; lean_object* v_infoState_3169_; lean_object* v_snapshotTasks_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3179_; 
v___x_3162_ = lean_st_ref_take(v___y_3160_);
v_env_3163_ = lean_ctor_get(v___x_3162_, 0);
v_nextMacroScope_3164_ = lean_ctor_get(v___x_3162_, 1);
v_ngen_3165_ = lean_ctor_get(v___x_3162_, 2);
v_auxDeclNGen_3166_ = lean_ctor_get(v___x_3162_, 3);
v_traceState_3167_ = lean_ctor_get(v___x_3162_, 4);
v_messages_3168_ = lean_ctor_get(v___x_3162_, 6);
v_infoState_3169_ = lean_ctor_get(v___x_3162_, 7);
v_snapshotTasks_3170_ = lean_ctor_get(v___x_3162_, 8);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3179_ == 0)
{
lean_object* v_unused_3180_; 
v_unused_3180_ = lean_ctor_get(v___x_3162_, 5);
lean_dec(v_unused_3180_);
v___x_3172_ = v___x_3162_;
v_isShared_3173_ = v_isSharedCheck_3179_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_snapshotTasks_3170_);
lean_inc(v_infoState_3169_);
lean_inc(v_messages_3168_);
lean_inc(v_traceState_3167_);
lean_inc(v_auxDeclNGen_3166_);
lean_inc(v_ngen_3165_);
lean_inc(v_nextMacroScope_3164_);
lean_inc(v_env_3163_);
lean_dec(v___x_3162_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3179_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3174_; lean_object* v___x_3176_; 
v___x_3174_ = l_Lean_Kernel_enableDiag(v_env_3163_, v___y_3156_);
lean_inc_ref(v___y_3147_);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 5, v___y_3147_);
lean_ctor_set(v___x_3172_, 0, v___x_3174_);
v___x_3176_ = v___x_3172_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v___x_3174_);
lean_ctor_set(v_reuseFailAlloc_3178_, 1, v_nextMacroScope_3164_);
lean_ctor_set(v_reuseFailAlloc_3178_, 2, v_ngen_3165_);
lean_ctor_set(v_reuseFailAlloc_3178_, 3, v_auxDeclNGen_3166_);
lean_ctor_set(v_reuseFailAlloc_3178_, 4, v_traceState_3167_);
lean_ctor_set(v_reuseFailAlloc_3178_, 5, v___y_3147_);
lean_ctor_set(v_reuseFailAlloc_3178_, 6, v_messages_3168_);
lean_ctor_set(v_reuseFailAlloc_3178_, 7, v_infoState_3169_);
lean_ctor_set(v_reuseFailAlloc_3178_, 8, v_snapshotTasks_3170_);
v___x_3176_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
lean_object* v___x_3177_; 
v___x_3177_ = lean_st_ref_set(v___y_3160_, v___x_3176_);
lean_inc(v___y_3160_);
v___y_3067_ = v___y_3138_;
v___y_3068_ = v___y_3139_;
v___y_3069_ = v___y_3140_;
v___y_3070_ = v___y_3141_;
v___y_3071_ = v___y_3142_;
v___y_3072_ = v___y_3144_;
v___y_3073_ = v___y_3143_;
v___y_3074_ = v___y_3145_;
v___y_3075_ = v___y_3146_;
v___y_3076_ = v___y_3147_;
v___y_3077_ = v___y_3149_;
v___y_3078_ = v___y_3150_;
v___y_3079_ = v___y_3151_;
v___y_3080_ = v___y_3152_;
v___y_3081_ = v___y_3153_;
v___y_3082_ = v___y_3154_;
v___y_3083_ = v___y_3155_;
v___y_3084_ = v___y_3156_;
v___y_3085_ = v___y_3157_;
v___y_3086_ = v___y_3158_;
v___y_3087_ = v___y_3159_;
v___y_3088_ = v___y_3160_;
v___y_3089_ = v___y_3148_;
v___y_3090_ = v___y_3160_;
goto v___jp_3066_;
}
}
}
else
{
lean_inc(v___y_3160_);
v___y_3067_ = v___y_3138_;
v___y_3068_ = v___y_3139_;
v___y_3069_ = v___y_3140_;
v___y_3070_ = v___y_3141_;
v___y_3071_ = v___y_3142_;
v___y_3072_ = v___y_3144_;
v___y_3073_ = v___y_3143_;
v___y_3074_ = v___y_3145_;
v___y_3075_ = v___y_3146_;
v___y_3076_ = v___y_3147_;
v___y_3077_ = v___y_3149_;
v___y_3078_ = v___y_3150_;
v___y_3079_ = v___y_3151_;
v___y_3080_ = v___y_3152_;
v___y_3081_ = v___y_3153_;
v___y_3082_ = v___y_3154_;
v___y_3083_ = v___y_3155_;
v___y_3084_ = v___y_3156_;
v___y_3085_ = v___y_3157_;
v___y_3086_ = v___y_3158_;
v___y_3087_ = v___y_3159_;
v___y_3088_ = v___y_3160_;
v___y_3089_ = v___y_3148_;
v___y_3090_ = v___y_3160_;
goto v___jp_3066_;
}
}
v___jp_3184_:
{
lean_object* v___x_3194_; 
if (v_isShared_2877_ == 0)
{
lean_ctor_set(v___x_2876_, 1, v___y_3192_);
lean_ctor_set(v___x_2876_, 0, v___y_3189_);
v___x_3194_ = v___x_2876_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___y_3189_);
lean_ctor_set(v_reuseFailAlloc_3289_, 1, v___y_3192_);
v___x_3194_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v_moduleData_3198_; lean_object* v___x_3199_; uint8_t v___x_3200_; 
v___x_3195_ = lean_box(0);
lean_inc_ref(v___y_3191_);
v___x_3196_ = l_Lean_EnvExtension_setState___redArg(v___y_3191_, v___y_3187_, v___x_3194_, v___x_3195_);
v___x_3197_ = l_Lean_Environment_header(v___x_3196_);
v_moduleData_3198_ = lean_ctor_get(v___x_3197_, 6);
lean_inc_ref(v_moduleData_3198_);
lean_dec_ref(v___x_3197_);
v___x_3199_ = lean_array_get_size(v_moduleData_3198_);
v___x_3200_ = lean_nat_dec_lt(v___y_3186_, v___x_3199_);
if (v___x_3200_ == 0)
{
lean_object* v___x_3201_; lean_object* v___x_3202_; 
lean_dec_ref(v_moduleData_3198_);
lean_dec_ref(v___x_3196_);
lean_dec(v___y_3188_);
lean_dec(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___x_2891_);
lean_dec(v_fst_2873_);
lean_dec(v_name_2860_);
lean_dec(v_head_2853_);
lean_dec(v_head_2852_);
v___x_3201_ = lean_obj_once(&l_main___closed__21, &l_main___closed__21_once, _init_l_main___closed__21);
v___x_3202_ = l_panic___at___00main_spec__5(v___x_3201_);
return v___x_3202_;
}
else
{
lean_object* v_base_3203_; lean_object* v_private_3204_; lean_object* v_header_3205_; lean_object* v_serverBaseExts_3206_; lean_object* v_checked_3207_; lean_object* v_asyncConstsMap_3208_; lean_object* v_asyncCtx_x3f_3209_; lean_object* v_importRealizationCtx_x3f_3210_; lean_object* v_localRealizationCtxMap_3211_; lean_object* v_allRealizations_3212_; uint8_t v_isExporting_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3287_; 
v_base_3203_ = lean_ctor_get(v___x_3196_, 0);
lean_inc_ref(v_base_3203_);
v_private_3204_ = lean_ctor_get(v_base_3203_, 0);
lean_inc(v_private_3204_);
v_header_3205_ = lean_ctor_get(v_private_3204_, 5);
lean_inc_ref(v_header_3205_);
v_serverBaseExts_3206_ = lean_ctor_get(v___x_3196_, 1);
v_checked_3207_ = lean_ctor_get(v___x_3196_, 2);
v_asyncConstsMap_3208_ = lean_ctor_get(v___x_3196_, 3);
v_asyncCtx_x3f_3209_ = lean_ctor_get(v___x_3196_, 4);
v_importRealizationCtx_x3f_3210_ = lean_ctor_get(v___x_3196_, 5);
v_localRealizationCtxMap_3211_ = lean_ctor_get(v___x_3196_, 6);
v_allRealizations_3212_ = lean_ctor_get(v___x_3196_, 7);
v_isExporting_3213_ = lean_ctor_get_uint8(v___x_3196_, sizeof(void*)*8);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3287_ == 0)
{
lean_object* v_unused_3288_; 
v_unused_3288_ = lean_ctor_get(v___x_3196_, 0);
lean_dec(v_unused_3288_);
v___x_3215_ = v___x_3196_;
v_isShared_3216_ = v_isSharedCheck_3287_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_allRealizations_3212_);
lean_inc(v_localRealizationCtxMap_3211_);
lean_inc(v_importRealizationCtx_x3f_3210_);
lean_inc(v_asyncCtx_x3f_3209_);
lean_inc(v_asyncConstsMap_3208_);
lean_inc(v_checked_3207_);
lean_inc(v_serverBaseExts_3206_);
lean_dec(v___x_3196_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3287_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v_public_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3285_; 
v_public_3217_ = lean_ctor_get(v_base_3203_, 1);
v_isSharedCheck_3285_ = !lean_is_exclusive(v_base_3203_);
if (v_isSharedCheck_3285_ == 0)
{
lean_object* v_unused_3286_; 
v_unused_3286_ = lean_ctor_get(v_base_3203_, 0);
lean_dec(v_unused_3286_);
v___x_3219_ = v_base_3203_;
v_isShared_3220_ = v_isSharedCheck_3285_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_public_3217_);
lean_dec(v_base_3203_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3285_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v_constants_3221_; uint8_t v_quotInit_3222_; lean_object* v_diagnostics_3223_; lean_object* v_const2ModIdx_3224_; lean_object* v_extensions_3225_; lean_object* v_irBaseExts_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3283_; 
v_constants_3221_ = lean_ctor_get(v_private_3204_, 0);
v_quotInit_3222_ = lean_ctor_get_uint8(v_private_3204_, sizeof(void*)*6);
v_diagnostics_3223_ = lean_ctor_get(v_private_3204_, 1);
v_const2ModIdx_3224_ = lean_ctor_get(v_private_3204_, 2);
v_extensions_3225_ = lean_ctor_get(v_private_3204_, 3);
v_irBaseExts_3226_ = lean_ctor_get(v_private_3204_, 4);
v_isSharedCheck_3283_ = !lean_is_exclusive(v_private_3204_);
if (v_isSharedCheck_3283_ == 0)
{
lean_object* v_unused_3284_; 
v_unused_3284_ = lean_ctor_get(v_private_3204_, 5);
lean_dec(v_unused_3284_);
v___x_3228_ = v_private_3204_;
v_isShared_3229_ = v_isSharedCheck_3283_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_irBaseExts_3226_);
lean_inc(v_extensions_3225_);
lean_inc(v_const2ModIdx_3224_);
lean_inc(v_diagnostics_3223_);
lean_inc(v_constants_3221_);
lean_dec(v_private_3204_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3283_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
uint32_t v_trustLevel_3230_; lean_object* v_mainModule_3231_; uint8_t v_isModule_3232_; lean_object* v_regions_3233_; lean_object* v_modules_3234_; lean_object* v_moduleName2Idx_3235_; lean_object* v_importAllModules_3236_; lean_object* v_moduleData_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3281_; 
v_trustLevel_3230_ = lean_ctor_get_uint32(v_header_3205_, sizeof(void*)*7);
v_mainModule_3231_ = lean_ctor_get(v_header_3205_, 0);
v_isModule_3232_ = lean_ctor_get_uint8(v_header_3205_, sizeof(void*)*7 + 4);
v_regions_3233_ = lean_ctor_get(v_header_3205_, 2);
v_modules_3234_ = lean_ctor_get(v_header_3205_, 3);
v_moduleName2Idx_3235_ = lean_ctor_get(v_header_3205_, 4);
v_importAllModules_3236_ = lean_ctor_get(v_header_3205_, 5);
v_moduleData_3237_ = lean_ctor_get(v_header_3205_, 6);
v_isSharedCheck_3281_ = !lean_is_exclusive(v_header_3205_);
if (v_isSharedCheck_3281_ == 0)
{
lean_object* v_unused_3282_; 
v_unused_3282_ = lean_ctor_get(v_header_3205_, 1);
lean_dec(v_unused_3282_);
v___x_3239_ = v_header_3205_;
v_isShared_3240_ = v_isSharedCheck_3281_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_moduleData_3237_);
lean_inc(v_importAllModules_3236_);
lean_inc(v_moduleName2Idx_3235_);
lean_inc(v_modules_3234_);
lean_inc(v_regions_3233_);
lean_inc(v_mainModule_3231_);
lean_dec(v_header_3205_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3281_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3241_; lean_object* v_imports_3242_; lean_object* v___x_3244_; 
v___x_3241_ = lean_array_fget(v_moduleData_3198_, v___y_3186_);
lean_dec_ref(v_moduleData_3198_);
v_imports_3242_ = lean_ctor_get(v___x_3241_, 0);
lean_inc_ref(v_imports_3242_);
lean_dec(v___x_3241_);
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 1, v_imports_3242_);
v___x_3244_ = v___x_3239_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(0, 7, 5);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_mainModule_3231_);
lean_ctor_set(v_reuseFailAlloc_3280_, 1, v_imports_3242_);
lean_ctor_set(v_reuseFailAlloc_3280_, 2, v_regions_3233_);
lean_ctor_set(v_reuseFailAlloc_3280_, 3, v_modules_3234_);
lean_ctor_set(v_reuseFailAlloc_3280_, 4, v_moduleName2Idx_3235_);
lean_ctor_set(v_reuseFailAlloc_3280_, 5, v_importAllModules_3236_);
lean_ctor_set(v_reuseFailAlloc_3280_, 6, v_moduleData_3237_);
lean_ctor_set_uint32(v_reuseFailAlloc_3280_, sizeof(void*)*7, v_trustLevel_3230_);
lean_ctor_set_uint8(v_reuseFailAlloc_3280_, sizeof(void*)*7 + 4, v_isModule_3232_);
v___x_3244_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
lean_object* v___x_3246_; 
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 5, v___x_3244_);
v___x_3246_ = v___x_3228_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_constants_3221_);
lean_ctor_set(v_reuseFailAlloc_3279_, 1, v_diagnostics_3223_);
lean_ctor_set(v_reuseFailAlloc_3279_, 2, v_const2ModIdx_3224_);
lean_ctor_set(v_reuseFailAlloc_3279_, 3, v_extensions_3225_);
lean_ctor_set(v_reuseFailAlloc_3279_, 4, v_irBaseExts_3226_);
lean_ctor_set(v_reuseFailAlloc_3279_, 5, v___x_3244_);
lean_ctor_set_uint8(v_reuseFailAlloc_3279_, sizeof(void*)*6, v_quotInit_3222_);
v___x_3246_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
lean_object* v___x_3248_; 
if (v_isShared_3220_ == 0)
{
lean_ctor_set(v___x_3219_, 0, v___x_3246_);
v___x_3248_ = v___x_3219_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v___x_3246_);
lean_ctor_set(v_reuseFailAlloc_3278_, 1, v_public_3217_);
v___x_3248_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
lean_object* v___x_3250_; 
if (v_isShared_3216_ == 0)
{
lean_ctor_set(v___x_3215_, 0, v___x_3248_);
v___x_3250_ = v___x_3215_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3248_);
lean_ctor_set(v_reuseFailAlloc_3277_, 1, v_serverBaseExts_3206_);
lean_ctor_set(v_reuseFailAlloc_3277_, 2, v_checked_3207_);
lean_ctor_set(v_reuseFailAlloc_3277_, 3, v_asyncConstsMap_3208_);
lean_ctor_set(v_reuseFailAlloc_3277_, 4, v_asyncCtx_x3f_3209_);
lean_ctor_set(v_reuseFailAlloc_3277_, 5, v_importRealizationCtx_x3f_3210_);
lean_ctor_set(v_reuseFailAlloc_3277_, 6, v_localRealizationCtxMap_3211_);
lean_ctor_set(v_reuseFailAlloc_3277_, 7, v_allRealizations_3212_);
lean_ctor_set_uint8(v_reuseFailAlloc_3277_, sizeof(void*)*8, v_isExporting_3213_);
v___x_3250_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v_env_3273_; lean_object* v___x_3274_; uint8_t v___x_3275_; uint8_t v___x_3276_; 
v___x_3251_ = l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
v___x_3252_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2885_, v___x_3251_, v___x_3250_, v___y_3186_, v___y_3190_);
lean_dec(v___y_3186_);
v___x_3253_ = l_Lean_firstFrontendMacroScope;
v___x_3254_ = lean_obj_once(&l_main___closed__22, &l_main___closed__22_once, _init_l_main___closed__22);
v___x_3255_ = ((lean_object*)(l_main___closed__25));
lean_inc_n(v___y_3188_, 3);
v___x_3256_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3256_, 0, v___y_3188_);
lean_ctor_set(v___x_3256_, 1, v___x_3183_);
lean_ctor_set(v___x_3256_, 2, v___x_2871_);
v___x_3257_ = lean_obj_once(&l_main___closed__26, &l_main___closed__26_once, _init_l_main___closed__26);
v___x_3258_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_3259_ = lean_obj_once(&l_main___closed__30, &l_main___closed__30_once, _init_l_main___closed__30);
v___x_3260_ = lean_obj_once(&l_main___closed__31, &l_main___closed__31_once, _init_l_main___closed__31);
v___x_3261_ = ((lean_object*)(l_main___closed__32));
lean_inc_ref(v___x_3256_);
v___x_3262_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3250_);
lean_ctor_set(v___x_3262_, 1, v___x_3254_);
lean_ctor_set(v___x_3262_, 2, v___x_3255_);
lean_ctor_set(v___x_3262_, 3, v___x_3256_);
lean_ctor_set(v___x_3262_, 4, v___x_3257_);
lean_ctor_set(v___x_3262_, 5, v___x_3258_);
lean_ctor_set(v___x_3262_, 6, v___x_3259_);
lean_ctor_set(v___x_3262_, 7, v___x_3260_);
lean_ctor_set(v___x_3262_, 8, v___x_3261_);
v___x_3263_ = lean_st_mk_ref(v___x_3262_);
v___x_3264_ = l_Lean_inheritedTraceOptions;
v___x_3265_ = lean_st_ref_get(v___x_3264_);
v___x_3266_ = lean_st_ref_get(v___x_3263_);
v___x_3267_ = l_Lean_instInhabitedFileMap_default;
v___x_3268_ = lean_unsigned_to_nat(1000u);
v___x_3269_ = lean_box(0);
v___x_3270_ = l_Lean_Core_getMaxHeartbeats(v___x_2891_);
v___x_3271_ = lean_box(0);
lean_inc_ref(v___x_2891_);
lean_inc(v_head_2852_);
v___x_3272_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3272_, 0, v_head_2852_);
lean_ctor_set(v___x_3272_, 1, v___x_3267_);
lean_ctor_set(v___x_3272_, 2, v___x_2891_);
lean_ctor_set(v___x_3272_, 3, v___x_2890_);
lean_ctor_set(v___x_3272_, 4, v___x_3268_);
lean_ctor_set(v___x_3272_, 5, v___x_3269_);
lean_ctor_set(v___x_3272_, 6, v___y_3188_);
lean_ctor_set(v___x_3272_, 7, v___x_2871_);
lean_ctor_set(v___x_3272_, 8, v___x_2890_);
lean_ctor_set(v___x_3272_, 9, v___x_3270_);
lean_ctor_set(v___x_3272_, 10, v___y_3188_);
lean_ctor_set(v___x_3272_, 11, v___x_3253_);
lean_ctor_set(v___x_3272_, 12, v___x_3271_);
lean_ctor_set(v___x_3272_, 13, v___x_3265_);
lean_ctor_set_uint8(v___x_3272_, sizeof(void*)*14, v___x_2862_);
lean_ctor_set_uint8(v___x_3272_, sizeof(void*)*14 + 1, v___x_2862_);
v_env_3273_ = lean_ctor_get(v___x_3266_, 0);
lean_inc_ref(v_env_3273_);
lean_dec(v___x_3266_);
v___x_3274_ = l_Lean_diagnostics;
v___x_3275_ = l_Lean_Option_get___at___00main_spec__8(v___x_2891_, v___x_3274_);
v___x_3276_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3273_);
lean_dec_ref(v_env_3273_);
if (v___x_3276_ == 0)
{
if (v___x_3275_ == 0)
{
v___y_3138_ = v___x_3258_;
v___y_3139_ = v___x_3264_;
v___y_3140_ = v___x_3253_;
v___y_3141_ = v___x_3200_;
v___y_3142_ = v___x_3267_;
v___y_3143_ = v___y_3185_;
v___y_3144_ = v___x_3271_;
v___y_3145_ = v___x_2871_;
v___y_3146_ = v___x_3269_;
v___y_3147_ = v___x_3258_;
v___y_3148_ = v___x_3272_;
v___y_3149_ = v___x_3255_;
v___y_3150_ = v___x_3254_;
v___y_3151_ = v___x_3259_;
v___y_3152_ = v___x_3257_;
v___y_3153_ = v___x_3256_;
v___y_3154_ = v___x_3261_;
v___y_3155_ = v___x_3251_;
v___y_3156_ = v___x_3275_;
v___y_3157_ = v___x_3260_;
v___y_3158_ = v___y_3188_;
v___y_3159_ = v___x_3252_;
v___y_3160_ = v___x_3263_;
v___y_3161_ = v___x_3200_;
goto v___jp_3137_;
}
else
{
v___y_3138_ = v___x_3258_;
v___y_3139_ = v___x_3264_;
v___y_3140_ = v___x_3253_;
v___y_3141_ = v___x_3200_;
v___y_3142_ = v___x_3267_;
v___y_3143_ = v___y_3185_;
v___y_3144_ = v___x_3271_;
v___y_3145_ = v___x_2871_;
v___y_3146_ = v___x_3269_;
v___y_3147_ = v___x_3258_;
v___y_3148_ = v___x_3272_;
v___y_3149_ = v___x_3255_;
v___y_3150_ = v___x_3254_;
v___y_3151_ = v___x_3259_;
v___y_3152_ = v___x_3257_;
v___y_3153_ = v___x_3256_;
v___y_3154_ = v___x_3261_;
v___y_3155_ = v___x_3251_;
v___y_3156_ = v___x_3275_;
v___y_3157_ = v___x_3260_;
v___y_3158_ = v___y_3188_;
v___y_3159_ = v___x_3252_;
v___y_3160_ = v___x_3263_;
v___y_3161_ = v___x_3276_;
goto v___jp_3137_;
}
}
else
{
v___y_3138_ = v___x_3258_;
v___y_3139_ = v___x_3264_;
v___y_3140_ = v___x_3253_;
v___y_3141_ = v___x_3200_;
v___y_3142_ = v___x_3267_;
v___y_3143_ = v___y_3185_;
v___y_3144_ = v___x_3271_;
v___y_3145_ = v___x_2871_;
v___y_3146_ = v___x_3269_;
v___y_3147_ = v___x_3258_;
v___y_3148_ = v___x_3272_;
v___y_3149_ = v___x_3255_;
v___y_3150_ = v___x_3254_;
v___y_3151_ = v___x_3259_;
v___y_3152_ = v___x_3257_;
v___y_3153_ = v___x_3256_;
v___y_3154_ = v___x_3261_;
v___y_3155_ = v___x_3251_;
v___y_3156_ = v___x_3275_;
v___y_3157_ = v___x_3260_;
v___y_3158_ = v___y_3188_;
v___y_3159_ = v___x_3252_;
v___y_3160_ = v___x_3263_;
v___y_3161_ = v___x_3275_;
goto v___jp_3137_;
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
v___jp_3290_:
{
lean_object* v___x_3296_; lean_object* v_toEnvExtension_3297_; lean_object* v_asyncMode_3298_; lean_object* v___x_3299_; lean_object* v_importedEntries_3300_; lean_object* v_state_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; uint8_t v___x_3304_; 
v___x_3296_ = l_Lean_IR_declMapExt;
v_toEnvExtension_3297_ = lean_ctor_get(v___x_3296_, 0);
v_asyncMode_3298_ = lean_ctor_get(v_toEnvExtension_3297_, 2);
lean_inc(v___y_3293_);
lean_inc_ref(v___y_3295_);
v___x_3299_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2882_, v_toEnvExtension_3297_, v___y_3295_, v_asyncMode_3298_, v___y_3293_);
v_importedEntries_3300_ = lean_ctor_get(v___x_3299_, 0);
lean_inc_ref(v_importedEntries_3300_);
v_state_3301_ = lean_ctor_get(v___x_3299_, 1);
lean_inc(v_state_3301_);
lean_dec(v___x_3299_);
v___x_3302_ = lean_array_get_borrowed(v___x_2883_, v_importedEntries_3300_, v___y_3292_);
v___x_3303_ = lean_array_get_size(v___x_3302_);
v___x_3304_ = lean_nat_dec_lt(v___x_2890_, v___x_3303_);
if (v___x_3304_ == 0)
{
v___y_3185_ = v___y_3291_;
v___y_3186_ = v___y_3292_;
v___y_3187_ = v___y_3295_;
v___y_3188_ = v___y_3293_;
v___y_3189_ = v_importedEntries_3300_;
v___y_3190_ = v___y_3294_;
v___y_3191_ = v_toEnvExtension_3297_;
v___y_3192_ = v_state_3301_;
goto v___jp_3184_;
}
else
{
uint8_t v___x_3305_; 
v___x_3305_ = lean_nat_dec_le(v___x_3303_, v___x_3303_);
if (v___x_3305_ == 0)
{
if (v___x_3304_ == 0)
{
v___y_3185_ = v___y_3291_;
v___y_3186_ = v___y_3292_;
v___y_3187_ = v___y_3295_;
v___y_3188_ = v___y_3293_;
v___y_3189_ = v_importedEntries_3300_;
v___y_3190_ = v___y_3294_;
v___y_3191_ = v_toEnvExtension_3297_;
v___y_3192_ = v_state_3301_;
goto v___jp_3184_;
}
else
{
size_t v___x_3306_; size_t v___x_3307_; lean_object* v___x_3308_; 
v___x_3306_ = ((size_t)0ULL);
v___x_3307_ = lean_usize_of_nat(v___x_3303_);
lean_inc_ref(v___y_3295_);
v___x_3308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3295_, v___x_3302_, v___x_3306_, v___x_3307_, v_state_3301_);
v___y_3185_ = v___y_3291_;
v___y_3186_ = v___y_3292_;
v___y_3187_ = v___y_3295_;
v___y_3188_ = v___y_3293_;
v___y_3189_ = v_importedEntries_3300_;
v___y_3190_ = v___y_3294_;
v___y_3191_ = v_toEnvExtension_3297_;
v___y_3192_ = v___x_3308_;
goto v___jp_3184_;
}
}
else
{
size_t v___x_3309_; size_t v___x_3310_; lean_object* v___x_3311_; 
v___x_3309_ = ((size_t)0ULL);
v___x_3310_ = lean_usize_of_nat(v___x_3303_);
lean_inc_ref(v___y_3295_);
v___x_3311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3295_, v___x_3302_, v___x_3309_, v___x_3310_, v_state_3301_);
v___y_3185_ = v___y_3291_;
v___y_3186_ = v___y_3292_;
v___y_3187_ = v___y_3295_;
v___y_3188_ = v___y_3293_;
v___y_3189_ = v_importedEntries_3300_;
v___y_3190_ = v___y_3294_;
v___y_3191_ = v_toEnvExtension_3297_;
v___y_3192_ = v___x_3311_;
goto v___jp_3184_;
}
}
}
v___jp_3312_:
{
uint8_t v___x_3320_; 
v___x_3320_ = lean_nat_dec_lt(v___x_2890_, v___y_3318_);
if (v___x_3320_ == 0)
{
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3314_);
v___y_3291_ = v___y_3313_;
v___y_3292_ = v___y_3315_;
v___y_3293_ = v___y_3316_;
v___y_3294_ = v___y_3317_;
v___y_3295_ = v___y_3319_;
goto v___jp_3290_;
}
else
{
uint8_t v___x_3321_; 
v___x_3321_ = lean_nat_dec_le(v___y_3318_, v___y_3318_);
if (v___x_3321_ == 0)
{
if (v___x_3320_ == 0)
{
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3314_);
v___y_3291_ = v___y_3313_;
v___y_3292_ = v___y_3315_;
v___y_3293_ = v___y_3316_;
v___y_3294_ = v___y_3317_;
v___y_3295_ = v___y_3319_;
goto v___jp_3290_;
}
else
{
size_t v___x_3322_; size_t v___x_3323_; lean_object* v___x_3324_; 
v___x_3322_ = ((size_t)0ULL);
v___x_3323_ = lean_usize_of_nat(v___y_3318_);
lean_dec(v___y_3318_);
v___x_3324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3314_, v___x_3322_, v___x_3323_, v___y_3319_);
lean_dec_ref(v___y_3314_);
v___y_3291_ = v___y_3313_;
v___y_3292_ = v___y_3315_;
v___y_3293_ = v___y_3316_;
v___y_3294_ = v___y_3317_;
v___y_3295_ = v___x_3324_;
goto v___jp_3290_;
}
}
else
{
size_t v___x_3325_; size_t v___x_3326_; lean_object* v___x_3327_; 
v___x_3325_ = ((size_t)0ULL);
v___x_3326_ = lean_usize_of_nat(v___y_3318_);
lean_dec(v___y_3318_);
v___x_3327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3314_, v___x_3325_, v___x_3326_, v___y_3319_);
lean_dec_ref(v___y_3314_);
v___y_3291_ = v___y_3313_;
v___y_3292_ = v___y_3315_;
v___y_3293_ = v___y_3316_;
v___y_3294_ = v___y_3317_;
v___y_3295_ = v___x_3327_;
goto v___jp_3290_;
}
}
}
v___jp_3328_:
{
lean_object* v___x_3335_; uint8_t v___x_3336_; 
v___x_3335_ = lean_array_get_size(v___y_3334_);
v___x_3336_ = lean_nat_dec_lt(v___x_2890_, v___x_3335_);
if (v___x_3336_ == 0)
{
v___y_3313_ = v___y_3330_;
v___y_3314_ = v___y_3334_;
v___y_3315_ = v___y_3329_;
v___y_3316_ = v___y_3332_;
v___y_3317_ = v___y_3333_;
v___y_3318_ = v___x_3335_;
v___y_3319_ = v___y_3331_;
goto v___jp_3312_;
}
else
{
uint8_t v___x_3337_; 
v___x_3337_ = lean_nat_dec_le(v___x_3335_, v___x_3335_);
if (v___x_3337_ == 0)
{
if (v___x_3336_ == 0)
{
v___y_3313_ = v___y_3330_;
v___y_3314_ = v___y_3334_;
v___y_3315_ = v___y_3329_;
v___y_3316_ = v___y_3332_;
v___y_3317_ = v___y_3333_;
v___y_3318_ = v___x_3335_;
v___y_3319_ = v___y_3331_;
goto v___jp_3312_;
}
else
{
size_t v___x_3338_; size_t v___x_3339_; lean_object* v___x_3340_; 
v___x_3338_ = ((size_t)0ULL);
v___x_3339_ = lean_usize_of_nat(v___x_3335_);
v___x_3340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3334_, v___x_3338_, v___x_3339_, v___y_3331_);
v___y_3313_ = v___y_3330_;
v___y_3314_ = v___y_3334_;
v___y_3315_ = v___y_3329_;
v___y_3316_ = v___y_3332_;
v___y_3317_ = v___y_3333_;
v___y_3318_ = v___x_3335_;
v___y_3319_ = v___x_3340_;
goto v___jp_3312_;
}
}
else
{
size_t v___x_3341_; size_t v___x_3342_; lean_object* v___x_3343_; 
v___x_3341_ = ((size_t)0ULL);
v___x_3342_ = lean_usize_of_nat(v___x_3335_);
v___x_3343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3334_, v___x_3341_, v___x_3342_, v___y_3331_);
v___y_3313_ = v___y_3330_;
v___y_3314_ = v___y_3334_;
v___y_3315_ = v___y_3329_;
v___y_3316_ = v___y_3332_;
v___y_3317_ = v___y_3333_;
v___y_3318_ = v___x_3335_;
v___y_3319_ = v___x_3343_;
goto v___jp_3312_;
}
}
}
v___jp_3347_:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___f_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3349_ = l_Lean_instInhabitedImportState_default;
v___x_3350_ = lean_box(v___x_3346_);
v___x_3351_ = lean_box(v___y_3348_);
v___x_3352_ = lean_box(v___x_2887_);
v___x_3353_ = lean_box(v___x_2862_);
lean_inc_ref(v___x_2891_);
lean_inc(v_name_2860_);
v___f_3354_ = lean_alloc_closure((void*)(l_main___lam__0___boxed), 10, 9);
lean_closure_set(v___f_3354_, 0, v___x_3349_);
lean_closure_set(v___f_3354_, 1, v___x_3345_);
lean_closure_set(v___f_3354_, 2, v___x_3350_);
lean_closure_set(v___f_3354_, 3, v___x_2884_);
lean_closure_set(v___f_3354_, 4, v___x_3351_);
lean_closure_set(v___f_3354_, 5, v_name_2860_);
lean_closure_set(v___f_3354_, 6, v___x_2891_);
lean_closure_set(v___f_3354_, 7, v___x_3352_);
lean_closure_set(v___f_3354_, 8, v___x_3353_);
v___x_3355_ = lean_alloc_closure((void*)(l_Lean_withImporting___boxed), 3, 2);
lean_closure_set(v___x_3355_, 0, lean_box(0));
lean_closure_set(v___x_3355_, 1, v___f_3354_);
v___x_3356_ = lean_box(0);
v___x_3357_ = l_Lean_profileitIOUnsafe___redArg(v___x_3181_, v___x_2891_, v___x_3355_, v___x_3356_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_a_3358_; lean_object* v___x_3359_; lean_object* v_ext_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_a_3358_);
lean_dec_ref(v___x_3357_);
v___x_3359_ = l_Lean_Compiler_CSimp_ext;
v_ext_3360_ = lean_ctor_get(v___x_3359_, 1);
lean_inc(v_name_2860_);
v___x_3361_ = l_Lean_Environment_setMainModule(v_a_3358_, v_name_2860_);
lean_inc_ref(v_ext_3360_);
v___x_3362_ = l_main___elam__0___redArg(v___x_3356_, v___x_2878_, v_ext_3360_, v___x_3361_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v___x_3364_; lean_object* v_ext_3365_; lean_object* v___x_3366_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3363_);
lean_dec_ref(v___x_3362_);
v___x_3364_ = l_Lean_Meta_instanceExtension;
v_ext_3365_ = lean_ctor_get(v___x_3364_, 1);
lean_inc_ref(v_ext_3365_);
v___x_3366_ = l_main___elam__0___redArg(v___x_3356_, v___x_2878_, v_ext_3365_, v_a_3363_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_a_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
lean_inc(v_a_3367_);
lean_dec_ref(v___x_3366_);
v___x_3368_ = l_Lean_classExtension;
v___x_3369_ = l_main___elam__0___redArg(v___x_3356_, v___x_2879_, v___x_3368_, v_a_3367_);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v_a_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; 
v_a_3370_ = lean_ctor_get(v___x_3369_, 0);
lean_inc(v_a_3370_);
lean_dec_ref(v___x_3369_);
v___x_3371_ = l_Lean_Meta_Match_Extension_extension;
v___x_3372_ = l_main___elam__0___redArg(v___x_3356_, v___x_2880_, v___x_3371_, v_a_3370_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3401_; 
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3375_ = v___x_3372_;
v_isShared_3376_ = v_isSharedCheck_3401_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3372_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3401_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3377_; 
v___x_3377_ = l_Lean_Environment_getModuleIdx_x3f(v_a_3373_, v_name_2860_);
if (lean_obj_tag(v___x_3377_) == 1)
{
lean_object* v_val_3378_; lean_object* v___x_3379_; uint8_t v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; uint8_t v___x_3384_; 
lean_del_object(v___x_3375_);
v_val_3378_ = lean_ctor_get(v___x_3377_, 0);
lean_inc(v_val_3378_);
lean_dec_ref(v___x_3377_);
v___x_3379_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_3380_ = 0;
v___x_3381_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2881_, v___x_3379_, v_a_3373_, v_val_3378_, v___x_3380_);
v___x_3382_ = lean_array_get_size(v___x_3381_);
v___x_3383_ = ((lean_object*)(l_main___closed__33));
v___x_3384_ = lean_nat_dec_lt(v___x_2890_, v___x_3382_);
if (v___x_3384_ == 0)
{
lean_dec_ref(v___x_3381_);
v___y_3329_ = v_val_3378_;
v___y_3330_ = v___x_3356_;
v___y_3331_ = v_a_3373_;
v___y_3332_ = v___x_3356_;
v___y_3333_ = v___x_3380_;
v___y_3334_ = v___x_3383_;
goto v___jp_3328_;
}
else
{
uint8_t v___x_3385_; 
v___x_3385_ = lean_nat_dec_le(v___x_3382_, v___x_3382_);
if (v___x_3385_ == 0)
{
if (v___x_3384_ == 0)
{
lean_dec_ref(v___x_3381_);
v___y_3329_ = v_val_3378_;
v___y_3330_ = v___x_3356_;
v___y_3331_ = v_a_3373_;
v___y_3332_ = v___x_3356_;
v___y_3333_ = v___x_3380_;
v___y_3334_ = v___x_3383_;
goto v___jp_3328_;
}
else
{
size_t v___x_3386_; size_t v___x_3387_; lean_object* v___x_3388_; 
v___x_3386_ = ((size_t)0ULL);
v___x_3387_ = lean_usize_of_nat(v___x_3382_);
lean_inc(v_a_3373_);
v___x_3388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3373_, v___x_3381_, v___x_3386_, v___x_3387_, v___x_3383_);
lean_dec_ref(v___x_3381_);
v___y_3329_ = v_val_3378_;
v___y_3330_ = v___x_3356_;
v___y_3331_ = v_a_3373_;
v___y_3332_ = v___x_3356_;
v___y_3333_ = v___x_3380_;
v___y_3334_ = v___x_3388_;
goto v___jp_3328_;
}
}
else
{
size_t v___x_3389_; size_t v___x_3390_; lean_object* v___x_3391_; 
v___x_3389_ = ((size_t)0ULL);
v___x_3390_ = lean_usize_of_nat(v___x_3382_);
lean_inc(v_a_3373_);
v___x_3391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3373_, v___x_3381_, v___x_3389_, v___x_3390_, v___x_3383_);
lean_dec_ref(v___x_3381_);
v___y_3329_ = v_val_3378_;
v___y_3330_ = v___x_3356_;
v___y_3331_ = v_a_3373_;
v___y_3332_ = v___x_3356_;
v___y_3333_ = v___x_3380_;
v___y_3334_ = v___x_3391_;
goto v___jp_3328_;
}
}
}
else
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3399_; 
lean_dec(v___x_3377_);
lean_dec(v_a_3373_);
lean_dec_ref(v___x_2891_);
lean_del_object(v___x_2876_);
lean_dec(v_fst_2873_);
lean_dec(v_head_2853_);
lean_dec(v_head_2852_);
v___x_3392_ = ((lean_object*)(l_main___closed__34));
v___x_3393_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2860_, v___x_2887_);
v___x_3394_ = lean_string_append(v___x_3392_, v___x_3393_);
lean_dec_ref(v___x_3393_);
v___x_3395_ = ((lean_object*)(l_main___closed__35));
v___x_3396_ = lean_string_append(v___x_3394_, v___x_3395_);
v___x_3397_ = lean_mk_io_user_error(v___x_3396_);
if (v_isShared_3376_ == 0)
{
lean_ctor_set_tag(v___x_3375_, 1);
lean_ctor_set(v___x_3375_, 0, v___x_3397_);
v___x_3399_ = v___x_3375_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v___x_3397_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
}
else
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
lean_dec_ref(v___x_2891_);
lean_del_object(v___x_2876_);
lean_dec(v_fst_2873_);
lean_dec(v_name_2860_);
lean_dec(v_head_2853_);
lean_dec(v_head_2852_);
v_a_3402_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3404_ = v___x_3372_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3372_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3402_);
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
lean_dec_ref(v___x_2891_);
lean_del_object(v___x_2876_);
lean_dec(v_fst_2873_);
lean_dec(v_name_2860_);
lean_dec(v_head_2853_);
lean_dec(v_head_2852_);
v_a_3410_ = lean_ctor_get(v___x_3369_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___x_3369_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3369_);
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
lean_dec_ref(v___x_2891_);
lean_del_object(v___x_2876_);
lean_dec(v_fst_2873_);
lean_dec(v_name_2860_);
lean_dec(v_head_2853_);
lean_dec(v_head_2852_);
v_a_3418_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3420_ = v___x_3366_;
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3366_);
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
lean_dec_ref(v___x_2891_);
lean_del_object(v___x_2876_);
lean_dec(v_fst_2873_);
lean_dec(v_name_2860_);
lean_dec(v_head_2853_);
lean_dec(v_head_2852_);
v_a_3426_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3428_ = v___x_3362_;
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___x_3362_);
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
lean_dec_ref(v___x_2891_);
lean_del_object(v___x_2876_);
lean_dec(v_fst_2873_);
lean_dec(v_name_2860_);
lean_dec(v_head_2853_);
lean_dec(v_head_2852_);
v_a_3434_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3357_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3357_);
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
}
}
else
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3451_; 
lean_dec(v_a_2868_);
lean_dec(v_name_2860_);
lean_dec(v_head_2853_);
lean_dec(v_head_2852_);
v_a_3444_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3446_ = v___x_2872_;
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_2872_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3444_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
}
else
{
lean_object* v_a_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3459_; 
lean_dec(v_a_2868_);
lean_dec(v_name_2860_);
lean_dec(v_head_2853_);
lean_dec(v_head_2852_);
v_a_3452_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3454_ = v___x_2869_;
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_a_3452_);
lean_dec(v___x_2869_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3457_; 
if (v_isShared_3455_ == 0)
{
v___x_3457_ = v___x_3454_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_a_3452_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
}
}
else
{
lean_object* v_a_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3467_; 
lean_dec(v_name_2860_);
lean_dec(v_head_2853_);
lean_dec(v_head_2852_);
v_a_3460_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3462_ = v___x_2867_;
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_a_3460_);
lean_dec(v___x_2867_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3465_; 
if (v_isShared_3463_ == 0)
{
v___x_3465_ = v___x_3462_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_a_3460_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
}
}
else
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3476_; 
lean_del_object(v___x_2856_);
lean_dec(v_tail_2854_);
lean_dec(v_head_2853_);
lean_dec(v_head_2852_);
v_a_3469_ = lean_ctor_get(v___x_2858_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3471_ = v___x_2858_;
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_2858_);
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
}
else
{
lean_dec_ref(v_tail_2849_);
lean_dec(v_tail_2850_);
lean_dec_ref(v_args_2824_);
goto v___jp_2826_;
}
}
else
{
lean_dec(v_tail_2849_);
lean_dec_ref(v_args_2824_);
goto v___jp_2826_;
}
}
else
{
lean_dec(v_args_2824_);
goto v___jp_2826_;
}
v___jp_2826_:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = ((lean_object*)(l_main___closed__0));
v___x_2828_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_2827_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2836_; 
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2836_ == 0)
{
lean_object* v_unused_2837_; 
v_unused_2837_ = lean_ctor_get(v___x_2828_, 0);
lean_dec(v_unused_2837_);
v___x_2830_ = v___x_2828_;
v_isShared_2831_ = v_isSharedCheck_2836_;
goto v_resetjp_2829_;
}
else
{
lean_dec(v___x_2828_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2836_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2832_; lean_object* v___x_2834_; 
v___x_2832_ = l_main___boxed__const__1;
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 0, v___x_2832_);
v___x_2834_ = v___x_2830_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v___x_2832_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
else
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
v_a_2838_ = lean_ctor_get(v___x_2828_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v___x_2828_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2828_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2841_ == 0)
{
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2838_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
v___jp_2846_:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2847_ = l_main___boxed__const__2;
v___x_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2847_);
return v___x_2848_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_3478_, lean_object* v_a_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = _lean_main(v_args_3478_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object* v_as_3481_, lean_object* v_as_x27_3482_, lean_object* v_b_3483_, lean_object* v_a_3484_){
_start:
{
lean_object* v___x_3486_; 
v___x_3486_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_3482_, v_b_3483_);
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object* v_as_3487_, lean_object* v_as_x27_3488_, lean_object* v_b_3489_, lean_object* v_a_3490_, lean_object* v___y_3491_){
_start:
{
lean_object* v_res_3492_; 
v_res_3492_ = l_List_forIn_x27_loop___at___00main_spec__1(v_as_3487_, v_as_x27_3488_, v_b_3489_, v_a_3490_);
lean_dec(v_as_x27_3488_);
lean_dec(v_as_3487_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
lean_object* v___x_3496_; 
v___x_3496_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_3494_);
return v___x_3496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___boxed(lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v_res_3500_; 
v_res_3500_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(v___y_3497_, v___y_3498_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(lean_object* v_00_u03b2_3501_, lean_object* v_m_3502_, lean_object* v_a_3503_, lean_object* v_fallback_3504_){
_start:
{
lean_object* v___x_3505_; 
v___x_3505_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_3502_, v_a_3503_, v_fallback_3504_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___boxed(lean_object* v_00_u03b2_3506_, lean_object* v_m_3507_, lean_object* v_a_3508_, lean_object* v_fallback_3509_){
_start:
{
lean_object* v_res_3510_; 
v_res_3510_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(v_00_u03b2_3506_, v_m_3507_, v_a_3508_, v_fallback_3509_);
lean_dec(v_fallback_3509_);
lean_dec_ref(v_a_3508_);
lean_dec_ref(v_m_3507_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18(lean_object* v_00_u03b2_3511_, lean_object* v_m_3512_, lean_object* v_a_3513_, lean_object* v_b_3514_){
_start:
{
lean_object* v___x_3515_; 
v___x_3515_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_m_3512_, v_a_3513_, v_b_3514_);
return v___x_3515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(lean_object* v_n_3516_, lean_object* v_as_3517_, lean_object* v_lo_3518_, lean_object* v_hi_3519_, lean_object* v_w_3520_, lean_object* v_hlo_3521_, lean_object* v_hhi_3522_){
_start:
{
lean_object* v___x_3523_; 
v___x_3523_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_as_3517_, v_lo_3518_, v_hi_3519_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___boxed(lean_object* v_n_3524_, lean_object* v_as_3525_, lean_object* v_lo_3526_, lean_object* v_hi_3527_, lean_object* v_w_3528_, lean_object* v_hlo_3529_, lean_object* v_hhi_3530_){
_start:
{
lean_object* v_res_3531_; 
v_res_3531_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(v_n_3524_, v_as_3525_, v_lo_3526_, v_hi_3527_, v_w_3528_, v_hlo_3529_, v_hhi_3530_);
lean_dec(v_hi_3527_);
lean_dec(v_n_3524_);
return v_res_3531_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(lean_object* v_00_u03b2_3532_, lean_object* v_a_3533_, lean_object* v_fallback_3534_, lean_object* v_x_3535_){
_start:
{
lean_object* v___x_3536_; 
v___x_3536_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_3533_, v_fallback_3534_, v_x_3535_);
return v___x_3536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3537_, lean_object* v_a_3538_, lean_object* v_fallback_3539_, lean_object* v_x_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(v_00_u03b2_3537_, v_a_3538_, v_fallback_3539_, v_x_3540_);
lean_dec(v_x_3540_);
lean_dec(v_fallback_3539_);
lean_dec_ref(v_a_3538_);
return v_res_3541_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(lean_object* v_00_u03b2_3542_, lean_object* v_a_3543_, lean_object* v_x_3544_){
_start:
{
uint8_t v___x_3545_; 
v___x_3545_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_3543_, v_x_3544_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___boxed(lean_object* v_00_u03b2_3546_, lean_object* v_a_3547_, lean_object* v_x_3548_){
_start:
{
uint8_t v_res_3549_; lean_object* v_r_3550_; 
v_res_3549_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(v_00_u03b2_3546_, v_a_3547_, v_x_3548_);
lean_dec(v_x_3548_);
lean_dec_ref(v_a_3547_);
v_r_3550_ = lean_box(v_res_3549_);
return v_r_3550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24(lean_object* v_00_u03b2_3551_, lean_object* v_data_3552_){
_start:
{
lean_object* v___x_3553_; 
v___x_3553_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_data_3552_);
return v___x_3553_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25(lean_object* v_00_u03b2_3554_, lean_object* v_a_3555_, lean_object* v_b_3556_, lean_object* v_x_3557_){
_start:
{
lean_object* v___x_3558_; 
v___x_3558_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_3555_, v_b_3556_, v_x_3557_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__39(lean_object* v_as_3559_, size_t v_sz_3560_, size_t v_i_3561_, lean_object* v_b_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_){
_start:
{
lean_object* v___x_3566_; 
v___x_3566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__39___redArg(v_as_3559_, v_sz_3560_, v_i_3561_, v_b_3562_, v___y_3563_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__39___boxed(lean_object* v_as_3567_, lean_object* v_sz_3568_, lean_object* v_i_3569_, lean_object* v_b_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
size_t v_sz_boxed_3574_; size_t v_i_boxed_3575_; lean_object* v_res_3576_; 
v_sz_boxed_3574_ = lean_unbox_usize(v_sz_3568_);
lean_dec(v_sz_3568_);
v_i_boxed_3575_ = lean_unbox_usize(v_i_3569_);
lean_dec(v_i_3569_);
v_res_3576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__39(v_as_3567_, v_sz_boxed_3574_, v_i_boxed_3575_, v_b_3570_, v___y_3571_, v___y_3572_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec_ref(v_as_3567_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35(lean_object* v_00_u03b2_3577_, lean_object* v_i_3578_, lean_object* v_source_3579_, lean_object* v_target_3580_){
_start:
{
lean_object* v___x_3581_; 
v___x_3581_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v_i_3578_, v_source_3579_, v_target_3580_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(uint8_t v___x_3582_, lean_object* v_as_3583_, size_t v_sz_3584_, size_t v_i_3585_, lean_object* v_b_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_){
_start:
{
lean_object* v___x_3590_; 
v___x_3590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_3582_, v_as_3583_, v_sz_3584_, v_i_3585_, v_b_3586_, v___y_3587_);
return v___x_3590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___boxed(lean_object* v___x_3591_, lean_object* v_as_3592_, lean_object* v_sz_3593_, lean_object* v_i_3594_, lean_object* v_b_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_){
_start:
{
uint8_t v___x_41097__boxed_3599_; size_t v_sz_boxed_3600_; size_t v_i_boxed_3601_; lean_object* v_res_3602_; 
v___x_41097__boxed_3599_ = lean_unbox(v___x_3591_);
v_sz_boxed_3600_ = lean_unbox_usize(v_sz_3593_);
lean_dec(v_sz_3593_);
v_i_boxed_3601_ = lean_unbox_usize(v_i_3594_);
lean_dec(v_i_3594_);
v_res_3602_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(v___x_41097__boxed_3599_, v_as_3592_, v_sz_boxed_3600_, v_i_boxed_3601_, v_b_3595_, v___y_3596_, v___y_3597_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec_ref(v_as_3592_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37_spec__50(lean_object* v_as_3603_, size_t v_sz_3604_, size_t v_i_3605_, lean_object* v_b_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
lean_object* v___x_3610_; 
v___x_3610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37_spec__50___redArg(v_as_3603_, v_sz_3604_, v_i_3605_, v_b_3606_, v___y_3607_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37_spec__50___boxed(lean_object* v_as_3611_, lean_object* v_sz_3612_, lean_object* v_i_3613_, lean_object* v_b_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
size_t v_sz_boxed_3618_; size_t v_i_boxed_3619_; lean_object* v_res_3620_; 
v_sz_boxed_3618_ = lean_unbox_usize(v_sz_3612_);
lean_dec(v_sz_3612_);
v_i_boxed_3619_ = lean_unbox_usize(v_i_3613_);
lean_dec(v_i_3613_);
v_res_3620_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37_spec__50(v_as_3611_, v_sz_boxed_3618_, v_i_boxed_3619_, v_b_3614_, v___y_3615_, v___y_3616_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
lean_dec_ref(v_as_3611_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44(lean_object* v_00_u03b2_3621_, lean_object* v_x_3622_, lean_object* v_x_3623_){
_start:
{
lean_object* v___x_3624_; 
v___x_3624_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_x_3622_, v_x_3623_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(uint8_t v___x_3625_, lean_object* v_as_3626_, size_t v_sz_3627_, size_t v_i_3628_, lean_object* v_b_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
lean_object* v___x_3633_; 
v___x_3633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_3625_, v_as_3626_, v_sz_3627_, v_i_3628_, v_b_3629_, v___y_3630_);
return v___x_3633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___boxed(lean_object* v___x_3634_, lean_object* v_as_3635_, lean_object* v_sz_3636_, lean_object* v_i_3637_, lean_object* v_b_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
uint8_t v___x_41128__boxed_3642_; size_t v_sz_boxed_3643_; size_t v_i_boxed_3644_; lean_object* v_res_3645_; 
v___x_41128__boxed_3642_ = lean_unbox(v___x_3634_);
v_sz_boxed_3643_ = lean_unbox_usize(v_sz_3636_);
lean_dec(v_sz_3636_);
v_i_boxed_3644_ = lean_unbox_usize(v_i_3637_);
lean_dec(v_i_3637_);
v_res_3645_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(v___x_41128__boxed_3642_, v_as_3635_, v_sz_boxed_3643_, v_i_boxed_3644_, v_b_3638_, v___y_3639_, v___y_3640_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec_ref(v_as_3635_);
return v_res_3645_;
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
