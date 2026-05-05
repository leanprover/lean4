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
uint8_t v___x_36303__boxed_479_; uint8_t v___y_36305__boxed_480_; uint8_t v___x_36307__boxed_481_; uint8_t v___x_36308__boxed_482_; lean_object* v_res_483_; 
v___x_36303__boxed_479_ = lean_unbox(v___x_471_);
v___y_36305__boxed_480_ = lean_unbox(v___y_473_);
v___x_36307__boxed_481_ = lean_unbox(v___x_476_);
v___x_36308__boxed_482_ = lean_unbox(v___x_477_);
v_res_483_ = l_main___lam__0(v___x_469_, v___x_470_, v___x_36303__boxed_479_, v___x_472_, v___y_36305__boxed_480_, v_name_474_, v___x_475_, v___x_36307__boxed_481_, v___x_36308__boxed_482_);
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
uint8_t v___x_36393__boxed_592_; uint8_t v___x_36394__boxed_593_; lean_object* v_res_594_; 
v___x_36393__boxed_592_ = lean_unbox(v___x_589_);
v___x_36394__boxed_593_ = lean_unbox(v___x_590_);
v_res_594_ = l_main___lam__1(v___x_574_, v___x_575_, v___x_576_, v_name_577_, v_a_578_, v___x_579_, v_head_580_, v___x_581_, v___x_582_, v___x_583_, v___x_584_, v___x_585_, v___x_586_, v___x_587_, v___x_588_, v___x_36393__boxed_592_, v___x_36394__boxed_593_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(lean_object* v_as_742_, size_t v_sz_743_, size_t v_i_744_, lean_object* v_b_745_, lean_object* v___y_746_){
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
v___x_754_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___boxed(lean_object* v_as_771_, lean_object* v_sz_772_, lean_object* v_i_773_, lean_object* v_b_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
size_t v_sz_boxed_777_; size_t v_i_boxed_778_; lean_object* v_res_779_; 
v_sz_boxed_777_ = lean_unbox_usize(v_sz_772_);
lean_dec(v_sz_772_);
v_i_boxed_778_ = lean_unbox_usize(v_i_773_);
lean_dec(v_i_773_);
v_res_779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_771_, v_sz_boxed_777_, v_i_boxed_778_, v_b_774_, v___y_775_);
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
v___x_793_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_794_ = ((size_t)1ULL);
v___x_795_ = lean_usize_add(v_i_782_, v___x_794_);
v___x_796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_780_, v_sz_781_, v___x_795_, v___x_793_, v___y_784_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(lean_object* v_as_823_, size_t v_sz_824_, size_t v_i_825_, lean_object* v_b_826_, lean_object* v___y_827_){
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
v___x_835_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___boxed(lean_object* v_as_852_, lean_object* v_sz_853_, lean_object* v_i_854_, lean_object* v_b_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
size_t v_sz_boxed_858_; size_t v_i_boxed_859_; lean_object* v_res_860_; 
v_sz_boxed_858_ = lean_unbox_usize(v_sz_853_);
lean_dec(v_sz_853_);
v_i_boxed_859_ = lean_unbox_usize(v_i_854_);
lean_dec(v_i_854_);
v_res_860_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_852_, v_sz_boxed_858_, v_i_boxed_859_, v_b_855_, v___y_856_);
lean_dec_ref(v___y_856_);
lean_dec_ref(v_as_852_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(lean_object* v_as_861_, size_t v_sz_862_, size_t v_i_863_, lean_object* v_b_864_, lean_object* v___y_865_, lean_object* v___y_866_){
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
v___x_874_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_875_ = ((size_t)1ULL);
v___x_876_ = lean_usize_add(v_i_863_, v___x_875_);
v___x_877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_861_, v_sz_862_, v___x_876_, v___x_874_, v___y_865_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38___boxed(lean_object* v_as_891_, lean_object* v_sz_892_, lean_object* v_i_893_, lean_object* v_b_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
size_t v_sz_boxed_898_; size_t v_i_boxed_899_; lean_object* v_res_900_; 
v_sz_boxed_898_ = lean_unbox_usize(v_sz_892_);
lean_dec(v_sz_892_);
v_i_boxed_899_ = lean_unbox_usize(v_i_893_);
lean_dec(v_i_893_);
v_res_900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(v_as_891_, v_sz_boxed_898_, v_i_boxed_899_, v_b_894_, v___y_895_, v___y_896_);
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
v___x_912_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_init_901_, v_cs_907_, v_sz_910_, v___x_911_, v___x_909_, v___y_904_, v___y_905_);
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
v___x_941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(v_vs_936_, v_sz_939_, v___x_940_, v___x_938_, v___y_904_, v___y_905_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(lean_object* v_init_965_, lean_object* v_as_966_, size_t v_sz_967_, size_t v_i_968_, lean_object* v_b_969_, lean_object* v___y_970_, lean_object* v___y_971_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37___boxed(lean_object* v_init_1011_, lean_object* v_as_1012_, lean_object* v_sz_1013_, lean_object* v_i_1014_, lean_object* v_b_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
size_t v_sz_boxed_1019_; size_t v_i_boxed_1020_; lean_object* v_res_1021_; 
v_sz_boxed_1019_ = lean_unbox_usize(v_sz_1013_);
lean_dec(v_sz_1013_);
v_i_boxed_1020_ = lean_unbox_usize(v_i_1014_);
lean_dec(v_i_1014_);
v_res_1021_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_init_1011_, v_as_1012_, v_sz_boxed_1019_, v_i_boxed_1020_, v_b_1015_, v___y_1016_, v___y_1017_);
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
uint8_t v___x_37260__boxed_1127_; uint8_t v_suppressElabErrors_boxed_1128_; uint8_t v_res_1129_; lean_object* v_r_1130_; 
v___x_37260__boxed_1127_ = lean_unbox(v___x_1123_);
v_suppressElabErrors_boxed_1128_ = lean_unbox(v_suppressElabErrors_1124_);
v_res_1129_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(v___x_37260__boxed_1127_, v_suppressElabErrors_boxed_1128_, v___x_1125_, v_x_1126_);
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
uint8_t v___x_37333__boxed_1236_; size_t v_sz_boxed_1237_; size_t v_i_boxed_1238_; lean_object* v_res_1239_; 
v___x_37333__boxed_1236_ = lean_unbox(v___x_1228_);
v_sz_boxed_1237_ = lean_unbox_usize(v_sz_1230_);
lean_dec(v_sz_1230_);
v_i_boxed_1238_ = lean_unbox_usize(v_i_1231_);
lean_dec(v_i_1231_);
v_res_1239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_37333__boxed_1236_, v_as_1229_, v_sz_boxed_1237_, v_i_boxed_1238_, v_b_1232_, v___y_1233_, v___y_1234_);
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
uint8_t v___x_37813__boxed_1509_; size_t v_sz_boxed_1510_; size_t v_i_boxed_1511_; lean_object* v_res_1512_; 
v___x_37813__boxed_1509_ = lean_unbox(v___x_1502_);
v_sz_boxed_1510_ = lean_unbox_usize(v_sz_1504_);
lean_dec(v_sz_1504_);
v_i_boxed_1511_ = lean_unbox_usize(v_i_1505_);
lean_dec(v_i_1505_);
v_res_1512_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_37813__boxed_1509_, v_as_1503_, v_sz_boxed_1510_, v_i_boxed_1511_, v_b_1506_, v___y_1507_);
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
uint8_t v___x_37894__boxed_1570_; size_t v_sz_boxed_1571_; size_t v_i_boxed_1572_; lean_object* v_res_1573_; 
v___x_37894__boxed_1570_ = lean_unbox(v___x_1562_);
v_sz_boxed_1571_ = lean_unbox_usize(v_sz_1564_);
lean_dec(v_sz_1564_);
v_i_boxed_1572_ = lean_unbox_usize(v_i_1565_);
lean_dec(v_i_1565_);
v_res_1573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_37894__boxed_1570_, v_as_1563_, v_sz_boxed_1571_, v_i_boxed_1572_, v_b_1566_, v___y_1567_, v___y_1568_);
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
uint8_t v___x_37975__boxed_1695_; size_t v_sz_boxed_1696_; size_t v_i_boxed_1697_; lean_object* v_res_1698_; 
v___x_37975__boxed_1695_ = lean_unbox(v___x_1687_);
v_sz_boxed_1696_ = lean_unbox_usize(v_sz_1689_);
lean_dec(v_sz_1689_);
v_i_boxed_1697_ = lean_unbox_usize(v_i_1690_);
lean_dec(v_i_1690_);
v_res_1698_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_1686_, v___x_37975__boxed_1695_, v_as_1688_, v_sz_boxed_1696_, v_i_boxed_1697_, v_b_1691_, v___y_1692_, v___y_1693_);
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
uint8_t v___x_37995__boxed_1706_; lean_object* v_res_1707_; 
v___x_37995__boxed_1706_ = lean_unbox(v___x_1700_);
v_res_1707_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1699_, v___x_37995__boxed_1706_, v_n_1701_, v_b_1702_, v___y_1703_, v___y_1704_);
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
uint8_t v___x_38178__boxed_1763_; size_t v_sz_boxed_1764_; size_t v_i_boxed_1765_; lean_object* v_res_1766_; 
v___x_38178__boxed_1763_ = lean_unbox(v___x_1756_);
v_sz_boxed_1764_ = lean_unbox_usize(v_sz_1758_);
lean_dec(v_sz_1758_);
v_i_boxed_1765_ = lean_unbox_usize(v_i_1759_);
lean_dec(v_i_1759_);
v_res_1766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_38178__boxed_1763_, v_as_1757_, v_sz_boxed_1764_, v_i_boxed_1765_, v_b_1760_, v___y_1761_);
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
uint8_t v___x_38258__boxed_1824_; size_t v_sz_boxed_1825_; size_t v_i_boxed_1826_; lean_object* v_res_1827_; 
v___x_38258__boxed_1824_ = lean_unbox(v___x_1816_);
v_sz_boxed_1825_ = lean_unbox_usize(v_sz_1818_);
lean_dec(v_sz_1818_);
v_i_boxed_1826_ = lean_unbox_usize(v_i_1819_);
lean_dec(v_i_1819_);
v_res_1827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_38258__boxed_1824_, v_as_1817_, v_sz_boxed_1825_, v_i_boxed_1826_, v_b_1820_, v___y_1821_, v___y_1822_);
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
uint8_t v___x_38339__boxed_1888_; lean_object* v_res_1889_; 
v___x_38339__boxed_1888_ = lean_unbox(v___x_1882_);
v_res_1889_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_38339__boxed_1888_, v_t_1883_, v_init_1884_, v___y_1885_, v___y_1886_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(lean_object* v_hi_1964_, lean_object* v_pivot_1965_, lean_object* v_as_1966_, lean_object* v_i_1967_, lean_object* v_k_1968_){
_start:
{
uint8_t v___x_1969_; 
v___x_1969_ = lean_nat_dec_lt(v_k_1968_, v_hi_1964_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
lean_dec(v_k_1968_);
v___x_1970_ = lean_array_fswap(v_as_1966_, v_i_1967_, v_hi_1964_);
v___x_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1971_, 0, v_i_1967_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
return v___x_1971_;
}
else
{
lean_object* v___x_1972_; lean_object* v_fst_1973_; lean_object* v_fst_1974_; lean_object* v_fst_1975_; lean_object* v_fst_1976_; uint8_t v___x_1977_; 
v___x_1972_ = lean_array_fget_borrowed(v_as_1966_, v_k_1968_);
v_fst_1973_ = lean_ctor_get(v___x_1972_, 0);
v_fst_1974_ = lean_ctor_get(v_pivot_1965_, 0);
v_fst_1975_ = lean_ctor_get(v_fst_1973_, 0);
v_fst_1976_ = lean_ctor_get(v_fst_1974_, 0);
v___x_1977_ = lean_nat_dec_lt(v_fst_1975_, v_fst_1976_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = lean_unsigned_to_nat(1u);
v___x_1979_ = lean_nat_add(v_k_1968_, v___x_1978_);
lean_dec(v_k_1968_);
v_k_1968_ = v___x_1979_;
goto _start;
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1981_ = lean_array_fswap(v_as_1966_, v_i_1967_, v_k_1968_);
v___x_1982_ = lean_unsigned_to_nat(1u);
v___x_1983_ = lean_nat_add(v_i_1967_, v___x_1982_);
lean_dec(v_i_1967_);
v___x_1984_ = lean_nat_add(v_k_1968_, v___x_1982_);
lean_dec(v_k_1968_);
v_as_1966_ = v___x_1981_;
v_i_1967_ = v___x_1983_;
v_k_1968_ = v___x_1984_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg___boxed(lean_object* v_hi_1986_, lean_object* v_pivot_1987_, lean_object* v_as_1988_, lean_object* v_i_1989_, lean_object* v_k_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_1986_, v_pivot_1987_, v_as_1988_, v_i_1989_, v_k_1990_);
lean_dec_ref(v_pivot_1987_);
lean_dec(v_hi_1986_);
return v_res_1991_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(lean_object* v_x_1992_, lean_object* v_x_1993_){
_start:
{
lean_object* v_fst_1994_; lean_object* v_fst_1995_; lean_object* v_fst_1996_; lean_object* v_fst_1997_; uint8_t v___x_1998_; 
v_fst_1994_ = lean_ctor_get(v_x_1992_, 0);
v_fst_1995_ = lean_ctor_get(v_x_1993_, 0);
v_fst_1996_ = lean_ctor_get(v_fst_1994_, 0);
v_fst_1997_ = lean_ctor_get(v_fst_1995_, 0);
v___x_1998_ = lean_nat_dec_lt(v_fst_1996_, v_fst_1997_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0___boxed(lean_object* v_x_1999_, lean_object* v_x_2000_){
_start:
{
uint8_t v_res_2001_; lean_object* v_r_2002_; 
v_res_2001_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v_x_1999_, v_x_2000_);
lean_dec_ref(v_x_2000_);
lean_dec_ref(v_x_1999_);
v_r_2002_ = lean_box(v_res_2001_);
return v_r_2002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(lean_object* v_n_2003_, lean_object* v_as_2004_, lean_object* v_lo_2005_, lean_object* v_hi_2006_){
_start:
{
lean_object* v___y_2008_; uint8_t v___x_2018_; 
v___x_2018_ = lean_nat_dec_lt(v_lo_2005_, v_hi_2006_);
if (v___x_2018_ == 0)
{
lean_dec(v_lo_2005_);
return v_as_2004_;
}
else
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v_mid_2021_; lean_object* v___y_2023_; lean_object* v___y_2029_; lean_object* v___x_2034_; lean_object* v___x_2035_; uint8_t v___x_2036_; 
v___x_2019_ = lean_nat_add(v_lo_2005_, v_hi_2006_);
v___x_2020_ = lean_unsigned_to_nat(1u);
v_mid_2021_ = lean_nat_shiftr(v___x_2019_, v___x_2020_);
lean_dec(v___x_2019_);
v___x_2034_ = lean_array_fget_borrowed(v_as_2004_, v_mid_2021_);
v___x_2035_ = lean_array_fget_borrowed(v_as_2004_, v_lo_2005_);
v___x_2036_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2034_, v___x_2035_);
if (v___x_2036_ == 0)
{
v___y_2029_ = v_as_2004_;
goto v___jp_2028_;
}
else
{
lean_object* v___x_2037_; 
v___x_2037_ = lean_array_fswap(v_as_2004_, v_lo_2005_, v_mid_2021_);
v___y_2029_ = v___x_2037_;
goto v___jp_2028_;
}
v___jp_2022_:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; uint8_t v___x_2026_; 
v___x_2024_ = lean_array_fget_borrowed(v___y_2023_, v_mid_2021_);
v___x_2025_ = lean_array_fget_borrowed(v___y_2023_, v_hi_2006_);
v___x_2026_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2024_, v___x_2025_);
if (v___x_2026_ == 0)
{
lean_dec(v_mid_2021_);
v___y_2008_ = v___y_2023_;
goto v___jp_2007_;
}
else
{
lean_object* v___x_2027_; 
v___x_2027_ = lean_array_fswap(v___y_2023_, v_mid_2021_, v_hi_2006_);
lean_dec(v_mid_2021_);
v___y_2008_ = v___x_2027_;
goto v___jp_2007_;
}
}
v___jp_2028_:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; uint8_t v___x_2032_; 
v___x_2030_ = lean_array_fget_borrowed(v___y_2029_, v_hi_2006_);
v___x_2031_ = lean_array_fget_borrowed(v___y_2029_, v_lo_2005_);
v___x_2032_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2030_, v___x_2031_);
if (v___x_2032_ == 0)
{
v___y_2023_ = v___y_2029_;
goto v___jp_2022_;
}
else
{
lean_object* v___x_2033_; 
v___x_2033_ = lean_array_fswap(v___y_2029_, v_lo_2005_, v_hi_2006_);
v___y_2023_ = v___x_2033_;
goto v___jp_2022_;
}
}
}
v___jp_2007_:
{
lean_object* v_pivot_2009_; lean_object* v___x_2010_; lean_object* v_fst_2011_; lean_object* v_snd_2012_; uint8_t v___x_2013_; 
v_pivot_2009_ = lean_array_fget(v___y_2008_, v_hi_2006_);
lean_inc_n(v_lo_2005_, 2);
v___x_2010_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_2006_, v_pivot_2009_, v___y_2008_, v_lo_2005_, v_lo_2005_);
lean_dec(v_pivot_2009_);
v_fst_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_fst_2011_);
v_snd_2012_ = lean_ctor_get(v___x_2010_, 1);
lean_inc(v_snd_2012_);
lean_dec_ref(v___x_2010_);
v___x_2013_ = lean_nat_dec_le(v_hi_2006_, v_fst_2011_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2014_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_2003_, v_snd_2012_, v_lo_2005_, v_fst_2011_);
v___x_2015_ = lean_unsigned_to_nat(1u);
v___x_2016_ = lean_nat_add(v_fst_2011_, v___x_2015_);
lean_dec(v_fst_2011_);
v_as_2004_ = v___x_2014_;
v_lo_2005_ = v___x_2016_;
goto _start;
}
else
{
lean_dec(v_fst_2011_);
lean_dec(v_lo_2005_);
return v_snd_2012_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___boxed(lean_object* v_n_2038_, lean_object* v_as_2039_, lean_object* v_lo_2040_, lean_object* v_hi_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_2038_, v_as_2039_, v_lo_2040_, v_hi_2041_);
lean_dec(v_hi_2041_);
lean_dec(v_n_2038_);
return v_res_2042_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2043_ = lean_box(0);
v___x_2044_ = lean_unsigned_to_nat(16u);
v___x_2045_ = lean_mk_array(v___x_2044_, v___x_2043_);
return v___x_2045_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v_pos2traces_2048_; 
v___x_2046_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0);
v___x_2047_ = lean_unsigned_to_nat(0u);
v_pos2traces_2048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_2048_, 0, v___x_2047_);
lean_ctor_set(v_pos2traces_2048_, 1, v___x_2046_);
return v_pos2traces_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10(lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v_options_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v_options_2052_ = lean_ctor_get(v___y_2049_, 2);
v___x_2053_ = l_Lean_trace_profiler_output;
v___x_2054_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(v_options_2052_, v___x_2053_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v___x_2055_; lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2122_; 
v___x_2055_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_2050_);
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2122_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2122_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
uint8_t v___x_2060_; 
v___x_2060_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_2056_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2061_; lean_object* v_pos2traces_2062_; lean_object* v___x_2063_; 
lean_del_object(v___x_2058_);
v___x_2061_ = lean_unsigned_to_nat(0u);
v_pos2traces_2062_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1);
v___x_2063_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_2060_, v_a_2056_, v_pos2traces_2062_, v___y_2049_, v___y_2050_);
lean_dec(v_a_2056_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; lean_object* v___y_2066_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2089_; lean_object* v___y_2092_; lean_object* v_size_2098_; lean_object* v_buckets_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; uint8_t v___x_2102_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref(v___x_2063_);
v_size_2098_ = lean_ctor_get(v_a_2064_, 0);
lean_inc(v_size_2098_);
v_buckets_2099_ = lean_ctor_get(v_a_2064_, 1);
lean_inc_ref(v_buckets_2099_);
lean_dec(v_a_2064_);
v___x_2100_ = lean_mk_empty_array_with_capacity(v_size_2098_);
lean_dec(v_size_2098_);
v___x_2101_ = lean_array_get_size(v_buckets_2099_);
v___x_2102_ = lean_nat_dec_lt(v___x_2061_, v___x_2101_);
if (v___x_2102_ == 0)
{
lean_dec_ref(v_buckets_2099_);
v___y_2092_ = v___x_2100_;
goto v___jp_2091_;
}
else
{
uint8_t v___x_2103_; 
v___x_2103_ = lean_nat_dec_le(v___x_2101_, v___x_2101_);
if (v___x_2103_ == 0)
{
if (v___x_2102_ == 0)
{
lean_dec_ref(v_buckets_2099_);
v___y_2092_ = v___x_2100_;
goto v___jp_2091_;
}
else
{
size_t v___x_2104_; size_t v___x_2105_; lean_object* v___x_2106_; 
v___x_2104_ = ((size_t)0ULL);
v___x_2105_ = lean_usize_of_nat(v___x_2101_);
v___x_2106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_buckets_2099_, v___x_2104_, v___x_2105_, v___x_2100_);
lean_dec_ref(v_buckets_2099_);
v___y_2092_ = v___x_2106_;
goto v___jp_2091_;
}
}
else
{
size_t v___x_2107_; size_t v___x_2108_; lean_object* v___x_2109_; 
v___x_2107_ = ((size_t)0ULL);
v___x_2108_ = lean_usize_of_nat(v___x_2101_);
v___x_2109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_buckets_2099_, v___x_2107_, v___x_2108_, v___x_2100_);
lean_dec_ref(v_buckets_2099_);
v___y_2092_ = v___x_2109_;
goto v___jp_2091_;
}
}
v___jp_2065_:
{
lean_object* v___x_2067_; size_t v_sz_2068_; size_t v___x_2069_; lean_object* v___x_2070_; 
v___x_2067_ = lean_box(0);
v_sz_2068_ = lean_array_size(v___y_2066_);
v___x_2069_ = ((size_t)0ULL);
v___x_2070_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_2060_, v___y_2066_, v_sz_2068_, v___x_2069_, v___x_2067_, v___y_2049_, v___y_2050_);
lean_dec_ref(v___y_2066_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2077_ == 0)
{
lean_object* v_unused_2078_; 
v_unused_2078_ = lean_ctor_get(v___x_2070_, 0);
lean_dec(v_unused_2078_);
v___x_2072_ = v___x_2070_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_dec(v___x_2070_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 0, v___x_2067_);
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2067_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
else
{
return v___x_2070_;
}
}
v___jp_2079_:
{
lean_object* v___x_2084_; 
v___x_2084_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v___y_2082_, v___y_2081_, v___y_2080_, v___y_2083_);
lean_dec(v___y_2083_);
lean_dec(v___y_2082_);
v___y_2066_ = v___x_2084_;
goto v___jp_2065_;
}
v___jp_2085_:
{
uint8_t v___x_2090_; 
v___x_2090_ = lean_nat_dec_le(v___y_2089_, v___y_2087_);
if (v___x_2090_ == 0)
{
lean_dec(v___y_2087_);
lean_inc(v___y_2089_);
v___y_2080_ = v___y_2089_;
v___y_2081_ = v___y_2086_;
v___y_2082_ = v___y_2088_;
v___y_2083_ = v___y_2089_;
goto v___jp_2079_;
}
else
{
v___y_2080_ = v___y_2089_;
v___y_2081_ = v___y_2086_;
v___y_2082_ = v___y_2088_;
v___y_2083_ = v___y_2087_;
goto v___jp_2079_;
}
}
v___jp_2091_:
{
lean_object* v___x_2093_; uint8_t v___x_2094_; 
v___x_2093_ = lean_array_get_size(v___y_2092_);
v___x_2094_ = lean_nat_dec_eq(v___x_2093_, v___x_2061_);
if (v___x_2094_ == 0)
{
lean_object* v___x_2095_; lean_object* v___x_2096_; uint8_t v___x_2097_; 
v___x_2095_ = lean_unsigned_to_nat(1u);
v___x_2096_ = lean_nat_sub(v___x_2093_, v___x_2095_);
v___x_2097_ = lean_nat_dec_le(v___x_2061_, v___x_2096_);
if (v___x_2097_ == 0)
{
lean_inc(v___x_2096_);
v___y_2086_ = v___y_2092_;
v___y_2087_ = v___x_2096_;
v___y_2088_ = v___x_2093_;
v___y_2089_ = v___x_2096_;
goto v___jp_2085_;
}
else
{
v___y_2086_ = v___y_2092_;
v___y_2087_ = v___x_2096_;
v___y_2088_ = v___x_2093_;
v___y_2089_ = v___x_2061_;
goto v___jp_2085_;
}
}
else
{
v___y_2066_ = v___y_2092_;
goto v___jp_2065_;
}
}
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
v_a_2110_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2063_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2063_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
else
{
lean_object* v___x_2118_; lean_object* v___x_2120_; 
lean_dec(v_a_2056_);
v___x_2118_ = lean_box(0);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v___x_2118_);
v___x_2120_ = v___x_2058_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2118_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
else
{
lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2130_; 
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2130_ == 0)
{
lean_object* v_unused_2131_; 
v_unused_2131_ = lean_ctor_get(v___x_2054_, 0);
lean_dec(v_unused_2131_);
v___x_2124_ = v___x_2054_;
v_isShared_2125_ = v_isSharedCheck_2130_;
goto v_resetjp_2123_;
}
else
{
lean_dec(v___x_2054_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2130_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; lean_object* v___x_2128_; 
v___x_2126_ = lean_box(0);
if (v_isShared_2125_ == 0)
{
lean_ctor_set_tag(v___x_2124_, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2126_);
v___x_2128_ = v___x_2124_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
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
uint8_t v___y_38951__boxed_2262_; uint8_t v_suppressElabErrors_boxed_2263_; uint8_t v_res_2264_; lean_object* v_r_2265_; 
v___y_38951__boxed_2262_ = lean_unbox(v___y_2259_);
v_suppressElabErrors_boxed_2263_ = lean_unbox(v_suppressElabErrors_2260_);
v_res_2264_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0(v___y_38951__boxed_2262_, v_suppressElabErrors_boxed_2263_, v_x_2261_);
lean_dec(v_x_2261_);
v_r_2265_ = lean_box(v_res_2264_);
return v_r_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(lean_object* v_ref_2266_, lean_object* v_msgData_2267_, uint8_t v_severity_2268_, uint8_t v_isSilent_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v___y_2274_; uint8_t v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; uint8_t v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2312_; uint8_t v___y_2313_; uint8_t v___y_2314_; lean_object* v___y_2315_; uint8_t v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2335_; lean_object* v___y_2336_; uint8_t v___y_2337_; uint8_t v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; uint8_t v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___y_2348_; uint8_t v___y_2349_; lean_object* v___y_2350_; uint8_t v___y_2351_; uint8_t v___y_2352_; uint8_t v___x_2357_; lean_object* v___y_2359_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2362_; uint8_t v___y_2363_; uint8_t v___y_2364_; uint8_t v___y_2365_; uint8_t v___y_2367_; uint8_t v___x_2382_; 
v___x_2357_ = 2;
v___x_2382_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2268_, v___x_2357_);
if (v___x_2382_ == 0)
{
v___y_2367_ = v___x_2382_;
goto v___jp_2366_;
}
else
{
uint8_t v___x_2383_; 
lean_inc_ref(v_msgData_2267_);
v___x_2383_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2267_);
v___y_2367_ = v___x_2383_;
goto v___jp_2366_;
}
v___jp_2273_:
{
lean_object* v___x_2283_; lean_object* v_currNamespace_2284_; lean_object* v_openDecls_2285_; lean_object* v_env_2286_; lean_object* v_nextMacroScope_2287_; lean_object* v_ngen_2288_; lean_object* v_auxDeclNGen_2289_; lean_object* v_traceState_2290_; lean_object* v_cache_2291_; lean_object* v_messages_2292_; lean_object* v_infoState_2293_; lean_object* v_snapshotTasks_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2308_; 
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
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2296_ = v___x_2283_;
v_isShared_2297_ = v_isSharedCheck_2308_;
goto v_resetjp_2295_;
}
else
{
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
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2308_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2303_; 
lean_inc(v_openDecls_2285_);
lean_inc(v_currNamespace_2284_);
v___x_2298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2298_, 0, v_currNamespace_2284_);
lean_ctor_set(v___x_2298_, 1, v_openDecls_2285_);
v___x_2299_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
lean_ctor_set(v___x_2299_, 1, v___y_2278_);
lean_inc_ref(v___y_2280_);
lean_inc_ref(v___y_2274_);
v___x_2300_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2300_, 0, v___y_2274_);
lean_ctor_set(v___x_2300_, 1, v___y_2276_);
lean_ctor_set(v___x_2300_, 2, v___y_2277_);
lean_ctor_set(v___x_2300_, 3, v___y_2280_);
lean_ctor_set(v___x_2300_, 4, v___x_2299_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*5, v___y_2279_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*5 + 1, v___y_2275_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*5 + 2, v_isSilent_2269_);
v___x_2301_ = l_Lean_MessageLog_add(v___x_2300_, v_messages_2292_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 6, v___x_2301_);
v___x_2303_ = v___x_2296_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_env_2286_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v_nextMacroScope_2287_);
lean_ctor_set(v_reuseFailAlloc_2307_, 2, v_ngen_2288_);
lean_ctor_set(v_reuseFailAlloc_2307_, 3, v_auxDeclNGen_2289_);
lean_ctor_set(v_reuseFailAlloc_2307_, 4, v_traceState_2290_);
lean_ctor_set(v_reuseFailAlloc_2307_, 5, v_cache_2291_);
lean_ctor_set(v_reuseFailAlloc_2307_, 6, v___x_2301_);
lean_ctor_set(v_reuseFailAlloc_2307_, 7, v_infoState_2293_);
lean_ctor_set(v_reuseFailAlloc_2307_, 8, v_snapshotTasks_2294_);
v___x_2303_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2304_ = lean_st_ref_set(v___y_2282_, v___x_2303_);
v___x_2305_ = lean_box(0);
v___x_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
return v___x_2306_;
}
}
}
v___jp_2309_:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2333_; 
v___x_2318_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2267_);
v___x_2319_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v___x_2318_, v___y_2270_, v___y_2271_);
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2322_ = v___x_2319_;
v_isShared_2323_ = v_isSharedCheck_2333_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2319_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2333_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
lean_inc_ref_n(v___y_2315_, 2);
v___x_2324_ = l_Lean_FileMap_toPosition(v___y_2315_, v___y_2311_);
lean_dec(v___y_2311_);
v___x_2325_ = l_Lean_FileMap_toPosition(v___y_2315_, v___y_2317_);
lean_dec(v___y_2317_);
v___x_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
v___x_2327_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1));
if (v___y_2316_ == 0)
{
lean_del_object(v___x_2322_);
lean_dec_ref(v___y_2310_);
v___y_2274_ = v___y_2312_;
v___y_2275_ = v___y_2313_;
v___y_2276_ = v___x_2324_;
v___y_2277_ = v___x_2326_;
v___y_2278_ = v_a_2320_;
v___y_2279_ = v___y_2314_;
v___y_2280_ = v___x_2327_;
v___y_2281_ = v___y_2270_;
v___y_2282_ = v___y_2271_;
goto v___jp_2273_;
}
else
{
uint8_t v___x_2328_; 
lean_inc(v_a_2320_);
v___x_2328_ = l_Lean_MessageData_hasTag(v___y_2310_, v_a_2320_);
if (v___x_2328_ == 0)
{
lean_object* v___x_2329_; lean_object* v___x_2331_; 
lean_dec_ref(v___x_2326_);
lean_dec_ref(v___x_2324_);
lean_dec(v_a_2320_);
v___x_2329_ = lean_box(0);
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 0, v___x_2329_);
v___x_2331_ = v___x_2322_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
else
{
lean_del_object(v___x_2322_);
v___y_2274_ = v___y_2312_;
v___y_2275_ = v___y_2313_;
v___y_2276_ = v___x_2324_;
v___y_2277_ = v___x_2326_;
v___y_2278_ = v_a_2320_;
v___y_2279_ = v___y_2314_;
v___y_2280_ = v___x_2327_;
v___y_2281_ = v___y_2270_;
v___y_2282_ = v___y_2271_;
goto v___jp_2273_;
}
}
}
}
v___jp_2334_:
{
lean_object* v___x_2343_; 
v___x_2343_ = l_Lean_Syntax_getTailPos_x3f(v___y_2340_, v___y_2338_);
lean_dec(v___y_2340_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_inc(v___y_2342_);
v___y_2310_ = v___y_2335_;
v___y_2311_ = v___y_2342_;
v___y_2312_ = v___y_2336_;
v___y_2313_ = v___y_2337_;
v___y_2314_ = v___y_2338_;
v___y_2315_ = v___y_2339_;
v___y_2316_ = v___y_2341_;
v___y_2317_ = v___y_2342_;
goto v___jp_2309_;
}
else
{
lean_object* v_val_2344_; 
v_val_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_val_2344_);
lean_dec_ref(v___x_2343_);
v___y_2310_ = v___y_2335_;
v___y_2311_ = v___y_2342_;
v___y_2312_ = v___y_2336_;
v___y_2313_ = v___y_2337_;
v___y_2314_ = v___y_2338_;
v___y_2315_ = v___y_2339_;
v___y_2316_ = v___y_2341_;
v___y_2317_ = v_val_2344_;
goto v___jp_2309_;
}
}
v___jp_2345_:
{
lean_object* v_ref_2353_; lean_object* v___x_2354_; 
v_ref_2353_ = l_Lean_replaceRef(v_ref_2266_, v___y_2348_);
v___x_2354_ = l_Lean_Syntax_getPos_x3f(v_ref_2353_, v___y_2349_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v___x_2355_; 
v___x_2355_ = lean_unsigned_to_nat(0u);
v___y_2335_ = v___y_2346_;
v___y_2336_ = v___y_2347_;
v___y_2337_ = v___y_2352_;
v___y_2338_ = v___y_2349_;
v___y_2339_ = v___y_2350_;
v___y_2340_ = v_ref_2353_;
v___y_2341_ = v___y_2351_;
v___y_2342_ = v___x_2355_;
goto v___jp_2334_;
}
else
{
lean_object* v_val_2356_; 
v_val_2356_ = lean_ctor_get(v___x_2354_, 0);
lean_inc(v_val_2356_);
lean_dec_ref(v___x_2354_);
v___y_2335_ = v___y_2346_;
v___y_2336_ = v___y_2347_;
v___y_2337_ = v___y_2352_;
v___y_2338_ = v___y_2349_;
v___y_2339_ = v___y_2350_;
v___y_2340_ = v_ref_2353_;
v___y_2341_ = v___y_2351_;
v___y_2342_ = v_val_2356_;
goto v___jp_2334_;
}
}
v___jp_2358_:
{
if (v___y_2365_ == 0)
{
v___y_2346_ = v___y_2361_;
v___y_2347_ = v___y_2359_;
v___y_2348_ = v___y_2360_;
v___y_2349_ = v___y_2364_;
v___y_2350_ = v___y_2362_;
v___y_2351_ = v___y_2363_;
v___y_2352_ = v_severity_2268_;
goto v___jp_2345_;
}
else
{
v___y_2346_ = v___y_2361_;
v___y_2347_ = v___y_2359_;
v___y_2348_ = v___y_2360_;
v___y_2349_ = v___y_2364_;
v___y_2350_ = v___y_2362_;
v___y_2351_ = v___y_2363_;
v___y_2352_ = v___x_2357_;
goto v___jp_2345_;
}
}
v___jp_2366_:
{
if (v___y_2367_ == 0)
{
lean_object* v_fileName_2368_; lean_object* v_fileMap_2369_; lean_object* v_options_2370_; lean_object* v_ref_2371_; uint8_t v_suppressElabErrors_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___f_2375_; uint8_t v___x_2376_; uint8_t v___x_2377_; 
v_fileName_2368_ = lean_ctor_get(v___y_2270_, 0);
v_fileMap_2369_ = lean_ctor_get(v___y_2270_, 1);
v_options_2370_ = lean_ctor_get(v___y_2270_, 2);
v_ref_2371_ = lean_ctor_get(v___y_2270_, 5);
v_suppressElabErrors_2372_ = lean_ctor_get_uint8(v___y_2270_, sizeof(void*)*14 + 1);
v___x_2373_ = lean_box(v___y_2367_);
v___x_2374_ = lean_box(v_suppressElabErrors_2372_);
v___f_2375_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2375_, 0, v___x_2373_);
lean_closure_set(v___f_2375_, 1, v___x_2374_);
v___x_2376_ = 1;
v___x_2377_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2268_, v___x_2376_);
if (v___x_2377_ == 0)
{
v___y_2359_ = v_fileName_2368_;
v___y_2360_ = v_ref_2371_;
v___y_2361_ = v___f_2375_;
v___y_2362_ = v_fileMap_2369_;
v___y_2363_ = v_suppressElabErrors_2372_;
v___y_2364_ = v___y_2367_;
v___y_2365_ = v___x_2377_;
goto v___jp_2358_;
}
else
{
lean_object* v___x_2378_; uint8_t v___x_2379_; 
v___x_2378_ = l_Lean_warningAsError;
v___x_2379_ = l_Lean_Option_get___at___00main_spec__8(v_options_2370_, v___x_2378_);
v___y_2359_ = v_fileName_2368_;
v___y_2360_ = v_ref_2371_;
v___y_2361_ = v___f_2375_;
v___y_2362_ = v_fileMap_2369_;
v___y_2363_ = v_suppressElabErrors_2372_;
v___y_2364_ = v___y_2367_;
v___y_2365_ = v___x_2379_;
goto v___jp_2358_;
}
}
else
{
lean_object* v___x_2380_; lean_object* v___x_2381_; 
lean_dec_ref(v_msgData_2267_);
v___x_2380_ = lean_box(0);
v___x_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
return v___x_2381_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___boxed(lean_object* v_ref_2384_, lean_object* v_msgData_2385_, lean_object* v_severity_2386_, lean_object* v_isSilent_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
uint8_t v_severity_boxed_2391_; uint8_t v_isSilent_boxed_2392_; lean_object* v_res_2393_; 
v_severity_boxed_2391_ = lean_unbox(v_severity_2386_);
v_isSilent_boxed_2392_ = lean_unbox(v_isSilent_2387_);
v_res_2393_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(v_ref_2384_, v_msgData_2385_, v_severity_boxed_2391_, v_isSilent_boxed_2392_, v___y_2388_, v___y_2389_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec(v_ref_2384_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(lean_object* v_msgData_2394_, uint8_t v_severity_2395_, uint8_t v_isSilent_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v_ref_2400_; lean_object* v___x_2401_; 
v_ref_2400_ = lean_ctor_get(v___y_2397_, 5);
v___x_2401_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(v_ref_2400_, v_msgData_2394_, v_severity_2395_, v_isSilent_2396_, v___y_2397_, v___y_2398_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30___boxed(lean_object* v_msgData_2402_, lean_object* v_severity_2403_, lean_object* v_isSilent_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
uint8_t v_severity_boxed_2408_; uint8_t v_isSilent_boxed_2409_; lean_object* v_res_2410_; 
v_severity_boxed_2408_ = lean_unbox(v_severity_2403_);
v_isSilent_boxed_2409_ = lean_unbox(v_isSilent_2404_);
v_res_2410_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2402_, v_severity_boxed_2408_, v_isSilent_boxed_2409_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14(lean_object* v_msgData_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
uint8_t v___x_2415_; uint8_t v___x_2416_; lean_object* v___x_2417_; 
v___x_2415_ = 2;
v___x_2416_ = 0;
v___x_2417_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2411_, v___x_2415_, v___x_2416_, v___y_2412_, v___y_2413_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14___boxed(lean_object* v_msgData_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Lean_logError___at___00main_spec__14(v_msgData_2418_, v___y_2419_, v___y_2420_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(lean_object* v_x2_2423_, lean_object* v_as_2424_, size_t v_i_2425_, size_t v_stop_2426_, lean_object* v_b_2427_){
_start:
{
uint8_t v___x_2428_; 
v___x_2428_ = lean_usize_dec_eq(v_i_2425_, v_stop_2426_);
if (v___x_2428_ == 0)
{
lean_object* v___x_2429_; lean_object* v___x_2430_; size_t v___x_2431_; size_t v___x_2432_; 
v___x_2429_ = lean_array_uget_borrowed(v_as_2424_, v_i_2425_);
lean_inc_ref(v_x2_2423_);
lean_inc(v___x_2429_);
v___x_2430_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2429_, v_x2_2423_, v_b_2427_);
v___x_2431_ = ((size_t)1ULL);
v___x_2432_ = lean_usize_add(v_i_2425_, v___x_2431_);
v_i_2425_ = v___x_2432_;
v_b_2427_ = v___x_2430_;
goto _start;
}
else
{
lean_dec_ref(v_x2_2423_);
return v_b_2427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(lean_object* v_x2_2434_, lean_object* v_as_2435_, lean_object* v_i_2436_, lean_object* v_stop_2437_, lean_object* v_b_2438_){
_start:
{
size_t v_i_boxed_2439_; size_t v_stop_boxed_2440_; lean_object* v_res_2441_; 
v_i_boxed_2439_ = lean_unbox_usize(v_i_2436_);
lean_dec(v_i_2436_);
v_stop_boxed_2440_ = lean_unbox_usize(v_stop_2437_);
lean_dec(v_stop_2437_);
v_res_2441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v_x2_2434_, v_as_2435_, v_i_boxed_2439_, v_stop_boxed_2440_, v_b_2438_);
lean_dec_ref(v_as_2435_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object* v_as_2442_, size_t v_i_2443_, size_t v_stop_2444_, lean_object* v_b_2445_){
_start:
{
lean_object* v___y_2447_; uint8_t v___x_2451_; 
v___x_2451_ = lean_usize_dec_eq(v_i_2443_, v_stop_2444_);
if (v___x_2451_ == 0)
{
lean_object* v___x_2452_; lean_object* v_declNames_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; uint8_t v___x_2456_; 
v___x_2452_ = lean_array_uget_borrowed(v_as_2442_, v_i_2443_);
v_declNames_2453_ = lean_ctor_get(v___x_2452_, 0);
v___x_2454_ = lean_unsigned_to_nat(0u);
v___x_2455_ = lean_array_get_size(v_declNames_2453_);
v___x_2456_ = lean_nat_dec_lt(v___x_2454_, v___x_2455_);
if (v___x_2456_ == 0)
{
v___y_2447_ = v_b_2445_;
goto v___jp_2446_;
}
else
{
uint8_t v___x_2457_; 
v___x_2457_ = lean_nat_dec_le(v___x_2455_, v___x_2455_);
if (v___x_2457_ == 0)
{
if (v___x_2456_ == 0)
{
v___y_2447_ = v_b_2445_;
goto v___jp_2446_;
}
else
{
size_t v___x_2458_; size_t v___x_2459_; lean_object* v___x_2460_; 
v___x_2458_ = ((size_t)0ULL);
v___x_2459_ = lean_usize_of_nat(v___x_2455_);
lean_inc(v___x_2452_);
v___x_2460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2452_, v_declNames_2453_, v___x_2458_, v___x_2459_, v_b_2445_);
v___y_2447_ = v___x_2460_;
goto v___jp_2446_;
}
}
else
{
size_t v___x_2461_; size_t v___x_2462_; lean_object* v___x_2463_; 
v___x_2461_ = ((size_t)0ULL);
v___x_2462_ = lean_usize_of_nat(v___x_2455_);
lean_inc(v___x_2452_);
v___x_2463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2452_, v_declNames_2453_, v___x_2461_, v___x_2462_, v_b_2445_);
v___y_2447_ = v___x_2463_;
goto v___jp_2446_;
}
}
}
else
{
return v_b_2445_;
}
v___jp_2446_:
{
size_t v___x_2448_; size_t v___x_2449_; 
v___x_2448_ = ((size_t)1ULL);
v___x_2449_ = lean_usize_add(v_i_2443_, v___x_2448_);
v_i_2443_ = v___x_2449_;
v_b_2445_ = v___y_2447_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object* v_as_2464_, lean_object* v_i_2465_, lean_object* v_stop_2466_, lean_object* v_b_2467_){
_start:
{
size_t v_i_boxed_2468_; size_t v_stop_boxed_2469_; lean_object* v_res_2470_; 
v_i_boxed_2468_ = lean_unbox_usize(v_i_2465_);
lean_dec(v_i_2465_);
v_stop_boxed_2469_ = lean_unbox_usize(v_stop_2466_);
lean_dec(v_stop_2466_);
v_res_2470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v_as_2464_, v_i_boxed_2468_, v_stop_boxed_2469_, v_b_2467_);
lean_dec_ref(v_as_2464_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(lean_object* v_a_2471_, lean_object* v_as_2472_, size_t v_i_2473_, size_t v_stop_2474_, lean_object* v_b_2475_){
_start:
{
lean_object* v___y_2477_; uint8_t v___x_2481_; 
v___x_2481_ = lean_usize_dec_eq(v_i_2473_, v_stop_2474_);
if (v___x_2481_ == 0)
{
lean_object* v___x_2482_; lean_object* v_name_2483_; uint8_t v___x_2484_; 
v___x_2482_ = lean_array_uget_borrowed(v_as_2472_, v_i_2473_);
v_name_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_name_2483_);
lean_inc_ref(v_a_2471_);
v___x_2484_ = l_Lean_isExtern(v_a_2471_, v_name_2483_);
if (v___x_2484_ == 0)
{
v___y_2477_ = v_b_2475_;
goto v___jp_2476_;
}
else
{
lean_object* v___x_2485_; 
lean_inc(v___x_2482_);
v___x_2485_ = lean_array_push(v_b_2475_, v___x_2482_);
v___y_2477_ = v___x_2485_;
goto v___jp_2476_;
}
}
else
{
lean_dec_ref(v_a_2471_);
return v_b_2475_;
}
v___jp_2476_:
{
size_t v___x_2478_; size_t v___x_2479_; 
v___x_2478_ = ((size_t)1ULL);
v___x_2479_ = lean_usize_add(v_i_2473_, v___x_2478_);
v_i_2473_ = v___x_2479_;
v_b_2475_ = v___y_2477_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19___boxed(lean_object* v_a_2486_, lean_object* v_as_2487_, lean_object* v_i_2488_, lean_object* v_stop_2489_, lean_object* v_b_2490_){
_start:
{
size_t v_i_boxed_2491_; size_t v_stop_boxed_2492_; lean_object* v_res_2493_; 
v_i_boxed_2491_ = lean_unbox_usize(v_i_2488_);
lean_dec(v_i_2488_);
v_stop_boxed_2492_ = lean_unbox_usize(v_stop_2489_);
lean_dec(v_stop_2489_);
v_res_2493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_2486_, v_as_2487_, v_i_boxed_2491_, v_stop_boxed_2492_, v_b_2490_);
lean_dec_ref(v_as_2487_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(lean_object* v_as_2494_, size_t v_sz_2495_, size_t v_i_2496_, lean_object* v_b_2497_){
_start:
{
uint8_t v___x_2499_; 
v___x_2499_ = lean_usize_dec_lt(v_i_2496_, v_sz_2495_);
if (v___x_2499_ == 0)
{
lean_object* v___x_2500_; 
v___x_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2500_, 0, v_b_2497_);
return v___x_2500_;
}
else
{
uint8_t v___x_2501_; lean_object* v_a_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
lean_dec_ref(v_b_2497_);
v___x_2501_ = 0;
v_a_2502_ = lean_array_uget_borrowed(v_as_2494_, v_i_2496_);
lean_inc(v_a_2502_);
v___x_2503_ = l_Lean_Message_toString(v_a_2502_, v___x_2501_);
v___x_2504_ = l_IO_eprintln___at___00main_spec__6(v___x_2503_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v___x_2505_; size_t v___x_2506_; size_t v___x_2507_; 
lean_dec_ref(v___x_2504_);
v___x_2505_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_2506_ = ((size_t)1ULL);
v___x_2507_ = lean_usize_add(v_i_2496_, v___x_2506_);
v_i_2496_ = v___x_2507_;
v_b_2497_ = v___x_2505_;
goto _start;
}
else
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
v_a_2509_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v___x_2504_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2504_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27___boxed(lean_object* v_as_2517_, lean_object* v_sz_2518_, lean_object* v_i_2519_, lean_object* v_b_2520_, lean_object* v___y_2521_){
_start:
{
size_t v_sz_boxed_2522_; size_t v_i_boxed_2523_; lean_object* v_res_2524_; 
v_sz_boxed_2522_ = lean_unbox_usize(v_sz_2518_);
lean_dec(v_sz_2518_);
v_i_boxed_2523_ = lean_unbox_usize(v_i_2519_);
lean_dec(v_i_2519_);
v_res_2524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2517_, v_sz_boxed_2522_, v_i_boxed_2523_, v_b_2520_);
lean_dec_ref(v_as_2517_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(lean_object* v_as_2525_, size_t v_sz_2526_, size_t v_i_2527_, lean_object* v_b_2528_){
_start:
{
uint8_t v___x_2530_; 
v___x_2530_ = lean_usize_dec_lt(v_i_2527_, v_sz_2526_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; 
v___x_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2531_, 0, v_b_2528_);
return v___x_2531_;
}
else
{
uint8_t v___x_2532_; lean_object* v_a_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
lean_dec_ref(v_b_2528_);
v___x_2532_ = 0;
v_a_2533_ = lean_array_uget_borrowed(v_as_2525_, v_i_2527_);
lean_inc(v_a_2533_);
v___x_2534_ = l_Lean_Message_toString(v_a_2533_, v___x_2532_);
v___x_2535_ = l_IO_eprintln___at___00main_spec__6(v___x_2534_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v___x_2536_; size_t v___x_2537_; size_t v___x_2538_; lean_object* v___x_2539_; 
lean_dec_ref(v___x_2535_);
v___x_2536_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_2537_ = ((size_t)1ULL);
v___x_2538_ = lean_usize_add(v_i_2527_, v___x_2537_);
v___x_2539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2525_, v_sz_2526_, v___x_2538_, v___x_2536_);
return v___x_2539_;
}
else
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
v_a_2540_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2535_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2535_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14___boxed(lean_object* v_as_2548_, lean_object* v_sz_2549_, lean_object* v_i_2550_, lean_object* v_b_2551_, lean_object* v___y_2552_){
_start:
{
size_t v_sz_boxed_2553_; size_t v_i_boxed_2554_; lean_object* v_res_2555_; 
v_sz_boxed_2553_ = lean_unbox_usize(v_sz_2549_);
lean_dec(v_sz_2549_);
v_i_boxed_2554_ = lean_unbox_usize(v_i_2550_);
lean_dec(v_i_2550_);
v_res_2555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_as_2548_, v_sz_boxed_2553_, v_i_boxed_2554_, v_b_2551_);
lean_dec_ref(v_as_2548_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(lean_object* v_init_2556_, lean_object* v_n_2557_, lean_object* v_b_2558_){
_start:
{
if (lean_obj_tag(v_n_2557_) == 0)
{
lean_object* v_cs_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; size_t v_sz_2563_; size_t v___x_2564_; lean_object* v___x_2565_; 
v_cs_2560_ = lean_ctor_get(v_n_2557_, 0);
v___x_2561_ = lean_box(0);
v___x_2562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2561_);
lean_ctor_set(v___x_2562_, 1, v_b_2558_);
v_sz_2563_ = lean_array_size(v_cs_2560_);
v___x_2564_ = ((size_t)0ULL);
v___x_2565_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2556_, v_cs_2560_, v_sz_2563_, v___x_2564_, v___x_2562_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2580_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2568_ = v___x_2565_;
v_isShared_2569_ = v_isSharedCheck_2580_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2565_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2580_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v_fst_2570_; 
v_fst_2570_ = lean_ctor_get(v_a_2566_, 0);
if (lean_obj_tag(v_fst_2570_) == 0)
{
lean_object* v_snd_2571_; lean_object* v___x_2572_; lean_object* v___x_2574_; 
v_snd_2571_ = lean_ctor_get(v_a_2566_, 1);
lean_inc(v_snd_2571_);
lean_dec(v_a_2566_);
v___x_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2572_, 0, v_snd_2571_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v___x_2572_);
v___x_2574_ = v___x_2568_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v___x_2572_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
else
{
lean_object* v_val_2576_; lean_object* v___x_2578_; 
lean_inc_ref(v_fst_2570_);
lean_dec(v_a_2566_);
v_val_2576_ = lean_ctor_get(v_fst_2570_, 0);
lean_inc(v_val_2576_);
lean_dec_ref(v_fst_2570_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v_val_2576_);
v___x_2578_ = v___x_2568_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_val_2576_);
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
else
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
v_a_2581_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2583_ = v___x_2565_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2565_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2581_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
else
{
lean_object* v_vs_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; size_t v_sz_2592_; size_t v___x_2593_; lean_object* v___x_2594_; 
v_vs_2589_ = lean_ctor_get(v_n_2557_, 0);
v___x_2590_ = lean_box(0);
v___x_2591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2590_);
lean_ctor_set(v___x_2591_, 1, v_b_2558_);
v_sz_2592_ = lean_array_size(v_vs_2589_);
v___x_2593_ = ((size_t)0ULL);
v___x_2594_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_vs_2589_, v_sz_2592_, v___x_2593_, v___x_2591_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2609_; 
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2597_ = v___x_2594_;
v_isShared_2598_ = v_isSharedCheck_2609_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2594_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2609_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v_fst_2599_; 
v_fst_2599_ = lean_ctor_get(v_a_2595_, 0);
if (lean_obj_tag(v_fst_2599_) == 0)
{
lean_object* v_snd_2600_; lean_object* v___x_2601_; lean_object* v___x_2603_; 
v_snd_2600_ = lean_ctor_get(v_a_2595_, 1);
lean_inc(v_snd_2600_);
lean_dec(v_a_2595_);
v___x_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2601_, 0, v_snd_2600_);
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 0, v___x_2601_);
v___x_2603_ = v___x_2597_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2601_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
else
{
lean_object* v_val_2605_; lean_object* v___x_2607_; 
lean_inc_ref(v_fst_2599_);
lean_dec(v_a_2595_);
v_val_2605_ = lean_ctor_get(v_fst_2599_, 0);
lean_inc(v_val_2605_);
lean_dec_ref(v_fst_2599_);
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 0, v_val_2605_);
v___x_2607_ = v___x_2597_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_val_2605_);
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
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
v_a_2610_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2594_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2594_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(lean_object* v_init_2618_, lean_object* v_as_2619_, size_t v_sz_2620_, size_t v_i_2621_, lean_object* v_b_2622_){
_start:
{
uint8_t v___x_2624_; 
v___x_2624_ = lean_usize_dec_lt(v_i_2621_, v_sz_2620_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2625_; 
v___x_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2625_, 0, v_b_2622_);
return v___x_2625_;
}
else
{
lean_object* v_snd_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2660_; 
v_snd_2626_ = lean_ctor_get(v_b_2622_, 1);
v_isSharedCheck_2660_ = !lean_is_exclusive(v_b_2622_);
if (v_isSharedCheck_2660_ == 0)
{
lean_object* v_unused_2661_; 
v_unused_2661_ = lean_ctor_get(v_b_2622_, 0);
lean_dec(v_unused_2661_);
v___x_2628_ = v_b_2622_;
v_isShared_2629_ = v_isSharedCheck_2660_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_snd_2626_);
lean_dec(v_b_2622_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2660_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v_a_2630_; lean_object* v___x_2631_; 
v_a_2630_ = lean_array_uget_borrowed(v_as_2619_, v_i_2621_);
lean_inc(v_snd_2626_);
v___x_2631_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2618_, v_a_2630_, v_snd_2626_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2651_; 
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2634_ = v___x_2631_;
v_isShared_2635_ = v_isSharedCheck_2651_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2631_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2651_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
if (lean_obj_tag(v_a_2632_) == 0)
{
lean_object* v___x_2636_; lean_object* v___x_2638_; 
v___x_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2636_, 0, v_a_2632_);
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 0, v___x_2636_);
v___x_2638_ = v___x_2628_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2636_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v_snd_2626_);
v___x_2638_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
lean_object* v___x_2640_; 
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 0, v___x_2638_);
v___x_2640_ = v___x_2634_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v___x_2638_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2644_; lean_object* v___x_2646_; 
lean_del_object(v___x_2634_);
lean_dec(v_snd_2626_);
v_a_2643_ = lean_ctor_get(v_a_2632_, 0);
lean_inc(v_a_2643_);
lean_dec_ref(v_a_2632_);
v___x_2644_ = lean_box(0);
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 1, v_a_2643_);
lean_ctor_set(v___x_2628_, 0, v___x_2644_);
v___x_2646_ = v___x_2628_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2644_);
lean_ctor_set(v_reuseFailAlloc_2650_, 1, v_a_2643_);
v___x_2646_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
size_t v___x_2647_; size_t v___x_2648_; 
v___x_2647_ = ((size_t)1ULL);
v___x_2648_ = lean_usize_add(v_i_2621_, v___x_2647_);
v_i_2621_ = v___x_2648_;
v_b_2622_ = v___x_2646_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
lean_del_object(v___x_2628_);
lean_dec(v_snd_2626_);
v_a_2652_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2631_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2631_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13___boxed(lean_object* v_init_2662_, lean_object* v_as_2663_, lean_object* v_sz_2664_, lean_object* v_i_2665_, lean_object* v_b_2666_, lean_object* v___y_2667_){
_start:
{
size_t v_sz_boxed_2668_; size_t v_i_boxed_2669_; lean_object* v_res_2670_; 
v_sz_boxed_2668_ = lean_unbox_usize(v_sz_2664_);
lean_dec(v_sz_2664_);
v_i_boxed_2669_ = lean_unbox_usize(v_i_2665_);
lean_dec(v_i_2665_);
v_res_2670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2662_, v_as_2663_, v_sz_boxed_2668_, v_i_boxed_2669_, v_b_2666_);
lean_dec_ref(v_as_2663_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10___boxed(lean_object* v_init_2671_, lean_object* v_n_2672_, lean_object* v_b_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v_res_2675_; 
v_res_2675_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2671_, v_n_2672_, v_b_2673_);
lean_dec_ref(v_n_2672_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(lean_object* v_as_2676_, size_t v_sz_2677_, size_t v_i_2678_, lean_object* v_b_2679_){
_start:
{
uint8_t v___x_2681_; 
v___x_2681_ = lean_usize_dec_lt(v_i_2678_, v_sz_2677_);
if (v___x_2681_ == 0)
{
lean_object* v___x_2682_; 
v___x_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2682_, 0, v_b_2679_);
return v___x_2682_;
}
else
{
uint8_t v___x_2683_; lean_object* v_a_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
lean_dec_ref(v_b_2679_);
v___x_2683_ = 0;
v_a_2684_ = lean_array_uget_borrowed(v_as_2676_, v_i_2678_);
lean_inc(v_a_2684_);
v___x_2685_ = l_Lean_Message_toString(v_a_2684_, v___x_2683_);
v___x_2686_ = l_IO_eprintln___at___00main_spec__6(v___x_2685_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v___x_2687_; size_t v___x_2688_; size_t v___x_2689_; 
lean_dec_ref(v___x_2686_);
v___x_2687_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_2688_ = ((size_t)1ULL);
v___x_2689_ = lean_usize_add(v_i_2678_, v___x_2688_);
v_i_2678_ = v___x_2689_;
v_b_2679_ = v___x_2687_;
goto _start;
}
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
v_a_2691_ = lean_ctor_get(v___x_2686_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2686_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2686_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2691_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16___boxed(lean_object* v_as_2699_, lean_object* v_sz_2700_, lean_object* v_i_2701_, lean_object* v_b_2702_, lean_object* v___y_2703_){
_start:
{
size_t v_sz_boxed_2704_; size_t v_i_boxed_2705_; lean_object* v_res_2706_; 
v_sz_boxed_2704_ = lean_unbox_usize(v_sz_2700_);
lean_dec(v_sz_2700_);
v_i_boxed_2705_ = lean_unbox_usize(v_i_2701_);
lean_dec(v_i_2701_);
v_res_2706_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2699_, v_sz_boxed_2704_, v_i_boxed_2705_, v_b_2702_);
lean_dec_ref(v_as_2699_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(lean_object* v_as_2707_, size_t v_sz_2708_, size_t v_i_2709_, lean_object* v_b_2710_){
_start:
{
uint8_t v___x_2712_; 
v___x_2712_ = lean_usize_dec_lt(v_i_2709_, v_sz_2708_);
if (v___x_2712_ == 0)
{
lean_object* v___x_2713_; 
v___x_2713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2713_, 0, v_b_2710_);
return v___x_2713_;
}
else
{
uint8_t v___x_2714_; lean_object* v_a_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
lean_dec_ref(v_b_2710_);
v___x_2714_ = 0;
v_a_2715_ = lean_array_uget_borrowed(v_as_2707_, v_i_2709_);
lean_inc(v_a_2715_);
v___x_2716_ = l_Lean_Message_toString(v_a_2715_, v___x_2714_);
v___x_2717_ = l_IO_eprintln___at___00main_spec__6(v___x_2716_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v___x_2718_; size_t v___x_2719_; size_t v___x_2720_; lean_object* v___x_2721_; 
lean_dec_ref(v___x_2717_);
v___x_2718_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_2719_ = ((size_t)1ULL);
v___x_2720_ = lean_usize_add(v_i_2709_, v___x_2719_);
v___x_2721_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2707_, v_sz_2708_, v___x_2720_, v___x_2718_);
return v___x_2721_;
}
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
v_a_2722_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___x_2717_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2717_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11___boxed(lean_object* v_as_2730_, lean_object* v_sz_2731_, lean_object* v_i_2732_, lean_object* v_b_2733_, lean_object* v___y_2734_){
_start:
{
size_t v_sz_boxed_2735_; size_t v_i_boxed_2736_; lean_object* v_res_2737_; 
v_sz_boxed_2735_ = lean_unbox_usize(v_sz_2731_);
lean_dec(v_sz_2731_);
v_i_boxed_2736_ = lean_unbox_usize(v_i_2732_);
lean_dec(v_i_2732_);
v_res_2737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_as_2730_, v_sz_boxed_2735_, v_i_boxed_2736_, v_b_2733_);
lean_dec_ref(v_as_2730_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7(lean_object* v_t_2738_, lean_object* v_init_2739_){
_start:
{
lean_object* v_root_2741_; lean_object* v_tail_2742_; lean_object* v___x_2743_; 
v_root_2741_ = lean_ctor_get(v_t_2738_, 0);
v_tail_2742_ = lean_ctor_get(v_t_2738_, 1);
v___x_2743_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2739_, v_root_2741_, v_init_2739_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2780_; 
v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2746_ = v___x_2743_;
v_isShared_2747_ = v_isSharedCheck_2780_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2743_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2780_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
if (lean_obj_tag(v_a_2744_) == 0)
{
lean_object* v_a_2748_; lean_object* v___x_2750_; 
v_a_2748_ = lean_ctor_get(v_a_2744_, 0);
lean_inc(v_a_2748_);
lean_dec_ref(v_a_2744_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 0, v_a_2748_);
v___x_2750_ = v___x_2746_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2748_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
else
{
lean_object* v_a_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; size_t v_sz_2755_; size_t v___x_2756_; lean_object* v___x_2757_; 
lean_del_object(v___x_2746_);
v_a_2752_ = lean_ctor_get(v_a_2744_, 0);
lean_inc(v_a_2752_);
lean_dec_ref(v_a_2744_);
v___x_2753_ = lean_box(0);
v___x_2754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2753_);
lean_ctor_set(v___x_2754_, 1, v_a_2752_);
v_sz_2755_ = lean_array_size(v_tail_2742_);
v___x_2756_ = ((size_t)0ULL);
v___x_2757_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_tail_2742_, v_sz_2755_, v___x_2756_, v___x_2754_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2771_; 
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2760_ = v___x_2757_;
v_isShared_2761_ = v_isSharedCheck_2771_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2757_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2771_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v_fst_2762_; 
v_fst_2762_ = lean_ctor_get(v_a_2758_, 0);
if (lean_obj_tag(v_fst_2762_) == 0)
{
lean_object* v_snd_2763_; lean_object* v___x_2765_; 
v_snd_2763_ = lean_ctor_get(v_a_2758_, 1);
lean_inc(v_snd_2763_);
lean_dec(v_a_2758_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v_snd_2763_);
v___x_2765_ = v___x_2760_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_snd_2763_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
else
{
lean_object* v_val_2767_; lean_object* v___x_2769_; 
lean_inc_ref(v_fst_2762_);
lean_dec(v_a_2758_);
v_val_2767_ = lean_ctor_get(v_fst_2762_, 0);
lean_inc(v_val_2767_);
lean_dec_ref(v_fst_2762_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v_val_2767_);
v___x_2769_ = v___x_2760_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_val_2767_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
else
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
v_a_2772_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2757_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2757_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
}
}
else
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
v_a_2781_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2783_ = v___x_2743_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2743_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2781_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7___boxed(lean_object* v_t_2789_, lean_object* v_init_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v_res_2792_; 
v_res_2792_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_t_2789_, v_init_2790_);
lean_dec_ref(v_t_2789_);
return v_res_2792_;
}
}
static lean_object* _init_l_main___closed__3(void){
_start:
{
lean_object* v___x_2796_; 
v___x_2796_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_box(0), lean_box(0), lean_box(0));
return v___x_2796_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2797_ = l_Lean_instInhabitedClassState_default;
v___x_2798_ = lean_box(0);
v___x_2799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2798_);
lean_ctor_set(v___x_2799_, 1, v___x_2797_);
return v___x_2799_;
}
}
static lean_object* _init_l_main___closed__5(void){
_start:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2800_ = l_Lean_Meta_Match_Extension_instInhabitedState;
v___x_2801_ = lean_box(0);
v___x_2802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
lean_ctor_set(v___x_2802_, 1, v___x_2800_);
return v___x_2802_;
}
}
static lean_object* _init_l_main___closed__6(void){
_start:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2803_ = ((lean_object*)(l_main___closed__2));
v___x_2804_ = ((lean_object*)(l_main___closed__1));
v___x_2805_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_2804_, v___x_2803_);
return v___x_2805_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2806_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2807_ = lean_box(0);
v___x_2808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
lean_ctor_set(v___x_2808_, 1, v___x_2806_);
return v___x_2808_;
}
}
static lean_object* _init_l_main___closed__8(void){
_start:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_2810_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2809_);
return v___x_2810_;
}
}
static lean_object* _init_l_main___closed__9(void){
_start:
{
lean_object* v___x_2811_; 
v___x_2811_ = l_Array_instInhabited(lean_box(0));
return v___x_2811_;
}
}
static lean_object* _init_l_main___closed__14(void){
_start:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2819_ = l_Lean_Options_empty;
v___x_2820_ = l_Lean_Core_getMaxHeartbeats(v___x_2819_);
return v___x_2820_;
}
}
static lean_object* _init_l_main___closed__19(void){
_start:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2825_ = ((lean_object*)(l_main___closed__18));
v___x_2826_ = lean_unsigned_to_nat(27u);
v___x_2827_ = lean_unsigned_to_nat(144u);
v___x_2828_ = ((lean_object*)(l_main___closed__17));
v___x_2829_ = ((lean_object*)(l_main___closed__16));
v___x_2830_ = l_mkPanicMessageWithDecl(v___x_2829_, v___x_2828_, v___x_2827_, v___x_2826_, v___x_2825_);
return v___x_2830_;
}
}
static lean_object* _init_l_main___closed__21(void){
_start:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2832_ = ((lean_object*)(l_main___closed__18));
v___x_2833_ = lean_unsigned_to_nat(51u);
v___x_2834_ = lean_unsigned_to_nat(117u);
v___x_2835_ = ((lean_object*)(l_main___closed__17));
v___x_2836_ = ((lean_object*)(l_main___closed__16));
v___x_2837_ = l_mkPanicMessageWithDecl(v___x_2836_, v___x_2835_, v___x_2834_, v___x_2833_, v___x_2832_);
return v___x_2837_;
}
}
static lean_object* _init_l_main___closed__22(void){
_start:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2838_ = lean_unsigned_to_nat(1u);
v___x_2839_ = l_Lean_firstFrontendMacroScope;
v___x_2840_ = lean_nat_add(v___x_2839_, v___x_2838_);
return v___x_2840_;
}
}
static lean_object* _init_l_main___closed__26(void){
_start:
{
lean_object* v___x_2847_; uint64_t v___x_2848_; lean_object* v___x_2849_; 
v___x_2847_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2848_ = 0ULL;
v___x_2849_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2849_, 0, v___x_2847_);
lean_ctor_set_uint64(v___x_2849_, sizeof(void*)*1, v___x_2848_);
return v___x_2849_;
}
}
static lean_object* _init_l_main___closed__27(void){
_start:
{
lean_object* v___x_2850_; 
v___x_2850_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2850_;
}
}
static lean_object* _init_l_main___closed__28(void){
_start:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2851_ = lean_obj_once(&l_main___closed__27, &l_main___closed__27_once, _init_l_main___closed__27);
v___x_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2851_);
return v___x_2852_;
}
}
static lean_object* _init_l_main___closed__29(void){
_start:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_2854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2853_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
return v___x_2854_;
}
}
static lean_object* _init_l_main___closed__30(void){
_start:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2855_ = l_Lean_NameSet_empty;
v___x_2856_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2857_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2856_);
lean_ctor_set(v___x_2857_, 1, v___x_2856_);
lean_ctor_set(v___x_2857_, 2, v___x_2855_);
return v___x_2857_;
}
}
static lean_object* _init_l_main___closed__31(void){
_start:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; uint8_t v___x_2860_; lean_object* v___x_2861_; 
v___x_2858_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2859_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_2860_ = 1;
v___x_2861_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2861_, 0, v___x_2859_);
lean_ctor_set(v___x_2861_, 1, v___x_2859_);
lean_ctor_set(v___x_2861_, 2, v___x_2858_);
lean_ctor_set_uint8(v___x_2861_, sizeof(void*)*3, v___x_2860_);
return v___x_2861_;
}
}
static uint8_t _init_l_main___closed__36(void){
_start:
{
uint8_t v___x_2868_; uint8_t v___x_2869_; 
v___x_2868_ = 2;
v___x_2869_ = l_Lean_instOrdOLeanLevel_ord(v___x_2868_, v___x_2868_);
return v___x_2869_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_2870_; lean_object* v___x_2871_; 
v___x_2870_ = 1;
v___x_2871_ = lean_box_uint32(v___x_2870_);
return v___x_2871_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_2872_; lean_object* v___x_2873_; 
v___x_2872_ = 0;
v___x_2873_ = lean_box_uint32(v___x_2872_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_2874_){
_start:
{
if (lean_obj_tag(v_args_2874_) == 1)
{
lean_object* v_tail_2899_; 
v_tail_2899_ = lean_ctor_get(v_args_2874_, 1);
lean_inc(v_tail_2899_);
if (lean_obj_tag(v_tail_2899_) == 1)
{
lean_object* v_tail_2900_; 
v_tail_2900_ = lean_ctor_get(v_tail_2899_, 1);
lean_inc(v_tail_2900_);
if (lean_obj_tag(v_tail_2900_) == 1)
{
lean_object* v_head_2901_; lean_object* v_head_2902_; lean_object* v_head_2903_; lean_object* v_tail_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_3527_; 
v_head_2901_ = lean_ctor_get(v_args_2874_, 0);
lean_inc(v_head_2901_);
lean_dec_ref(v_args_2874_);
v_head_2902_ = lean_ctor_get(v_tail_2899_, 0);
lean_inc(v_head_2902_);
lean_dec_ref(v_tail_2899_);
v_head_2903_ = lean_ctor_get(v_tail_2900_, 0);
v_tail_2904_ = lean_ctor_get(v_tail_2900_, 1);
v_isSharedCheck_3527_ = !lean_is_exclusive(v_tail_2900_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_2906_ = v_tail_2900_;
v_isShared_2907_ = v_isSharedCheck_3527_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_tail_2904_);
lean_inc(v_head_2903_);
lean_dec(v_tail_2900_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_3527_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2908_; 
v___x_2908_ = l_Lean_ModuleSetup_load(v_head_2901_);
lean_dec(v_head_2901_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v_a_2909_; lean_object* v_name_2910_; lean_object* v_options_2911_; uint8_t v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2916_; 
v_a_2909_ = lean_ctor_get(v___x_2908_, 0);
lean_inc(v_a_2909_);
lean_dec_ref(v___x_2908_);
v_name_2910_ = lean_ctor_get(v_a_2909_, 0);
lean_inc(v_name_2910_);
v_options_2911_ = lean_ctor_get(v_a_2909_, 6);
lean_inc(v_options_2911_);
lean_dec(v_a_2909_);
v___x_2912_ = 0;
v___x_2913_ = l_Lean_LeanOptions_toOptions(v_options_2911_);
v___x_2914_ = lean_box(v___x_2912_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set_tag(v___x_2906_, 0);
lean_ctor_set(v___x_2906_, 1, v___x_2913_);
lean_ctor_set(v___x_2906_, 0, v___x_2914_);
v___x_2916_ = v___x_2906_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_2914_);
lean_ctor_set(v_reuseFailAlloc_3518_, 1, v___x_2913_);
v___x_2916_ = v_reuseFailAlloc_3518_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
lean_object* v___x_2917_; 
v___x_2917_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_tail_2904_, v___x_2916_);
lean_dec(v_tail_2904_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; lean_object* v___x_2919_; 
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_a_2918_);
lean_dec_ref(v___x_2917_);
v___x_2919_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_a_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
lean_inc(v_a_2920_);
lean_dec_ref(v___x_2919_);
v___x_2921_ = lean_box(0);
v___x_2922_ = l_Lean_initSearchPath(v_a_2920_, v___x_2921_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_fst_2923_; lean_object* v_snd_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_3493_; 
lean_dec_ref(v___x_2922_);
v_fst_2923_ = lean_ctor_get(v_a_2918_, 0);
v_snd_2924_ = lean_ctor_get(v_a_2918_, 1);
v_isSharedCheck_3493_ = !lean_is_exclusive(v_a_2918_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_2926_ = v_a_2918_;
v_isShared_2927_ = v_isSharedCheck_3493_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_snd_2924_);
lean_inc(v_fst_2923_);
lean_dec(v_a_2918_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_3493_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; uint8_t v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___y_2943_; lean_object* v___y_2944_; uint8_t v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_3074_; lean_object* v___y_3075_; uint8_t v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v_nextMacroScope_3090_; lean_object* v_ngen_3091_; lean_object* v_auxDeclNGen_3092_; lean_object* v_traceState_3093_; lean_object* v_messages_3094_; lean_object* v_infoState_3095_; lean_object* v_snapshotTasks_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3117_; lean_object* v___y_3118_; uint8_t v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; uint8_t v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3188_; lean_object* v___y_3189_; uint8_t v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; uint8_t v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; uint8_t v___y_3211_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___y_3235_; uint8_t v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3341_; uint8_t v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3363_; lean_object* v___y_3364_; uint8_t v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3379_; lean_object* v___y_3380_; uint8_t v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___x_3394_; lean_object* v___x_3395_; uint8_t v___x_3396_; uint8_t v___y_3398_; uint8_t v___x_3492_; 
v___x_2928_ = lean_obj_once(&l_main___closed__3, &l_main___closed__3_once, _init_l_main___closed__3);
v___x_2929_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2930_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_2931_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2932_ = lean_obj_once(&l_main___closed__8, &l_main___closed__8_once, _init_l_main___closed__8);
v___x_2933_ = lean_obj_once(&l_main___closed__9, &l_main___closed__9_once, _init_l_main___closed__9);
v___x_2934_ = lean_box(1);
v___x_2935_ = ((lean_object*)(l_main___closed__10));
v___x_2936_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_2937_ = 1;
v___x_2938_ = l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(v_snd_2924_, v___x_2936_, v___x_2937_);
v___x_2939_ = l_Lean_maxHeartbeats;
v___x_2940_ = lean_unsigned_to_nat(0u);
v___x_2941_ = l_Lean_Option_set___at___00main_spec__3(v___x_2938_, v___x_2939_, v___x_2940_);
v___x_3231_ = ((lean_object*)(l_main___closed__20));
lean_inc(v_name_2910_);
v___x_3232_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3232_, 0, v_name_2910_);
lean_ctor_set_uint8(v___x_3232_, sizeof(void*)*1, v___x_2937_);
lean_ctor_set_uint8(v___x_3232_, sizeof(void*)*1 + 1, v___x_2937_);
lean_ctor_set_uint8(v___x_3232_, sizeof(void*)*1 + 2, v___x_2937_);
v___x_3233_ = lean_unsigned_to_nat(1u);
v___x_3394_ = lean_mk_empty_array_with_capacity(v___x_3233_);
v___x_3395_ = lean_array_push(v___x_3394_, v___x_3232_);
v___x_3396_ = 2;
v___x_3492_ = lean_uint8_once(&l_main___closed__36, &l_main___closed__36_once, _init_l_main___closed__36);
if (v___x_3492_ == 0)
{
v___y_3398_ = v___x_2937_;
goto v___jp_3397_;
}
else
{
v___y_3398_ = v___x_2912_;
goto v___jp_3397_;
}
v___jp_2942_:
{
lean_object* v___x_2962_; lean_object* v_messages_2963_; lean_object* v_env_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_3065_; 
v___x_2962_ = lean_st_ref_get(v___y_2959_);
lean_dec(v___y_2959_);
v_messages_2963_ = lean_ctor_get(v___x_2962_, 6);
v_env_2964_ = lean_ctor_get(v___x_2962_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_3065_ == 0)
{
lean_object* v_unused_3066_; lean_object* v_unused_3067_; lean_object* v_unused_3068_; lean_object* v_unused_3069_; lean_object* v_unused_3070_; lean_object* v_unused_3071_; lean_object* v_unused_3072_; 
v_unused_3066_ = lean_ctor_get(v___x_2962_, 8);
lean_dec(v_unused_3066_);
v_unused_3067_ = lean_ctor_get(v___x_2962_, 7);
lean_dec(v_unused_3067_);
v_unused_3068_ = lean_ctor_get(v___x_2962_, 5);
lean_dec(v_unused_3068_);
v_unused_3069_ = lean_ctor_get(v___x_2962_, 4);
lean_dec(v_unused_3069_);
v_unused_3070_ = lean_ctor_get(v___x_2962_, 3);
lean_dec(v_unused_3070_);
v_unused_3071_ = lean_ctor_get(v___x_2962_, 2);
lean_dec(v_unused_3071_);
v_unused_3072_ = lean_ctor_get(v___x_2962_, 1);
lean_dec(v_unused_3072_);
v___x_2966_ = v___x_2962_;
v_isShared_2967_ = v_isSharedCheck_3065_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_messages_2963_);
lean_inc(v_env_2964_);
lean_dec(v___x_2962_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_3065_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v_unreported_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v_unreported_2968_ = lean_ctor_get(v_messages_2963_, 1);
v___x_2969_ = lean_box(0);
v___x_2970_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_unreported_2968_, v___x_2969_);
if (lean_obj_tag(v___x_2970_) == 0)
{
lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_3055_; 
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_3055_ == 0)
{
lean_object* v_unused_3056_; 
v_unused_3056_ = lean_ctor_get(v___x_2970_, 0);
lean_dec(v_unused_3056_);
v___x_2972_ = v___x_2970_;
v_isShared_2973_ = v_isSharedCheck_3055_;
goto v_resetjp_2971_;
}
else
{
lean_dec(v___x_2970_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_3055_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
uint8_t v___x_2974_; 
v___x_2974_ = l_Lean_MessageLog_hasErrors(v_messages_2963_);
lean_dec_ref(v_messages_2963_);
if (v___x_2974_ == 0)
{
lean_object* v___x_2975_; 
lean_del_object(v___x_2972_);
lean_inc_ref(v_env_2964_);
v___x_2975_ = l___private_LeanIR_0__mkIRData(v_env_2964_);
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_object* v_a_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v_a_2976_ = lean_ctor_get(v___x_2975_, 0);
lean_inc(v_a_2976_);
lean_dec_ref(v___x_2975_);
v___x_2977_ = l_Lean_Environment_mainModule(v_env_2964_);
v___x_2978_ = ((lean_object*)(l_main___closed__12));
v___x_2979_ = l_Lean_Name_append(v___x_2977_, v___x_2978_);
lean_inc(v_head_2902_);
v___x_2980_ = l_Lean_saveModuleData(v_head_2902_, v___x_2979_, v_a_2976_);
lean_dec(v___x_2979_);
if (lean_obj_tag(v___x_2980_) == 0)
{
uint8_t v___x_2981_; lean_object* v___x_2982_; 
lean_dec_ref(v___x_2980_);
v___x_2981_ = 1;
v___x_2982_ = lean_io_prim_handle_mk(v_head_2903_, v___x_2981_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2988_; 
lean_dec(v_head_2903_);
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2983_);
lean_dec_ref(v___x_2982_);
v___x_2984_ = ((lean_object*)(l_main___closed__13));
v___x_2985_ = l_Lean_Options_empty;
v___x_2986_ = lean_obj_once(&l_main___closed__14, &l_main___closed__14_once, _init_l_main___closed__14);
lean_inc_ref(v___y_2954_);
lean_inc_ref(v___y_2956_);
lean_inc_ref(v___y_2960_);
lean_inc_ref(v___y_2952_);
lean_inc_ref(v___y_2961_);
lean_inc_ref(v___y_2957_);
lean_inc(v___y_2953_);
lean_inc_ref(v_env_2964_);
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 8, v___y_2954_);
lean_ctor_set(v___x_2966_, 7, v___y_2956_);
lean_ctor_set(v___x_2966_, 6, v___y_2960_);
lean_ctor_set(v___x_2966_, 5, v___y_2952_);
lean_ctor_set(v___x_2966_, 4, v___y_2961_);
lean_ctor_set(v___x_2966_, 3, v___y_2958_);
lean_ctor_set(v___x_2966_, 2, v___y_2957_);
lean_ctor_set(v___x_2966_, 1, v___y_2953_);
v___x_2988_ = v___x_2966_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_env_2964_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v___y_2953_);
lean_ctor_set(v_reuseFailAlloc_3012_, 2, v___y_2957_);
lean_ctor_set(v_reuseFailAlloc_3012_, 3, v___y_2958_);
lean_ctor_set(v_reuseFailAlloc_3012_, 4, v___y_2961_);
lean_ctor_set(v_reuseFailAlloc_3012_, 5, v___y_2952_);
lean_ctor_set(v_reuseFailAlloc_3012_, 6, v___y_2960_);
lean_ctor_set(v_reuseFailAlloc_3012_, 7, v___y_2956_);
lean_ctor_set(v_reuseFailAlloc_3012_, 8, v___y_2954_);
v___x_2988_ = v_reuseFailAlloc_3012_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___f_2991_; lean_object* v___x_2992_; 
v___x_2989_ = lean_box(v___x_2912_);
v___x_2990_ = lean_box(v___y_2945_);
lean_inc(v___y_2951_);
lean_inc(v___y_2943_);
lean_inc(v___y_2948_);
lean_inc_ref(v___y_2950_);
lean_inc_ref(v___y_2944_);
lean_inc(v___y_2949_);
v___f_2991_ = lean_alloc_closure((void*)(l_main___lam__1___boxed), 18, 17);
lean_closure_set(v___f_2991_, 0, v___x_2988_);
lean_closure_set(v___f_2991_, 1, v___y_2949_);
lean_closure_set(v___f_2991_, 2, v___x_2985_);
lean_closure_set(v___f_2991_, 3, v_name_2910_);
lean_closure_set(v___f_2991_, 4, v_a_2983_);
lean_closure_set(v___f_2991_, 5, v___y_2944_);
lean_closure_set(v___f_2991_, 6, v_head_2902_);
lean_closure_set(v___f_2991_, 7, v___y_2950_);
lean_closure_set(v___f_2991_, 8, v___x_2940_);
lean_closure_set(v___f_2991_, 9, v___y_2948_);
lean_closure_set(v___f_2991_, 10, v___y_2947_);
lean_closure_set(v___f_2991_, 11, v___y_2946_);
lean_closure_set(v___f_2991_, 12, v___x_2986_);
lean_closure_set(v___f_2991_, 13, v___y_2943_);
lean_closure_set(v___f_2991_, 14, v___y_2951_);
lean_closure_set(v___f_2991_, 15, v___x_2989_);
lean_closure_set(v___f_2991_, 16, v___x_2990_);
v___x_2992_ = l_Lean_profileitIOUnsafe___redArg(v___x_2984_, v___x_2941_, v___f_2991_, v___y_2955_);
lean_dec_ref(v___x_2941_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v___x_2993_; uint8_t v___x_2994_; 
lean_dec_ref(v___x_2992_);
v___x_2993_ = lean_display_cumulative_profiling_times();
v___x_2994_ = lean_unbox(v_fst_2923_);
lean_dec(v_fst_2923_);
if (v___x_2994_ == 0)
{
lean_dec_ref(v_env_2964_);
goto v___jp_2896_;
}
else
{
lean_object* v___x_2995_; 
v___x_2995_ = l_Lean_Environment_displayStats(v_env_2964_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_dec_ref(v___x_2995_);
goto v___jp_2896_;
}
else
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2998_ = v___x_2995_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2995_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2996_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
}
else
{
lean_object* v_a_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3011_; 
lean_dec_ref(v_env_2964_);
lean_dec(v_fst_2923_);
v_a_3004_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3006_ = v___x_2992_;
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_a_3004_);
lean_dec(v___x_2992_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3009_; 
if (v_isShared_3007_ == 0)
{
v___x_3009_ = v___x_3006_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_a_3004_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
}
}
}
else
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
lean_dec_ref(v___x_2982_);
lean_del_object(v___x_2966_);
lean_dec_ref(v_env_2964_);
lean_dec_ref(v___y_2958_);
lean_dec(v___y_2955_);
lean_dec(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec_ref(v___x_2941_);
lean_dec(v_fst_2923_);
lean_dec(v_name_2910_);
lean_dec(v_head_2902_);
v___x_3013_ = ((lean_object*)(l_main___closed__15));
v___x_3014_ = lean_string_append(v___x_3013_, v_head_2903_);
lean_dec(v_head_2903_);
v___x_3015_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__5));
v___x_3016_ = lean_string_append(v___x_3014_, v___x_3015_);
v___x_3017_ = l_IO_eprintln___at___00main_spec__6(v___x_3016_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3025_; 
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3025_ == 0)
{
lean_object* v_unused_3026_; 
v_unused_3026_ = lean_ctor_get(v___x_3017_, 0);
lean_dec(v_unused_3026_);
v___x_3019_ = v___x_3017_;
v_isShared_3020_ = v_isSharedCheck_3025_;
goto v_resetjp_3018_;
}
else
{
lean_dec(v___x_3017_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3025_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3021_; lean_object* v___x_3023_; 
v___x_3021_ = l_main___boxed__const__1;
if (v_isShared_3020_ == 0)
{
lean_ctor_set(v___x_3019_, 0, v___x_3021_);
v___x_3023_ = v___x_3019_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v___x_3021_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
v_a_3027_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_3017_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3017_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
}
else
{
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3042_; 
lean_del_object(v___x_2966_);
lean_dec_ref(v_env_2964_);
lean_dec_ref(v___y_2958_);
lean_dec(v___y_2955_);
lean_dec(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec_ref(v___x_2941_);
lean_dec(v_fst_2923_);
lean_dec(v_name_2910_);
lean_dec(v_head_2903_);
lean_dec(v_head_2902_);
v_a_3035_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3037_ = v___x_2980_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_2980_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
if (v_isShared_3038_ == 0)
{
v___x_3040_ = v___x_3037_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
}
else
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
lean_del_object(v___x_2966_);
lean_dec_ref(v_env_2964_);
lean_dec_ref(v___y_2958_);
lean_dec(v___y_2955_);
lean_dec(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec_ref(v___x_2941_);
lean_dec(v_fst_2923_);
lean_dec(v_name_2910_);
lean_dec(v_head_2903_);
lean_dec(v_head_2902_);
v_a_3043_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_2975_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_2975_);
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
else
{
lean_object* v___x_3051_; lean_object* v___x_3053_; 
lean_del_object(v___x_2966_);
lean_dec_ref(v_env_2964_);
lean_dec_ref(v___y_2958_);
lean_dec(v___y_2955_);
lean_dec(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec_ref(v___x_2941_);
lean_dec(v_fst_2923_);
lean_dec(v_name_2910_);
lean_dec(v_head_2903_);
lean_dec(v_head_2902_);
v___x_3051_ = l_main___boxed__const__1;
if (v_isShared_2973_ == 0)
{
lean_ctor_set(v___x_2972_, 0, v___x_3051_);
v___x_3053_ = v___x_2972_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_3051_);
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
else
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3064_; 
lean_del_object(v___x_2966_);
lean_dec_ref(v_env_2964_);
lean_dec_ref(v_messages_2963_);
lean_dec_ref(v___y_2958_);
lean_dec(v___y_2955_);
lean_dec(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec_ref(v___x_2941_);
lean_dec(v_fst_2923_);
lean_dec(v_name_2910_);
lean_dec(v_head_2903_);
lean_dec(v_head_2902_);
v_a_3057_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3059_ = v___x_2970_;
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_2970_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3062_; 
if (v_isShared_3060_ == 0)
{
v___x_3062_ = v___x_3059_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_a_3057_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
}
}
v___jp_3073_:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; size_t v_sz_3107_; size_t v___x_3108_; lean_object* v___x_3109_; 
lean_inc_ref(v___y_3097_);
v___x_3104_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3104_, 0, v___y_3103_);
lean_ctor_set(v___x_3104_, 1, v_nextMacroScope_3090_);
lean_ctor_set(v___x_3104_, 2, v_ngen_3091_);
lean_ctor_set(v___x_3104_, 3, v_auxDeclNGen_3092_);
lean_ctor_set(v___x_3104_, 4, v_traceState_3093_);
lean_ctor_set(v___x_3104_, 5, v___y_3097_);
lean_ctor_set(v___x_3104_, 6, v_messages_3094_);
lean_ctor_set(v___x_3104_, 7, v_infoState_3095_);
lean_ctor_set(v___x_3104_, 8, v_snapshotTasks_3096_);
v___x_3105_ = lean_st_ref_set(v___y_3101_, v___x_3104_);
v___x_3106_ = lean_box(0);
v_sz_3107_ = lean_array_size(v___y_3087_);
v___x_3108_ = ((size_t)0ULL);
v___x_3109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v___y_3087_, v_sz_3107_, v___x_3108_, v___x_3106_, v___y_3083_, v___y_3101_);
lean_dec_ref(v___y_3087_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_dec_ref(v___x_3109_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3083_);
v___y_2943_ = v___y_3074_;
v___y_2944_ = v___y_3075_;
v___y_2945_ = v___y_3076_;
v___y_2946_ = v___y_3078_;
v___y_2947_ = v___y_3077_;
v___y_2948_ = v___y_3079_;
v___y_2949_ = v___y_3080_;
v___y_2950_ = v___y_3081_;
v___y_2951_ = v___y_3082_;
v___y_2952_ = v___y_3097_;
v___y_2953_ = v___y_3098_;
v___y_2954_ = v___y_3084_;
v___y_2955_ = v___y_3099_;
v___y_2956_ = v___y_3100_;
v___y_2957_ = v___y_3085_;
v___y_2958_ = v___y_3086_;
v___y_2959_ = v___y_3102_;
v___y_2960_ = v___y_3089_;
v___y_2961_ = v___y_3088_;
goto v___jp_2942_;
}
else
{
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_dec_ref(v___x_3109_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3083_);
v___y_2943_ = v___y_3074_;
v___y_2944_ = v___y_3075_;
v___y_2945_ = v___y_3076_;
v___y_2946_ = v___y_3078_;
v___y_2947_ = v___y_3077_;
v___y_2948_ = v___y_3079_;
v___y_2949_ = v___y_3080_;
v___y_2950_ = v___y_3081_;
v___y_2951_ = v___y_3082_;
v___y_2952_ = v___y_3097_;
v___y_2953_ = v___y_3098_;
v___y_2954_ = v___y_3084_;
v___y_2955_ = v___y_3099_;
v___y_2956_ = v___y_3100_;
v___y_2957_ = v___y_3085_;
v___y_2958_ = v___y_3086_;
v___y_2959_ = v___y_3102_;
v___y_2960_ = v___y_3089_;
v___y_2961_ = v___y_3088_;
goto v___jp_2942_;
}
else
{
lean_object* v_a_3110_; uint8_t v___x_3111_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
lean_inc(v_a_3110_);
lean_dec_ref(v___x_3109_);
v___x_3111_ = l_Lean_Exception_isInterrupt(v_a_3110_);
if (v___x_3111_ == 0)
{
lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3112_ = l_Lean_Exception_toMessageData(v_a_3110_);
v___x_3113_ = l_Lean_logError___at___00main_spec__14(v___x_3112_, v___y_3083_, v___y_3101_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3083_);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_dec_ref(v___x_3113_);
v___y_2943_ = v___y_3074_;
v___y_2944_ = v___y_3075_;
v___y_2945_ = v___y_3076_;
v___y_2946_ = v___y_3078_;
v___y_2947_ = v___y_3077_;
v___y_2948_ = v___y_3079_;
v___y_2949_ = v___y_3080_;
v___y_2950_ = v___y_3081_;
v___y_2951_ = v___y_3082_;
v___y_2952_ = v___y_3097_;
v___y_2953_ = v___y_3098_;
v___y_2954_ = v___y_3084_;
v___y_2955_ = v___y_3099_;
v___y_2956_ = v___y_3100_;
v___y_2957_ = v___y_3085_;
v___y_2958_ = v___y_3086_;
v___y_2959_ = v___y_3102_;
v___y_2960_ = v___y_3089_;
v___y_2961_ = v___y_3088_;
goto v___jp_2942_;
}
else
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
lean_dec_ref(v___x_3113_);
lean_dec(v___y_3102_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3086_);
lean_dec(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___x_2941_);
lean_dec(v_fst_2923_);
lean_dec(v_name_2910_);
lean_dec(v_head_2903_);
lean_dec(v_head_2902_);
v___x_3114_ = lean_obj_once(&l_main___closed__19, &l_main___closed__19_once, _init_l_main___closed__19);
v___x_3115_ = l_panic___at___00main_spec__5(v___x_3114_);
return v___x_3115_;
}
}
else
{
lean_dec(v_a_3110_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3083_);
v___y_2943_ = v___y_3074_;
v___y_2944_ = v___y_3075_;
v___y_2945_ = v___y_3076_;
v___y_2946_ = v___y_3078_;
v___y_2947_ = v___y_3077_;
v___y_2948_ = v___y_3079_;
v___y_2949_ = v___y_3080_;
v___y_2950_ = v___y_3081_;
v___y_2951_ = v___y_3082_;
v___y_2952_ = v___y_3097_;
v___y_2953_ = v___y_3098_;
v___y_2954_ = v___y_3084_;
v___y_2955_ = v___y_3099_;
v___y_2956_ = v___y_3100_;
v___y_2957_ = v___y_3085_;
v___y_2958_ = v___y_3086_;
v___y_2959_ = v___y_3102_;
v___y_2960_ = v___y_3089_;
v___y_2961_ = v___y_3088_;
goto v___jp_2942_;
}
}
}
}
v___jp_3116_:
{
lean_object* v___x_3141_; lean_object* v_fileName_3142_; lean_object* v_fileMap_3143_; lean_object* v_currRecDepth_3144_; lean_object* v_ref_3145_; lean_object* v_currNamespace_3146_; lean_object* v_openDecls_3147_; lean_object* v_initHeartbeats_3148_; lean_object* v_maxHeartbeats_3149_; lean_object* v_quotContext_3150_; lean_object* v_currMacroScope_3151_; lean_object* v_cancelTk_x3f_3152_; uint8_t v_suppressElabErrors_3153_; lean_object* v_inheritedTraceOptions_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3184_; 
v___x_3141_ = lean_st_ref_take(v___y_3140_);
v_fileName_3142_ = lean_ctor_get(v___y_3139_, 0);
v_fileMap_3143_ = lean_ctor_get(v___y_3139_, 1);
v_currRecDepth_3144_ = lean_ctor_get(v___y_3139_, 3);
v_ref_3145_ = lean_ctor_get(v___y_3139_, 5);
v_currNamespace_3146_ = lean_ctor_get(v___y_3139_, 6);
v_openDecls_3147_ = lean_ctor_get(v___y_3139_, 7);
v_initHeartbeats_3148_ = lean_ctor_get(v___y_3139_, 8);
v_maxHeartbeats_3149_ = lean_ctor_get(v___y_3139_, 9);
v_quotContext_3150_ = lean_ctor_get(v___y_3139_, 10);
v_currMacroScope_3151_ = lean_ctor_get(v___y_3139_, 11);
v_cancelTk_x3f_3152_ = lean_ctor_get(v___y_3139_, 12);
v_suppressElabErrors_3153_ = lean_ctor_get_uint8(v___y_3139_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3154_ = lean_ctor_get(v___y_3139_, 13);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___y_3139_);
if (v_isSharedCheck_3184_ == 0)
{
lean_object* v_unused_3185_; lean_object* v_unused_3186_; 
v_unused_3185_ = lean_ctor_get(v___y_3139_, 4);
lean_dec(v_unused_3185_);
v_unused_3186_ = lean_ctor_get(v___y_3139_, 2);
lean_dec(v_unused_3186_);
v___x_3156_ = v___y_3139_;
v_isShared_3157_ = v_isSharedCheck_3184_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_inheritedTraceOptions_3154_);
lean_inc(v_cancelTk_x3f_3152_);
lean_inc(v_currMacroScope_3151_);
lean_inc(v_quotContext_3150_);
lean_inc(v_maxHeartbeats_3149_);
lean_inc(v_initHeartbeats_3148_);
lean_inc(v_openDecls_3147_);
lean_inc(v_currNamespace_3146_);
lean_inc(v_ref_3145_);
lean_inc(v_currRecDepth_3144_);
lean_inc(v_fileMap_3143_);
lean_inc(v_fileName_3142_);
lean_dec(v___y_3139_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3184_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v_env_3158_; lean_object* v_nextMacroScope_3159_; lean_object* v_ngen_3160_; lean_object* v_auxDeclNGen_3161_; lean_object* v_traceState_3162_; lean_object* v_messages_3163_; lean_object* v_infoState_3164_; lean_object* v_snapshotTasks_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3169_; 
v_env_3158_ = lean_ctor_get(v___x_3141_, 0);
lean_inc_ref(v_env_3158_);
v_nextMacroScope_3159_ = lean_ctor_get(v___x_3141_, 1);
lean_inc(v_nextMacroScope_3159_);
v_ngen_3160_ = lean_ctor_get(v___x_3141_, 2);
lean_inc_ref(v_ngen_3160_);
v_auxDeclNGen_3161_ = lean_ctor_get(v___x_3141_, 3);
lean_inc_ref(v_auxDeclNGen_3161_);
v_traceState_3162_ = lean_ctor_get(v___x_3141_, 4);
lean_inc_ref(v_traceState_3162_);
v_messages_3163_ = lean_ctor_get(v___x_3141_, 6);
lean_inc_ref(v_messages_3163_);
v_infoState_3164_ = lean_ctor_get(v___x_3141_, 7);
lean_inc_ref(v_infoState_3164_);
v_snapshotTasks_3165_ = lean_ctor_get(v___x_3141_, 8);
lean_inc_ref(v_snapshotTasks_3165_);
lean_dec(v___x_3141_);
v___x_3166_ = l_Lean_maxRecDepth;
v___x_3167_ = l_Lean_Option_get___at___00main_spec__9(v___x_2941_, v___x_3166_);
lean_inc_ref(v___x_2941_);
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 4, v___x_3167_);
lean_ctor_set(v___x_3156_, 2, v___x_2941_);
v___x_3169_ = v___x_3156_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_fileName_3142_);
lean_ctor_set(v_reuseFailAlloc_3183_, 1, v_fileMap_3143_);
lean_ctor_set(v_reuseFailAlloc_3183_, 2, v___x_2941_);
lean_ctor_set(v_reuseFailAlloc_3183_, 3, v_currRecDepth_3144_);
lean_ctor_set(v_reuseFailAlloc_3183_, 4, v___x_3167_);
lean_ctor_set(v_reuseFailAlloc_3183_, 5, v_ref_3145_);
lean_ctor_set(v_reuseFailAlloc_3183_, 6, v_currNamespace_3146_);
lean_ctor_set(v_reuseFailAlloc_3183_, 7, v_openDecls_3147_);
lean_ctor_set(v_reuseFailAlloc_3183_, 8, v_initHeartbeats_3148_);
lean_ctor_set(v_reuseFailAlloc_3183_, 9, v_maxHeartbeats_3149_);
lean_ctor_set(v_reuseFailAlloc_3183_, 10, v_quotContext_3150_);
lean_ctor_set(v_reuseFailAlloc_3183_, 11, v_currMacroScope_3151_);
lean_ctor_set(v_reuseFailAlloc_3183_, 12, v_cancelTk_x3f_3152_);
lean_ctor_set(v_reuseFailAlloc_3183_, 13, v_inheritedTraceOptions_3154_);
lean_ctor_set_uint8(v_reuseFailAlloc_3183_, sizeof(void*)*14 + 1, v_suppressElabErrors_3153_);
v___x_3169_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
lean_object* v___x_3170_; uint8_t v___x_3171_; 
lean_ctor_set_uint8(v___x_3169_, sizeof(void*)*14, v___y_3135_);
v___x_3170_ = lean_array_get_size(v___y_3129_);
v___x_3171_ = lean_nat_dec_lt(v___x_2940_, v___x_3170_);
if (v___x_3171_ == 0)
{
lean_object* v___x_3172_; 
lean_inc_ref(v___y_3138_);
v___x_3172_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3138_, v_env_3158_, v___x_2934_);
v___y_3074_ = v___y_3117_;
v___y_3075_ = v___y_3118_;
v___y_3076_ = v___y_3119_;
v___y_3077_ = v___y_3121_;
v___y_3078_ = v___y_3120_;
v___y_3079_ = v___y_3122_;
v___y_3080_ = v___y_3123_;
v___y_3081_ = v___y_3124_;
v___y_3082_ = v___y_3125_;
v___y_3083_ = v___x_3169_;
v___y_3084_ = v___y_3126_;
v___y_3085_ = v___y_3127_;
v___y_3086_ = v___y_3128_;
v___y_3087_ = v___y_3129_;
v___y_3088_ = v___y_3130_;
v___y_3089_ = v___y_3131_;
v_nextMacroScope_3090_ = v_nextMacroScope_3159_;
v_ngen_3091_ = v_ngen_3160_;
v_auxDeclNGen_3092_ = v_auxDeclNGen_3161_;
v_traceState_3093_ = v_traceState_3162_;
v_messages_3094_ = v_messages_3163_;
v_infoState_3095_ = v_infoState_3164_;
v_snapshotTasks_3096_ = v_snapshotTasks_3165_;
v___y_3097_ = v___y_3132_;
v___y_3098_ = v___y_3133_;
v___y_3099_ = v___y_3134_;
v___y_3100_ = v___y_3136_;
v___y_3101_ = v___y_3140_;
v___y_3102_ = v___y_3137_;
v___y_3103_ = v___x_3172_;
goto v___jp_3073_;
}
else
{
uint8_t v___x_3173_; 
v___x_3173_ = lean_nat_dec_le(v___x_3170_, v___x_3170_);
if (v___x_3173_ == 0)
{
if (v___x_3171_ == 0)
{
lean_object* v___x_3174_; 
lean_inc_ref(v___y_3138_);
v___x_3174_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3138_, v_env_3158_, v___x_2934_);
v___y_3074_ = v___y_3117_;
v___y_3075_ = v___y_3118_;
v___y_3076_ = v___y_3119_;
v___y_3077_ = v___y_3121_;
v___y_3078_ = v___y_3120_;
v___y_3079_ = v___y_3122_;
v___y_3080_ = v___y_3123_;
v___y_3081_ = v___y_3124_;
v___y_3082_ = v___y_3125_;
v___y_3083_ = v___x_3169_;
v___y_3084_ = v___y_3126_;
v___y_3085_ = v___y_3127_;
v___y_3086_ = v___y_3128_;
v___y_3087_ = v___y_3129_;
v___y_3088_ = v___y_3130_;
v___y_3089_ = v___y_3131_;
v_nextMacroScope_3090_ = v_nextMacroScope_3159_;
v_ngen_3091_ = v_ngen_3160_;
v_auxDeclNGen_3092_ = v_auxDeclNGen_3161_;
v_traceState_3093_ = v_traceState_3162_;
v_messages_3094_ = v_messages_3163_;
v_infoState_3095_ = v_infoState_3164_;
v_snapshotTasks_3096_ = v_snapshotTasks_3165_;
v___y_3097_ = v___y_3132_;
v___y_3098_ = v___y_3133_;
v___y_3099_ = v___y_3134_;
v___y_3100_ = v___y_3136_;
v___y_3101_ = v___y_3140_;
v___y_3102_ = v___y_3137_;
v___y_3103_ = v___x_3174_;
goto v___jp_3073_;
}
else
{
size_t v___x_3175_; size_t v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3175_ = ((size_t)0ULL);
v___x_3176_ = lean_usize_of_nat(v___x_3170_);
v___x_3177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3129_, v___x_3175_, v___x_3176_, v___x_2934_);
lean_inc_ref(v___y_3138_);
v___x_3178_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3138_, v_env_3158_, v___x_3177_);
v___y_3074_ = v___y_3117_;
v___y_3075_ = v___y_3118_;
v___y_3076_ = v___y_3119_;
v___y_3077_ = v___y_3121_;
v___y_3078_ = v___y_3120_;
v___y_3079_ = v___y_3122_;
v___y_3080_ = v___y_3123_;
v___y_3081_ = v___y_3124_;
v___y_3082_ = v___y_3125_;
v___y_3083_ = v___x_3169_;
v___y_3084_ = v___y_3126_;
v___y_3085_ = v___y_3127_;
v___y_3086_ = v___y_3128_;
v___y_3087_ = v___y_3129_;
v___y_3088_ = v___y_3130_;
v___y_3089_ = v___y_3131_;
v_nextMacroScope_3090_ = v_nextMacroScope_3159_;
v_ngen_3091_ = v_ngen_3160_;
v_auxDeclNGen_3092_ = v_auxDeclNGen_3161_;
v_traceState_3093_ = v_traceState_3162_;
v_messages_3094_ = v_messages_3163_;
v_infoState_3095_ = v_infoState_3164_;
v_snapshotTasks_3096_ = v_snapshotTasks_3165_;
v___y_3097_ = v___y_3132_;
v___y_3098_ = v___y_3133_;
v___y_3099_ = v___y_3134_;
v___y_3100_ = v___y_3136_;
v___y_3101_ = v___y_3140_;
v___y_3102_ = v___y_3137_;
v___y_3103_ = v___x_3178_;
goto v___jp_3073_;
}
}
else
{
size_t v___x_3179_; size_t v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3179_ = ((size_t)0ULL);
v___x_3180_ = lean_usize_of_nat(v___x_3170_);
v___x_3181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3129_, v___x_3179_, v___x_3180_, v___x_2934_);
lean_inc_ref(v___y_3138_);
v___x_3182_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3138_, v_env_3158_, v___x_3181_);
v___y_3074_ = v___y_3117_;
v___y_3075_ = v___y_3118_;
v___y_3076_ = v___y_3119_;
v___y_3077_ = v___y_3121_;
v___y_3078_ = v___y_3120_;
v___y_3079_ = v___y_3122_;
v___y_3080_ = v___y_3123_;
v___y_3081_ = v___y_3124_;
v___y_3082_ = v___y_3125_;
v___y_3083_ = v___x_3169_;
v___y_3084_ = v___y_3126_;
v___y_3085_ = v___y_3127_;
v___y_3086_ = v___y_3128_;
v___y_3087_ = v___y_3129_;
v___y_3088_ = v___y_3130_;
v___y_3089_ = v___y_3131_;
v_nextMacroScope_3090_ = v_nextMacroScope_3159_;
v_ngen_3091_ = v_ngen_3160_;
v_auxDeclNGen_3092_ = v_auxDeclNGen_3161_;
v_traceState_3093_ = v_traceState_3162_;
v_messages_3094_ = v_messages_3163_;
v_infoState_3095_ = v_infoState_3164_;
v_snapshotTasks_3096_ = v_snapshotTasks_3165_;
v___y_3097_ = v___y_3132_;
v___y_3098_ = v___y_3133_;
v___y_3099_ = v___y_3134_;
v___y_3100_ = v___y_3136_;
v___y_3101_ = v___y_3140_;
v___y_3102_ = v___y_3137_;
v___y_3103_ = v___x_3182_;
goto v___jp_3073_;
}
}
}
}
}
v___jp_3187_:
{
if (v___y_3211_ == 0)
{
lean_object* v___x_3212_; lean_object* v_env_3213_; lean_object* v_nextMacroScope_3214_; lean_object* v_ngen_3215_; lean_object* v_auxDeclNGen_3216_; lean_object* v_traceState_3217_; lean_object* v_messages_3218_; lean_object* v_infoState_3219_; lean_object* v_snapshotTasks_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3229_; 
v___x_3212_ = lean_st_ref_take(v___y_3209_);
v_env_3213_ = lean_ctor_get(v___x_3212_, 0);
v_nextMacroScope_3214_ = lean_ctor_get(v___x_3212_, 1);
v_ngen_3215_ = lean_ctor_get(v___x_3212_, 2);
v_auxDeclNGen_3216_ = lean_ctor_get(v___x_3212_, 3);
v_traceState_3217_ = lean_ctor_get(v___x_3212_, 4);
v_messages_3218_ = lean_ctor_get(v___x_3212_, 6);
v_infoState_3219_ = lean_ctor_get(v___x_3212_, 7);
v_snapshotTasks_3220_ = lean_ctor_get(v___x_3212_, 8);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3229_ == 0)
{
lean_object* v_unused_3230_; 
v_unused_3230_ = lean_ctor_get(v___x_3212_, 5);
lean_dec(v_unused_3230_);
v___x_3222_ = v___x_3212_;
v_isShared_3223_ = v_isSharedCheck_3229_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_snapshotTasks_3220_);
lean_inc(v_infoState_3219_);
lean_inc(v_messages_3218_);
lean_inc(v_traceState_3217_);
lean_inc(v_auxDeclNGen_3216_);
lean_inc(v_ngen_3215_);
lean_inc(v_nextMacroScope_3214_);
lean_inc(v_env_3213_);
lean_dec(v___x_3212_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3229_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3224_; lean_object* v___x_3226_; 
v___x_3224_ = l_Lean_Kernel_enableDiag(v_env_3213_, v___y_3208_);
lean_inc_ref(v___y_3203_);
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 5, v___y_3203_);
lean_ctor_set(v___x_3222_, 0, v___x_3224_);
v___x_3226_ = v___x_3222_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3224_);
lean_ctor_set(v_reuseFailAlloc_3228_, 1, v_nextMacroScope_3214_);
lean_ctor_set(v_reuseFailAlloc_3228_, 2, v_ngen_3215_);
lean_ctor_set(v_reuseFailAlloc_3228_, 3, v_auxDeclNGen_3216_);
lean_ctor_set(v_reuseFailAlloc_3228_, 4, v_traceState_3217_);
lean_ctor_set(v_reuseFailAlloc_3228_, 5, v___y_3203_);
lean_ctor_set(v_reuseFailAlloc_3228_, 6, v_messages_3218_);
lean_ctor_set(v_reuseFailAlloc_3228_, 7, v_infoState_3219_);
lean_ctor_set(v_reuseFailAlloc_3228_, 8, v_snapshotTasks_3220_);
v___x_3226_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
lean_object* v___x_3227_; 
v___x_3227_ = lean_st_ref_set(v___y_3209_, v___x_3226_);
lean_inc(v___y_3209_);
v___y_3117_ = v___y_3188_;
v___y_3118_ = v___y_3189_;
v___y_3119_ = v___y_3190_;
v___y_3120_ = v___y_3192_;
v___y_3121_ = v___y_3191_;
v___y_3122_ = v___y_3193_;
v___y_3123_ = v___y_3194_;
v___y_3124_ = v___y_3195_;
v___y_3125_ = v___y_3196_;
v___y_3126_ = v___y_3197_;
v___y_3127_ = v___y_3198_;
v___y_3128_ = v___y_3199_;
v___y_3129_ = v___y_3200_;
v___y_3130_ = v___y_3201_;
v___y_3131_ = v___y_3202_;
v___y_3132_ = v___y_3203_;
v___y_3133_ = v___y_3204_;
v___y_3134_ = v___y_3206_;
v___y_3135_ = v___y_3208_;
v___y_3136_ = v___y_3207_;
v___y_3137_ = v___y_3209_;
v___y_3138_ = v___y_3210_;
v___y_3139_ = v___y_3205_;
v___y_3140_ = v___y_3209_;
goto v___jp_3116_;
}
}
}
else
{
lean_inc(v___y_3209_);
v___y_3117_ = v___y_3188_;
v___y_3118_ = v___y_3189_;
v___y_3119_ = v___y_3190_;
v___y_3120_ = v___y_3192_;
v___y_3121_ = v___y_3191_;
v___y_3122_ = v___y_3193_;
v___y_3123_ = v___y_3194_;
v___y_3124_ = v___y_3195_;
v___y_3125_ = v___y_3196_;
v___y_3126_ = v___y_3197_;
v___y_3127_ = v___y_3198_;
v___y_3128_ = v___y_3199_;
v___y_3129_ = v___y_3200_;
v___y_3130_ = v___y_3201_;
v___y_3131_ = v___y_3202_;
v___y_3132_ = v___y_3203_;
v___y_3133_ = v___y_3204_;
v___y_3134_ = v___y_3206_;
v___y_3135_ = v___y_3208_;
v___y_3136_ = v___y_3207_;
v___y_3137_ = v___y_3209_;
v___y_3138_ = v___y_3210_;
v___y_3139_ = v___y_3205_;
v___y_3140_ = v___y_3209_;
goto v___jp_3116_;
}
}
v___jp_3234_:
{
lean_object* v___x_3244_; 
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 1, v___y_3242_);
lean_ctor_set(v___x_2926_, 0, v___y_3239_);
v___x_3244_ = v___x_2926_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___y_3239_);
lean_ctor_set(v_reuseFailAlloc_3339_, 1, v___y_3242_);
v___x_3244_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v_moduleData_3248_; lean_object* v___x_3249_; uint8_t v___x_3250_; 
v___x_3245_ = lean_box(0);
lean_inc_ref(v___y_3241_);
v___x_3246_ = l_Lean_EnvExtension_setState___redArg(v___y_3241_, v___y_3240_, v___x_3244_, v___x_3245_);
v___x_3247_ = l_Lean_Environment_header(v___x_3246_);
v_moduleData_3248_ = lean_ctor_get(v___x_3247_, 6);
lean_inc_ref(v_moduleData_3248_);
lean_dec_ref(v___x_3247_);
v___x_3249_ = lean_array_get_size(v_moduleData_3248_);
v___x_3250_ = lean_nat_dec_lt(v___y_3238_, v___x_3249_);
if (v___x_3250_ == 0)
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
lean_dec_ref(v_moduleData_3248_);
lean_dec_ref(v___x_3246_);
lean_dec(v___y_3238_);
lean_dec(v___y_3237_);
lean_dec(v___y_3235_);
lean_dec_ref(v___x_2941_);
lean_dec(v_fst_2923_);
lean_dec(v_name_2910_);
lean_dec(v_head_2903_);
lean_dec(v_head_2902_);
v___x_3251_ = lean_obj_once(&l_main___closed__21, &l_main___closed__21_once, _init_l_main___closed__21);
v___x_3252_ = l_panic___at___00main_spec__5(v___x_3251_);
return v___x_3252_;
}
else
{
lean_object* v_base_3253_; lean_object* v_private_3254_; lean_object* v_header_3255_; lean_object* v_serverBaseExts_3256_; lean_object* v_checked_3257_; lean_object* v_asyncConstsMap_3258_; lean_object* v_asyncCtx_x3f_3259_; lean_object* v_importRealizationCtx_x3f_3260_; lean_object* v_localRealizationCtxMap_3261_; lean_object* v_allRealizations_3262_; uint8_t v_isExporting_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3337_; 
v_base_3253_ = lean_ctor_get(v___x_3246_, 0);
lean_inc_ref(v_base_3253_);
v_private_3254_ = lean_ctor_get(v_base_3253_, 0);
lean_inc(v_private_3254_);
v_header_3255_ = lean_ctor_get(v_private_3254_, 5);
lean_inc_ref(v_header_3255_);
v_serverBaseExts_3256_ = lean_ctor_get(v___x_3246_, 1);
v_checked_3257_ = lean_ctor_get(v___x_3246_, 2);
v_asyncConstsMap_3258_ = lean_ctor_get(v___x_3246_, 3);
v_asyncCtx_x3f_3259_ = lean_ctor_get(v___x_3246_, 4);
v_importRealizationCtx_x3f_3260_ = lean_ctor_get(v___x_3246_, 5);
v_localRealizationCtxMap_3261_ = lean_ctor_get(v___x_3246_, 6);
v_allRealizations_3262_ = lean_ctor_get(v___x_3246_, 7);
v_isExporting_3263_ = lean_ctor_get_uint8(v___x_3246_, sizeof(void*)*8);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3337_ == 0)
{
lean_object* v_unused_3338_; 
v_unused_3338_ = lean_ctor_get(v___x_3246_, 0);
lean_dec(v_unused_3338_);
v___x_3265_ = v___x_3246_;
v_isShared_3266_ = v_isSharedCheck_3337_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_allRealizations_3262_);
lean_inc(v_localRealizationCtxMap_3261_);
lean_inc(v_importRealizationCtx_x3f_3260_);
lean_inc(v_asyncCtx_x3f_3259_);
lean_inc(v_asyncConstsMap_3258_);
lean_inc(v_checked_3257_);
lean_inc(v_serverBaseExts_3256_);
lean_dec(v___x_3246_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3337_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v_public_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3335_; 
v_public_3267_ = lean_ctor_get(v_base_3253_, 1);
v_isSharedCheck_3335_ = !lean_is_exclusive(v_base_3253_);
if (v_isSharedCheck_3335_ == 0)
{
lean_object* v_unused_3336_; 
v_unused_3336_ = lean_ctor_get(v_base_3253_, 0);
lean_dec(v_unused_3336_);
v___x_3269_ = v_base_3253_;
v_isShared_3270_ = v_isSharedCheck_3335_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_public_3267_);
lean_dec(v_base_3253_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3335_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v_constants_3271_; uint8_t v_quotInit_3272_; lean_object* v_diagnostics_3273_; lean_object* v_const2ModIdx_3274_; lean_object* v_extensions_3275_; lean_object* v_irBaseExts_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3333_; 
v_constants_3271_ = lean_ctor_get(v_private_3254_, 0);
v_quotInit_3272_ = lean_ctor_get_uint8(v_private_3254_, sizeof(void*)*6);
v_diagnostics_3273_ = lean_ctor_get(v_private_3254_, 1);
v_const2ModIdx_3274_ = lean_ctor_get(v_private_3254_, 2);
v_extensions_3275_ = lean_ctor_get(v_private_3254_, 3);
v_irBaseExts_3276_ = lean_ctor_get(v_private_3254_, 4);
v_isSharedCheck_3333_ = !lean_is_exclusive(v_private_3254_);
if (v_isSharedCheck_3333_ == 0)
{
lean_object* v_unused_3334_; 
v_unused_3334_ = lean_ctor_get(v_private_3254_, 5);
lean_dec(v_unused_3334_);
v___x_3278_ = v_private_3254_;
v_isShared_3279_ = v_isSharedCheck_3333_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_irBaseExts_3276_);
lean_inc(v_extensions_3275_);
lean_inc(v_const2ModIdx_3274_);
lean_inc(v_diagnostics_3273_);
lean_inc(v_constants_3271_);
lean_dec(v_private_3254_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3333_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
uint32_t v_trustLevel_3280_; lean_object* v_mainModule_3281_; uint8_t v_isModule_3282_; lean_object* v_regions_3283_; lean_object* v_modules_3284_; lean_object* v_moduleName2Idx_3285_; lean_object* v_importAllModules_3286_; lean_object* v_moduleData_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3331_; 
v_trustLevel_3280_ = lean_ctor_get_uint32(v_header_3255_, sizeof(void*)*7);
v_mainModule_3281_ = lean_ctor_get(v_header_3255_, 0);
v_isModule_3282_ = lean_ctor_get_uint8(v_header_3255_, sizeof(void*)*7 + 4);
v_regions_3283_ = lean_ctor_get(v_header_3255_, 2);
v_modules_3284_ = lean_ctor_get(v_header_3255_, 3);
v_moduleName2Idx_3285_ = lean_ctor_get(v_header_3255_, 4);
v_importAllModules_3286_ = lean_ctor_get(v_header_3255_, 5);
v_moduleData_3287_ = lean_ctor_get(v_header_3255_, 6);
v_isSharedCheck_3331_ = !lean_is_exclusive(v_header_3255_);
if (v_isSharedCheck_3331_ == 0)
{
lean_object* v_unused_3332_; 
v_unused_3332_ = lean_ctor_get(v_header_3255_, 1);
lean_dec(v_unused_3332_);
v___x_3289_ = v_header_3255_;
v_isShared_3290_ = v_isSharedCheck_3331_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_moduleData_3287_);
lean_inc(v_importAllModules_3286_);
lean_inc(v_moduleName2Idx_3285_);
lean_inc(v_modules_3284_);
lean_inc(v_regions_3283_);
lean_inc(v_mainModule_3281_);
lean_dec(v_header_3255_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3331_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___x_3291_; lean_object* v_imports_3292_; lean_object* v___x_3294_; 
v___x_3291_ = lean_array_fget(v_moduleData_3248_, v___y_3238_);
lean_dec_ref(v_moduleData_3248_);
v_imports_3292_ = lean_ctor_get(v___x_3291_, 0);
lean_inc_ref(v_imports_3292_);
lean_dec(v___x_3291_);
if (v_isShared_3290_ == 0)
{
lean_ctor_set(v___x_3289_, 1, v_imports_3292_);
v___x_3294_ = v___x_3289_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 7, 5);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_mainModule_3281_);
lean_ctor_set(v_reuseFailAlloc_3330_, 1, v_imports_3292_);
lean_ctor_set(v_reuseFailAlloc_3330_, 2, v_regions_3283_);
lean_ctor_set(v_reuseFailAlloc_3330_, 3, v_modules_3284_);
lean_ctor_set(v_reuseFailAlloc_3330_, 4, v_moduleName2Idx_3285_);
lean_ctor_set(v_reuseFailAlloc_3330_, 5, v_importAllModules_3286_);
lean_ctor_set(v_reuseFailAlloc_3330_, 6, v_moduleData_3287_);
lean_ctor_set_uint32(v_reuseFailAlloc_3330_, sizeof(void*)*7, v_trustLevel_3280_);
lean_ctor_set_uint8(v_reuseFailAlloc_3330_, sizeof(void*)*7 + 4, v_isModule_3282_);
v___x_3294_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
lean_object* v___x_3296_; 
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 5, v___x_3294_);
v___x_3296_ = v___x_3278_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_constants_3271_);
lean_ctor_set(v_reuseFailAlloc_3329_, 1, v_diagnostics_3273_);
lean_ctor_set(v_reuseFailAlloc_3329_, 2, v_const2ModIdx_3274_);
lean_ctor_set(v_reuseFailAlloc_3329_, 3, v_extensions_3275_);
lean_ctor_set(v_reuseFailAlloc_3329_, 4, v_irBaseExts_3276_);
lean_ctor_set(v_reuseFailAlloc_3329_, 5, v___x_3294_);
lean_ctor_set_uint8(v_reuseFailAlloc_3329_, sizeof(void*)*6, v_quotInit_3272_);
v___x_3296_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
lean_object* v___x_3298_; 
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 0, v___x_3296_);
v___x_3298_ = v___x_3269_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v___x_3296_);
lean_ctor_set(v_reuseFailAlloc_3328_, 1, v_public_3267_);
v___x_3298_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
lean_object* v___x_3300_; 
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 0, v___x_3298_);
v___x_3300_ = v___x_3265_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v___x_3298_);
lean_ctor_set(v_reuseFailAlloc_3327_, 1, v_serverBaseExts_3256_);
lean_ctor_set(v_reuseFailAlloc_3327_, 2, v_checked_3257_);
lean_ctor_set(v_reuseFailAlloc_3327_, 3, v_asyncConstsMap_3258_);
lean_ctor_set(v_reuseFailAlloc_3327_, 4, v_asyncCtx_x3f_3259_);
lean_ctor_set(v_reuseFailAlloc_3327_, 5, v_importRealizationCtx_x3f_3260_);
lean_ctor_set(v_reuseFailAlloc_3327_, 6, v_localRealizationCtxMap_3261_);
lean_ctor_set(v_reuseFailAlloc_3327_, 7, v_allRealizations_3262_);
lean_ctor_set_uint8(v_reuseFailAlloc_3327_, sizeof(void*)*8, v_isExporting_3263_);
v___x_3300_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v_env_3323_; lean_object* v___x_3324_; uint8_t v___x_3325_; uint8_t v___x_3326_; 
v___x_3301_ = l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
v___x_3302_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2935_, v___x_3301_, v___x_3300_, v___y_3238_, v___y_3236_);
lean_dec(v___y_3238_);
v___x_3303_ = l_Lean_firstFrontendMacroScope;
v___x_3304_ = lean_obj_once(&l_main___closed__22, &l_main___closed__22_once, _init_l_main___closed__22);
v___x_3305_ = ((lean_object*)(l_main___closed__25));
lean_inc_n(v___y_3237_, 3);
v___x_3306_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3306_, 0, v___y_3237_);
lean_ctor_set(v___x_3306_, 1, v___x_3233_);
lean_ctor_set(v___x_3306_, 2, v___x_2921_);
v___x_3307_ = lean_obj_once(&l_main___closed__26, &l_main___closed__26_once, _init_l_main___closed__26);
v___x_3308_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_3309_ = lean_obj_once(&l_main___closed__30, &l_main___closed__30_once, _init_l_main___closed__30);
v___x_3310_ = lean_obj_once(&l_main___closed__31, &l_main___closed__31_once, _init_l_main___closed__31);
v___x_3311_ = ((lean_object*)(l_main___closed__32));
lean_inc_ref(v___x_3306_);
v___x_3312_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3300_);
lean_ctor_set(v___x_3312_, 1, v___x_3304_);
lean_ctor_set(v___x_3312_, 2, v___x_3305_);
lean_ctor_set(v___x_3312_, 3, v___x_3306_);
lean_ctor_set(v___x_3312_, 4, v___x_3307_);
lean_ctor_set(v___x_3312_, 5, v___x_3308_);
lean_ctor_set(v___x_3312_, 6, v___x_3309_);
lean_ctor_set(v___x_3312_, 7, v___x_3310_);
lean_ctor_set(v___x_3312_, 8, v___x_3311_);
v___x_3313_ = lean_st_mk_ref(v___x_3312_);
v___x_3314_ = l_Lean_inheritedTraceOptions;
v___x_3315_ = lean_st_ref_get(v___x_3314_);
v___x_3316_ = lean_st_ref_get(v___x_3313_);
v___x_3317_ = l_Lean_instInhabitedFileMap_default;
v___x_3318_ = lean_unsigned_to_nat(1000u);
v___x_3319_ = lean_box(0);
v___x_3320_ = l_Lean_Core_getMaxHeartbeats(v___x_2941_);
v___x_3321_ = lean_box(0);
lean_inc_ref(v___x_2941_);
lean_inc(v_head_2902_);
v___x_3322_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3322_, 0, v_head_2902_);
lean_ctor_set(v___x_3322_, 1, v___x_3317_);
lean_ctor_set(v___x_3322_, 2, v___x_2941_);
lean_ctor_set(v___x_3322_, 3, v___x_2940_);
lean_ctor_set(v___x_3322_, 4, v___x_3318_);
lean_ctor_set(v___x_3322_, 5, v___x_3319_);
lean_ctor_set(v___x_3322_, 6, v___y_3237_);
lean_ctor_set(v___x_3322_, 7, v___x_2921_);
lean_ctor_set(v___x_3322_, 8, v___x_2940_);
lean_ctor_set(v___x_3322_, 9, v___x_3320_);
lean_ctor_set(v___x_3322_, 10, v___y_3237_);
lean_ctor_set(v___x_3322_, 11, v___x_3303_);
lean_ctor_set(v___x_3322_, 12, v___x_3321_);
lean_ctor_set(v___x_3322_, 13, v___x_3315_);
lean_ctor_set_uint8(v___x_3322_, sizeof(void*)*14, v___x_2912_);
lean_ctor_set_uint8(v___x_3322_, sizeof(void*)*14 + 1, v___x_2912_);
v_env_3323_ = lean_ctor_get(v___x_3316_, 0);
lean_inc_ref(v_env_3323_);
lean_dec(v___x_3316_);
v___x_3324_ = l_Lean_diagnostics;
v___x_3325_ = l_Lean_Option_get___at___00main_spec__8(v___x_2941_, v___x_3324_);
v___x_3326_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3323_);
lean_dec_ref(v_env_3323_);
if (v___x_3326_ == 0)
{
if (v___x_3325_ == 0)
{
v___y_3188_ = v___x_3303_;
v___y_3189_ = v___x_3308_;
v___y_3190_ = v___x_3250_;
v___y_3191_ = v___y_3235_;
v___y_3192_ = v___x_2921_;
v___y_3193_ = v___x_3319_;
v___y_3194_ = v___x_3314_;
v___y_3195_ = v___x_3317_;
v___y_3196_ = v___x_3321_;
v___y_3197_ = v___x_3311_;
v___y_3198_ = v___x_3305_;
v___y_3199_ = v___x_3306_;
v___y_3200_ = v___x_3302_;
v___y_3201_ = v___x_3307_;
v___y_3202_ = v___x_3309_;
v___y_3203_ = v___x_3308_;
v___y_3204_ = v___x_3304_;
v___y_3205_ = v___x_3322_;
v___y_3206_ = v___y_3237_;
v___y_3207_ = v___x_3310_;
v___y_3208_ = v___x_3325_;
v___y_3209_ = v___x_3313_;
v___y_3210_ = v___x_3301_;
v___y_3211_ = v___x_3250_;
goto v___jp_3187_;
}
else
{
v___y_3188_ = v___x_3303_;
v___y_3189_ = v___x_3308_;
v___y_3190_ = v___x_3250_;
v___y_3191_ = v___y_3235_;
v___y_3192_ = v___x_2921_;
v___y_3193_ = v___x_3319_;
v___y_3194_ = v___x_3314_;
v___y_3195_ = v___x_3317_;
v___y_3196_ = v___x_3321_;
v___y_3197_ = v___x_3311_;
v___y_3198_ = v___x_3305_;
v___y_3199_ = v___x_3306_;
v___y_3200_ = v___x_3302_;
v___y_3201_ = v___x_3307_;
v___y_3202_ = v___x_3309_;
v___y_3203_ = v___x_3308_;
v___y_3204_ = v___x_3304_;
v___y_3205_ = v___x_3322_;
v___y_3206_ = v___y_3237_;
v___y_3207_ = v___x_3310_;
v___y_3208_ = v___x_3325_;
v___y_3209_ = v___x_3313_;
v___y_3210_ = v___x_3301_;
v___y_3211_ = v___x_3326_;
goto v___jp_3187_;
}
}
else
{
v___y_3188_ = v___x_3303_;
v___y_3189_ = v___x_3308_;
v___y_3190_ = v___x_3250_;
v___y_3191_ = v___y_3235_;
v___y_3192_ = v___x_2921_;
v___y_3193_ = v___x_3319_;
v___y_3194_ = v___x_3314_;
v___y_3195_ = v___x_3317_;
v___y_3196_ = v___x_3321_;
v___y_3197_ = v___x_3311_;
v___y_3198_ = v___x_3305_;
v___y_3199_ = v___x_3306_;
v___y_3200_ = v___x_3302_;
v___y_3201_ = v___x_3307_;
v___y_3202_ = v___x_3309_;
v___y_3203_ = v___x_3308_;
v___y_3204_ = v___x_3304_;
v___y_3205_ = v___x_3322_;
v___y_3206_ = v___y_3237_;
v___y_3207_ = v___x_3310_;
v___y_3208_ = v___x_3325_;
v___y_3209_ = v___x_3313_;
v___y_3210_ = v___x_3301_;
v___y_3211_ = v___x_3325_;
goto v___jp_3187_;
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
v___jp_3340_:
{
lean_object* v___x_3346_; lean_object* v_toEnvExtension_3347_; lean_object* v_asyncMode_3348_; lean_object* v___x_3349_; lean_object* v_importedEntries_3350_; lean_object* v_state_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; uint8_t v___x_3354_; 
v___x_3346_ = l_Lean_IR_declMapExt;
v_toEnvExtension_3347_ = lean_ctor_get(v___x_3346_, 0);
v_asyncMode_3348_ = lean_ctor_get(v_toEnvExtension_3347_, 2);
lean_inc(v___y_3343_);
lean_inc_ref(v___y_3345_);
v___x_3349_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2932_, v_toEnvExtension_3347_, v___y_3345_, v_asyncMode_3348_, v___y_3343_);
v_importedEntries_3350_ = lean_ctor_get(v___x_3349_, 0);
lean_inc_ref(v_importedEntries_3350_);
v_state_3351_ = lean_ctor_get(v___x_3349_, 1);
lean_inc(v_state_3351_);
lean_dec(v___x_3349_);
v___x_3352_ = lean_array_get_borrowed(v___x_2933_, v_importedEntries_3350_, v___y_3344_);
v___x_3353_ = lean_array_get_size(v___x_3352_);
v___x_3354_ = lean_nat_dec_lt(v___x_2940_, v___x_3353_);
if (v___x_3354_ == 0)
{
v___y_3235_ = v___y_3341_;
v___y_3236_ = v___y_3342_;
v___y_3237_ = v___y_3343_;
v___y_3238_ = v___y_3344_;
v___y_3239_ = v_importedEntries_3350_;
v___y_3240_ = v___y_3345_;
v___y_3241_ = v_toEnvExtension_3347_;
v___y_3242_ = v_state_3351_;
goto v___jp_3234_;
}
else
{
uint8_t v___x_3355_; 
v___x_3355_ = lean_nat_dec_le(v___x_3353_, v___x_3353_);
if (v___x_3355_ == 0)
{
if (v___x_3354_ == 0)
{
v___y_3235_ = v___y_3341_;
v___y_3236_ = v___y_3342_;
v___y_3237_ = v___y_3343_;
v___y_3238_ = v___y_3344_;
v___y_3239_ = v_importedEntries_3350_;
v___y_3240_ = v___y_3345_;
v___y_3241_ = v_toEnvExtension_3347_;
v___y_3242_ = v_state_3351_;
goto v___jp_3234_;
}
else
{
size_t v___x_3356_; size_t v___x_3357_; lean_object* v___x_3358_; 
v___x_3356_ = ((size_t)0ULL);
v___x_3357_ = lean_usize_of_nat(v___x_3353_);
lean_inc_ref(v___y_3345_);
v___x_3358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3345_, v___x_3352_, v___x_3356_, v___x_3357_, v_state_3351_);
v___y_3235_ = v___y_3341_;
v___y_3236_ = v___y_3342_;
v___y_3237_ = v___y_3343_;
v___y_3238_ = v___y_3344_;
v___y_3239_ = v_importedEntries_3350_;
v___y_3240_ = v___y_3345_;
v___y_3241_ = v_toEnvExtension_3347_;
v___y_3242_ = v___x_3358_;
goto v___jp_3234_;
}
}
else
{
size_t v___x_3359_; size_t v___x_3360_; lean_object* v___x_3361_; 
v___x_3359_ = ((size_t)0ULL);
v___x_3360_ = lean_usize_of_nat(v___x_3353_);
lean_inc_ref(v___y_3345_);
v___x_3361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3345_, v___x_3352_, v___x_3359_, v___x_3360_, v_state_3351_);
v___y_3235_ = v___y_3341_;
v___y_3236_ = v___y_3342_;
v___y_3237_ = v___y_3343_;
v___y_3238_ = v___y_3344_;
v___y_3239_ = v_importedEntries_3350_;
v___y_3240_ = v___y_3345_;
v___y_3241_ = v_toEnvExtension_3347_;
v___y_3242_ = v___x_3361_;
goto v___jp_3234_;
}
}
}
v___jp_3362_:
{
uint8_t v___x_3370_; 
v___x_3370_ = lean_nat_dec_lt(v___x_2940_, v___y_3364_);
if (v___x_3370_ == 0)
{
lean_dec_ref(v___y_3366_);
lean_dec(v___y_3364_);
v___y_3341_ = v___y_3363_;
v___y_3342_ = v___y_3365_;
v___y_3343_ = v___y_3367_;
v___y_3344_ = v___y_3368_;
v___y_3345_ = v___y_3369_;
goto v___jp_3340_;
}
else
{
uint8_t v___x_3371_; 
v___x_3371_ = lean_nat_dec_le(v___y_3364_, v___y_3364_);
if (v___x_3371_ == 0)
{
if (v___x_3370_ == 0)
{
lean_dec_ref(v___y_3366_);
lean_dec(v___y_3364_);
v___y_3341_ = v___y_3363_;
v___y_3342_ = v___y_3365_;
v___y_3343_ = v___y_3367_;
v___y_3344_ = v___y_3368_;
v___y_3345_ = v___y_3369_;
goto v___jp_3340_;
}
else
{
size_t v___x_3372_; size_t v___x_3373_; lean_object* v___x_3374_; 
v___x_3372_ = ((size_t)0ULL);
v___x_3373_ = lean_usize_of_nat(v___y_3364_);
lean_dec(v___y_3364_);
v___x_3374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3366_, v___x_3372_, v___x_3373_, v___y_3369_);
lean_dec_ref(v___y_3366_);
v___y_3341_ = v___y_3363_;
v___y_3342_ = v___y_3365_;
v___y_3343_ = v___y_3367_;
v___y_3344_ = v___y_3368_;
v___y_3345_ = v___x_3374_;
goto v___jp_3340_;
}
}
else
{
size_t v___x_3375_; size_t v___x_3376_; lean_object* v___x_3377_; 
v___x_3375_ = ((size_t)0ULL);
v___x_3376_ = lean_usize_of_nat(v___y_3364_);
lean_dec(v___y_3364_);
v___x_3377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3366_, v___x_3375_, v___x_3376_, v___y_3369_);
lean_dec_ref(v___y_3366_);
v___y_3341_ = v___y_3363_;
v___y_3342_ = v___y_3365_;
v___y_3343_ = v___y_3367_;
v___y_3344_ = v___y_3368_;
v___y_3345_ = v___x_3377_;
goto v___jp_3340_;
}
}
}
v___jp_3378_:
{
lean_object* v___x_3385_; uint8_t v___x_3386_; 
v___x_3385_ = lean_array_get_size(v___y_3384_);
v___x_3386_ = lean_nat_dec_lt(v___x_2940_, v___x_3385_);
if (v___x_3386_ == 0)
{
v___y_3363_ = v___y_3379_;
v___y_3364_ = v___x_3385_;
v___y_3365_ = v___y_3381_;
v___y_3366_ = v___y_3384_;
v___y_3367_ = v___y_3382_;
v___y_3368_ = v___y_3380_;
v___y_3369_ = v___y_3383_;
goto v___jp_3362_;
}
else
{
uint8_t v___x_3387_; 
v___x_3387_ = lean_nat_dec_le(v___x_3385_, v___x_3385_);
if (v___x_3387_ == 0)
{
if (v___x_3386_ == 0)
{
v___y_3363_ = v___y_3379_;
v___y_3364_ = v___x_3385_;
v___y_3365_ = v___y_3381_;
v___y_3366_ = v___y_3384_;
v___y_3367_ = v___y_3382_;
v___y_3368_ = v___y_3380_;
v___y_3369_ = v___y_3383_;
goto v___jp_3362_;
}
else
{
size_t v___x_3388_; size_t v___x_3389_; lean_object* v___x_3390_; 
v___x_3388_ = ((size_t)0ULL);
v___x_3389_ = lean_usize_of_nat(v___x_3385_);
v___x_3390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3384_, v___x_3388_, v___x_3389_, v___y_3383_);
v___y_3363_ = v___y_3379_;
v___y_3364_ = v___x_3385_;
v___y_3365_ = v___y_3381_;
v___y_3366_ = v___y_3384_;
v___y_3367_ = v___y_3382_;
v___y_3368_ = v___y_3380_;
v___y_3369_ = v___x_3390_;
goto v___jp_3362_;
}
}
else
{
size_t v___x_3391_; size_t v___x_3392_; lean_object* v___x_3393_; 
v___x_3391_ = ((size_t)0ULL);
v___x_3392_ = lean_usize_of_nat(v___x_3385_);
v___x_3393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3384_, v___x_3391_, v___x_3392_, v___y_3383_);
v___y_3363_ = v___y_3379_;
v___y_3364_ = v___x_3385_;
v___y_3365_ = v___y_3381_;
v___y_3366_ = v___y_3384_;
v___y_3367_ = v___y_3382_;
v___y_3368_ = v___y_3380_;
v___y_3369_ = v___x_3393_;
goto v___jp_3362_;
}
}
}
v___jp_3397_:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___f_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3399_ = l_Lean_instInhabitedImportState_default;
v___x_3400_ = lean_box(v___x_3396_);
v___x_3401_ = lean_box(v___y_3398_);
v___x_3402_ = lean_box(v___x_2937_);
v___x_3403_ = lean_box(v___x_2912_);
lean_inc_ref(v___x_2941_);
lean_inc(v_name_2910_);
v___f_3404_ = lean_alloc_closure((void*)(l_main___lam__0___boxed), 10, 9);
lean_closure_set(v___f_3404_, 0, v___x_3399_);
lean_closure_set(v___f_3404_, 1, v___x_3395_);
lean_closure_set(v___f_3404_, 2, v___x_3400_);
lean_closure_set(v___f_3404_, 3, v___x_2934_);
lean_closure_set(v___f_3404_, 4, v___x_3401_);
lean_closure_set(v___f_3404_, 5, v_name_2910_);
lean_closure_set(v___f_3404_, 6, v___x_2941_);
lean_closure_set(v___f_3404_, 7, v___x_3402_);
lean_closure_set(v___f_3404_, 8, v___x_3403_);
v___x_3405_ = lean_alloc_closure((void*)(l_Lean_withImporting___boxed), 3, 2);
lean_closure_set(v___x_3405_, 0, lean_box(0));
lean_closure_set(v___x_3405_, 1, v___f_3404_);
v___x_3406_ = lean_box(0);
v___x_3407_ = l_Lean_profileitIOUnsafe___redArg(v___x_3231_, v___x_2941_, v___x_3405_, v___x_3406_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; lean_object* v___x_3409_; lean_object* v_ext_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3408_);
lean_dec_ref(v___x_3407_);
v___x_3409_ = l_Lean_Compiler_CSimp_ext;
v_ext_3410_ = lean_ctor_get(v___x_3409_, 1);
lean_inc(v_name_2910_);
v___x_3411_ = l_Lean_Environment_setMainModule(v_a_3408_, v_name_2910_);
lean_inc_ref(v_ext_3410_);
v___x_3412_ = l_main___elam__0___redArg(v___x_3406_, v___x_2928_, v_ext_3410_, v___x_3411_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_object* v_a_3413_; lean_object* v___x_3414_; lean_object* v_ext_3415_; lean_object* v___x_3416_; 
v_a_3413_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_a_3413_);
lean_dec_ref(v___x_3412_);
v___x_3414_ = l_Lean_Meta_instanceExtension;
v_ext_3415_ = lean_ctor_get(v___x_3414_, 1);
lean_inc_ref(v_ext_3415_);
v___x_3416_ = l_main___elam__0___redArg(v___x_3406_, v___x_2928_, v_ext_3415_, v_a_3413_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_a_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
lean_inc(v_a_3417_);
lean_dec_ref(v___x_3416_);
v___x_3418_ = l_Lean_classExtension;
v___x_3419_ = l_main___elam__0___redArg(v___x_3406_, v___x_2929_, v___x_3418_, v_a_3417_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v_a_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v_a_3420_ = lean_ctor_get(v___x_3419_, 0);
lean_inc(v_a_3420_);
lean_dec_ref(v___x_3419_);
v___x_3421_ = l_Lean_Meta_Match_Extension_extension;
v___x_3422_ = l_main___elam__0___redArg(v___x_3406_, v___x_2930_, v___x_3421_, v_a_3420_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3451_; 
v_a_3423_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3425_ = v___x_3422_;
v_isShared_3426_ = v_isSharedCheck_3451_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3422_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3451_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3427_; 
v___x_3427_ = l_Lean_Environment_getModuleIdx_x3f(v_a_3423_, v_name_2910_);
if (lean_obj_tag(v___x_3427_) == 1)
{
lean_object* v_val_3428_; lean_object* v___x_3429_; uint8_t v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; uint8_t v___x_3434_; 
lean_del_object(v___x_3425_);
v_val_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_val_3428_);
lean_dec_ref(v___x_3427_);
v___x_3429_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_3430_ = 0;
v___x_3431_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2931_, v___x_3429_, v_a_3423_, v_val_3428_, v___x_3430_);
v___x_3432_ = lean_array_get_size(v___x_3431_);
v___x_3433_ = ((lean_object*)(l_main___closed__33));
v___x_3434_ = lean_nat_dec_lt(v___x_2940_, v___x_3432_);
if (v___x_3434_ == 0)
{
lean_dec_ref(v___x_3431_);
v___y_3379_ = v___x_3406_;
v___y_3380_ = v_val_3428_;
v___y_3381_ = v___x_3430_;
v___y_3382_ = v___x_3406_;
v___y_3383_ = v_a_3423_;
v___y_3384_ = v___x_3433_;
goto v___jp_3378_;
}
else
{
uint8_t v___x_3435_; 
v___x_3435_ = lean_nat_dec_le(v___x_3432_, v___x_3432_);
if (v___x_3435_ == 0)
{
if (v___x_3434_ == 0)
{
lean_dec_ref(v___x_3431_);
v___y_3379_ = v___x_3406_;
v___y_3380_ = v_val_3428_;
v___y_3381_ = v___x_3430_;
v___y_3382_ = v___x_3406_;
v___y_3383_ = v_a_3423_;
v___y_3384_ = v___x_3433_;
goto v___jp_3378_;
}
else
{
size_t v___x_3436_; size_t v___x_3437_; lean_object* v___x_3438_; 
v___x_3436_ = ((size_t)0ULL);
v___x_3437_ = lean_usize_of_nat(v___x_3432_);
lean_inc(v_a_3423_);
v___x_3438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3423_, v___x_3431_, v___x_3436_, v___x_3437_, v___x_3433_);
lean_dec_ref(v___x_3431_);
v___y_3379_ = v___x_3406_;
v___y_3380_ = v_val_3428_;
v___y_3381_ = v___x_3430_;
v___y_3382_ = v___x_3406_;
v___y_3383_ = v_a_3423_;
v___y_3384_ = v___x_3438_;
goto v___jp_3378_;
}
}
else
{
size_t v___x_3439_; size_t v___x_3440_; lean_object* v___x_3441_; 
v___x_3439_ = ((size_t)0ULL);
v___x_3440_ = lean_usize_of_nat(v___x_3432_);
lean_inc(v_a_3423_);
v___x_3441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3423_, v___x_3431_, v___x_3439_, v___x_3440_, v___x_3433_);
lean_dec_ref(v___x_3431_);
v___y_3379_ = v___x_3406_;
v___y_3380_ = v_val_3428_;
v___y_3381_ = v___x_3430_;
v___y_3382_ = v___x_3406_;
v___y_3383_ = v_a_3423_;
v___y_3384_ = v___x_3441_;
goto v___jp_3378_;
}
}
}
else
{
lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3449_; 
lean_dec(v___x_3427_);
lean_dec(v_a_3423_);
lean_dec_ref(v___x_2941_);
lean_del_object(v___x_2926_);
lean_dec(v_fst_2923_);
lean_dec(v_head_2903_);
lean_dec(v_head_2902_);
v___x_3442_ = ((lean_object*)(l_main___closed__34));
v___x_3443_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2910_, v___x_2937_);
v___x_3444_ = lean_string_append(v___x_3442_, v___x_3443_);
lean_dec_ref(v___x_3443_);
v___x_3445_ = ((lean_object*)(l_main___closed__35));
v___x_3446_ = lean_string_append(v___x_3444_, v___x_3445_);
v___x_3447_ = lean_mk_io_user_error(v___x_3446_);
if (v_isShared_3426_ == 0)
{
lean_ctor_set_tag(v___x_3425_, 1);
lean_ctor_set(v___x_3425_, 0, v___x_3447_);
v___x_3449_ = v___x_3425_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v___x_3447_);
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
lean_dec_ref(v___x_2941_);
lean_del_object(v___x_2926_);
lean_dec(v_fst_2923_);
lean_dec(v_name_2910_);
lean_dec(v_head_2903_);
lean_dec(v_head_2902_);
v_a_3452_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3454_ = v___x_3422_;
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_a_3452_);
lean_dec(v___x_3422_);
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
lean_dec_ref(v___x_2941_);
lean_del_object(v___x_2926_);
lean_dec(v_fst_2923_);
lean_dec(v_name_2910_);
lean_dec(v_head_2903_);
lean_dec(v_head_2902_);
v_a_3460_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3462_ = v___x_3419_;
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_a_3460_);
lean_dec(v___x_3419_);
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
else
{
lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3475_; 
lean_dec_ref(v___x_2941_);
lean_del_object(v___x_2926_);
lean_dec(v_fst_2923_);
lean_dec(v_name_2910_);
lean_dec(v_head_2903_);
lean_dec(v_head_2902_);
v_a_3468_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3470_ = v___x_3416_;
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_a_3468_);
lean_dec(v___x_3416_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3473_; 
if (v_isShared_3471_ == 0)
{
v___x_3473_ = v___x_3470_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_a_3468_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
else
{
lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3483_; 
lean_dec_ref(v___x_2941_);
lean_del_object(v___x_2926_);
lean_dec(v_fst_2923_);
lean_dec(v_name_2910_);
lean_dec(v_head_2903_);
lean_dec(v_head_2902_);
v_a_3476_ = lean_ctor_get(v___x_3412_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3478_ = v___x_3412_;
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v___x_3412_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3481_; 
if (v_isShared_3479_ == 0)
{
v___x_3481_ = v___x_3478_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_a_3476_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
}
else
{
lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3491_; 
lean_dec_ref(v___x_2941_);
lean_del_object(v___x_2926_);
lean_dec(v_fst_2923_);
lean_dec(v_name_2910_);
lean_dec(v_head_2903_);
lean_dec(v_head_2902_);
v_a_3484_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3486_ = v___x_3407_;
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_dec(v___x_3407_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3489_; 
if (v_isShared_3487_ == 0)
{
v___x_3489_ = v___x_3486_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_a_3484_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
}
}
}
}
else
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3501_; 
lean_dec(v_a_2918_);
lean_dec(v_name_2910_);
lean_dec(v_head_2903_);
lean_dec(v_head_2902_);
v_a_3494_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3496_ = v___x_2922_;
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_2922_);
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
lean_dec(v_a_2918_);
lean_dec(v_name_2910_);
lean_dec(v_head_2903_);
lean_dec(v_head_2902_);
v_a_3502_ = lean_ctor_get(v___x_2919_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3504_ = v___x_2919_;
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_2919_);
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
lean_dec(v_name_2910_);
lean_dec(v_head_2903_);
lean_dec(v_head_2902_);
v_a_3510_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_2917_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_2917_);
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
}
else
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3526_; 
lean_del_object(v___x_2906_);
lean_dec(v_tail_2904_);
lean_dec(v_head_2903_);
lean_dec(v_head_2902_);
v_a_3519_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3521_ = v___x_2908_;
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_2908_);
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
lean_dec_ref(v_tail_2899_);
lean_dec(v_tail_2900_);
lean_dec_ref(v_args_2874_);
goto v___jp_2876_;
}
}
else
{
lean_dec(v_tail_2899_);
lean_dec_ref(v_args_2874_);
goto v___jp_2876_;
}
}
else
{
lean_dec(v_args_2874_);
goto v___jp_2876_;
}
v___jp_2876_:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2877_ = ((lean_object*)(l_main___closed__0));
v___x_2878_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_2877_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2886_; 
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2886_ == 0)
{
lean_object* v_unused_2887_; 
v_unused_2887_ = lean_ctor_get(v___x_2878_, 0);
lean_dec(v_unused_2887_);
v___x_2880_ = v___x_2878_;
v_isShared_2881_ = v_isSharedCheck_2886_;
goto v_resetjp_2879_;
}
else
{
lean_dec(v___x_2878_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2886_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2882_; lean_object* v___x_2884_; 
v___x_2882_ = l_main___boxed__const__1;
if (v_isShared_2881_ == 0)
{
lean_ctor_set(v___x_2880_, 0, v___x_2882_);
v___x_2884_ = v___x_2880_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v___x_2882_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
v_a_2888_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2878_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2878_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
v___jp_2896_:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2897_ = l_main___boxed__const__2;
v___x_2898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2897_);
return v___x_2898_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_3528_, lean_object* v_a_3529_){
_start:
{
lean_object* v_res_3530_; 
v_res_3530_ = _lean_main(v_args_3528_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object* v_as_3531_, lean_object* v_as_x27_3532_, lean_object* v_b_3533_, lean_object* v_a_3534_){
_start:
{
lean_object* v___x_3536_; 
v___x_3536_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_3532_, v_b_3533_);
return v___x_3536_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object* v_as_3537_, lean_object* v_as_x27_3538_, lean_object* v_b_3539_, lean_object* v_a_3540_, lean_object* v___y_3541_){
_start:
{
lean_object* v_res_3542_; 
v_res_3542_ = l_List_forIn_x27_loop___at___00main_spec__1(v_as_3537_, v_as_x27_3538_, v_b_3539_, v_a_3540_);
lean_dec(v_as_x27_3538_);
lean_dec(v_as_3537_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
lean_object* v___x_3546_; 
v___x_3546_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_3544_);
return v___x_3546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___boxed(lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
lean_object* v_res_3550_; 
v_res_3550_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(v___y_3547_, v___y_3548_);
lean_dec(v___y_3548_);
lean_dec_ref(v___y_3547_);
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(lean_object* v_00_u03b2_3551_, lean_object* v_m_3552_, lean_object* v_a_3553_, lean_object* v_fallback_3554_){
_start:
{
lean_object* v___x_3555_; 
v___x_3555_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_3552_, v_a_3553_, v_fallback_3554_);
return v___x_3555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___boxed(lean_object* v_00_u03b2_3556_, lean_object* v_m_3557_, lean_object* v_a_3558_, lean_object* v_fallback_3559_){
_start:
{
lean_object* v_res_3560_; 
v_res_3560_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(v_00_u03b2_3556_, v_m_3557_, v_a_3558_, v_fallback_3559_);
lean_dec(v_fallback_3559_);
lean_dec_ref(v_a_3558_);
lean_dec_ref(v_m_3557_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18(lean_object* v_00_u03b2_3561_, lean_object* v_m_3562_, lean_object* v_a_3563_, lean_object* v_b_3564_){
_start:
{
lean_object* v___x_3565_; 
v___x_3565_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_m_3562_, v_a_3563_, v_b_3564_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(lean_object* v_n_3566_, lean_object* v_as_3567_, lean_object* v_lo_3568_, lean_object* v_hi_3569_, lean_object* v_w_3570_, lean_object* v_hlo_3571_, lean_object* v_hhi_3572_){
_start:
{
lean_object* v___x_3573_; 
v___x_3573_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_3566_, v_as_3567_, v_lo_3568_, v_hi_3569_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___boxed(lean_object* v_n_3574_, lean_object* v_as_3575_, lean_object* v_lo_3576_, lean_object* v_hi_3577_, lean_object* v_w_3578_, lean_object* v_hlo_3579_, lean_object* v_hhi_3580_){
_start:
{
lean_object* v_res_3581_; 
v_res_3581_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(v_n_3574_, v_as_3575_, v_lo_3576_, v_hi_3577_, v_w_3578_, v_hlo_3579_, v_hhi_3580_);
lean_dec(v_hi_3577_);
lean_dec(v_n_3574_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(lean_object* v_00_u03b2_3582_, lean_object* v_a_3583_, lean_object* v_fallback_3584_, lean_object* v_x_3585_){
_start:
{
lean_object* v___x_3586_; 
v___x_3586_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_3583_, v_fallback_3584_, v_x_3585_);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3587_, lean_object* v_a_3588_, lean_object* v_fallback_3589_, lean_object* v_x_3590_){
_start:
{
lean_object* v_res_3591_; 
v_res_3591_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(v_00_u03b2_3587_, v_a_3588_, v_fallback_3589_, v_x_3590_);
lean_dec(v_x_3590_);
lean_dec(v_fallback_3589_);
lean_dec_ref(v_a_3588_);
return v_res_3591_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(lean_object* v_00_u03b2_3592_, lean_object* v_a_3593_, lean_object* v_x_3594_){
_start:
{
uint8_t v___x_3595_; 
v___x_3595_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_3593_, v_x_3594_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___boxed(lean_object* v_00_u03b2_3596_, lean_object* v_a_3597_, lean_object* v_x_3598_){
_start:
{
uint8_t v_res_3599_; lean_object* v_r_3600_; 
v_res_3599_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(v_00_u03b2_3596_, v_a_3597_, v_x_3598_);
lean_dec(v_x_3598_);
lean_dec_ref(v_a_3597_);
v_r_3600_ = lean_box(v_res_3599_);
return v_r_3600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24(lean_object* v_00_u03b2_3601_, lean_object* v_data_3602_){
_start:
{
lean_object* v___x_3603_; 
v___x_3603_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_data_3602_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25(lean_object* v_00_u03b2_3604_, lean_object* v_a_3605_, lean_object* v_b_3606_, lean_object* v_x_3607_){
_start:
{
lean_object* v___x_3608_; 
v___x_3608_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_3605_, v_b_3606_, v_x_3607_);
return v___x_3608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(lean_object* v_n_3609_, lean_object* v_lo_3610_, lean_object* v_hi_3611_, lean_object* v_hhi_3612_, lean_object* v_pivot_3613_, lean_object* v_as_3614_, lean_object* v_i_3615_, lean_object* v_k_3616_, lean_object* v_ilo_3617_, lean_object* v_ik_3618_, lean_object* v_w_3619_){
_start:
{
lean_object* v___x_3620_; 
v___x_3620_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_3611_, v_pivot_3613_, v_as_3614_, v_i_3615_, v_k_3616_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___boxed(lean_object* v_n_3621_, lean_object* v_lo_3622_, lean_object* v_hi_3623_, lean_object* v_hhi_3624_, lean_object* v_pivot_3625_, lean_object* v_as_3626_, lean_object* v_i_3627_, lean_object* v_k_3628_, lean_object* v_ilo_3629_, lean_object* v_ik_3630_, lean_object* v_w_3631_){
_start:
{
lean_object* v_res_3632_; 
v_res_3632_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(v_n_3621_, v_lo_3622_, v_hi_3623_, v_hhi_3624_, v_pivot_3625_, v_as_3626_, v_i_3627_, v_k_3628_, v_ilo_3629_, v_ik_3630_, v_w_3631_);
lean_dec_ref(v_pivot_3625_);
lean_dec(v_hi_3623_);
lean_dec(v_lo_3622_);
lean_dec(v_n_3621_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(lean_object* v_as_3633_, size_t v_sz_3634_, size_t v_i_3635_, lean_object* v_b_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_){
_start:
{
lean_object* v___x_3640_; 
v___x_3640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_3633_, v_sz_3634_, v_i_3635_, v_b_3636_, v___y_3637_);
return v___x_3640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___boxed(lean_object* v_as_3641_, lean_object* v_sz_3642_, lean_object* v_i_3643_, lean_object* v_b_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
size_t v_sz_boxed_3648_; size_t v_i_boxed_3649_; lean_object* v_res_3650_; 
v_sz_boxed_3648_ = lean_unbox_usize(v_sz_3642_);
lean_dec(v_sz_3642_);
v_i_boxed_3649_ = lean_unbox_usize(v_i_3643_);
lean_dec(v_i_3643_);
v_res_3650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(v_as_3641_, v_sz_boxed_3648_, v_i_boxed_3649_, v_b_3644_, v___y_3645_, v___y_3646_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec_ref(v_as_3641_);
return v_res_3650_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35(lean_object* v_00_u03b2_3651_, lean_object* v_i_3652_, lean_object* v_source_3653_, lean_object* v_target_3654_){
_start:
{
lean_object* v___x_3655_; 
v___x_3655_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v_i_3652_, v_source_3653_, v_target_3654_);
return v___x_3655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(uint8_t v___x_3656_, lean_object* v_as_3657_, size_t v_sz_3658_, size_t v_i_3659_, lean_object* v_b_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
lean_object* v___x_3664_; 
v___x_3664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_3656_, v_as_3657_, v_sz_3658_, v_i_3659_, v_b_3660_, v___y_3661_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___boxed(lean_object* v___x_3665_, lean_object* v_as_3666_, lean_object* v_sz_3667_, lean_object* v_i_3668_, lean_object* v_b_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
uint8_t v___x_41280__boxed_3673_; size_t v_sz_boxed_3674_; size_t v_i_boxed_3675_; lean_object* v_res_3676_; 
v___x_41280__boxed_3673_ = lean_unbox(v___x_3665_);
v_sz_boxed_3674_ = lean_unbox_usize(v_sz_3667_);
lean_dec(v_sz_3667_);
v_i_boxed_3675_ = lean_unbox_usize(v_i_3668_);
lean_dec(v_i_3668_);
v_res_3676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(v___x_41280__boxed_3673_, v_as_3666_, v_sz_boxed_3674_, v_i_boxed_3675_, v_b_3669_, v___y_3670_, v___y_3671_);
lean_dec(v___y_3671_);
lean_dec_ref(v___y_3670_);
lean_dec_ref(v_as_3666_);
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(lean_object* v_as_3677_, size_t v_sz_3678_, size_t v_i_3679_, lean_object* v_b_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_){
_start:
{
lean_object* v___x_3684_; 
v___x_3684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_3677_, v_sz_3678_, v_i_3679_, v_b_3680_, v___y_3681_);
return v___x_3684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___boxed(lean_object* v_as_3685_, lean_object* v_sz_3686_, lean_object* v_i_3687_, lean_object* v_b_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_){
_start:
{
size_t v_sz_boxed_3692_; size_t v_i_boxed_3693_; lean_object* v_res_3694_; 
v_sz_boxed_3692_ = lean_unbox_usize(v_sz_3686_);
lean_dec(v_sz_3686_);
v_i_boxed_3693_ = lean_unbox_usize(v_i_3687_);
lean_dec(v_i_3687_);
v_res_3694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(v_as_3685_, v_sz_boxed_3692_, v_i_boxed_3693_, v_b_3688_, v___y_3689_, v___y_3690_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
lean_dec_ref(v_as_3685_);
return v_res_3694_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44(lean_object* v_00_u03b2_3695_, lean_object* v_x_3696_, lean_object* v_x_3697_){
_start:
{
lean_object* v___x_3698_; 
v___x_3698_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_x_3696_, v_x_3697_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(uint8_t v___x_3699_, lean_object* v_as_3700_, size_t v_sz_3701_, size_t v_i_3702_, lean_object* v_b_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_){
_start:
{
lean_object* v___x_3707_; 
v___x_3707_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_3699_, v_as_3700_, v_sz_3701_, v_i_3702_, v_b_3703_, v___y_3704_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___boxed(lean_object* v___x_3708_, lean_object* v_as_3709_, lean_object* v_sz_3710_, lean_object* v_i_3711_, lean_object* v_b_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_){
_start:
{
uint8_t v___x_41311__boxed_3716_; size_t v_sz_boxed_3717_; size_t v_i_boxed_3718_; lean_object* v_res_3719_; 
v___x_41311__boxed_3716_ = lean_unbox(v___x_3708_);
v_sz_boxed_3717_ = lean_unbox_usize(v_sz_3710_);
lean_dec(v_sz_3710_);
v_i_boxed_3718_ = lean_unbox_usize(v_i_3711_);
lean_dec(v_i_3711_);
v_res_3719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(v___x_41311__boxed_3716_, v_as_3709_, v_sz_boxed_3717_, v_i_boxed_3718_, v_b_3712_, v___y_3713_, v___y_3714_);
lean_dec(v___y_3714_);
lean_dec_ref(v___y_3713_);
lean_dec_ref(v_as_3709_);
return v_res_3719_;
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
