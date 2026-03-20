// Lean compiler output
// Module: LeanIR
// Imports: public import Init import Lean.CoreM import Lean.Util.ForEachExpr import all Lean.Util.Path import all Lean.Environment import Lean.Compiler.Options import Lean.Compiler.IR.CompilerM import all Lean.Compiler.CSimpAttr import Lean.Compiler.LCNF.EmitC import Lean.Language.Lean import Lean.Compiler.LCNF.PhaseExt import Lean.Compiler.LCNF.Main
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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_instDecidableEqOLeanLevel(uint8_t, uint8_t);
lean_object* l_Lean_finalizeImport(lean_object*, lean_object*, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Message_toString(lean_object*, uint8_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stderr();
size_t lean_usize_add(size_t, size_t);
double lean_float_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedClassState_default;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint64_t l_String_instHashableRaw_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_ir_export_entries(lean_object*);
lean_object* l_Lean_mkModuleData(lean_object*, uint8_t);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_get_ir_extra_const_names(lean_object*, uint8_t, uint8_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Match_Extension_instInhabitedState;
lean_object* l_IO_println___at___00Lean_Environment_displayStats_spec__1(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedError;
lean_object* l_instInhabitedEST___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_ModuleSetup_load(lean_object*);
lean_object* l_Lean_LeanOptions_toOptions(lean_object*);
lean_object* l_Lean_getBuildDir();
lean_object* l_Lean_initSearchPath(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
extern lean_object* l_Lean_Compiler_compiler_inLeanIR;
lean_object* l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_maxHeartbeats;
extern lean_object* l_Lean_trace_profiler_output;
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_saveModuleData(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* lean_io_get_num_heartbeats();
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
lean_object* l_Lean_Compiler_LCNF_resumeCompilation(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_SimplePersistentEnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
extern lean_object* l_Lean_inheritedTraceOptions;
extern lean_object* l_Lean_instInhabitedFileMap_default;
extern lean_object* l_Lean_diagnostics;
extern lean_object* l_Lean_IR_declMapExt;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_name(lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_panic___at___00main_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00main_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00main_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00main_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00main_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_main___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_main___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_main___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l_main___lam__1___closed__0 = (const lean_object*)&l_main___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_main___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_main___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__9_spec__20(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__9_spec__20___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__9(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__9___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__30_spec__43___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__30_spec__43___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__30_spec__43___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__30_spec__43(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__30_spec__43___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__30(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__29(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__23_spec__32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__23_spec__32___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__23_spec__32___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__23_spec__32(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__23_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__23(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__10___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__4_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__4_spec__4___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__4_spec__4___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__4_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__4_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__4_spec__4___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__4_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__4_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00main_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__17___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__18(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16_spec__28_spec__37___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16_spec__28___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__32(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20_spec__35___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20_spec__35___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___closed__0;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__10___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTraceAsMessages___at___00main_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___at___00main_spec__8___closed__0;
static lean_once_cell_t l_Lean_addTraceAsMessages___at___00main_spec__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___at___00main_spec__8___closed__1;
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_boxed"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27_spec__37___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27_spec__37___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27_spec__37(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27_spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "usage: leanir <setup.json> <module> <output.ir> <output.c> <-Dopt=val>..."};
static const lean_object* l_main___closed__0 = (const lean_object*)&l_main___closed__0_value;
static const lean_string_object l_main___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "LeanIR"};
static const lean_object* l_main___closed__1 = (const lean_object*)&l_main___closed__1_value;
static const lean_string_object l_main___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "main"};
static const lean_object* l_main___closed__2 = (const lean_object*)&l_main___closed__2_value;
static const lean_string_object l_main___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_main___closed__3 = (const lean_object*)&l_main___closed__3_value;
static lean_once_cell_t l_main___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__4;
static const lean_closure_object l_main___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_main___closed__5 = (const lean_object*)&l_main___closed__5_value;
static const lean_closure_object l_main___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_main___closed__6 = (const lean_object*)&l_main___closed__6_value;
static lean_once_cell_t l_main___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__7;
static lean_once_cell_t l_main___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__8;
static lean_once_cell_t l_main___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__9;
static lean_once_cell_t l_main___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__10;
static lean_once_cell_t l_main___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__11;
static lean_once_cell_t l_main___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__12;
static lean_once_cell_t l_main___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__13;
static const lean_ctor_object l_main___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_main___closed__14 = (const lean_object*)&l_main___closed__14_value;
static const lean_string_object l_main___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ir"};
static const lean_object* l_main___closed__15 = (const lean_object*)&l_main___closed__15_value;
static const lean_ctor_object l_main___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__15_value),LEAN_SCALAR_PTR_LITERAL(157, 0, 67, 166, 172, 92, 38, 85)}};
static const lean_object* l_main___closed__16 = (const lean_object*)&l_main___closed__16_value;
static const lean_string_object l_main___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "C code generation"};
static const lean_object* l_main___closed__17 = (const lean_object*)&l_main___closed__17_value;
static lean_once_cell_t l_main___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__18;
static const lean_string_object l_main___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "failed to create '"};
static const lean_object* l_main___closed__19 = (const lean_object*)&l_main___closed__19_value;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16_spec__28(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20_spec__35(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20_spec__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16_spec__28_spec__37(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_irEntries_79_; uint8_t v___x_80_; lean_object* v___x_81_; lean_object* v_a_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_112_; 
lean_inc_ref(v_env_77_);
v_irEntries_79_ = lean_ir_export_entries(v_env_77_);
v___x_80_ = 2;
lean_inc_ref(v_env_77_);
v___x_81_ = l_Lean_mkModuleData(v_env_77_, v___x_80_);
v_a_82_ = lean_ctor_get(v___x_81_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_112_ == 0)
{
v___x_84_ = v___x_81_;
v_isShared_85_ = v_isSharedCheck_112_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_a_82_);
lean_dec(v___x_81_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_112_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___y_87_; lean_object* v_entries_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v_entries_99_ = lean_ctor_get(v_a_82_, 4);
lean_inc_ref(v_entries_99_);
lean_dec(v_a_82_);
v___x_100_ = lean_unsigned_to_nat(0u);
v___x_101_ = lean_array_get_size(v_entries_99_);
v___x_102_ = ((lean_object*)(l___private_LeanIR_0__mkIRData___closed__1));
v___x_103_ = lean_nat_dec_lt(v___x_100_, v___x_101_);
if (v___x_103_ == 0)
{
lean_dec_ref(v_entries_99_);
v___y_87_ = v___x_102_;
goto v___jp_86_;
}
else
{
size_t v_sz_104_; size_t v___x_105_; lean_object* v_irExtNames_106_; uint8_t v___x_107_; 
v_sz_104_ = lean_array_size(v_irEntries_79_);
v___x_105_ = ((size_t)0ULL);
lean_inc_ref(v_irEntries_79_);
v_irExtNames_106_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0(v_sz_104_, v___x_105_, v_irEntries_79_);
v___x_107_ = lean_nat_dec_le(v___x_101_, v___x_101_);
if (v___x_107_ == 0)
{
if (v___x_103_ == 0)
{
lean_dec_ref(v_irExtNames_106_);
lean_dec_ref(v_entries_99_);
v___y_87_ = v___x_102_;
goto v___jp_86_;
}
else
{
size_t v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_usize_of_nat(v___x_101_);
v___x_109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(v_irExtNames_106_, v_entries_99_, v___x_105_, v___x_108_, v___x_102_);
lean_dec_ref(v_entries_99_);
lean_dec_ref(v_irExtNames_106_);
v___y_87_ = v___x_109_;
goto v___jp_86_;
}
}
else
{
size_t v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_usize_of_nat(v___x_101_);
v___x_111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(v_irExtNames_106_, v_entries_99_, v___x_105_, v___x_110_, v___x_102_);
lean_dec_ref(v_entries_99_);
lean_dec_ref(v_irExtNames_106_);
v___y_87_ = v___x_111_;
goto v___jp_86_;
}
}
v___jp_86_:
{
lean_object* v___x_88_; uint8_t v_isModule_89_; lean_object* v_imports_90_; lean_object* v___x_91_; uint8_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_97_; 
v___x_88_ = l_Lean_Environment_header(v_env_77_);
v_isModule_89_ = lean_ctor_get_uint8(v___x_88_, sizeof(void*)*7 + 4);
v_imports_90_ = lean_ctor_get(v___x_88_, 1);
lean_inc_ref(v_imports_90_);
lean_dec_ref(v___x_88_);
v___x_91_ = ((lean_object*)(l___private_LeanIR_0__mkIRData___closed__0));
v___x_92_ = 1;
v___x_93_ = lean_get_ir_extra_const_names(v_env_77_, v___x_80_, v___x_92_);
v___x_94_ = l_Array_append___redArg(v_irEntries_79_, v___y_87_);
lean_dec_ref(v___y_87_);
v___x_95_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_95_, 0, v_imports_90_);
lean_ctor_set(v___x_95_, 1, v___x_91_);
lean_ctor_set(v___x_95_, 2, v___x_91_);
lean_ctor_set(v___x_95_, 3, v___x_93_);
lean_ctor_set(v___x_95_, 4, v___x_94_);
lean_ctor_set_uint8(v___x_95_, sizeof(void*)*5, v_isModule_89_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 0, v___x_95_);
v___x_97_ = v___x_84_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v___x_95_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__mkIRData___boxed(lean_object* v_env_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l___private_LeanIR_0__mkIRData(v_env_113_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(lean_object* v_arg_116_, lean_object* v___x_117_, lean_object* v_arg_118_, lean_object* v_a_119_, lean_object* v_b_120_){
_start:
{
lean_object* v_startInclusive_121_; lean_object* v_endExclusive_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v_startInclusive_121_ = lean_ctor_get(v_arg_116_, 1);
v_endExclusive_122_ = lean_ctor_get(v_arg_116_, 2);
v___x_123_ = lean_nat_sub(v_endExclusive_122_, v_startInclusive_121_);
v___x_124_ = lean_nat_dec_eq(v_a_119_, v___x_123_);
lean_dec(v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; uint32_t v___x_126_; uint32_t v___x_127_; uint8_t v___x_128_; 
lean_dec(v_b_120_);
v___x_125_ = lean_nat_add(v___x_117_, v_a_119_);
v___x_126_ = lean_string_utf8_get_fast(v_arg_118_, v___x_125_);
v___x_127_ = 61;
v___x_128_ = lean_uint32_dec_eq(v___x_126_, v___x_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
lean_dec(v_a_119_);
v___x_129_ = lean_box(0);
v___x_130_ = lean_string_utf8_next_fast(v_arg_118_, v___x_125_);
lean_dec(v___x_125_);
v___x_131_ = lean_nat_sub(v___x_130_, v___x_117_);
v_a_119_ = v___x_131_;
v_b_120_ = v___x_129_;
goto _start;
}
else
{
lean_object* v___x_133_; 
lean_dec(v___x_125_);
v___x_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_133_, 0, v_a_119_);
return v___x_133_;
}
}
else
{
lean_dec(v_a_119_);
return v_b_120_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___boxed(lean_object* v_arg_134_, lean_object* v___x_135_, lean_object* v_arg_136_, lean_object* v_a_137_, lean_object* v_b_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(v_arg_134_, v___x_135_, v_arg_136_, v_a_137_, v_b_138_);
lean_dec_ref(v_arg_136_);
lean_dec(v___x_135_);
lean_dec_ref(v_arg_134_);
return v_res_139_;
}
}
static lean_object* _init_l___private_LeanIR_0__setConfigOption___closed__3(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__2));
v___x_144_ = lean_string_utf8_byte_size(v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption(lean_object* v_opts_150_, lean_object* v_arg_151_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_160_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__2));
v___x_161_ = lean_string_utf8_byte_size(v_arg_151_);
v___x_162_ = lean_obj_once(&l___private_LeanIR_0__setConfigOption___closed__3, &l___private_LeanIR_0__setConfigOption___closed__3_once, _init_l___private_LeanIR_0__setConfigOption___closed__3);
v___x_163_ = lean_nat_dec_le(v___x_162_, v___x_161_);
if (v___x_163_ == 0)
{
lean_dec_ref(v_opts_150_);
goto v___jp_153_;
}
else
{
lean_object* v_searcher_164_; uint8_t v___x_165_; 
v_searcher_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = lean_string_memcmp(v_arg_151_, v___x_160_, v_searcher_164_, v_searcher_164_, v___x_162_);
if (v___x_165_ == 0)
{
lean_dec_ref(v_opts_150_);
goto v___jp_153_;
}
else
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___y_170_; lean_object* v_arg_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_166_ = lean_unsigned_to_nat(2u);
lean_inc_ref(v_arg_151_);
v___x_167_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_167_, 0, v_arg_151_);
lean_ctor_set(v___x_167_, 1, v_searcher_164_);
lean_ctor_set(v___x_167_, 2, v___x_161_);
v___x_168_ = l_String_Slice_Pos_nextn(v___x_167_, v_searcher_164_, v___x_166_);
lean_dec_ref(v___x_167_);
lean_inc(v___x_168_);
lean_inc_ref(v_arg_151_);
v_arg_208_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_arg_208_, 0, v_arg_151_);
lean_ctor_set(v_arg_208_, 1, v___x_168_);
lean_ctor_set(v_arg_208_, 2, v___x_161_);
v___x_209_ = lean_box(0);
v___x_210_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(v_arg_208_, v___x_168_, v_arg_151_, v_searcher_164_, v___x_209_);
lean_dec_ref(v_arg_208_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v___x_211_; 
v___x_211_ = lean_nat_sub(v___x_161_, v___x_168_);
v___y_170_ = v___x_211_;
goto v___jp_169_;
}
else
{
lean_object* v_val_212_; 
v_val_212_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_val_212_);
lean_dec_ref(v___x_210_);
v___y_170_ = v_val_212_;
goto v___jp_169_;
}
v___jp_169_:
{
lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_171_ = lean_nat_sub(v___x_161_, v___x_168_);
v___x_172_ = lean_nat_dec_eq(v___y_170_, v___x_171_);
lean_dec(v___x_171_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_197_; 
v_a_174_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_197_ == 0)
{
v___x_176_ = v___x_173_;
v_isShared_177_ = v_isSharedCheck_197_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_173_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_197_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v_name_180_; lean_object* v___x_181_; 
v___x_178_ = lean_nat_add(v___x_168_, v___y_170_);
lean_dec(v___y_170_);
lean_inc(v___x_178_);
lean_inc(v___x_168_);
lean_inc_ref(v_arg_151_);
v___x_179_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_179_, 0, v_arg_151_);
lean_ctor_set(v___x_179_, 1, v___x_168_);
lean_ctor_set(v___x_179_, 2, v___x_178_);
v_name_180_ = l_String_Slice_toName(v___x_179_);
lean_dec_ref(v___x_179_);
v___x_181_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_174_, v_name_180_);
lean_dec(v_a_174_);
if (lean_obj_tag(v___x_181_) == 1)
{
lean_object* v_val_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v_val_186_; lean_object* v___x_187_; 
lean_del_object(v___x_176_);
v_val_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_val_182_);
lean_dec_ref(v___x_181_);
v___x_183_ = lean_string_utf8_next_fast(v_arg_151_, v___x_178_);
lean_dec(v___x_178_);
v___x_184_ = lean_nat_sub(v___x_183_, v___x_168_);
v___x_185_ = lean_nat_add(v___x_168_, v___x_184_);
lean_dec(v___x_184_);
lean_dec(v___x_168_);
v_val_186_ = lean_string_utf8_extract(v_arg_151_, v___x_185_, v___x_161_);
lean_dec(v___x_185_);
lean_dec_ref(v_arg_151_);
v___x_187_ = l_Lean_Language_Lean_setOption(v_opts_150_, v_val_182_, v_name_180_, v_val_186_);
return v___x_187_;
}
else
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_195_; 
lean_dec(v___x_181_);
lean_dec(v___x_178_);
lean_dec(v___x_168_);
lean_dec_ref(v_arg_151_);
lean_dec_ref(v_opts_150_);
v___x_188_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__4));
v___x_189_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_180_, v___x_165_);
v___x_190_ = lean_string_append(v___x_188_, v___x_189_);
lean_dec_ref(v___x_189_);
v___x_191_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__5));
v___x_192_ = lean_string_append(v___x_190_, v___x_191_);
v___x_193_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
if (v_isShared_177_ == 0)
{
lean_ctor_set_tag(v___x_176_, 1);
lean_ctor_set(v___x_176_, 0, v___x_193_);
v___x_195_ = v___x_176_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_193_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
else
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
lean_dec(v___y_170_);
lean_dec(v___x_168_);
lean_dec_ref(v_arg_151_);
lean_dec_ref(v_opts_150_);
v_a_198_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_173_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_173_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
else
{
lean_object* v___x_206_; lean_object* v___x_207_; 
lean_dec(v___y_170_);
lean_dec(v___x_168_);
lean_dec_ref(v_arg_151_);
lean_dec_ref(v_opts_150_);
v___x_206_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__7));
v___x_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
return v___x_207_;
}
}
}
}
v___jp_153_:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_154_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__0));
v___x_155_ = lean_string_append(v___x_154_, v_arg_151_);
lean_dec_ref(v_arg_151_);
v___x_156_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__1));
v___x_157_ = lean_string_append(v___x_155_, v___x_156_);
v___x_158_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
v___x_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption___boxed(lean_object* v_opts_213_, lean_object* v_arg_214_, lean_object* v_a_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l___private_LeanIR_0__setConfigOption(v_opts_213_, v_arg_214_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0(lean_object* v_arg_217_, lean_object* v___x_218_, lean_object* v_arg_219_, lean_object* v_inst_220_, lean_object* v_R_221_, lean_object* v_a_222_, lean_object* v_b_223_, lean_object* v_c_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(v_arg_217_, v___x_218_, v_arg_219_, v_a_222_, v_b_223_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___boxed(lean_object* v_arg_226_, lean_object* v___x_227_, lean_object* v_arg_228_, lean_object* v_inst_229_, lean_object* v_R_230_, lean_object* v_a_231_, lean_object* v_b_232_, lean_object* v_c_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0(v_arg_226_, v___x_227_, v_arg_228_, v_inst_229_, v_R_230_, v_a_231_, v_b_232_, v_c_233_);
lean_dec_ref(v_arg_228_);
lean_dec(v___x_227_);
lean_dec_ref(v_arg_226_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg(lean_object* v___x_235_, lean_object* v_inst_236_, lean_object* v_ext_237_, lean_object* v_env_238_){
_start:
{
lean_object* v_toEnvExtension_240_; lean_object* v_addImportedFn_241_; lean_object* v_asyncMode_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v_importedEntries_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_273_; 
v_toEnvExtension_240_ = lean_ctor_get(v_ext_237_, 0);
lean_inc_ref(v_toEnvExtension_240_);
v_addImportedFn_241_ = lean_ctor_get(v_ext_237_, 2);
lean_inc_ref(v_addImportedFn_241_);
lean_dec_ref(v_ext_237_);
v_asyncMode_242_ = lean_ctor_get(v_toEnvExtension_240_, 2);
v___x_243_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v_inst_236_);
lean_inc_ref(v_env_238_);
v___x_244_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_243_, v_toEnvExtension_240_, v_env_238_, v_asyncMode_242_, v___x_235_);
v_importedEntries_245_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_273_ == 0)
{
lean_object* v_unused_274_; 
v_unused_274_ = lean_ctor_get(v___x_244_, 1);
lean_dec(v_unused_274_);
v___x_247_ = v___x_244_;
v_isShared_248_ = v_isSharedCheck_273_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_importedEntries_245_);
lean_dec(v___x_244_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_273_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_249_ = l_Lean_Options_empty;
lean_inc_ref(v_env_238_);
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v_env_238_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
lean_inc_ref(v_importedEntries_245_);
v___x_251_ = lean_apply_3(v_addImportedFn_241_, v_importedEntries_245_, v___x_250_, lean_box(0));
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_264_; 
v_a_252_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_264_ == 0)
{
v___x_254_ = v___x_251_;
v_isShared_255_ = v_isSharedCheck_264_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_251_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_264_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 1, v_a_252_);
v___x_257_ = v___x_247_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_importedEntries_245_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_a_252_);
v___x_257_ = v_reuseFailAlloc_263_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_258_ = lean_box(0);
v___x_259_ = l_Lean_EnvExtension_setState___redArg(v_toEnvExtension_240_, v_env_238_, v___x_257_, v___x_258_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 0, v___x_259_);
v___x_261_ = v___x_254_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
else
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
lean_del_object(v___x_247_);
lean_dec_ref(v_importedEntries_245_);
lean_dec_ref(v_toEnvExtension_240_);
lean_dec_ref(v_env_238_);
v_a_265_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v___x_251_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_251_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg___boxed(lean_object* v___x_275_, lean_object* v_inst_276_, lean_object* v_ext_277_, lean_object* v_env_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_main___elam__0___redArg(v___x_275_, v_inst_276_, v_ext_277_, v_env_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0(lean_object* v___x_281_, lean_object* v_00_u03b1_282_, lean_object* v_00_u03b2_283_, lean_object* v_00_u03c3_284_, lean_object* v_inst_285_, lean_object* v_ext_286_, lean_object* v_env_287_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_main___elam__0___redArg(v___x_281_, v_inst_285_, v_ext_286_, v_env_287_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___boxed(lean_object* v___x_290_, lean_object* v_00_u03b1_291_, lean_object* v_00_u03b2_292_, lean_object* v_00_u03c3_293_, lean_object* v_inst_294_, lean_object* v_ext_295_, lean_object* v_env_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_main___elam__0(v___x_290_, v_00_u03b1_291_, v_00_u03b2_292_, v_00_u03c3_293_, v_inst_294_, v_ext_295_, v_env_296_);
return v_res_298_;
}
}
static lean_object* _init_l_panic___at___00main_spec__1___closed__0(void){
_start:
{
lean_object* v___x_299_; lean_object* v___f_300_; 
v___x_299_ = l_instInhabitedError;
v___f_300_ = lean_alloc_closure((void*)(l_instInhabitedEST___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_300_, 0, v___x_299_);
return v___f_300_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00main_spec__1(lean_object* v_msg_301_){
_start:
{
lean_object* v___f_303_; lean_object* v___x_19912__overap_304_; lean_object* v___x_305_; 
v___f_303_ = lean_obj_once(&l_panic___at___00main_spec__1___closed__0, &l_panic___at___00main_spec__1___closed__0_once, _init_l_panic___at___00main_spec__1___closed__0);
v___x_19912__overap_304_ = lean_panic_fn(v___f_303_, v_msg_301_);
v___x_305_ = lean_apply_1(v___x_19912__overap_304_, lean_box(0));
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00main_spec__1___boxed(lean_object* v_msg_306_, lean_object* v___y_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_panic___at___00main_spec__1(v_msg_306_);
return v_res_308_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00main_spec__6(lean_object* v_opts_309_, lean_object* v_opt_310_){
_start:
{
lean_object* v_name_311_; lean_object* v_defValue_312_; lean_object* v_map_313_; lean_object* v___x_314_; 
v_name_311_ = lean_ctor_get(v_opt_310_, 0);
v_defValue_312_ = lean_ctor_get(v_opt_310_, 1);
v_map_313_ = lean_ctor_get(v_opts_309_, 0);
v___x_314_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_313_, v_name_311_);
if (lean_obj_tag(v___x_314_) == 0)
{
uint8_t v___x_315_; 
v___x_315_ = lean_unbox(v_defValue_312_);
return v___x_315_;
}
else
{
lean_object* v_val_316_; 
v_val_316_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_val_316_);
lean_dec_ref(v___x_314_);
if (lean_obj_tag(v_val_316_) == 1)
{
uint8_t v_v_317_; 
v_v_317_ = lean_ctor_get_uint8(v_val_316_, 0);
lean_dec_ref(v_val_316_);
return v_v_317_;
}
else
{
uint8_t v___x_318_; 
lean_dec(v_val_316_);
v___x_318_ = lean_unbox(v_defValue_312_);
return v___x_318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__6___boxed(lean_object* v_opts_319_, lean_object* v_opt_320_){
_start:
{
uint8_t v_res_321_; lean_object* v_r_322_; 
v_res_321_ = l_Lean_Option_get___at___00main_spec__6(v_opts_319_, v_opt_320_);
lean_dec_ref(v_opt_320_);
lean_dec_ref(v_opts_319_);
v_r_322_ = lean_box(v_res_321_);
return v_r_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__7(lean_object* v_opts_323_, lean_object* v_opt_324_){
_start:
{
lean_object* v_name_325_; lean_object* v_defValue_326_; lean_object* v_map_327_; lean_object* v___x_328_; 
v_name_325_ = lean_ctor_get(v_opt_324_, 0);
v_defValue_326_ = lean_ctor_get(v_opt_324_, 1);
v_map_327_ = lean_ctor_get(v_opts_323_, 0);
v___x_328_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_327_, v_name_325_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_inc(v_defValue_326_);
return v_defValue_326_;
}
else
{
lean_object* v_val_329_; 
v_val_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_val_329_);
lean_dec_ref(v___x_328_);
if (lean_obj_tag(v_val_329_) == 3)
{
lean_object* v_v_330_; 
v_v_330_ = lean_ctor_get(v_val_329_, 0);
lean_inc(v_v_330_);
lean_dec_ref(v_val_329_);
return v_v_330_;
}
else
{
lean_dec(v_val_329_);
lean_inc(v_defValue_326_);
return v_defValue_326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__7___boxed(lean_object* v_opts_331_, lean_object* v_opt_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Option_get___at___00main_spec__7(v_opts_331_, v_opt_332_);
lean_dec_ref(v_opt_332_);
lean_dec_ref(v_opts_331_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5_spec__6(lean_object* v___x_334_, lean_object* v_a_335_, lean_object* v_x_336_){
_start:
{
if (lean_obj_tag(v_x_336_) == 0)
{
lean_dec(v_a_335_);
return v_x_336_;
}
else
{
lean_object* v_key_337_; lean_object* v_value_338_; lean_object* v_tail_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_385_; 
v_key_337_ = lean_ctor_get(v_x_336_, 0);
v_value_338_ = lean_ctor_get(v_x_336_, 1);
v_tail_339_ = lean_ctor_get(v_x_336_, 2);
v_isSharedCheck_385_ = !lean_is_exclusive(v_x_336_);
if (v_isSharedCheck_385_ == 0)
{
v___x_341_ = v_x_336_;
v_isShared_342_ = v_isSharedCheck_385_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_tail_339_);
lean_inc(v_value_338_);
lean_inc(v_key_337_);
lean_dec(v_x_336_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_385_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
uint8_t v___x_343_; 
v___x_343_ = lean_name_eq(v_key_337_, v_a_335_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; lean_object* v___x_346_; 
v___x_344_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5_spec__6(v___x_334_, v_a_335_, v_tail_339_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 2, v___x_344_);
v___x_346_ = v___x_341_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_key_337_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_value_338_);
lean_ctor_set(v_reuseFailAlloc_347_, 2, v___x_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
else
{
lean_object* v_toEffectiveImport_348_; lean_object* v_toImport_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_384_; 
lean_dec(v_key_337_);
v_toEffectiveImport_348_ = lean_ctor_get(v_value_338_, 0);
lean_inc_ref(v_toEffectiveImport_348_);
v_toImport_349_ = lean_ctor_get(v_toEffectiveImport_348_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v_toEffectiveImport_348_);
if (v_isSharedCheck_384_ == 0)
{
v___x_351_ = v_toEffectiveImport_348_;
v_isShared_352_ = v_isSharedCheck_384_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_toImport_349_);
lean_dec(v_toEffectiveImport_348_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_384_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v_parts_353_; lean_object* v_irData_x3f_354_; uint8_t v_needsData_355_; uint8_t v_needsIRTrans_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_382_; 
v_parts_353_ = lean_ctor_get(v_value_338_, 1);
v_irData_x3f_354_ = lean_ctor_get(v_value_338_, 2);
v_needsData_355_ = lean_ctor_get_uint8(v_value_338_, sizeof(void*)*3);
v_needsIRTrans_356_ = lean_ctor_get_uint8(v_value_338_, sizeof(void*)*3 + 1);
v_isSharedCheck_382_ = !lean_is_exclusive(v_value_338_);
if (v_isSharedCheck_382_ == 0)
{
lean_object* v_unused_383_; 
v_unused_383_ = lean_ctor_get(v_value_338_, 0);
lean_dec(v_unused_383_);
v___x_358_ = v_value_338_;
v_isShared_359_ = v_isSharedCheck_382_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_irData_x3f_354_);
lean_inc(v_parts_353_);
lean_dec(v_value_338_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_382_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v_module_360_; uint8_t v___x_361_; 
v_module_360_ = lean_ctor_get(v_toImport_349_, 0);
v___x_361_ = lean_name_eq(v_module_360_, v___x_334_);
if (v___x_361_ == 0)
{
uint8_t v___x_362_; lean_object* v___x_364_; 
v___x_362_ = 2;
if (v_isShared_352_ == 0)
{
v___x_364_ = v___x_351_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_toImport_349_);
v___x_364_ = v_reuseFailAlloc_371_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_366_; 
lean_ctor_set_uint8(v___x_364_, sizeof(void*)*1, v___x_362_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_364_);
v___x_366_ = v___x_358_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_364_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_parts_353_);
lean_ctor_set(v_reuseFailAlloc_370_, 2, v_irData_x3f_354_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, sizeof(void*)*3, v_needsData_355_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, sizeof(void*)*3 + 1, v_needsIRTrans_356_);
v___x_366_ = v_reuseFailAlloc_370_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_368_; 
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 1, v___x_366_);
lean_ctor_set(v___x_341_, 0, v_a_335_);
v___x_368_ = v___x_341_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_335_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_369_, 2, v_tail_339_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
else
{
uint8_t v___x_372_; lean_object* v___x_374_; 
v___x_372_ = 0;
if (v_isShared_352_ == 0)
{
v___x_374_ = v___x_351_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_toImport_349_);
v___x_374_ = v_reuseFailAlloc_381_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_376_; 
lean_ctor_set_uint8(v___x_374_, sizeof(void*)*1, v___x_372_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_374_);
v___x_376_ = v___x_358_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_parts_353_);
lean_ctor_set(v_reuseFailAlloc_380_, 2, v_irData_x3f_354_);
lean_ctor_set_uint8(v_reuseFailAlloc_380_, sizeof(void*)*3, v_needsData_355_);
lean_ctor_set_uint8(v_reuseFailAlloc_380_, sizeof(void*)*3 + 1, v_needsIRTrans_356_);
v___x_376_ = v_reuseFailAlloc_380_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_378_; 
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 1, v___x_376_);
lean_ctor_set(v___x_341_, 0, v_a_335_);
v___x_378_ = v___x_341_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_335_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_379_, 2, v_tail_339_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5_spec__6___boxed(lean_object* v___x_386_, lean_object* v_a_387_, lean_object* v_x_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5_spec__6(v___x_386_, v_a_387_, v_x_388_);
lean_dec(v___x_386_);
return v_res_389_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5___closed__0(void){
_start:
{
lean_object* v___x_390_; uint64_t v___x_391_; 
v___x_390_ = lean_unsigned_to_nat(1723u);
v___x_391_ = lean_uint64_of_nat(v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5(lean_object* v___x_392_, lean_object* v_m_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_size_395_; lean_object* v_buckets_396_; lean_object* v___x_397_; uint64_t v___y_399_; 
v_size_395_ = lean_ctor_get(v_m_393_, 0);
v_buckets_396_ = lean_ctor_get(v_m_393_, 1);
v___x_397_ = lean_array_get_size(v_buckets_396_);
if (lean_obj_tag(v_a_394_) == 0)
{
uint64_t v___x_426_; 
v___x_426_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5___closed__0);
v___y_399_ = v___x_426_;
goto v___jp_398_;
}
else
{
uint64_t v_hash_427_; 
v_hash_427_ = lean_ctor_get_uint64(v_a_394_, sizeof(void*)*2);
v___y_399_ = v_hash_427_;
goto v___jp_398_;
}
v___jp_398_:
{
uint64_t v___x_400_; uint64_t v___x_401_; uint64_t v_fold_402_; uint64_t v___x_403_; uint64_t v___x_404_; uint64_t v___x_405_; size_t v___x_406_; size_t v___x_407_; size_t v___x_408_; size_t v___x_409_; size_t v___x_410_; lean_object* v_bucket_411_; uint8_t v___x_412_; 
v___x_400_ = 32ULL;
v___x_401_ = lean_uint64_shift_right(v___y_399_, v___x_400_);
v_fold_402_ = lean_uint64_xor(v___y_399_, v___x_401_);
v___x_403_ = 16ULL;
v___x_404_ = lean_uint64_shift_right(v_fold_402_, v___x_403_);
v___x_405_ = lean_uint64_xor(v_fold_402_, v___x_404_);
v___x_406_ = lean_uint64_to_usize(v___x_405_);
v___x_407_ = lean_usize_of_nat(v___x_397_);
v___x_408_ = ((size_t)1ULL);
v___x_409_ = lean_usize_sub(v___x_407_, v___x_408_);
v___x_410_ = lean_usize_land(v___x_406_, v___x_409_);
v_bucket_411_ = lean_array_uget_borrowed(v_buckets_396_, v___x_410_);
v___x_412_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_a_394_, v_bucket_411_);
if (v___x_412_ == 0)
{
lean_dec(v_a_394_);
return v_m_393_;
}
else
{
lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_423_; 
lean_inc(v_bucket_411_);
lean_inc_ref(v_buckets_396_);
lean_inc(v_size_395_);
v_isSharedCheck_423_ = !lean_is_exclusive(v_m_393_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; lean_object* v_unused_425_; 
v_unused_424_ = lean_ctor_get(v_m_393_, 1);
lean_dec(v_unused_424_);
v_unused_425_ = lean_ctor_get(v_m_393_, 0);
lean_dec(v_unused_425_);
v___x_414_ = v_m_393_;
v_isShared_415_ = v_isSharedCheck_423_;
goto v_resetjp_413_;
}
else
{
lean_dec(v_m_393_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_423_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v_buckets_417_; lean_object* v_bucket_418_; lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_416_ = lean_box(0);
v_buckets_417_ = lean_array_uset(v_buckets_396_, v___x_410_, v___x_416_);
v_bucket_418_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5_spec__6(v___x_392_, v_a_394_, v_bucket_411_);
v___x_419_ = lean_array_uset(v_buckets_417_, v___x_410_, v_bucket_418_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 1, v___x_419_);
v___x_421_ = v___x_414_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_size_395_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5___boxed(lean_object* v___x_428_, lean_object* v_m_429_, lean_object* v_a_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5(v___x_428_, v_m_429_, v_a_430_);
lean_dec(v___x_428_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_main___lam__0(lean_object* v___x_432_, lean_object* v___x_433_, uint8_t v___x_434_, lean_object* v___x_435_, uint8_t v___y_436_, lean_object* v_name_437_, lean_object* v___x_438_, uint8_t v___x_439_){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_st_mk_ref(v___x_432_);
lean_inc(v___x_441_);
v___x_442_ = l_Lean_importModulesCore(v___x_433_, v___x_434_, v___x_435_, v___y_436_, v___x_441_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v___x_443_; lean_object* v_moduleNameMap_444_; lean_object* v_moduleNames_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_459_; 
lean_dec_ref(v___x_442_);
v___x_443_ = lean_st_ref_get(v___x_441_);
lean_dec(v___x_441_);
v_moduleNameMap_444_ = lean_ctor_get(v___x_443_, 0);
v_moduleNames_445_ = lean_ctor_get(v___x_443_, 1);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_459_ == 0)
{
v___x_447_ = v___x_443_;
v_isShared_448_ = v_isSharedCheck_459_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_moduleNames_445_);
lean_inc(v_moduleNameMap_444_);
lean_dec(v___x_443_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_459_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_451_; 
lean_inc(v_name_437_);
v___x_449_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5(v_name_437_, v_moduleNameMap_444_, v_name_437_);
lean_dec(v_name_437_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_449_);
v___x_451_ = v___x_447_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_449_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_moduleNames_445_);
v___x_451_ = v_reuseFailAlloc_458_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
uint32_t v___x_452_; uint8_t v___x_453_; uint8_t v___x_454_; uint8_t v___x_455_; 
v___x_452_ = 0;
v___x_453_ = 0;
v___x_454_ = 0;
v___x_455_ = l_Lean_instDecidableEqOLeanLevel(v___x_454_, v___x_434_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_finalizeImport(v___x_451_, v___x_433_, v___x_438_, v___x_452_, v___x_439_, v___x_453_, v___x_454_, v___x_439_);
lean_dec_ref(v___x_451_);
return v___x_456_;
}
else
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_finalizeImport(v___x_451_, v___x_433_, v___x_438_, v___x_452_, v___x_439_, v___x_453_, v___x_454_, v___x_453_);
lean_dec_ref(v___x_451_);
return v___x_457_;
}
}
}
}
else
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
lean_dec(v___x_441_);
lean_dec_ref(v___x_438_);
lean_dec(v_name_437_);
lean_dec_ref(v___x_433_);
v_a_460_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___x_442_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_442_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_460_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__0___boxed(lean_object* v___x_468_, lean_object* v___x_469_, lean_object* v___x_470_, lean_object* v___x_471_, lean_object* v___y_472_, lean_object* v_name_473_, lean_object* v___x_474_, lean_object* v___x_475_, lean_object* v___y_476_){
_start:
{
uint8_t v___x_36003__boxed_477_; uint8_t v___y_36005__boxed_478_; uint8_t v___x_36007__boxed_479_; lean_object* v_res_480_; 
v___x_36003__boxed_477_ = lean_unbox(v___x_470_);
v___y_36005__boxed_478_ = lean_unbox(v___y_472_);
v___x_36007__boxed_479_ = lean_unbox(v___x_475_);
v_res_480_ = l_main___lam__0(v___x_468_, v___x_469_, v___x_36003__boxed_477_, v___x_471_, v___y_36005__boxed_478_, v_name_473_, v___x_474_, v___x_36007__boxed_479_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_main___lam__1(lean_object* v___x_482_, lean_object* v___x_483_, lean_object* v___x_484_, lean_object* v___x_485_, lean_object* v___x_486_, lean_object* v_name_487_, lean_object* v_a_488_, lean_object* v___x_489_, lean_object* v_head_490_, lean_object* v___x_491_, lean_object* v___x_492_, lean_object* v___x_493_, lean_object* v___x_494_, lean_object* v___x_495_, lean_object* v___x_496_, lean_object* v___x_497_, lean_object* v___x_498_, uint8_t v___x_499_, uint8_t v___x_500_){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v_env_506_; uint8_t v___x_507_; lean_object* v_fileName_509_; lean_object* v_fileMap_510_; lean_object* v_currRecDepth_511_; lean_object* v_ref_512_; lean_object* v_currNamespace_513_; lean_object* v_openDecls_514_; lean_object* v_initHeartbeats_515_; lean_object* v_maxHeartbeats_516_; lean_object* v_quotContext_517_; lean_object* v_currMacroScope_518_; lean_object* v_cancelTk_x3f_519_; uint8_t v_suppressElabErrors_520_; lean_object* v_inheritedTraceOptions_521_; lean_object* v___y_522_; uint8_t v___y_550_; uint8_t v___x_570_; 
v___x_502_ = lean_io_get_num_heartbeats();
v___x_503_ = lean_st_mk_ref(v___x_482_);
v___x_504_ = lean_st_ref_get(v___x_483_);
v___x_505_ = lean_st_ref_get(v___x_503_);
v_env_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc_ref(v_env_506_);
lean_dec(v___x_505_);
v___x_507_ = l_Lean_Option_get___at___00main_spec__6(v___x_484_, v___x_485_);
v___x_570_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_506_);
lean_dec_ref(v_env_506_);
if (v___x_570_ == 0)
{
if (v___x_507_ == 0)
{
v___y_550_ = v___x_500_;
goto v___jp_549_;
}
else
{
v___y_550_ = v___x_570_;
goto v___jp_549_;
}
}
else
{
v___y_550_ = v___x_507_;
goto v___jp_549_;
}
v___jp_508_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_523_ = l_Lean_Option_get___at___00main_spec__7(v___x_484_, v___x_486_);
v___x_524_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_524_, 0, v_fileName_509_);
lean_ctor_set(v___x_524_, 1, v_fileMap_510_);
lean_ctor_set(v___x_524_, 2, v___x_484_);
lean_ctor_set(v___x_524_, 3, v_currRecDepth_511_);
lean_ctor_set(v___x_524_, 4, v___x_523_);
lean_ctor_set(v___x_524_, 5, v_ref_512_);
lean_ctor_set(v___x_524_, 6, v_currNamespace_513_);
lean_ctor_set(v___x_524_, 7, v_openDecls_514_);
lean_ctor_set(v___x_524_, 8, v_initHeartbeats_515_);
lean_ctor_set(v___x_524_, 9, v_maxHeartbeats_516_);
lean_ctor_set(v___x_524_, 10, v_quotContext_517_);
lean_ctor_set(v___x_524_, 11, v_currMacroScope_518_);
lean_ctor_set(v___x_524_, 12, v_cancelTk_x3f_519_);
lean_ctor_set(v___x_524_, 13, v_inheritedTraceOptions_521_);
lean_ctor_set_uint8(v___x_524_, sizeof(void*)*14, v___x_507_);
lean_ctor_set_uint8(v___x_524_, sizeof(void*)*14 + 1, v_suppressElabErrors_520_);
v___x_525_ = l_Lean_Compiler_LCNF_emitC(v_name_487_, v___x_524_, v___y_522_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref(v___x_525_);
v___x_527_ = lean_st_ref_get(v___x_503_);
lean_dec(v___x_503_);
lean_dec(v___x_527_);
v___x_528_ = lean_string_to_utf8(v_a_526_);
lean_dec(v_a_526_);
v___x_529_ = lean_io_prim_handle_write(v_a_488_, v___x_528_);
lean_dec_ref(v___x_528_);
return v___x_529_;
}
else
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_548_; 
lean_dec(v___x_503_);
v_a_530_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_548_ == 0)
{
v___x_532_ = v___x_525_;
v_isShared_533_ = v_isSharedCheck_548_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_525_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_548_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
if (lean_obj_tag(v_a_530_) == 0)
{
lean_object* v_msg_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_538_; 
v_msg_534_ = lean_ctor_get(v_a_530_, 1);
lean_inc_ref(v_msg_534_);
lean_dec_ref(v_a_530_);
v___x_535_ = l_Lean_MessageData_toString(v_msg_534_);
v___x_536_ = lean_mk_io_user_error(v___x_535_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_536_);
v___x_538_ = v___x_532_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
else
{
lean_object* v_id_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_546_; 
v_id_540_ = lean_ctor_get(v_a_530_, 0);
lean_inc(v_id_540_);
lean_dec_ref(v_a_530_);
v___x_541_ = ((lean_object*)(l_main___lam__1___closed__0));
v___x_542_ = l_Nat_reprFast(v_id_540_);
v___x_543_ = lean_string_append(v___x_541_, v___x_542_);
lean_dec_ref(v___x_542_);
v___x_544_ = lean_mk_io_user_error(v___x_543_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_544_);
v___x_546_ = v___x_532_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
v___jp_549_:
{
if (v___y_550_ == 0)
{
lean_object* v___x_551_; lean_object* v_env_552_; lean_object* v_nextMacroScope_553_; lean_object* v_ngen_554_; lean_object* v_auxDeclNGen_555_; lean_object* v_traceState_556_; lean_object* v_messages_557_; lean_object* v_infoState_558_; lean_object* v_snapshotTasks_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_568_; 
v___x_551_ = lean_st_ref_take(v___x_503_);
v_env_552_ = lean_ctor_get(v___x_551_, 0);
v_nextMacroScope_553_ = lean_ctor_get(v___x_551_, 1);
v_ngen_554_ = lean_ctor_get(v___x_551_, 2);
v_auxDeclNGen_555_ = lean_ctor_get(v___x_551_, 3);
v_traceState_556_ = lean_ctor_get(v___x_551_, 4);
v_messages_557_ = lean_ctor_get(v___x_551_, 6);
v_infoState_558_ = lean_ctor_get(v___x_551_, 7);
v_snapshotTasks_559_ = lean_ctor_get(v___x_551_, 8);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_568_ == 0)
{
lean_object* v_unused_569_; 
v_unused_569_ = lean_ctor_get(v___x_551_, 5);
lean_dec(v_unused_569_);
v___x_561_ = v___x_551_;
v_isShared_562_ = v_isSharedCheck_568_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_snapshotTasks_559_);
lean_inc(v_infoState_558_);
lean_inc(v_messages_557_);
lean_inc(v_traceState_556_);
lean_inc(v_auxDeclNGen_555_);
lean_inc(v_ngen_554_);
lean_inc(v_nextMacroScope_553_);
lean_inc(v_env_552_);
lean_dec(v___x_551_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_568_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_563_ = l_Lean_Kernel_enableDiag(v_env_552_, v___x_507_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 5, v___x_489_);
lean_ctor_set(v___x_561_, 0, v___x_563_);
v___x_565_ = v___x_561_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_nextMacroScope_553_);
lean_ctor_set(v_reuseFailAlloc_567_, 2, v_ngen_554_);
lean_ctor_set(v_reuseFailAlloc_567_, 3, v_auxDeclNGen_555_);
lean_ctor_set(v_reuseFailAlloc_567_, 4, v_traceState_556_);
lean_ctor_set(v_reuseFailAlloc_567_, 5, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_567_, 6, v_messages_557_);
lean_ctor_set(v_reuseFailAlloc_567_, 7, v_infoState_558_);
lean_ctor_set(v_reuseFailAlloc_567_, 8, v_snapshotTasks_559_);
v___x_565_ = v_reuseFailAlloc_567_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_566_; 
v___x_566_ = lean_st_ref_set(v___x_503_, v___x_565_);
lean_inc(v___x_503_);
lean_inc(v___x_494_);
v_fileName_509_ = v_head_490_;
v_fileMap_510_ = v___x_491_;
v_currRecDepth_511_ = v___x_492_;
v_ref_512_ = v___x_493_;
v_currNamespace_513_ = v___x_494_;
v_openDecls_514_ = v___x_495_;
v_initHeartbeats_515_ = v___x_502_;
v_maxHeartbeats_516_ = v___x_496_;
v_quotContext_517_ = v___x_494_;
v_currMacroScope_518_ = v___x_497_;
v_cancelTk_x3f_519_ = v___x_498_;
v_suppressElabErrors_520_ = v___x_499_;
v_inheritedTraceOptions_521_ = v___x_504_;
v___y_522_ = v___x_503_;
goto v___jp_508_;
}
}
}
else
{
lean_dec_ref(v___x_489_);
lean_inc(v___x_503_);
lean_inc(v___x_494_);
v_fileName_509_ = v_head_490_;
v_fileMap_510_ = v___x_491_;
v_currRecDepth_511_ = v___x_492_;
v_ref_512_ = v___x_493_;
v_currNamespace_513_ = v___x_494_;
v_openDecls_514_ = v___x_495_;
v_initHeartbeats_515_ = v___x_502_;
v_maxHeartbeats_516_ = v___x_496_;
v_quotContext_517_ = v___x_494_;
v_currMacroScope_518_ = v___x_497_;
v_cancelTk_x3f_519_ = v___x_498_;
v_suppressElabErrors_520_ = v___x_499_;
v_inheritedTraceOptions_521_ = v___x_504_;
v___y_522_ = v___x_503_;
goto v___jp_508_;
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__1___boxed(lean_object** _args){
lean_object* v___x_571_ = _args[0];
lean_object* v___x_572_ = _args[1];
lean_object* v___x_573_ = _args[2];
lean_object* v___x_574_ = _args[3];
lean_object* v___x_575_ = _args[4];
lean_object* v_name_576_ = _args[5];
lean_object* v_a_577_ = _args[6];
lean_object* v___x_578_ = _args[7];
lean_object* v_head_579_ = _args[8];
lean_object* v___x_580_ = _args[9];
lean_object* v___x_581_ = _args[10];
lean_object* v___x_582_ = _args[11];
lean_object* v___x_583_ = _args[12];
lean_object* v___x_584_ = _args[13];
lean_object* v___x_585_ = _args[14];
lean_object* v___x_586_ = _args[15];
lean_object* v___x_587_ = _args[16];
lean_object* v___x_588_ = _args[17];
lean_object* v___x_589_ = _args[18];
lean_object* v___y_590_ = _args[19];
_start:
{
uint8_t v___x_36094__boxed_591_; uint8_t v___x_36095__boxed_592_; lean_object* v_res_593_; 
v___x_36094__boxed_591_ = lean_unbox(v___x_588_);
v___x_36095__boxed_592_ = lean_unbox(v___x_589_);
v_res_593_ = l_main___lam__1(v___x_571_, v___x_572_, v___x_573_, v___x_574_, v___x_575_, v_name_576_, v_a_577_, v___x_578_, v_head_579_, v___x_580_, v___x_581_, v___x_582_, v___x_583_, v___x_584_, v___x_585_, v___x_586_, v___x_587_, v___x_36094__boxed_591_, v___x_36095__boxed_592_);
lean_dec(v_a_577_);
lean_dec_ref(v___x_575_);
lean_dec_ref(v___x_574_);
lean_dec(v___x_572_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__3(lean_object* v_x2_594_, lean_object* v_as_595_, size_t v_i_596_, size_t v_stop_597_, lean_object* v_b_598_){
_start:
{
uint8_t v___x_599_; 
v___x_599_ = lean_usize_dec_eq(v_i_596_, v_stop_597_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; size_t v___x_602_; size_t v___x_603_; 
v___x_600_ = lean_array_uget_borrowed(v_as_595_, v_i_596_);
lean_inc_ref(v_x2_594_);
lean_inc(v___x_600_);
v___x_601_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_600_, v_x2_594_, v_b_598_);
v___x_602_ = ((size_t)1ULL);
v___x_603_ = lean_usize_add(v_i_596_, v___x_602_);
v_i_596_ = v___x_603_;
v_b_598_ = v___x_601_;
goto _start;
}
else
{
lean_dec_ref(v_x2_594_);
return v_b_598_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__3___boxed(lean_object* v_x2_605_, lean_object* v_as_606_, lean_object* v_i_607_, lean_object* v_stop_608_, lean_object* v_b_609_){
_start:
{
size_t v_i_boxed_610_; size_t v_stop_boxed_611_; lean_object* v_res_612_; 
v_i_boxed_610_ = lean_unbox_usize(v_i_607_);
lean_dec(v_i_607_);
v_stop_boxed_611_ = lean_unbox_usize(v_stop_608_);
lean_dec(v_stop_608_);
v_res_612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__3(v_x2_605_, v_as_606_, v_i_boxed_610_, v_stop_boxed_611_, v_b_609_);
lean_dec_ref(v_as_606_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(lean_object* v_as_613_, size_t v_i_614_, size_t v_stop_615_, lean_object* v_b_616_){
_start:
{
lean_object* v___y_618_; uint8_t v___x_622_; 
v___x_622_ = lean_usize_dec_eq(v_i_614_, v_stop_615_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_623_ = lean_unsigned_to_nat(0u);
v___x_624_ = lean_array_uget_borrowed(v_as_613_, v_i_614_);
v___x_625_ = lean_array_get_size(v___x_624_);
v___x_626_ = lean_nat_dec_lt(v___x_623_, v___x_625_);
if (v___x_626_ == 0)
{
v___y_618_ = v_b_616_;
goto v___jp_617_;
}
else
{
uint8_t v___x_627_; 
v___x_627_ = lean_nat_dec_le(v___x_625_, v___x_625_);
if (v___x_627_ == 0)
{
if (v___x_626_ == 0)
{
v___y_618_ = v_b_616_;
goto v___jp_617_;
}
else
{
size_t v___x_628_; size_t v___x_629_; lean_object* v___x_630_; 
v___x_628_ = ((size_t)0ULL);
v___x_629_ = lean_usize_of_nat(v___x_625_);
lean_inc(v___x_624_);
v___x_630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__3(v___x_624_, v___x_624_, v___x_628_, v___x_629_, v_b_616_);
v___y_618_ = v___x_630_;
goto v___jp_617_;
}
}
else
{
size_t v___x_631_; size_t v___x_632_; lean_object* v___x_633_; 
v___x_631_ = ((size_t)0ULL);
v___x_632_ = lean_usize_of_nat(v___x_625_);
lean_inc(v___x_624_);
v___x_633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__3(v___x_624_, v___x_624_, v___x_631_, v___x_632_, v_b_616_);
v___y_618_ = v___x_633_;
goto v___jp_617_;
}
}
}
else
{
return v_b_616_;
}
v___jp_617_:
{
size_t v___x_619_; size_t v___x_620_; 
v___x_619_ = ((size_t)1ULL);
v___x_620_ = lean_usize_add(v_i_614_, v___x_619_);
v_i_614_ = v___x_620_;
v_b_616_ = v___y_618_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14___boxed(lean_object* v_as_634_, lean_object* v_i_635_, lean_object* v_stop_636_, lean_object* v_b_637_){
_start:
{
size_t v_i_boxed_638_; size_t v_stop_boxed_639_; lean_object* v_res_640_; 
v_i_boxed_638_ = lean_unbox_usize(v_i_635_);
lean_dec(v_i_635_);
v_stop_boxed_639_ = lean_unbox_usize(v_stop_636_);
lean_dec(v_stop_636_);
v_res_640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v_as_634_, v_i_boxed_638_, v_stop_boxed_639_, v_b_637_);
lean_dec_ref(v_as_634_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__9_spec__20(lean_object* v_s_641_){
_start:
{
lean_object* v___x_643_; lean_object* v_putStr_644_; lean_object* v___x_645_; 
v___x_643_ = lean_get_stderr();
v_putStr_644_ = lean_ctor_get(v___x_643_, 4);
lean_inc_ref(v_putStr_644_);
lean_dec_ref(v___x_643_);
v___x_645_ = lean_apply_2(v_putStr_644_, v_s_641_, lean_box(0));
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__9_spec__20___boxed(lean_object* v_s_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__9_spec__20(v_s_646_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__9(lean_object* v_s_649_){
_start:
{
uint32_t v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_651_ = 10;
v___x_652_ = lean_string_push(v_s_649_, v___x_651_);
v___x_653_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__9_spec__20(v___x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__9___boxed(lean_object* v_s_654_, lean_object* v_a_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_IO_eprintln___at___00main_spec__9(v_s_654_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__30_spec__43(lean_object* v_as_660_, size_t v_sz_661_, size_t v_i_662_, lean_object* v_b_663_){
_start:
{
uint8_t v___x_665_; 
v___x_665_ = lean_usize_dec_lt(v_i_662_, v_sz_661_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; 
v___x_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_666_, 0, v_b_663_);
return v___x_666_;
}
else
{
uint8_t v___x_667_; lean_object* v_a_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
lean_dec_ref(v_b_663_);
v___x_667_ = 0;
v_a_668_ = lean_array_uget_borrowed(v_as_660_, v_i_662_);
lean_inc(v_a_668_);
v___x_669_ = l_Lean_Message_toString(v_a_668_, v___x_667_);
v___x_670_ = l_IO_eprintln___at___00main_spec__9(v___x_669_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v___x_671_; size_t v___x_672_; size_t v___x_673_; 
lean_dec_ref(v___x_670_);
v___x_671_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__30_spec__43___closed__0));
v___x_672_ = ((size_t)1ULL);
v___x_673_ = lean_usize_add(v_i_662_, v___x_672_);
v_i_662_ = v___x_673_;
v_b_663_ = v___x_671_;
goto _start;
}
else
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
v_a_675_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_670_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_670_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__30_spec__43___boxed(lean_object* v_as_683_, lean_object* v_sz_684_, lean_object* v_i_685_, lean_object* v_b_686_, lean_object* v___y_687_){
_start:
{
size_t v_sz_boxed_688_; size_t v_i_boxed_689_; lean_object* v_res_690_; 
v_sz_boxed_688_ = lean_unbox_usize(v_sz_684_);
lean_dec(v_sz_684_);
v_i_boxed_689_ = lean_unbox_usize(v_i_685_);
lean_dec(v_i_685_);
v_res_690_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__30_spec__43(v_as_683_, v_sz_boxed_688_, v_i_boxed_689_, v_b_686_);
lean_dec_ref(v_as_683_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__30(lean_object* v_as_691_, size_t v_sz_692_, size_t v_i_693_, lean_object* v_b_694_){
_start:
{
uint8_t v___x_696_; 
v___x_696_ = lean_usize_dec_lt(v_i_693_, v_sz_692_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; 
v___x_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_697_, 0, v_b_694_);
return v___x_697_;
}
else
{
uint8_t v___x_698_; lean_object* v_a_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
lean_dec_ref(v_b_694_);
v___x_698_ = 0;
v_a_699_ = lean_array_uget_borrowed(v_as_691_, v_i_693_);
lean_inc(v_a_699_);
v___x_700_ = l_Lean_Message_toString(v_a_699_, v___x_698_);
v___x_701_ = l_IO_eprintln___at___00main_spec__9(v___x_700_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v___x_702_; size_t v___x_703_; size_t v___x_704_; lean_object* v___x_705_; 
lean_dec_ref(v___x_701_);
v___x_702_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__30_spec__43___closed__0));
v___x_703_ = ((size_t)1ULL);
v___x_704_ = lean_usize_add(v_i_693_, v___x_703_);
v___x_705_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__30_spec__43(v_as_691_, v_sz_692_, v___x_704_, v___x_702_);
return v___x_705_;
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
v_a_706_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_701_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_701_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__30___boxed(lean_object* v_as_714_, lean_object* v_sz_715_, lean_object* v_i_716_, lean_object* v_b_717_, lean_object* v___y_718_){
_start:
{
size_t v_sz_boxed_719_; size_t v_i_boxed_720_; lean_object* v_res_721_; 
v_sz_boxed_719_ = lean_unbox_usize(v_sz_715_);
lean_dec(v_sz_715_);
v_i_boxed_720_ = lean_unbox_usize(v_i_716_);
lean_dec(v_i_716_);
v_res_721_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__30(v_as_714_, v_sz_boxed_719_, v_i_boxed_720_, v_b_717_);
lean_dec_ref(v_as_714_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22(lean_object* v_inh_722_, lean_object* v_n_723_, lean_object* v_b_724_){
_start:
{
if (lean_obj_tag(v_n_723_) == 0)
{
lean_object* v_cs_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_760_; 
v_cs_726_ = lean_ctor_get(v_n_723_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v_n_723_);
if (v_isSharedCheck_760_ == 0)
{
v___x_728_ = v_n_723_;
v_isShared_729_ = v_isSharedCheck_760_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_cs_726_);
lean_dec(v_n_723_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_760_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v___x_731_; size_t v_sz_732_; size_t v___x_733_; lean_object* v___x_734_; 
v___x_730_ = lean_box(0);
v___x_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
lean_ctor_set(v___x_731_, 1, v_b_724_);
v_sz_732_ = lean_array_size(v_cs_726_);
v___x_733_ = ((size_t)0ULL);
v___x_734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__29(v_inh_722_, v_cs_726_, v_sz_732_, v___x_733_, v___x_731_);
lean_dec_ref(v_cs_726_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_751_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_751_ == 0)
{
v___x_737_ = v___x_734_;
v_isShared_738_ = v_isSharedCheck_751_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_751_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v_fst_739_; 
v_fst_739_ = lean_ctor_get(v_a_735_, 0);
if (lean_obj_tag(v_fst_739_) == 0)
{
lean_object* v_snd_740_; lean_object* v___x_742_; 
v_snd_740_ = lean_ctor_get(v_a_735_, 1);
lean_inc(v_snd_740_);
lean_dec(v_a_735_);
if (v_isShared_729_ == 0)
{
lean_ctor_set_tag(v___x_728_, 1);
lean_ctor_set(v___x_728_, 0, v_snd_740_);
v___x_742_ = v___x_728_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_snd_740_);
v___x_742_ = v_reuseFailAlloc_746_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_744_; 
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_742_);
v___x_744_ = v___x_737_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
else
{
lean_object* v_val_747_; lean_object* v___x_749_; 
lean_inc_ref(v_fst_739_);
lean_dec(v_a_735_);
lean_del_object(v___x_728_);
v_val_747_ = lean_ctor_get(v_fst_739_, 0);
lean_inc(v_val_747_);
lean_dec_ref(v_fst_739_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v_val_747_);
v___x_749_ = v___x_737_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_val_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_del_object(v___x_728_);
v_a_752_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_734_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_734_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
}
else
{
lean_object* v_vs_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_795_; 
v_vs_761_ = lean_ctor_get(v_n_723_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v_n_723_);
if (v_isSharedCheck_795_ == 0)
{
v___x_763_ = v_n_723_;
v_isShared_764_ = v_isSharedCheck_795_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_vs_761_);
lean_dec(v_n_723_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_795_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; lean_object* v___x_766_; size_t v_sz_767_; size_t v___x_768_; lean_object* v___x_769_; 
v___x_765_ = lean_box(0);
v___x_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
lean_ctor_set(v___x_766_, 1, v_b_724_);
v_sz_767_ = lean_array_size(v_vs_761_);
v___x_768_ = ((size_t)0ULL);
v___x_769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__30(v_vs_761_, v_sz_767_, v___x_768_, v___x_766_);
lean_dec_ref(v_vs_761_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_786_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_786_ == 0)
{
v___x_772_ = v___x_769_;
v_isShared_773_ = v_isSharedCheck_786_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_769_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_786_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v_fst_774_; 
v_fst_774_ = lean_ctor_get(v_a_770_, 0);
if (lean_obj_tag(v_fst_774_) == 0)
{
lean_object* v_snd_775_; lean_object* v___x_777_; 
v_snd_775_ = lean_ctor_get(v_a_770_, 1);
lean_inc(v_snd_775_);
lean_dec(v_a_770_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v_snd_775_);
v___x_777_ = v___x_763_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_snd_775_);
v___x_777_ = v_reuseFailAlloc_781_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_779_; 
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_777_);
v___x_779_ = v___x_772_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_777_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
else
{
lean_object* v_val_782_; lean_object* v___x_784_; 
lean_inc_ref(v_fst_774_);
lean_dec(v_a_770_);
lean_del_object(v___x_763_);
v_val_782_ = lean_ctor_get(v_fst_774_, 0);
lean_inc(v_val_782_);
lean_dec_ref(v_fst_774_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v_val_782_);
v___x_784_ = v___x_772_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_val_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_del_object(v___x_763_);
v_a_787_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_769_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_769_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__29(lean_object* v_inh_796_, lean_object* v_as_797_, size_t v_sz_798_, size_t v_i_799_, lean_object* v_b_800_){
_start:
{
uint8_t v___x_802_; 
v___x_802_ = lean_usize_dec_lt(v_i_799_, v_sz_798_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; 
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v_b_800_);
return v___x_803_;
}
else
{
lean_object* v_snd_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_838_; 
v_snd_804_ = lean_ctor_get(v_b_800_, 1);
v_isSharedCheck_838_ = !lean_is_exclusive(v_b_800_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; 
v_unused_839_ = lean_ctor_get(v_b_800_, 0);
lean_dec(v_unused_839_);
v___x_806_ = v_b_800_;
v_isShared_807_ = v_isSharedCheck_838_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_snd_804_);
lean_dec(v_b_800_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_838_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v_a_808_; lean_object* v___x_809_; 
v_a_808_ = lean_array_uget_borrowed(v_as_797_, v_i_799_);
lean_inc(v_snd_804_);
lean_inc(v_a_808_);
v___x_809_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22(v_inh_796_, v_a_808_, v_snd_804_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_829_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_829_ == 0)
{
v___x_812_ = v___x_809_;
v_isShared_813_ = v_isSharedCheck_829_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_809_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_829_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
if (lean_obj_tag(v_a_810_) == 0)
{
lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_814_, 0, v_a_810_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v___x_814_);
v___x_816_ = v___x_806_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_snd_804_);
v___x_816_ = v_reuseFailAlloc_820_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_818_; 
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v___x_816_);
v___x_818_ = v___x_812_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
else
{
lean_object* v_a_821_; lean_object* v___x_822_; lean_object* v___x_824_; 
lean_del_object(v___x_812_);
lean_dec(v_snd_804_);
v_a_821_ = lean_ctor_get(v_a_810_, 0);
lean_inc(v_a_821_);
lean_dec_ref(v_a_810_);
v___x_822_ = lean_box(0);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 1, v_a_821_);
lean_ctor_set(v___x_806_, 0, v___x_822_);
v___x_824_ = v___x_806_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_822_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_a_821_);
v___x_824_ = v_reuseFailAlloc_828_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
size_t v___x_825_; size_t v___x_826_; 
v___x_825_ = ((size_t)1ULL);
v___x_826_ = lean_usize_add(v_i_799_, v___x_825_);
v_i_799_ = v___x_826_;
v_b_800_ = v___x_824_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_del_object(v___x_806_);
lean_dec(v_snd_804_);
v_a_830_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_809_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_809_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__29___boxed(lean_object* v_inh_840_, lean_object* v_as_841_, lean_object* v_sz_842_, lean_object* v_i_843_, lean_object* v_b_844_, lean_object* v___y_845_){
_start:
{
size_t v_sz_boxed_846_; size_t v_i_boxed_847_; lean_object* v_res_848_; 
v_sz_boxed_846_ = lean_unbox_usize(v_sz_842_);
lean_dec(v_sz_842_);
v_i_boxed_847_ = lean_unbox_usize(v_i_843_);
lean_dec(v_i_843_);
v_res_848_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__29(v_inh_840_, v_as_841_, v_sz_boxed_846_, v_i_boxed_847_, v_b_844_);
lean_dec_ref(v_as_841_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22___boxed(lean_object* v_inh_849_, lean_object* v_n_850_, lean_object* v_b_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22(v_inh_849_, v_n_850_, v_b_851_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__23_spec__32(lean_object* v_as_857_, size_t v_sz_858_, size_t v_i_859_, lean_object* v_b_860_){
_start:
{
uint8_t v___x_862_; 
v___x_862_ = lean_usize_dec_lt(v_i_859_, v_sz_858_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; 
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v_b_860_);
return v___x_863_;
}
else
{
uint8_t v___x_864_; lean_object* v_a_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
lean_dec_ref(v_b_860_);
v___x_864_ = 0;
v_a_865_ = lean_array_uget_borrowed(v_as_857_, v_i_859_);
lean_inc(v_a_865_);
v___x_866_ = l_Lean_Message_toString(v_a_865_, v___x_864_);
v___x_867_ = l_IO_eprintln___at___00main_spec__9(v___x_866_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v___x_868_; size_t v___x_869_; size_t v___x_870_; 
lean_dec_ref(v___x_867_);
v___x_868_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__23_spec__32___closed__0));
v___x_869_ = ((size_t)1ULL);
v___x_870_ = lean_usize_add(v_i_859_, v___x_869_);
v_i_859_ = v___x_870_;
v_b_860_ = v___x_868_;
goto _start;
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
v_a_872_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_867_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_867_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__23_spec__32___boxed(lean_object* v_as_880_, lean_object* v_sz_881_, lean_object* v_i_882_, lean_object* v_b_883_, lean_object* v___y_884_){
_start:
{
size_t v_sz_boxed_885_; size_t v_i_boxed_886_; lean_object* v_res_887_; 
v_sz_boxed_885_ = lean_unbox_usize(v_sz_881_);
lean_dec(v_sz_881_);
v_i_boxed_886_ = lean_unbox_usize(v_i_882_);
lean_dec(v_i_882_);
v_res_887_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__23_spec__32(v_as_880_, v_sz_boxed_885_, v_i_boxed_886_, v_b_883_);
lean_dec_ref(v_as_880_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__23(lean_object* v_as_888_, size_t v_sz_889_, size_t v_i_890_, lean_object* v_b_891_){
_start:
{
uint8_t v___x_893_; 
v___x_893_ = lean_usize_dec_lt(v_i_890_, v_sz_889_);
if (v___x_893_ == 0)
{
lean_object* v___x_894_; 
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v_b_891_);
return v___x_894_;
}
else
{
uint8_t v___x_895_; lean_object* v_a_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
lean_dec_ref(v_b_891_);
v___x_895_ = 0;
v_a_896_ = lean_array_uget_borrowed(v_as_888_, v_i_890_);
lean_inc(v_a_896_);
v___x_897_ = l_Lean_Message_toString(v_a_896_, v___x_895_);
v___x_898_ = l_IO_eprintln___at___00main_spec__9(v___x_897_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v___x_899_; size_t v___x_900_; size_t v___x_901_; lean_object* v___x_902_; 
lean_dec_ref(v___x_898_);
v___x_899_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__23_spec__32___closed__0));
v___x_900_ = ((size_t)1ULL);
v___x_901_ = lean_usize_add(v_i_890_, v___x_900_);
v___x_902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__23_spec__32(v_as_888_, v_sz_889_, v___x_901_, v___x_899_);
return v___x_902_;
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
v_a_903_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_898_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_898_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__23___boxed(lean_object* v_as_911_, lean_object* v_sz_912_, lean_object* v_i_913_, lean_object* v_b_914_, lean_object* v___y_915_){
_start:
{
size_t v_sz_boxed_916_; size_t v_i_boxed_917_; lean_object* v_res_918_; 
v_sz_boxed_916_ = lean_unbox_usize(v_sz_912_);
lean_dec(v_sz_912_);
v_i_boxed_917_ = lean_unbox_usize(v_i_913_);
lean_dec(v_i_913_);
v_res_918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__23(v_as_911_, v_sz_boxed_916_, v_i_boxed_917_, v_b_914_);
lean_dec_ref(v_as_911_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__10(lean_object* v_t_919_, lean_object* v_init_920_){
_start:
{
lean_object* v_root_922_; lean_object* v_tail_923_; lean_object* v___x_924_; 
v_root_922_ = lean_ctor_get(v_t_919_, 0);
lean_inc_ref(v_root_922_);
v_tail_923_ = lean_ctor_get(v_t_919_, 1);
lean_inc_ref(v_tail_923_);
lean_dec_ref(v_t_919_);
v___x_924_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22(v_init_920_, v_root_922_, v_init_920_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_961_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_961_ == 0)
{
v___x_927_ = v___x_924_;
v_isShared_928_ = v_isSharedCheck_961_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_924_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_961_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
if (lean_obj_tag(v_a_925_) == 0)
{
lean_object* v_a_929_; lean_object* v___x_931_; 
lean_dec_ref(v_tail_923_);
v_a_929_ = lean_ctor_get(v_a_925_, 0);
lean_inc(v_a_929_);
lean_dec_ref(v_a_925_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v_a_929_);
v___x_931_ = v___x_927_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
else
{
lean_object* v_a_933_; lean_object* v___x_934_; lean_object* v___x_935_; size_t v_sz_936_; size_t v___x_937_; lean_object* v___x_938_; 
lean_del_object(v___x_927_);
v_a_933_ = lean_ctor_get(v_a_925_, 0);
lean_inc(v_a_933_);
lean_dec_ref(v_a_925_);
v___x_934_ = lean_box(0);
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set(v___x_935_, 1, v_a_933_);
v_sz_936_ = lean_array_size(v_tail_923_);
v___x_937_ = ((size_t)0ULL);
v___x_938_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__23(v_tail_923_, v_sz_936_, v___x_937_, v___x_935_);
lean_dec_ref(v_tail_923_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_952_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_952_ == 0)
{
v___x_941_ = v___x_938_;
v_isShared_942_ = v_isSharedCheck_952_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_952_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v_fst_943_; 
v_fst_943_ = lean_ctor_get(v_a_939_, 0);
if (lean_obj_tag(v_fst_943_) == 0)
{
lean_object* v_snd_944_; lean_object* v___x_946_; 
v_snd_944_ = lean_ctor_get(v_a_939_, 1);
lean_inc(v_snd_944_);
lean_dec(v_a_939_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v_snd_944_);
v___x_946_ = v___x_941_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_snd_944_);
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
lean_inc_ref(v_fst_943_);
lean_dec(v_a_939_);
v_val_948_ = lean_ctor_get(v_fst_943_, 0);
lean_inc(v_val_948_);
lean_dec_ref(v_fst_943_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v_val_948_);
v___x_950_ = v___x_941_;
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
v_a_953_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_938_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_938_);
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
}
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
lean_dec_ref(v_tail_923_);
v_a_962_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_924_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_924_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__10___boxed(lean_object* v_t_970_, lean_object* v_init_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_PersistentArray_forIn___at___00main_spec__10(v_t_970_, v_init_971_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__4_spec__4(lean_object* v_o_977_, lean_object* v_k_978_, lean_object* v_v_979_){
_start:
{
lean_object* v_map_980_; uint8_t v_hasTrace_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_995_; 
v_map_980_ = lean_ctor_get(v_o_977_, 0);
v_hasTrace_981_ = lean_ctor_get_uint8(v_o_977_, sizeof(void*)*1);
v_isSharedCheck_995_ = !lean_is_exclusive(v_o_977_);
if (v_isSharedCheck_995_ == 0)
{
v___x_983_ = v_o_977_;
v_isShared_984_ = v_isSharedCheck_995_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_map_980_);
lean_dec(v_o_977_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_995_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_985_, 0, v_v_979_);
lean_inc(v_k_978_);
v___x_986_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_978_, v___x_985_, v_map_980_);
if (v_hasTrace_981_ == 0)
{
lean_object* v___x_987_; uint8_t v___x_988_; lean_object* v___x_990_; 
v___x_987_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__4_spec__4___closed__1));
v___x_988_ = l_Lean_Name_isPrefixOf(v___x_987_, v_k_978_);
lean_dec(v_k_978_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_986_);
v___x_990_ = v___x_983_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_986_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_ctor_set_uint8(v___x_990_, sizeof(void*)*1, v___x_988_);
return v___x_990_;
}
}
else
{
lean_object* v___x_993_; 
lean_dec(v_k_978_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_986_);
v___x_993_ = v___x_983_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_986_);
lean_ctor_set_uint8(v_reuseFailAlloc_994_, sizeof(void*)*1, v_hasTrace_981_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00main_spec__4(lean_object* v_opts_996_, lean_object* v_opt_997_, lean_object* v_val_998_){
_start:
{
lean_object* v_name_999_; lean_object* v___x_1000_; 
v_name_999_ = lean_ctor_get(v_opt_997_, 0);
lean_inc(v_name_999_);
lean_dec_ref(v_opt_997_);
v___x_1000_ = l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__4_spec__4(v_opts_996_, v_name_999_, v_val_998_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg(lean_object* v_as_x27_1001_, lean_object* v_b_1002_){
_start:
{
if (lean_obj_tag(v_as_x27_1001_) == 0)
{
lean_object* v___x_1004_; 
v___x_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1004_, 0, v_b_1002_);
return v___x_1004_;
}
else
{
lean_object* v_head_1005_; lean_object* v_tail_1006_; lean_object* v___x_1007_; 
v_head_1005_ = lean_ctor_get(v_as_x27_1001_, 0);
lean_inc(v_head_1005_);
v_tail_1006_ = lean_ctor_get(v_as_x27_1001_, 1);
lean_inc(v_tail_1006_);
lean_dec_ref(v_as_x27_1001_);
v___x_1007_ = l___private_LeanIR_0__setConfigOption(v_b_1002_, v_head_1005_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref(v___x_1007_);
v_as_x27_1001_ = v_tail_1006_;
v_b_1002_ = v_a_1008_;
goto _start;
}
else
{
lean_dec(v_tail_1006_);
return v___x_1007_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg___boxed(lean_object* v_as_x27_1010_, lean_object* v_b_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v_as_x27_1010_, v_b_1011_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__17(lean_object* v_x_1014_, lean_object* v_x_1015_){
_start:
{
if (lean_obj_tag(v_x_1015_) == 0)
{
return v_x_1014_;
}
else
{
lean_object* v_key_1016_; lean_object* v_value_1017_; lean_object* v_tail_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v_key_1016_ = lean_ctor_get(v_x_1015_, 0);
v_value_1017_ = lean_ctor_get(v_x_1015_, 1);
v_tail_1018_ = lean_ctor_get(v_x_1015_, 2);
lean_inc(v_value_1017_);
lean_inc(v_key_1016_);
v___x_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1019_, 0, v_key_1016_);
lean_ctor_set(v___x_1019_, 1, v_value_1017_);
v___x_1020_ = lean_array_push(v_x_1014_, v___x_1019_);
v_x_1014_ = v___x_1020_;
v_x_1015_ = v_tail_1018_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__17___boxed(lean_object* v_x_1022_, lean_object* v_x_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__17(v_x_1022_, v_x_1023_);
lean_dec(v_x_1023_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__18(lean_object* v_as_1025_, size_t v_i_1026_, size_t v_stop_1027_, lean_object* v_b_1028_){
_start:
{
uint8_t v___x_1029_; 
v___x_1029_ = lean_usize_dec_eq(v_i_1026_, v_stop_1027_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; lean_object* v___x_1031_; size_t v___x_1032_; size_t v___x_1033_; 
v___x_1030_ = lean_array_uget_borrowed(v_as_1025_, v_i_1026_);
v___x_1031_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__17(v_b_1028_, v___x_1030_);
v___x_1032_ = ((size_t)1ULL);
v___x_1033_ = lean_usize_add(v_i_1026_, v___x_1032_);
v_i_1026_ = v___x_1033_;
v_b_1028_ = v___x_1031_;
goto _start;
}
else
{
return v_b_1028_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__18___boxed(lean_object* v_as_1035_, lean_object* v_i_1036_, lean_object* v_stop_1037_, lean_object* v_b_1038_){
_start:
{
size_t v_i_boxed_1039_; size_t v_stop_boxed_1040_; lean_object* v_res_1041_; 
v_i_boxed_1039_ = lean_unbox_usize(v_i_1036_);
lean_dec(v_i_1036_);
v_stop_boxed_1040_ = lean_unbox_usize(v_stop_1037_);
lean_dec(v_stop_1037_);
v_res_1041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__18(v_as_1035_, v_i_boxed_1039_, v_stop_boxed_1040_, v_b_1038_);
lean_dec_ref(v_as_1035_);
return v_res_1041_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg___lam__0(lean_object* v_x_1042_, lean_object* v_x_1043_){
_start:
{
lean_object* v_fst_1044_; lean_object* v_fst_1045_; lean_object* v_fst_1046_; lean_object* v_fst_1047_; uint8_t v___x_1048_; 
v_fst_1044_ = lean_ctor_get(v_x_1042_, 0);
v_fst_1045_ = lean_ctor_get(v_x_1043_, 0);
v_fst_1046_ = lean_ctor_get(v_fst_1044_, 0);
v_fst_1047_ = lean_ctor_get(v_fst_1045_, 0);
v___x_1048_ = lean_nat_dec_lt(v_fst_1046_, v_fst_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg___lam__0___boxed(lean_object* v_x_1049_, lean_object* v_x_1050_){
_start:
{
uint8_t v_res_1051_; lean_object* v_r_1052_; 
v_res_1051_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg___lam__0(v_x_1049_, v_x_1050_);
lean_dec_ref(v_x_1050_);
lean_dec_ref(v_x_1049_);
v_r_1052_ = lean_box(v_res_1051_);
return v_r_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg(lean_object* v_as_1054_, lean_object* v_lo_1055_, lean_object* v_hi_1056_){
_start:
{
uint8_t v___x_1057_; 
v___x_1057_ = lean_nat_dec_lt(v_lo_1055_, v_hi_1056_);
if (v___x_1057_ == 0)
{
lean_dec(v_lo_1055_);
return v_as_1054_;
}
else
{
lean_object* v___f_1058_; lean_object* v___x_1059_; lean_object* v_fst_1060_; lean_object* v_snd_1061_; uint8_t v___x_1062_; 
v___f_1058_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg___closed__0));
lean_inc(v_lo_1055_);
v___x_1059_ = l_Array_qpartition___redArg(v_as_1054_, v___f_1058_, v_lo_1055_, v_hi_1056_);
v_fst_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_fst_1060_);
v_snd_1061_ = lean_ctor_get(v___x_1059_, 1);
lean_inc(v_snd_1061_);
lean_dec_ref(v___x_1059_);
v___x_1062_ = lean_nat_dec_le(v_hi_1056_, v_fst_1060_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1063_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg(v_snd_1061_, v_lo_1055_, v_fst_1060_);
v___x_1064_ = lean_unsigned_to_nat(1u);
v___x_1065_ = lean_nat_add(v_fst_1060_, v___x_1064_);
lean_dec(v_fst_1060_);
v_as_1054_ = v___x_1063_;
v_lo_1055_ = v___x_1065_;
goto _start;
}
else
{
lean_dec(v_fst_1060_);
lean_dec(v_lo_1055_);
return v_snd_1061_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg___boxed(lean_object* v_as_1067_, lean_object* v_lo_1068_, lean_object* v_hi_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg(v_as_1067_, v_lo_1068_, v_hi_1069_);
lean_dec(v_hi_1069_);
return v_res_1070_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__15___redArg(lean_object* v_a_1071_, lean_object* v_x_1072_){
_start:
{
if (lean_obj_tag(v_x_1072_) == 0)
{
uint8_t v___x_1073_; 
v___x_1073_ = 0;
return v___x_1073_;
}
else
{
lean_object* v_key_1074_; lean_object* v_tail_1075_; uint8_t v___y_1077_; lean_object* v_fst_1079_; lean_object* v_snd_1080_; lean_object* v_fst_1081_; lean_object* v_snd_1082_; uint8_t v___x_1083_; 
v_key_1074_ = lean_ctor_get(v_x_1072_, 0);
v_tail_1075_ = lean_ctor_get(v_x_1072_, 2);
v_fst_1079_ = lean_ctor_get(v_key_1074_, 0);
v_snd_1080_ = lean_ctor_get(v_key_1074_, 1);
v_fst_1081_ = lean_ctor_get(v_a_1071_, 0);
v_snd_1082_ = lean_ctor_get(v_a_1071_, 1);
v___x_1083_ = lean_nat_dec_eq(v_fst_1079_, v_fst_1081_);
if (v___x_1083_ == 0)
{
v___y_1077_ = v___x_1083_;
goto v___jp_1076_;
}
else
{
uint8_t v___x_1084_; 
v___x_1084_ = lean_nat_dec_eq(v_snd_1080_, v_snd_1082_);
v___y_1077_ = v___x_1084_;
goto v___jp_1076_;
}
v___jp_1076_:
{
if (v___y_1077_ == 0)
{
v_x_1072_ = v_tail_1075_;
goto _start;
}
else
{
return v___y_1077_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__15___redArg___boxed(lean_object* v_a_1085_, lean_object* v_x_1086_){
_start:
{
uint8_t v_res_1087_; lean_object* v_r_1088_; 
v_res_1087_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__15___redArg(v_a_1085_, v_x_1086_);
lean_dec(v_x_1086_);
lean_dec_ref(v_a_1085_);
v_r_1088_ = lean_box(v_res_1087_);
return v_r_1088_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16_spec__28_spec__37___redArg(lean_object* v_x_1089_, lean_object* v_x_1090_){
_start:
{
if (lean_obj_tag(v_x_1090_) == 0)
{
return v_x_1089_;
}
else
{
lean_object* v_key_1091_; lean_object* v_value_1092_; lean_object* v_tail_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1120_; 
v_key_1091_ = lean_ctor_get(v_x_1090_, 0);
v_value_1092_ = lean_ctor_get(v_x_1090_, 1);
v_tail_1093_ = lean_ctor_get(v_x_1090_, 2);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_x_1090_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1095_ = v_x_1090_;
v_isShared_1096_ = v_isSharedCheck_1120_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_tail_1093_);
lean_inc(v_value_1092_);
lean_inc(v_key_1091_);
lean_dec(v_x_1090_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1120_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v_fst_1097_; lean_object* v_snd_1098_; lean_object* v___x_1099_; uint64_t v___x_1100_; uint64_t v___x_1101_; uint64_t v___x_1102_; uint64_t v___x_1103_; uint64_t v___x_1104_; uint64_t v_fold_1105_; uint64_t v___x_1106_; uint64_t v___x_1107_; uint64_t v___x_1108_; size_t v___x_1109_; size_t v___x_1110_; size_t v___x_1111_; size_t v___x_1112_; size_t v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1116_; 
v_fst_1097_ = lean_ctor_get(v_key_1091_, 0);
v_snd_1098_ = lean_ctor_get(v_key_1091_, 1);
v___x_1099_ = lean_array_get_size(v_x_1089_);
v___x_1100_ = l_String_instHashableRaw_hash(v_fst_1097_);
v___x_1101_ = l_String_instHashableRaw_hash(v_snd_1098_);
v___x_1102_ = lean_uint64_mix_hash(v___x_1100_, v___x_1101_);
v___x_1103_ = 32ULL;
v___x_1104_ = lean_uint64_shift_right(v___x_1102_, v___x_1103_);
v_fold_1105_ = lean_uint64_xor(v___x_1102_, v___x_1104_);
v___x_1106_ = 16ULL;
v___x_1107_ = lean_uint64_shift_right(v_fold_1105_, v___x_1106_);
v___x_1108_ = lean_uint64_xor(v_fold_1105_, v___x_1107_);
v___x_1109_ = lean_uint64_to_usize(v___x_1108_);
v___x_1110_ = lean_usize_of_nat(v___x_1099_);
v___x_1111_ = ((size_t)1ULL);
v___x_1112_ = lean_usize_sub(v___x_1110_, v___x_1111_);
v___x_1113_ = lean_usize_land(v___x_1109_, v___x_1112_);
v___x_1114_ = lean_array_uget_borrowed(v_x_1089_, v___x_1113_);
lean_inc(v___x_1114_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 2, v___x_1114_);
v___x_1116_ = v___x_1095_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_key_1091_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_value_1092_);
lean_ctor_set(v_reuseFailAlloc_1119_, 2, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_array_uset(v_x_1089_, v___x_1113_, v___x_1116_);
v_x_1089_ = v___x_1117_;
v_x_1090_ = v_tail_1093_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16_spec__28___redArg(lean_object* v_i_1121_, lean_object* v_source_1122_, lean_object* v_target_1123_){
_start:
{
lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1124_ = lean_array_get_size(v_source_1122_);
v___x_1125_ = lean_nat_dec_lt(v_i_1121_, v___x_1124_);
if (v___x_1125_ == 0)
{
lean_dec_ref(v_source_1122_);
lean_dec(v_i_1121_);
return v_target_1123_;
}
else
{
lean_object* v_es_1126_; lean_object* v___x_1127_; lean_object* v_source_1128_; lean_object* v_target_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v_es_1126_ = lean_array_fget(v_source_1122_, v_i_1121_);
v___x_1127_ = lean_box(0);
v_source_1128_ = lean_array_fset(v_source_1122_, v_i_1121_, v___x_1127_);
v_target_1129_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16_spec__28_spec__37___redArg(v_target_1123_, v_es_1126_);
v___x_1130_ = lean_unsigned_to_nat(1u);
v___x_1131_ = lean_nat_add(v_i_1121_, v___x_1130_);
lean_dec(v_i_1121_);
v_i_1121_ = v___x_1131_;
v_source_1122_ = v_source_1128_;
v_target_1123_ = v_target_1129_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16___redArg(lean_object* v_data_1133_){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v_nbuckets_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1134_ = lean_array_get_size(v_data_1133_);
v___x_1135_ = lean_unsigned_to_nat(2u);
v_nbuckets_1136_ = lean_nat_mul(v___x_1134_, v___x_1135_);
v___x_1137_ = lean_unsigned_to_nat(0u);
v___x_1138_ = lean_box(0);
v___x_1139_ = lean_mk_array(v_nbuckets_1136_, v___x_1138_);
v___x_1140_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16_spec__28___redArg(v___x_1137_, v_data_1133_, v___x_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__17___redArg(lean_object* v_a_1141_, lean_object* v_b_1142_, lean_object* v_x_1143_){
_start:
{
if (lean_obj_tag(v_x_1143_) == 0)
{
lean_dec(v_b_1142_);
lean_dec_ref(v_a_1141_);
return v_x_1143_;
}
else
{
lean_object* v_key_1144_; lean_object* v_value_1145_; lean_object* v_tail_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1165_; 
v_key_1144_ = lean_ctor_get(v_x_1143_, 0);
v_value_1145_ = lean_ctor_get(v_x_1143_, 1);
v_tail_1146_ = lean_ctor_get(v_x_1143_, 2);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_x_1143_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1148_ = v_x_1143_;
v_isShared_1149_ = v_isSharedCheck_1165_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_tail_1146_);
lean_inc(v_value_1145_);
lean_inc(v_key_1144_);
lean_dec(v_x_1143_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1165_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
uint8_t v___y_1151_; lean_object* v_fst_1159_; lean_object* v_snd_1160_; lean_object* v_fst_1161_; lean_object* v_snd_1162_; uint8_t v___x_1163_; 
v_fst_1159_ = lean_ctor_get(v_key_1144_, 0);
v_snd_1160_ = lean_ctor_get(v_key_1144_, 1);
v_fst_1161_ = lean_ctor_get(v_a_1141_, 0);
v_snd_1162_ = lean_ctor_get(v_a_1141_, 1);
v___x_1163_ = lean_nat_dec_eq(v_fst_1159_, v_fst_1161_);
if (v___x_1163_ == 0)
{
v___y_1151_ = v___x_1163_;
goto v___jp_1150_;
}
else
{
uint8_t v___x_1164_; 
v___x_1164_ = lean_nat_dec_eq(v_snd_1160_, v_snd_1162_);
v___y_1151_ = v___x_1164_;
goto v___jp_1150_;
}
v___jp_1150_:
{
if (v___y_1151_ == 0)
{
lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1152_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__17___redArg(v_a_1141_, v_b_1142_, v_tail_1146_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 2, v___x_1152_);
v___x_1154_ = v___x_1148_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_key_1144_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_value_1145_);
lean_ctor_set(v_reuseFailAlloc_1155_, 2, v___x_1152_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
else
{
lean_object* v___x_1157_; 
lean_dec(v_value_1145_);
lean_dec(v_key_1144_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 1, v_b_1142_);
lean_ctor_set(v___x_1148_, 0, v_a_1141_);
v___x_1157_ = v___x_1148_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1141_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_b_1142_);
lean_ctor_set(v_reuseFailAlloc_1158_, 2, v_tail_1146_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13___redArg(lean_object* v_m_1166_, lean_object* v_a_1167_, lean_object* v_b_1168_){
_start:
{
lean_object* v_size_1169_; lean_object* v_buckets_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1217_; 
v_size_1169_ = lean_ctor_get(v_m_1166_, 0);
v_buckets_1170_ = lean_ctor_get(v_m_1166_, 1);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_m_1166_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1172_ = v_m_1166_;
v_isShared_1173_ = v_isSharedCheck_1217_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_buckets_1170_);
lean_inc(v_size_1169_);
lean_dec(v_m_1166_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1217_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v_fst_1174_; lean_object* v_snd_1175_; lean_object* v___x_1176_; uint64_t v___x_1177_; uint64_t v___x_1178_; uint64_t v___x_1179_; uint64_t v___x_1180_; uint64_t v___x_1181_; uint64_t v_fold_1182_; uint64_t v___x_1183_; uint64_t v___x_1184_; uint64_t v___x_1185_; size_t v___x_1186_; size_t v___x_1187_; size_t v___x_1188_; size_t v___x_1189_; size_t v___x_1190_; lean_object* v_bkt_1191_; uint8_t v___x_1192_; 
v_fst_1174_ = lean_ctor_get(v_a_1167_, 0);
v_snd_1175_ = lean_ctor_get(v_a_1167_, 1);
v___x_1176_ = lean_array_get_size(v_buckets_1170_);
v___x_1177_ = l_String_instHashableRaw_hash(v_fst_1174_);
v___x_1178_ = l_String_instHashableRaw_hash(v_snd_1175_);
v___x_1179_ = lean_uint64_mix_hash(v___x_1177_, v___x_1178_);
v___x_1180_ = 32ULL;
v___x_1181_ = lean_uint64_shift_right(v___x_1179_, v___x_1180_);
v_fold_1182_ = lean_uint64_xor(v___x_1179_, v___x_1181_);
v___x_1183_ = 16ULL;
v___x_1184_ = lean_uint64_shift_right(v_fold_1182_, v___x_1183_);
v___x_1185_ = lean_uint64_xor(v_fold_1182_, v___x_1184_);
v___x_1186_ = lean_uint64_to_usize(v___x_1185_);
v___x_1187_ = lean_usize_of_nat(v___x_1176_);
v___x_1188_ = ((size_t)1ULL);
v___x_1189_ = lean_usize_sub(v___x_1187_, v___x_1188_);
v___x_1190_ = lean_usize_land(v___x_1186_, v___x_1189_);
v_bkt_1191_ = lean_array_uget_borrowed(v_buckets_1170_, v___x_1190_);
v___x_1192_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__15___redArg(v_a_1167_, v_bkt_1191_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; lean_object* v_size_x27_1194_; lean_object* v___x_1195_; lean_object* v_buckets_x27_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
v___x_1193_ = lean_unsigned_to_nat(1u);
v_size_x27_1194_ = lean_nat_add(v_size_1169_, v___x_1193_);
lean_dec(v_size_1169_);
lean_inc(v_bkt_1191_);
v___x_1195_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1195_, 0, v_a_1167_);
lean_ctor_set(v___x_1195_, 1, v_b_1168_);
lean_ctor_set(v___x_1195_, 2, v_bkt_1191_);
v_buckets_x27_1196_ = lean_array_uset(v_buckets_1170_, v___x_1190_, v___x_1195_);
v___x_1197_ = lean_unsigned_to_nat(4u);
v___x_1198_ = lean_nat_mul(v_size_x27_1194_, v___x_1197_);
v___x_1199_ = lean_unsigned_to_nat(3u);
v___x_1200_ = lean_nat_div(v___x_1198_, v___x_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_array_get_size(v_buckets_x27_1196_);
v___x_1202_ = lean_nat_dec_le(v___x_1200_, v___x_1201_);
lean_dec(v___x_1200_);
if (v___x_1202_ == 0)
{
lean_object* v_val_1203_; lean_object* v___x_1205_; 
v_val_1203_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16___redArg(v_buckets_x27_1196_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 1, v_val_1203_);
lean_ctor_set(v___x_1172_, 0, v_size_x27_1194_);
v___x_1205_ = v___x_1172_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_size_x27_1194_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_val_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
else
{
lean_object* v___x_1208_; 
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 1, v_buckets_x27_1196_);
lean_ctor_set(v___x_1172_, 0, v_size_x27_1194_);
v___x_1208_ = v___x_1172_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_size_x27_1194_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_buckets_x27_1196_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
else
{
lean_object* v___x_1210_; lean_object* v_buckets_x27_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1215_; 
lean_inc(v_bkt_1191_);
v___x_1210_ = lean_box(0);
v_buckets_x27_1211_ = lean_array_uset(v_buckets_1170_, v___x_1190_, v___x_1210_);
v___x_1212_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__17___redArg(v_a_1167_, v_b_1168_, v_bkt_1191_);
v___x_1213_ = lean_array_uset(v_buckets_x27_1211_, v___x_1190_, v___x_1212_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 1, v___x_1213_);
v___x_1215_ = v___x_1172_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_size_1169_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v___x_1213_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12_spec__13___redArg(lean_object* v_a_1218_, lean_object* v_fallback_1219_, lean_object* v_x_1220_){
_start:
{
if (lean_obj_tag(v_x_1220_) == 0)
{
lean_inc(v_fallback_1219_);
return v_fallback_1219_;
}
else
{
lean_object* v_key_1221_; lean_object* v_value_1222_; lean_object* v_tail_1223_; uint8_t v___y_1225_; lean_object* v_fst_1227_; lean_object* v_snd_1228_; lean_object* v_fst_1229_; lean_object* v_snd_1230_; uint8_t v___x_1231_; 
v_key_1221_ = lean_ctor_get(v_x_1220_, 0);
v_value_1222_ = lean_ctor_get(v_x_1220_, 1);
v_tail_1223_ = lean_ctor_get(v_x_1220_, 2);
v_fst_1227_ = lean_ctor_get(v_key_1221_, 0);
v_snd_1228_ = lean_ctor_get(v_key_1221_, 1);
v_fst_1229_ = lean_ctor_get(v_a_1218_, 0);
v_snd_1230_ = lean_ctor_get(v_a_1218_, 1);
v___x_1231_ = lean_nat_dec_eq(v_fst_1227_, v_fst_1229_);
if (v___x_1231_ == 0)
{
v___y_1225_ = v___x_1231_;
goto v___jp_1224_;
}
else
{
uint8_t v___x_1232_; 
v___x_1232_ = lean_nat_dec_eq(v_snd_1228_, v_snd_1230_);
v___y_1225_ = v___x_1232_;
goto v___jp_1224_;
}
v___jp_1224_:
{
if (v___y_1225_ == 0)
{
v_x_1220_ = v_tail_1223_;
goto _start;
}
else
{
lean_inc(v_value_1222_);
return v_value_1222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12_spec__13___redArg___boxed(lean_object* v_a_1233_, lean_object* v_fallback_1234_, lean_object* v_x_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12_spec__13___redArg(v_a_1233_, v_fallback_1234_, v_x_1235_);
lean_dec(v_x_1235_);
lean_dec(v_fallback_1234_);
lean_dec_ref(v_a_1233_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12___redArg(lean_object* v_m_1237_, lean_object* v_a_1238_, lean_object* v_fallback_1239_){
_start:
{
lean_object* v_buckets_1240_; lean_object* v_fst_1241_; lean_object* v_snd_1242_; lean_object* v___x_1243_; uint64_t v___x_1244_; uint64_t v___x_1245_; uint64_t v___x_1246_; uint64_t v___x_1247_; uint64_t v___x_1248_; uint64_t v_fold_1249_; uint64_t v___x_1250_; uint64_t v___x_1251_; uint64_t v___x_1252_; size_t v___x_1253_; size_t v___x_1254_; size_t v___x_1255_; size_t v___x_1256_; size_t v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v_buckets_1240_ = lean_ctor_get(v_m_1237_, 1);
v_fst_1241_ = lean_ctor_get(v_a_1238_, 0);
v_snd_1242_ = lean_ctor_get(v_a_1238_, 1);
v___x_1243_ = lean_array_get_size(v_buckets_1240_);
v___x_1244_ = l_String_instHashableRaw_hash(v_fst_1241_);
v___x_1245_ = l_String_instHashableRaw_hash(v_snd_1242_);
v___x_1246_ = lean_uint64_mix_hash(v___x_1244_, v___x_1245_);
v___x_1247_ = 32ULL;
v___x_1248_ = lean_uint64_shift_right(v___x_1246_, v___x_1247_);
v_fold_1249_ = lean_uint64_xor(v___x_1246_, v___x_1248_);
v___x_1250_ = 16ULL;
v___x_1251_ = lean_uint64_shift_right(v_fold_1249_, v___x_1250_);
v___x_1252_ = lean_uint64_xor(v_fold_1249_, v___x_1251_);
v___x_1253_ = lean_uint64_to_usize(v___x_1252_);
v___x_1254_ = lean_usize_of_nat(v___x_1243_);
v___x_1255_ = ((size_t)1ULL);
v___x_1256_ = lean_usize_sub(v___x_1254_, v___x_1255_);
v___x_1257_ = lean_usize_land(v___x_1253_, v___x_1256_);
v___x_1258_ = lean_array_uget_borrowed(v_buckets_1240_, v___x_1257_);
v___x_1259_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12_spec__13___redArg(v_a_1238_, v_fallback_1239_, v___x_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12___redArg___boxed(lean_object* v_m_1260_, lean_object* v_a_1261_, lean_object* v_fallback_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12___redArg(v_m_1260_, v_a_1261_, v_fallback_1262_);
lean_dec(v_fallback_1262_);
lean_dec_ref(v_a_1261_);
lean_dec_ref(v_m_1260_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42___redArg(uint8_t v___x_1266_, lean_object* v_as_1267_, size_t v_sz_1268_, size_t v_i_1269_, lean_object* v_b_1270_, lean_object* v___y_1271_){
_start:
{
uint8_t v___x_1273_; 
v___x_1273_ = lean_usize_dec_lt(v_i_1269_, v_sz_1268_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; 
v___x_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1274_, 0, v_b_1270_);
return v___x_1274_;
}
else
{
lean_object* v_snd_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1312_; 
v_snd_1275_ = lean_ctor_get(v_b_1270_, 1);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_b_1270_);
if (v_isSharedCheck_1312_ == 0)
{
lean_object* v_unused_1313_; 
v_unused_1313_ = lean_ctor_get(v_b_1270_, 0);
lean_dec(v_unused_1313_);
v___x_1277_ = v_b_1270_;
v_isShared_1278_ = v_isSharedCheck_1312_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_snd_1275_);
lean_dec(v_b_1270_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1312_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v_ref_1279_; lean_object* v_a_1280_; lean_object* v_ref_1281_; lean_object* v_msg_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1311_; 
v_ref_1279_ = lean_ctor_get(v___y_1271_, 5);
v_a_1280_ = lean_array_uget(v_as_1267_, v_i_1269_);
v_ref_1281_ = lean_ctor_get(v_a_1280_, 0);
v_msg_1282_ = lean_ctor_get(v_a_1280_, 1);
v_isSharedCheck_1311_ = !lean_is_exclusive(v_a_1280_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1284_ = v_a_1280_;
v_isShared_1285_ = v_isSharedCheck_1311_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_msg_1282_);
lean_inc(v_ref_1281_);
lean_dec(v_a_1280_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1311_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1286_; lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v_ref_1303_; lean_object* v___y_1305_; lean_object* v___x_1308_; 
v___x_1286_ = lean_box(0);
v_ref_1303_ = l_Lean_replaceRef(v_ref_1281_, v_ref_1279_);
lean_dec(v_ref_1281_);
v___x_1308_ = l_Lean_Syntax_getPos_x3f(v_ref_1303_, v___x_1266_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v___x_1309_; 
v___x_1309_ = lean_unsigned_to_nat(0u);
v___y_1305_ = v___x_1309_;
goto v___jp_1304_;
}
else
{
lean_object* v_val_1310_; 
v_val_1310_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_val_1310_);
lean_dec_ref(v___x_1308_);
v___y_1305_ = v_val_1310_;
goto v___jp_1304_;
}
v___jp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 1, v___y_1289_);
lean_ctor_set(v___x_1277_, 0, v___y_1288_);
v___x_1291_ = v___x_1277_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___y_1288_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v___y_1289_);
v___x_1291_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v_pos2traces_1295_; lean_object* v___x_1297_; 
v___x_1292_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42___redArg___closed__0));
v___x_1293_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12___redArg(v_snd_1275_, v___x_1291_, v___x_1292_);
v___x_1294_ = lean_array_push(v___x_1293_, v_msg_1282_);
v_pos2traces_1295_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13___redArg(v_snd_1275_, v___x_1291_, v___x_1294_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 1, v_pos2traces_1295_);
lean_ctor_set(v___x_1284_, 0, v___x_1286_);
v___x_1297_ = v___x_1284_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v_pos2traces_1295_);
v___x_1297_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
size_t v___x_1298_; size_t v___x_1299_; 
v___x_1298_ = ((size_t)1ULL);
v___x_1299_ = lean_usize_add(v_i_1269_, v___x_1298_);
v_i_1269_ = v___x_1299_;
v_b_1270_ = v___x_1297_;
goto _start;
}
}
}
v___jp_1304_:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1303_, v___x_1266_);
lean_dec(v_ref_1303_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_inc(v___y_1305_);
v___y_1288_ = v___y_1305_;
v___y_1289_ = v___y_1305_;
goto v___jp_1287_;
}
else
{
lean_object* v_val_1307_; 
v_val_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_val_1307_);
lean_dec_ref(v___x_1306_);
v___y_1288_ = v___y_1305_;
v___y_1289_ = v_val_1307_;
goto v___jp_1287_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42___redArg___boxed(lean_object* v___x_1314_, lean_object* v_as_1315_, lean_object* v_sz_1316_, lean_object* v_i_1317_, lean_object* v_b_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
uint8_t v___x_37215__boxed_1321_; size_t v_sz_boxed_1322_; size_t v_i_boxed_1323_; lean_object* v_res_1324_; 
v___x_37215__boxed_1321_ = lean_unbox(v___x_1314_);
v_sz_boxed_1322_ = lean_unbox_usize(v_sz_1316_);
lean_dec(v_sz_1316_);
v_i_boxed_1323_ = lean_unbox_usize(v_i_1317_);
lean_dec(v_i_1317_);
v_res_1324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42___redArg(v___x_37215__boxed_1321_, v_as_1315_, v_sz_boxed_1322_, v_i_boxed_1323_, v_b_1318_, v___y_1319_);
lean_dec_ref(v___y_1319_);
lean_dec_ref(v_as_1315_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33(uint8_t v___x_1325_, lean_object* v_as_1326_, size_t v_sz_1327_, size_t v_i_1328_, lean_object* v_b_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
uint8_t v___x_1333_; 
v___x_1333_ = lean_usize_dec_lt(v_i_1328_, v_sz_1327_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; 
v___x_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1334_, 0, v_b_1329_);
return v___x_1334_;
}
else
{
lean_object* v_snd_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1372_; 
v_snd_1335_ = lean_ctor_get(v_b_1329_, 1);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_b_1329_);
if (v_isSharedCheck_1372_ == 0)
{
lean_object* v_unused_1373_; 
v_unused_1373_ = lean_ctor_get(v_b_1329_, 0);
lean_dec(v_unused_1373_);
v___x_1337_ = v_b_1329_;
v_isShared_1338_ = v_isSharedCheck_1372_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_snd_1335_);
lean_dec(v_b_1329_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1372_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v_ref_1339_; lean_object* v_a_1340_; lean_object* v_ref_1341_; lean_object* v_msg_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1371_; 
v_ref_1339_ = lean_ctor_get(v___y_1330_, 5);
v_a_1340_ = lean_array_uget(v_as_1326_, v_i_1328_);
v_ref_1341_ = lean_ctor_get(v_a_1340_, 0);
v_msg_1342_ = lean_ctor_get(v_a_1340_, 1);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_a_1340_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1344_ = v_a_1340_;
v_isShared_1345_ = v_isSharedCheck_1371_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_msg_1342_);
lean_inc(v_ref_1341_);
lean_dec(v_a_1340_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1371_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v_ref_1363_; lean_object* v___y_1365_; lean_object* v___x_1368_; 
v___x_1346_ = lean_box(0);
v_ref_1363_ = l_Lean_replaceRef(v_ref_1341_, v_ref_1339_);
lean_dec(v_ref_1341_);
v___x_1368_ = l_Lean_Syntax_getPos_x3f(v_ref_1363_, v___x_1325_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v___x_1369_; 
v___x_1369_ = lean_unsigned_to_nat(0u);
v___y_1365_ = v___x_1369_;
goto v___jp_1364_;
}
else
{
lean_object* v_val_1370_; 
v_val_1370_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_val_1370_);
lean_dec_ref(v___x_1368_);
v___y_1365_ = v_val_1370_;
goto v___jp_1364_;
}
v___jp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 1, v___y_1349_);
lean_ctor_set(v___x_1337_, 0, v___y_1348_);
v___x_1351_ = v___x_1337_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___y_1348_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v___y_1349_);
v___x_1351_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v_pos2traces_1355_; lean_object* v___x_1357_; 
v___x_1352_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42___redArg___closed__0));
v___x_1353_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12___redArg(v_snd_1335_, v___x_1351_, v___x_1352_);
v___x_1354_ = lean_array_push(v___x_1353_, v_msg_1342_);
v_pos2traces_1355_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13___redArg(v_snd_1335_, v___x_1351_, v___x_1354_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 1, v_pos2traces_1355_);
lean_ctor_set(v___x_1344_, 0, v___x_1346_);
v___x_1357_ = v___x_1344_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_pos2traces_1355_);
v___x_1357_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
size_t v___x_1358_; size_t v___x_1359_; lean_object* v___x_1360_; 
v___x_1358_ = ((size_t)1ULL);
v___x_1359_ = lean_usize_add(v_i_1328_, v___x_1358_);
v___x_1360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42___redArg(v___x_1325_, v_as_1326_, v_sz_1327_, v___x_1359_, v___x_1357_, v___y_1330_);
return v___x_1360_;
}
}
}
v___jp_1364_:
{
lean_object* v___x_1366_; 
v___x_1366_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1363_, v___x_1325_);
lean_dec(v_ref_1363_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_inc(v___y_1365_);
v___y_1348_ = v___y_1365_;
v___y_1349_ = v___y_1365_;
goto v___jp_1347_;
}
else
{
lean_object* v_val_1367_; 
v_val_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_val_1367_);
lean_dec_ref(v___x_1366_);
v___y_1348_ = v___y_1365_;
v___y_1349_ = v_val_1367_;
goto v___jp_1347_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33___boxed(lean_object* v___x_1374_, lean_object* v_as_1375_, lean_object* v_sz_1376_, lean_object* v_i_1377_, lean_object* v_b_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
uint8_t v___x_37296__boxed_1382_; size_t v_sz_boxed_1383_; size_t v_i_boxed_1384_; lean_object* v_res_1385_; 
v___x_37296__boxed_1382_ = lean_unbox(v___x_1374_);
v_sz_boxed_1383_ = lean_unbox_usize(v_sz_1376_);
lean_dec(v_sz_1376_);
v_i_boxed_1384_ = lean_unbox_usize(v_i_1377_);
lean_dec(v_i_1377_);
v_res_1385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33(v___x_37296__boxed_1382_, v_as_1375_, v_sz_boxed_1383_, v_i_boxed_1384_, v_b_1378_, v___y_1379_, v___y_1380_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec_ref(v_as_1375_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19(uint8_t v___x_1386_, lean_object* v_inh_1387_, lean_object* v_n_1388_, lean_object* v_b_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
if (lean_obj_tag(v_n_1388_) == 0)
{
lean_object* v_cs_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1427_; 
v_cs_1393_ = lean_ctor_get(v_n_1388_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_n_1388_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1395_ = v_n_1388_;
v_isShared_1396_ = v_isSharedCheck_1427_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_cs_1393_);
lean_dec(v_n_1388_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1427_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; size_t v_sz_1399_; size_t v___x_1400_; lean_object* v___x_1401_; 
v___x_1397_ = lean_box(0);
v___x_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
lean_ctor_set(v___x_1398_, 1, v_b_1389_);
v_sz_1399_ = lean_array_size(v_cs_1393_);
v___x_1400_ = ((size_t)0ULL);
v___x_1401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__32(v___x_1386_, v_inh_1387_, v_cs_1393_, v_sz_1399_, v___x_1400_, v___x_1398_, v___y_1390_, v___y_1391_);
lean_dec_ref(v_cs_1393_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1418_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1404_ = v___x_1401_;
v_isShared_1405_ = v_isSharedCheck_1418_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1418_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v_fst_1406_; 
v_fst_1406_ = lean_ctor_get(v_a_1402_, 0);
if (lean_obj_tag(v_fst_1406_) == 0)
{
lean_object* v_snd_1407_; lean_object* v___x_1409_; 
v_snd_1407_ = lean_ctor_get(v_a_1402_, 1);
lean_inc(v_snd_1407_);
lean_dec(v_a_1402_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set_tag(v___x_1395_, 1);
lean_ctor_set(v___x_1395_, 0, v_snd_1407_);
v___x_1409_ = v___x_1395_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_snd_1407_);
v___x_1409_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1411_; 
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1409_);
v___x_1411_ = v___x_1404_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1409_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
else
{
lean_object* v_val_1414_; lean_object* v___x_1416_; 
lean_inc_ref(v_fst_1406_);
lean_dec(v_a_1402_);
lean_del_object(v___x_1395_);
v_val_1414_ = lean_ctor_get(v_fst_1406_, 0);
lean_inc(v_val_1414_);
lean_dec_ref(v_fst_1406_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v_val_1414_);
v___x_1416_ = v___x_1404_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_val_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_del_object(v___x_1395_);
v_a_1419_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1401_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1401_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
}
else
{
lean_object* v_vs_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1462_; 
v_vs_1428_ = lean_ctor_get(v_n_1388_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_n_1388_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1430_ = v_n_1388_;
v_isShared_1431_ = v_isSharedCheck_1462_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_vs_1428_);
lean_dec(v_n_1388_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1462_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; size_t v_sz_1434_; size_t v___x_1435_; lean_object* v___x_1436_; 
v___x_1432_ = lean_box(0);
v___x_1433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
lean_ctor_set(v___x_1433_, 1, v_b_1389_);
v_sz_1434_ = lean_array_size(v_vs_1428_);
v___x_1435_ = ((size_t)0ULL);
v___x_1436_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33(v___x_1386_, v_vs_1428_, v_sz_1434_, v___x_1435_, v___x_1433_, v___y_1390_, v___y_1391_);
lean_dec_ref(v_vs_1428_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1453_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1453_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1453_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v_fst_1441_; 
v_fst_1441_ = lean_ctor_get(v_a_1437_, 0);
if (lean_obj_tag(v_fst_1441_) == 0)
{
lean_object* v_snd_1442_; lean_object* v___x_1444_; 
v_snd_1442_ = lean_ctor_get(v_a_1437_, 1);
lean_inc(v_snd_1442_);
lean_dec(v_a_1437_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v_snd_1442_);
v___x_1444_ = v___x_1430_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_snd_1442_);
v___x_1444_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1446_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v___x_1444_);
v___x_1446_ = v___x_1439_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
else
{
lean_object* v_val_1449_; lean_object* v___x_1451_; 
lean_inc_ref(v_fst_1441_);
lean_dec(v_a_1437_);
lean_del_object(v___x_1430_);
v_val_1449_ = lean_ctor_get(v_fst_1441_, 0);
lean_inc(v_val_1449_);
lean_dec_ref(v_fst_1441_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v_val_1449_);
v___x_1451_ = v___x_1439_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_val_1449_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_del_object(v___x_1430_);
v_a_1454_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1436_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1436_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__32(uint8_t v___x_1463_, lean_object* v_inh_1464_, lean_object* v_as_1465_, size_t v_sz_1466_, size_t v_i_1467_, lean_object* v_b_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
uint8_t v___x_1472_; 
v___x_1472_ = lean_usize_dec_lt(v_i_1467_, v_sz_1466_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; 
v___x_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1473_, 0, v_b_1468_);
return v___x_1473_;
}
else
{
lean_object* v_snd_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1508_; 
v_snd_1474_ = lean_ctor_get(v_b_1468_, 1);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_b_1468_);
if (v_isSharedCheck_1508_ == 0)
{
lean_object* v_unused_1509_; 
v_unused_1509_ = lean_ctor_get(v_b_1468_, 0);
lean_dec(v_unused_1509_);
v___x_1476_ = v_b_1468_;
v_isShared_1477_ = v_isSharedCheck_1508_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_snd_1474_);
lean_dec(v_b_1468_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1508_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v_a_1478_; lean_object* v___x_1479_; 
v_a_1478_ = lean_array_uget_borrowed(v_as_1465_, v_i_1467_);
lean_inc(v_snd_1474_);
lean_inc(v_a_1478_);
v___x_1479_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19(v___x_1463_, v_inh_1464_, v_a_1478_, v_snd_1474_, v___y_1469_, v___y_1470_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1499_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1482_ = v___x_1479_;
v_isShared_1483_ = v_isSharedCheck_1499_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1499_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
if (lean_obj_tag(v_a_1480_) == 0)
{
lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___x_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1484_, 0, v_a_1480_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 0, v___x_1484_);
v___x_1486_ = v___x_1476_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_snd_1474_);
v___x_1486_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v___x_1488_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 0, v___x_1486_);
v___x_1488_ = v___x_1482_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1486_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
else
{
lean_object* v_a_1491_; lean_object* v___x_1492_; lean_object* v___x_1494_; 
lean_del_object(v___x_1482_);
lean_dec(v_snd_1474_);
v_a_1491_ = lean_ctor_get(v_a_1480_, 0);
lean_inc(v_a_1491_);
lean_dec_ref(v_a_1480_);
v___x_1492_ = lean_box(0);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 1, v_a_1491_);
lean_ctor_set(v___x_1476_, 0, v___x_1492_);
v___x_1494_ = v___x_1476_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1492_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_a_1491_);
v___x_1494_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
size_t v___x_1495_; size_t v___x_1496_; 
v___x_1495_ = ((size_t)1ULL);
v___x_1496_ = lean_usize_add(v_i_1467_, v___x_1495_);
v_i_1467_ = v___x_1496_;
v_b_1468_ = v___x_1494_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_del_object(v___x_1476_);
lean_dec(v_snd_1474_);
v_a_1500_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1479_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1479_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__32___boxed(lean_object* v___x_1510_, lean_object* v_inh_1511_, lean_object* v_as_1512_, lean_object* v_sz_1513_, lean_object* v_i_1514_, lean_object* v_b_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
uint8_t v___x_37377__boxed_1519_; size_t v_sz_boxed_1520_; size_t v_i_boxed_1521_; lean_object* v_res_1522_; 
v___x_37377__boxed_1519_ = lean_unbox(v___x_1510_);
v_sz_boxed_1520_ = lean_unbox_usize(v_sz_1513_);
lean_dec(v_sz_1513_);
v_i_boxed_1521_ = lean_unbox_usize(v_i_1514_);
lean_dec(v_i_1514_);
v_res_1522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__32(v___x_37377__boxed_1519_, v_inh_1511_, v_as_1512_, v_sz_boxed_1520_, v_i_boxed_1521_, v_b_1515_, v___y_1516_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec_ref(v_as_1512_);
lean_dec_ref(v_inh_1511_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19___boxed(lean_object* v___x_1523_, lean_object* v_inh_1524_, lean_object* v_n_1525_, lean_object* v_b_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
uint8_t v___x_37397__boxed_1530_; lean_object* v_res_1531_; 
v___x_37397__boxed_1530_ = lean_unbox(v___x_1523_);
v_res_1531_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19(v___x_37397__boxed_1530_, v_inh_1524_, v_n_1525_, v_b_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec_ref(v_inh_1524_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20_spec__35___redArg(uint8_t v___x_1532_, lean_object* v_as_1533_, size_t v_sz_1534_, size_t v_i_1535_, lean_object* v_b_1536_, lean_object* v___y_1537_){
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
v_ref_1545_ = lean_ctor_get(v___y_1537_, 5);
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
lean_dec_ref(v___x_1574_);
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
v___x_1558_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42___redArg___closed__0));
v___x_1559_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12___redArg(v_snd_1541_, v___x_1557_, v___x_1558_);
v___x_1560_ = lean_array_push(v___x_1559_, v_msg_1548_);
v_pos2traces_1561_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13___redArg(v_snd_1541_, v___x_1557_, v___x_1560_);
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
lean_dec_ref(v___x_1572_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20_spec__35___redArg___boxed(lean_object* v___x_1580_, lean_object* v_as_1581_, lean_object* v_sz_1582_, lean_object* v_i_1583_, lean_object* v_b_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
uint8_t v___x_37604__boxed_1587_; size_t v_sz_boxed_1588_; size_t v_i_boxed_1589_; lean_object* v_res_1590_; 
v___x_37604__boxed_1587_ = lean_unbox(v___x_1580_);
v_sz_boxed_1588_ = lean_unbox_usize(v_sz_1582_);
lean_dec(v_sz_1582_);
v_i_boxed_1589_ = lean_unbox_usize(v_i_1583_);
lean_dec(v_i_1583_);
v_res_1590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20_spec__35___redArg(v___x_37604__boxed_1587_, v_as_1581_, v_sz_boxed_1588_, v_i_boxed_1589_, v_b_1584_, v___y_1585_);
lean_dec_ref(v___y_1585_);
lean_dec_ref(v_as_1581_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20(uint8_t v___x_1591_, lean_object* v_as_1592_, size_t v_sz_1593_, size_t v_i_1594_, lean_object* v_b_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
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
v_ref_1605_ = lean_ctor_get(v___y_1596_, 5);
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
lean_dec_ref(v___x_1634_);
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
v___x_1618_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42___redArg___closed__0));
v___x_1619_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12___redArg(v_snd_1601_, v___x_1617_, v___x_1618_);
v___x_1620_ = lean_array_push(v___x_1619_, v_msg_1608_);
v_pos2traces_1621_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13___redArg(v_snd_1601_, v___x_1617_, v___x_1620_);
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
v___x_1626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20_spec__35___redArg(v___x_1591_, v_as_1592_, v_sz_1593_, v___x_1625_, v___x_1623_, v___y_1596_);
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
lean_dec_ref(v___x_1632_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20___boxed(lean_object* v___x_1640_, lean_object* v_as_1641_, lean_object* v_sz_1642_, lean_object* v_i_1643_, lean_object* v_b_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
uint8_t v___x_37684__boxed_1648_; size_t v_sz_boxed_1649_; size_t v_i_boxed_1650_; lean_object* v_res_1651_; 
v___x_37684__boxed_1648_ = lean_unbox(v___x_1640_);
v_sz_boxed_1649_ = lean_unbox_usize(v_sz_1642_);
lean_dec(v_sz_1642_);
v_i_boxed_1650_ = lean_unbox_usize(v_i_1643_);
lean_dec(v_i_1643_);
v_res_1651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20(v___x_37684__boxed_1648_, v_as_1641_, v_sz_boxed_1649_, v_i_boxed_1650_, v_b_1644_, v___y_1645_, v___y_1646_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec_ref(v_as_1641_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14(uint8_t v___x_1652_, lean_object* v_t_1653_, lean_object* v_init_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v_root_1658_; lean_object* v_tail_1659_; lean_object* v___x_1660_; 
v_root_1658_ = lean_ctor_get(v_t_1653_, 0);
lean_inc_ref(v_root_1658_);
v_tail_1659_ = lean_ctor_get(v_t_1653_, 1);
lean_inc_ref(v_tail_1659_);
lean_dec_ref(v_t_1653_);
lean_inc_ref(v_init_1654_);
v___x_1660_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19(v___x_1652_, v_init_1654_, v_root_1658_, v_init_1654_, v___y_1655_, v___y_1656_);
lean_dec_ref(v_init_1654_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1697_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1663_ = v___x_1660_;
v_isShared_1664_ = v_isSharedCheck_1697_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1660_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1697_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
if (lean_obj_tag(v_a_1661_) == 0)
{
lean_object* v_a_1665_; lean_object* v___x_1667_; 
lean_dec_ref(v_tail_1659_);
v_a_1665_ = lean_ctor_get(v_a_1661_, 0);
lean_inc(v_a_1665_);
lean_dec_ref(v_a_1661_);
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 0, v_a_1665_);
v___x_1667_ = v___x_1663_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1665_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; size_t v_sz_1672_; size_t v___x_1673_; lean_object* v___x_1674_; 
lean_del_object(v___x_1663_);
v_a_1669_ = lean_ctor_get(v_a_1661_, 0);
lean_inc(v_a_1669_);
lean_dec_ref(v_a_1661_);
v___x_1670_ = lean_box(0);
v___x_1671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
lean_ctor_set(v___x_1671_, 1, v_a_1669_);
v_sz_1672_ = lean_array_size(v_tail_1659_);
v___x_1673_ = ((size_t)0ULL);
v___x_1674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20(v___x_1652_, v_tail_1659_, v_sz_1672_, v___x_1673_, v___x_1671_, v___y_1655_, v___y_1656_);
lean_dec_ref(v_tail_1659_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1688_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1677_ = v___x_1674_;
v_isShared_1678_ = v_isSharedCheck_1688_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1674_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1688_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v_fst_1679_; 
v_fst_1679_ = lean_ctor_get(v_a_1675_, 0);
if (lean_obj_tag(v_fst_1679_) == 0)
{
lean_object* v_snd_1680_; lean_object* v___x_1682_; 
v_snd_1680_ = lean_ctor_get(v_a_1675_, 1);
lean_inc(v_snd_1680_);
lean_dec(v_a_1675_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v_snd_1680_);
v___x_1682_ = v___x_1677_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_snd_1680_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
else
{
lean_object* v_val_1684_; lean_object* v___x_1686_; 
lean_inc_ref(v_fst_1679_);
lean_dec(v_a_1675_);
v_val_1684_ = lean_ctor_get(v_fst_1679_, 0);
lean_inc(v_val_1684_);
lean_dec_ref(v_fst_1679_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v_val_1684_);
v___x_1686_ = v___x_1677_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_val_1684_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
v_a_1689_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1674_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1674_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
lean_dec_ref(v_tail_1659_);
v_a_1698_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1660_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1660_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14___boxed(lean_object* v___x_1706_, lean_object* v_t_1707_, lean_object* v_init_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
uint8_t v___x_37765__boxed_1712_; lean_object* v_res_1713_; 
v___x_37765__boxed_1712_ = lean_unbox(v___x_1706_);
v_res_1713_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14(v___x_37765__boxed_1712_, v_t_1707_, v_init_1708_, v___y_1709_, v___y_1710_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
return v_res_1713_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0(uint8_t v___x_1721_, uint8_t v_suppressElabErrors_1722_, lean_object* v___x_1723_, lean_object* v_x_1724_){
_start:
{
if (lean_obj_tag(v_x_1724_) == 1)
{
lean_object* v_pre_1725_; 
v_pre_1725_ = lean_ctor_get(v_x_1724_, 0);
switch(lean_obj_tag(v_pre_1725_))
{
case 1:
{
lean_object* v_pre_1726_; 
v_pre_1726_ = lean_ctor_get(v_pre_1725_, 0);
switch(lean_obj_tag(v_pre_1726_))
{
case 0:
{
lean_object* v_str_1727_; lean_object* v_str_1728_; lean_object* v___x_1729_; uint8_t v___x_1730_; 
v_str_1727_ = lean_ctor_get(v_x_1724_, 1);
v_str_1728_ = lean_ctor_get(v_pre_1725_, 1);
v___x_1729_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__0));
v___x_1730_ = lean_string_dec_eq(v_str_1728_, v___x_1729_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1731_; uint8_t v___x_1732_; 
v___x_1731_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__1));
v___x_1732_ = lean_string_dec_eq(v_str_1728_, v___x_1731_);
if (v___x_1732_ == 0)
{
return v___x_1721_;
}
else
{
lean_object* v___x_1733_; uint8_t v___x_1734_; 
v___x_1733_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__2));
v___x_1734_ = lean_string_dec_eq(v_str_1727_, v___x_1733_);
if (v___x_1734_ == 0)
{
return v___x_1721_;
}
else
{
return v_suppressElabErrors_1722_;
}
}
}
else
{
lean_object* v___x_1735_; uint8_t v___x_1736_; 
v___x_1735_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__3));
v___x_1736_ = lean_string_dec_eq(v_str_1727_, v___x_1735_);
if (v___x_1736_ == 0)
{
return v___x_1721_;
}
else
{
return v_suppressElabErrors_1722_;
}
}
}
case 1:
{
lean_object* v_pre_1737_; 
v_pre_1737_ = lean_ctor_get(v_pre_1726_, 0);
if (lean_obj_tag(v_pre_1737_) == 0)
{
lean_object* v_str_1738_; lean_object* v_str_1739_; lean_object* v_str_1740_; lean_object* v___x_1741_; uint8_t v___x_1742_; 
v_str_1738_ = lean_ctor_get(v_x_1724_, 1);
v_str_1739_ = lean_ctor_get(v_pre_1725_, 1);
v_str_1740_ = lean_ctor_get(v_pre_1726_, 1);
v___x_1741_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__4));
v___x_1742_ = lean_string_dec_eq(v_str_1740_, v___x_1741_);
if (v___x_1742_ == 0)
{
return v___x_1721_;
}
else
{
lean_object* v___x_1743_; uint8_t v___x_1744_; 
v___x_1743_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__5));
v___x_1744_ = lean_string_dec_eq(v_str_1739_, v___x_1743_);
if (v___x_1744_ == 0)
{
return v___x_1721_;
}
else
{
lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1745_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__6));
v___x_1746_ = lean_string_dec_eq(v_str_1738_, v___x_1745_);
if (v___x_1746_ == 0)
{
return v___x_1721_;
}
else
{
return v_suppressElabErrors_1722_;
}
}
}
}
else
{
return v___x_1721_;
}
}
default: 
{
return v___x_1721_;
}
}
}
case 0:
{
lean_object* v_str_1747_; uint8_t v___x_1748_; 
v_str_1747_ = lean_ctor_get(v_x_1724_, 1);
v___x_1748_ = lean_string_dec_eq(v_str_1747_, v___x_1723_);
if (v___x_1748_ == 0)
{
return v___x_1721_;
}
else
{
return v_suppressElabErrors_1722_;
}
}
default: 
{
return v___x_1721_;
}
}
}
else
{
return v___x_1721_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___boxed(lean_object* v___x_1749_, lean_object* v_suppressElabErrors_1750_, lean_object* v___x_1751_, lean_object* v_x_1752_){
_start:
{
uint8_t v___x_37877__boxed_1753_; uint8_t v_suppressElabErrors_boxed_1754_; uint8_t v_res_1755_; lean_object* v_r_1756_; 
v___x_37877__boxed_1753_ = lean_unbox(v___x_1749_);
v_suppressElabErrors_boxed_1754_ = lean_unbox(v_suppressElabErrors_1750_);
v_res_1755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0(v___x_37877__boxed_1753_, v_suppressElabErrors_boxed_1754_, v___x_1751_, v_x_1752_);
lean_dec(v_x_1752_);
lean_dec_ref(v___x_1751_);
v_r_1756_ = lean_box(v_res_1755_);
return v_r_1756_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___closed__0(void){
_start:
{
lean_object* v___x_1757_; double v___x_1758_; 
v___x_1757_ = lean_unsigned_to_nat(0u);
v___x_1758_ = lean_float_of_nat(v___x_1757_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15(uint8_t v___x_1760_, lean_object* v_as_1761_, size_t v_sz_1762_, size_t v_i_1763_, lean_object* v_b_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v_a_1769_; uint8_t v___x_1773_; 
v___x_1773_ = lean_usize_dec_lt(v_i_1763_, v_sz_1762_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; 
lean_dec_ref(v___y_1765_);
v___x_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1774_, 0, v_b_1764_);
return v___x_1774_;
}
else
{
lean_object* v_a_1775_; lean_object* v_fst_1776_; lean_object* v_snd_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1853_; 
v_a_1775_ = lean_array_uget(v_as_1761_, v_i_1763_);
v_fst_1776_ = lean_ctor_get(v_a_1775_, 0);
v_snd_1777_ = lean_ctor_get(v_a_1775_, 1);
v_isSharedCheck_1853_ = !lean_is_exclusive(v_a_1775_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1779_ = v_a_1775_;
v_isShared_1780_ = v_isSharedCheck_1853_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_snd_1777_);
lean_inc(v_fst_1776_);
lean_dec(v_a_1775_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1853_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v_fst_1781_; lean_object* v_snd_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1852_; 
v_fst_1781_ = lean_ctor_get(v_fst_1776_, 0);
v_snd_1782_ = lean_ctor_get(v_fst_1776_, 1);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_fst_1776_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1784_ = v_fst_1776_;
v_isShared_1785_ = v_isSharedCheck_1852_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_snd_1782_);
lean_inc(v_fst_1781_);
lean_dec(v_fst_1776_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1852_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; double v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v_fileName_1791_; lean_object* v_fileMap_1792_; uint8_t v_suppressElabErrors_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1800_; 
v___x_1786_ = lean_box(0);
v___x_1787_ = lean_box(0);
v___x_1788_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___closed__0);
v___x_1789_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___closed__1));
v___x_1790_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1790_, 0, v___x_1786_);
lean_ctor_set(v___x_1790_, 1, v___x_1787_);
lean_ctor_set(v___x_1790_, 2, v___x_1789_);
lean_ctor_set_float(v___x_1790_, sizeof(void*)*3, v___x_1788_);
lean_ctor_set_float(v___x_1790_, sizeof(void*)*3 + 8, v___x_1788_);
lean_ctor_set_uint8(v___x_1790_, sizeof(void*)*3 + 16, v___x_1773_);
v_fileName_1791_ = lean_ctor_get(v___y_1765_, 0);
v_fileMap_1792_ = lean_ctor_get(v___y_1765_, 1);
v_suppressElabErrors_1793_ = lean_ctor_get_uint8(v___y_1765_, sizeof(void*)*14 + 1);
v___x_1794_ = lean_box(0);
v___x_1795_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__4_spec__4___closed__0));
v___x_1796_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__4_spec__4___closed__1));
v___x_1797_ = l_Lean_MessageData_nil;
v___x_1798_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1790_);
lean_ctor_set(v___x_1798_, 1, v___x_1797_);
lean_ctor_set(v___x_1798_, 2, v_snd_1777_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set_tag(v___x_1784_, 8);
lean_ctor_set(v___x_1784_, 1, v___x_1798_);
lean_ctor_set(v___x_1784_, 0, v___x_1796_);
v___x_1800_ = v___x_1784_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1796_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v___x_1798_);
v___x_1800_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
uint8_t v___x_1801_; lean_object* v___x_1802_; lean_object* v___y_1804_; lean_object* v___y_1805_; 
v___x_1801_ = 0;
lean_inc_ref(v_fileMap_1792_);
lean_inc_ref(v_fileName_1791_);
v___x_1802_ = l_Lean_Elab_mkMessageCore(v_fileName_1791_, v_fileMap_1792_, v___x_1800_, v___x_1801_, v_fst_1781_, v_snd_1782_);
lean_dec(v_snd_1782_);
lean_dec(v_fst_1781_);
if (v_suppressElabErrors_1793_ == 0)
{
lean_inc_ref(v___y_1765_);
v___y_1804_ = v___y_1765_;
v___y_1805_ = v___y_1766_;
goto v___jp_1803_;
}
else
{
lean_object* v_data_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___f_1849_; uint8_t v___x_1850_; 
v_data_1846_ = lean_ctor_get(v___x_1802_, 4);
lean_inc(v_data_1846_);
v___x_1847_ = lean_box(v___x_1760_);
v___x_1848_ = lean_box(v_suppressElabErrors_1793_);
v___f_1849_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1849_, 0, v___x_1847_);
lean_closure_set(v___f_1849_, 1, v___x_1848_);
lean_closure_set(v___f_1849_, 2, v___x_1795_);
v___x_1850_ = l_Lean_MessageData_hasTag(v___f_1849_, v_data_1846_);
if (v___x_1850_ == 0)
{
lean_dec_ref(v___x_1802_);
lean_del_object(v___x_1779_);
v_a_1769_ = v___x_1794_;
goto v___jp_1768_;
}
else
{
lean_inc_ref(v___y_1765_);
v___y_1804_ = v___y_1765_;
v___y_1805_ = v___y_1766_;
goto v___jp_1803_;
}
}
v___jp_1803_:
{
lean_object* v___x_1806_; lean_object* v_fileName_1807_; lean_object* v_pos_1808_; lean_object* v_endPos_1809_; uint8_t v_keepFullRange_1810_; uint8_t v_severity_1811_; uint8_t v_isSilent_1812_; lean_object* v_caption_1813_; lean_object* v_data_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1845_; 
v___x_1806_ = lean_st_ref_take(v___y_1805_);
v_fileName_1807_ = lean_ctor_get(v___x_1802_, 0);
v_pos_1808_ = lean_ctor_get(v___x_1802_, 1);
v_endPos_1809_ = lean_ctor_get(v___x_1802_, 2);
v_keepFullRange_1810_ = lean_ctor_get_uint8(v___x_1802_, sizeof(void*)*5);
v_severity_1811_ = lean_ctor_get_uint8(v___x_1802_, sizeof(void*)*5 + 1);
v_isSilent_1812_ = lean_ctor_get_uint8(v___x_1802_, sizeof(void*)*5 + 2);
v_caption_1813_ = lean_ctor_get(v___x_1802_, 3);
v_data_1814_ = lean_ctor_get(v___x_1802_, 4);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1816_ = v___x_1802_;
v_isShared_1817_ = v_isSharedCheck_1845_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_data_1814_);
lean_inc(v_caption_1813_);
lean_inc(v_endPos_1809_);
lean_inc(v_pos_1808_);
lean_inc(v_fileName_1807_);
lean_dec(v___x_1802_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1845_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v_currNamespace_1818_; lean_object* v_openDecls_1819_; lean_object* v_env_1820_; lean_object* v_nextMacroScope_1821_; lean_object* v_ngen_1822_; lean_object* v_auxDeclNGen_1823_; lean_object* v_traceState_1824_; lean_object* v_cache_1825_; lean_object* v_messages_1826_; lean_object* v_infoState_1827_; lean_object* v_snapshotTasks_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1844_; 
v_currNamespace_1818_ = lean_ctor_get(v___y_1804_, 6);
lean_inc(v_currNamespace_1818_);
v_openDecls_1819_ = lean_ctor_get(v___y_1804_, 7);
lean_inc(v_openDecls_1819_);
lean_dec_ref(v___y_1804_);
v_env_1820_ = lean_ctor_get(v___x_1806_, 0);
v_nextMacroScope_1821_ = lean_ctor_get(v___x_1806_, 1);
v_ngen_1822_ = lean_ctor_get(v___x_1806_, 2);
v_auxDeclNGen_1823_ = lean_ctor_get(v___x_1806_, 3);
v_traceState_1824_ = lean_ctor_get(v___x_1806_, 4);
v_cache_1825_ = lean_ctor_get(v___x_1806_, 5);
v_messages_1826_ = lean_ctor_get(v___x_1806_, 6);
v_infoState_1827_ = lean_ctor_get(v___x_1806_, 7);
v_snapshotTasks_1828_ = lean_ctor_get(v___x_1806_, 8);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1830_ = v___x_1806_;
v_isShared_1831_ = v_isSharedCheck_1844_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_snapshotTasks_1828_);
lean_inc(v_infoState_1827_);
lean_inc(v_messages_1826_);
lean_inc(v_cache_1825_);
lean_inc(v_traceState_1824_);
lean_inc(v_auxDeclNGen_1823_);
lean_inc(v_ngen_1822_);
lean_inc(v_nextMacroScope_1821_);
lean_inc(v_env_1820_);
lean_dec(v___x_1806_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1844_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 1, v_openDecls_1819_);
lean_ctor_set(v___x_1779_, 0, v_currNamespace_1818_);
v___x_1833_ = v___x_1779_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_currNamespace_1818_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_openDecls_1819_);
v___x_1833_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
lean_object* v___x_1834_; lean_object* v___x_1836_; 
v___x_1834_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
lean_ctor_set(v___x_1834_, 1, v_data_1814_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 4, v___x_1834_);
v___x_1836_ = v___x_1816_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_fileName_1807_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v_pos_1808_);
lean_ctor_set(v_reuseFailAlloc_1842_, 2, v_endPos_1809_);
lean_ctor_set(v_reuseFailAlloc_1842_, 3, v_caption_1813_);
lean_ctor_set(v_reuseFailAlloc_1842_, 4, v___x_1834_);
lean_ctor_set_uint8(v_reuseFailAlloc_1842_, sizeof(void*)*5, v_keepFullRange_1810_);
lean_ctor_set_uint8(v_reuseFailAlloc_1842_, sizeof(void*)*5 + 1, v_severity_1811_);
lean_ctor_set_uint8(v_reuseFailAlloc_1842_, sizeof(void*)*5 + 2, v_isSilent_1812_);
v___x_1836_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
lean_object* v___x_1837_; lean_object* v___x_1839_; 
v___x_1837_ = l_Lean_MessageLog_add(v___x_1836_, v_messages_1826_);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 6, v___x_1837_);
v___x_1839_ = v___x_1830_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_env_1820_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_nextMacroScope_1821_);
lean_ctor_set(v_reuseFailAlloc_1841_, 2, v_ngen_1822_);
lean_ctor_set(v_reuseFailAlloc_1841_, 3, v_auxDeclNGen_1823_);
lean_ctor_set(v_reuseFailAlloc_1841_, 4, v_traceState_1824_);
lean_ctor_set(v_reuseFailAlloc_1841_, 5, v_cache_1825_);
lean_ctor_set(v_reuseFailAlloc_1841_, 6, v___x_1837_);
lean_ctor_set(v_reuseFailAlloc_1841_, 7, v_infoState_1827_);
lean_ctor_set(v_reuseFailAlloc_1841_, 8, v_snapshotTasks_1828_);
v___x_1839_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
lean_object* v___x_1840_; 
v___x_1840_ = lean_st_ref_set(v___y_1805_, v___x_1839_);
v_a_1769_ = v___x_1794_;
goto v___jp_1768_;
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
v___jp_1768_:
{
size_t v___x_1770_; size_t v___x_1771_; 
v___x_1770_ = ((size_t)1ULL);
v___x_1771_ = lean_usize_add(v_i_1763_, v___x_1770_);
v_i_1763_ = v___x_1771_;
v_b_1764_ = v_a_1769_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___boxed(lean_object* v___x_1854_, lean_object* v_as_1855_, lean_object* v_sz_1856_, lean_object* v_i_1857_, lean_object* v_b_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
uint8_t v___x_37950__boxed_1862_; size_t v_sz_boxed_1863_; size_t v_i_boxed_1864_; lean_object* v_res_1865_; 
v___x_37950__boxed_1862_ = lean_unbox(v___x_1854_);
v_sz_boxed_1863_ = lean_unbox_usize(v_sz_1856_);
lean_dec(v_sz_1856_);
v_i_boxed_1864_ = lean_unbox_usize(v_i_1857_);
lean_dec(v_i_1857_);
v_res_1865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15(v___x_37950__boxed_1862_, v_as_1855_, v_sz_boxed_1863_, v_i_boxed_1864_, v_b_1858_, v___y_1859_, v___y_1860_);
lean_dec(v___y_1860_);
lean_dec_ref(v_as_1855_);
return v_res_1865_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1866_ = lean_unsigned_to_nat(32u);
v___x_1867_ = lean_mk_empty_array_with_capacity(v___x_1866_);
v___x_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1867_);
return v___x_1868_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1(void){
_start:
{
size_t v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1869_ = ((size_t)5ULL);
v___x_1870_ = lean_unsigned_to_nat(0u);
v___x_1871_ = lean_unsigned_to_nat(32u);
v___x_1872_ = lean_mk_empty_array_with_capacity(v___x_1871_);
v___x_1873_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__0);
v___x_1874_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
lean_ctor_set(v___x_1874_, 1, v___x_1872_);
lean_ctor_set(v___x_1874_, 2, v___x_1870_);
lean_ctor_set(v___x_1874_, 3, v___x_1870_);
lean_ctor_set_usize(v___x_1874_, 4, v___x_1869_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg(lean_object* v___y_1875_){
_start:
{
lean_object* v___x_1877_; lean_object* v_traceState_1878_; lean_object* v_traces_1879_; lean_object* v___x_1880_; lean_object* v_traceState_1881_; lean_object* v_env_1882_; lean_object* v_nextMacroScope_1883_; lean_object* v_ngen_1884_; lean_object* v_auxDeclNGen_1885_; lean_object* v_cache_1886_; lean_object* v_messages_1887_; lean_object* v_infoState_1888_; lean_object* v_snapshotTasks_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1908_; 
v___x_1877_ = lean_st_ref_get(v___y_1875_);
v_traceState_1878_ = lean_ctor_get(v___x_1877_, 4);
lean_inc_ref(v_traceState_1878_);
lean_dec(v___x_1877_);
v_traces_1879_ = lean_ctor_get(v_traceState_1878_, 0);
lean_inc_ref(v_traces_1879_);
lean_dec_ref(v_traceState_1878_);
v___x_1880_ = lean_st_ref_take(v___y_1875_);
v_traceState_1881_ = lean_ctor_get(v___x_1880_, 4);
v_env_1882_ = lean_ctor_get(v___x_1880_, 0);
v_nextMacroScope_1883_ = lean_ctor_get(v___x_1880_, 1);
v_ngen_1884_ = lean_ctor_get(v___x_1880_, 2);
v_auxDeclNGen_1885_ = lean_ctor_get(v___x_1880_, 3);
v_cache_1886_ = lean_ctor_get(v___x_1880_, 5);
v_messages_1887_ = lean_ctor_get(v___x_1880_, 6);
v_infoState_1888_ = lean_ctor_get(v___x_1880_, 7);
v_snapshotTasks_1889_ = lean_ctor_get(v___x_1880_, 8);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1891_ = v___x_1880_;
v_isShared_1892_ = v_isSharedCheck_1908_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_snapshotTasks_1889_);
lean_inc(v_infoState_1888_);
lean_inc(v_messages_1887_);
lean_inc(v_cache_1886_);
lean_inc(v_traceState_1881_);
lean_inc(v_auxDeclNGen_1885_);
lean_inc(v_ngen_1884_);
lean_inc(v_nextMacroScope_1883_);
lean_inc(v_env_1882_);
lean_dec(v___x_1880_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1908_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
uint64_t v_tid_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1906_; 
v_tid_1893_ = lean_ctor_get_uint64(v_traceState_1881_, sizeof(void*)*1);
v_isSharedCheck_1906_ = !lean_is_exclusive(v_traceState_1881_);
if (v_isSharedCheck_1906_ == 0)
{
lean_object* v_unused_1907_; 
v_unused_1907_ = lean_ctor_get(v_traceState_1881_, 0);
lean_dec(v_unused_1907_);
v___x_1895_ = v_traceState_1881_;
v_isShared_1896_ = v_isSharedCheck_1906_;
goto v_resetjp_1894_;
}
else
{
lean_dec(v_traceState_1881_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1906_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1897_; lean_object* v___x_1899_; 
v___x_1897_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 0, v___x_1897_);
v___x_1899_ = v___x_1895_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v___x_1897_);
lean_ctor_set_uint64(v_reuseFailAlloc_1905_, sizeof(void*)*1, v_tid_1893_);
v___x_1899_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
lean_object* v___x_1901_; 
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 4, v___x_1899_);
v___x_1901_ = v___x_1891_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_env_1882_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v_nextMacroScope_1883_);
lean_ctor_set(v_reuseFailAlloc_1904_, 2, v_ngen_1884_);
lean_ctor_set(v_reuseFailAlloc_1904_, 3, v_auxDeclNGen_1885_);
lean_ctor_set(v_reuseFailAlloc_1904_, 4, v___x_1899_);
lean_ctor_set(v_reuseFailAlloc_1904_, 5, v_cache_1886_);
lean_ctor_set(v_reuseFailAlloc_1904_, 6, v_messages_1887_);
lean_ctor_set(v_reuseFailAlloc_1904_, 7, v_infoState_1888_);
lean_ctor_set(v_reuseFailAlloc_1904_, 8, v_snapshotTasks_1889_);
v___x_1901_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1902_ = lean_st_ref_set(v___y_1875_, v___x_1901_);
v___x_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1903_, 0, v_traces_1879_);
return v___x_1903_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___boxed(lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg(v___y_1909_);
lean_dec(v___y_1909_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__10(lean_object* v_opts_1912_, lean_object* v_opt_1913_){
_start:
{
lean_object* v_name_1914_; lean_object* v_map_1915_; lean_object* v___x_1916_; 
v_name_1914_ = lean_ctor_get(v_opt_1913_, 0);
v_map_1915_ = lean_ctor_get(v_opts_1912_, 0);
v___x_1916_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1915_, v_name_1914_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v___x_1917_; 
v___x_1917_ = lean_box(0);
return v___x_1917_;
}
else
{
lean_object* v_val_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1927_; 
v_val_1918_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1920_ = v___x_1916_;
v_isShared_1921_ = v_isSharedCheck_1927_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_val_1918_);
lean_dec(v___x_1916_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1927_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
if (lean_obj_tag(v_val_1918_) == 0)
{
lean_object* v_v_1922_; lean_object* v___x_1924_; 
v_v_1922_ = lean_ctor_get(v_val_1918_, 0);
lean_inc_ref(v_v_1922_);
lean_dec_ref(v_val_1918_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v_v_1922_);
v___x_1924_ = v___x_1920_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_v_1922_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
else
{
lean_object* v___x_1926_; 
lean_del_object(v___x_1920_);
lean_dec(v_val_1918_);
v___x_1926_ = lean_box(0);
return v___x_1926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__10___boxed(lean_object* v_opts_1928_, lean_object* v_opt_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__10(v_opts_1928_, v_opt_1929_);
lean_dec_ref(v_opt_1929_);
lean_dec_ref(v_opts_1928_);
return v_res_1930_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__8___closed__0(void){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1931_ = lean_box(0);
v___x_1932_ = lean_unsigned_to_nat(16u);
v___x_1933_ = lean_mk_array(v___x_1932_, v___x_1931_);
return v___x_1933_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__8___closed__1(void){
_start:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v_pos2traces_1936_; 
v___x_1934_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__8___closed__0, &l_Lean_addTraceAsMessages___at___00main_spec__8___closed__0_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__8___closed__0);
v___x_1935_ = lean_unsigned_to_nat(0u);
v_pos2traces_1936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_1936_, 0, v___x_1935_);
lean_ctor_set(v_pos2traces_1936_, 1, v___x_1934_);
return v_pos2traces_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__8(lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v_options_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v_options_1940_ = lean_ctor_get(v___y_1937_, 2);
v___x_1941_ = l_Lean_trace_profiler_output;
v___x_1942_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__10(v_options_1940_, v___x_1941_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v___x_1943_; lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_2010_; 
v___x_1943_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg(v___y_1938_);
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_1946_ = v___x_1943_;
v_isShared_1947_ = v_isSharedCheck_2010_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1943_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_2010_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
uint8_t v___x_1948_; 
v___x_1948_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_1944_);
if (v___x_1948_ == 0)
{
lean_object* v___x_1949_; lean_object* v_pos2traces_1950_; lean_object* v___x_1951_; 
lean_del_object(v___x_1946_);
v___x_1949_ = lean_unsigned_to_nat(0u);
v_pos2traces_1950_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__8___closed__1, &l_Lean_addTraceAsMessages___at___00main_spec__8___closed__1_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__8___closed__1);
v___x_1951_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14(v___x_1948_, v_a_1944_, v_pos2traces_1950_, v___y_1937_, v___y_1938_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___y_1954_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1980_; lean_object* v_size_1986_; lean_object* v_buckets_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref(v___x_1951_);
v_size_1986_ = lean_ctor_get(v_a_1952_, 0);
lean_inc(v_size_1986_);
v_buckets_1987_ = lean_ctor_get(v_a_1952_, 1);
lean_inc_ref(v_buckets_1987_);
lean_dec(v_a_1952_);
v___x_1988_ = lean_mk_empty_array_with_capacity(v_size_1986_);
lean_dec(v_size_1986_);
v___x_1989_ = lean_array_get_size(v_buckets_1987_);
v___x_1990_ = lean_nat_dec_lt(v___x_1949_, v___x_1989_);
if (v___x_1990_ == 0)
{
lean_dec_ref(v_buckets_1987_);
v___y_1980_ = v___x_1988_;
goto v___jp_1979_;
}
else
{
uint8_t v___x_1991_; 
v___x_1991_ = lean_nat_dec_le(v___x_1989_, v___x_1989_);
if (v___x_1991_ == 0)
{
if (v___x_1990_ == 0)
{
lean_dec_ref(v_buckets_1987_);
v___y_1980_ = v___x_1988_;
goto v___jp_1979_;
}
else
{
size_t v___x_1992_; size_t v___x_1993_; lean_object* v___x_1994_; 
v___x_1992_ = ((size_t)0ULL);
v___x_1993_ = lean_usize_of_nat(v___x_1989_);
v___x_1994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__18(v_buckets_1987_, v___x_1992_, v___x_1993_, v___x_1988_);
lean_dec_ref(v_buckets_1987_);
v___y_1980_ = v___x_1994_;
goto v___jp_1979_;
}
}
else
{
size_t v___x_1995_; size_t v___x_1996_; lean_object* v___x_1997_; 
v___x_1995_ = ((size_t)0ULL);
v___x_1996_ = lean_usize_of_nat(v___x_1989_);
v___x_1997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__18(v_buckets_1987_, v___x_1995_, v___x_1996_, v___x_1988_);
lean_dec_ref(v_buckets_1987_);
v___y_1980_ = v___x_1997_;
goto v___jp_1979_;
}
}
v___jp_1953_:
{
lean_object* v___x_1955_; size_t v_sz_1956_; size_t v___x_1957_; lean_object* v___x_1958_; 
v___x_1955_ = lean_box(0);
v_sz_1956_ = lean_array_size(v___y_1954_);
v___x_1957_ = ((size_t)0ULL);
v___x_1958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15(v___x_1948_, v___y_1954_, v_sz_1956_, v___x_1957_, v___x_1955_, v___y_1937_, v___y_1938_);
lean_dec_ref(v___y_1954_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1965_ == 0)
{
lean_object* v_unused_1966_; 
v_unused_1966_ = lean_ctor_get(v___x_1958_, 0);
lean_dec(v_unused_1966_);
v___x_1960_ = v___x_1958_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_dec(v___x_1958_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 0, v___x_1955_);
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1955_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
else
{
return v___x_1958_;
}
}
v___jp_1967_:
{
lean_object* v___x_1972_; 
lean_dec(v___y_1969_);
v___x_1972_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg(v___y_1970_, v___y_1968_, v___y_1971_);
lean_dec(v___y_1971_);
v___y_1954_ = v___x_1972_;
goto v___jp_1953_;
}
v___jp_1973_:
{
uint8_t v___x_1978_; 
v___x_1978_ = lean_nat_dec_le(v___y_1977_, v___y_1975_);
if (v___x_1978_ == 0)
{
lean_dec(v___y_1975_);
lean_inc(v___y_1977_);
v___y_1968_ = v___y_1977_;
v___y_1969_ = v___y_1974_;
v___y_1970_ = v___y_1976_;
v___y_1971_ = v___y_1977_;
goto v___jp_1967_;
}
else
{
v___y_1968_ = v___y_1977_;
v___y_1969_ = v___y_1974_;
v___y_1970_ = v___y_1976_;
v___y_1971_ = v___y_1975_;
goto v___jp_1967_;
}
}
v___jp_1979_:
{
lean_object* v___x_1981_; uint8_t v___x_1982_; 
v___x_1981_ = lean_array_get_size(v___y_1980_);
v___x_1982_ = lean_nat_dec_eq(v___x_1981_, v___x_1949_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; lean_object* v___x_1984_; uint8_t v___x_1985_; 
v___x_1983_ = lean_unsigned_to_nat(1u);
v___x_1984_ = lean_nat_sub(v___x_1981_, v___x_1983_);
v___x_1985_ = lean_nat_dec_le(v___x_1949_, v___x_1984_);
if (v___x_1985_ == 0)
{
lean_inc(v___x_1984_);
v___y_1974_ = v___x_1981_;
v___y_1975_ = v___x_1984_;
v___y_1976_ = v___y_1980_;
v___y_1977_ = v___x_1984_;
goto v___jp_1973_;
}
else
{
v___y_1974_ = v___x_1981_;
v___y_1975_ = v___x_1984_;
v___y_1976_ = v___y_1980_;
v___y_1977_ = v___x_1949_;
goto v___jp_1973_;
}
}
else
{
v___y_1954_ = v___y_1980_;
goto v___jp_1953_;
}
}
}
else
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2005_; 
lean_dec_ref(v___y_1937_);
v_a_1998_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_2000_ = v___x_1951_;
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1951_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_2001_ == 0)
{
v___x_2003_ = v___x_2000_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_a_1998_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
else
{
lean_object* v___x_2006_; lean_object* v___x_2008_; 
lean_dec(v_a_1944_);
lean_dec_ref(v___y_1937_);
v___x_2006_ = lean_box(0);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 0, v___x_2006_);
v___x_2008_ = v___x_1946_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2006_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
else
{
lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2018_; 
lean_dec_ref(v___y_1937_);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_2018_ == 0)
{
lean_object* v_unused_2019_; 
v_unused_2019_ = lean_ctor_get(v___x_1942_, 0);
lean_dec(v_unused_2019_);
v___x_2012_ = v___x_1942_;
v_isShared_2013_ = v_isSharedCheck_2018_;
goto v_resetjp_2011_;
}
else
{
lean_dec(v___x_1942_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2018_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2014_; lean_object* v___x_2016_; 
v___x_2014_ = lean_box(0);
if (v_isShared_2013_ == 0)
{
lean_ctor_set_tag(v___x_2012_, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2014_);
v___x_2016_ = v___x_2012_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2014_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__8___boxed(lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l_Lean_addTraceAsMessages___at___00main_spec__8(v___y_2020_, v___y_2021_);
lean_dec(v___y_2021_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object* v_as_2024_, size_t v_i_2025_, size_t v_stop_2026_, lean_object* v_b_2027_){
_start:
{
uint8_t v___x_2028_; 
v___x_2028_ = lean_usize_dec_eq(v_i_2025_, v_stop_2026_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; lean_object* v_name_2030_; lean_object* v___x_2031_; size_t v___x_2032_; size_t v___x_2033_; 
v___x_2029_ = lean_array_uget_borrowed(v_as_2024_, v_i_2025_);
v_name_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_name_2030_);
v___x_2031_ = l_Lean_Compiler_LCNF_setDeclPublic(v_b_2027_, v_name_2030_);
v___x_2032_ = ((size_t)1ULL);
v___x_2033_ = lean_usize_add(v_i_2025_, v___x_2032_);
v_i_2025_ = v___x_2033_;
v_b_2027_ = v___x_2031_;
goto _start;
}
else
{
return v_b_2027_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object* v_as_2035_, lean_object* v_i_2036_, lean_object* v_stop_2037_, lean_object* v_b_2038_){
_start:
{
size_t v_i_boxed_2039_; size_t v_stop_boxed_2040_; lean_object* v_res_2041_; 
v_i_boxed_2039_ = lean_unbox_usize(v_i_2036_);
lean_dec(v_i_2036_);
v_stop_boxed_2040_ = lean_unbox_usize(v_stop_2037_);
lean_dec(v_stop_2037_);
v_res_2041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v_as_2035_, v_i_boxed_2039_, v_stop_boxed_2040_, v_b_2038_);
lean_dec_ref(v_as_2035_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object* v_a_2042_, lean_object* v_as_2043_, size_t v_i_2044_, size_t v_stop_2045_, lean_object* v_b_2046_){
_start:
{
lean_object* v___y_2048_; uint8_t v___x_2052_; 
v___x_2052_ = lean_usize_dec_eq(v_i_2044_, v_stop_2045_);
if (v___x_2052_ == 0)
{
lean_object* v___x_2053_; lean_object* v_name_2054_; uint8_t v___x_2055_; 
v___x_2053_ = lean_array_uget_borrowed(v_as_2043_, v_i_2044_);
v_name_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_name_2054_);
lean_inc_ref(v_a_2042_);
v___x_2055_ = l_Lean_isExtern(v_a_2042_, v_name_2054_);
if (v___x_2055_ == 0)
{
v___y_2048_ = v_b_2046_;
goto v___jp_2047_;
}
else
{
lean_object* v___x_2056_; 
lean_inc(v___x_2053_);
v___x_2056_ = lean_array_push(v_b_2046_, v___x_2053_);
v___y_2048_ = v___x_2056_;
goto v___jp_2047_;
}
}
else
{
lean_dec_ref(v_a_2042_);
return v_b_2046_;
}
v___jp_2047_:
{
size_t v___x_2049_; size_t v___x_2050_; 
v___x_2049_ = ((size_t)1ULL);
v___x_2050_ = lean_usize_add(v_i_2044_, v___x_2049_);
v_i_2044_ = v___x_2050_;
v_b_2046_ = v___y_2048_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object* v_a_2057_, lean_object* v_as_2058_, lean_object* v_i_2059_, lean_object* v_stop_2060_, lean_object* v_b_2061_){
_start:
{
size_t v_i_boxed_2062_; size_t v_stop_boxed_2063_; lean_object* v_res_2064_; 
v_i_boxed_2062_ = lean_unbox_usize(v_i_2059_);
lean_dec(v_i_2059_);
v_stop_boxed_2063_ = lean_unbox_usize(v_stop_2060_);
lean_dec(v_stop_2060_);
v_res_2064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_2057_, v_as_2058_, v_i_boxed_2062_, v_stop_boxed_2063_, v_b_2061_);
lean_dec_ref(v_as_2058_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object* v_as_2065_, size_t v_i_2066_, size_t v_stop_2067_, lean_object* v_b_2068_){
_start:
{
uint8_t v___x_2069_; 
v___x_2069_ = lean_usize_dec_eq(v_i_2066_, v_stop_2067_);
if (v___x_2069_ == 0)
{
lean_object* v___x_2070_; lean_object* v_toEnvExtension_2071_; lean_object* v_asyncMode_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; size_t v___x_2076_; size_t v___x_2077_; 
v___x_2070_ = l_Lean_Compiler_LCNF_impureSigExt;
v_toEnvExtension_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc_ref(v_toEnvExtension_2071_);
v_asyncMode_2072_ = lean_ctor_get(v_toEnvExtension_2071_, 2);
lean_inc(v_asyncMode_2072_);
lean_dec_ref(v_toEnvExtension_2071_);
v___x_2073_ = lean_box(0);
v___x_2074_ = lean_array_uget_borrowed(v_as_2065_, v_i_2066_);
lean_inc(v___x_2074_);
v___x_2075_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2070_, v_b_2068_, v___x_2074_, v_asyncMode_2072_, v___x_2073_);
lean_dec(v_asyncMode_2072_);
v___x_2076_ = ((size_t)1ULL);
v___x_2077_ = lean_usize_add(v_i_2066_, v___x_2076_);
v_i_2066_ = v___x_2077_;
v_b_2068_ = v___x_2075_;
goto _start;
}
else
{
return v_b_2068_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object* v_as_2079_, lean_object* v_i_2080_, lean_object* v_stop_2081_, lean_object* v_b_2082_){
_start:
{
size_t v_i_boxed_2083_; size_t v_stop_boxed_2084_; lean_object* v_res_2085_; 
v_i_boxed_2083_ = lean_unbox_usize(v_i_2080_);
lean_dec(v_i_2080_);
v_stop_boxed_2084_ = lean_unbox_usize(v_stop_2081_);
lean_dec(v_stop_2081_);
v_res_2085_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v_as_2079_, v_i_boxed_2083_, v_stop_boxed_2084_, v_b_2082_);
lean_dec_ref(v_as_2079_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object* v___y_2087_, lean_object* v_as_2088_, size_t v_i_2089_, size_t v_stop_2090_, lean_object* v_b_2091_){
_start:
{
lean_object* v___y_2093_; uint8_t v___x_2097_; 
v___x_2097_ = lean_usize_dec_eq(v_i_2089_, v_stop_2090_);
if (v___x_2097_ == 0)
{
lean_object* v_fst_2098_; lean_object* v_snd_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___y_2103_; 
v_fst_2098_ = lean_ctor_get(v_b_2091_, 0);
v_snd_2099_ = lean_ctor_get(v_b_2091_, 1);
v___x_2100_ = lean_array_uget_borrowed(v_as_2088_, v_i_2089_);
v___x_2101_ = l_Lean_IR_Decl_name(v___x_2100_);
if (lean_obj_tag(v___x_2101_) == 1)
{
lean_object* v_pre_2116_; lean_object* v_str_2117_; lean_object* v___x_2118_; uint8_t v___x_2119_; 
v_pre_2116_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_pre_2116_);
v_str_2117_ = lean_ctor_get(v___x_2101_, 1);
lean_inc_ref(v_str_2117_);
v___x_2118_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___closed__0));
v___x_2119_ = lean_string_dec_eq(v_str_2117_, v___x_2118_);
lean_dec_ref(v_str_2117_);
if (v___x_2119_ == 0)
{
lean_dec(v_pre_2116_);
lean_inc_ref(v___x_2101_);
v___y_2103_ = v___x_2101_;
goto v___jp_2102_;
}
else
{
v___y_2103_ = v_pre_2116_;
goto v___jp_2102_;
}
}
else
{
lean_inc(v___x_2101_);
v___y_2103_ = v___x_2101_;
goto v___jp_2102_;
}
v___jp_2102_:
{
uint8_t v___x_2104_; 
lean_inc_ref(v___y_2087_);
v___x_2104_ = l_Lean_isExtern(v___y_2087_, v___y_2103_);
if (v___x_2104_ == 0)
{
lean_dec(v___x_2101_);
v___y_2093_ = v_b_2091_;
goto v___jp_2092_;
}
else
{
lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2113_; 
lean_inc(v_snd_2099_);
lean_inc(v_fst_2098_);
v_isSharedCheck_2113_ = !lean_is_exclusive(v_b_2091_);
if (v_isSharedCheck_2113_ == 0)
{
lean_object* v_unused_2114_; lean_object* v_unused_2115_; 
v_unused_2114_ = lean_ctor_get(v_b_2091_, 1);
lean_dec(v_unused_2114_);
v_unused_2115_ = lean_ctor_get(v_b_2091_, 0);
lean_dec(v_unused_2115_);
v___x_2106_ = v_b_2091_;
v_isShared_2107_ = v_isSharedCheck_2113_;
goto v_resetjp_2105_;
}
else
{
lean_dec(v_b_2091_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2113_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2111_; 
lean_inc(v___x_2100_);
v___x_2108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2100_);
lean_ctor_set(v___x_2108_, 1, v_fst_2098_);
lean_inc(v___x_2100_);
v___x_2109_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_2099_, v___x_2101_, v___x_2100_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 1, v___x_2109_);
lean_ctor_set(v___x_2106_, 0, v___x_2108_);
v___x_2111_ = v___x_2106_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2108_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v___x_2109_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
v___y_2093_ = v___x_2111_;
goto v___jp_2092_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_2087_);
return v_b_2091_;
}
v___jp_2092_:
{
size_t v___x_2094_; size_t v___x_2095_; 
v___x_2094_ = ((size_t)1ULL);
v___x_2095_ = lean_usize_add(v_i_2089_, v___x_2094_);
v_i_2089_ = v___x_2095_;
v_b_2091_ = v___y_2093_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object* v___y_2120_, lean_object* v_as_2121_, lean_object* v_i_2122_, lean_object* v_stop_2123_, lean_object* v_b_2124_){
_start:
{
size_t v_i_boxed_2125_; size_t v_stop_boxed_2126_; lean_object* v_res_2127_; 
v_i_boxed_2125_ = lean_unbox_usize(v_i_2122_);
lean_dec(v_i_2122_);
v_stop_boxed_2126_ = lean_unbox_usize(v_stop_2123_);
lean_dec(v_stop_2123_);
v_res_2127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_2120_, v_as_2121_, v_i_boxed_2125_, v_stop_boxed_2126_, v_b_2124_);
lean_dec_ref(v_as_2121_);
return v_res_2127_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27_spec__37___lam__0(uint8_t v___y_2128_, uint8_t v_suppressElabErrors_2129_, lean_object* v_x_2130_){
_start:
{
if (lean_obj_tag(v_x_2130_) == 1)
{
lean_object* v_pre_2131_; 
v_pre_2131_ = lean_ctor_get(v_x_2130_, 0);
switch(lean_obj_tag(v_pre_2131_))
{
case 1:
{
lean_object* v_pre_2132_; 
v_pre_2132_ = lean_ctor_get(v_pre_2131_, 0);
switch(lean_obj_tag(v_pre_2132_))
{
case 0:
{
lean_object* v_str_2133_; lean_object* v_str_2134_; lean_object* v___x_2135_; uint8_t v___x_2136_; 
v_str_2133_ = lean_ctor_get(v_x_2130_, 1);
v_str_2134_ = lean_ctor_get(v_pre_2131_, 1);
v___x_2135_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__0));
v___x_2136_ = lean_string_dec_eq(v_str_2134_, v___x_2135_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2137_; uint8_t v___x_2138_; 
v___x_2137_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__1));
v___x_2138_ = lean_string_dec_eq(v_str_2134_, v___x_2137_);
if (v___x_2138_ == 0)
{
return v___y_2128_;
}
else
{
lean_object* v___x_2139_; uint8_t v___x_2140_; 
v___x_2139_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__2));
v___x_2140_ = lean_string_dec_eq(v_str_2133_, v___x_2139_);
if (v___x_2140_ == 0)
{
return v___y_2128_;
}
else
{
return v_suppressElabErrors_2129_;
}
}
}
else
{
lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2141_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__3));
v___x_2142_ = lean_string_dec_eq(v_str_2133_, v___x_2141_);
if (v___x_2142_ == 0)
{
return v___y_2128_;
}
else
{
return v_suppressElabErrors_2129_;
}
}
}
case 1:
{
lean_object* v_pre_2143_; 
v_pre_2143_ = lean_ctor_get(v_pre_2132_, 0);
if (lean_obj_tag(v_pre_2143_) == 0)
{
lean_object* v_str_2144_; lean_object* v_str_2145_; lean_object* v_str_2146_; lean_object* v___x_2147_; uint8_t v___x_2148_; 
v_str_2144_ = lean_ctor_get(v_x_2130_, 1);
v_str_2145_ = lean_ctor_get(v_pre_2131_, 1);
v_str_2146_ = lean_ctor_get(v_pre_2132_, 1);
v___x_2147_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__4));
v___x_2148_ = lean_string_dec_eq(v_str_2146_, v___x_2147_);
if (v___x_2148_ == 0)
{
return v___y_2128_;
}
else
{
lean_object* v___x_2149_; uint8_t v___x_2150_; 
v___x_2149_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__5));
v___x_2150_ = lean_string_dec_eq(v_str_2145_, v___x_2149_);
if (v___x_2150_ == 0)
{
return v___y_2128_;
}
else
{
lean_object* v___x_2151_; uint8_t v___x_2152_; 
v___x_2151_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__6));
v___x_2152_ = lean_string_dec_eq(v_str_2144_, v___x_2151_);
if (v___x_2152_ == 0)
{
return v___y_2128_;
}
else
{
return v_suppressElabErrors_2129_;
}
}
}
}
else
{
return v___y_2128_;
}
}
default: 
{
return v___y_2128_;
}
}
}
case 0:
{
lean_object* v_str_2153_; lean_object* v___x_2154_; uint8_t v___x_2155_; 
v_str_2153_ = lean_ctor_get(v_x_2130_, 1);
v___x_2154_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__4_spec__4___closed__0));
v___x_2155_ = lean_string_dec_eq(v_str_2153_, v___x_2154_);
if (v___x_2155_ == 0)
{
return v___y_2128_;
}
else
{
return v_suppressElabErrors_2129_;
}
}
default: 
{
return v___y_2128_;
}
}
}
else
{
return v___y_2128_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27_spec__37___lam__0___boxed(lean_object* v___y_2156_, lean_object* v_suppressElabErrors_2157_, lean_object* v_x_2158_){
_start:
{
uint8_t v___y_38485__boxed_2159_; uint8_t v_suppressElabErrors_boxed_2160_; uint8_t v_res_2161_; lean_object* v_r_2162_; 
v___y_38485__boxed_2159_ = lean_unbox(v___y_2156_);
v_suppressElabErrors_boxed_2160_ = lean_unbox(v_suppressElabErrors_2157_);
v_res_2161_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27_spec__37___lam__0(v___y_38485__boxed_2159_, v_suppressElabErrors_boxed_2160_, v_x_2158_);
lean_dec(v_x_2158_);
v_r_2162_ = lean_box(v_res_2161_);
return v_r_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27_spec__37(lean_object* v_ref_2163_, lean_object* v_msgData_2164_, uint8_t v_severity_2165_, uint8_t v_isSilent_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
lean_object* v___y_2171_; uint8_t v___y_2172_; uint8_t v___y_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2207_; lean_object* v___y_2208_; uint8_t v___y_2209_; lean_object* v___y_2210_; uint8_t v___y_2211_; lean_object* v___y_2212_; uint8_t v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2232_; lean_object* v___y_2233_; uint8_t v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; uint8_t v___y_2237_; uint8_t v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; uint8_t v___y_2246_; lean_object* v___y_2247_; uint8_t v___y_2248_; uint8_t v___y_2249_; uint8_t v___x_2254_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; uint8_t v___y_2260_; uint8_t v___y_2261_; uint8_t v___y_2262_; uint8_t v___y_2264_; uint8_t v___x_2279_; 
v___x_2254_ = 2;
v___x_2279_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2165_, v___x_2254_);
if (v___x_2279_ == 0)
{
v___y_2264_ = v___x_2279_;
goto v___jp_2263_;
}
else
{
uint8_t v___x_2280_; 
lean_inc_ref(v_msgData_2164_);
v___x_2280_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2164_);
v___y_2264_ = v___x_2280_;
goto v___jp_2263_;
}
v___jp_2170_:
{
lean_object* v___x_2180_; lean_object* v_currNamespace_2181_; lean_object* v_openDecls_2182_; lean_object* v_env_2183_; lean_object* v_nextMacroScope_2184_; lean_object* v_ngen_2185_; lean_object* v_auxDeclNGen_2186_; lean_object* v_traceState_2187_; lean_object* v_cache_2188_; lean_object* v_messages_2189_; lean_object* v_infoState_2190_; lean_object* v_snapshotTasks_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2205_; 
v___x_2180_ = lean_st_ref_take(v___y_2179_);
v_currNamespace_2181_ = lean_ctor_get(v___y_2178_, 6);
lean_inc(v_currNamespace_2181_);
v_openDecls_2182_ = lean_ctor_get(v___y_2178_, 7);
lean_inc(v_openDecls_2182_);
lean_dec_ref(v___y_2178_);
v_env_2183_ = lean_ctor_get(v___x_2180_, 0);
v_nextMacroScope_2184_ = lean_ctor_get(v___x_2180_, 1);
v_ngen_2185_ = lean_ctor_get(v___x_2180_, 2);
v_auxDeclNGen_2186_ = lean_ctor_get(v___x_2180_, 3);
v_traceState_2187_ = lean_ctor_get(v___x_2180_, 4);
v_cache_2188_ = lean_ctor_get(v___x_2180_, 5);
v_messages_2189_ = lean_ctor_get(v___x_2180_, 6);
v_infoState_2190_ = lean_ctor_get(v___x_2180_, 7);
v_snapshotTasks_2191_ = lean_ctor_get(v___x_2180_, 8);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2193_ = v___x_2180_;
v_isShared_2194_ = v_isSharedCheck_2205_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_snapshotTasks_2191_);
lean_inc(v_infoState_2190_);
lean_inc(v_messages_2189_);
lean_inc(v_cache_2188_);
lean_inc(v_traceState_2187_);
lean_inc(v_auxDeclNGen_2186_);
lean_inc(v_ngen_2185_);
lean_inc(v_nextMacroScope_2184_);
lean_inc(v_env_2183_);
lean_dec(v___x_2180_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2205_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2195_, 0, v_currNamespace_2181_);
lean_ctor_set(v___x_2195_, 1, v_openDecls_2182_);
v___x_2196_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
lean_ctor_set(v___x_2196_, 1, v___y_2177_);
v___x_2197_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2197_, 0, v___y_2171_);
lean_ctor_set(v___x_2197_, 1, v___y_2174_);
lean_ctor_set(v___x_2197_, 2, v___y_2176_);
lean_ctor_set(v___x_2197_, 3, v___y_2175_);
lean_ctor_set(v___x_2197_, 4, v___x_2196_);
lean_ctor_set_uint8(v___x_2197_, sizeof(void*)*5, v___y_2172_);
lean_ctor_set_uint8(v___x_2197_, sizeof(void*)*5 + 1, v___y_2173_);
lean_ctor_set_uint8(v___x_2197_, sizeof(void*)*5 + 2, v_isSilent_2166_);
v___x_2198_ = l_Lean_MessageLog_add(v___x_2197_, v_messages_2189_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 6, v___x_2198_);
v___x_2200_ = v___x_2193_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_env_2183_);
lean_ctor_set(v_reuseFailAlloc_2204_, 1, v_nextMacroScope_2184_);
lean_ctor_set(v_reuseFailAlloc_2204_, 2, v_ngen_2185_);
lean_ctor_set(v_reuseFailAlloc_2204_, 3, v_auxDeclNGen_2186_);
lean_ctor_set(v_reuseFailAlloc_2204_, 4, v_traceState_2187_);
lean_ctor_set(v_reuseFailAlloc_2204_, 5, v_cache_2188_);
lean_ctor_set(v_reuseFailAlloc_2204_, 6, v___x_2198_);
lean_ctor_set(v_reuseFailAlloc_2204_, 7, v_infoState_2190_);
lean_ctor_set(v_reuseFailAlloc_2204_, 8, v_snapshotTasks_2191_);
v___x_2200_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2201_ = lean_st_ref_set(v___y_2179_, v___x_2200_);
v___x_2202_ = lean_box(0);
v___x_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
return v___x_2203_;
}
}
}
v___jp_2206_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2230_; 
v___x_2215_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2164_);
v___x_2216_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v___x_2215_, v___y_2167_, v___y_2168_);
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2219_ = v___x_2216_;
v_isShared_2220_ = v_isSharedCheck_2230_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2216_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2230_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
lean_inc_ref(v___y_2210_);
v___x_2221_ = l_Lean_FileMap_toPosition(v___y_2210_, v___y_2212_);
lean_dec(v___y_2212_);
v___x_2222_ = l_Lean_FileMap_toPosition(v___y_2210_, v___y_2214_);
lean_dec(v___y_2214_);
v___x_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
v___x_2224_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___closed__1));
if (v___y_2213_ == 0)
{
lean_del_object(v___x_2219_);
lean_dec_ref(v___y_2207_);
v___y_2171_ = v___y_2208_;
v___y_2172_ = v___y_2209_;
v___y_2173_ = v___y_2211_;
v___y_2174_ = v___x_2221_;
v___y_2175_ = v___x_2224_;
v___y_2176_ = v___x_2223_;
v___y_2177_ = v_a_2217_;
v___y_2178_ = v___y_2167_;
v___y_2179_ = v___y_2168_;
goto v___jp_2170_;
}
else
{
uint8_t v___x_2225_; 
lean_inc(v_a_2217_);
v___x_2225_ = l_Lean_MessageData_hasTag(v___y_2207_, v_a_2217_);
if (v___x_2225_ == 0)
{
lean_object* v___x_2226_; lean_object* v___x_2228_; 
lean_dec_ref(v___x_2223_);
lean_dec_ref(v___x_2221_);
lean_dec(v_a_2217_);
lean_dec_ref(v___y_2208_);
lean_dec_ref(v___y_2167_);
v___x_2226_ = lean_box(0);
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 0, v___x_2226_);
v___x_2228_ = v___x_2219_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2226_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
else
{
lean_del_object(v___x_2219_);
v___y_2171_ = v___y_2208_;
v___y_2172_ = v___y_2209_;
v___y_2173_ = v___y_2211_;
v___y_2174_ = v___x_2221_;
v___y_2175_ = v___x_2224_;
v___y_2176_ = v___x_2223_;
v___y_2177_ = v_a_2217_;
v___y_2178_ = v___y_2167_;
v___y_2179_ = v___y_2168_;
goto v___jp_2170_;
}
}
}
}
v___jp_2231_:
{
lean_object* v___x_2240_; 
v___x_2240_ = l_Lean_Syntax_getTailPos_x3f(v___y_2235_, v___y_2234_);
lean_dec(v___y_2235_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_inc(v___y_2239_);
v___y_2207_ = v___y_2232_;
v___y_2208_ = v___y_2233_;
v___y_2209_ = v___y_2234_;
v___y_2210_ = v___y_2236_;
v___y_2211_ = v___y_2237_;
v___y_2212_ = v___y_2239_;
v___y_2213_ = v___y_2238_;
v___y_2214_ = v___y_2239_;
goto v___jp_2206_;
}
else
{
lean_object* v_val_2241_; 
v_val_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_val_2241_);
lean_dec_ref(v___x_2240_);
v___y_2207_ = v___y_2232_;
v___y_2208_ = v___y_2233_;
v___y_2209_ = v___y_2234_;
v___y_2210_ = v___y_2236_;
v___y_2211_ = v___y_2237_;
v___y_2212_ = v___y_2239_;
v___y_2213_ = v___y_2238_;
v___y_2214_ = v_val_2241_;
goto v___jp_2206_;
}
}
v___jp_2242_:
{
lean_object* v_ref_2250_; lean_object* v___x_2251_; 
v_ref_2250_ = l_Lean_replaceRef(v_ref_2163_, v___y_2245_);
lean_dec(v___y_2245_);
v___x_2251_ = l_Lean_Syntax_getPos_x3f(v_ref_2250_, v___y_2246_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v___x_2252_; 
v___x_2252_ = lean_unsigned_to_nat(0u);
v___y_2232_ = v___y_2243_;
v___y_2233_ = v___y_2244_;
v___y_2234_ = v___y_2246_;
v___y_2235_ = v_ref_2250_;
v___y_2236_ = v___y_2247_;
v___y_2237_ = v___y_2249_;
v___y_2238_ = v___y_2248_;
v___y_2239_ = v___x_2252_;
goto v___jp_2231_;
}
else
{
lean_object* v_val_2253_; 
v_val_2253_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_val_2253_);
lean_dec_ref(v___x_2251_);
v___y_2232_ = v___y_2243_;
v___y_2233_ = v___y_2244_;
v___y_2234_ = v___y_2246_;
v___y_2235_ = v_ref_2250_;
v___y_2236_ = v___y_2247_;
v___y_2237_ = v___y_2249_;
v___y_2238_ = v___y_2248_;
v___y_2239_ = v_val_2253_;
goto v___jp_2231_;
}
}
v___jp_2255_:
{
if (v___y_2262_ == 0)
{
v___y_2243_ = v___y_2258_;
v___y_2244_ = v___y_2256_;
v___y_2245_ = v___y_2257_;
v___y_2246_ = v___y_2261_;
v___y_2247_ = v___y_2259_;
v___y_2248_ = v___y_2260_;
v___y_2249_ = v_severity_2165_;
goto v___jp_2242_;
}
else
{
v___y_2243_ = v___y_2258_;
v___y_2244_ = v___y_2256_;
v___y_2245_ = v___y_2257_;
v___y_2246_ = v___y_2261_;
v___y_2247_ = v___y_2259_;
v___y_2248_ = v___y_2260_;
v___y_2249_ = v___x_2254_;
goto v___jp_2242_;
}
}
v___jp_2263_:
{
if (v___y_2264_ == 0)
{
lean_object* v_fileName_2265_; lean_object* v_fileMap_2266_; lean_object* v_options_2267_; lean_object* v_ref_2268_; uint8_t v_suppressElabErrors_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___f_2272_; uint8_t v___x_2273_; uint8_t v___x_2274_; 
v_fileName_2265_ = lean_ctor_get(v___y_2167_, 0);
v_fileMap_2266_ = lean_ctor_get(v___y_2167_, 1);
v_options_2267_ = lean_ctor_get(v___y_2167_, 2);
v_ref_2268_ = lean_ctor_get(v___y_2167_, 5);
v_suppressElabErrors_2269_ = lean_ctor_get_uint8(v___y_2167_, sizeof(void*)*14 + 1);
v___x_2270_ = lean_box(v___y_2264_);
v___x_2271_ = lean_box(v_suppressElabErrors_2269_);
v___f_2272_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27_spec__37___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2272_, 0, v___x_2270_);
lean_closure_set(v___f_2272_, 1, v___x_2271_);
v___x_2273_ = 1;
v___x_2274_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2165_, v___x_2273_);
if (v___x_2274_ == 0)
{
lean_inc_ref(v_fileMap_2266_);
lean_inc(v_ref_2268_);
lean_inc_ref(v_fileName_2265_);
v___y_2256_ = v_fileName_2265_;
v___y_2257_ = v_ref_2268_;
v___y_2258_ = v___f_2272_;
v___y_2259_ = v_fileMap_2266_;
v___y_2260_ = v_suppressElabErrors_2269_;
v___y_2261_ = v___y_2264_;
v___y_2262_ = v___x_2274_;
goto v___jp_2255_;
}
else
{
lean_object* v___x_2275_; uint8_t v___x_2276_; 
v___x_2275_ = l_Lean_warningAsError;
v___x_2276_ = l_Lean_Option_get___at___00main_spec__6(v_options_2267_, v___x_2275_);
lean_inc_ref(v_fileMap_2266_);
lean_inc(v_ref_2268_);
lean_inc_ref(v_fileName_2265_);
v___y_2256_ = v_fileName_2265_;
v___y_2257_ = v_ref_2268_;
v___y_2258_ = v___f_2272_;
v___y_2259_ = v_fileMap_2266_;
v___y_2260_ = v_suppressElabErrors_2269_;
v___y_2261_ = v___y_2264_;
v___y_2262_ = v___x_2276_;
goto v___jp_2255_;
}
}
else
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
lean_dec_ref(v___y_2167_);
lean_dec_ref(v_msgData_2164_);
v___x_2277_ = lean_box(0);
v___x_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
return v___x_2278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27_spec__37___boxed(lean_object* v_ref_2281_, lean_object* v_msgData_2282_, lean_object* v_severity_2283_, lean_object* v_isSilent_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
uint8_t v_severity_boxed_2288_; uint8_t v_isSilent_boxed_2289_; lean_object* v_res_2290_; 
v_severity_boxed_2288_ = lean_unbox(v_severity_2283_);
v_isSilent_boxed_2289_ = lean_unbox(v_isSilent_2284_);
v_res_2290_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27_spec__37(v_ref_2281_, v_msgData_2282_, v_severity_boxed_2288_, v_isSilent_boxed_2289_, v___y_2285_, v___y_2286_);
lean_dec(v___y_2286_);
lean_dec(v_ref_2281_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27(lean_object* v_msgData_2291_, uint8_t v_severity_2292_, uint8_t v_isSilent_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v_ref_2297_; lean_object* v___x_2298_; 
v_ref_2297_ = lean_ctor_get(v___y_2294_, 5);
lean_inc(v_ref_2297_);
v___x_2298_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27_spec__37(v_ref_2297_, v_msgData_2291_, v_severity_2292_, v_isSilent_2293_, v___y_2294_, v___y_2295_);
lean_dec(v_ref_2297_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27___boxed(lean_object* v_msgData_2299_, lean_object* v_severity_2300_, lean_object* v_isSilent_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
uint8_t v_severity_boxed_2305_; uint8_t v_isSilent_boxed_2306_; lean_object* v_res_2307_; 
v_severity_boxed_2305_ = lean_unbox(v_severity_2300_);
v_isSilent_boxed_2306_ = lean_unbox(v_isSilent_2301_);
v_res_2307_ = l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27(v_msgData_2299_, v_severity_boxed_2305_, v_isSilent_boxed_2306_, v___y_2302_, v___y_2303_);
lean_dec(v___y_2303_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13(lean_object* v_msgData_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
uint8_t v___x_2312_; uint8_t v___x_2313_; lean_object* v___x_2314_; 
v___x_2312_ = 2;
v___x_2313_ = 0;
v___x_2314_ = l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27(v_msgData_2308_, v___x_2312_, v___x_2313_, v___y_2309_, v___y_2310_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13___boxed(lean_object* v_msgData_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l_Lean_logError___at___00main_spec__13(v_msgData_2315_, v___y_2316_, v___y_2317_);
lean_dec(v___y_2317_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(lean_object* v_as_2320_, size_t v_sz_2321_, size_t v_i_2322_, lean_object* v_b_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
uint8_t v___x_2327_; 
v___x_2327_ = lean_usize_dec_lt(v_i_2322_, v_sz_2321_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2328_; 
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
v___x_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2328_, 0, v_b_2323_);
return v___x_2328_;
}
else
{
lean_object* v_a_2329_; lean_object* v___x_2330_; 
v_a_2329_ = lean_array_uget_borrowed(v_as_2320_, v_i_2322_);
lean_inc(v___y_2325_);
lean_inc_ref(v___y_2324_);
lean_inc(v_a_2329_);
v___x_2330_ = l_Lean_Compiler_LCNF_resumeCompilation(v_a_2329_, v___y_2324_, v___y_2325_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v___x_2331_; size_t v___x_2332_; size_t v___x_2333_; 
lean_dec_ref(v___x_2330_);
v___x_2331_ = lean_box(0);
v___x_2332_ = ((size_t)1ULL);
v___x_2333_ = lean_usize_add(v_i_2322_, v___x_2332_);
v_i_2322_ = v___x_2333_;
v_b_2323_ = v___x_2331_;
goto _start;
}
else
{
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
return v___x_2330_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11___boxed(lean_object* v_as_2335_, lean_object* v_sz_2336_, lean_object* v_i_2337_, lean_object* v_b_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
size_t v_sz_boxed_2342_; size_t v_i_boxed_2343_; lean_object* v_res_2344_; 
v_sz_boxed_2342_ = lean_unbox_usize(v_sz_2336_);
lean_dec(v_sz_2336_);
v_i_boxed_2343_ = lean_unbox_usize(v_i_2337_);
lean_dec(v_i_2337_);
v_res_2344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_as_2335_, v_sz_boxed_2342_, v_i_boxed_2343_, v_b_2338_, v___y_2339_, v___y_2340_);
lean_dec_ref(v_as_2335_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(lean_object* v_as_2345_, size_t v_sz_2346_, size_t v_i_2347_, lean_object* v_b_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
uint8_t v___x_2352_; 
v___x_2352_ = lean_usize_dec_lt(v_i_2347_, v_sz_2346_);
if (v___x_2352_ == 0)
{
lean_object* v___x_2353_; 
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
v___x_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2353_, 0, v_b_2348_);
return v___x_2353_;
}
else
{
lean_object* v___x_2354_; lean_object* v_a_2355_; size_t v_sz_2356_; size_t v___x_2357_; lean_object* v___x_2358_; 
v___x_2354_ = lean_box(0);
v_a_2355_ = lean_array_uget_borrowed(v_as_2345_, v_i_2347_);
v_sz_2356_ = lean_array_size(v_a_2355_);
v___x_2357_ = ((size_t)0ULL);
lean_inc(v___y_2350_);
lean_inc_ref(v___y_2349_);
v___x_2358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_a_2355_, v_sz_2356_, v___x_2357_, v___x_2354_, v___y_2349_, v___y_2350_);
if (lean_obj_tag(v___x_2358_) == 0)
{
size_t v___x_2359_; size_t v___x_2360_; 
lean_dec_ref(v___x_2358_);
v___x_2359_ = ((size_t)1ULL);
v___x_2360_ = lean_usize_add(v_i_2347_, v___x_2359_);
v_i_2347_ = v___x_2360_;
v_b_2348_ = v___x_2354_;
goto _start;
}
else
{
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
return v___x_2358_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___boxed(lean_object* v_as_2362_, lean_object* v_sz_2363_, lean_object* v_i_2364_, lean_object* v_b_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
size_t v_sz_boxed_2369_; size_t v_i_boxed_2370_; lean_object* v_res_2371_; 
v_sz_boxed_2369_ = lean_unbox_usize(v_sz_2363_);
lean_dec(v_sz_2363_);
v_i_boxed_2370_ = lean_unbox_usize(v_i_2364_);
lean_dec(v_i_2364_);
v_res_2371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(v_as_2362_, v_sz_boxed_2369_, v_i_boxed_2370_, v_b_2365_, v___y_2366_, v___y_2367_);
lean_dec_ref(v_as_2362_);
return v_res_2371_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2376_ = ((lean_object*)(l_main___closed__3));
v___x_2377_ = lean_unsigned_to_nat(27u);
v___x_2378_ = lean_unsigned_to_nat(137u);
v___x_2379_ = ((lean_object*)(l_main___closed__2));
v___x_2380_ = ((lean_object*)(l_main___closed__1));
v___x_2381_ = l_mkPanicMessageWithDecl(v___x_2380_, v___x_2379_, v___x_2378_, v___x_2377_, v___x_2376_);
return v___x_2381_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
lean_object* v___x_2384_; 
v___x_2384_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_box(0), lean_box(0), lean_box(0));
return v___x_2384_;
}
}
static lean_object* _init_l_main___closed__8(void){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2385_ = l_Lean_instInhabitedClassState_default;
v___x_2386_ = lean_box(0);
v___x_2387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
lean_ctor_set(v___x_2387_, 1, v___x_2385_);
return v___x_2387_;
}
}
static lean_object* _init_l_main___closed__9(void){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2388_ = l_Lean_Meta_Match_Extension_instInhabitedState;
v___x_2389_ = lean_box(0);
v___x_2390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2389_);
lean_ctor_set(v___x_2390_, 1, v___x_2388_);
return v___x_2390_;
}
}
static lean_object* _init_l_main___closed__10(void){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2391_ = ((lean_object*)(l_main___closed__6));
v___x_2392_ = ((lean_object*)(l_main___closed__5));
v___x_2393_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_2392_, v___x_2391_);
return v___x_2393_;
}
}
static lean_object* _init_l_main___closed__11(void){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2394_ = lean_obj_once(&l_main___closed__10, &l_main___closed__10_once, _init_l_main___closed__10);
v___x_2395_ = lean_box(0);
v___x_2396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
lean_ctor_set(v___x_2396_, 1, v___x_2394_);
return v___x_2396_;
}
}
static lean_object* _init_l_main___closed__12(void){
_start:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2397_ = lean_obj_once(&l_main___closed__11, &l_main___closed__11_once, _init_l_main___closed__11);
v___x_2398_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2397_);
return v___x_2398_;
}
}
static lean_object* _init_l_main___closed__13(void){
_start:
{
lean_object* v___x_2399_; 
v___x_2399_ = l_Array_instInhabited(lean_box(0));
return v___x_2399_;
}
}
static lean_object* _init_l_main___closed__18(void){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = l_Lean_Options_empty;
v___x_2408_ = l_Lean_Core_getMaxHeartbeats(v___x_2407_);
return v___x_2408_;
}
}
static lean_object* _init_l_main___closed__21(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2411_ = ((lean_object*)(l_main___closed__3));
v___x_2412_ = lean_unsigned_to_nat(51u);
v___x_2413_ = lean_unsigned_to_nat(113u);
v___x_2414_ = ((lean_object*)(l_main___closed__2));
v___x_2415_ = ((lean_object*)(l_main___closed__1));
v___x_2416_ = l_mkPanicMessageWithDecl(v___x_2415_, v___x_2414_, v___x_2413_, v___x_2412_, v___x_2411_);
return v___x_2416_;
}
}
static lean_object* _init_l_main___closed__22(void){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2417_ = lean_unsigned_to_nat(1u);
v___x_2418_ = l_Lean_firstFrontendMacroScope;
v___x_2419_ = lean_nat_add(v___x_2418_, v___x_2417_);
return v___x_2419_;
}
}
static lean_object* _init_l_main___closed__26(void){
_start:
{
lean_object* v___x_2426_; uint64_t v___x_2427_; lean_object* v___x_2428_; 
v___x_2426_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1);
v___x_2427_ = 0ULL;
v___x_2428_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2428_, 0, v___x_2426_);
lean_ctor_set_uint64(v___x_2428_, sizeof(void*)*1, v___x_2427_);
return v___x_2428_;
}
}
static lean_object* _init_l_main___closed__27(void){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2429_;
}
}
static lean_object* _init_l_main___closed__28(void){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2430_ = lean_obj_once(&l_main___closed__27, &l_main___closed__27_once, _init_l_main___closed__27);
v___x_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2430_);
return v___x_2431_;
}
}
static lean_object* _init_l_main___closed__29(void){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2432_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_2433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2432_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
return v___x_2433_;
}
}
static lean_object* _init_l_main___closed__30(void){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2434_ = l_Lean_NameSet_empty;
v___x_2435_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1);
v___x_2436_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
lean_ctor_set(v___x_2436_, 1, v___x_2435_);
lean_ctor_set(v___x_2436_, 2, v___x_2434_);
return v___x_2436_;
}
}
static lean_object* _init_l_main___closed__31(void){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; uint8_t v___x_2439_; lean_object* v___x_2440_; 
v___x_2437_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1);
v___x_2438_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_2439_ = 1;
v___x_2440_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2440_, 0, v___x_2438_);
lean_ctor_set(v___x_2440_, 1, v___x_2438_);
lean_ctor_set(v___x_2440_, 2, v___x_2437_);
lean_ctor_set_uint8(v___x_2440_, sizeof(void*)*3, v___x_2439_);
return v___x_2440_;
}
}
static uint8_t _init_l_main___closed__36(void){
_start:
{
uint8_t v___x_2447_; uint8_t v___x_2448_; 
v___x_2447_ = 2;
v___x_2448_ = l_Lean_instOrdOLeanLevel_ord(v___x_2447_, v___x_2447_);
return v___x_2448_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = 1;
v___x_2450_ = lean_box_uint32(v___x_2449_);
return v___x_2450_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = 0;
v___x_2452_ = lean_box_uint32(v___x_2451_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_2453_){
_start:
{
if (lean_obj_tag(v_args_2453_) == 1)
{
lean_object* v_tail_2478_; 
v_tail_2478_ = lean_ctor_get(v_args_2453_, 1);
lean_inc(v_tail_2478_);
if (lean_obj_tag(v_tail_2478_) == 1)
{
lean_object* v_tail_2479_; 
v_tail_2479_ = lean_ctor_get(v_tail_2478_, 1);
lean_inc(v_tail_2479_);
if (lean_obj_tag(v_tail_2479_) == 1)
{
lean_object* v_head_2480_; lean_object* v_head_2481_; lean_object* v_head_2482_; lean_object* v_tail_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_3099_; 
v_head_2480_ = lean_ctor_get(v_args_2453_, 0);
lean_inc(v_head_2480_);
lean_dec_ref(v_args_2453_);
v_head_2481_ = lean_ctor_get(v_tail_2478_, 0);
lean_inc(v_head_2481_);
lean_dec_ref(v_tail_2478_);
v_head_2482_ = lean_ctor_get(v_tail_2479_, 0);
v_tail_2483_ = lean_ctor_get(v_tail_2479_, 1);
v_isSharedCheck_3099_ = !lean_is_exclusive(v_tail_2479_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_2485_ = v_tail_2479_;
v_isShared_2486_ = v_isSharedCheck_3099_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_tail_2483_);
lean_inc(v_head_2482_);
lean_dec(v_tail_2479_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_3099_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2487_; 
v___x_2487_ = l_Lean_ModuleSetup_load(v_head_2480_);
lean_dec(v_head_2480_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_a_2488_; lean_object* v_name_2489_; lean_object* v_options_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_a_2488_);
lean_dec_ref(v___x_2487_);
v_name_2489_ = lean_ctor_get(v_a_2488_, 0);
lean_inc(v_name_2489_);
v_options_2490_ = lean_ctor_get(v_a_2488_, 6);
lean_inc(v_options_2490_);
lean_dec(v_a_2488_);
v___x_2491_ = l_Lean_LeanOptions_toOptions(v_options_2490_);
v___x_2492_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v_tail_2483_, v___x_2491_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v_a_2493_; lean_object* v___x_2494_; 
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
lean_inc(v_a_2493_);
lean_dec_ref(v___x_2492_);
v___x_2494_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2495_);
lean_dec_ref(v___x_2494_);
v___x_2496_ = lean_box(0);
v___x_2497_ = l_Lean_initSearchPath(v_a_2495_, v___x_2496_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; uint8_t v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; uint8_t v___y_2518_; uint8_t v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; uint8_t v___y_2646_; lean_object* v___y_2647_; uint8_t v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v_nextMacroScope_2653_; lean_object* v_ngen_2654_; lean_object* v_auxDeclNGen_2655_; lean_object* v_traceState_2656_; lean_object* v_messages_2657_; lean_object* v_infoState_2658_; lean_object* v_snapshotTasks_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; uint8_t v___y_2691_; lean_object* v___y_2692_; uint8_t v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___y_2698_; lean_object* v___y_2699_; lean_object* v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; uint8_t v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; uint8_t v___y_2764_; uint8_t v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; uint8_t v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; uint8_t v___y_2784_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; uint8_t v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2915_; lean_object* v___y_2916_; uint8_t v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; uint8_t v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2953_; lean_object* v___y_2954_; uint8_t v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___x_2968_; lean_object* v___x_2969_; uint8_t v___x_2970_; uint8_t v___y_2972_; uint8_t v___x_3065_; 
lean_dec_ref(v___x_2497_);
v___x_2498_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_2499_ = lean_obj_once(&l_main___closed__8, &l_main___closed__8_once, _init_l_main___closed__8);
v___x_2500_ = lean_obj_once(&l_main___closed__9, &l_main___closed__9_once, _init_l_main___closed__9);
v___x_2501_ = lean_obj_once(&l_main___closed__10, &l_main___closed__10_once, _init_l_main___closed__10);
v___x_2502_ = lean_obj_once(&l_main___closed__12, &l_main___closed__12_once, _init_l_main___closed__12);
v___x_2503_ = lean_obj_once(&l_main___closed__13, &l_main___closed__13_once, _init_l_main___closed__13);
v___x_2504_ = lean_box(1);
v___x_2505_ = ((lean_object*)(l_main___closed__14));
v___x_2506_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_2507_ = 1;
v___x_2508_ = l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(v_a_2493_, v___x_2506_, v___x_2507_);
v___x_2509_ = l_Lean_maxHeartbeats;
v___x_2510_ = lean_unsigned_to_nat(0u);
v___x_2511_ = l_Lean_Option_set___at___00main_spec__4(v___x_2508_, v___x_2509_, v___x_2510_);
v___x_2804_ = ((lean_object*)(l_main___closed__20));
lean_inc(v_name_2489_);
v___x_2805_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2805_, 0, v_name_2489_);
lean_ctor_set_uint8(v___x_2805_, sizeof(void*)*1, v___x_2507_);
lean_ctor_set_uint8(v___x_2805_, sizeof(void*)*1 + 1, v___x_2507_);
lean_ctor_set_uint8(v___x_2805_, sizeof(void*)*1 + 2, v___x_2507_);
v___x_2806_ = lean_unsigned_to_nat(1u);
v___x_2968_ = lean_mk_empty_array_with_capacity(v___x_2806_);
v___x_2969_ = lean_array_push(v___x_2968_, v___x_2805_);
v___x_2970_ = 2;
v___x_3065_ = lean_uint8_once(&l_main___closed__36, &l_main___closed__36_once, _init_l_main___closed__36);
if (v___x_3065_ == 0)
{
v___y_2972_ = v___x_2507_;
goto v___jp_2971_;
}
else
{
uint8_t v___x_3066_; 
v___x_3066_ = 0;
v___y_2972_ = v___x_3066_;
goto v___jp_2971_;
}
v___jp_2512_:
{
lean_object* v___x_2537_; 
v___x_2537_ = l_Lean_addTraceAsMessages___at___00main_spec__8(v___y_2534_, v___y_2529_);
lean_dec(v___y_2529_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v___x_2538_; lean_object* v_messages_2539_; lean_object* v_env_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2632_; 
lean_dec_ref(v___x_2537_);
v___x_2538_ = lean_st_ref_get(v___y_2526_);
lean_dec(v___y_2526_);
v_messages_2539_ = lean_ctor_get(v___x_2538_, 6);
v_env_2540_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2632_ == 0)
{
lean_object* v_unused_2633_; lean_object* v_unused_2634_; lean_object* v_unused_2635_; lean_object* v_unused_2636_; lean_object* v_unused_2637_; lean_object* v_unused_2638_; lean_object* v_unused_2639_; 
v_unused_2633_ = lean_ctor_get(v___x_2538_, 8);
lean_dec(v_unused_2633_);
v_unused_2634_ = lean_ctor_get(v___x_2538_, 7);
lean_dec(v_unused_2634_);
v_unused_2635_ = lean_ctor_get(v___x_2538_, 5);
lean_dec(v_unused_2635_);
v_unused_2636_ = lean_ctor_get(v___x_2538_, 4);
lean_dec(v_unused_2636_);
v_unused_2637_ = lean_ctor_get(v___x_2538_, 3);
lean_dec(v_unused_2637_);
v_unused_2638_ = lean_ctor_get(v___x_2538_, 2);
lean_dec(v_unused_2638_);
v_unused_2639_ = lean_ctor_get(v___x_2538_, 1);
lean_dec(v_unused_2639_);
v___x_2542_ = v___x_2538_;
v_isShared_2543_ = v_isSharedCheck_2632_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_messages_2539_);
lean_inc(v_env_2540_);
lean_dec(v___x_2538_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2632_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v_unreported_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v_unreported_2544_ = lean_ctor_get(v_messages_2539_, 1);
v___x_2545_ = lean_box(0);
lean_inc_ref(v_unreported_2544_);
v___x_2546_ = l_Lean_PersistentArray_forIn___at___00main_spec__10(v_unreported_2544_, v___x_2545_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2622_; 
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2622_ == 0)
{
lean_object* v_unused_2623_; 
v_unused_2623_ = lean_ctor_get(v___x_2546_, 0);
lean_dec(v_unused_2623_);
v___x_2548_ = v___x_2546_;
v_isShared_2549_ = v_isSharedCheck_2622_;
goto v_resetjp_2547_;
}
else
{
lean_dec(v___x_2546_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2622_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
uint8_t v___x_2550_; 
v___x_2550_ = l_Lean_MessageLog_hasErrors(v_messages_2539_);
lean_dec_ref(v_messages_2539_);
if (v___x_2550_ == 0)
{
lean_object* v___x_2551_; lean_object* v_a_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
lean_del_object(v___x_2548_);
lean_inc_ref(v_env_2540_);
v___x_2551_ = l___private_LeanIR_0__mkIRData(v_env_2540_);
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
lean_inc(v_a_2552_);
lean_dec_ref(v___x_2551_);
v___x_2553_ = l_Lean_Environment_mainModule(v_env_2540_);
v___x_2554_ = ((lean_object*)(l_main___closed__16));
v___x_2555_ = l_Lean_Name_append(v___x_2553_, v___x_2554_);
lean_inc(v_head_2481_);
v___x_2556_ = l_Lean_saveModuleData(v_head_2481_, v___x_2555_, v_a_2552_);
lean_dec(v___x_2555_);
if (lean_obj_tag(v___x_2556_) == 0)
{
uint8_t v___x_2557_; lean_object* v___x_2558_; 
lean_dec_ref(v___x_2556_);
v___x_2557_ = 1;
v___x_2558_ = lean_io_prim_handle_mk(v_head_2482_, v___x_2557_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2564_; 
lean_dec(v_head_2482_);
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_a_2559_);
lean_dec_ref(v___x_2558_);
v___x_2560_ = ((lean_object*)(l_main___closed__17));
v___x_2561_ = l_Lean_Options_empty;
v___x_2562_ = lean_obj_once(&l_main___closed__18, &l_main___closed__18_once, _init_l_main___closed__18);
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 8, v___y_2535_);
lean_ctor_set(v___x_2542_, 7, v___y_2530_);
lean_ctor_set(v___x_2542_, 6, v___y_2532_);
lean_ctor_set(v___x_2542_, 5, v___y_2533_);
lean_ctor_set(v___x_2542_, 4, v___y_2525_);
lean_ctor_set(v___x_2542_, 3, v___y_2528_);
lean_ctor_set(v___x_2542_, 2, v___y_2536_);
lean_ctor_set(v___x_2542_, 1, v___y_2531_);
v___x_2564_ = v___x_2542_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_env_2540_);
lean_ctor_set(v_reuseFailAlloc_2587_, 1, v___y_2531_);
lean_ctor_set(v_reuseFailAlloc_2587_, 2, v___y_2536_);
lean_ctor_set(v_reuseFailAlloc_2587_, 3, v___y_2528_);
lean_ctor_set(v_reuseFailAlloc_2587_, 4, v___y_2525_);
lean_ctor_set(v_reuseFailAlloc_2587_, 5, v___y_2533_);
lean_ctor_set(v_reuseFailAlloc_2587_, 6, v___y_2532_);
lean_ctor_set(v_reuseFailAlloc_2587_, 7, v___y_2530_);
lean_ctor_set(v_reuseFailAlloc_2587_, 8, v___y_2535_);
v___x_2564_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___f_2567_; lean_object* v___x_2568_; 
v___x_2565_ = lean_box(v___y_2519_);
v___x_2566_ = lean_box(v___y_2518_);
v___f_2567_ = lean_alloc_closure((void*)(l_main___lam__1___boxed), 20, 19);
lean_closure_set(v___f_2567_, 0, v___x_2564_);
lean_closure_set(v___f_2567_, 1, v___y_2517_);
lean_closure_set(v___f_2567_, 2, v___x_2561_);
lean_closure_set(v___f_2567_, 3, v___y_2523_);
lean_closure_set(v___f_2567_, 4, v___y_2524_);
lean_closure_set(v___f_2567_, 5, v_name_2489_);
lean_closure_set(v___f_2567_, 6, v_a_2559_);
lean_closure_set(v___f_2567_, 7, v___y_2521_);
lean_closure_set(v___f_2567_, 8, v_head_2481_);
lean_closure_set(v___f_2567_, 9, v___y_2513_);
lean_closure_set(v___f_2567_, 10, v___x_2510_);
lean_closure_set(v___f_2567_, 11, v___y_2520_);
lean_closure_set(v___f_2567_, 12, v___y_2514_);
lean_closure_set(v___f_2567_, 13, v___y_2522_);
lean_closure_set(v___f_2567_, 14, v___x_2562_);
lean_closure_set(v___f_2567_, 15, v___y_2515_);
lean_closure_set(v___f_2567_, 16, v___y_2516_);
lean_closure_set(v___f_2567_, 17, v___x_2565_);
lean_closure_set(v___f_2567_, 18, v___x_2566_);
v___x_2568_ = l_Lean_profileitIOUnsafe___redArg(v___x_2560_, v___x_2511_, v___f_2567_, v___y_2527_);
lean_dec_ref(v___x_2511_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2577_; 
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2577_ == 0)
{
lean_object* v_unused_2578_; 
v_unused_2578_ = lean_ctor_get(v___x_2568_, 0);
lean_dec(v_unused_2578_);
v___x_2570_ = v___x_2568_;
v_isShared_2571_ = v_isSharedCheck_2577_;
goto v_resetjp_2569_;
}
else
{
lean_dec(v___x_2568_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2577_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2575_; 
v___x_2572_ = lean_display_cumulative_profiling_times();
v___x_2573_ = l_main___boxed__const__2;
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 0, v___x_2573_);
v___x_2575_ = v___x_2570_;
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
}
else
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2586_; 
v_a_2579_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2581_ = v___x_2568_;
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2568_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2584_; 
if (v_isShared_2582_ == 0)
{
v___x_2584_ = v___x_2581_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_a_2579_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
}
else
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
lean_dec_ref(v___x_2558_);
lean_del_object(v___x_2542_);
lean_dec_ref(v_env_2540_);
lean_dec_ref(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec_ref(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec_ref(v___x_2511_);
lean_dec(v_name_2489_);
lean_dec(v_head_2481_);
v___x_2588_ = ((lean_object*)(l_main___closed__19));
v___x_2589_ = lean_string_append(v___x_2588_, v_head_2482_);
lean_dec(v_head_2482_);
v___x_2590_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__5));
v___x_2591_ = lean_string_append(v___x_2589_, v___x_2590_);
v___x_2592_ = l_IO_eprintln___at___00main_spec__9(v___x_2591_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2600_; 
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2600_ == 0)
{
lean_object* v_unused_2601_; 
v_unused_2601_ = lean_ctor_get(v___x_2592_, 0);
lean_dec(v_unused_2601_);
v___x_2594_ = v___x_2592_;
v_isShared_2595_ = v_isSharedCheck_2600_;
goto v_resetjp_2593_;
}
else
{
lean_dec(v___x_2592_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2600_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2596_; lean_object* v___x_2598_; 
v___x_2596_ = l_main___boxed__const__1;
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v___x_2596_);
v___x_2598_ = v___x_2594_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2596_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
v_a_2602_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___x_2592_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2592_);
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
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
lean_del_object(v___x_2542_);
lean_dec_ref(v_env_2540_);
lean_dec_ref(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec_ref(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec_ref(v___x_2511_);
lean_dec(v_name_2489_);
lean_dec(v_head_2482_);
lean_dec(v_head_2481_);
v_a_2610_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2556_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2556_);
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
else
{
lean_object* v___x_2618_; lean_object* v___x_2620_; 
lean_del_object(v___x_2542_);
lean_dec_ref(v_env_2540_);
lean_dec_ref(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec_ref(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec_ref(v___x_2511_);
lean_dec(v_name_2489_);
lean_dec(v_head_2482_);
lean_dec(v_head_2481_);
v___x_2618_ = l_main___boxed__const__1;
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 0, v___x_2618_);
v___x_2620_ = v___x_2548_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v___x_2618_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
else
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
lean_del_object(v___x_2542_);
lean_dec_ref(v_env_2540_);
lean_dec_ref(v_messages_2539_);
lean_dec_ref(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec_ref(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec_ref(v___x_2511_);
lean_dec(v_name_2489_);
lean_dec(v_head_2482_);
lean_dec(v_head_2481_);
v_a_2624_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2546_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2546_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2537_);
lean_dec_ref(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec_ref(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec_ref(v___x_2511_);
lean_dec(v_name_2489_);
lean_dec(v_head_2482_);
lean_dec(v_head_2481_);
goto v___jp_2475_;
}
}
v___jp_2640_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; size_t v_sz_2677_; size_t v___x_2678_; lean_object* v___x_2679_; 
lean_inc_ref(v___y_2672_);
v___x_2674_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2674_, 0, v___y_2673_);
lean_ctor_set(v___x_2674_, 1, v_nextMacroScope_2653_);
lean_ctor_set(v___x_2674_, 2, v_ngen_2654_);
lean_ctor_set(v___x_2674_, 3, v_auxDeclNGen_2655_);
lean_ctor_set(v___x_2674_, 4, v_traceState_2656_);
lean_ctor_set(v___x_2674_, 5, v___y_2672_);
lean_ctor_set(v___x_2674_, 6, v_messages_2657_);
lean_ctor_set(v___x_2674_, 7, v_infoState_2658_);
lean_ctor_set(v___x_2674_, 8, v_snapshotTasks_2659_);
v___x_2675_ = lean_st_ref_set(v___y_2662_, v___x_2674_);
v___x_2676_ = lean_box(0);
v_sz_2677_ = lean_array_size(v___y_2665_);
v___x_2678_ = ((size_t)0ULL);
lean_inc(v___y_2662_);
lean_inc_ref(v___y_2666_);
v___x_2679_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(v___y_2665_, v_sz_2677_, v___x_2678_, v___x_2676_, v___y_2666_, v___y_2662_);
lean_dec_ref(v___y_2665_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_dec_ref(v___x_2679_);
v___y_2513_ = v___y_2641_;
v___y_2514_ = v___y_2642_;
v___y_2515_ = v___y_2643_;
v___y_2516_ = v___y_2644_;
v___y_2517_ = v___y_2645_;
v___y_2518_ = v___y_2646_;
v___y_2519_ = v___y_2648_;
v___y_2520_ = v___y_2647_;
v___y_2521_ = v___y_2649_;
v___y_2522_ = v___y_2651_;
v___y_2523_ = v___y_2650_;
v___y_2524_ = v___y_2652_;
v___y_2525_ = v___y_2660_;
v___y_2526_ = v___y_2661_;
v___y_2527_ = v___y_2663_;
v___y_2528_ = v___y_2669_;
v___y_2529_ = v___y_2662_;
v___y_2530_ = v___y_2664_;
v___y_2531_ = v___y_2670_;
v___y_2532_ = v___y_2671_;
v___y_2533_ = v___y_2672_;
v___y_2534_ = v___y_2666_;
v___y_2535_ = v___y_2668_;
v___y_2536_ = v___y_2667_;
goto v___jp_2512_;
}
else
{
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_dec_ref(v___x_2679_);
v___y_2513_ = v___y_2641_;
v___y_2514_ = v___y_2642_;
v___y_2515_ = v___y_2643_;
v___y_2516_ = v___y_2644_;
v___y_2517_ = v___y_2645_;
v___y_2518_ = v___y_2646_;
v___y_2519_ = v___y_2648_;
v___y_2520_ = v___y_2647_;
v___y_2521_ = v___y_2649_;
v___y_2522_ = v___y_2651_;
v___y_2523_ = v___y_2650_;
v___y_2524_ = v___y_2652_;
v___y_2525_ = v___y_2660_;
v___y_2526_ = v___y_2661_;
v___y_2527_ = v___y_2663_;
v___y_2528_ = v___y_2669_;
v___y_2529_ = v___y_2662_;
v___y_2530_ = v___y_2664_;
v___y_2531_ = v___y_2670_;
v___y_2532_ = v___y_2671_;
v___y_2533_ = v___y_2672_;
v___y_2534_ = v___y_2666_;
v___y_2535_ = v___y_2668_;
v___y_2536_ = v___y_2667_;
goto v___jp_2512_;
}
else
{
lean_object* v_a_2680_; uint8_t v___x_2681_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref(v___x_2679_);
v___x_2681_ = l_Lean_Exception_isInterrupt(v_a_2680_);
if (v___x_2681_ == 0)
{
lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2682_ = l_Lean_Exception_toMessageData(v_a_2680_);
lean_inc_ref(v___y_2666_);
v___x_2683_ = l_Lean_logError___at___00main_spec__13(v___x_2682_, v___y_2666_, v___y_2662_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_dec_ref(v___x_2683_);
v___y_2513_ = v___y_2641_;
v___y_2514_ = v___y_2642_;
v___y_2515_ = v___y_2643_;
v___y_2516_ = v___y_2644_;
v___y_2517_ = v___y_2645_;
v___y_2518_ = v___y_2646_;
v___y_2519_ = v___y_2648_;
v___y_2520_ = v___y_2647_;
v___y_2521_ = v___y_2649_;
v___y_2522_ = v___y_2651_;
v___y_2523_ = v___y_2650_;
v___y_2524_ = v___y_2652_;
v___y_2525_ = v___y_2660_;
v___y_2526_ = v___y_2661_;
v___y_2527_ = v___y_2663_;
v___y_2528_ = v___y_2669_;
v___y_2529_ = v___y_2662_;
v___y_2530_ = v___y_2664_;
v___y_2531_ = v___y_2670_;
v___y_2532_ = v___y_2671_;
v___y_2533_ = v___y_2672_;
v___y_2534_ = v___y_2666_;
v___y_2535_ = v___y_2668_;
v___y_2536_ = v___y_2667_;
goto v___jp_2512_;
}
else
{
lean_object* v___x_2684_; 
lean_dec_ref(v___x_2683_);
lean_dec_ref(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec_ref(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2647_);
lean_dec(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec_ref(v___x_2511_);
lean_dec(v_name_2489_);
lean_dec(v_head_2482_);
lean_dec(v_head_2481_);
v___x_2684_ = l_Lean_addTraceAsMessages___at___00main_spec__8(v___y_2666_, v___y_2662_);
lean_dec(v___y_2662_);
lean_dec_ref(v___x_2684_);
goto v___jp_2475_;
}
}
else
{
lean_dec(v_a_2680_);
v___y_2513_ = v___y_2641_;
v___y_2514_ = v___y_2642_;
v___y_2515_ = v___y_2643_;
v___y_2516_ = v___y_2644_;
v___y_2517_ = v___y_2645_;
v___y_2518_ = v___y_2646_;
v___y_2519_ = v___y_2648_;
v___y_2520_ = v___y_2647_;
v___y_2521_ = v___y_2649_;
v___y_2522_ = v___y_2651_;
v___y_2523_ = v___y_2650_;
v___y_2524_ = v___y_2652_;
v___y_2525_ = v___y_2660_;
v___y_2526_ = v___y_2661_;
v___y_2527_ = v___y_2663_;
v___y_2528_ = v___y_2669_;
v___y_2529_ = v___y_2662_;
v___y_2530_ = v___y_2664_;
v___y_2531_ = v___y_2670_;
v___y_2532_ = v___y_2671_;
v___y_2533_ = v___y_2672_;
v___y_2534_ = v___y_2666_;
v___y_2535_ = v___y_2668_;
v___y_2536_ = v___y_2667_;
goto v___jp_2512_;
}
}
}
}
v___jp_2685_:
{
lean_object* v___x_2712_; lean_object* v_fileName_2713_; lean_object* v_fileMap_2714_; lean_object* v_currRecDepth_2715_; lean_object* v_ref_2716_; lean_object* v_currNamespace_2717_; lean_object* v_openDecls_2718_; lean_object* v_initHeartbeats_2719_; lean_object* v_maxHeartbeats_2720_; lean_object* v_quotContext_2721_; lean_object* v_currMacroScope_2722_; lean_object* v_cancelTk_x3f_2723_; uint8_t v_suppressElabErrors_2724_; lean_object* v_inheritedTraceOptions_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2755_; 
v___x_2712_ = lean_st_ref_take(v___y_2711_);
v_fileName_2713_ = lean_ctor_get(v___y_2710_, 0);
v_fileMap_2714_ = lean_ctor_get(v___y_2710_, 1);
v_currRecDepth_2715_ = lean_ctor_get(v___y_2710_, 3);
v_ref_2716_ = lean_ctor_get(v___y_2710_, 5);
v_currNamespace_2717_ = lean_ctor_get(v___y_2710_, 6);
v_openDecls_2718_ = lean_ctor_get(v___y_2710_, 7);
v_initHeartbeats_2719_ = lean_ctor_get(v___y_2710_, 8);
v_maxHeartbeats_2720_ = lean_ctor_get(v___y_2710_, 9);
v_quotContext_2721_ = lean_ctor_get(v___y_2710_, 10);
v_currMacroScope_2722_ = lean_ctor_get(v___y_2710_, 11);
v_cancelTk_x3f_2723_ = lean_ctor_get(v___y_2710_, 12);
v_suppressElabErrors_2724_ = lean_ctor_get_uint8(v___y_2710_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2725_ = lean_ctor_get(v___y_2710_, 13);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___y_2710_);
if (v_isSharedCheck_2755_ == 0)
{
lean_object* v_unused_2756_; lean_object* v_unused_2757_; 
v_unused_2756_ = lean_ctor_get(v___y_2710_, 4);
lean_dec(v_unused_2756_);
v_unused_2757_ = lean_ctor_get(v___y_2710_, 2);
lean_dec(v_unused_2757_);
v___x_2727_ = v___y_2710_;
v_isShared_2728_ = v_isSharedCheck_2755_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_inheritedTraceOptions_2725_);
lean_inc(v_cancelTk_x3f_2723_);
lean_inc(v_currMacroScope_2722_);
lean_inc(v_quotContext_2721_);
lean_inc(v_maxHeartbeats_2720_);
lean_inc(v_initHeartbeats_2719_);
lean_inc(v_openDecls_2718_);
lean_inc(v_currNamespace_2717_);
lean_inc(v_ref_2716_);
lean_inc(v_currRecDepth_2715_);
lean_inc(v_fileMap_2714_);
lean_inc(v_fileName_2713_);
lean_dec(v___y_2710_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2755_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v_env_2729_; lean_object* v_nextMacroScope_2730_; lean_object* v_ngen_2731_; lean_object* v_auxDeclNGen_2732_; lean_object* v_traceState_2733_; lean_object* v_messages_2734_; lean_object* v_infoState_2735_; lean_object* v_snapshotTasks_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2740_; 
v_env_2729_ = lean_ctor_get(v___x_2712_, 0);
lean_inc_ref(v_env_2729_);
v_nextMacroScope_2730_ = lean_ctor_get(v___x_2712_, 1);
lean_inc(v_nextMacroScope_2730_);
v_ngen_2731_ = lean_ctor_get(v___x_2712_, 2);
lean_inc_ref(v_ngen_2731_);
v_auxDeclNGen_2732_ = lean_ctor_get(v___x_2712_, 3);
lean_inc_ref(v_auxDeclNGen_2732_);
v_traceState_2733_ = lean_ctor_get(v___x_2712_, 4);
lean_inc_ref(v_traceState_2733_);
v_messages_2734_ = lean_ctor_get(v___x_2712_, 6);
lean_inc_ref(v_messages_2734_);
v_infoState_2735_ = lean_ctor_get(v___x_2712_, 7);
lean_inc_ref(v_infoState_2735_);
v_snapshotTasks_2736_ = lean_ctor_get(v___x_2712_, 8);
lean_inc_ref(v_snapshotTasks_2736_);
lean_dec(v___x_2712_);
v___x_2737_ = l_Lean_maxRecDepth;
v___x_2738_ = l_Lean_Option_get___at___00main_spec__7(v___x_2511_, v___x_2737_);
lean_inc_ref(v___x_2511_);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 4, v___x_2738_);
lean_ctor_set(v___x_2727_, 2, v___x_2511_);
v___x_2740_ = v___x_2727_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_fileName_2713_);
lean_ctor_set(v_reuseFailAlloc_2754_, 1, v_fileMap_2714_);
lean_ctor_set(v_reuseFailAlloc_2754_, 2, v___x_2511_);
lean_ctor_set(v_reuseFailAlloc_2754_, 3, v_currRecDepth_2715_);
lean_ctor_set(v_reuseFailAlloc_2754_, 4, v___x_2738_);
lean_ctor_set(v_reuseFailAlloc_2754_, 5, v_ref_2716_);
lean_ctor_set(v_reuseFailAlloc_2754_, 6, v_currNamespace_2717_);
lean_ctor_set(v_reuseFailAlloc_2754_, 7, v_openDecls_2718_);
lean_ctor_set(v_reuseFailAlloc_2754_, 8, v_initHeartbeats_2719_);
lean_ctor_set(v_reuseFailAlloc_2754_, 9, v_maxHeartbeats_2720_);
lean_ctor_set(v_reuseFailAlloc_2754_, 10, v_quotContext_2721_);
lean_ctor_set(v_reuseFailAlloc_2754_, 11, v_currMacroScope_2722_);
lean_ctor_set(v_reuseFailAlloc_2754_, 12, v_cancelTk_x3f_2723_);
lean_ctor_set(v_reuseFailAlloc_2754_, 13, v_inheritedTraceOptions_2725_);
lean_ctor_set_uint8(v_reuseFailAlloc_2754_, sizeof(void*)*14 + 1, v_suppressElabErrors_2724_);
v___x_2740_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
lean_object* v___x_2741_; uint8_t v___x_2742_; 
lean_ctor_set_uint8(v___x_2740_, sizeof(void*)*14, v___y_2706_);
v___x_2741_ = lean_array_get_size(v___y_2701_);
v___x_2742_ = lean_nat_dec_lt(v___x_2510_, v___x_2741_);
if (v___x_2742_ == 0)
{
lean_object* v___x_2743_; 
v___x_2743_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_2704_, v_env_2729_, v___x_2504_);
v___y_2641_ = v___y_2686_;
v___y_2642_ = v___y_2687_;
v___y_2643_ = v___y_2688_;
v___y_2644_ = v___y_2689_;
v___y_2645_ = v___y_2690_;
v___y_2646_ = v___y_2691_;
v___y_2647_ = v___y_2692_;
v___y_2648_ = v___y_2693_;
v___y_2649_ = v___y_2694_;
v___y_2650_ = v___y_2695_;
v___y_2651_ = v___y_2696_;
v___y_2652_ = v___x_2737_;
v_nextMacroScope_2653_ = v_nextMacroScope_2730_;
v_ngen_2654_ = v_ngen_2731_;
v_auxDeclNGen_2655_ = v_auxDeclNGen_2732_;
v_traceState_2656_ = v_traceState_2733_;
v_messages_2657_ = v_messages_2734_;
v_infoState_2658_ = v_infoState_2735_;
v_snapshotTasks_2659_ = v_snapshotTasks_2736_;
v___y_2660_ = v___y_2697_;
v___y_2661_ = v___y_2698_;
v___y_2662_ = v___y_2711_;
v___y_2663_ = v___y_2699_;
v___y_2664_ = v___y_2700_;
v___y_2665_ = v___y_2701_;
v___y_2666_ = v___x_2740_;
v___y_2667_ = v___y_2703_;
v___y_2668_ = v___y_2702_;
v___y_2669_ = v___y_2705_;
v___y_2670_ = v___y_2707_;
v___y_2671_ = v___y_2708_;
v___y_2672_ = v___y_2709_;
v___y_2673_ = v___x_2743_;
goto v___jp_2640_;
}
else
{
uint8_t v___x_2744_; 
v___x_2744_ = lean_nat_dec_le(v___x_2741_, v___x_2741_);
if (v___x_2744_ == 0)
{
if (v___x_2742_ == 0)
{
lean_object* v___x_2745_; 
v___x_2745_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_2704_, v_env_2729_, v___x_2504_);
v___y_2641_ = v___y_2686_;
v___y_2642_ = v___y_2687_;
v___y_2643_ = v___y_2688_;
v___y_2644_ = v___y_2689_;
v___y_2645_ = v___y_2690_;
v___y_2646_ = v___y_2691_;
v___y_2647_ = v___y_2692_;
v___y_2648_ = v___y_2693_;
v___y_2649_ = v___y_2694_;
v___y_2650_ = v___y_2695_;
v___y_2651_ = v___y_2696_;
v___y_2652_ = v___x_2737_;
v_nextMacroScope_2653_ = v_nextMacroScope_2730_;
v_ngen_2654_ = v_ngen_2731_;
v_auxDeclNGen_2655_ = v_auxDeclNGen_2732_;
v_traceState_2656_ = v_traceState_2733_;
v_messages_2657_ = v_messages_2734_;
v_infoState_2658_ = v_infoState_2735_;
v_snapshotTasks_2659_ = v_snapshotTasks_2736_;
v___y_2660_ = v___y_2697_;
v___y_2661_ = v___y_2698_;
v___y_2662_ = v___y_2711_;
v___y_2663_ = v___y_2699_;
v___y_2664_ = v___y_2700_;
v___y_2665_ = v___y_2701_;
v___y_2666_ = v___x_2740_;
v___y_2667_ = v___y_2703_;
v___y_2668_ = v___y_2702_;
v___y_2669_ = v___y_2705_;
v___y_2670_ = v___y_2707_;
v___y_2671_ = v___y_2708_;
v___y_2672_ = v___y_2709_;
v___y_2673_ = v___x_2745_;
goto v___jp_2640_;
}
else
{
size_t v___x_2746_; size_t v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2746_ = ((size_t)0ULL);
v___x_2747_ = lean_usize_of_nat(v___x_2741_);
v___x_2748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v___y_2701_, v___x_2746_, v___x_2747_, v___x_2504_);
v___x_2749_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_2704_, v_env_2729_, v___x_2748_);
v___y_2641_ = v___y_2686_;
v___y_2642_ = v___y_2687_;
v___y_2643_ = v___y_2688_;
v___y_2644_ = v___y_2689_;
v___y_2645_ = v___y_2690_;
v___y_2646_ = v___y_2691_;
v___y_2647_ = v___y_2692_;
v___y_2648_ = v___y_2693_;
v___y_2649_ = v___y_2694_;
v___y_2650_ = v___y_2695_;
v___y_2651_ = v___y_2696_;
v___y_2652_ = v___x_2737_;
v_nextMacroScope_2653_ = v_nextMacroScope_2730_;
v_ngen_2654_ = v_ngen_2731_;
v_auxDeclNGen_2655_ = v_auxDeclNGen_2732_;
v_traceState_2656_ = v_traceState_2733_;
v_messages_2657_ = v_messages_2734_;
v_infoState_2658_ = v_infoState_2735_;
v_snapshotTasks_2659_ = v_snapshotTasks_2736_;
v___y_2660_ = v___y_2697_;
v___y_2661_ = v___y_2698_;
v___y_2662_ = v___y_2711_;
v___y_2663_ = v___y_2699_;
v___y_2664_ = v___y_2700_;
v___y_2665_ = v___y_2701_;
v___y_2666_ = v___x_2740_;
v___y_2667_ = v___y_2703_;
v___y_2668_ = v___y_2702_;
v___y_2669_ = v___y_2705_;
v___y_2670_ = v___y_2707_;
v___y_2671_ = v___y_2708_;
v___y_2672_ = v___y_2709_;
v___y_2673_ = v___x_2749_;
goto v___jp_2640_;
}
}
else
{
size_t v___x_2750_; size_t v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2750_ = ((size_t)0ULL);
v___x_2751_ = lean_usize_of_nat(v___x_2741_);
v___x_2752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v___y_2701_, v___x_2750_, v___x_2751_, v___x_2504_);
v___x_2753_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_2704_, v_env_2729_, v___x_2752_);
v___y_2641_ = v___y_2686_;
v___y_2642_ = v___y_2687_;
v___y_2643_ = v___y_2688_;
v___y_2644_ = v___y_2689_;
v___y_2645_ = v___y_2690_;
v___y_2646_ = v___y_2691_;
v___y_2647_ = v___y_2692_;
v___y_2648_ = v___y_2693_;
v___y_2649_ = v___y_2694_;
v___y_2650_ = v___y_2695_;
v___y_2651_ = v___y_2696_;
v___y_2652_ = v___x_2737_;
v_nextMacroScope_2653_ = v_nextMacroScope_2730_;
v_ngen_2654_ = v_ngen_2731_;
v_auxDeclNGen_2655_ = v_auxDeclNGen_2732_;
v_traceState_2656_ = v_traceState_2733_;
v_messages_2657_ = v_messages_2734_;
v_infoState_2658_ = v_infoState_2735_;
v_snapshotTasks_2659_ = v_snapshotTasks_2736_;
v___y_2660_ = v___y_2697_;
v___y_2661_ = v___y_2698_;
v___y_2662_ = v___y_2711_;
v___y_2663_ = v___y_2699_;
v___y_2664_ = v___y_2700_;
v___y_2665_ = v___y_2701_;
v___y_2666_ = v___x_2740_;
v___y_2667_ = v___y_2703_;
v___y_2668_ = v___y_2702_;
v___y_2669_ = v___y_2705_;
v___y_2670_ = v___y_2707_;
v___y_2671_ = v___y_2708_;
v___y_2672_ = v___y_2709_;
v___y_2673_ = v___x_2753_;
goto v___jp_2640_;
}
}
}
}
}
v___jp_2758_:
{
if (v___y_2784_ == 0)
{
lean_object* v___x_2785_; lean_object* v_env_2786_; lean_object* v_nextMacroScope_2787_; lean_object* v_ngen_2788_; lean_object* v_auxDeclNGen_2789_; lean_object* v_traceState_2790_; lean_object* v_messages_2791_; lean_object* v_infoState_2792_; lean_object* v_snapshotTasks_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2802_; 
v___x_2785_ = lean_st_ref_take(v___y_2770_);
v_env_2786_ = lean_ctor_get(v___x_2785_, 0);
v_nextMacroScope_2787_ = lean_ctor_get(v___x_2785_, 1);
v_ngen_2788_ = lean_ctor_get(v___x_2785_, 2);
v_auxDeclNGen_2789_ = lean_ctor_get(v___x_2785_, 3);
v_traceState_2790_ = lean_ctor_get(v___x_2785_, 4);
v_messages_2791_ = lean_ctor_get(v___x_2785_, 6);
v_infoState_2792_ = lean_ctor_get(v___x_2785_, 7);
v_snapshotTasks_2793_ = lean_ctor_get(v___x_2785_, 8);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2802_ == 0)
{
lean_object* v_unused_2803_; 
v_unused_2803_ = lean_ctor_get(v___x_2785_, 5);
lean_dec(v_unused_2803_);
v___x_2795_ = v___x_2785_;
v_isShared_2796_ = v_isSharedCheck_2802_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_snapshotTasks_2793_);
lean_inc(v_infoState_2792_);
lean_inc(v_messages_2791_);
lean_inc(v_traceState_2790_);
lean_inc(v_auxDeclNGen_2789_);
lean_inc(v_ngen_2788_);
lean_inc(v_nextMacroScope_2787_);
lean_inc(v_env_2786_);
lean_dec(v___x_2785_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2802_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2797_; lean_object* v___x_2799_; 
v___x_2797_ = l_Lean_Kernel_enableDiag(v_env_2786_, v___y_2781_);
lean_inc_ref(v___y_2783_);
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 5, v___y_2783_);
lean_ctor_set(v___x_2795_, 0, v___x_2797_);
v___x_2799_ = v___x_2795_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2797_);
lean_ctor_set(v_reuseFailAlloc_2801_, 1, v_nextMacroScope_2787_);
lean_ctor_set(v_reuseFailAlloc_2801_, 2, v_ngen_2788_);
lean_ctor_set(v_reuseFailAlloc_2801_, 3, v_auxDeclNGen_2789_);
lean_ctor_set(v_reuseFailAlloc_2801_, 4, v_traceState_2790_);
lean_ctor_set(v_reuseFailAlloc_2801_, 5, v___y_2783_);
lean_ctor_set(v_reuseFailAlloc_2801_, 6, v_messages_2791_);
lean_ctor_set(v_reuseFailAlloc_2801_, 7, v_infoState_2792_);
lean_ctor_set(v_reuseFailAlloc_2801_, 8, v_snapshotTasks_2793_);
v___x_2799_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
lean_object* v___x_2800_; 
v___x_2800_ = lean_st_ref_set(v___y_2770_, v___x_2799_);
lean_inc(v___y_2770_);
v___y_2686_ = v___y_2759_;
v___y_2687_ = v___y_2760_;
v___y_2688_ = v___y_2761_;
v___y_2689_ = v___y_2762_;
v___y_2690_ = v___y_2763_;
v___y_2691_ = v___y_2764_;
v___y_2692_ = v___y_2766_;
v___y_2693_ = v___y_2765_;
v___y_2694_ = v___y_2767_;
v___y_2695_ = v___y_2769_;
v___y_2696_ = v___y_2768_;
v___y_2697_ = v___y_2771_;
v___y_2698_ = v___y_2770_;
v___y_2699_ = v___y_2773_;
v___y_2700_ = v___y_2774_;
v___y_2701_ = v___y_2775_;
v___y_2702_ = v___y_2776_;
v___y_2703_ = v___y_2777_;
v___y_2704_ = v___y_2778_;
v___y_2705_ = v___y_2779_;
v___y_2706_ = v___y_2781_;
v___y_2707_ = v___y_2780_;
v___y_2708_ = v___y_2782_;
v___y_2709_ = v___y_2783_;
v___y_2710_ = v___y_2772_;
v___y_2711_ = v___y_2770_;
goto v___jp_2685_;
}
}
}
else
{
lean_inc(v___y_2770_);
v___y_2686_ = v___y_2759_;
v___y_2687_ = v___y_2760_;
v___y_2688_ = v___y_2761_;
v___y_2689_ = v___y_2762_;
v___y_2690_ = v___y_2763_;
v___y_2691_ = v___y_2764_;
v___y_2692_ = v___y_2766_;
v___y_2693_ = v___y_2765_;
v___y_2694_ = v___y_2767_;
v___y_2695_ = v___y_2769_;
v___y_2696_ = v___y_2768_;
v___y_2697_ = v___y_2771_;
v___y_2698_ = v___y_2770_;
v___y_2699_ = v___y_2773_;
v___y_2700_ = v___y_2774_;
v___y_2701_ = v___y_2775_;
v___y_2702_ = v___y_2776_;
v___y_2703_ = v___y_2777_;
v___y_2704_ = v___y_2778_;
v___y_2705_ = v___y_2779_;
v___y_2706_ = v___y_2781_;
v___y_2707_ = v___y_2780_;
v___y_2708_ = v___y_2782_;
v___y_2709_ = v___y_2783_;
v___y_2710_ = v___y_2772_;
v___y_2711_ = v___y_2770_;
goto v___jp_2685_;
}
}
v___jp_2807_:
{
lean_object* v___x_2817_; 
if (v_isShared_2486_ == 0)
{
lean_ctor_set_tag(v___x_2485_, 0);
lean_ctor_set(v___x_2485_, 1, v___y_2815_);
lean_ctor_set(v___x_2485_, 0, v___y_2814_);
v___x_2817_ = v___x_2485_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___y_2814_);
lean_ctor_set(v_reuseFailAlloc_2913_, 1, v___y_2815_);
v___x_2817_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v_moduleData_2821_; lean_object* v___x_2822_; uint8_t v___x_2823_; 
v___x_2818_ = lean_box(0);
v___x_2819_ = l_Lean_EnvExtension_setState___redArg(v___y_2812_, v___y_2813_, v___x_2817_, v___x_2818_);
v___x_2820_ = l_Lean_Environment_header(v___x_2819_);
v_moduleData_2821_ = lean_ctor_get(v___x_2820_, 6);
lean_inc_ref(v_moduleData_2821_);
lean_dec_ref(v___x_2820_);
v___x_2822_ = lean_array_get_size(v_moduleData_2821_);
v___x_2823_ = lean_nat_dec_lt(v___y_2809_, v___x_2822_);
if (v___x_2823_ == 0)
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
lean_dec_ref(v_moduleData_2821_);
lean_dec_ref(v___x_2819_);
lean_dec(v___y_2810_);
lean_dec(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec_ref(v___x_2511_);
lean_dec(v_name_2489_);
lean_dec(v_head_2482_);
lean_dec(v_head_2481_);
v___x_2824_ = lean_obj_once(&l_main___closed__21, &l_main___closed__21_once, _init_l_main___closed__21);
v___x_2825_ = l_panic___at___00main_spec__1(v___x_2824_);
return v___x_2825_;
}
else
{
lean_object* v_base_2826_; lean_object* v_private_2827_; lean_object* v_header_2828_; lean_object* v_serverBaseExts_2829_; lean_object* v_checked_2830_; lean_object* v_asyncConstsMap_2831_; lean_object* v_asyncCtx_x3f_2832_; lean_object* v_importRealizationCtx_x3f_2833_; lean_object* v_localRealizationCtxMap_2834_; lean_object* v_allRealizations_2835_; uint8_t v_isExporting_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2911_; 
v_base_2826_ = lean_ctor_get(v___x_2819_, 0);
lean_inc_ref(v_base_2826_);
v_private_2827_ = lean_ctor_get(v_base_2826_, 0);
lean_inc(v_private_2827_);
v_header_2828_ = lean_ctor_get(v_private_2827_, 5);
lean_inc_ref(v_header_2828_);
v_serverBaseExts_2829_ = lean_ctor_get(v___x_2819_, 1);
v_checked_2830_ = lean_ctor_get(v___x_2819_, 2);
v_asyncConstsMap_2831_ = lean_ctor_get(v___x_2819_, 3);
v_asyncCtx_x3f_2832_ = lean_ctor_get(v___x_2819_, 4);
v_importRealizationCtx_x3f_2833_ = lean_ctor_get(v___x_2819_, 5);
v_localRealizationCtxMap_2834_ = lean_ctor_get(v___x_2819_, 6);
v_allRealizations_2835_ = lean_ctor_get(v___x_2819_, 7);
v_isExporting_2836_ = lean_ctor_get_uint8(v___x_2819_, sizeof(void*)*8);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2911_ == 0)
{
lean_object* v_unused_2912_; 
v_unused_2912_ = lean_ctor_get(v___x_2819_, 0);
lean_dec(v_unused_2912_);
v___x_2838_ = v___x_2819_;
v_isShared_2839_ = v_isSharedCheck_2911_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_allRealizations_2835_);
lean_inc(v_localRealizationCtxMap_2834_);
lean_inc(v_importRealizationCtx_x3f_2833_);
lean_inc(v_asyncCtx_x3f_2832_);
lean_inc(v_asyncConstsMap_2831_);
lean_inc(v_checked_2830_);
lean_inc(v_serverBaseExts_2829_);
lean_dec(v___x_2819_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2911_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v_public_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2909_; 
v_public_2840_ = lean_ctor_get(v_base_2826_, 1);
v_isSharedCheck_2909_ = !lean_is_exclusive(v_base_2826_);
if (v_isSharedCheck_2909_ == 0)
{
lean_object* v_unused_2910_; 
v_unused_2910_ = lean_ctor_get(v_base_2826_, 0);
lean_dec(v_unused_2910_);
v___x_2842_ = v_base_2826_;
v_isShared_2843_ = v_isSharedCheck_2909_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_public_2840_);
lean_dec(v_base_2826_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2909_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v_constants_2844_; uint8_t v_quotInit_2845_; lean_object* v_diagnostics_2846_; lean_object* v_const2ModIdx_2847_; lean_object* v_extensions_2848_; lean_object* v_irBaseExts_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2907_; 
v_constants_2844_ = lean_ctor_get(v_private_2827_, 0);
v_quotInit_2845_ = lean_ctor_get_uint8(v_private_2827_, sizeof(void*)*6);
v_diagnostics_2846_ = lean_ctor_get(v_private_2827_, 1);
v_const2ModIdx_2847_ = lean_ctor_get(v_private_2827_, 2);
v_extensions_2848_ = lean_ctor_get(v_private_2827_, 3);
v_irBaseExts_2849_ = lean_ctor_get(v_private_2827_, 4);
v_isSharedCheck_2907_ = !lean_is_exclusive(v_private_2827_);
if (v_isSharedCheck_2907_ == 0)
{
lean_object* v_unused_2908_; 
v_unused_2908_ = lean_ctor_get(v_private_2827_, 5);
lean_dec(v_unused_2908_);
v___x_2851_ = v_private_2827_;
v_isShared_2852_ = v_isSharedCheck_2907_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_irBaseExts_2849_);
lean_inc(v_extensions_2848_);
lean_inc(v_const2ModIdx_2847_);
lean_inc(v_diagnostics_2846_);
lean_inc(v_constants_2844_);
lean_dec(v_private_2827_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2907_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
uint32_t v_trustLevel_2853_; lean_object* v_mainModule_2854_; uint8_t v_isModule_2855_; lean_object* v_regions_2856_; lean_object* v_modules_2857_; lean_object* v_moduleName2Idx_2858_; lean_object* v_importAllModules_2859_; lean_object* v_moduleData_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2905_; 
v_trustLevel_2853_ = lean_ctor_get_uint32(v_header_2828_, sizeof(void*)*7);
v_mainModule_2854_ = lean_ctor_get(v_header_2828_, 0);
v_isModule_2855_ = lean_ctor_get_uint8(v_header_2828_, sizeof(void*)*7 + 4);
v_regions_2856_ = lean_ctor_get(v_header_2828_, 2);
v_modules_2857_ = lean_ctor_get(v_header_2828_, 3);
v_moduleName2Idx_2858_ = lean_ctor_get(v_header_2828_, 4);
v_importAllModules_2859_ = lean_ctor_get(v_header_2828_, 5);
v_moduleData_2860_ = lean_ctor_get(v_header_2828_, 6);
v_isSharedCheck_2905_ = !lean_is_exclusive(v_header_2828_);
if (v_isSharedCheck_2905_ == 0)
{
lean_object* v_unused_2906_; 
v_unused_2906_ = lean_ctor_get(v_header_2828_, 1);
lean_dec(v_unused_2906_);
v___x_2862_ = v_header_2828_;
v_isShared_2863_ = v_isSharedCheck_2905_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_moduleData_2860_);
lean_inc(v_importAllModules_2859_);
lean_inc(v_moduleName2Idx_2858_);
lean_inc(v_modules_2857_);
lean_inc(v_regions_2856_);
lean_inc(v_mainModule_2854_);
lean_dec(v_header_2828_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2905_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2864_; lean_object* v_imports_2865_; lean_object* v___x_2867_; 
v___x_2864_ = lean_array_fget(v_moduleData_2821_, v___y_2809_);
lean_dec_ref(v_moduleData_2821_);
v_imports_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc_ref(v_imports_2865_);
lean_dec(v___x_2864_);
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 1, v_imports_2865_);
v___x_2867_ = v___x_2862_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 7, 5);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_mainModule_2854_);
lean_ctor_set(v_reuseFailAlloc_2904_, 1, v_imports_2865_);
lean_ctor_set(v_reuseFailAlloc_2904_, 2, v_regions_2856_);
lean_ctor_set(v_reuseFailAlloc_2904_, 3, v_modules_2857_);
lean_ctor_set(v_reuseFailAlloc_2904_, 4, v_moduleName2Idx_2858_);
lean_ctor_set(v_reuseFailAlloc_2904_, 5, v_importAllModules_2859_);
lean_ctor_set(v_reuseFailAlloc_2904_, 6, v_moduleData_2860_);
lean_ctor_set_uint32(v_reuseFailAlloc_2904_, sizeof(void*)*7, v_trustLevel_2853_);
lean_ctor_set_uint8(v_reuseFailAlloc_2904_, sizeof(void*)*7 + 4, v_isModule_2855_);
v___x_2867_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
lean_object* v___x_2869_; 
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 5, v___x_2867_);
v___x_2869_ = v___x_2851_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_constants_2844_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_diagnostics_2846_);
lean_ctor_set(v_reuseFailAlloc_2903_, 2, v_const2ModIdx_2847_);
lean_ctor_set(v_reuseFailAlloc_2903_, 3, v_extensions_2848_);
lean_ctor_set(v_reuseFailAlloc_2903_, 4, v_irBaseExts_2849_);
lean_ctor_set(v_reuseFailAlloc_2903_, 5, v___x_2867_);
lean_ctor_set_uint8(v_reuseFailAlloc_2903_, sizeof(void*)*6, v_quotInit_2845_);
v___x_2869_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
lean_object* v___x_2871_; 
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v___x_2869_);
v___x_2871_ = v___x_2842_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2869_);
lean_ctor_set(v_reuseFailAlloc_2902_, 1, v_public_2840_);
v___x_2871_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
lean_object* v___x_2873_; 
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 0, v___x_2871_);
v___x_2873_ = v___x_2838_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2871_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v_serverBaseExts_2829_);
lean_ctor_set(v_reuseFailAlloc_2901_, 2, v_checked_2830_);
lean_ctor_set(v_reuseFailAlloc_2901_, 3, v_asyncConstsMap_2831_);
lean_ctor_set(v_reuseFailAlloc_2901_, 4, v_asyncCtx_x3f_2832_);
lean_ctor_set(v_reuseFailAlloc_2901_, 5, v_importRealizationCtx_x3f_2833_);
lean_ctor_set(v_reuseFailAlloc_2901_, 6, v_localRealizationCtxMap_2834_);
lean_ctor_set(v_reuseFailAlloc_2901_, 7, v_allRealizations_2835_);
lean_ctor_set_uint8(v_reuseFailAlloc_2901_, sizeof(void*)*8, v_isExporting_2836_);
v___x_2873_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; uint8_t v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v_env_2897_; lean_object* v___x_2898_; uint8_t v___x_2899_; uint8_t v___x_2900_; 
v___x_2874_ = l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
v___x_2875_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2505_, v___x_2874_, v___x_2873_, v___y_2809_, v___y_2811_);
lean_dec(v___y_2809_);
v___x_2876_ = l_Lean_firstFrontendMacroScope;
v___x_2877_ = lean_obj_once(&l_main___closed__22, &l_main___closed__22_once, _init_l_main___closed__22);
v___x_2878_ = ((lean_object*)(l_main___closed__25));
lean_inc(v___y_2810_);
v___x_2879_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2879_, 0, v___y_2810_);
lean_ctor_set(v___x_2879_, 1, v___x_2806_);
lean_ctor_set(v___x_2879_, 2, v___x_2496_);
v___x_2880_ = lean_obj_once(&l_main___closed__26, &l_main___closed__26_once, _init_l_main___closed__26);
v___x_2881_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_2882_ = lean_obj_once(&l_main___closed__30, &l_main___closed__30_once, _init_l_main___closed__30);
v___x_2883_ = lean_obj_once(&l_main___closed__31, &l_main___closed__31_once, _init_l_main___closed__31);
v___x_2884_ = ((lean_object*)(l_main___closed__32));
lean_inc_ref(v___x_2879_);
v___x_2885_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2873_);
lean_ctor_set(v___x_2885_, 1, v___x_2877_);
lean_ctor_set(v___x_2885_, 2, v___x_2878_);
lean_ctor_set(v___x_2885_, 3, v___x_2879_);
lean_ctor_set(v___x_2885_, 4, v___x_2880_);
lean_ctor_set(v___x_2885_, 5, v___x_2881_);
lean_ctor_set(v___x_2885_, 6, v___x_2882_);
lean_ctor_set(v___x_2885_, 7, v___x_2883_);
lean_ctor_set(v___x_2885_, 8, v___x_2884_);
v___x_2886_ = lean_st_mk_ref(v___x_2885_);
v___x_2887_ = l_Lean_inheritedTraceOptions;
v___x_2888_ = lean_st_ref_get(v___x_2887_);
v___x_2889_ = lean_st_ref_get(v___x_2886_);
v___x_2890_ = l_Lean_instInhabitedFileMap_default;
v___x_2891_ = lean_unsigned_to_nat(1000u);
v___x_2892_ = lean_box(0);
v___x_2893_ = l_Lean_Core_getMaxHeartbeats(v___x_2511_);
v___x_2894_ = 0;
v___x_2895_ = lean_box(0);
lean_inc_n(v___y_2810_, 2);
lean_inc_ref(v___x_2511_);
lean_inc(v_head_2481_);
v___x_2896_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2896_, 0, v_head_2481_);
lean_ctor_set(v___x_2896_, 1, v___x_2890_);
lean_ctor_set(v___x_2896_, 2, v___x_2511_);
lean_ctor_set(v___x_2896_, 3, v___x_2510_);
lean_ctor_set(v___x_2896_, 4, v___x_2891_);
lean_ctor_set(v___x_2896_, 5, v___x_2892_);
lean_ctor_set(v___x_2896_, 6, v___y_2810_);
lean_ctor_set(v___x_2896_, 7, v___x_2496_);
lean_ctor_set(v___x_2896_, 8, v___x_2510_);
lean_ctor_set(v___x_2896_, 9, v___x_2893_);
lean_ctor_set(v___x_2896_, 10, v___y_2810_);
lean_ctor_set(v___x_2896_, 11, v___x_2876_);
lean_ctor_set(v___x_2896_, 12, v___x_2895_);
lean_ctor_set(v___x_2896_, 13, v___x_2888_);
lean_ctor_set_uint8(v___x_2896_, sizeof(void*)*14, v___x_2894_);
lean_ctor_set_uint8(v___x_2896_, sizeof(void*)*14 + 1, v___x_2894_);
v_env_2897_ = lean_ctor_get(v___x_2889_, 0);
lean_inc_ref(v_env_2897_);
lean_dec(v___x_2889_);
v___x_2898_ = l_Lean_diagnostics;
v___x_2899_ = l_Lean_Option_get___at___00main_spec__6(v___x_2511_, v___x_2898_);
v___x_2900_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2897_);
lean_dec_ref(v_env_2897_);
if (v___x_2900_ == 0)
{
if (v___x_2899_ == 0)
{
v___y_2759_ = v___x_2890_;
v___y_2760_ = v___y_2808_;
v___y_2761_ = v___x_2876_;
v___y_2762_ = v___x_2895_;
v___y_2763_ = v___x_2887_;
v___y_2764_ = v___x_2823_;
v___y_2765_ = v___x_2894_;
v___y_2766_ = v___x_2892_;
v___y_2767_ = v___x_2881_;
v___y_2768_ = v___x_2496_;
v___y_2769_ = v___x_2898_;
v___y_2770_ = v___x_2886_;
v___y_2771_ = v___x_2880_;
v___y_2772_ = v___x_2896_;
v___y_2773_ = v___y_2810_;
v___y_2774_ = v___x_2883_;
v___y_2775_ = v___x_2875_;
v___y_2776_ = v___x_2884_;
v___y_2777_ = v___x_2878_;
v___y_2778_ = v___x_2874_;
v___y_2779_ = v___x_2879_;
v___y_2780_ = v___x_2877_;
v___y_2781_ = v___x_2899_;
v___y_2782_ = v___x_2882_;
v___y_2783_ = v___x_2881_;
v___y_2784_ = v___x_2823_;
goto v___jp_2758_;
}
else
{
v___y_2759_ = v___x_2890_;
v___y_2760_ = v___y_2808_;
v___y_2761_ = v___x_2876_;
v___y_2762_ = v___x_2895_;
v___y_2763_ = v___x_2887_;
v___y_2764_ = v___x_2823_;
v___y_2765_ = v___x_2894_;
v___y_2766_ = v___x_2892_;
v___y_2767_ = v___x_2881_;
v___y_2768_ = v___x_2496_;
v___y_2769_ = v___x_2898_;
v___y_2770_ = v___x_2886_;
v___y_2771_ = v___x_2880_;
v___y_2772_ = v___x_2896_;
v___y_2773_ = v___y_2810_;
v___y_2774_ = v___x_2883_;
v___y_2775_ = v___x_2875_;
v___y_2776_ = v___x_2884_;
v___y_2777_ = v___x_2878_;
v___y_2778_ = v___x_2874_;
v___y_2779_ = v___x_2879_;
v___y_2780_ = v___x_2877_;
v___y_2781_ = v___x_2899_;
v___y_2782_ = v___x_2882_;
v___y_2783_ = v___x_2881_;
v___y_2784_ = v___x_2900_;
goto v___jp_2758_;
}
}
else
{
v___y_2759_ = v___x_2890_;
v___y_2760_ = v___y_2808_;
v___y_2761_ = v___x_2876_;
v___y_2762_ = v___x_2895_;
v___y_2763_ = v___x_2887_;
v___y_2764_ = v___x_2823_;
v___y_2765_ = v___x_2894_;
v___y_2766_ = v___x_2892_;
v___y_2767_ = v___x_2881_;
v___y_2768_ = v___x_2496_;
v___y_2769_ = v___x_2898_;
v___y_2770_ = v___x_2886_;
v___y_2771_ = v___x_2880_;
v___y_2772_ = v___x_2896_;
v___y_2773_ = v___y_2810_;
v___y_2774_ = v___x_2883_;
v___y_2775_ = v___x_2875_;
v___y_2776_ = v___x_2884_;
v___y_2777_ = v___x_2878_;
v___y_2778_ = v___x_2874_;
v___y_2779_ = v___x_2879_;
v___y_2780_ = v___x_2877_;
v___y_2781_ = v___x_2899_;
v___y_2782_ = v___x_2882_;
v___y_2783_ = v___x_2881_;
v___y_2784_ = v___x_2899_;
goto v___jp_2758_;
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
v___jp_2914_:
{
lean_object* v___x_2920_; lean_object* v_toEnvExtension_2921_; lean_object* v_asyncMode_2922_; lean_object* v___x_2923_; lean_object* v_importedEntries_2924_; lean_object* v_state_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; uint8_t v___x_2928_; 
v___x_2920_ = l_Lean_IR_declMapExt;
v_toEnvExtension_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc_ref(v_toEnvExtension_2921_);
v_asyncMode_2922_ = lean_ctor_get(v_toEnvExtension_2921_, 2);
lean_inc(v___y_2918_);
lean_inc_ref(v___y_2919_);
v___x_2923_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2502_, v_toEnvExtension_2921_, v___y_2919_, v_asyncMode_2922_, v___y_2918_);
v_importedEntries_2924_ = lean_ctor_get(v___x_2923_, 0);
lean_inc_ref(v_importedEntries_2924_);
v_state_2925_ = lean_ctor_get(v___x_2923_, 1);
lean_inc(v_state_2925_);
lean_dec(v___x_2923_);
v___x_2926_ = lean_array_get_borrowed(v___x_2503_, v_importedEntries_2924_, v___y_2916_);
v___x_2927_ = lean_array_get_size(v___x_2926_);
v___x_2928_ = lean_nat_dec_lt(v___x_2510_, v___x_2927_);
if (v___x_2928_ == 0)
{
v___y_2808_ = v___y_2915_;
v___y_2809_ = v___y_2916_;
v___y_2810_ = v___y_2918_;
v___y_2811_ = v___y_2917_;
v___y_2812_ = v_toEnvExtension_2921_;
v___y_2813_ = v___y_2919_;
v___y_2814_ = v_importedEntries_2924_;
v___y_2815_ = v_state_2925_;
goto v___jp_2807_;
}
else
{
uint8_t v___x_2929_; 
v___x_2929_ = lean_nat_dec_le(v___x_2927_, v___x_2927_);
if (v___x_2929_ == 0)
{
if (v___x_2928_ == 0)
{
v___y_2808_ = v___y_2915_;
v___y_2809_ = v___y_2916_;
v___y_2810_ = v___y_2918_;
v___y_2811_ = v___y_2917_;
v___y_2812_ = v_toEnvExtension_2921_;
v___y_2813_ = v___y_2919_;
v___y_2814_ = v_importedEntries_2924_;
v___y_2815_ = v_state_2925_;
goto v___jp_2807_;
}
else
{
size_t v___x_2930_; size_t v___x_2931_; lean_object* v___x_2932_; 
v___x_2930_ = ((size_t)0ULL);
v___x_2931_ = lean_usize_of_nat(v___x_2927_);
lean_inc_ref(v___y_2919_);
v___x_2932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_2919_, v___x_2926_, v___x_2930_, v___x_2931_, v_state_2925_);
v___y_2808_ = v___y_2915_;
v___y_2809_ = v___y_2916_;
v___y_2810_ = v___y_2918_;
v___y_2811_ = v___y_2917_;
v___y_2812_ = v_toEnvExtension_2921_;
v___y_2813_ = v___y_2919_;
v___y_2814_ = v_importedEntries_2924_;
v___y_2815_ = v___x_2932_;
goto v___jp_2807_;
}
}
else
{
size_t v___x_2933_; size_t v___x_2934_; lean_object* v___x_2935_; 
v___x_2933_ = ((size_t)0ULL);
v___x_2934_ = lean_usize_of_nat(v___x_2927_);
lean_inc_ref(v___y_2919_);
v___x_2935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_2919_, v___x_2926_, v___x_2933_, v___x_2934_, v_state_2925_);
v___y_2808_ = v___y_2915_;
v___y_2809_ = v___y_2916_;
v___y_2810_ = v___y_2918_;
v___y_2811_ = v___y_2917_;
v___y_2812_ = v_toEnvExtension_2921_;
v___y_2813_ = v___y_2919_;
v___y_2814_ = v_importedEntries_2924_;
v___y_2815_ = v___x_2935_;
goto v___jp_2807_;
}
}
}
v___jp_2936_:
{
uint8_t v___x_2944_; 
v___x_2944_ = lean_nat_dec_lt(v___x_2510_, v___y_2942_);
if (v___x_2944_ == 0)
{
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2938_);
v___y_2915_ = v___y_2937_;
v___y_2916_ = v___y_2939_;
v___y_2917_ = v___y_2941_;
v___y_2918_ = v___y_2940_;
v___y_2919_ = v___y_2943_;
goto v___jp_2914_;
}
else
{
uint8_t v___x_2945_; 
v___x_2945_ = lean_nat_dec_le(v___y_2942_, v___y_2942_);
if (v___x_2945_ == 0)
{
if (v___x_2944_ == 0)
{
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2938_);
v___y_2915_ = v___y_2937_;
v___y_2916_ = v___y_2939_;
v___y_2917_ = v___y_2941_;
v___y_2918_ = v___y_2940_;
v___y_2919_ = v___y_2943_;
goto v___jp_2914_;
}
else
{
size_t v___x_2946_; size_t v___x_2947_; lean_object* v___x_2948_; 
v___x_2946_ = ((size_t)0ULL);
v___x_2947_ = lean_usize_of_nat(v___y_2942_);
lean_dec(v___y_2942_);
v___x_2948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_2938_, v___x_2946_, v___x_2947_, v___y_2943_);
lean_dec_ref(v___y_2938_);
v___y_2915_ = v___y_2937_;
v___y_2916_ = v___y_2939_;
v___y_2917_ = v___y_2941_;
v___y_2918_ = v___y_2940_;
v___y_2919_ = v___x_2948_;
goto v___jp_2914_;
}
}
else
{
size_t v___x_2949_; size_t v___x_2950_; lean_object* v___x_2951_; 
v___x_2949_ = ((size_t)0ULL);
v___x_2950_ = lean_usize_of_nat(v___y_2942_);
lean_dec(v___y_2942_);
v___x_2951_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_2938_, v___x_2949_, v___x_2950_, v___y_2943_);
lean_dec_ref(v___y_2938_);
v___y_2915_ = v___y_2937_;
v___y_2916_ = v___y_2939_;
v___y_2917_ = v___y_2941_;
v___y_2918_ = v___y_2940_;
v___y_2919_ = v___x_2951_;
goto v___jp_2914_;
}
}
}
v___jp_2952_:
{
lean_object* v___x_2959_; uint8_t v___x_2960_; 
v___x_2959_ = lean_array_get_size(v___y_2958_);
v___x_2960_ = lean_nat_dec_lt(v___x_2510_, v___x_2959_);
if (v___x_2960_ == 0)
{
v___y_2937_ = v___y_2954_;
v___y_2938_ = v___y_2958_;
v___y_2939_ = v___y_2953_;
v___y_2940_ = v___y_2956_;
v___y_2941_ = v___y_2955_;
v___y_2942_ = v___x_2959_;
v___y_2943_ = v___y_2957_;
goto v___jp_2936_;
}
else
{
uint8_t v___x_2961_; 
v___x_2961_ = lean_nat_dec_le(v___x_2959_, v___x_2959_);
if (v___x_2961_ == 0)
{
if (v___x_2960_ == 0)
{
v___y_2937_ = v___y_2954_;
v___y_2938_ = v___y_2958_;
v___y_2939_ = v___y_2953_;
v___y_2940_ = v___y_2956_;
v___y_2941_ = v___y_2955_;
v___y_2942_ = v___x_2959_;
v___y_2943_ = v___y_2957_;
goto v___jp_2936_;
}
else
{
size_t v___x_2962_; size_t v___x_2963_; lean_object* v___x_2964_; 
v___x_2962_ = ((size_t)0ULL);
v___x_2963_ = lean_usize_of_nat(v___x_2959_);
v___x_2964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_2958_, v___x_2962_, v___x_2963_, v___y_2957_);
v___y_2937_ = v___y_2954_;
v___y_2938_ = v___y_2958_;
v___y_2939_ = v___y_2953_;
v___y_2940_ = v___y_2956_;
v___y_2941_ = v___y_2955_;
v___y_2942_ = v___x_2959_;
v___y_2943_ = v___x_2964_;
goto v___jp_2936_;
}
}
else
{
size_t v___x_2965_; size_t v___x_2966_; lean_object* v___x_2967_; 
v___x_2965_ = ((size_t)0ULL);
v___x_2966_ = lean_usize_of_nat(v___x_2959_);
v___x_2967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_2958_, v___x_2965_, v___x_2966_, v___y_2957_);
v___y_2937_ = v___y_2954_;
v___y_2938_ = v___y_2958_;
v___y_2939_ = v___y_2953_;
v___y_2940_ = v___y_2956_;
v___y_2941_ = v___y_2955_;
v___y_2942_ = v___x_2959_;
v___y_2943_ = v___x_2967_;
goto v___jp_2936_;
}
}
}
v___jp_2971_:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___f_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2973_ = l_Lean_instInhabitedImportState_default;
v___x_2974_ = lean_box(v___x_2970_);
v___x_2975_ = lean_box(v___y_2972_);
v___x_2976_ = lean_box(v___x_2507_);
lean_inc_ref(v___x_2511_);
lean_inc(v_name_2489_);
v___f_2977_ = lean_alloc_closure((void*)(l_main___lam__0___boxed), 9, 8);
lean_closure_set(v___f_2977_, 0, v___x_2973_);
lean_closure_set(v___f_2977_, 1, v___x_2969_);
lean_closure_set(v___f_2977_, 2, v___x_2974_);
lean_closure_set(v___f_2977_, 3, v___x_2504_);
lean_closure_set(v___f_2977_, 4, v___x_2975_);
lean_closure_set(v___f_2977_, 5, v_name_2489_);
lean_closure_set(v___f_2977_, 6, v___x_2511_);
lean_closure_set(v___f_2977_, 7, v___x_2976_);
v___x_2978_ = lean_alloc_closure((void*)(l_Lean_withImporting___boxed), 3, 2);
lean_closure_set(v___x_2978_, 0, lean_box(0));
lean_closure_set(v___x_2978_, 1, v___f_2977_);
v___x_2979_ = lean_box(0);
v___x_2980_ = l_Lean_profileitIOUnsafe___redArg(v___x_2804_, v___x_2511_, v___x_2978_, v___x_2979_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v___x_2982_; lean_object* v_ext_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref(v___x_2980_);
v___x_2982_ = l_Lean_Compiler_CSimp_ext;
v_ext_2983_ = lean_ctor_get(v___x_2982_, 1);
lean_inc_ref(v_ext_2983_);
lean_inc(v_name_2489_);
v___x_2984_ = l_Lean_Environment_setMainModule(v_a_2981_, v_name_2489_);
v___x_2985_ = l_main___elam__0___redArg(v___x_2979_, v___x_2498_, v_ext_2983_, v___x_2984_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2986_; lean_object* v___x_2987_; lean_object* v_ext_2988_; lean_object* v___x_2989_; 
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc(v_a_2986_);
lean_dec_ref(v___x_2985_);
v___x_2987_ = l_Lean_Meta_instanceExtension;
v_ext_2988_ = lean_ctor_get(v___x_2987_, 1);
lean_inc_ref(v_ext_2988_);
v___x_2989_ = l_main___elam__0___redArg(v___x_2979_, v___x_2498_, v_ext_2988_, v_a_2986_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_a_2990_);
lean_dec_ref(v___x_2989_);
v___x_2991_ = l_Lean_classExtension;
v___x_2992_ = l_main___elam__0___redArg(v___x_2979_, v___x_2499_, v___x_2991_, v_a_2990_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
lean_inc(v_a_2993_);
lean_dec_ref(v___x_2992_);
v___x_2994_ = l_Lean_Meta_Match_Extension_extension;
v___x_2995_ = l_main___elam__0___redArg(v___x_2979_, v___x_2500_, v___x_2994_, v_a_2993_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3024_; 
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_2998_ = v___x_2995_;
v_isShared_2999_ = v_isSharedCheck_3024_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2995_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3024_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3000_; 
v___x_3000_ = l_Lean_Environment_getModuleIdx_x3f(v_a_2996_, v_name_2489_);
if (lean_obj_tag(v___x_3000_) == 1)
{
lean_object* v_val_3001_; lean_object* v___x_3002_; uint8_t v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; uint8_t v___x_3007_; 
lean_del_object(v___x_2998_);
v_val_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_val_3001_);
lean_dec_ref(v___x_3000_);
v___x_3002_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_3003_ = 0;
v___x_3004_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2501_, v___x_3002_, v_a_2996_, v_val_3001_, v___x_3003_);
v___x_3005_ = lean_array_get_size(v___x_3004_);
v___x_3006_ = ((lean_object*)(l_main___closed__33));
v___x_3007_ = lean_nat_dec_lt(v___x_2510_, v___x_3005_);
if (v___x_3007_ == 0)
{
lean_dec_ref(v___x_3004_);
v___y_2953_ = v_val_3001_;
v___y_2954_ = v___x_2979_;
v___y_2955_ = v___x_3003_;
v___y_2956_ = v___x_2979_;
v___y_2957_ = v_a_2996_;
v___y_2958_ = v___x_3006_;
goto v___jp_2952_;
}
else
{
uint8_t v___x_3008_; 
v___x_3008_ = lean_nat_dec_le(v___x_3005_, v___x_3005_);
if (v___x_3008_ == 0)
{
if (v___x_3007_ == 0)
{
lean_dec_ref(v___x_3004_);
v___y_2953_ = v_val_3001_;
v___y_2954_ = v___x_2979_;
v___y_2955_ = v___x_3003_;
v___y_2956_ = v___x_2979_;
v___y_2957_ = v_a_2996_;
v___y_2958_ = v___x_3006_;
goto v___jp_2952_;
}
else
{
size_t v___x_3009_; size_t v___x_3010_; lean_object* v___x_3011_; 
v___x_3009_ = ((size_t)0ULL);
v___x_3010_ = lean_usize_of_nat(v___x_3005_);
lean_inc(v_a_2996_);
v___x_3011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_2996_, v___x_3004_, v___x_3009_, v___x_3010_, v___x_3006_);
lean_dec_ref(v___x_3004_);
v___y_2953_ = v_val_3001_;
v___y_2954_ = v___x_2979_;
v___y_2955_ = v___x_3003_;
v___y_2956_ = v___x_2979_;
v___y_2957_ = v_a_2996_;
v___y_2958_ = v___x_3011_;
goto v___jp_2952_;
}
}
else
{
size_t v___x_3012_; size_t v___x_3013_; lean_object* v___x_3014_; 
v___x_3012_ = ((size_t)0ULL);
v___x_3013_ = lean_usize_of_nat(v___x_3005_);
lean_inc(v_a_2996_);
v___x_3014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_2996_, v___x_3004_, v___x_3012_, v___x_3013_, v___x_3006_);
lean_dec_ref(v___x_3004_);
v___y_2953_ = v_val_3001_;
v___y_2954_ = v___x_2979_;
v___y_2955_ = v___x_3003_;
v___y_2956_ = v___x_2979_;
v___y_2957_ = v_a_2996_;
v___y_2958_ = v___x_3014_;
goto v___jp_2952_;
}
}
}
else
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3022_; 
lean_dec(v___x_3000_);
lean_dec(v_a_2996_);
lean_dec_ref(v___x_2511_);
lean_del_object(v___x_2485_);
lean_dec(v_head_2482_);
lean_dec(v_head_2481_);
v___x_3015_ = ((lean_object*)(l_main___closed__34));
v___x_3016_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2489_, v___x_2507_);
v___x_3017_ = lean_string_append(v___x_3015_, v___x_3016_);
lean_dec_ref(v___x_3016_);
v___x_3018_ = ((lean_object*)(l_main___closed__35));
v___x_3019_ = lean_string_append(v___x_3017_, v___x_3018_);
v___x_3020_ = lean_mk_io_user_error(v___x_3019_);
if (v_isShared_2999_ == 0)
{
lean_ctor_set_tag(v___x_2998_, 1);
lean_ctor_set(v___x_2998_, 0, v___x_3020_);
v___x_3022_ = v___x_2998_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v___x_3020_);
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
else
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
lean_dec_ref(v___x_2511_);
lean_dec(v_name_2489_);
lean_del_object(v___x_2485_);
lean_dec(v_head_2482_);
lean_dec(v_head_2481_);
v_a_3025_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_2995_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_2995_);
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
else
{
lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3040_; 
lean_dec_ref(v___x_2511_);
lean_dec(v_name_2489_);
lean_del_object(v___x_2485_);
lean_dec(v_head_2482_);
lean_dec(v_head_2481_);
v_a_3033_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3035_ = v___x_2992_;
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_dec(v___x_2992_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3038_; 
if (v_isShared_3036_ == 0)
{
v___x_3038_ = v___x_3035_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_a_3033_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
else
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3048_; 
lean_dec_ref(v___x_2511_);
lean_dec(v_name_2489_);
lean_del_object(v___x_2485_);
lean_dec(v_head_2482_);
lean_dec(v_head_2481_);
v_a_3041_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3043_ = v___x_2989_;
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_2989_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3046_; 
if (v_isShared_3044_ == 0)
{
v___x_3046_ = v___x_3043_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3041_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
else
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
lean_dec_ref(v___x_2511_);
lean_dec(v_name_2489_);
lean_del_object(v___x_2485_);
lean_dec(v_head_2482_);
lean_dec(v_head_2481_);
v_a_3049_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v___x_2985_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_2985_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
else
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3064_; 
lean_dec_ref(v___x_2511_);
lean_dec(v_name_2489_);
lean_del_object(v___x_2485_);
lean_dec(v_head_2482_);
lean_dec(v_head_2481_);
v_a_3057_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3059_ = v___x_2980_;
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_2980_);
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
else
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
lean_dec(v_a_2493_);
lean_dec(v_name_2489_);
lean_del_object(v___x_2485_);
lean_dec(v_head_2482_);
lean_dec(v_head_2481_);
v_a_3067_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3069_ = v___x_2497_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_2497_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3067_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
else
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
lean_dec(v_a_2493_);
lean_dec(v_name_2489_);
lean_del_object(v___x_2485_);
lean_dec(v_head_2482_);
lean_dec(v_head_2481_);
v_a_3075_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3077_ = v___x_2494_;
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_2494_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3078_ == 0)
{
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3075_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
else
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3090_; 
lean_dec(v_name_2489_);
lean_del_object(v___x_2485_);
lean_dec(v_head_2482_);
lean_dec(v_head_2481_);
v_a_3083_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3085_ = v___x_2492_;
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_2492_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_a_3083_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
else
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
lean_del_object(v___x_2485_);
lean_dec(v_tail_2483_);
lean_dec(v_head_2482_);
lean_dec(v_head_2481_);
v_a_3091_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_2487_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_2487_);
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
else
{
lean_dec_ref(v_tail_2478_);
lean_dec(v_tail_2479_);
lean_dec_ref(v_args_2453_);
goto v___jp_2455_;
}
}
else
{
lean_dec_ref(v_args_2453_);
lean_dec(v_tail_2478_);
goto v___jp_2455_;
}
}
else
{
lean_dec(v_args_2453_);
goto v___jp_2455_;
}
v___jp_2455_:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2456_ = ((lean_object*)(l_main___closed__0));
v___x_2457_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_2456_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2465_; 
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2465_ == 0)
{
lean_object* v_unused_2466_; 
v_unused_2466_ = lean_ctor_get(v___x_2457_, 0);
lean_dec(v_unused_2466_);
v___x_2459_ = v___x_2457_;
v_isShared_2460_ = v_isSharedCheck_2465_;
goto v_resetjp_2458_;
}
else
{
lean_dec(v___x_2457_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2465_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2461_; lean_object* v___x_2463_; 
v___x_2461_ = l_main___boxed__const__1;
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 0, v___x_2461_);
v___x_2463_ = v___x_2459_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v___x_2461_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
v_a_2467_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2457_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2457_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
v___jp_2475_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2477_ = l_panic___at___00main_spec__1(v___x_2476_);
return v___x_2477_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_3100_, lean_object* v_a_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = _lean_main(v_args_3100_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2(lean_object* v_as_3103_, lean_object* v_as_x27_3104_, lean_object* v_b_3105_, lean_object* v_a_3106_){
_start:
{
lean_object* v___x_3108_; 
v___x_3108_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v_as_x27_3104_, v_b_3105_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___boxed(lean_object* v_as_3109_, lean_object* v_as_x27_3110_, lean_object* v_b_3111_, lean_object* v_a_3112_, lean_object* v___y_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l_List_forIn_x27_loop___at___00main_spec__2(v_as_3109_, v_as_x27_3110_, v_b_3111_, v_a_3112_);
lean_dec(v_as_3109_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11(lean_object* v___y_3115_, lean_object* v___y_3116_){
_start:
{
lean_object* v___x_3118_; 
v___x_3118_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg(v___y_3116_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___boxed(lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11(v___y_3119_, v___y_3120_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12(lean_object* v_00_u03b2_3123_, lean_object* v_m_3124_, lean_object* v_a_3125_, lean_object* v_fallback_3126_){
_start:
{
lean_object* v___x_3127_; 
v___x_3127_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12___redArg(v_m_3124_, v_a_3125_, v_fallback_3126_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12___boxed(lean_object* v_00_u03b2_3128_, lean_object* v_m_3129_, lean_object* v_a_3130_, lean_object* v_fallback_3131_){
_start:
{
lean_object* v_res_3132_; 
v_res_3132_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12(v_00_u03b2_3128_, v_m_3129_, v_a_3130_, v_fallback_3131_);
lean_dec(v_fallback_3131_);
lean_dec_ref(v_a_3130_);
lean_dec_ref(v_m_3129_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13(lean_object* v_00_u03b2_3133_, lean_object* v_m_3134_, lean_object* v_a_3135_, lean_object* v_b_3136_){
_start:
{
lean_object* v___x_3137_; 
v___x_3137_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13___redArg(v_m_3134_, v_a_3135_, v_b_3136_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16(lean_object* v_n_3138_, lean_object* v_as_3139_, lean_object* v_lo_3140_, lean_object* v_hi_3141_, lean_object* v_w_3142_, lean_object* v_hlo_3143_, lean_object* v_hhi_3144_){
_start:
{
lean_object* v___x_3145_; 
v___x_3145_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg(v_as_3139_, v_lo_3140_, v_hi_3141_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___boxed(lean_object* v_n_3146_, lean_object* v_as_3147_, lean_object* v_lo_3148_, lean_object* v_hi_3149_, lean_object* v_w_3150_, lean_object* v_hlo_3151_, lean_object* v_hhi_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16(v_n_3146_, v_as_3147_, v_lo_3148_, v_hi_3149_, v_w_3150_, v_hlo_3151_, v_hhi_3152_);
lean_dec(v_hi_3149_);
lean_dec(v_n_3146_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12_spec__13(lean_object* v_00_u03b2_3154_, lean_object* v_a_3155_, lean_object* v_fallback_3156_, lean_object* v_x_3157_){
_start:
{
lean_object* v___x_3158_; 
v___x_3158_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12_spec__13___redArg(v_a_3155_, v_fallback_3156_, v_x_3157_);
return v___x_3158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12_spec__13___boxed(lean_object* v_00_u03b2_3159_, lean_object* v_a_3160_, lean_object* v_fallback_3161_, lean_object* v_x_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12_spec__13(v_00_u03b2_3159_, v_a_3160_, v_fallback_3161_, v_x_3162_);
lean_dec(v_x_3162_);
lean_dec(v_fallback_3161_);
lean_dec_ref(v_a_3160_);
return v_res_3163_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__15(lean_object* v_00_u03b2_3164_, lean_object* v_a_3165_, lean_object* v_x_3166_){
_start:
{
uint8_t v___x_3167_; 
v___x_3167_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__15___redArg(v_a_3165_, v_x_3166_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__15___boxed(lean_object* v_00_u03b2_3168_, lean_object* v_a_3169_, lean_object* v_x_3170_){
_start:
{
uint8_t v_res_3171_; lean_object* v_r_3172_; 
v_res_3171_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__15(v_00_u03b2_3168_, v_a_3169_, v_x_3170_);
lean_dec(v_x_3170_);
lean_dec_ref(v_a_3169_);
v_r_3172_ = lean_box(v_res_3171_);
return v_r_3172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16(lean_object* v_00_u03b2_3173_, lean_object* v_data_3174_){
_start:
{
lean_object* v___x_3175_; 
v___x_3175_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16___redArg(v_data_3174_);
return v___x_3175_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__17(lean_object* v_00_u03b2_3176_, lean_object* v_a_3177_, lean_object* v_b_3178_, lean_object* v_x_3179_){
_start:
{
lean_object* v___x_3180_; 
v___x_3180_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__17___redArg(v_a_3177_, v_b_3178_, v_x_3179_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16_spec__28(lean_object* v_00_u03b2_3181_, lean_object* v_i_3182_, lean_object* v_source_3183_, lean_object* v_target_3184_){
_start:
{
lean_object* v___x_3185_; 
v___x_3185_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16_spec__28___redArg(v_i_3182_, v_source_3183_, v_target_3184_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20_spec__35(uint8_t v___x_3186_, lean_object* v_as_3187_, size_t v_sz_3188_, size_t v_i_3189_, lean_object* v_b_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_){
_start:
{
lean_object* v___x_3194_; 
v___x_3194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20_spec__35___redArg(v___x_3186_, v_as_3187_, v_sz_3188_, v_i_3189_, v_b_3190_, v___y_3191_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20_spec__35___boxed(lean_object* v___x_3195_, lean_object* v_as_3196_, lean_object* v_sz_3197_, lean_object* v_i_3198_, lean_object* v_b_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
uint8_t v___x_40344__boxed_3203_; size_t v_sz_boxed_3204_; size_t v_i_boxed_3205_; lean_object* v_res_3206_; 
v___x_40344__boxed_3203_ = lean_unbox(v___x_3195_);
v_sz_boxed_3204_ = lean_unbox_usize(v_sz_3197_);
lean_dec(v_sz_3197_);
v_i_boxed_3205_ = lean_unbox_usize(v_i_3198_);
lean_dec(v_i_3198_);
v_res_3206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20_spec__35(v___x_40344__boxed_3203_, v_as_3196_, v_sz_boxed_3204_, v_i_boxed_3205_, v_b_3199_, v___y_3200_, v___y_3201_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec_ref(v_as_3196_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16_spec__28_spec__37(lean_object* v_00_u03b2_3207_, lean_object* v_x_3208_, lean_object* v_x_3209_){
_start:
{
lean_object* v___x_3210_; 
v___x_3210_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16_spec__28_spec__37___redArg(v_x_3208_, v_x_3209_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42(uint8_t v___x_3211_, lean_object* v_as_3212_, size_t v_sz_3213_, size_t v_i_3214_, lean_object* v_b_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_){
_start:
{
lean_object* v___x_3219_; 
v___x_3219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42___redArg(v___x_3211_, v_as_3212_, v_sz_3213_, v_i_3214_, v_b_3215_, v___y_3216_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42___boxed(lean_object* v___x_3220_, lean_object* v_as_3221_, lean_object* v_sz_3222_, lean_object* v_i_3223_, lean_object* v_b_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_){
_start:
{
uint8_t v___x_40364__boxed_3228_; size_t v_sz_boxed_3229_; size_t v_i_boxed_3230_; lean_object* v_res_3231_; 
v___x_40364__boxed_3228_ = lean_unbox(v___x_3220_);
v_sz_boxed_3229_ = lean_unbox_usize(v_sz_3222_);
lean_dec(v_sz_3222_);
v_i_boxed_3230_ = lean_unbox_usize(v_i_3223_);
lean_dec(v_i_3223_);
v_res_3231_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42(v___x_40364__boxed_3228_, v_as_3221_, v_sz_boxed_3229_, v_i_boxed_3230_, v_b_3224_, v___y_3225_, v___y_3226_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec_ref(v_as_3221_);
return v_res_3231_;
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
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_LeanIR(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
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
int main(int argc, char ** argv) {
#if defined(WIN32) || defined(_WIN32)
  SetErrorMode(SEM_FAILCRITICALERRORS);
  SetConsoleOutputCP(CP_UTF8);
#endif
  lean_object* in; lean_object* res;
  argv = lean_setup_args(argc, argv);
  lean_initialize();
  res = runtime_initialize_LeanIR(1 /* builtin */);
  lean_io_mark_end_initialization();
  if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
    lean_init_task_manager();
    in = lean_box(0);
    int i = argc;
    while (i > 1) {
      lean_object* n;
      i--;
      n = lean_alloc_ctor(1,2,0); lean_ctor_set(n, 0, lean_mk_string(argv[i])); lean_ctor_set(n, 1, in);
      in = n;
    }
    res = _lean_main(in);
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
