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
uint8_t l_String_instDecidableLtRaw___aux__1(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_ir_export_entries(lean_object*);
lean_object* l_Lean_mkModuleData(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_get_ir_extra_const_names(lean_object*, uint8_t, uint8_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Match_Extension_instInhabitedState;
lean_object* l_IO_println___at___00Lean_Environment_displayStats_spec__1(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedError;
lean_object* l_instInhabitedEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__32(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_panic___at___00main_spec__1___closed__0(void){
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
LEAN_EXPORT lean_object* l_panic___at___00main_spec__1(lean_object* v_msg_302_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_18535__overap_305_; lean_object* v___x_306_; 
v___x_304_ = lean_obj_once(&l_panic___at___00main_spec__1___closed__0, &l_panic___at___00main_spec__1___closed__0_once, _init_l_panic___at___00main_spec__1___closed__0);
v___x_18535__overap_305_ = lean_panic_fn_borrowed(v___x_304_, v_msg_302_);
v___x_306_ = lean_apply_1(v___x_18535__overap_305_, lean_box(0));
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00main_spec__1___boxed(lean_object* v_msg_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_panic___at___00main_spec__1(v_msg_307_);
return v_res_309_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00main_spec__6(lean_object* v_opts_310_, lean_object* v_opt_311_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__6___boxed(lean_object* v_opts_320_, lean_object* v_opt_321_){
_start:
{
uint8_t v_res_322_; lean_object* v_r_323_; 
v_res_322_ = l_Lean_Option_get___at___00main_spec__6(v_opts_320_, v_opt_321_);
lean_dec_ref(v_opt_321_);
lean_dec_ref(v_opts_320_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__7(lean_object* v_opts_324_, lean_object* v_opt_325_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__7___boxed(lean_object* v_opts_332_, lean_object* v_opt_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Option_get___at___00main_spec__7(v_opts_332_, v_opt_333_);
lean_dec_ref(v_opt_333_);
lean_dec_ref(v_opts_332_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5_spec__6(lean_object* v___x_335_, lean_object* v_a_336_, lean_object* v_x_337_){
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
v___x_345_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5_spec__6(v___x_335_, v_a_336_, v_tail_340_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5_spec__6___boxed(lean_object* v___x_387_, lean_object* v_a_388_, lean_object* v_x_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5_spec__6(v___x_387_, v_a_388_, v_x_389_);
lean_dec(v___x_387_);
return v_res_390_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5___closed__0(void){
_start:
{
lean_object* v___x_391_; uint64_t v___x_392_; 
v___x_391_ = lean_unsigned_to_nat(1723u);
v___x_392_ = lean_uint64_of_nat(v___x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5(lean_object* v___x_393_, lean_object* v_m_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_size_396_; lean_object* v_buckets_397_; lean_object* v___x_398_; uint64_t v___y_400_; 
v_size_396_ = lean_ctor_get(v_m_394_, 0);
v_buckets_397_ = lean_ctor_get(v_m_394_, 1);
v___x_398_ = lean_array_get_size(v_buckets_397_);
if (lean_obj_tag(v_a_395_) == 0)
{
uint64_t v___x_427_; 
v___x_427_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5___closed__0);
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
v___x_413_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_a_395_, v_bucket_412_);
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
v_bucket_419_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5_spec__6(v___x_393_, v_a_395_, v_bucket_412_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5___boxed(lean_object* v___x_429_, lean_object* v_m_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5(v___x_429_, v_m_430_, v_a_431_);
lean_dec(v___x_429_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_main___lam__0(lean_object* v___x_433_, lean_object* v___x_434_, uint8_t v___x_435_, lean_object* v___x_436_, uint8_t v___y_437_, lean_object* v_name_438_, lean_object* v___x_439_, uint8_t v___x_440_){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_st_mk_ref(v___x_433_);
v___x_443_ = l_Lean_importModulesCore(v___x_434_, v___x_435_, v___x_436_, v___y_437_, v___x_442_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v___x_444_; lean_object* v_moduleNameMap_445_; lean_object* v_moduleNames_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_460_; 
lean_dec_ref(v___x_443_);
v___x_444_ = lean_st_ref_get(v___x_442_);
lean_dec(v___x_442_);
v_moduleNameMap_445_ = lean_ctor_get(v___x_444_, 0);
v_moduleNames_446_ = lean_ctor_get(v___x_444_, 1);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_460_ == 0)
{
v___x_448_ = v___x_444_;
v_isShared_449_ = v_isSharedCheck_460_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_moduleNames_446_);
lean_inc(v_moduleNameMap_445_);
lean_dec(v___x_444_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_460_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v___x_452_; 
lean_inc(v_name_438_);
v___x_450_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__5(v_name_438_, v_moduleNameMap_445_, v_name_438_);
lean_dec(v_name_438_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v___x_450_);
v___x_452_ = v___x_448_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_450_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_moduleNames_446_);
v___x_452_ = v_reuseFailAlloc_459_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
uint32_t v___x_453_; uint8_t v___x_454_; uint8_t v___x_455_; uint8_t v___x_456_; 
v___x_453_ = 0;
v___x_454_ = 0;
v___x_455_ = 0;
v___x_456_ = l_Lean_instDecidableEqOLeanLevel(v___x_455_, v___x_435_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_finalizeImport(v___x_452_, v___x_434_, v___x_439_, v___x_453_, v___x_440_, v___x_454_, v___x_455_, v___x_440_);
lean_dec_ref(v___x_452_);
return v___x_457_;
}
else
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_finalizeImport(v___x_452_, v___x_434_, v___x_439_, v___x_453_, v___x_440_, v___x_454_, v___x_455_, v___x_454_);
lean_dec_ref(v___x_452_);
return v___x_458_;
}
}
}
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
lean_dec(v___x_442_);
lean_dec_ref(v___x_439_);
lean_dec(v_name_438_);
lean_dec_ref(v___x_434_);
v_a_461_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_443_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_443_);
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
LEAN_EXPORT lean_object* l_main___lam__0___boxed(lean_object* v___x_469_, lean_object* v___x_470_, lean_object* v___x_471_, lean_object* v___x_472_, lean_object* v___y_473_, lean_object* v_name_474_, lean_object* v___x_475_, lean_object* v___x_476_, lean_object* v___y_477_){
_start:
{
uint8_t v___x_32147__boxed_478_; uint8_t v___y_32149__boxed_479_; uint8_t v___x_32151__boxed_480_; lean_object* v_res_481_; 
v___x_32147__boxed_478_ = lean_unbox(v___x_471_);
v___y_32149__boxed_479_ = lean_unbox(v___y_473_);
v___x_32151__boxed_480_ = lean_unbox(v___x_476_);
v_res_481_ = l_main___lam__0(v___x_469_, v___x_470_, v___x_32147__boxed_478_, v___x_472_, v___y_32149__boxed_479_, v_name_474_, v___x_475_, v___x_32151__boxed_480_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_main___lam__1(lean_object* v___x_483_, lean_object* v___x_484_, lean_object* v___x_485_, lean_object* v___x_486_, lean_object* v___x_487_, lean_object* v_name_488_, lean_object* v_a_489_, lean_object* v___x_490_, lean_object* v_head_491_, lean_object* v___x_492_, lean_object* v___x_493_, lean_object* v___x_494_, lean_object* v___x_495_, lean_object* v___x_496_, lean_object* v___x_497_, lean_object* v___x_498_, lean_object* v___x_499_, uint8_t v___x_500_, uint8_t v___x_501_){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v_env_507_; uint8_t v___x_508_; lean_object* v_fileName_510_; lean_object* v_fileMap_511_; lean_object* v_currRecDepth_512_; lean_object* v_ref_513_; lean_object* v_currNamespace_514_; lean_object* v_openDecls_515_; lean_object* v_initHeartbeats_516_; lean_object* v_maxHeartbeats_517_; lean_object* v_quotContext_518_; lean_object* v_currMacroScope_519_; lean_object* v_cancelTk_x3f_520_; uint8_t v_suppressElabErrors_521_; lean_object* v_inheritedTraceOptions_522_; lean_object* v___y_523_; uint8_t v___y_551_; uint8_t v___x_571_; 
v___x_503_ = lean_io_get_num_heartbeats();
v___x_504_ = lean_st_mk_ref(v___x_483_);
v___x_505_ = lean_st_ref_get(v___x_484_);
v___x_506_ = lean_st_ref_get(v___x_504_);
v_env_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc_ref(v_env_507_);
lean_dec(v___x_506_);
v___x_508_ = l_Lean_Option_get___at___00main_spec__6(v___x_485_, v___x_486_);
v___x_571_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_507_);
lean_dec_ref(v_env_507_);
if (v___x_571_ == 0)
{
if (v___x_508_ == 0)
{
v___y_551_ = v___x_501_;
goto v___jp_550_;
}
else
{
v___y_551_ = v___x_571_;
goto v___jp_550_;
}
}
else
{
v___y_551_ = v___x_508_;
goto v___jp_550_;
}
v___jp_509_:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_524_ = l_Lean_Option_get___at___00main_spec__7(v___x_485_, v___x_487_);
v___x_525_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_525_, 0, v_fileName_510_);
lean_ctor_set(v___x_525_, 1, v_fileMap_511_);
lean_ctor_set(v___x_525_, 2, v___x_485_);
lean_ctor_set(v___x_525_, 3, v_currRecDepth_512_);
lean_ctor_set(v___x_525_, 4, v___x_524_);
lean_ctor_set(v___x_525_, 5, v_ref_513_);
lean_ctor_set(v___x_525_, 6, v_currNamespace_514_);
lean_ctor_set(v___x_525_, 7, v_openDecls_515_);
lean_ctor_set(v___x_525_, 8, v_initHeartbeats_516_);
lean_ctor_set(v___x_525_, 9, v_maxHeartbeats_517_);
lean_ctor_set(v___x_525_, 10, v_quotContext_518_);
lean_ctor_set(v___x_525_, 11, v_currMacroScope_519_);
lean_ctor_set(v___x_525_, 12, v_cancelTk_x3f_520_);
lean_ctor_set(v___x_525_, 13, v_inheritedTraceOptions_522_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*14, v___x_508_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*14 + 1, v_suppressElabErrors_521_);
v___x_526_ = l_Lean_Compiler_LCNF_emitC(v_name_488_, v___x_525_, v___y_523_);
lean_dec(v___y_523_);
lean_dec_ref(v___x_525_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
lean_dec_ref(v___x_526_);
v___x_528_ = lean_st_ref_get(v___x_504_);
lean_dec(v___x_504_);
lean_dec(v___x_528_);
v___x_529_ = lean_string_to_utf8(v_a_527_);
lean_dec(v_a_527_);
v___x_530_ = lean_io_prim_handle_write(v_a_489_, v___x_529_);
lean_dec_ref(v___x_529_);
return v___x_530_;
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_549_; 
lean_dec(v___x_504_);
v_a_531_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_549_ == 0)
{
v___x_533_ = v___x_526_;
v_isShared_534_ = v_isSharedCheck_549_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_526_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_549_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
if (lean_obj_tag(v_a_531_) == 0)
{
lean_object* v_msg_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_539_; 
v_msg_535_ = lean_ctor_get(v_a_531_, 1);
lean_inc_ref(v_msg_535_);
lean_dec_ref(v_a_531_);
v___x_536_ = l_Lean_MessageData_toString(v_msg_535_);
v___x_537_ = lean_mk_io_user_error(v___x_536_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_537_);
v___x_539_ = v___x_533_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
else
{
lean_object* v_id_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_547_; 
v_id_541_ = lean_ctor_get(v_a_531_, 0);
lean_inc(v_id_541_);
lean_dec_ref(v_a_531_);
v___x_542_ = ((lean_object*)(l_main___lam__1___closed__0));
v___x_543_ = l_Nat_reprFast(v_id_541_);
v___x_544_ = lean_string_append(v___x_542_, v___x_543_);
lean_dec_ref(v___x_543_);
v___x_545_ = lean_mk_io_user_error(v___x_544_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_545_);
v___x_547_ = v___x_533_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_545_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
v___jp_550_:
{
if (v___y_551_ == 0)
{
lean_object* v___x_552_; lean_object* v_env_553_; lean_object* v_nextMacroScope_554_; lean_object* v_ngen_555_; lean_object* v_auxDeclNGen_556_; lean_object* v_traceState_557_; lean_object* v_messages_558_; lean_object* v_infoState_559_; lean_object* v_snapshotTasks_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_569_; 
v___x_552_ = lean_st_ref_take(v___x_504_);
v_env_553_ = lean_ctor_get(v___x_552_, 0);
v_nextMacroScope_554_ = lean_ctor_get(v___x_552_, 1);
v_ngen_555_ = lean_ctor_get(v___x_552_, 2);
v_auxDeclNGen_556_ = lean_ctor_get(v___x_552_, 3);
v_traceState_557_ = lean_ctor_get(v___x_552_, 4);
v_messages_558_ = lean_ctor_get(v___x_552_, 6);
v_infoState_559_ = lean_ctor_get(v___x_552_, 7);
v_snapshotTasks_560_ = lean_ctor_get(v___x_552_, 8);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_569_ == 0)
{
lean_object* v_unused_570_; 
v_unused_570_ = lean_ctor_get(v___x_552_, 5);
lean_dec(v_unused_570_);
v___x_562_ = v___x_552_;
v_isShared_563_ = v_isSharedCheck_569_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_snapshotTasks_560_);
lean_inc(v_infoState_559_);
lean_inc(v_messages_558_);
lean_inc(v_traceState_557_);
lean_inc(v_auxDeclNGen_556_);
lean_inc(v_ngen_555_);
lean_inc(v_nextMacroScope_554_);
lean_inc(v_env_553_);
lean_dec(v___x_552_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_569_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; lean_object* v___x_566_; 
v___x_564_ = l_Lean_Kernel_enableDiag(v_env_553_, v___x_508_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 5, v___x_490_);
lean_ctor_set(v___x_562_, 0, v___x_564_);
v___x_566_ = v___x_562_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_nextMacroScope_554_);
lean_ctor_set(v_reuseFailAlloc_568_, 2, v_ngen_555_);
lean_ctor_set(v_reuseFailAlloc_568_, 3, v_auxDeclNGen_556_);
lean_ctor_set(v_reuseFailAlloc_568_, 4, v_traceState_557_);
lean_ctor_set(v_reuseFailAlloc_568_, 5, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_568_, 6, v_messages_558_);
lean_ctor_set(v_reuseFailAlloc_568_, 7, v_infoState_559_);
lean_ctor_set(v_reuseFailAlloc_568_, 8, v_snapshotTasks_560_);
v___x_566_ = v_reuseFailAlloc_568_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_object* v___x_567_; 
v___x_567_ = lean_st_ref_set(v___x_504_, v___x_566_);
lean_inc(v___x_504_);
lean_inc(v___x_495_);
v_fileName_510_ = v_head_491_;
v_fileMap_511_ = v___x_492_;
v_currRecDepth_512_ = v___x_493_;
v_ref_513_ = v___x_494_;
v_currNamespace_514_ = v___x_495_;
v_openDecls_515_ = v___x_496_;
v_initHeartbeats_516_ = v___x_503_;
v_maxHeartbeats_517_ = v___x_497_;
v_quotContext_518_ = v___x_495_;
v_currMacroScope_519_ = v___x_498_;
v_cancelTk_x3f_520_ = v___x_499_;
v_suppressElabErrors_521_ = v___x_500_;
v_inheritedTraceOptions_522_ = v___x_505_;
v___y_523_ = v___x_504_;
goto v___jp_509_;
}
}
}
else
{
lean_dec_ref(v___x_490_);
lean_inc(v___x_504_);
lean_inc(v___x_495_);
v_fileName_510_ = v_head_491_;
v_fileMap_511_ = v___x_492_;
v_currRecDepth_512_ = v___x_493_;
v_ref_513_ = v___x_494_;
v_currNamespace_514_ = v___x_495_;
v_openDecls_515_ = v___x_496_;
v_initHeartbeats_516_ = v___x_503_;
v_maxHeartbeats_517_ = v___x_497_;
v_quotContext_518_ = v___x_495_;
v_currMacroScope_519_ = v___x_498_;
v_cancelTk_x3f_520_ = v___x_499_;
v_suppressElabErrors_521_ = v___x_500_;
v_inheritedTraceOptions_522_ = v___x_505_;
v___y_523_ = v___x_504_;
goto v___jp_509_;
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__1___boxed(lean_object** _args){
lean_object* v___x_572_ = _args[0];
lean_object* v___x_573_ = _args[1];
lean_object* v___x_574_ = _args[2];
lean_object* v___x_575_ = _args[3];
lean_object* v___x_576_ = _args[4];
lean_object* v_name_577_ = _args[5];
lean_object* v_a_578_ = _args[6];
lean_object* v___x_579_ = _args[7];
lean_object* v_head_580_ = _args[8];
lean_object* v___x_581_ = _args[9];
lean_object* v___x_582_ = _args[10];
lean_object* v___x_583_ = _args[11];
lean_object* v___x_584_ = _args[12];
lean_object* v___x_585_ = _args[13];
lean_object* v___x_586_ = _args[14];
lean_object* v___x_587_ = _args[15];
lean_object* v___x_588_ = _args[16];
lean_object* v___x_589_ = _args[17];
lean_object* v___x_590_ = _args[18];
lean_object* v___y_591_ = _args[19];
_start:
{
uint8_t v___x_32238__boxed_592_; uint8_t v___x_32239__boxed_593_; lean_object* v_res_594_; 
v___x_32238__boxed_592_ = lean_unbox(v___x_589_);
v___x_32239__boxed_593_ = lean_unbox(v___x_590_);
v_res_594_ = l_main___lam__1(v___x_572_, v___x_573_, v___x_574_, v___x_575_, v___x_576_, v_name_577_, v_a_578_, v___x_579_, v_head_580_, v___x_581_, v___x_582_, v___x_583_, v___x_584_, v___x_585_, v___x_586_, v___x_587_, v___x_588_, v___x_32238__boxed_592_, v___x_32239__boxed_593_);
lean_dec(v_a_578_);
lean_dec_ref(v___x_576_);
lean_dec_ref(v___x_575_);
lean_dec(v___x_573_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__3(lean_object* v_x2_595_, lean_object* v_as_596_, size_t v_i_597_, size_t v_stop_598_, lean_object* v_b_599_){
_start:
{
uint8_t v___x_600_; 
v___x_600_ = lean_usize_dec_eq(v_i_597_, v_stop_598_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; lean_object* v___x_602_; size_t v___x_603_; size_t v___x_604_; 
v___x_601_ = lean_array_uget_borrowed(v_as_596_, v_i_597_);
lean_inc_ref(v_x2_595_);
lean_inc(v___x_601_);
v___x_602_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_601_, v_x2_595_, v_b_599_);
v___x_603_ = ((size_t)1ULL);
v___x_604_ = lean_usize_add(v_i_597_, v___x_603_);
v_i_597_ = v___x_604_;
v_b_599_ = v___x_602_;
goto _start;
}
else
{
lean_dec_ref(v_x2_595_);
return v_b_599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__3___boxed(lean_object* v_x2_606_, lean_object* v_as_607_, lean_object* v_i_608_, lean_object* v_stop_609_, lean_object* v_b_610_){
_start:
{
size_t v_i_boxed_611_; size_t v_stop_boxed_612_; lean_object* v_res_613_; 
v_i_boxed_611_ = lean_unbox_usize(v_i_608_);
lean_dec(v_i_608_);
v_stop_boxed_612_ = lean_unbox_usize(v_stop_609_);
lean_dec(v_stop_609_);
v_res_613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__3(v_x2_606_, v_as_607_, v_i_boxed_611_, v_stop_boxed_612_, v_b_610_);
lean_dec_ref(v_as_607_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(lean_object* v_as_614_, size_t v_i_615_, size_t v_stop_616_, lean_object* v_b_617_){
_start:
{
lean_object* v___y_619_; uint8_t v___x_623_; 
v___x_623_ = lean_usize_dec_eq(v_i_615_, v_stop_616_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_624_ = lean_unsigned_to_nat(0u);
v___x_625_ = lean_array_uget_borrowed(v_as_614_, v_i_615_);
v___x_626_ = lean_array_get_size(v___x_625_);
v___x_627_ = lean_nat_dec_lt(v___x_624_, v___x_626_);
if (v___x_627_ == 0)
{
v___y_619_ = v_b_617_;
goto v___jp_618_;
}
else
{
uint8_t v___x_628_; 
v___x_628_ = lean_nat_dec_le(v___x_626_, v___x_626_);
if (v___x_628_ == 0)
{
if (v___x_627_ == 0)
{
v___y_619_ = v_b_617_;
goto v___jp_618_;
}
else
{
size_t v___x_629_; size_t v___x_630_; lean_object* v___x_631_; 
v___x_629_ = ((size_t)0ULL);
v___x_630_ = lean_usize_of_nat(v___x_626_);
lean_inc(v___x_625_);
v___x_631_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__3(v___x_625_, v___x_625_, v___x_629_, v___x_630_, v_b_617_);
v___y_619_ = v___x_631_;
goto v___jp_618_;
}
}
else
{
size_t v___x_632_; size_t v___x_633_; lean_object* v___x_634_; 
v___x_632_ = ((size_t)0ULL);
v___x_633_ = lean_usize_of_nat(v___x_626_);
lean_inc(v___x_625_);
v___x_634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__3(v___x_625_, v___x_625_, v___x_632_, v___x_633_, v_b_617_);
v___y_619_ = v___x_634_;
goto v___jp_618_;
}
}
}
else
{
return v_b_617_;
}
v___jp_618_:
{
size_t v___x_620_; size_t v___x_621_; 
v___x_620_ = ((size_t)1ULL);
v___x_621_ = lean_usize_add(v_i_615_, v___x_620_);
v_i_615_ = v___x_621_;
v_b_617_ = v___y_619_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14___boxed(lean_object* v_as_635_, lean_object* v_i_636_, lean_object* v_stop_637_, lean_object* v_b_638_){
_start:
{
size_t v_i_boxed_639_; size_t v_stop_boxed_640_; lean_object* v_res_641_; 
v_i_boxed_639_ = lean_unbox_usize(v_i_636_);
lean_dec(v_i_636_);
v_stop_boxed_640_ = lean_unbox_usize(v_stop_637_);
lean_dec(v_stop_637_);
v_res_641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v_as_635_, v_i_boxed_639_, v_stop_boxed_640_, v_b_638_);
lean_dec_ref(v_as_635_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__9_spec__20(lean_object* v_s_642_){
_start:
{
lean_object* v___x_644_; lean_object* v_putStr_645_; lean_object* v___x_646_; 
v___x_644_ = lean_get_stderr();
v_putStr_645_ = lean_ctor_get(v___x_644_, 4);
lean_inc_ref(v_putStr_645_);
lean_dec_ref(v___x_644_);
v___x_646_ = lean_apply_2(v_putStr_645_, v_s_642_, lean_box(0));
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__9_spec__20___boxed(lean_object* v_s_647_, lean_object* v_a_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__9_spec__20(v_s_647_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__9(lean_object* v_s_650_){
_start:
{
uint32_t v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_652_ = 10;
v___x_653_ = lean_string_push(v_s_650_, v___x_652_);
v___x_654_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__9_spec__20(v___x_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__9___boxed(lean_object* v_s_655_, lean_object* v_a_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_IO_eprintln___at___00main_spec__9(v_s_655_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__30_spec__43(lean_object* v_as_661_, size_t v_sz_662_, size_t v_i_663_, lean_object* v_b_664_){
_start:
{
uint8_t v___x_666_; 
v___x_666_ = lean_usize_dec_lt(v_i_663_, v_sz_662_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; 
v___x_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_667_, 0, v_b_664_);
return v___x_667_;
}
else
{
uint8_t v___x_668_; lean_object* v_a_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
lean_dec_ref(v_b_664_);
v___x_668_ = 0;
v_a_669_ = lean_array_uget_borrowed(v_as_661_, v_i_663_);
lean_inc(v_a_669_);
v___x_670_ = l_Lean_Message_toString(v_a_669_, v___x_668_);
v___x_671_ = l_IO_eprintln___at___00main_spec__9(v___x_670_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v___x_672_; size_t v___x_673_; size_t v___x_674_; 
lean_dec_ref(v___x_671_);
v___x_672_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__30_spec__43___closed__0));
v___x_673_ = ((size_t)1ULL);
v___x_674_ = lean_usize_add(v_i_663_, v___x_673_);
v_i_663_ = v___x_674_;
v_b_664_ = v___x_672_;
goto _start;
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
v_a_676_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_671_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_671_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__30_spec__43___boxed(lean_object* v_as_684_, lean_object* v_sz_685_, lean_object* v_i_686_, lean_object* v_b_687_, lean_object* v___y_688_){
_start:
{
size_t v_sz_boxed_689_; size_t v_i_boxed_690_; lean_object* v_res_691_; 
v_sz_boxed_689_ = lean_unbox_usize(v_sz_685_);
lean_dec(v_sz_685_);
v_i_boxed_690_ = lean_unbox_usize(v_i_686_);
lean_dec(v_i_686_);
v_res_691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__30_spec__43(v_as_684_, v_sz_boxed_689_, v_i_boxed_690_, v_b_687_);
lean_dec_ref(v_as_684_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__30(lean_object* v_as_692_, size_t v_sz_693_, size_t v_i_694_, lean_object* v_b_695_){
_start:
{
uint8_t v___x_697_; 
v___x_697_ = lean_usize_dec_lt(v_i_694_, v_sz_693_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; 
v___x_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_698_, 0, v_b_695_);
return v___x_698_;
}
else
{
uint8_t v___x_699_; lean_object* v_a_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
lean_dec_ref(v_b_695_);
v___x_699_ = 0;
v_a_700_ = lean_array_uget_borrowed(v_as_692_, v_i_694_);
lean_inc(v_a_700_);
v___x_701_ = l_Lean_Message_toString(v_a_700_, v___x_699_);
v___x_702_ = l_IO_eprintln___at___00main_spec__9(v___x_701_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v___x_703_; size_t v___x_704_; size_t v___x_705_; lean_object* v___x_706_; 
lean_dec_ref(v___x_702_);
v___x_703_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__30_spec__43___closed__0));
v___x_704_ = ((size_t)1ULL);
v___x_705_ = lean_usize_add(v_i_694_, v___x_704_);
v___x_706_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__30_spec__43(v_as_692_, v_sz_693_, v___x_705_, v___x_703_);
return v___x_706_;
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
v_a_707_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_702_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_702_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__30___boxed(lean_object* v_as_715_, lean_object* v_sz_716_, lean_object* v_i_717_, lean_object* v_b_718_, lean_object* v___y_719_){
_start:
{
size_t v_sz_boxed_720_; size_t v_i_boxed_721_; lean_object* v_res_722_; 
v_sz_boxed_720_ = lean_unbox_usize(v_sz_716_);
lean_dec(v_sz_716_);
v_i_boxed_721_ = lean_unbox_usize(v_i_717_);
lean_dec(v_i_717_);
v_res_722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__30(v_as_715_, v_sz_boxed_720_, v_i_boxed_721_, v_b_718_);
lean_dec_ref(v_as_715_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22(lean_object* v_init_723_, lean_object* v_n_724_, lean_object* v_b_725_){
_start:
{
if (lean_obj_tag(v_n_724_) == 0)
{
lean_object* v_cs_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_761_; 
v_cs_727_ = lean_ctor_get(v_n_724_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v_n_724_);
if (v_isSharedCheck_761_ == 0)
{
v___x_729_ = v_n_724_;
v_isShared_730_ = v_isSharedCheck_761_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_cs_727_);
lean_dec(v_n_724_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_761_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; lean_object* v___x_732_; size_t v_sz_733_; size_t v___x_734_; lean_object* v___x_735_; 
v___x_731_ = lean_box(0);
v___x_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
lean_ctor_set(v___x_732_, 1, v_b_725_);
v_sz_733_ = lean_array_size(v_cs_727_);
v___x_734_ = ((size_t)0ULL);
v___x_735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__29(v_init_723_, v_cs_727_, v_sz_733_, v___x_734_, v___x_732_);
lean_dec_ref(v_cs_727_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_752_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_752_ == 0)
{
v___x_738_ = v___x_735_;
v_isShared_739_ = v_isSharedCheck_752_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_752_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v_fst_740_; 
v_fst_740_ = lean_ctor_get(v_a_736_, 0);
if (lean_obj_tag(v_fst_740_) == 0)
{
lean_object* v_snd_741_; lean_object* v___x_743_; 
v_snd_741_ = lean_ctor_get(v_a_736_, 1);
lean_inc(v_snd_741_);
lean_dec(v_a_736_);
if (v_isShared_730_ == 0)
{
lean_ctor_set_tag(v___x_729_, 1);
lean_ctor_set(v___x_729_, 0, v_snd_741_);
v___x_743_ = v___x_729_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_snd_741_);
v___x_743_ = v_reuseFailAlloc_747_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_745_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_743_);
v___x_745_ = v___x_738_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
else
{
lean_object* v_val_748_; lean_object* v___x_750_; 
lean_inc_ref(v_fst_740_);
lean_dec(v_a_736_);
lean_del_object(v___x_729_);
v_val_748_ = lean_ctor_get(v_fst_740_, 0);
lean_inc(v_val_748_);
lean_dec_ref(v_fst_740_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v_val_748_);
v___x_750_ = v___x_738_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_val_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_del_object(v___x_729_);
v_a_753_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_735_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_735_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
else
{
lean_object* v_vs_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_796_; 
v_vs_762_ = lean_ctor_get(v_n_724_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v_n_724_);
if (v_isSharedCheck_796_ == 0)
{
v___x_764_ = v_n_724_;
v_isShared_765_ = v_isSharedCheck_796_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_vs_762_);
lean_dec(v_n_724_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_796_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_767_; size_t v_sz_768_; size_t v___x_769_; lean_object* v___x_770_; 
v___x_766_ = lean_box(0);
v___x_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set(v___x_767_, 1, v_b_725_);
v_sz_768_ = lean_array_size(v_vs_762_);
v___x_769_ = ((size_t)0ULL);
v___x_770_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__30(v_vs_762_, v_sz_768_, v___x_769_, v___x_767_);
lean_dec_ref(v_vs_762_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_787_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_787_ == 0)
{
v___x_773_ = v___x_770_;
v_isShared_774_ = v_isSharedCheck_787_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_770_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_787_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v_fst_775_; 
v_fst_775_ = lean_ctor_get(v_a_771_, 0);
if (lean_obj_tag(v_fst_775_) == 0)
{
lean_object* v_snd_776_; lean_object* v___x_778_; 
v_snd_776_ = lean_ctor_get(v_a_771_, 1);
lean_inc(v_snd_776_);
lean_dec(v_a_771_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v_snd_776_);
v___x_778_ = v___x_764_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_snd_776_);
v___x_778_ = v_reuseFailAlloc_782_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_780_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_778_);
v___x_780_ = v___x_773_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
else
{
lean_object* v_val_783_; lean_object* v___x_785_; 
lean_inc_ref(v_fst_775_);
lean_dec(v_a_771_);
lean_del_object(v___x_764_);
v_val_783_ = lean_ctor_get(v_fst_775_, 0);
lean_inc(v_val_783_);
lean_dec_ref(v_fst_775_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v_val_783_);
v___x_785_ = v___x_773_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_val_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_del_object(v___x_764_);
v_a_788_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_770_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_770_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__29(lean_object* v_init_797_, lean_object* v_as_798_, size_t v_sz_799_, size_t v_i_800_, lean_object* v_b_801_){
_start:
{
uint8_t v___x_803_; 
v___x_803_ = lean_usize_dec_lt(v_i_800_, v_sz_799_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; 
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v_b_801_);
return v___x_804_;
}
else
{
lean_object* v_snd_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_839_; 
v_snd_805_ = lean_ctor_get(v_b_801_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v_b_801_);
if (v_isSharedCheck_839_ == 0)
{
lean_object* v_unused_840_; 
v_unused_840_ = lean_ctor_get(v_b_801_, 0);
lean_dec(v_unused_840_);
v___x_807_ = v_b_801_;
v_isShared_808_ = v_isSharedCheck_839_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_snd_805_);
lean_dec(v_b_801_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_839_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v_a_809_; lean_object* v___x_810_; 
v_a_809_ = lean_array_uget_borrowed(v_as_798_, v_i_800_);
lean_inc(v_snd_805_);
lean_inc(v_a_809_);
v___x_810_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22(v_init_797_, v_a_809_, v_snd_805_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_830_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_830_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_830_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_830_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
if (lean_obj_tag(v_a_811_) == 0)
{
lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_815_, 0, v_a_811_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_815_);
v___x_817_ = v___x_807_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_snd_805_);
v___x_817_ = v_reuseFailAlloc_821_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_819_; 
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_817_);
v___x_819_ = v___x_813_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
else
{
lean_object* v_a_822_; lean_object* v___x_823_; lean_object* v___x_825_; 
lean_del_object(v___x_813_);
lean_dec(v_snd_805_);
v_a_822_ = lean_ctor_get(v_a_811_, 0);
lean_inc(v_a_822_);
lean_dec_ref(v_a_811_);
v___x_823_ = lean_box(0);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 1, v_a_822_);
lean_ctor_set(v___x_807_, 0, v___x_823_);
v___x_825_ = v___x_807_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_823_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_a_822_);
v___x_825_ = v_reuseFailAlloc_829_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
size_t v___x_826_; size_t v___x_827_; 
v___x_826_ = ((size_t)1ULL);
v___x_827_ = lean_usize_add(v_i_800_, v___x_826_);
v_i_800_ = v___x_827_;
v_b_801_ = v___x_825_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_del_object(v___x_807_);
lean_dec(v_snd_805_);
v_a_831_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_810_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_810_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__29___boxed(lean_object* v_init_841_, lean_object* v_as_842_, lean_object* v_sz_843_, lean_object* v_i_844_, lean_object* v_b_845_, lean_object* v___y_846_){
_start:
{
size_t v_sz_boxed_847_; size_t v_i_boxed_848_; lean_object* v_res_849_; 
v_sz_boxed_847_ = lean_unbox_usize(v_sz_843_);
lean_dec(v_sz_843_);
v_i_boxed_848_ = lean_unbox_usize(v_i_844_);
lean_dec(v_i_844_);
v_res_849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22_spec__29(v_init_841_, v_as_842_, v_sz_boxed_847_, v_i_boxed_848_, v_b_845_);
lean_dec_ref(v_as_842_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22___boxed(lean_object* v_init_850_, lean_object* v_n_851_, lean_object* v_b_852_, lean_object* v___y_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22(v_init_850_, v_n_851_, v_b_852_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__23_spec__32(lean_object* v_as_858_, size_t v_sz_859_, size_t v_i_860_, lean_object* v_b_861_){
_start:
{
uint8_t v___x_863_; 
v___x_863_ = lean_usize_dec_lt(v_i_860_, v_sz_859_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; 
v___x_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_864_, 0, v_b_861_);
return v___x_864_;
}
else
{
uint8_t v___x_865_; lean_object* v_a_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
lean_dec_ref(v_b_861_);
v___x_865_ = 0;
v_a_866_ = lean_array_uget_borrowed(v_as_858_, v_i_860_);
lean_inc(v_a_866_);
v___x_867_ = l_Lean_Message_toString(v_a_866_, v___x_865_);
v___x_868_ = l_IO_eprintln___at___00main_spec__9(v___x_867_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v___x_869_; size_t v___x_870_; size_t v___x_871_; 
lean_dec_ref(v___x_868_);
v___x_869_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__23_spec__32___closed__0));
v___x_870_ = ((size_t)1ULL);
v___x_871_ = lean_usize_add(v_i_860_, v___x_870_);
v_i_860_ = v___x_871_;
v_b_861_ = v___x_869_;
goto _start;
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
v_a_873_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_868_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_868_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__23_spec__32___boxed(lean_object* v_as_881_, lean_object* v_sz_882_, lean_object* v_i_883_, lean_object* v_b_884_, lean_object* v___y_885_){
_start:
{
size_t v_sz_boxed_886_; size_t v_i_boxed_887_; lean_object* v_res_888_; 
v_sz_boxed_886_ = lean_unbox_usize(v_sz_882_);
lean_dec(v_sz_882_);
v_i_boxed_887_ = lean_unbox_usize(v_i_883_);
lean_dec(v_i_883_);
v_res_888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__23_spec__32(v_as_881_, v_sz_boxed_886_, v_i_boxed_887_, v_b_884_);
lean_dec_ref(v_as_881_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__23(lean_object* v_as_889_, size_t v_sz_890_, size_t v_i_891_, lean_object* v_b_892_){
_start:
{
uint8_t v___x_894_; 
v___x_894_ = lean_usize_dec_lt(v_i_891_, v_sz_890_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; 
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v_b_892_);
return v___x_895_;
}
else
{
uint8_t v___x_896_; lean_object* v_a_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
lean_dec_ref(v_b_892_);
v___x_896_ = 0;
v_a_897_ = lean_array_uget_borrowed(v_as_889_, v_i_891_);
lean_inc(v_a_897_);
v___x_898_ = l_Lean_Message_toString(v_a_897_, v___x_896_);
v___x_899_ = l_IO_eprintln___at___00main_spec__9(v___x_898_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v___x_900_; size_t v___x_901_; size_t v___x_902_; lean_object* v___x_903_; 
lean_dec_ref(v___x_899_);
v___x_900_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__23_spec__32___closed__0));
v___x_901_ = ((size_t)1ULL);
v___x_902_ = lean_usize_add(v_i_891_, v___x_901_);
v___x_903_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__23_spec__32(v_as_889_, v_sz_890_, v___x_902_, v___x_900_);
return v___x_903_;
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
v_a_904_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_899_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_899_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__23___boxed(lean_object* v_as_912_, lean_object* v_sz_913_, lean_object* v_i_914_, lean_object* v_b_915_, lean_object* v___y_916_){
_start:
{
size_t v_sz_boxed_917_; size_t v_i_boxed_918_; lean_object* v_res_919_; 
v_sz_boxed_917_ = lean_unbox_usize(v_sz_913_);
lean_dec(v_sz_913_);
v_i_boxed_918_ = lean_unbox_usize(v_i_914_);
lean_dec(v_i_914_);
v_res_919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__23(v_as_912_, v_sz_boxed_917_, v_i_boxed_918_, v_b_915_);
lean_dec_ref(v_as_912_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__10(lean_object* v_t_920_, lean_object* v_init_921_){
_start:
{
lean_object* v_root_923_; lean_object* v_tail_924_; lean_object* v___x_925_; 
v_root_923_ = lean_ctor_get(v_t_920_, 0);
lean_inc_ref(v_root_923_);
v_tail_924_ = lean_ctor_get(v_t_920_, 1);
lean_inc_ref(v_tail_924_);
lean_dec_ref(v_t_920_);
v___x_925_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__22(v_init_921_, v_root_923_, v_init_921_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_962_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_962_ == 0)
{
v___x_928_ = v___x_925_;
v_isShared_929_ = v_isSharedCheck_962_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_925_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_962_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
if (lean_obj_tag(v_a_926_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_932_; 
lean_dec_ref(v_tail_924_);
v_a_930_ = lean_ctor_get(v_a_926_, 0);
lean_inc(v_a_930_);
lean_dec_ref(v_a_926_);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 0, v_a_930_);
v___x_932_ = v___x_928_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_930_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
else
{
lean_object* v_a_934_; lean_object* v___x_935_; lean_object* v___x_936_; size_t v_sz_937_; size_t v___x_938_; lean_object* v___x_939_; 
lean_del_object(v___x_928_);
v_a_934_ = lean_ctor_get(v_a_926_, 0);
lean_inc(v_a_934_);
lean_dec_ref(v_a_926_);
v___x_935_ = lean_box(0);
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v_a_934_);
v_sz_937_ = lean_array_size(v_tail_924_);
v___x_938_ = ((size_t)0ULL);
v___x_939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__10_spec__23(v_tail_924_, v_sz_937_, v___x_938_, v___x_936_);
lean_dec_ref(v_tail_924_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_953_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_953_ == 0)
{
v___x_942_ = v___x_939_;
v_isShared_943_ = v_isSharedCheck_953_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_939_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_953_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v_fst_944_; 
v_fst_944_ = lean_ctor_get(v_a_940_, 0);
if (lean_obj_tag(v_fst_944_) == 0)
{
lean_object* v_snd_945_; lean_object* v___x_947_; 
v_snd_945_ = lean_ctor_get(v_a_940_, 1);
lean_inc(v_snd_945_);
lean_dec(v_a_940_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v_snd_945_);
v___x_947_ = v___x_942_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_snd_945_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
else
{
lean_object* v_val_949_; lean_object* v___x_951_; 
lean_inc_ref(v_fst_944_);
lean_dec(v_a_940_);
v_val_949_ = lean_ctor_get(v_fst_944_, 0);
lean_inc(v_val_949_);
lean_dec_ref(v_fst_944_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v_val_949_);
v___x_951_ = v___x_942_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_val_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
v_a_954_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_939_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_939_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
}
}
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
lean_dec_ref(v_tail_924_);
v_a_963_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_925_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_925_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__10___boxed(lean_object* v_t_971_, lean_object* v_init_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_PersistentArray_forIn___at___00main_spec__10(v_t_971_, v_init_972_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__4_spec__4(lean_object* v_o_978_, lean_object* v_k_979_, lean_object* v_v_980_){
_start:
{
lean_object* v_map_981_; uint8_t v_hasTrace_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_996_; 
v_map_981_ = lean_ctor_get(v_o_978_, 0);
v_hasTrace_982_ = lean_ctor_get_uint8(v_o_978_, sizeof(void*)*1);
v_isSharedCheck_996_ = !lean_is_exclusive(v_o_978_);
if (v_isSharedCheck_996_ == 0)
{
v___x_984_ = v_o_978_;
v_isShared_985_ = v_isSharedCheck_996_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_map_981_);
lean_dec(v_o_978_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_996_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_986_, 0, v_v_980_);
lean_inc(v_k_979_);
v___x_987_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_979_, v___x_986_, v_map_981_);
if (v_hasTrace_982_ == 0)
{
lean_object* v___x_988_; uint8_t v___x_989_; lean_object* v___x_991_; 
v___x_988_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__4_spec__4___closed__1));
v___x_989_ = l_Lean_Name_isPrefixOf(v___x_988_, v_k_979_);
lean_dec(v_k_979_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v___x_987_);
v___x_991_ = v___x_984_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_987_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_ctor_set_uint8(v___x_991_, sizeof(void*)*1, v___x_989_);
return v___x_991_;
}
}
else
{
lean_object* v___x_994_; 
lean_dec(v_k_979_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v___x_987_);
v___x_994_ = v___x_984_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_987_);
lean_ctor_set_uint8(v_reuseFailAlloc_995_, sizeof(void*)*1, v_hasTrace_982_);
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
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00main_spec__4(lean_object* v_opts_997_, lean_object* v_opt_998_, lean_object* v_val_999_){
_start:
{
lean_object* v_name_1000_; lean_object* v___x_1001_; 
v_name_1000_ = lean_ctor_get(v_opt_998_, 0);
lean_inc(v_name_1000_);
lean_dec_ref(v_opt_998_);
v___x_1001_ = l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__4_spec__4(v_opts_997_, v_name_1000_, v_val_999_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg(lean_object* v_as_x27_1002_, lean_object* v_b_1003_){
_start:
{
if (lean_obj_tag(v_as_x27_1002_) == 0)
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1005_, 0, v_b_1003_);
return v___x_1005_;
}
else
{
lean_object* v_head_1006_; lean_object* v_tail_1007_; lean_object* v___x_1008_; 
v_head_1006_ = lean_ctor_get(v_as_x27_1002_, 0);
lean_inc(v_head_1006_);
v_tail_1007_ = lean_ctor_get(v_as_x27_1002_, 1);
lean_inc(v_tail_1007_);
lean_dec_ref(v_as_x27_1002_);
v___x_1008_ = l___private_LeanIR_0__setConfigOption(v_b_1003_, v_head_1006_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref(v___x_1008_);
v_as_x27_1002_ = v_tail_1007_;
v_b_1003_ = v_a_1009_;
goto _start;
}
else
{
lean_dec(v_tail_1007_);
return v___x_1008_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg___boxed(lean_object* v_as_x27_1011_, lean_object* v_b_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v_as_x27_1011_, v_b_1012_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__17(lean_object* v_x_1015_, lean_object* v_x_1016_){
_start:
{
if (lean_obj_tag(v_x_1016_) == 0)
{
return v_x_1015_;
}
else
{
lean_object* v_key_1017_; lean_object* v_value_1018_; lean_object* v_tail_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v_key_1017_ = lean_ctor_get(v_x_1016_, 0);
v_value_1018_ = lean_ctor_get(v_x_1016_, 1);
v_tail_1019_ = lean_ctor_get(v_x_1016_, 2);
lean_inc(v_value_1018_);
lean_inc(v_key_1017_);
v___x_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1020_, 0, v_key_1017_);
lean_ctor_set(v___x_1020_, 1, v_value_1018_);
v___x_1021_ = lean_array_push(v_x_1015_, v___x_1020_);
v_x_1015_ = v___x_1021_;
v_x_1016_ = v_tail_1019_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__17___boxed(lean_object* v_x_1023_, lean_object* v_x_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__17(v_x_1023_, v_x_1024_);
lean_dec(v_x_1024_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__18(lean_object* v_as_1026_, size_t v_i_1027_, size_t v_stop_1028_, lean_object* v_b_1029_){
_start:
{
uint8_t v___x_1030_; 
v___x_1030_ = lean_usize_dec_eq(v_i_1027_, v_stop_1028_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; lean_object* v___x_1032_; size_t v___x_1033_; size_t v___x_1034_; 
v___x_1031_ = lean_array_uget_borrowed(v_as_1026_, v_i_1027_);
v___x_1032_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__17(v_b_1029_, v___x_1031_);
v___x_1033_ = ((size_t)1ULL);
v___x_1034_ = lean_usize_add(v_i_1027_, v___x_1033_);
v_i_1027_ = v___x_1034_;
v_b_1029_ = v___x_1032_;
goto _start;
}
else
{
return v_b_1029_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__18___boxed(lean_object* v_as_1036_, lean_object* v_i_1037_, lean_object* v_stop_1038_, lean_object* v_b_1039_){
_start:
{
size_t v_i_boxed_1040_; size_t v_stop_boxed_1041_; lean_object* v_res_1042_; 
v_i_boxed_1040_ = lean_unbox_usize(v_i_1037_);
lean_dec(v_i_1037_);
v_stop_boxed_1041_ = lean_unbox_usize(v_stop_1038_);
lean_dec(v_stop_1038_);
v_res_1042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__18(v_as_1036_, v_i_boxed_1040_, v_stop_boxed_1041_, v_b_1039_);
lean_dec_ref(v_as_1036_);
return v_res_1042_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg___lam__0(lean_object* v_x_1043_, lean_object* v_x_1044_){
_start:
{
lean_object* v_fst_1045_; lean_object* v_fst_1046_; lean_object* v_fst_1047_; lean_object* v_fst_1048_; uint8_t v___x_1049_; 
v_fst_1045_ = lean_ctor_get(v_x_1043_, 0);
v_fst_1046_ = lean_ctor_get(v_x_1044_, 0);
v_fst_1047_ = lean_ctor_get(v_fst_1045_, 0);
v_fst_1048_ = lean_ctor_get(v_fst_1046_, 0);
v___x_1049_ = l_String_instDecidableLtRaw___aux__1(v_fst_1047_, v_fst_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg___lam__0___boxed(lean_object* v_x_1050_, lean_object* v_x_1051_){
_start:
{
uint8_t v_res_1052_; lean_object* v_r_1053_; 
v_res_1052_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg___lam__0(v_x_1050_, v_x_1051_);
lean_dec_ref(v_x_1051_);
lean_dec_ref(v_x_1050_);
v_r_1053_ = lean_box(v_res_1052_);
return v_r_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg(lean_object* v_as_1055_, lean_object* v_lo_1056_, lean_object* v_hi_1057_){
_start:
{
uint8_t v___x_1058_; 
v___x_1058_ = lean_nat_dec_lt(v_lo_1056_, v_hi_1057_);
if (v___x_1058_ == 0)
{
lean_dec(v_lo_1056_);
return v_as_1055_;
}
else
{
lean_object* v___f_1059_; lean_object* v___x_1060_; lean_object* v_fst_1061_; lean_object* v_snd_1062_; uint8_t v___x_1063_; 
v___f_1059_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg___closed__0));
lean_inc(v_lo_1056_);
v___x_1060_ = l_Array_qpartition___redArg(v_as_1055_, v___f_1059_, v_lo_1056_, v_hi_1057_);
v_fst_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_fst_1061_);
v_snd_1062_ = lean_ctor_get(v___x_1060_, 1);
lean_inc(v_snd_1062_);
lean_dec_ref(v___x_1060_);
v___x_1063_ = lean_nat_dec_le(v_hi_1057_, v_fst_1061_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1064_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg(v_snd_1062_, v_lo_1056_, v_fst_1061_);
v___x_1065_ = lean_unsigned_to_nat(1u);
v___x_1066_ = lean_nat_add(v_fst_1061_, v___x_1065_);
lean_dec(v_fst_1061_);
v_as_1055_ = v___x_1064_;
v_lo_1056_ = v___x_1066_;
goto _start;
}
else
{
lean_dec(v_fst_1061_);
lean_dec(v_lo_1056_);
return v_snd_1062_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg___boxed(lean_object* v_as_1068_, lean_object* v_lo_1069_, lean_object* v_hi_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg(v_as_1068_, v_lo_1069_, v_hi_1070_);
lean_dec(v_hi_1070_);
return v_res_1071_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__15___redArg(lean_object* v_a_1072_, lean_object* v_x_1073_){
_start:
{
if (lean_obj_tag(v_x_1073_) == 0)
{
uint8_t v___x_1074_; 
v___x_1074_ = 0;
return v___x_1074_;
}
else
{
lean_object* v_key_1075_; lean_object* v_tail_1076_; uint8_t v___y_1078_; lean_object* v_fst_1080_; lean_object* v_snd_1081_; lean_object* v_fst_1082_; lean_object* v_snd_1083_; uint8_t v___x_1084_; 
v_key_1075_ = lean_ctor_get(v_x_1073_, 0);
v_tail_1076_ = lean_ctor_get(v_x_1073_, 2);
v_fst_1080_ = lean_ctor_get(v_key_1075_, 0);
v_snd_1081_ = lean_ctor_get(v_key_1075_, 1);
v_fst_1082_ = lean_ctor_get(v_a_1072_, 0);
v_snd_1083_ = lean_ctor_get(v_a_1072_, 1);
v___x_1084_ = lean_nat_dec_eq(v_fst_1080_, v_fst_1082_);
if (v___x_1084_ == 0)
{
v___y_1078_ = v___x_1084_;
goto v___jp_1077_;
}
else
{
uint8_t v___x_1085_; 
v___x_1085_ = lean_nat_dec_eq(v_snd_1081_, v_snd_1083_);
v___y_1078_ = v___x_1085_;
goto v___jp_1077_;
}
v___jp_1077_:
{
if (v___y_1078_ == 0)
{
v_x_1073_ = v_tail_1076_;
goto _start;
}
else
{
return v___y_1078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__15___redArg___boxed(lean_object* v_a_1086_, lean_object* v_x_1087_){
_start:
{
uint8_t v_res_1088_; lean_object* v_r_1089_; 
v_res_1088_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__15___redArg(v_a_1086_, v_x_1087_);
lean_dec(v_x_1087_);
lean_dec_ref(v_a_1086_);
v_r_1089_ = lean_box(v_res_1088_);
return v_r_1089_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16_spec__28_spec__37___redArg(lean_object* v_x_1090_, lean_object* v_x_1091_){
_start:
{
if (lean_obj_tag(v_x_1091_) == 0)
{
return v_x_1090_;
}
else
{
lean_object* v_key_1092_; lean_object* v_value_1093_; lean_object* v_tail_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1121_; 
v_key_1092_ = lean_ctor_get(v_x_1091_, 0);
v_value_1093_ = lean_ctor_get(v_x_1091_, 1);
v_tail_1094_ = lean_ctor_get(v_x_1091_, 2);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_x_1091_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1096_ = v_x_1091_;
v_isShared_1097_ = v_isSharedCheck_1121_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_tail_1094_);
lean_inc(v_value_1093_);
lean_inc(v_key_1092_);
lean_dec(v_x_1091_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1121_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v_fst_1098_; lean_object* v_snd_1099_; lean_object* v___x_1100_; uint64_t v___x_1101_; uint64_t v___x_1102_; uint64_t v___x_1103_; uint64_t v___x_1104_; uint64_t v___x_1105_; uint64_t v_fold_1106_; uint64_t v___x_1107_; uint64_t v___x_1108_; uint64_t v___x_1109_; size_t v___x_1110_; size_t v___x_1111_; size_t v___x_1112_; size_t v___x_1113_; size_t v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1117_; 
v_fst_1098_ = lean_ctor_get(v_key_1092_, 0);
v_snd_1099_ = lean_ctor_get(v_key_1092_, 1);
v___x_1100_ = lean_array_get_size(v_x_1090_);
v___x_1101_ = l_String_instHashableRaw_hash(v_fst_1098_);
v___x_1102_ = l_String_instHashableRaw_hash(v_snd_1099_);
v___x_1103_ = lean_uint64_mix_hash(v___x_1101_, v___x_1102_);
v___x_1104_ = 32ULL;
v___x_1105_ = lean_uint64_shift_right(v___x_1103_, v___x_1104_);
v_fold_1106_ = lean_uint64_xor(v___x_1103_, v___x_1105_);
v___x_1107_ = 16ULL;
v___x_1108_ = lean_uint64_shift_right(v_fold_1106_, v___x_1107_);
v___x_1109_ = lean_uint64_xor(v_fold_1106_, v___x_1108_);
v___x_1110_ = lean_uint64_to_usize(v___x_1109_);
v___x_1111_ = lean_usize_of_nat(v___x_1100_);
v___x_1112_ = ((size_t)1ULL);
v___x_1113_ = lean_usize_sub(v___x_1111_, v___x_1112_);
v___x_1114_ = lean_usize_land(v___x_1110_, v___x_1113_);
v___x_1115_ = lean_array_uget_borrowed(v_x_1090_, v___x_1114_);
lean_inc(v___x_1115_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 2, v___x_1115_);
v___x_1117_ = v___x_1096_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_key_1092_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_value_1093_);
lean_ctor_set(v_reuseFailAlloc_1120_, 2, v___x_1115_);
v___x_1117_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1118_; 
v___x_1118_ = lean_array_uset(v_x_1090_, v___x_1114_, v___x_1117_);
v_x_1090_ = v___x_1118_;
v_x_1091_ = v_tail_1094_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16_spec__28___redArg(lean_object* v_i_1122_, lean_object* v_source_1123_, lean_object* v_target_1124_){
_start:
{
lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1125_ = lean_array_get_size(v_source_1123_);
v___x_1126_ = lean_nat_dec_lt(v_i_1122_, v___x_1125_);
if (v___x_1126_ == 0)
{
lean_dec_ref(v_source_1123_);
lean_dec(v_i_1122_);
return v_target_1124_;
}
else
{
lean_object* v_es_1127_; lean_object* v___x_1128_; lean_object* v_source_1129_; lean_object* v_target_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v_es_1127_ = lean_array_fget(v_source_1123_, v_i_1122_);
v___x_1128_ = lean_box(0);
v_source_1129_ = lean_array_fset(v_source_1123_, v_i_1122_, v___x_1128_);
v_target_1130_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16_spec__28_spec__37___redArg(v_target_1124_, v_es_1127_);
v___x_1131_ = lean_unsigned_to_nat(1u);
v___x_1132_ = lean_nat_add(v_i_1122_, v___x_1131_);
lean_dec(v_i_1122_);
v_i_1122_ = v___x_1132_;
v_source_1123_ = v_source_1129_;
v_target_1124_ = v_target_1130_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16___redArg(lean_object* v_data_1134_){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v_nbuckets_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1135_ = lean_array_get_size(v_data_1134_);
v___x_1136_ = lean_unsigned_to_nat(2u);
v_nbuckets_1137_ = lean_nat_mul(v___x_1135_, v___x_1136_);
v___x_1138_ = lean_unsigned_to_nat(0u);
v___x_1139_ = lean_box(0);
v___x_1140_ = lean_mk_array(v_nbuckets_1137_, v___x_1139_);
v___x_1141_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16_spec__28___redArg(v___x_1138_, v_data_1134_, v___x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__17___redArg(lean_object* v_a_1142_, lean_object* v_b_1143_, lean_object* v_x_1144_){
_start:
{
if (lean_obj_tag(v_x_1144_) == 0)
{
lean_dec(v_b_1143_);
lean_dec_ref(v_a_1142_);
return v_x_1144_;
}
else
{
lean_object* v_key_1145_; lean_object* v_value_1146_; lean_object* v_tail_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1166_; 
v_key_1145_ = lean_ctor_get(v_x_1144_, 0);
v_value_1146_ = lean_ctor_get(v_x_1144_, 1);
v_tail_1147_ = lean_ctor_get(v_x_1144_, 2);
v_isSharedCheck_1166_ = !lean_is_exclusive(v_x_1144_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1149_ = v_x_1144_;
v_isShared_1150_ = v_isSharedCheck_1166_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_tail_1147_);
lean_inc(v_value_1146_);
lean_inc(v_key_1145_);
lean_dec(v_x_1144_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1166_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
uint8_t v___y_1152_; lean_object* v_fst_1160_; lean_object* v_snd_1161_; lean_object* v_fst_1162_; lean_object* v_snd_1163_; uint8_t v___x_1164_; 
v_fst_1160_ = lean_ctor_get(v_key_1145_, 0);
v_snd_1161_ = lean_ctor_get(v_key_1145_, 1);
v_fst_1162_ = lean_ctor_get(v_a_1142_, 0);
v_snd_1163_ = lean_ctor_get(v_a_1142_, 1);
v___x_1164_ = lean_nat_dec_eq(v_fst_1160_, v_fst_1162_);
if (v___x_1164_ == 0)
{
v___y_1152_ = v___x_1164_;
goto v___jp_1151_;
}
else
{
uint8_t v___x_1165_; 
v___x_1165_ = lean_nat_dec_eq(v_snd_1161_, v_snd_1163_);
v___y_1152_ = v___x_1165_;
goto v___jp_1151_;
}
v___jp_1151_:
{
if (v___y_1152_ == 0)
{
lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1153_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__17___redArg(v_a_1142_, v_b_1143_, v_tail_1147_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 2, v___x_1153_);
v___x_1155_ = v___x_1149_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_key_1145_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_value_1146_);
lean_ctor_set(v_reuseFailAlloc_1156_, 2, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
else
{
lean_object* v___x_1158_; 
lean_dec(v_value_1146_);
lean_dec(v_key_1145_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 1, v_b_1143_);
lean_ctor_set(v___x_1149_, 0, v_a_1142_);
v___x_1158_ = v___x_1149_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1142_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_b_1143_);
lean_ctor_set(v_reuseFailAlloc_1159_, 2, v_tail_1147_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13___redArg(lean_object* v_m_1167_, lean_object* v_a_1168_, lean_object* v_b_1169_){
_start:
{
lean_object* v_size_1170_; lean_object* v_buckets_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1218_; 
v_size_1170_ = lean_ctor_get(v_m_1167_, 0);
v_buckets_1171_ = lean_ctor_get(v_m_1167_, 1);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_m_1167_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1173_ = v_m_1167_;
v_isShared_1174_ = v_isSharedCheck_1218_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_buckets_1171_);
lean_inc(v_size_1170_);
lean_dec(v_m_1167_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1218_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v_fst_1175_; lean_object* v_snd_1176_; lean_object* v___x_1177_; uint64_t v___x_1178_; uint64_t v___x_1179_; uint64_t v___x_1180_; uint64_t v___x_1181_; uint64_t v___x_1182_; uint64_t v_fold_1183_; uint64_t v___x_1184_; uint64_t v___x_1185_; uint64_t v___x_1186_; size_t v___x_1187_; size_t v___x_1188_; size_t v___x_1189_; size_t v___x_1190_; size_t v___x_1191_; lean_object* v_bkt_1192_; uint8_t v___x_1193_; 
v_fst_1175_ = lean_ctor_get(v_a_1168_, 0);
v_snd_1176_ = lean_ctor_get(v_a_1168_, 1);
v___x_1177_ = lean_array_get_size(v_buckets_1171_);
v___x_1178_ = l_String_instHashableRaw_hash(v_fst_1175_);
v___x_1179_ = l_String_instHashableRaw_hash(v_snd_1176_);
v___x_1180_ = lean_uint64_mix_hash(v___x_1178_, v___x_1179_);
v___x_1181_ = 32ULL;
v___x_1182_ = lean_uint64_shift_right(v___x_1180_, v___x_1181_);
v_fold_1183_ = lean_uint64_xor(v___x_1180_, v___x_1182_);
v___x_1184_ = 16ULL;
v___x_1185_ = lean_uint64_shift_right(v_fold_1183_, v___x_1184_);
v___x_1186_ = lean_uint64_xor(v_fold_1183_, v___x_1185_);
v___x_1187_ = lean_uint64_to_usize(v___x_1186_);
v___x_1188_ = lean_usize_of_nat(v___x_1177_);
v___x_1189_ = ((size_t)1ULL);
v___x_1190_ = lean_usize_sub(v___x_1188_, v___x_1189_);
v___x_1191_ = lean_usize_land(v___x_1187_, v___x_1190_);
v_bkt_1192_ = lean_array_uget_borrowed(v_buckets_1171_, v___x_1191_);
v___x_1193_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__15___redArg(v_a_1168_, v_bkt_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; lean_object* v_size_x27_1195_; lean_object* v___x_1196_; lean_object* v_buckets_x27_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
v___x_1194_ = lean_unsigned_to_nat(1u);
v_size_x27_1195_ = lean_nat_add(v_size_1170_, v___x_1194_);
lean_dec(v_size_1170_);
lean_inc(v_bkt_1192_);
v___x_1196_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1196_, 0, v_a_1168_);
lean_ctor_set(v___x_1196_, 1, v_b_1169_);
lean_ctor_set(v___x_1196_, 2, v_bkt_1192_);
v_buckets_x27_1197_ = lean_array_uset(v_buckets_1171_, v___x_1191_, v___x_1196_);
v___x_1198_ = lean_unsigned_to_nat(4u);
v___x_1199_ = lean_nat_mul(v_size_x27_1195_, v___x_1198_);
v___x_1200_ = lean_unsigned_to_nat(3u);
v___x_1201_ = lean_nat_div(v___x_1199_, v___x_1200_);
lean_dec(v___x_1199_);
v___x_1202_ = lean_array_get_size(v_buckets_x27_1197_);
v___x_1203_ = lean_nat_dec_le(v___x_1201_, v___x_1202_);
lean_dec(v___x_1201_);
if (v___x_1203_ == 0)
{
lean_object* v_val_1204_; lean_object* v___x_1206_; 
v_val_1204_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16___redArg(v_buckets_x27_1197_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 1, v_val_1204_);
lean_ctor_set(v___x_1173_, 0, v_size_x27_1195_);
v___x_1206_ = v___x_1173_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_size_x27_1195_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_val_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
else
{
lean_object* v___x_1209_; 
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 1, v_buckets_x27_1197_);
lean_ctor_set(v___x_1173_, 0, v_size_x27_1195_);
v___x_1209_ = v___x_1173_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_size_x27_1195_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_buckets_x27_1197_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
else
{
lean_object* v___x_1211_; lean_object* v_buckets_x27_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1216_; 
lean_inc(v_bkt_1192_);
v___x_1211_ = lean_box(0);
v_buckets_x27_1212_ = lean_array_uset(v_buckets_1171_, v___x_1191_, v___x_1211_);
v___x_1213_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__17___redArg(v_a_1168_, v_b_1169_, v_bkt_1192_);
v___x_1214_ = lean_array_uset(v_buckets_x27_1212_, v___x_1191_, v___x_1213_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 1, v___x_1214_);
v___x_1216_ = v___x_1173_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_size_1170_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12_spec__13___redArg(lean_object* v_a_1219_, lean_object* v_fallback_1220_, lean_object* v_x_1221_){
_start:
{
if (lean_obj_tag(v_x_1221_) == 0)
{
lean_inc(v_fallback_1220_);
return v_fallback_1220_;
}
else
{
lean_object* v_key_1222_; lean_object* v_value_1223_; lean_object* v_tail_1224_; uint8_t v___y_1226_; lean_object* v_fst_1228_; lean_object* v_snd_1229_; lean_object* v_fst_1230_; lean_object* v_snd_1231_; uint8_t v___x_1232_; 
v_key_1222_ = lean_ctor_get(v_x_1221_, 0);
v_value_1223_ = lean_ctor_get(v_x_1221_, 1);
v_tail_1224_ = lean_ctor_get(v_x_1221_, 2);
v_fst_1228_ = lean_ctor_get(v_key_1222_, 0);
v_snd_1229_ = lean_ctor_get(v_key_1222_, 1);
v_fst_1230_ = lean_ctor_get(v_a_1219_, 0);
v_snd_1231_ = lean_ctor_get(v_a_1219_, 1);
v___x_1232_ = lean_nat_dec_eq(v_fst_1228_, v_fst_1230_);
if (v___x_1232_ == 0)
{
v___y_1226_ = v___x_1232_;
goto v___jp_1225_;
}
else
{
uint8_t v___x_1233_; 
v___x_1233_ = lean_nat_dec_eq(v_snd_1229_, v_snd_1231_);
v___y_1226_ = v___x_1233_;
goto v___jp_1225_;
}
v___jp_1225_:
{
if (v___y_1226_ == 0)
{
v_x_1221_ = v_tail_1224_;
goto _start;
}
else
{
lean_inc(v_value_1223_);
return v_value_1223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12_spec__13___redArg___boxed(lean_object* v_a_1234_, lean_object* v_fallback_1235_, lean_object* v_x_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12_spec__13___redArg(v_a_1234_, v_fallback_1235_, v_x_1236_);
lean_dec(v_x_1236_);
lean_dec(v_fallback_1235_);
lean_dec_ref(v_a_1234_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12___redArg(lean_object* v_m_1238_, lean_object* v_a_1239_, lean_object* v_fallback_1240_){
_start:
{
lean_object* v_buckets_1241_; lean_object* v_fst_1242_; lean_object* v_snd_1243_; lean_object* v___x_1244_; uint64_t v___x_1245_; uint64_t v___x_1246_; uint64_t v___x_1247_; uint64_t v___x_1248_; uint64_t v___x_1249_; uint64_t v_fold_1250_; uint64_t v___x_1251_; uint64_t v___x_1252_; uint64_t v___x_1253_; size_t v___x_1254_; size_t v___x_1255_; size_t v___x_1256_; size_t v___x_1257_; size_t v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v_buckets_1241_ = lean_ctor_get(v_m_1238_, 1);
v_fst_1242_ = lean_ctor_get(v_a_1239_, 0);
v_snd_1243_ = lean_ctor_get(v_a_1239_, 1);
v___x_1244_ = lean_array_get_size(v_buckets_1241_);
v___x_1245_ = l_String_instHashableRaw_hash(v_fst_1242_);
v___x_1246_ = l_String_instHashableRaw_hash(v_snd_1243_);
v___x_1247_ = lean_uint64_mix_hash(v___x_1245_, v___x_1246_);
v___x_1248_ = 32ULL;
v___x_1249_ = lean_uint64_shift_right(v___x_1247_, v___x_1248_);
v_fold_1250_ = lean_uint64_xor(v___x_1247_, v___x_1249_);
v___x_1251_ = 16ULL;
v___x_1252_ = lean_uint64_shift_right(v_fold_1250_, v___x_1251_);
v___x_1253_ = lean_uint64_xor(v_fold_1250_, v___x_1252_);
v___x_1254_ = lean_uint64_to_usize(v___x_1253_);
v___x_1255_ = lean_usize_of_nat(v___x_1244_);
v___x_1256_ = ((size_t)1ULL);
v___x_1257_ = lean_usize_sub(v___x_1255_, v___x_1256_);
v___x_1258_ = lean_usize_land(v___x_1254_, v___x_1257_);
v___x_1259_ = lean_array_uget_borrowed(v_buckets_1241_, v___x_1258_);
v___x_1260_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12_spec__13___redArg(v_a_1239_, v_fallback_1240_, v___x_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12___redArg___boxed(lean_object* v_m_1261_, lean_object* v_a_1262_, lean_object* v_fallback_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12___redArg(v_m_1261_, v_a_1262_, v_fallback_1263_);
lean_dec(v_fallback_1263_);
lean_dec_ref(v_a_1262_);
lean_dec_ref(v_m_1261_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42___redArg(uint8_t v___x_1267_, lean_object* v_as_1268_, size_t v_sz_1269_, size_t v_i_1270_, lean_object* v_b_1271_, lean_object* v___y_1272_){
_start:
{
uint8_t v___x_1274_; 
v___x_1274_ = lean_usize_dec_lt(v_i_1270_, v_sz_1269_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; 
v___x_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1275_, 0, v_b_1271_);
return v___x_1275_;
}
else
{
lean_object* v_snd_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1313_; 
v_snd_1276_ = lean_ctor_get(v_b_1271_, 1);
v_isSharedCheck_1313_ = !lean_is_exclusive(v_b_1271_);
if (v_isSharedCheck_1313_ == 0)
{
lean_object* v_unused_1314_; 
v_unused_1314_ = lean_ctor_get(v_b_1271_, 0);
lean_dec(v_unused_1314_);
v___x_1278_ = v_b_1271_;
v_isShared_1279_ = v_isSharedCheck_1313_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_snd_1276_);
lean_dec(v_b_1271_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1313_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v_ref_1280_; lean_object* v_a_1281_; lean_object* v_ref_1282_; lean_object* v_msg_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1312_; 
v_ref_1280_ = lean_ctor_get(v___y_1272_, 5);
v_a_1281_ = lean_array_uget(v_as_1268_, v_i_1270_);
v_ref_1282_ = lean_ctor_get(v_a_1281_, 0);
v_msg_1283_ = lean_ctor_get(v_a_1281_, 1);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_a_1281_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1285_ = v_a_1281_;
v_isShared_1286_ = v_isSharedCheck_1312_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_msg_1283_);
lean_inc(v_ref_1282_);
lean_dec(v_a_1281_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1312_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v_ref_1304_; lean_object* v___y_1306_; lean_object* v___x_1309_; 
v___x_1287_ = lean_box(0);
v_ref_1304_ = l_Lean_replaceRef(v_ref_1282_, v_ref_1280_);
lean_dec(v_ref_1282_);
v___x_1309_ = l_Lean_Syntax_getPos_x3f(v_ref_1304_, v___x_1267_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v___x_1310_; 
v___x_1310_ = lean_unsigned_to_nat(0u);
v___y_1306_ = v___x_1310_;
goto v___jp_1305_;
}
else
{
lean_object* v_val_1311_; 
v_val_1311_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_val_1311_);
lean_dec_ref(v___x_1309_);
v___y_1306_ = v_val_1311_;
goto v___jp_1305_;
}
v___jp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 1, v___y_1290_);
lean_ctor_set(v___x_1278_, 0, v___y_1289_);
v___x_1292_ = v___x_1278_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___y_1289_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v___y_1290_);
v___x_1292_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v_pos2traces_1296_; lean_object* v___x_1298_; 
v___x_1293_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42___redArg___closed__0));
v___x_1294_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12___redArg(v_snd_1276_, v___x_1292_, v___x_1293_);
v___x_1295_ = lean_array_push(v___x_1294_, v_msg_1283_);
v_pos2traces_1296_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13___redArg(v_snd_1276_, v___x_1292_, v___x_1295_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v_pos2traces_1296_);
lean_ctor_set(v___x_1285_, 0, v___x_1287_);
v___x_1298_ = v___x_1285_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_pos2traces_1296_);
v___x_1298_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
size_t v___x_1299_; size_t v___x_1300_; 
v___x_1299_ = ((size_t)1ULL);
v___x_1300_ = lean_usize_add(v_i_1270_, v___x_1299_);
v_i_1270_ = v___x_1300_;
v_b_1271_ = v___x_1298_;
goto _start;
}
}
}
v___jp_1305_:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1304_, v___x_1267_);
lean_dec(v_ref_1304_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_inc(v___y_1306_);
v___y_1289_ = v___y_1306_;
v___y_1290_ = v___y_1306_;
goto v___jp_1288_;
}
else
{
lean_object* v_val_1308_; 
v_val_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_val_1308_);
lean_dec_ref(v___x_1307_);
v___y_1289_ = v___y_1306_;
v___y_1290_ = v_val_1308_;
goto v___jp_1288_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42___redArg___boxed(lean_object* v___x_1315_, lean_object* v_as_1316_, lean_object* v_sz_1317_, lean_object* v_i_1318_, lean_object* v_b_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
uint8_t v___x_33359__boxed_1322_; size_t v_sz_boxed_1323_; size_t v_i_boxed_1324_; lean_object* v_res_1325_; 
v___x_33359__boxed_1322_ = lean_unbox(v___x_1315_);
v_sz_boxed_1323_ = lean_unbox_usize(v_sz_1317_);
lean_dec(v_sz_1317_);
v_i_boxed_1324_ = lean_unbox_usize(v_i_1318_);
lean_dec(v_i_1318_);
v_res_1325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42___redArg(v___x_33359__boxed_1322_, v_as_1316_, v_sz_boxed_1323_, v_i_boxed_1324_, v_b_1319_, v___y_1320_);
lean_dec_ref(v___y_1320_);
lean_dec_ref(v_as_1316_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33(uint8_t v___x_1326_, lean_object* v_as_1327_, size_t v_sz_1328_, size_t v_i_1329_, lean_object* v_b_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
uint8_t v___x_1334_; 
v___x_1334_ = lean_usize_dec_lt(v_i_1329_, v_sz_1328_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; 
v___x_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1335_, 0, v_b_1330_);
return v___x_1335_;
}
else
{
lean_object* v_snd_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1373_; 
v_snd_1336_ = lean_ctor_get(v_b_1330_, 1);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_b_1330_);
if (v_isSharedCheck_1373_ == 0)
{
lean_object* v_unused_1374_; 
v_unused_1374_ = lean_ctor_get(v_b_1330_, 0);
lean_dec(v_unused_1374_);
v___x_1338_ = v_b_1330_;
v_isShared_1339_ = v_isSharedCheck_1373_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_snd_1336_);
lean_dec(v_b_1330_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1373_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v_ref_1340_; lean_object* v_a_1341_; lean_object* v_ref_1342_; lean_object* v_msg_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1372_; 
v_ref_1340_ = lean_ctor_get(v___y_1331_, 5);
v_a_1341_ = lean_array_uget(v_as_1327_, v_i_1329_);
v_ref_1342_ = lean_ctor_get(v_a_1341_, 0);
v_msg_1343_ = lean_ctor_get(v_a_1341_, 1);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_a_1341_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1345_ = v_a_1341_;
v_isShared_1346_ = v_isSharedCheck_1372_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_msg_1343_);
lean_inc(v_ref_1342_);
lean_dec(v_a_1341_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1372_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v_ref_1364_; lean_object* v___y_1366_; lean_object* v___x_1369_; 
v___x_1347_ = lean_box(0);
v_ref_1364_ = l_Lean_replaceRef(v_ref_1342_, v_ref_1340_);
lean_dec(v_ref_1342_);
v___x_1369_ = l_Lean_Syntax_getPos_x3f(v_ref_1364_, v___x_1326_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_unsigned_to_nat(0u);
v___y_1366_ = v___x_1370_;
goto v___jp_1365_;
}
else
{
lean_object* v_val_1371_; 
v_val_1371_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_val_1371_);
lean_dec_ref(v___x_1369_);
v___y_1366_ = v_val_1371_;
goto v___jp_1365_;
}
v___jp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 1, v___y_1350_);
lean_ctor_set(v___x_1338_, 0, v___y_1349_);
v___x_1352_ = v___x_1338_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___y_1349_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v___y_1350_);
v___x_1352_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v_pos2traces_1356_; lean_object* v___x_1358_; 
v___x_1353_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42___redArg___closed__0));
v___x_1354_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12___redArg(v_snd_1336_, v___x_1352_, v___x_1353_);
v___x_1355_ = lean_array_push(v___x_1354_, v_msg_1343_);
v_pos2traces_1356_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13___redArg(v_snd_1336_, v___x_1352_, v___x_1355_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 1, v_pos2traces_1356_);
lean_ctor_set(v___x_1345_, 0, v___x_1347_);
v___x_1358_ = v___x_1345_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1347_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_pos2traces_1356_);
v___x_1358_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
size_t v___x_1359_; size_t v___x_1360_; lean_object* v___x_1361_; 
v___x_1359_ = ((size_t)1ULL);
v___x_1360_ = lean_usize_add(v_i_1329_, v___x_1359_);
v___x_1361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42___redArg(v___x_1326_, v_as_1327_, v_sz_1328_, v___x_1360_, v___x_1358_, v___y_1331_);
return v___x_1361_;
}
}
}
v___jp_1365_:
{
lean_object* v___x_1367_; 
v___x_1367_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1364_, v___x_1326_);
lean_dec(v_ref_1364_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_inc(v___y_1366_);
v___y_1349_ = v___y_1366_;
v___y_1350_ = v___y_1366_;
goto v___jp_1348_;
}
else
{
lean_object* v_val_1368_; 
v_val_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_val_1368_);
lean_dec_ref(v___x_1367_);
v___y_1349_ = v___y_1366_;
v___y_1350_ = v_val_1368_;
goto v___jp_1348_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33___boxed(lean_object* v___x_1375_, lean_object* v_as_1376_, lean_object* v_sz_1377_, lean_object* v_i_1378_, lean_object* v_b_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
uint8_t v___x_33440__boxed_1383_; size_t v_sz_boxed_1384_; size_t v_i_boxed_1385_; lean_object* v_res_1386_; 
v___x_33440__boxed_1383_ = lean_unbox(v___x_1375_);
v_sz_boxed_1384_ = lean_unbox_usize(v_sz_1377_);
lean_dec(v_sz_1377_);
v_i_boxed_1385_ = lean_unbox_usize(v_i_1378_);
lean_dec(v_i_1378_);
v_res_1386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33(v___x_33440__boxed_1383_, v_as_1376_, v_sz_boxed_1384_, v_i_boxed_1385_, v_b_1379_, v___y_1380_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec_ref(v_as_1376_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19(lean_object* v_init_1387_, uint8_t v___x_1388_, lean_object* v_n_1389_, lean_object* v_b_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
if (lean_obj_tag(v_n_1389_) == 0)
{
lean_object* v_cs_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1428_; 
v_cs_1394_ = lean_ctor_get(v_n_1389_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_n_1389_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1396_ = v_n_1389_;
v_isShared_1397_ = v_isSharedCheck_1428_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_cs_1394_);
lean_dec(v_n_1389_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1428_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; size_t v_sz_1400_; size_t v___x_1401_; lean_object* v___x_1402_; 
v___x_1398_ = lean_box(0);
v___x_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
lean_ctor_set(v___x_1399_, 1, v_b_1390_);
v_sz_1400_ = lean_array_size(v_cs_1394_);
v___x_1401_ = ((size_t)0ULL);
v___x_1402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__32(v_init_1387_, v___x_1388_, v_cs_1394_, v_sz_1400_, v___x_1401_, v___x_1399_, v___y_1391_, v___y_1392_);
lean_dec_ref(v_cs_1394_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1419_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1405_ = v___x_1402_;
v_isShared_1406_ = v_isSharedCheck_1419_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1402_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1419_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v_fst_1407_; 
v_fst_1407_ = lean_ctor_get(v_a_1403_, 0);
if (lean_obj_tag(v_fst_1407_) == 0)
{
lean_object* v_snd_1408_; lean_object* v___x_1410_; 
v_snd_1408_ = lean_ctor_get(v_a_1403_, 1);
lean_inc(v_snd_1408_);
lean_dec(v_a_1403_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set_tag(v___x_1396_, 1);
lean_ctor_set(v___x_1396_, 0, v_snd_1408_);
v___x_1410_ = v___x_1396_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_snd_1408_);
v___x_1410_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1412_; 
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v___x_1410_);
v___x_1412_ = v___x_1405_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
else
{
lean_object* v_val_1415_; lean_object* v___x_1417_; 
lean_inc_ref(v_fst_1407_);
lean_dec(v_a_1403_);
lean_del_object(v___x_1396_);
v_val_1415_ = lean_ctor_get(v_fst_1407_, 0);
lean_inc(v_val_1415_);
lean_dec_ref(v_fst_1407_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v_val_1415_);
v___x_1417_ = v___x_1405_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_val_1415_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_del_object(v___x_1396_);
v_a_1420_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1402_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1402_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
else
{
lean_object* v_vs_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1463_; 
v_vs_1429_ = lean_ctor_get(v_n_1389_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_n_1389_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1431_ = v_n_1389_;
v_isShared_1432_ = v_isSharedCheck_1463_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_vs_1429_);
lean_dec(v_n_1389_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1463_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; size_t v_sz_1435_; size_t v___x_1436_; lean_object* v___x_1437_; 
v___x_1433_ = lean_box(0);
v___x_1434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
lean_ctor_set(v___x_1434_, 1, v_b_1390_);
v_sz_1435_ = lean_array_size(v_vs_1429_);
v___x_1436_ = ((size_t)0ULL);
v___x_1437_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33(v___x_1388_, v_vs_1429_, v_sz_1435_, v___x_1436_, v___x_1434_, v___y_1391_, v___y_1392_);
lean_dec_ref(v_vs_1429_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1454_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1440_ = v___x_1437_;
v_isShared_1441_ = v_isSharedCheck_1454_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1437_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1454_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v_fst_1442_; 
v_fst_1442_ = lean_ctor_get(v_a_1438_, 0);
if (lean_obj_tag(v_fst_1442_) == 0)
{
lean_object* v_snd_1443_; lean_object* v___x_1445_; 
v_snd_1443_ = lean_ctor_get(v_a_1438_, 1);
lean_inc(v_snd_1443_);
lean_dec(v_a_1438_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v_snd_1443_);
v___x_1445_ = v___x_1431_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_snd_1443_);
v___x_1445_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1447_; 
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v___x_1445_);
v___x_1447_ = v___x_1440_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1445_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
else
{
lean_object* v_val_1450_; lean_object* v___x_1452_; 
lean_inc_ref(v_fst_1442_);
lean_dec(v_a_1438_);
lean_del_object(v___x_1431_);
v_val_1450_ = lean_ctor_get(v_fst_1442_, 0);
lean_inc(v_val_1450_);
lean_dec_ref(v_fst_1442_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v_val_1450_);
v___x_1452_ = v___x_1440_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_val_1450_);
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
else
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
lean_del_object(v___x_1431_);
v_a_1455_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1437_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1437_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__32(lean_object* v_init_1464_, uint8_t v___x_1465_, lean_object* v_as_1466_, size_t v_sz_1467_, size_t v_i_1468_, lean_object* v_b_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
uint8_t v___x_1473_; 
v___x_1473_ = lean_usize_dec_lt(v_i_1468_, v_sz_1467_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; 
v___x_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1474_, 0, v_b_1469_);
return v___x_1474_;
}
else
{
lean_object* v_snd_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1509_; 
v_snd_1475_ = lean_ctor_get(v_b_1469_, 1);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_b_1469_);
if (v_isSharedCheck_1509_ == 0)
{
lean_object* v_unused_1510_; 
v_unused_1510_ = lean_ctor_get(v_b_1469_, 0);
lean_dec(v_unused_1510_);
v___x_1477_ = v_b_1469_;
v_isShared_1478_ = v_isSharedCheck_1509_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_snd_1475_);
lean_dec(v_b_1469_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1509_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v_a_1479_; lean_object* v___x_1480_; 
v_a_1479_ = lean_array_uget_borrowed(v_as_1466_, v_i_1468_);
lean_inc(v_snd_1475_);
lean_inc(v_a_1479_);
v___x_1480_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19(v_init_1464_, v___x_1465_, v_a_1479_, v_snd_1475_, v___y_1470_, v___y_1471_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1500_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1500_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1500_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
if (lean_obj_tag(v_a_1481_) == 0)
{
lean_object* v___x_1485_; lean_object* v___x_1487_; 
v___x_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1485_, 0, v_a_1481_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 0, v___x_1485_);
v___x_1487_ = v___x_1477_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1485_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_snd_1475_);
v___x_1487_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1489_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1487_);
v___x_1489_ = v___x_1483_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1487_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1493_; lean_object* v___x_1495_; 
lean_del_object(v___x_1483_);
lean_dec(v_snd_1475_);
v_a_1492_ = lean_ctor_get(v_a_1481_, 0);
lean_inc(v_a_1492_);
lean_dec_ref(v_a_1481_);
v___x_1493_ = lean_box(0);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 1, v_a_1492_);
lean_ctor_set(v___x_1477_, 0, v___x_1493_);
v___x_1495_ = v___x_1477_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1493_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_a_1492_);
v___x_1495_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
size_t v___x_1496_; size_t v___x_1497_; 
v___x_1496_ = ((size_t)1ULL);
v___x_1497_ = lean_usize_add(v_i_1468_, v___x_1496_);
v_i_1468_ = v___x_1497_;
v_b_1469_ = v___x_1495_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
lean_del_object(v___x_1477_);
lean_dec(v_snd_1475_);
v_a_1501_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1480_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1480_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__32___boxed(lean_object* v_init_1511_, lean_object* v___x_1512_, lean_object* v_as_1513_, lean_object* v_sz_1514_, lean_object* v_i_1515_, lean_object* v_b_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
uint8_t v___x_33521__boxed_1520_; size_t v_sz_boxed_1521_; size_t v_i_boxed_1522_; lean_object* v_res_1523_; 
v___x_33521__boxed_1520_ = lean_unbox(v___x_1512_);
v_sz_boxed_1521_ = lean_unbox_usize(v_sz_1514_);
lean_dec(v_sz_1514_);
v_i_boxed_1522_ = lean_unbox_usize(v_i_1515_);
lean_dec(v_i_1515_);
v_res_1523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__32(v_init_1511_, v___x_33521__boxed_1520_, v_as_1513_, v_sz_boxed_1521_, v_i_boxed_1522_, v_b_1516_, v___y_1517_, v___y_1518_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec_ref(v_as_1513_);
lean_dec_ref(v_init_1511_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19___boxed(lean_object* v_init_1524_, lean_object* v___x_1525_, lean_object* v_n_1526_, lean_object* v_b_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
uint8_t v___x_33541__boxed_1531_; lean_object* v_res_1532_; 
v___x_33541__boxed_1531_ = lean_unbox(v___x_1525_);
v_res_1532_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19(v_init_1524_, v___x_33541__boxed_1531_, v_n_1526_, v_b_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec_ref(v_init_1524_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20_spec__35___redArg(uint8_t v___x_1533_, lean_object* v_as_1534_, size_t v_sz_1535_, size_t v_i_1536_, lean_object* v_b_1537_, lean_object* v___y_1538_){
_start:
{
uint8_t v___x_1540_; 
v___x_1540_ = lean_usize_dec_lt(v_i_1536_, v_sz_1535_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; 
v___x_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1541_, 0, v_b_1537_);
return v___x_1541_;
}
else
{
lean_object* v_snd_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1579_; 
v_snd_1542_ = lean_ctor_get(v_b_1537_, 1);
v_isSharedCheck_1579_ = !lean_is_exclusive(v_b_1537_);
if (v_isSharedCheck_1579_ == 0)
{
lean_object* v_unused_1580_; 
v_unused_1580_ = lean_ctor_get(v_b_1537_, 0);
lean_dec(v_unused_1580_);
v___x_1544_ = v_b_1537_;
v_isShared_1545_ = v_isSharedCheck_1579_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_snd_1542_);
lean_dec(v_b_1537_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1579_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v_ref_1546_; lean_object* v_a_1547_; lean_object* v_ref_1548_; lean_object* v_msg_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1578_; 
v_ref_1546_ = lean_ctor_get(v___y_1538_, 5);
v_a_1547_ = lean_array_uget(v_as_1534_, v_i_1536_);
v_ref_1548_ = lean_ctor_get(v_a_1547_, 0);
v_msg_1549_ = lean_ctor_get(v_a_1547_, 1);
v_isSharedCheck_1578_ = !lean_is_exclusive(v_a_1547_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1551_ = v_a_1547_;
v_isShared_1552_ = v_isSharedCheck_1578_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_msg_1549_);
lean_inc(v_ref_1548_);
lean_dec(v_a_1547_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1578_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1553_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v_ref_1570_; lean_object* v___y_1572_; lean_object* v___x_1575_; 
v___x_1553_ = lean_box(0);
v_ref_1570_ = l_Lean_replaceRef(v_ref_1548_, v_ref_1546_);
lean_dec(v_ref_1548_);
v___x_1575_ = l_Lean_Syntax_getPos_x3f(v_ref_1570_, v___x_1533_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v___x_1576_; 
v___x_1576_ = lean_unsigned_to_nat(0u);
v___y_1572_ = v___x_1576_;
goto v___jp_1571_;
}
else
{
lean_object* v_val_1577_; 
v_val_1577_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_val_1577_);
lean_dec_ref(v___x_1575_);
v___y_1572_ = v_val_1577_;
goto v___jp_1571_;
}
v___jp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 1, v___y_1556_);
lean_ctor_set(v___x_1544_, 0, v___y_1555_);
v___x_1558_ = v___x_1544_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___y_1555_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v___y_1556_);
v___x_1558_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v_pos2traces_1562_; lean_object* v___x_1564_; 
v___x_1559_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42___redArg___closed__0));
v___x_1560_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12___redArg(v_snd_1542_, v___x_1558_, v___x_1559_);
v___x_1561_ = lean_array_push(v___x_1560_, v_msg_1549_);
v_pos2traces_1562_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13___redArg(v_snd_1542_, v___x_1558_, v___x_1561_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 1, v_pos2traces_1562_);
lean_ctor_set(v___x_1551_, 0, v___x_1553_);
v___x_1564_ = v___x_1551_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v_pos2traces_1562_);
v___x_1564_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
size_t v___x_1565_; size_t v___x_1566_; 
v___x_1565_ = ((size_t)1ULL);
v___x_1566_ = lean_usize_add(v_i_1536_, v___x_1565_);
v_i_1536_ = v___x_1566_;
v_b_1537_ = v___x_1564_;
goto _start;
}
}
}
v___jp_1571_:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1570_, v___x_1533_);
lean_dec(v_ref_1570_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_inc(v___y_1572_);
v___y_1555_ = v___y_1572_;
v___y_1556_ = v___y_1572_;
goto v___jp_1554_;
}
else
{
lean_object* v_val_1574_; 
v_val_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_val_1574_);
lean_dec_ref(v___x_1573_);
v___y_1555_ = v___y_1572_;
v___y_1556_ = v_val_1574_;
goto v___jp_1554_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20_spec__35___redArg___boxed(lean_object* v___x_1581_, lean_object* v_as_1582_, lean_object* v_sz_1583_, lean_object* v_i_1584_, lean_object* v_b_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
uint8_t v___x_33748__boxed_1588_; size_t v_sz_boxed_1589_; size_t v_i_boxed_1590_; lean_object* v_res_1591_; 
v___x_33748__boxed_1588_ = lean_unbox(v___x_1581_);
v_sz_boxed_1589_ = lean_unbox_usize(v_sz_1583_);
lean_dec(v_sz_1583_);
v_i_boxed_1590_ = lean_unbox_usize(v_i_1584_);
lean_dec(v_i_1584_);
v_res_1591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20_spec__35___redArg(v___x_33748__boxed_1588_, v_as_1582_, v_sz_boxed_1589_, v_i_boxed_1590_, v_b_1585_, v___y_1586_);
lean_dec_ref(v___y_1586_);
lean_dec_ref(v_as_1582_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20(uint8_t v___x_1592_, lean_object* v_as_1593_, size_t v_sz_1594_, size_t v_i_1595_, lean_object* v_b_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
uint8_t v___x_1600_; 
v___x_1600_ = lean_usize_dec_lt(v_i_1595_, v_sz_1594_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1601_; 
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v_b_1596_);
return v___x_1601_;
}
else
{
lean_object* v_snd_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1639_; 
v_snd_1602_ = lean_ctor_get(v_b_1596_, 1);
v_isSharedCheck_1639_ = !lean_is_exclusive(v_b_1596_);
if (v_isSharedCheck_1639_ == 0)
{
lean_object* v_unused_1640_; 
v_unused_1640_ = lean_ctor_get(v_b_1596_, 0);
lean_dec(v_unused_1640_);
v___x_1604_ = v_b_1596_;
v_isShared_1605_ = v_isSharedCheck_1639_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_snd_1602_);
lean_dec(v_b_1596_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1639_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v_ref_1606_; lean_object* v_a_1607_; lean_object* v_ref_1608_; lean_object* v_msg_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1638_; 
v_ref_1606_ = lean_ctor_get(v___y_1597_, 5);
v_a_1607_ = lean_array_uget(v_as_1593_, v_i_1595_);
v_ref_1608_ = lean_ctor_get(v_a_1607_, 0);
v_msg_1609_ = lean_ctor_get(v_a_1607_, 1);
v_isSharedCheck_1638_ = !lean_is_exclusive(v_a_1607_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1611_ = v_a_1607_;
v_isShared_1612_ = v_isSharedCheck_1638_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_msg_1609_);
lean_inc(v_ref_1608_);
lean_dec(v_a_1607_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1638_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1613_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v_ref_1630_; lean_object* v___y_1632_; lean_object* v___x_1635_; 
v___x_1613_ = lean_box(0);
v_ref_1630_ = l_Lean_replaceRef(v_ref_1608_, v_ref_1606_);
lean_dec(v_ref_1608_);
v___x_1635_ = l_Lean_Syntax_getPos_x3f(v_ref_1630_, v___x_1592_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v___x_1636_; 
v___x_1636_ = lean_unsigned_to_nat(0u);
v___y_1632_ = v___x_1636_;
goto v___jp_1631_;
}
else
{
lean_object* v_val_1637_; 
v_val_1637_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_val_1637_);
lean_dec_ref(v___x_1635_);
v___y_1632_ = v_val_1637_;
goto v___jp_1631_;
}
v___jp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 1, v___y_1616_);
lean_ctor_set(v___x_1604_, 0, v___y_1615_);
v___x_1618_ = v___x_1604_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___y_1615_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v___y_1616_);
v___x_1618_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v_pos2traces_1622_; lean_object* v___x_1624_; 
v___x_1619_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42___redArg___closed__0));
v___x_1620_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12___redArg(v_snd_1602_, v___x_1618_, v___x_1619_);
v___x_1621_ = lean_array_push(v___x_1620_, v_msg_1609_);
v_pos2traces_1622_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13___redArg(v_snd_1602_, v___x_1618_, v___x_1621_);
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 1, v_pos2traces_1622_);
lean_ctor_set(v___x_1611_, 0, v___x_1613_);
v___x_1624_ = v___x_1611_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1613_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v_pos2traces_1622_);
v___x_1624_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
size_t v___x_1625_; size_t v___x_1626_; lean_object* v___x_1627_; 
v___x_1625_ = ((size_t)1ULL);
v___x_1626_ = lean_usize_add(v_i_1595_, v___x_1625_);
v___x_1627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20_spec__35___redArg(v___x_1592_, v_as_1593_, v_sz_1594_, v___x_1626_, v___x_1624_, v___y_1597_);
return v___x_1627_;
}
}
}
v___jp_1631_:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1630_, v___x_1592_);
lean_dec(v_ref_1630_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_inc(v___y_1632_);
v___y_1615_ = v___y_1632_;
v___y_1616_ = v___y_1632_;
goto v___jp_1614_;
}
else
{
lean_object* v_val_1634_; 
v_val_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_val_1634_);
lean_dec_ref(v___x_1633_);
v___y_1615_ = v___y_1632_;
v___y_1616_ = v_val_1634_;
goto v___jp_1614_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20___boxed(lean_object* v___x_1641_, lean_object* v_as_1642_, lean_object* v_sz_1643_, lean_object* v_i_1644_, lean_object* v_b_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
uint8_t v___x_33828__boxed_1649_; size_t v_sz_boxed_1650_; size_t v_i_boxed_1651_; lean_object* v_res_1652_; 
v___x_33828__boxed_1649_ = lean_unbox(v___x_1641_);
v_sz_boxed_1650_ = lean_unbox_usize(v_sz_1643_);
lean_dec(v_sz_1643_);
v_i_boxed_1651_ = lean_unbox_usize(v_i_1644_);
lean_dec(v_i_1644_);
v_res_1652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20(v___x_33828__boxed_1649_, v_as_1642_, v_sz_boxed_1650_, v_i_boxed_1651_, v_b_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec_ref(v_as_1642_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14(uint8_t v___x_1653_, lean_object* v_t_1654_, lean_object* v_init_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v_root_1659_; lean_object* v_tail_1660_; lean_object* v___x_1661_; 
v_root_1659_ = lean_ctor_get(v_t_1654_, 0);
lean_inc_ref(v_root_1659_);
v_tail_1660_ = lean_ctor_get(v_t_1654_, 1);
lean_inc_ref(v_tail_1660_);
lean_dec_ref(v_t_1654_);
lean_inc_ref(v_init_1655_);
v___x_1661_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19(v_init_1655_, v___x_1653_, v_root_1659_, v_init_1655_, v___y_1656_, v___y_1657_);
lean_dec_ref(v_init_1655_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1698_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1698_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1698_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
if (lean_obj_tag(v_a_1662_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1668_; 
lean_dec_ref(v_tail_1660_);
v_a_1666_ = lean_ctor_get(v_a_1662_, 0);
lean_inc(v_a_1666_);
lean_dec_ref(v_a_1662_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v_a_1666_);
v___x_1668_ = v___x_1664_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1666_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; size_t v_sz_1673_; size_t v___x_1674_; lean_object* v___x_1675_; 
lean_del_object(v___x_1664_);
v_a_1670_ = lean_ctor_get(v_a_1662_, 0);
lean_inc(v_a_1670_);
lean_dec_ref(v_a_1662_);
v___x_1671_ = lean_box(0);
v___x_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
lean_ctor_set(v___x_1672_, 1, v_a_1670_);
v_sz_1673_ = lean_array_size(v_tail_1660_);
v___x_1674_ = ((size_t)0ULL);
v___x_1675_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20(v___x_1653_, v_tail_1660_, v_sz_1673_, v___x_1674_, v___x_1672_, v___y_1656_, v___y_1657_);
lean_dec_ref(v_tail_1660_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1689_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1678_ = v___x_1675_;
v_isShared_1679_ = v_isSharedCheck_1689_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1675_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1689_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v_fst_1680_; 
v_fst_1680_ = lean_ctor_get(v_a_1676_, 0);
if (lean_obj_tag(v_fst_1680_) == 0)
{
lean_object* v_snd_1681_; lean_object* v___x_1683_; 
v_snd_1681_ = lean_ctor_get(v_a_1676_, 1);
lean_inc(v_snd_1681_);
lean_dec(v_a_1676_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 0, v_snd_1681_);
v___x_1683_ = v___x_1678_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_snd_1681_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
else
{
lean_object* v_val_1685_; lean_object* v___x_1687_; 
lean_inc_ref(v_fst_1680_);
lean_dec(v_a_1676_);
v_val_1685_ = lean_ctor_get(v_fst_1680_, 0);
lean_inc(v_val_1685_);
lean_dec_ref(v_fst_1680_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 0, v_val_1685_);
v___x_1687_ = v___x_1678_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_val_1685_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
v_a_1690_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1675_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1675_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
}
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
lean_dec_ref(v_tail_1660_);
v_a_1699_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1661_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1661_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14___boxed(lean_object* v___x_1707_, lean_object* v_t_1708_, lean_object* v_init_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
uint8_t v___x_33909__boxed_1713_; lean_object* v_res_1714_; 
v___x_33909__boxed_1713_ = lean_unbox(v___x_1707_);
v_res_1714_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14(v___x_33909__boxed_1713_, v_t_1708_, v_init_1709_, v___y_1710_, v___y_1711_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
return v_res_1714_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0(uint8_t v___x_1722_, uint8_t v_suppressElabErrors_1723_, lean_object* v___x_1724_, lean_object* v_x_1725_){
_start:
{
if (lean_obj_tag(v_x_1725_) == 1)
{
lean_object* v_pre_1726_; 
v_pre_1726_ = lean_ctor_get(v_x_1725_, 0);
switch(lean_obj_tag(v_pre_1726_))
{
case 1:
{
lean_object* v_pre_1727_; 
v_pre_1727_ = lean_ctor_get(v_pre_1726_, 0);
switch(lean_obj_tag(v_pre_1727_))
{
case 0:
{
lean_object* v_str_1728_; lean_object* v_str_1729_; lean_object* v___x_1730_; uint8_t v___x_1731_; 
v_str_1728_ = lean_ctor_get(v_x_1725_, 1);
v_str_1729_ = lean_ctor_get(v_pre_1726_, 1);
v___x_1730_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__0));
v___x_1731_ = lean_string_dec_eq(v_str_1729_, v___x_1730_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; uint8_t v___x_1733_; 
v___x_1732_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__1));
v___x_1733_ = lean_string_dec_eq(v_str_1729_, v___x_1732_);
if (v___x_1733_ == 0)
{
return v___x_1722_;
}
else
{
lean_object* v___x_1734_; uint8_t v___x_1735_; 
v___x_1734_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__2));
v___x_1735_ = lean_string_dec_eq(v_str_1728_, v___x_1734_);
if (v___x_1735_ == 0)
{
return v___x_1722_;
}
else
{
return v_suppressElabErrors_1723_;
}
}
}
else
{
lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1736_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__3));
v___x_1737_ = lean_string_dec_eq(v_str_1728_, v___x_1736_);
if (v___x_1737_ == 0)
{
return v___x_1722_;
}
else
{
return v_suppressElabErrors_1723_;
}
}
}
case 1:
{
lean_object* v_pre_1738_; 
v_pre_1738_ = lean_ctor_get(v_pre_1727_, 0);
if (lean_obj_tag(v_pre_1738_) == 0)
{
lean_object* v_str_1739_; lean_object* v_str_1740_; lean_object* v_str_1741_; lean_object* v___x_1742_; uint8_t v___x_1743_; 
v_str_1739_ = lean_ctor_get(v_x_1725_, 1);
v_str_1740_ = lean_ctor_get(v_pre_1726_, 1);
v_str_1741_ = lean_ctor_get(v_pre_1727_, 1);
v___x_1742_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__4));
v___x_1743_ = lean_string_dec_eq(v_str_1741_, v___x_1742_);
if (v___x_1743_ == 0)
{
return v___x_1722_;
}
else
{
lean_object* v___x_1744_; uint8_t v___x_1745_; 
v___x_1744_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__5));
v___x_1745_ = lean_string_dec_eq(v_str_1740_, v___x_1744_);
if (v___x_1745_ == 0)
{
return v___x_1722_;
}
else
{
lean_object* v___x_1746_; uint8_t v___x_1747_; 
v___x_1746_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__6));
v___x_1747_ = lean_string_dec_eq(v_str_1739_, v___x_1746_);
if (v___x_1747_ == 0)
{
return v___x_1722_;
}
else
{
return v_suppressElabErrors_1723_;
}
}
}
}
else
{
return v___x_1722_;
}
}
default: 
{
return v___x_1722_;
}
}
}
case 0:
{
lean_object* v_str_1748_; uint8_t v___x_1749_; 
v_str_1748_ = lean_ctor_get(v_x_1725_, 1);
v___x_1749_ = lean_string_dec_eq(v_str_1748_, v___x_1724_);
if (v___x_1749_ == 0)
{
return v___x_1722_;
}
else
{
return v_suppressElabErrors_1723_;
}
}
default: 
{
return v___x_1722_;
}
}
}
else
{
return v___x_1722_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___boxed(lean_object* v___x_1750_, lean_object* v_suppressElabErrors_1751_, lean_object* v___x_1752_, lean_object* v_x_1753_){
_start:
{
uint8_t v___x_34021__boxed_1754_; uint8_t v_suppressElabErrors_boxed_1755_; uint8_t v_res_1756_; lean_object* v_r_1757_; 
v___x_34021__boxed_1754_ = lean_unbox(v___x_1750_);
v_suppressElabErrors_boxed_1755_ = lean_unbox(v_suppressElabErrors_1751_);
v_res_1756_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0(v___x_34021__boxed_1754_, v_suppressElabErrors_boxed_1755_, v___x_1752_, v_x_1753_);
lean_dec(v_x_1753_);
lean_dec_ref(v___x_1752_);
v_r_1757_ = lean_box(v_res_1756_);
return v_r_1757_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___closed__0(void){
_start:
{
lean_object* v___x_1758_; double v___x_1759_; 
v___x_1758_ = lean_unsigned_to_nat(0u);
v___x_1759_ = lean_float_of_nat(v___x_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15(uint8_t v___x_1761_, lean_object* v_as_1762_, size_t v_sz_1763_, size_t v_i_1764_, lean_object* v_b_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v_a_1770_; uint8_t v___x_1774_; 
v___x_1774_ = lean_usize_dec_lt(v_i_1764_, v_sz_1763_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; 
v___x_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1775_, 0, v_b_1765_);
return v___x_1775_;
}
else
{
lean_object* v_a_1776_; lean_object* v_fst_1777_; lean_object* v_snd_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1854_; 
v_a_1776_ = lean_array_uget(v_as_1762_, v_i_1764_);
v_fst_1777_ = lean_ctor_get(v_a_1776_, 0);
v_snd_1778_ = lean_ctor_get(v_a_1776_, 1);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_a_1776_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1780_ = v_a_1776_;
v_isShared_1781_ = v_isSharedCheck_1854_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_snd_1778_);
lean_inc(v_fst_1777_);
lean_dec(v_a_1776_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1854_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v_fst_1782_; lean_object* v_snd_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1853_; 
v_fst_1782_ = lean_ctor_get(v_fst_1777_, 0);
v_snd_1783_ = lean_ctor_get(v_fst_1777_, 1);
v_isSharedCheck_1853_ = !lean_is_exclusive(v_fst_1777_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1785_ = v_fst_1777_;
v_isShared_1786_ = v_isSharedCheck_1853_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_snd_1783_);
lean_inc(v_fst_1782_);
lean_dec(v_fst_1777_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1853_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; double v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v_fileName_1792_; lean_object* v_fileMap_1793_; uint8_t v_suppressElabErrors_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1801_; 
v___x_1787_ = lean_box(0);
v___x_1788_ = lean_box(0);
v___x_1789_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___closed__0);
v___x_1790_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___closed__1));
v___x_1791_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1791_, 0, v___x_1787_);
lean_ctor_set(v___x_1791_, 1, v___x_1788_);
lean_ctor_set(v___x_1791_, 2, v___x_1790_);
lean_ctor_set_float(v___x_1791_, sizeof(void*)*3, v___x_1789_);
lean_ctor_set_float(v___x_1791_, sizeof(void*)*3 + 8, v___x_1789_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 16, v___x_1774_);
v_fileName_1792_ = lean_ctor_get(v___y_1766_, 0);
v_fileMap_1793_ = lean_ctor_get(v___y_1766_, 1);
v_suppressElabErrors_1794_ = lean_ctor_get_uint8(v___y_1766_, sizeof(void*)*14 + 1);
v___x_1795_ = lean_box(0);
v___x_1796_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__4_spec__4___closed__0));
v___x_1797_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__4_spec__4___closed__1));
v___x_1798_ = l_Lean_MessageData_nil;
v___x_1799_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1791_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
lean_ctor_set(v___x_1799_, 2, v_snd_1778_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set_tag(v___x_1785_, 8);
lean_ctor_set(v___x_1785_, 1, v___x_1799_);
lean_ctor_set(v___x_1785_, 0, v___x_1797_);
v___x_1801_ = v___x_1785_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1797_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v___x_1799_);
v___x_1801_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
uint8_t v___x_1802_; lean_object* v___x_1803_; lean_object* v___y_1805_; lean_object* v___y_1806_; 
v___x_1802_ = 0;
lean_inc_ref(v_fileMap_1793_);
lean_inc_ref(v_fileName_1792_);
v___x_1803_ = l_Lean_Elab_mkMessageCore(v_fileName_1792_, v_fileMap_1793_, v___x_1801_, v___x_1802_, v_fst_1782_, v_snd_1783_);
lean_dec(v_snd_1783_);
lean_dec(v_fst_1782_);
if (v_suppressElabErrors_1794_ == 0)
{
v___y_1805_ = v___y_1766_;
v___y_1806_ = v___y_1767_;
goto v___jp_1804_;
}
else
{
lean_object* v_data_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___f_1850_; uint8_t v___x_1851_; 
v_data_1847_ = lean_ctor_get(v___x_1803_, 4);
lean_inc(v_data_1847_);
v___x_1848_ = lean_box(v___x_1761_);
v___x_1849_ = lean_box(v_suppressElabErrors_1794_);
v___f_1850_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1850_, 0, v___x_1848_);
lean_closure_set(v___f_1850_, 1, v___x_1849_);
lean_closure_set(v___f_1850_, 2, v___x_1796_);
v___x_1851_ = l_Lean_MessageData_hasTag(v___f_1850_, v_data_1847_);
if (v___x_1851_ == 0)
{
lean_dec_ref(v___x_1803_);
lean_del_object(v___x_1780_);
v_a_1770_ = v___x_1795_;
goto v___jp_1769_;
}
else
{
v___y_1805_ = v___y_1766_;
v___y_1806_ = v___y_1767_;
goto v___jp_1804_;
}
}
v___jp_1804_:
{
lean_object* v___x_1807_; lean_object* v_fileName_1808_; lean_object* v_pos_1809_; lean_object* v_endPos_1810_; uint8_t v_keepFullRange_1811_; uint8_t v_severity_1812_; uint8_t v_isSilent_1813_; lean_object* v_caption_1814_; lean_object* v_data_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1846_; 
v___x_1807_ = lean_st_ref_take(v___y_1806_);
v_fileName_1808_ = lean_ctor_get(v___x_1803_, 0);
v_pos_1809_ = lean_ctor_get(v___x_1803_, 1);
v_endPos_1810_ = lean_ctor_get(v___x_1803_, 2);
v_keepFullRange_1811_ = lean_ctor_get_uint8(v___x_1803_, sizeof(void*)*5);
v_severity_1812_ = lean_ctor_get_uint8(v___x_1803_, sizeof(void*)*5 + 1);
v_isSilent_1813_ = lean_ctor_get_uint8(v___x_1803_, sizeof(void*)*5 + 2);
v_caption_1814_ = lean_ctor_get(v___x_1803_, 3);
v_data_1815_ = lean_ctor_get(v___x_1803_, 4);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1817_ = v___x_1803_;
v_isShared_1818_ = v_isSharedCheck_1846_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_data_1815_);
lean_inc(v_caption_1814_);
lean_inc(v_endPos_1810_);
lean_inc(v_pos_1809_);
lean_inc(v_fileName_1808_);
lean_dec(v___x_1803_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1846_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v_currNamespace_1819_; lean_object* v_openDecls_1820_; lean_object* v_env_1821_; lean_object* v_nextMacroScope_1822_; lean_object* v_ngen_1823_; lean_object* v_auxDeclNGen_1824_; lean_object* v_traceState_1825_; lean_object* v_cache_1826_; lean_object* v_messages_1827_; lean_object* v_infoState_1828_; lean_object* v_snapshotTasks_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1845_; 
v_currNamespace_1819_ = lean_ctor_get(v___y_1805_, 6);
v_openDecls_1820_ = lean_ctor_get(v___y_1805_, 7);
v_env_1821_ = lean_ctor_get(v___x_1807_, 0);
v_nextMacroScope_1822_ = lean_ctor_get(v___x_1807_, 1);
v_ngen_1823_ = lean_ctor_get(v___x_1807_, 2);
v_auxDeclNGen_1824_ = lean_ctor_get(v___x_1807_, 3);
v_traceState_1825_ = lean_ctor_get(v___x_1807_, 4);
v_cache_1826_ = lean_ctor_get(v___x_1807_, 5);
v_messages_1827_ = lean_ctor_get(v___x_1807_, 6);
v_infoState_1828_ = lean_ctor_get(v___x_1807_, 7);
v_snapshotTasks_1829_ = lean_ctor_get(v___x_1807_, 8);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1831_ = v___x_1807_;
v_isShared_1832_ = v_isSharedCheck_1845_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_snapshotTasks_1829_);
lean_inc(v_infoState_1828_);
lean_inc(v_messages_1827_);
lean_inc(v_cache_1826_);
lean_inc(v_traceState_1825_);
lean_inc(v_auxDeclNGen_1824_);
lean_inc(v_ngen_1823_);
lean_inc(v_nextMacroScope_1822_);
lean_inc(v_env_1821_);
lean_dec(v___x_1807_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1845_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
lean_inc(v_openDecls_1820_);
lean_inc(v_currNamespace_1819_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 1, v_openDecls_1820_);
lean_ctor_set(v___x_1780_, 0, v_currNamespace_1819_);
v___x_1834_ = v___x_1780_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_currNamespace_1819_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v_openDecls_1820_);
v___x_1834_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
lean_object* v___x_1835_; lean_object* v___x_1837_; 
v___x_1835_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
lean_ctor_set(v___x_1835_, 1, v_data_1815_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 4, v___x_1835_);
v___x_1837_ = v___x_1817_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_fileName_1808_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_pos_1809_);
lean_ctor_set(v_reuseFailAlloc_1843_, 2, v_endPos_1810_);
lean_ctor_set(v_reuseFailAlloc_1843_, 3, v_caption_1814_);
lean_ctor_set(v_reuseFailAlloc_1843_, 4, v___x_1835_);
lean_ctor_set_uint8(v_reuseFailAlloc_1843_, sizeof(void*)*5, v_keepFullRange_1811_);
lean_ctor_set_uint8(v_reuseFailAlloc_1843_, sizeof(void*)*5 + 1, v_severity_1812_);
lean_ctor_set_uint8(v_reuseFailAlloc_1843_, sizeof(void*)*5 + 2, v_isSilent_1813_);
v___x_1837_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
lean_object* v___x_1838_; lean_object* v___x_1840_; 
v___x_1838_ = l_Lean_MessageLog_add(v___x_1837_, v_messages_1827_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 6, v___x_1838_);
v___x_1840_ = v___x_1831_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_env_1821_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v_nextMacroScope_1822_);
lean_ctor_set(v_reuseFailAlloc_1842_, 2, v_ngen_1823_);
lean_ctor_set(v_reuseFailAlloc_1842_, 3, v_auxDeclNGen_1824_);
lean_ctor_set(v_reuseFailAlloc_1842_, 4, v_traceState_1825_);
lean_ctor_set(v_reuseFailAlloc_1842_, 5, v_cache_1826_);
lean_ctor_set(v_reuseFailAlloc_1842_, 6, v___x_1838_);
lean_ctor_set(v_reuseFailAlloc_1842_, 7, v_infoState_1828_);
lean_ctor_set(v_reuseFailAlloc_1842_, 8, v_snapshotTasks_1829_);
v___x_1840_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_st_ref_set(v___y_1806_, v___x_1840_);
v_a_1770_ = v___x_1795_;
goto v___jp_1769_;
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
v___jp_1769_:
{
size_t v___x_1771_; size_t v___x_1772_; 
v___x_1771_ = ((size_t)1ULL);
v___x_1772_ = lean_usize_add(v_i_1764_, v___x_1771_);
v_i_1764_ = v___x_1772_;
v_b_1765_ = v_a_1770_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___boxed(lean_object* v___x_1855_, lean_object* v_as_1856_, lean_object* v_sz_1857_, lean_object* v_i_1858_, lean_object* v_b_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
uint8_t v___x_34094__boxed_1863_; size_t v_sz_boxed_1864_; size_t v_i_boxed_1865_; lean_object* v_res_1866_; 
v___x_34094__boxed_1863_ = lean_unbox(v___x_1855_);
v_sz_boxed_1864_ = lean_unbox_usize(v_sz_1857_);
lean_dec(v_sz_1857_);
v_i_boxed_1865_ = lean_unbox_usize(v_i_1858_);
lean_dec(v_i_1858_);
v_res_1866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15(v___x_34094__boxed_1863_, v_as_1856_, v_sz_boxed_1864_, v_i_boxed_1865_, v_b_1859_, v___y_1860_, v___y_1861_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec_ref(v_as_1856_);
return v_res_1866_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1867_ = lean_unsigned_to_nat(32u);
v___x_1868_ = lean_mk_empty_array_with_capacity(v___x_1867_);
v___x_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
return v___x_1869_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1(void){
_start:
{
size_t v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1870_ = ((size_t)5ULL);
v___x_1871_ = lean_unsigned_to_nat(0u);
v___x_1872_ = lean_unsigned_to_nat(32u);
v___x_1873_ = lean_mk_empty_array_with_capacity(v___x_1872_);
v___x_1874_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__0);
v___x_1875_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v___x_1873_);
lean_ctor_set(v___x_1875_, 2, v___x_1871_);
lean_ctor_set(v___x_1875_, 3, v___x_1871_);
lean_ctor_set_usize(v___x_1875_, 4, v___x_1870_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg(lean_object* v___y_1876_){
_start:
{
lean_object* v___x_1878_; lean_object* v_traceState_1879_; lean_object* v_traces_1880_; lean_object* v___x_1881_; lean_object* v_traceState_1882_; lean_object* v_env_1883_; lean_object* v_nextMacroScope_1884_; lean_object* v_ngen_1885_; lean_object* v_auxDeclNGen_1886_; lean_object* v_cache_1887_; lean_object* v_messages_1888_; lean_object* v_infoState_1889_; lean_object* v_snapshotTasks_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1909_; 
v___x_1878_ = lean_st_ref_get(v___y_1876_);
v_traceState_1879_ = lean_ctor_get(v___x_1878_, 4);
lean_inc_ref(v_traceState_1879_);
lean_dec(v___x_1878_);
v_traces_1880_ = lean_ctor_get(v_traceState_1879_, 0);
lean_inc_ref(v_traces_1880_);
lean_dec_ref(v_traceState_1879_);
v___x_1881_ = lean_st_ref_take(v___y_1876_);
v_traceState_1882_ = lean_ctor_get(v___x_1881_, 4);
v_env_1883_ = lean_ctor_get(v___x_1881_, 0);
v_nextMacroScope_1884_ = lean_ctor_get(v___x_1881_, 1);
v_ngen_1885_ = lean_ctor_get(v___x_1881_, 2);
v_auxDeclNGen_1886_ = lean_ctor_get(v___x_1881_, 3);
v_cache_1887_ = lean_ctor_get(v___x_1881_, 5);
v_messages_1888_ = lean_ctor_get(v___x_1881_, 6);
v_infoState_1889_ = lean_ctor_get(v___x_1881_, 7);
v_snapshotTasks_1890_ = lean_ctor_get(v___x_1881_, 8);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1892_ = v___x_1881_;
v_isShared_1893_ = v_isSharedCheck_1909_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_snapshotTasks_1890_);
lean_inc(v_infoState_1889_);
lean_inc(v_messages_1888_);
lean_inc(v_cache_1887_);
lean_inc(v_traceState_1882_);
lean_inc(v_auxDeclNGen_1886_);
lean_inc(v_ngen_1885_);
lean_inc(v_nextMacroScope_1884_);
lean_inc(v_env_1883_);
lean_dec(v___x_1881_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1909_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
uint64_t v_tid_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1907_; 
v_tid_1894_ = lean_ctor_get_uint64(v_traceState_1882_, sizeof(void*)*1);
v_isSharedCheck_1907_ = !lean_is_exclusive(v_traceState_1882_);
if (v_isSharedCheck_1907_ == 0)
{
lean_object* v_unused_1908_; 
v_unused_1908_ = lean_ctor_get(v_traceState_1882_, 0);
lean_dec(v_unused_1908_);
v___x_1896_ = v_traceState_1882_;
v_isShared_1897_ = v_isSharedCheck_1907_;
goto v_resetjp_1895_;
}
else
{
lean_dec(v_traceState_1882_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1907_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; lean_object* v___x_1900_; 
v___x_1898_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v___x_1898_);
v___x_1900_ = v___x_1896_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1898_);
lean_ctor_set_uint64(v_reuseFailAlloc_1906_, sizeof(void*)*1, v_tid_1894_);
v___x_1900_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
lean_object* v___x_1902_; 
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 4, v___x_1900_);
v___x_1902_ = v___x_1892_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_env_1883_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v_nextMacroScope_1884_);
lean_ctor_set(v_reuseFailAlloc_1905_, 2, v_ngen_1885_);
lean_ctor_set(v_reuseFailAlloc_1905_, 3, v_auxDeclNGen_1886_);
lean_ctor_set(v_reuseFailAlloc_1905_, 4, v___x_1900_);
lean_ctor_set(v_reuseFailAlloc_1905_, 5, v_cache_1887_);
lean_ctor_set(v_reuseFailAlloc_1905_, 6, v_messages_1888_);
lean_ctor_set(v_reuseFailAlloc_1905_, 7, v_infoState_1889_);
lean_ctor_set(v_reuseFailAlloc_1905_, 8, v_snapshotTasks_1890_);
v___x_1902_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = lean_st_ref_set(v___y_1876_, v___x_1902_);
v___x_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1904_, 0, v_traces_1880_);
return v___x_1904_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___boxed(lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg(v___y_1910_);
lean_dec(v___y_1910_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__10(lean_object* v_opts_1913_, lean_object* v_opt_1914_){
_start:
{
lean_object* v_name_1915_; lean_object* v_map_1916_; lean_object* v___x_1917_; 
v_name_1915_ = lean_ctor_get(v_opt_1914_, 0);
v_map_1916_ = lean_ctor_get(v_opts_1913_, 0);
v___x_1917_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1916_, v_name_1915_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v___x_1918_; 
v___x_1918_ = lean_box(0);
return v___x_1918_;
}
else
{
lean_object* v_val_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1928_; 
v_val_1919_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1921_ = v___x_1917_;
v_isShared_1922_ = v_isSharedCheck_1928_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_val_1919_);
lean_dec(v___x_1917_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1928_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
if (lean_obj_tag(v_val_1919_) == 0)
{
lean_object* v_v_1923_; lean_object* v___x_1925_; 
v_v_1923_ = lean_ctor_get(v_val_1919_, 0);
lean_inc_ref(v_v_1923_);
lean_dec_ref(v_val_1919_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v_v_1923_);
v___x_1925_ = v___x_1921_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_v_1923_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
else
{
lean_object* v___x_1927_; 
lean_del_object(v___x_1921_);
lean_dec(v_val_1919_);
v___x_1927_ = lean_box(0);
return v___x_1927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__10___boxed(lean_object* v_opts_1929_, lean_object* v_opt_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__10(v_opts_1929_, v_opt_1930_);
lean_dec_ref(v_opt_1930_);
lean_dec_ref(v_opts_1929_);
return v_res_1931_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__8___closed__0(void){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1932_ = lean_box(0);
v___x_1933_ = lean_unsigned_to_nat(16u);
v___x_1934_ = lean_mk_array(v___x_1933_, v___x_1932_);
return v___x_1934_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__8___closed__1(void){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v_pos2traces_1937_; 
v___x_1935_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__8___closed__0, &l_Lean_addTraceAsMessages___at___00main_spec__8___closed__0_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__8___closed__0);
v___x_1936_ = lean_unsigned_to_nat(0u);
v_pos2traces_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_1937_, 0, v___x_1936_);
lean_ctor_set(v_pos2traces_1937_, 1, v___x_1935_);
return v_pos2traces_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__8(lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v_options_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v_options_1941_ = lean_ctor_get(v___y_1938_, 2);
v___x_1942_ = l_Lean_trace_profiler_output;
v___x_1943_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__10(v_options_1941_, v___x_1942_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v___x_1944_; lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_2011_; 
v___x_1944_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg(v___y_1939_);
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_1947_ = v___x_1944_;
v_isShared_1948_ = v_isSharedCheck_2011_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1944_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_2011_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
uint8_t v___x_1949_; 
v___x_1949_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_1945_);
if (v___x_1949_ == 0)
{
lean_object* v___x_1950_; lean_object* v_pos2traces_1951_; lean_object* v___x_1952_; 
lean_del_object(v___x_1947_);
v___x_1950_ = lean_unsigned_to_nat(0u);
v_pos2traces_1951_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__8___closed__1, &l_Lean_addTraceAsMessages___at___00main_spec__8___closed__1_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__8___closed__1);
v___x_1952_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14(v___x_1949_, v_a_1945_, v_pos2traces_1951_, v___y_1938_, v___y_1939_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; lean_object* v___y_1955_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1981_; lean_object* v_size_1987_; lean_object* v_buckets_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref(v___x_1952_);
v_size_1987_ = lean_ctor_get(v_a_1953_, 0);
lean_inc(v_size_1987_);
v_buckets_1988_ = lean_ctor_get(v_a_1953_, 1);
lean_inc_ref(v_buckets_1988_);
lean_dec(v_a_1953_);
v___x_1989_ = lean_mk_empty_array_with_capacity(v_size_1987_);
lean_dec(v_size_1987_);
v___x_1990_ = lean_array_get_size(v_buckets_1988_);
v___x_1991_ = lean_nat_dec_lt(v___x_1950_, v___x_1990_);
if (v___x_1991_ == 0)
{
lean_dec_ref(v_buckets_1988_);
v___y_1981_ = v___x_1989_;
goto v___jp_1980_;
}
else
{
uint8_t v___x_1992_; 
v___x_1992_ = lean_nat_dec_le(v___x_1990_, v___x_1990_);
if (v___x_1992_ == 0)
{
if (v___x_1991_ == 0)
{
lean_dec_ref(v_buckets_1988_);
v___y_1981_ = v___x_1989_;
goto v___jp_1980_;
}
else
{
size_t v___x_1993_; size_t v___x_1994_; lean_object* v___x_1995_; 
v___x_1993_ = ((size_t)0ULL);
v___x_1994_ = lean_usize_of_nat(v___x_1990_);
v___x_1995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__18(v_buckets_1988_, v___x_1993_, v___x_1994_, v___x_1989_);
lean_dec_ref(v_buckets_1988_);
v___y_1981_ = v___x_1995_;
goto v___jp_1980_;
}
}
else
{
size_t v___x_1996_; size_t v___x_1997_; lean_object* v___x_1998_; 
v___x_1996_ = ((size_t)0ULL);
v___x_1997_ = lean_usize_of_nat(v___x_1990_);
v___x_1998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__18(v_buckets_1988_, v___x_1996_, v___x_1997_, v___x_1989_);
lean_dec_ref(v_buckets_1988_);
v___y_1981_ = v___x_1998_;
goto v___jp_1980_;
}
}
v___jp_1954_:
{
lean_object* v___x_1956_; size_t v_sz_1957_; size_t v___x_1958_; lean_object* v___x_1959_; 
v___x_1956_ = lean_box(0);
v_sz_1957_ = lean_array_size(v___y_1955_);
v___x_1958_ = ((size_t)0ULL);
v___x_1959_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15(v___x_1949_, v___y_1955_, v_sz_1957_, v___x_1958_, v___x_1956_, v___y_1938_, v___y_1939_);
lean_dec_ref(v___y_1955_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1966_ == 0)
{
lean_object* v_unused_1967_; 
v_unused_1967_ = lean_ctor_get(v___x_1959_, 0);
lean_dec(v_unused_1967_);
v___x_1961_ = v___x_1959_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_dec(v___x_1959_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 0, v___x_1956_);
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1956_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
else
{
return v___x_1959_;
}
}
v___jp_1968_:
{
lean_object* v___x_1973_; 
lean_dec(v___y_1969_);
v___x_1973_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg(v___y_1971_, v___y_1970_, v___y_1972_);
lean_dec(v___y_1972_);
v___y_1955_ = v___x_1973_;
goto v___jp_1954_;
}
v___jp_1974_:
{
uint8_t v___x_1979_; 
v___x_1979_ = lean_nat_dec_le(v___y_1978_, v___y_1976_);
if (v___x_1979_ == 0)
{
lean_dec(v___y_1976_);
lean_inc(v___y_1978_);
v___y_1969_ = v___y_1975_;
v___y_1970_ = v___y_1978_;
v___y_1971_ = v___y_1977_;
v___y_1972_ = v___y_1978_;
goto v___jp_1968_;
}
else
{
v___y_1969_ = v___y_1975_;
v___y_1970_ = v___y_1978_;
v___y_1971_ = v___y_1977_;
v___y_1972_ = v___y_1976_;
goto v___jp_1968_;
}
}
v___jp_1980_:
{
lean_object* v___x_1982_; uint8_t v___x_1983_; 
v___x_1982_ = lean_array_get_size(v___y_1981_);
v___x_1983_ = lean_nat_dec_eq(v___x_1982_, v___x_1950_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; 
v___x_1984_ = lean_unsigned_to_nat(1u);
v___x_1985_ = lean_nat_sub(v___x_1982_, v___x_1984_);
v___x_1986_ = lean_nat_dec_le(v___x_1950_, v___x_1985_);
if (v___x_1986_ == 0)
{
lean_inc(v___x_1985_);
v___y_1975_ = v___x_1982_;
v___y_1976_ = v___x_1985_;
v___y_1977_ = v___y_1981_;
v___y_1978_ = v___x_1985_;
goto v___jp_1974_;
}
else
{
v___y_1975_ = v___x_1982_;
v___y_1976_ = v___x_1985_;
v___y_1977_ = v___y_1981_;
v___y_1978_ = v___x_1950_;
goto v___jp_1974_;
}
}
else
{
v___y_1955_ = v___y_1981_;
goto v___jp_1954_;
}
}
}
else
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
v_a_1999_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1952_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1952_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
else
{
lean_object* v___x_2007_; lean_object* v___x_2009_; 
lean_dec(v_a_1945_);
v___x_2007_ = lean_box(0);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 0, v___x_2007_);
v___x_2009_ = v___x_1947_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2007_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
else
{
lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2019_; 
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_2019_ == 0)
{
lean_object* v_unused_2020_; 
v_unused_2020_ = lean_ctor_get(v___x_1943_, 0);
lean_dec(v_unused_2020_);
v___x_2013_ = v___x_1943_;
v_isShared_2014_ = v_isSharedCheck_2019_;
goto v_resetjp_2012_;
}
else
{
lean_dec(v___x_1943_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2019_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2015_; lean_object* v___x_2017_; 
v___x_2015_ = lean_box(0);
if (v_isShared_2014_ == 0)
{
lean_ctor_set_tag(v___x_2013_, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2015_);
v___x_2017_ = v___x_2013_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2015_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__8___boxed(lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l_Lean_addTraceAsMessages___at___00main_spec__8(v___y_2021_, v___y_2022_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object* v_as_2025_, size_t v_i_2026_, size_t v_stop_2027_, lean_object* v_b_2028_){
_start:
{
uint8_t v___x_2029_; 
v___x_2029_ = lean_usize_dec_eq(v_i_2026_, v_stop_2027_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; lean_object* v_name_2031_; lean_object* v___x_2032_; size_t v___x_2033_; size_t v___x_2034_; 
v___x_2030_ = lean_array_uget_borrowed(v_as_2025_, v_i_2026_);
v_name_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_name_2031_);
v___x_2032_ = l_Lean_Compiler_LCNF_setDeclPublic(v_b_2028_, v_name_2031_);
v___x_2033_ = ((size_t)1ULL);
v___x_2034_ = lean_usize_add(v_i_2026_, v___x_2033_);
v_i_2026_ = v___x_2034_;
v_b_2028_ = v___x_2032_;
goto _start;
}
else
{
return v_b_2028_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object* v_as_2036_, lean_object* v_i_2037_, lean_object* v_stop_2038_, lean_object* v_b_2039_){
_start:
{
size_t v_i_boxed_2040_; size_t v_stop_boxed_2041_; lean_object* v_res_2042_; 
v_i_boxed_2040_ = lean_unbox_usize(v_i_2037_);
lean_dec(v_i_2037_);
v_stop_boxed_2041_ = lean_unbox_usize(v_stop_2038_);
lean_dec(v_stop_2038_);
v_res_2042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v_as_2036_, v_i_boxed_2040_, v_stop_boxed_2041_, v_b_2039_);
lean_dec_ref(v_as_2036_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object* v_a_2043_, lean_object* v_as_2044_, size_t v_i_2045_, size_t v_stop_2046_, lean_object* v_b_2047_){
_start:
{
lean_object* v___y_2049_; uint8_t v___x_2053_; 
v___x_2053_ = lean_usize_dec_eq(v_i_2045_, v_stop_2046_);
if (v___x_2053_ == 0)
{
lean_object* v___x_2054_; lean_object* v_name_2055_; uint8_t v___x_2056_; 
v___x_2054_ = lean_array_uget_borrowed(v_as_2044_, v_i_2045_);
v_name_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_name_2055_);
lean_inc_ref(v_a_2043_);
v___x_2056_ = l_Lean_isExtern(v_a_2043_, v_name_2055_);
if (v___x_2056_ == 0)
{
v___y_2049_ = v_b_2047_;
goto v___jp_2048_;
}
else
{
lean_object* v___x_2057_; 
lean_inc(v___x_2054_);
v___x_2057_ = lean_array_push(v_b_2047_, v___x_2054_);
v___y_2049_ = v___x_2057_;
goto v___jp_2048_;
}
}
else
{
lean_dec_ref(v_a_2043_);
return v_b_2047_;
}
v___jp_2048_:
{
size_t v___x_2050_; size_t v___x_2051_; 
v___x_2050_ = ((size_t)1ULL);
v___x_2051_ = lean_usize_add(v_i_2045_, v___x_2050_);
v_i_2045_ = v___x_2051_;
v_b_2047_ = v___y_2049_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object* v_a_2058_, lean_object* v_as_2059_, lean_object* v_i_2060_, lean_object* v_stop_2061_, lean_object* v_b_2062_){
_start:
{
size_t v_i_boxed_2063_; size_t v_stop_boxed_2064_; lean_object* v_res_2065_; 
v_i_boxed_2063_ = lean_unbox_usize(v_i_2060_);
lean_dec(v_i_2060_);
v_stop_boxed_2064_ = lean_unbox_usize(v_stop_2061_);
lean_dec(v_stop_2061_);
v_res_2065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_2058_, v_as_2059_, v_i_boxed_2063_, v_stop_boxed_2064_, v_b_2062_);
lean_dec_ref(v_as_2059_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object* v_as_2066_, size_t v_i_2067_, size_t v_stop_2068_, lean_object* v_b_2069_){
_start:
{
uint8_t v___x_2070_; 
v___x_2070_ = lean_usize_dec_eq(v_i_2067_, v_stop_2068_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; lean_object* v_toEnvExtension_2072_; lean_object* v_asyncMode_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; size_t v___x_2077_; size_t v___x_2078_; 
v___x_2071_ = l_Lean_Compiler_LCNF_impureSigExt;
v_toEnvExtension_2072_ = lean_ctor_get(v___x_2071_, 0);
v_asyncMode_2073_ = lean_ctor_get(v_toEnvExtension_2072_, 2);
v___x_2074_ = lean_box(0);
v___x_2075_ = lean_array_uget_borrowed(v_as_2066_, v_i_2067_);
lean_inc(v___x_2075_);
v___x_2076_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2071_, v_b_2069_, v___x_2075_, v_asyncMode_2073_, v___x_2074_);
v___x_2077_ = ((size_t)1ULL);
v___x_2078_ = lean_usize_add(v_i_2067_, v___x_2077_);
v_i_2067_ = v___x_2078_;
v_b_2069_ = v___x_2076_;
goto _start;
}
else
{
return v_b_2069_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object* v_as_2080_, lean_object* v_i_2081_, lean_object* v_stop_2082_, lean_object* v_b_2083_){
_start:
{
size_t v_i_boxed_2084_; size_t v_stop_boxed_2085_; lean_object* v_res_2086_; 
v_i_boxed_2084_ = lean_unbox_usize(v_i_2081_);
lean_dec(v_i_2081_);
v_stop_boxed_2085_ = lean_unbox_usize(v_stop_2082_);
lean_dec(v_stop_2082_);
v_res_2086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v_as_2080_, v_i_boxed_2084_, v_stop_boxed_2085_, v_b_2083_);
lean_dec_ref(v_as_2080_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object* v___y_2088_, lean_object* v_as_2089_, size_t v_i_2090_, size_t v_stop_2091_, lean_object* v_b_2092_){
_start:
{
lean_object* v___y_2094_; uint8_t v___x_2098_; 
v___x_2098_ = lean_usize_dec_eq(v_i_2090_, v_stop_2091_);
if (v___x_2098_ == 0)
{
lean_object* v_fst_2099_; lean_object* v_snd_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___y_2104_; 
v_fst_2099_ = lean_ctor_get(v_b_2092_, 0);
v_snd_2100_ = lean_ctor_get(v_b_2092_, 1);
v___x_2101_ = lean_array_uget_borrowed(v_as_2089_, v_i_2090_);
v___x_2102_ = l_Lean_IR_Decl_name(v___x_2101_);
if (lean_obj_tag(v___x_2102_) == 1)
{
lean_object* v_pre_2117_; lean_object* v_str_2118_; lean_object* v___x_2119_; uint8_t v___x_2120_; 
v_pre_2117_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_pre_2117_);
v_str_2118_ = lean_ctor_get(v___x_2102_, 1);
lean_inc_ref(v_str_2118_);
v___x_2119_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___closed__0));
v___x_2120_ = lean_string_dec_eq(v_str_2118_, v___x_2119_);
lean_dec_ref(v_str_2118_);
if (v___x_2120_ == 0)
{
lean_dec(v_pre_2117_);
lean_inc_ref(v___x_2102_);
v___y_2104_ = v___x_2102_;
goto v___jp_2103_;
}
else
{
v___y_2104_ = v_pre_2117_;
goto v___jp_2103_;
}
}
else
{
lean_inc(v___x_2102_);
v___y_2104_ = v___x_2102_;
goto v___jp_2103_;
}
v___jp_2103_:
{
uint8_t v___x_2105_; 
lean_inc_ref(v___y_2088_);
v___x_2105_ = l_Lean_isExtern(v___y_2088_, v___y_2104_);
if (v___x_2105_ == 0)
{
lean_dec(v___x_2102_);
v___y_2094_ = v_b_2092_;
goto v___jp_2093_;
}
else
{
lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2114_; 
lean_inc(v_snd_2100_);
lean_inc(v_fst_2099_);
v_isSharedCheck_2114_ = !lean_is_exclusive(v_b_2092_);
if (v_isSharedCheck_2114_ == 0)
{
lean_object* v_unused_2115_; lean_object* v_unused_2116_; 
v_unused_2115_ = lean_ctor_get(v_b_2092_, 1);
lean_dec(v_unused_2115_);
v_unused_2116_ = lean_ctor_get(v_b_2092_, 0);
lean_dec(v_unused_2116_);
v___x_2107_ = v_b_2092_;
v_isShared_2108_ = v_isSharedCheck_2114_;
goto v_resetjp_2106_;
}
else
{
lean_dec(v_b_2092_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2114_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2112_; 
lean_inc_n(v___x_2101_, 2);
v___x_2109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2101_);
lean_ctor_set(v___x_2109_, 1, v_fst_2099_);
v___x_2110_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_2100_, v___x_2102_, v___x_2101_);
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 1, v___x_2110_);
lean_ctor_set(v___x_2107_, 0, v___x_2109_);
v___x_2112_ = v___x_2107_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2109_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v___x_2110_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
v___y_2094_ = v___x_2112_;
goto v___jp_2093_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_2088_);
return v_b_2092_;
}
v___jp_2093_:
{
size_t v___x_2095_; size_t v___x_2096_; 
v___x_2095_ = ((size_t)1ULL);
v___x_2096_ = lean_usize_add(v_i_2090_, v___x_2095_);
v_i_2090_ = v___x_2096_;
v_b_2092_ = v___y_2094_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object* v___y_2121_, lean_object* v_as_2122_, lean_object* v_i_2123_, lean_object* v_stop_2124_, lean_object* v_b_2125_){
_start:
{
size_t v_i_boxed_2126_; size_t v_stop_boxed_2127_; lean_object* v_res_2128_; 
v_i_boxed_2126_ = lean_unbox_usize(v_i_2123_);
lean_dec(v_i_2123_);
v_stop_boxed_2127_ = lean_unbox_usize(v_stop_2124_);
lean_dec(v_stop_2124_);
v_res_2128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_2121_, v_as_2122_, v_i_boxed_2126_, v_stop_boxed_2127_, v_b_2125_);
lean_dec_ref(v_as_2122_);
return v_res_2128_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27_spec__37___lam__0(uint8_t v___y_2129_, uint8_t v_suppressElabErrors_2130_, lean_object* v_x_2131_){
_start:
{
if (lean_obj_tag(v_x_2131_) == 1)
{
lean_object* v_pre_2132_; 
v_pre_2132_ = lean_ctor_get(v_x_2131_, 0);
switch(lean_obj_tag(v_pre_2132_))
{
case 1:
{
lean_object* v_pre_2133_; 
v_pre_2133_ = lean_ctor_get(v_pre_2132_, 0);
switch(lean_obj_tag(v_pre_2133_))
{
case 0:
{
lean_object* v_str_2134_; lean_object* v_str_2135_; lean_object* v___x_2136_; uint8_t v___x_2137_; 
v_str_2134_ = lean_ctor_get(v_x_2131_, 1);
v_str_2135_ = lean_ctor_get(v_pre_2132_, 1);
v___x_2136_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__0));
v___x_2137_ = lean_string_dec_eq(v_str_2135_, v___x_2136_);
if (v___x_2137_ == 0)
{
lean_object* v___x_2138_; uint8_t v___x_2139_; 
v___x_2138_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__1));
v___x_2139_ = lean_string_dec_eq(v_str_2135_, v___x_2138_);
if (v___x_2139_ == 0)
{
return v___y_2129_;
}
else
{
lean_object* v___x_2140_; uint8_t v___x_2141_; 
v___x_2140_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__2));
v___x_2141_ = lean_string_dec_eq(v_str_2134_, v___x_2140_);
if (v___x_2141_ == 0)
{
return v___y_2129_;
}
else
{
return v_suppressElabErrors_2130_;
}
}
}
else
{
lean_object* v___x_2142_; uint8_t v___x_2143_; 
v___x_2142_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__3));
v___x_2143_ = lean_string_dec_eq(v_str_2134_, v___x_2142_);
if (v___x_2143_ == 0)
{
return v___y_2129_;
}
else
{
return v_suppressElabErrors_2130_;
}
}
}
case 1:
{
lean_object* v_pre_2144_; 
v_pre_2144_ = lean_ctor_get(v_pre_2133_, 0);
if (lean_obj_tag(v_pre_2144_) == 0)
{
lean_object* v_str_2145_; lean_object* v_str_2146_; lean_object* v_str_2147_; lean_object* v___x_2148_; uint8_t v___x_2149_; 
v_str_2145_ = lean_ctor_get(v_x_2131_, 1);
v_str_2146_ = lean_ctor_get(v_pre_2132_, 1);
v_str_2147_ = lean_ctor_get(v_pre_2133_, 1);
v___x_2148_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__4));
v___x_2149_ = lean_string_dec_eq(v_str_2147_, v___x_2148_);
if (v___x_2149_ == 0)
{
return v___y_2129_;
}
else
{
lean_object* v___x_2150_; uint8_t v___x_2151_; 
v___x_2150_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__5));
v___x_2151_ = lean_string_dec_eq(v_str_2146_, v___x_2150_);
if (v___x_2151_ == 0)
{
return v___y_2129_;
}
else
{
lean_object* v___x_2152_; uint8_t v___x_2153_; 
v___x_2152_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___lam__0___closed__6));
v___x_2153_ = lean_string_dec_eq(v_str_2145_, v___x_2152_);
if (v___x_2153_ == 0)
{
return v___y_2129_;
}
else
{
return v_suppressElabErrors_2130_;
}
}
}
}
else
{
return v___y_2129_;
}
}
default: 
{
return v___y_2129_;
}
}
}
case 0:
{
lean_object* v_str_2154_; lean_object* v___x_2155_; uint8_t v___x_2156_; 
v_str_2154_ = lean_ctor_get(v_x_2131_, 1);
v___x_2155_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__4_spec__4___closed__0));
v___x_2156_ = lean_string_dec_eq(v_str_2154_, v___x_2155_);
if (v___x_2156_ == 0)
{
return v___y_2129_;
}
else
{
return v_suppressElabErrors_2130_;
}
}
default: 
{
return v___y_2129_;
}
}
}
else
{
return v___y_2129_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27_spec__37___lam__0___boxed(lean_object* v___y_2157_, lean_object* v_suppressElabErrors_2158_, lean_object* v_x_2159_){
_start:
{
uint8_t v___y_34629__boxed_2160_; uint8_t v_suppressElabErrors_boxed_2161_; uint8_t v_res_2162_; lean_object* v_r_2163_; 
v___y_34629__boxed_2160_ = lean_unbox(v___y_2157_);
v_suppressElabErrors_boxed_2161_ = lean_unbox(v_suppressElabErrors_2158_);
v_res_2162_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27_spec__37___lam__0(v___y_34629__boxed_2160_, v_suppressElabErrors_boxed_2161_, v_x_2159_);
lean_dec(v_x_2159_);
v_r_2163_ = lean_box(v_res_2162_);
return v_r_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27_spec__37(lean_object* v_ref_2164_, lean_object* v_msgData_2165_, uint8_t v_severity_2166_, uint8_t v_isSilent_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
uint8_t v___y_2172_; lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2176_; uint8_t v___y_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v___y_2208_; uint8_t v___y_2209_; lean_object* v___y_2210_; uint8_t v___y_2211_; lean_object* v___y_2212_; uint8_t v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; lean_object* v___y_2233_; lean_object* v___y_2234_; uint8_t v___y_2235_; uint8_t v___y_2236_; uint8_t v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2244_; lean_object* v___y_2245_; uint8_t v___y_2246_; uint8_t v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; uint8_t v___y_2250_; uint8_t v___x_2255_; lean_object* v___y_2257_; lean_object* v___y_2258_; uint8_t v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; uint8_t v___y_2262_; uint8_t v___y_2263_; uint8_t v___y_2265_; uint8_t v___x_2280_; 
v___x_2255_ = 2;
v___x_2280_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2166_, v___x_2255_);
if (v___x_2280_ == 0)
{
v___y_2265_ = v___x_2280_;
goto v___jp_2264_;
}
else
{
uint8_t v___x_2281_; 
lean_inc_ref(v_msgData_2165_);
v___x_2281_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2165_);
v___y_2265_ = v___x_2281_;
goto v___jp_2264_;
}
v___jp_2171_:
{
lean_object* v___x_2181_; lean_object* v_currNamespace_2182_; lean_object* v_openDecls_2183_; lean_object* v_env_2184_; lean_object* v_nextMacroScope_2185_; lean_object* v_ngen_2186_; lean_object* v_auxDeclNGen_2187_; lean_object* v_traceState_2188_; lean_object* v_cache_2189_; lean_object* v_messages_2190_; lean_object* v_infoState_2191_; lean_object* v_snapshotTasks_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2206_; 
v___x_2181_ = lean_st_ref_take(v___y_2180_);
v_currNamespace_2182_ = lean_ctor_get(v___y_2179_, 6);
v_openDecls_2183_ = lean_ctor_get(v___y_2179_, 7);
v_env_2184_ = lean_ctor_get(v___x_2181_, 0);
v_nextMacroScope_2185_ = lean_ctor_get(v___x_2181_, 1);
v_ngen_2186_ = lean_ctor_get(v___x_2181_, 2);
v_auxDeclNGen_2187_ = lean_ctor_get(v___x_2181_, 3);
v_traceState_2188_ = lean_ctor_get(v___x_2181_, 4);
v_cache_2189_ = lean_ctor_get(v___x_2181_, 5);
v_messages_2190_ = lean_ctor_get(v___x_2181_, 6);
v_infoState_2191_ = lean_ctor_get(v___x_2181_, 7);
v_snapshotTasks_2192_ = lean_ctor_get(v___x_2181_, 8);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2194_ = v___x_2181_;
v_isShared_2195_ = v_isSharedCheck_2206_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_snapshotTasks_2192_);
lean_inc(v_infoState_2191_);
lean_inc(v_messages_2190_);
lean_inc(v_cache_2189_);
lean_inc(v_traceState_2188_);
lean_inc(v_auxDeclNGen_2187_);
lean_inc(v_ngen_2186_);
lean_inc(v_nextMacroScope_2185_);
lean_inc(v_env_2184_);
lean_dec(v___x_2181_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2206_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2201_; 
lean_inc(v_openDecls_2183_);
lean_inc(v_currNamespace_2182_);
v___x_2196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2196_, 0, v_currNamespace_2182_);
lean_ctor_set(v___x_2196_, 1, v_openDecls_2183_);
v___x_2197_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
lean_ctor_set(v___x_2197_, 1, v___y_2175_);
lean_inc_ref(v___y_2174_);
lean_inc_ref(v___y_2178_);
v___x_2198_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2198_, 0, v___y_2178_);
lean_ctor_set(v___x_2198_, 1, v___y_2173_);
lean_ctor_set(v___x_2198_, 2, v___y_2176_);
lean_ctor_set(v___x_2198_, 3, v___y_2174_);
lean_ctor_set(v___x_2198_, 4, v___x_2197_);
lean_ctor_set_uint8(v___x_2198_, sizeof(void*)*5, v___y_2172_);
lean_ctor_set_uint8(v___x_2198_, sizeof(void*)*5 + 1, v___y_2177_);
lean_ctor_set_uint8(v___x_2198_, sizeof(void*)*5 + 2, v_isSilent_2167_);
v___x_2199_ = l_Lean_MessageLog_add(v___x_2198_, v_messages_2190_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 6, v___x_2199_);
v___x_2201_ = v___x_2194_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_env_2184_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v_nextMacroScope_2185_);
lean_ctor_set(v_reuseFailAlloc_2205_, 2, v_ngen_2186_);
lean_ctor_set(v_reuseFailAlloc_2205_, 3, v_auxDeclNGen_2187_);
lean_ctor_set(v_reuseFailAlloc_2205_, 4, v_traceState_2188_);
lean_ctor_set(v_reuseFailAlloc_2205_, 5, v_cache_2189_);
lean_ctor_set(v_reuseFailAlloc_2205_, 6, v___x_2199_);
lean_ctor_set(v_reuseFailAlloc_2205_, 7, v_infoState_2191_);
lean_ctor_set(v_reuseFailAlloc_2205_, 8, v_snapshotTasks_2192_);
v___x_2201_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2202_ = lean_st_ref_set(v___y_2180_, v___x_2201_);
v___x_2203_ = lean_box(0);
v___x_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
return v___x_2204_;
}
}
}
v___jp_2207_:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2231_; 
v___x_2216_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2165_);
v___x_2217_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v___x_2216_, v___y_2168_, v___y_2169_);
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2220_ = v___x_2217_;
v_isShared_2221_ = v_isSharedCheck_2231_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2217_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2231_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
lean_inc_ref_n(v___y_2214_, 2);
v___x_2222_ = l_Lean_FileMap_toPosition(v___y_2214_, v___y_2210_);
lean_dec(v___y_2210_);
v___x_2223_ = l_Lean_FileMap_toPosition(v___y_2214_, v___y_2215_);
lean_dec(v___y_2215_);
v___x_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
v___x_2225_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__15___closed__1));
if (v___y_2211_ == 0)
{
lean_del_object(v___x_2220_);
lean_dec_ref(v___y_2208_);
v___y_2172_ = v___y_2209_;
v___y_2173_ = v___x_2222_;
v___y_2174_ = v___x_2225_;
v___y_2175_ = v_a_2218_;
v___y_2176_ = v___x_2224_;
v___y_2177_ = v___y_2213_;
v___y_2178_ = v___y_2212_;
v___y_2179_ = v___y_2168_;
v___y_2180_ = v___y_2169_;
goto v___jp_2171_;
}
else
{
uint8_t v___x_2226_; 
lean_inc(v_a_2218_);
v___x_2226_ = l_Lean_MessageData_hasTag(v___y_2208_, v_a_2218_);
if (v___x_2226_ == 0)
{
lean_object* v___x_2227_; lean_object* v___x_2229_; 
lean_dec_ref(v___x_2224_);
lean_dec_ref(v___x_2222_);
lean_dec(v_a_2218_);
v___x_2227_ = lean_box(0);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 0, v___x_2227_);
v___x_2229_ = v___x_2220_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2227_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
else
{
lean_del_object(v___x_2220_);
v___y_2172_ = v___y_2209_;
v___y_2173_ = v___x_2222_;
v___y_2174_ = v___x_2225_;
v___y_2175_ = v_a_2218_;
v___y_2176_ = v___x_2224_;
v___y_2177_ = v___y_2213_;
v___y_2178_ = v___y_2212_;
v___y_2179_ = v___y_2168_;
v___y_2180_ = v___y_2169_;
goto v___jp_2171_;
}
}
}
}
v___jp_2232_:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Lean_Syntax_getTailPos_x3f(v___y_2234_, v___y_2235_);
lean_dec(v___y_2234_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_inc(v___y_2240_);
v___y_2208_ = v___y_2233_;
v___y_2209_ = v___y_2235_;
v___y_2210_ = v___y_2240_;
v___y_2211_ = v___y_2236_;
v___y_2212_ = v___y_2238_;
v___y_2213_ = v___y_2237_;
v___y_2214_ = v___y_2239_;
v___y_2215_ = v___y_2240_;
goto v___jp_2207_;
}
else
{
lean_object* v_val_2242_; 
v_val_2242_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_val_2242_);
lean_dec_ref(v___x_2241_);
v___y_2208_ = v___y_2233_;
v___y_2209_ = v___y_2235_;
v___y_2210_ = v___y_2240_;
v___y_2211_ = v___y_2236_;
v___y_2212_ = v___y_2238_;
v___y_2213_ = v___y_2237_;
v___y_2214_ = v___y_2239_;
v___y_2215_ = v_val_2242_;
goto v___jp_2207_;
}
}
v___jp_2243_:
{
lean_object* v_ref_2251_; lean_object* v___x_2252_; 
v_ref_2251_ = l_Lean_replaceRef(v_ref_2164_, v___y_2245_);
v___x_2252_ = l_Lean_Syntax_getPos_x3f(v_ref_2251_, v___y_2246_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v___x_2253_; 
v___x_2253_ = lean_unsigned_to_nat(0u);
v___y_2233_ = v___y_2244_;
v___y_2234_ = v_ref_2251_;
v___y_2235_ = v___y_2246_;
v___y_2236_ = v___y_2247_;
v___y_2237_ = v___y_2250_;
v___y_2238_ = v___y_2248_;
v___y_2239_ = v___y_2249_;
v___y_2240_ = v___x_2253_;
goto v___jp_2232_;
}
else
{
lean_object* v_val_2254_; 
v_val_2254_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_val_2254_);
lean_dec_ref(v___x_2252_);
v___y_2233_ = v___y_2244_;
v___y_2234_ = v_ref_2251_;
v___y_2235_ = v___y_2246_;
v___y_2236_ = v___y_2247_;
v___y_2237_ = v___y_2250_;
v___y_2238_ = v___y_2248_;
v___y_2239_ = v___y_2249_;
v___y_2240_ = v_val_2254_;
goto v___jp_2232_;
}
}
v___jp_2256_:
{
if (v___y_2263_ == 0)
{
v___y_2244_ = v___y_2258_;
v___y_2245_ = v___y_2257_;
v___y_2246_ = v___y_2262_;
v___y_2247_ = v___y_2259_;
v___y_2248_ = v___y_2260_;
v___y_2249_ = v___y_2261_;
v___y_2250_ = v_severity_2166_;
goto v___jp_2243_;
}
else
{
v___y_2244_ = v___y_2258_;
v___y_2245_ = v___y_2257_;
v___y_2246_ = v___y_2262_;
v___y_2247_ = v___y_2259_;
v___y_2248_ = v___y_2260_;
v___y_2249_ = v___y_2261_;
v___y_2250_ = v___x_2255_;
goto v___jp_2243_;
}
}
v___jp_2264_:
{
if (v___y_2265_ == 0)
{
lean_object* v_fileName_2266_; lean_object* v_fileMap_2267_; lean_object* v_options_2268_; lean_object* v_ref_2269_; uint8_t v_suppressElabErrors_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___f_2273_; uint8_t v___x_2274_; uint8_t v___x_2275_; 
v_fileName_2266_ = lean_ctor_get(v___y_2168_, 0);
v_fileMap_2267_ = lean_ctor_get(v___y_2168_, 1);
v_options_2268_ = lean_ctor_get(v___y_2168_, 2);
v_ref_2269_ = lean_ctor_get(v___y_2168_, 5);
v_suppressElabErrors_2270_ = lean_ctor_get_uint8(v___y_2168_, sizeof(void*)*14 + 1);
v___x_2271_ = lean_box(v___y_2265_);
v___x_2272_ = lean_box(v_suppressElabErrors_2270_);
v___f_2273_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27_spec__37___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2273_, 0, v___x_2271_);
lean_closure_set(v___f_2273_, 1, v___x_2272_);
v___x_2274_ = 1;
v___x_2275_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2166_, v___x_2274_);
if (v___x_2275_ == 0)
{
v___y_2257_ = v_ref_2269_;
v___y_2258_ = v___f_2273_;
v___y_2259_ = v_suppressElabErrors_2270_;
v___y_2260_ = v_fileName_2266_;
v___y_2261_ = v_fileMap_2267_;
v___y_2262_ = v___y_2265_;
v___y_2263_ = v___x_2275_;
goto v___jp_2256_;
}
else
{
lean_object* v___x_2276_; uint8_t v___x_2277_; 
v___x_2276_ = l_Lean_warningAsError;
v___x_2277_ = l_Lean_Option_get___at___00main_spec__6(v_options_2268_, v___x_2276_);
v___y_2257_ = v_ref_2269_;
v___y_2258_ = v___f_2273_;
v___y_2259_ = v_suppressElabErrors_2270_;
v___y_2260_ = v_fileName_2266_;
v___y_2261_ = v_fileMap_2267_;
v___y_2262_ = v___y_2265_;
v___y_2263_ = v___x_2277_;
goto v___jp_2256_;
}
}
else
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
lean_dec_ref(v_msgData_2165_);
v___x_2278_ = lean_box(0);
v___x_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
return v___x_2279_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27_spec__37___boxed(lean_object* v_ref_2282_, lean_object* v_msgData_2283_, lean_object* v_severity_2284_, lean_object* v_isSilent_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
uint8_t v_severity_boxed_2289_; uint8_t v_isSilent_boxed_2290_; lean_object* v_res_2291_; 
v_severity_boxed_2289_ = lean_unbox(v_severity_2284_);
v_isSilent_boxed_2290_ = lean_unbox(v_isSilent_2285_);
v_res_2291_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27_spec__37(v_ref_2282_, v_msgData_2283_, v_severity_boxed_2289_, v_isSilent_boxed_2290_, v___y_2286_, v___y_2287_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v_ref_2282_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27(lean_object* v_msgData_2292_, uint8_t v_severity_2293_, uint8_t v_isSilent_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v_ref_2298_; lean_object* v___x_2299_; 
v_ref_2298_ = lean_ctor_get(v___y_2295_, 5);
v___x_2299_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27_spec__37(v_ref_2298_, v_msgData_2292_, v_severity_2293_, v_isSilent_2294_, v___y_2295_, v___y_2296_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27___boxed(lean_object* v_msgData_2300_, lean_object* v_severity_2301_, lean_object* v_isSilent_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
uint8_t v_severity_boxed_2306_; uint8_t v_isSilent_boxed_2307_; lean_object* v_res_2308_; 
v_severity_boxed_2306_ = lean_unbox(v_severity_2301_);
v_isSilent_boxed_2307_ = lean_unbox(v_isSilent_2302_);
v_res_2308_ = l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27(v_msgData_2300_, v_severity_boxed_2306_, v_isSilent_boxed_2307_, v___y_2303_, v___y_2304_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13(lean_object* v_msgData_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
uint8_t v___x_2313_; uint8_t v___x_2314_; lean_object* v___x_2315_; 
v___x_2313_ = 2;
v___x_2314_ = 0;
v___x_2315_ = l_Lean_log___at___00Lean_logError___at___00main_spec__13_spec__27(v_msgData_2309_, v___x_2313_, v___x_2314_, v___y_2310_, v___y_2311_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__13___boxed(lean_object* v_msgData_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Lean_logError___at___00main_spec__13(v_msgData_2316_, v___y_2317_, v___y_2318_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(lean_object* v_as_2321_, size_t v_sz_2322_, size_t v_i_2323_, lean_object* v_b_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
uint8_t v___x_2328_; 
v___x_2328_ = lean_usize_dec_lt(v_i_2323_, v_sz_2322_);
if (v___x_2328_ == 0)
{
lean_object* v___x_2329_; 
v___x_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2329_, 0, v_b_2324_);
return v___x_2329_;
}
else
{
lean_object* v_a_2330_; lean_object* v___x_2331_; 
v_a_2330_ = lean_array_uget_borrowed(v_as_2321_, v_i_2323_);
lean_inc(v_a_2330_);
v___x_2331_ = l_Lean_Compiler_LCNF_resumeCompilation(v_a_2330_, v___y_2325_, v___y_2326_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v___x_2332_; size_t v___x_2333_; size_t v___x_2334_; 
lean_dec_ref(v___x_2331_);
v___x_2332_ = lean_box(0);
v___x_2333_ = ((size_t)1ULL);
v___x_2334_ = lean_usize_add(v_i_2323_, v___x_2333_);
v_i_2323_ = v___x_2334_;
v_b_2324_ = v___x_2332_;
goto _start;
}
else
{
return v___x_2331_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11___boxed(lean_object* v_as_2336_, lean_object* v_sz_2337_, lean_object* v_i_2338_, lean_object* v_b_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
size_t v_sz_boxed_2343_; size_t v_i_boxed_2344_; lean_object* v_res_2345_; 
v_sz_boxed_2343_ = lean_unbox_usize(v_sz_2337_);
lean_dec(v_sz_2337_);
v_i_boxed_2344_ = lean_unbox_usize(v_i_2338_);
lean_dec(v_i_2338_);
v_res_2345_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_as_2336_, v_sz_boxed_2343_, v_i_boxed_2344_, v_b_2339_, v___y_2340_, v___y_2341_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec_ref(v_as_2336_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(lean_object* v_as_2346_, size_t v_sz_2347_, size_t v_i_2348_, lean_object* v_b_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
uint8_t v___x_2353_; 
v___x_2353_ = lean_usize_dec_lt(v_i_2348_, v_sz_2347_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2354_; 
v___x_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2354_, 0, v_b_2349_);
return v___x_2354_;
}
else
{
lean_object* v___x_2355_; lean_object* v_a_2356_; size_t v_sz_2357_; size_t v___x_2358_; lean_object* v___x_2359_; 
v___x_2355_ = lean_box(0);
v_a_2356_ = lean_array_uget_borrowed(v_as_2346_, v_i_2348_);
v_sz_2357_ = lean_array_size(v_a_2356_);
v___x_2358_ = ((size_t)0ULL);
v___x_2359_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_a_2356_, v_sz_2357_, v___x_2358_, v___x_2355_, v___y_2350_, v___y_2351_);
if (lean_obj_tag(v___x_2359_) == 0)
{
size_t v___x_2360_; size_t v___x_2361_; 
lean_dec_ref(v___x_2359_);
v___x_2360_ = ((size_t)1ULL);
v___x_2361_ = lean_usize_add(v_i_2348_, v___x_2360_);
v_i_2348_ = v___x_2361_;
v_b_2349_ = v___x_2355_;
goto _start;
}
else
{
return v___x_2359_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12___boxed(lean_object* v_as_2363_, lean_object* v_sz_2364_, lean_object* v_i_2365_, lean_object* v_b_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
size_t v_sz_boxed_2370_; size_t v_i_boxed_2371_; lean_object* v_res_2372_; 
v_sz_boxed_2370_ = lean_unbox_usize(v_sz_2364_);
lean_dec(v_sz_2364_);
v_i_boxed_2371_ = lean_unbox_usize(v_i_2365_);
lean_dec(v_i_2365_);
v_res_2372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(v_as_2363_, v_sz_boxed_2370_, v_i_boxed_2371_, v_b_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec_ref(v_as_2363_);
return v_res_2372_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2377_ = ((lean_object*)(l_main___closed__3));
v___x_2378_ = lean_unsigned_to_nat(27u);
v___x_2379_ = lean_unsigned_to_nat(137u);
v___x_2380_ = ((lean_object*)(l_main___closed__2));
v___x_2381_ = ((lean_object*)(l_main___closed__1));
v___x_2382_ = l_mkPanicMessageWithDecl(v___x_2381_, v___x_2380_, v___x_2379_, v___x_2378_, v___x_2377_);
return v___x_2382_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
lean_object* v___x_2385_; 
v___x_2385_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_box(0), lean_box(0), lean_box(0));
return v___x_2385_;
}
}
static lean_object* _init_l_main___closed__8(void){
_start:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2386_ = l_Lean_instInhabitedClassState_default;
v___x_2387_ = lean_box(0);
v___x_2388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2387_);
lean_ctor_set(v___x_2388_, 1, v___x_2386_);
return v___x_2388_;
}
}
static lean_object* _init_l_main___closed__9(void){
_start:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2389_ = l_Lean_Meta_Match_Extension_instInhabitedState;
v___x_2390_ = lean_box(0);
v___x_2391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
lean_ctor_set(v___x_2391_, 1, v___x_2389_);
return v___x_2391_;
}
}
static lean_object* _init_l_main___closed__10(void){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2392_ = ((lean_object*)(l_main___closed__6));
v___x_2393_ = ((lean_object*)(l_main___closed__5));
v___x_2394_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_2393_, v___x_2392_);
return v___x_2394_;
}
}
static lean_object* _init_l_main___closed__11(void){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2395_ = lean_obj_once(&l_main___closed__10, &l_main___closed__10_once, _init_l_main___closed__10);
v___x_2396_ = lean_box(0);
v___x_2397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2396_);
lean_ctor_set(v___x_2397_, 1, v___x_2395_);
return v___x_2397_;
}
}
static lean_object* _init_l_main___closed__12(void){
_start:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = lean_obj_once(&l_main___closed__11, &l_main___closed__11_once, _init_l_main___closed__11);
v___x_2399_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2398_);
return v___x_2399_;
}
}
static lean_object* _init_l_main___closed__13(void){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = l_Array_instInhabited(lean_box(0));
return v___x_2400_;
}
}
static lean_object* _init_l_main___closed__18(void){
_start:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2408_ = l_Lean_Options_empty;
v___x_2409_ = l_Lean_Core_getMaxHeartbeats(v___x_2408_);
return v___x_2409_;
}
}
static lean_object* _init_l_main___closed__21(void){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2412_ = ((lean_object*)(l_main___closed__3));
v___x_2413_ = lean_unsigned_to_nat(51u);
v___x_2414_ = lean_unsigned_to_nat(113u);
v___x_2415_ = ((lean_object*)(l_main___closed__2));
v___x_2416_ = ((lean_object*)(l_main___closed__1));
v___x_2417_ = l_mkPanicMessageWithDecl(v___x_2416_, v___x_2415_, v___x_2414_, v___x_2413_, v___x_2412_);
return v___x_2417_;
}
}
static lean_object* _init_l_main___closed__22(void){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2418_ = lean_unsigned_to_nat(1u);
v___x_2419_ = l_Lean_firstFrontendMacroScope;
v___x_2420_ = lean_nat_add(v___x_2419_, v___x_2418_);
return v___x_2420_;
}
}
static lean_object* _init_l_main___closed__26(void){
_start:
{
lean_object* v___x_2427_; uint64_t v___x_2428_; lean_object* v___x_2429_; 
v___x_2427_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1);
v___x_2428_ = 0ULL;
v___x_2429_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2429_, 0, v___x_2427_);
lean_ctor_set_uint64(v___x_2429_, sizeof(void*)*1, v___x_2428_);
return v___x_2429_;
}
}
static lean_object* _init_l_main___closed__27(void){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2430_;
}
}
static lean_object* _init_l_main___closed__28(void){
_start:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2431_ = lean_obj_once(&l_main___closed__27, &l_main___closed__27_once, _init_l_main___closed__27);
v___x_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2431_);
return v___x_2432_;
}
}
static lean_object* _init_l_main___closed__29(void){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
lean_ctor_set(v___x_2434_, 1, v___x_2433_);
return v___x_2434_;
}
}
static lean_object* _init_l_main___closed__30(void){
_start:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2435_ = l_Lean_NameSet_empty;
v___x_2436_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1);
v___x_2437_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2436_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
lean_ctor_set(v___x_2437_, 2, v___x_2435_);
return v___x_2437_;
}
}
static lean_object* _init_l_main___closed__31(void){
_start:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; lean_object* v___x_2441_; 
v___x_2438_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg___closed__1);
v___x_2439_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_2440_ = 1;
v___x_2441_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2441_, 0, v___x_2439_);
lean_ctor_set(v___x_2441_, 1, v___x_2439_);
lean_ctor_set(v___x_2441_, 2, v___x_2438_);
lean_ctor_set_uint8(v___x_2441_, sizeof(void*)*3, v___x_2440_);
return v___x_2441_;
}
}
static uint8_t _init_l_main___closed__36(void){
_start:
{
uint8_t v___x_2448_; uint8_t v___x_2449_; 
v___x_2448_ = 2;
v___x_2449_ = l_Lean_instOrdOLeanLevel_ord(v___x_2448_, v___x_2448_);
return v___x_2449_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_2450_; lean_object* v___x_2451_; 
v___x_2450_ = 1;
v___x_2451_ = lean_box_uint32(v___x_2450_);
return v___x_2451_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = 0;
v___x_2453_ = lean_box_uint32(v___x_2452_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_2454_){
_start:
{
if (lean_obj_tag(v_args_2454_) == 1)
{
lean_object* v_tail_2479_; 
v_tail_2479_ = lean_ctor_get(v_args_2454_, 1);
lean_inc(v_tail_2479_);
if (lean_obj_tag(v_tail_2479_) == 1)
{
lean_object* v_tail_2480_; 
v_tail_2480_ = lean_ctor_get(v_tail_2479_, 1);
lean_inc(v_tail_2480_);
if (lean_obj_tag(v_tail_2480_) == 1)
{
lean_object* v_head_2481_; lean_object* v_head_2482_; lean_object* v_head_2483_; lean_object* v_tail_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_3108_; 
v_head_2481_ = lean_ctor_get(v_args_2454_, 0);
lean_inc(v_head_2481_);
lean_dec_ref(v_args_2454_);
v_head_2482_ = lean_ctor_get(v_tail_2479_, 0);
lean_inc(v_head_2482_);
lean_dec_ref(v_tail_2479_);
v_head_2483_ = lean_ctor_get(v_tail_2480_, 0);
v_tail_2484_ = lean_ctor_get(v_tail_2480_, 1);
v_isSharedCheck_3108_ = !lean_is_exclusive(v_tail_2480_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_2486_ = v_tail_2480_;
v_isShared_2487_ = v_isSharedCheck_3108_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_tail_2484_);
lean_inc(v_head_2483_);
lean_dec(v_tail_2480_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_3108_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2488_; 
v___x_2488_ = l_Lean_ModuleSetup_load(v_head_2481_);
lean_dec(v_head_2481_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_object* v_a_2489_; lean_object* v_name_2490_; lean_object* v_options_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
lean_inc(v_a_2489_);
lean_dec_ref(v___x_2488_);
v_name_2490_ = lean_ctor_get(v_a_2489_, 0);
lean_inc(v_name_2490_);
v_options_2491_ = lean_ctor_get(v_a_2489_, 6);
lean_inc(v_options_2491_);
lean_dec(v_a_2489_);
v___x_2492_ = l_Lean_LeanOptions_toOptions(v_options_2491_);
v___x_2493_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v_tail_2484_, v___x_2492_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v_a_2494_; lean_object* v___x_2495_; 
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_a_2494_);
lean_dec_ref(v___x_2493_);
v___x_2495_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v_a_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_a_2496_);
lean_dec_ref(v___x_2495_);
v___x_2497_ = lean_box(0);
v___x_2498_ = l_Lean_initSearchPath(v_a_2496_, v___x_2497_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; uint8_t v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___y_2514_; uint8_t v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; uint8_t v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; uint8_t v___y_2653_; lean_object* v___y_2654_; uint8_t v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v_nextMacroScope_2669_; lean_object* v_ngen_2670_; lean_object* v_auxDeclNGen_2671_; lean_object* v_traceState_2672_; lean_object* v_messages_2673_; lean_object* v_infoState_2674_; lean_object* v_snapshotTasks_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2697_; uint8_t v___y_2698_; lean_object* v___y_2699_; uint8_t v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; uint8_t v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2768_; uint8_t v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; uint8_t v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; uint8_t v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; uint8_t v___y_2793_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___y_2817_; uint8_t v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2924_; uint8_t v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2946_; uint8_t v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; uint8_t v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___x_2977_; lean_object* v___x_2978_; uint8_t v___x_2979_; uint8_t v___y_2981_; uint8_t v___x_3074_; 
lean_dec_ref(v___x_2498_);
v___x_2499_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_2500_ = lean_obj_once(&l_main___closed__8, &l_main___closed__8_once, _init_l_main___closed__8);
v___x_2501_ = lean_obj_once(&l_main___closed__9, &l_main___closed__9_once, _init_l_main___closed__9);
v___x_2502_ = lean_obj_once(&l_main___closed__10, &l_main___closed__10_once, _init_l_main___closed__10);
v___x_2503_ = lean_obj_once(&l_main___closed__12, &l_main___closed__12_once, _init_l_main___closed__12);
v___x_2504_ = lean_obj_once(&l_main___closed__13, &l_main___closed__13_once, _init_l_main___closed__13);
v___x_2505_ = lean_box(1);
v___x_2506_ = ((lean_object*)(l_main___closed__14));
v___x_2507_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_2508_ = 1;
v___x_2509_ = l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(v_a_2494_, v___x_2507_, v___x_2508_);
v___x_2510_ = l_Lean_maxHeartbeats;
v___x_2511_ = lean_unsigned_to_nat(0u);
v___x_2512_ = l_Lean_Option_set___at___00main_spec__4(v___x_2509_, v___x_2510_, v___x_2511_);
v___x_2813_ = ((lean_object*)(l_main___closed__20));
lean_inc(v_name_2490_);
v___x_2814_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_2814_, 0, v_name_2490_);
lean_ctor_set_uint8(v___x_2814_, sizeof(void*)*1, v___x_2508_);
lean_ctor_set_uint8(v___x_2814_, sizeof(void*)*1 + 1, v___x_2508_);
lean_ctor_set_uint8(v___x_2814_, sizeof(void*)*1 + 2, v___x_2508_);
v___x_2815_ = lean_unsigned_to_nat(1u);
v___x_2977_ = lean_mk_empty_array_with_capacity(v___x_2815_);
v___x_2978_ = lean_array_push(v___x_2977_, v___x_2814_);
v___x_2979_ = 2;
v___x_3074_ = lean_uint8_once(&l_main___closed__36, &l_main___closed__36_once, _init_l_main___closed__36);
if (v___x_3074_ == 0)
{
v___y_2981_ = v___x_2508_;
goto v___jp_2980_;
}
else
{
uint8_t v___x_3075_; 
v___x_3075_ = 0;
v___y_2981_ = v___x_3075_;
goto v___jp_2980_;
}
v___jp_2513_:
{
lean_object* v___x_2538_; 
v___x_2538_ = l_Lean_addTraceAsMessages___at___00main_spec__8(v___y_2533_, v___y_2526_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2533_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v___x_2539_; lean_object* v_messages_2540_; lean_object* v_env_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2641_; 
lean_dec_ref(v___x_2538_);
v___x_2539_ = lean_st_ref_get(v___y_2529_);
lean_dec(v___y_2529_);
v_messages_2540_ = lean_ctor_get(v___x_2539_, 6);
v_env_2541_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2641_ == 0)
{
lean_object* v_unused_2642_; lean_object* v_unused_2643_; lean_object* v_unused_2644_; lean_object* v_unused_2645_; lean_object* v_unused_2646_; lean_object* v_unused_2647_; lean_object* v_unused_2648_; 
v_unused_2642_ = lean_ctor_get(v___x_2539_, 8);
lean_dec(v_unused_2642_);
v_unused_2643_ = lean_ctor_get(v___x_2539_, 7);
lean_dec(v_unused_2643_);
v_unused_2644_ = lean_ctor_get(v___x_2539_, 5);
lean_dec(v_unused_2644_);
v_unused_2645_ = lean_ctor_get(v___x_2539_, 4);
lean_dec(v_unused_2645_);
v_unused_2646_ = lean_ctor_get(v___x_2539_, 3);
lean_dec(v_unused_2646_);
v_unused_2647_ = lean_ctor_get(v___x_2539_, 2);
lean_dec(v_unused_2647_);
v_unused_2648_ = lean_ctor_get(v___x_2539_, 1);
lean_dec(v_unused_2648_);
v___x_2543_ = v___x_2539_;
v_isShared_2544_ = v_isSharedCheck_2641_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_messages_2540_);
lean_inc(v_env_2541_);
lean_dec(v___x_2539_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2641_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v_unreported_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v_unreported_2545_ = lean_ctor_get(v_messages_2540_, 1);
v___x_2546_ = lean_box(0);
lean_inc_ref(v_unreported_2545_);
v___x_2547_ = l_Lean_PersistentArray_forIn___at___00main_spec__10(v_unreported_2545_, v___x_2546_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2631_; 
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2631_ == 0)
{
lean_object* v_unused_2632_; 
v_unused_2632_ = lean_ctor_get(v___x_2547_, 0);
lean_dec(v_unused_2632_);
v___x_2549_ = v___x_2547_;
v_isShared_2550_ = v_isSharedCheck_2631_;
goto v_resetjp_2548_;
}
else
{
lean_dec(v___x_2547_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2631_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
uint8_t v___x_2551_; 
v___x_2551_ = l_Lean_MessageLog_hasErrors(v_messages_2540_);
lean_dec_ref(v_messages_2540_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2552_; 
lean_del_object(v___x_2549_);
lean_inc_ref(v_env_2541_);
v___x_2552_ = l___private_LeanIR_0__mkIRData(v_env_2541_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref(v___x_2552_);
v___x_2554_ = l_Lean_Environment_mainModule(v_env_2541_);
v___x_2555_ = ((lean_object*)(l_main___closed__16));
v___x_2556_ = l_Lean_Name_append(v___x_2554_, v___x_2555_);
lean_inc(v_head_2482_);
v___x_2557_ = l_Lean_saveModuleData(v_head_2482_, v___x_2556_, v_a_2553_);
lean_dec(v___x_2556_);
if (lean_obj_tag(v___x_2557_) == 0)
{
uint8_t v___x_2558_; lean_object* v___x_2559_; 
lean_dec_ref(v___x_2557_);
v___x_2558_ = 1;
v___x_2559_ = lean_io_prim_handle_mk(v_head_2483_, v___x_2558_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2565_; 
lean_dec(v_head_2483_);
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_a_2560_);
lean_dec_ref(v___x_2559_);
v___x_2561_ = ((lean_object*)(l_main___closed__17));
v___x_2562_ = l_Lean_Options_empty;
v___x_2563_ = lean_obj_once(&l_main___closed__18, &l_main___closed__18_once, _init_l_main___closed__18);
lean_inc_ref(v___y_2531_);
lean_inc_ref(v___y_2527_);
lean_inc_ref(v___y_2537_);
lean_inc_ref(v___y_2532_);
lean_inc_ref(v___y_2528_);
lean_inc_ref(v___y_2530_);
lean_inc(v___y_2536_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 8, v___y_2531_);
lean_ctor_set(v___x_2543_, 7, v___y_2527_);
lean_ctor_set(v___x_2543_, 6, v___y_2537_);
lean_ctor_set(v___x_2543_, 5, v___y_2532_);
lean_ctor_set(v___x_2543_, 4, v___y_2528_);
lean_ctor_set(v___x_2543_, 3, v___y_2535_);
lean_ctor_set(v___x_2543_, 2, v___y_2530_);
lean_ctor_set(v___x_2543_, 1, v___y_2536_);
v___x_2565_ = v___x_2543_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_env_2541_);
lean_ctor_set(v_reuseFailAlloc_2588_, 1, v___y_2536_);
lean_ctor_set(v_reuseFailAlloc_2588_, 2, v___y_2530_);
lean_ctor_set(v_reuseFailAlloc_2588_, 3, v___y_2535_);
lean_ctor_set(v_reuseFailAlloc_2588_, 4, v___y_2528_);
lean_ctor_set(v_reuseFailAlloc_2588_, 5, v___y_2532_);
lean_ctor_set(v_reuseFailAlloc_2588_, 6, v___y_2537_);
lean_ctor_set(v_reuseFailAlloc_2588_, 7, v___y_2527_);
lean_ctor_set(v_reuseFailAlloc_2588_, 8, v___y_2531_);
v___x_2565_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___f_2568_; lean_object* v___x_2569_; 
v___x_2566_ = lean_box(v___y_2518_);
v___x_2567_ = lean_box(v___y_2515_);
lean_inc(v___y_2514_);
lean_inc(v___y_2516_);
lean_inc(v___y_2522_);
lean_inc_ref(v___y_2523_);
lean_inc_ref(v___y_2519_);
lean_inc_ref(v___y_2524_);
lean_inc_ref(v___y_2521_);
lean_inc(v___y_2525_);
v___f_2568_ = lean_alloc_closure((void*)(l_main___lam__1___boxed), 20, 19);
lean_closure_set(v___f_2568_, 0, v___x_2565_);
lean_closure_set(v___f_2568_, 1, v___y_2525_);
lean_closure_set(v___f_2568_, 2, v___x_2562_);
lean_closure_set(v___f_2568_, 3, v___y_2521_);
lean_closure_set(v___f_2568_, 4, v___y_2524_);
lean_closure_set(v___f_2568_, 5, v_name_2490_);
lean_closure_set(v___f_2568_, 6, v_a_2560_);
lean_closure_set(v___f_2568_, 7, v___y_2519_);
lean_closure_set(v___f_2568_, 8, v_head_2482_);
lean_closure_set(v___f_2568_, 9, v___y_2523_);
lean_closure_set(v___f_2568_, 10, v___x_2511_);
lean_closure_set(v___f_2568_, 11, v___y_2522_);
lean_closure_set(v___f_2568_, 12, v___y_2520_);
lean_closure_set(v___f_2568_, 13, v___y_2517_);
lean_closure_set(v___f_2568_, 14, v___x_2563_);
lean_closure_set(v___f_2568_, 15, v___y_2516_);
lean_closure_set(v___f_2568_, 16, v___y_2514_);
lean_closure_set(v___f_2568_, 17, v___x_2566_);
lean_closure_set(v___f_2568_, 18, v___x_2567_);
v___x_2569_ = l_Lean_profileitIOUnsafe___redArg(v___x_2561_, v___x_2512_, v___f_2568_, v___y_2534_);
lean_dec_ref(v___x_2512_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2578_; 
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2578_ == 0)
{
lean_object* v_unused_2579_; 
v_unused_2579_ = lean_ctor_get(v___x_2569_, 0);
lean_dec(v_unused_2579_);
v___x_2571_ = v___x_2569_;
v_isShared_2572_ = v_isSharedCheck_2578_;
goto v_resetjp_2570_;
}
else
{
lean_dec(v___x_2569_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2578_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2576_; 
v___x_2573_ = lean_display_cumulative_profiling_times();
v___x_2574_ = l_main___boxed__const__2;
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 0, v___x_2574_);
v___x_2576_ = v___x_2571_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2574_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
else
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
v_a_2580_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2582_ = v___x_2569_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2569_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
}
else
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
lean_dec_ref(v___x_2559_);
lean_del_object(v___x_2543_);
lean_dec_ref(v_env_2541_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec(v___y_2520_);
lean_dec(v___y_2517_);
lean_dec_ref(v___x_2512_);
lean_dec(v_name_2490_);
lean_dec(v_head_2482_);
v___x_2589_ = ((lean_object*)(l_main___closed__19));
v___x_2590_ = lean_string_append(v___x_2589_, v_head_2483_);
lean_dec(v_head_2483_);
v___x_2591_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__5));
v___x_2592_ = lean_string_append(v___x_2590_, v___x_2591_);
v___x_2593_ = l_IO_eprintln___at___00main_spec__9(v___x_2592_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2601_; 
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2601_ == 0)
{
lean_object* v_unused_2602_; 
v_unused_2602_ = lean_ctor_get(v___x_2593_, 0);
lean_dec(v_unused_2602_);
v___x_2595_ = v___x_2593_;
v_isShared_2596_ = v_isSharedCheck_2601_;
goto v_resetjp_2594_;
}
else
{
lean_dec(v___x_2593_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2601_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2597_; lean_object* v___x_2599_; 
v___x_2597_ = l_main___boxed__const__1;
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v___x_2597_);
v___x_2599_ = v___x_2595_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2597_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
v_a_2603_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2593_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2593_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
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
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
lean_del_object(v___x_2543_);
lean_dec_ref(v_env_2541_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec(v___y_2520_);
lean_dec(v___y_2517_);
lean_dec_ref(v___x_2512_);
lean_dec(v_name_2490_);
lean_dec(v_head_2483_);
lean_dec(v_head_2482_);
v_a_2611_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2557_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2557_);
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
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_del_object(v___x_2543_);
lean_dec_ref(v_env_2541_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec(v___y_2520_);
lean_dec(v___y_2517_);
lean_dec_ref(v___x_2512_);
lean_dec(v_name_2490_);
lean_dec(v_head_2483_);
lean_dec(v_head_2482_);
v_a_2619_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2552_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2552_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
else
{
lean_object* v___x_2627_; lean_object* v___x_2629_; 
lean_del_object(v___x_2543_);
lean_dec_ref(v_env_2541_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec(v___y_2520_);
lean_dec(v___y_2517_);
lean_dec_ref(v___x_2512_);
lean_dec(v_name_2490_);
lean_dec(v_head_2483_);
lean_dec(v_head_2482_);
v___x_2627_ = l_main___boxed__const__1;
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 0, v___x_2627_);
v___x_2629_ = v___x_2549_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2627_);
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
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_del_object(v___x_2543_);
lean_dec_ref(v_env_2541_);
lean_dec_ref(v_messages_2540_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec(v___y_2520_);
lean_dec(v___y_2517_);
lean_dec_ref(v___x_2512_);
lean_dec(v_name_2490_);
lean_dec(v_head_2483_);
lean_dec(v_head_2482_);
v_a_2633_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2547_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2547_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
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
}
else
{
lean_dec_ref(v___x_2538_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec(v___y_2529_);
lean_dec(v___y_2520_);
lean_dec(v___y_2517_);
lean_dec_ref(v___x_2512_);
lean_dec(v_name_2490_);
lean_dec(v_head_2483_);
lean_dec(v_head_2482_);
goto v___jp_2476_;
}
}
v___jp_2649_:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; size_t v_sz_2686_; size_t v___x_2687_; lean_object* v___x_2688_; 
lean_inc_ref(v___y_2677_);
v___x_2683_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2683_, 0, v___y_2682_);
lean_ctor_set(v___x_2683_, 1, v_nextMacroScope_2669_);
lean_ctor_set(v___x_2683_, 2, v_ngen_2670_);
lean_ctor_set(v___x_2683_, 3, v_auxDeclNGen_2671_);
lean_ctor_set(v___x_2683_, 4, v_traceState_2672_);
lean_ctor_set(v___x_2683_, 5, v___y_2677_);
lean_ctor_set(v___x_2683_, 6, v_messages_2673_);
lean_ctor_set(v___x_2683_, 7, v_infoState_2674_);
lean_ctor_set(v___x_2683_, 8, v_snapshotTasks_2675_);
v___x_2684_ = lean_st_ref_set(v___y_2676_, v___x_2683_);
v___x_2685_ = lean_box(0);
v_sz_2686_ = lean_array_size(v___y_2678_);
v___x_2687_ = ((size_t)0ULL);
v___x_2688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__12(v___y_2678_, v_sz_2686_, v___x_2687_, v___x_2685_, v___y_2679_, v___y_2676_);
lean_dec_ref(v___y_2678_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_dec_ref(v___x_2688_);
v___y_2514_ = v___y_2650_;
v___y_2515_ = v___y_2653_;
v___y_2516_ = v___y_2652_;
v___y_2517_ = v___y_2651_;
v___y_2518_ = v___y_2655_;
v___y_2519_ = v___y_2654_;
v___y_2520_ = v___y_2657_;
v___y_2521_ = v___y_2656_;
v___y_2522_ = v___y_2658_;
v___y_2523_ = v___y_2659_;
v___y_2524_ = v___y_2661_;
v___y_2525_ = v___y_2660_;
v___y_2526_ = v___y_2676_;
v___y_2527_ = v___y_2662_;
v___y_2528_ = v___y_2663_;
v___y_2529_ = v___y_2664_;
v___y_2530_ = v___y_2665_;
v___y_2531_ = v___y_2666_;
v___y_2532_ = v___y_2677_;
v___y_2533_ = v___y_2679_;
v___y_2534_ = v___y_2667_;
v___y_2535_ = v___y_2680_;
v___y_2536_ = v___y_2668_;
v___y_2537_ = v___y_2681_;
goto v___jp_2513_;
}
else
{
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_dec_ref(v___x_2688_);
v___y_2514_ = v___y_2650_;
v___y_2515_ = v___y_2653_;
v___y_2516_ = v___y_2652_;
v___y_2517_ = v___y_2651_;
v___y_2518_ = v___y_2655_;
v___y_2519_ = v___y_2654_;
v___y_2520_ = v___y_2657_;
v___y_2521_ = v___y_2656_;
v___y_2522_ = v___y_2658_;
v___y_2523_ = v___y_2659_;
v___y_2524_ = v___y_2661_;
v___y_2525_ = v___y_2660_;
v___y_2526_ = v___y_2676_;
v___y_2527_ = v___y_2662_;
v___y_2528_ = v___y_2663_;
v___y_2529_ = v___y_2664_;
v___y_2530_ = v___y_2665_;
v___y_2531_ = v___y_2666_;
v___y_2532_ = v___y_2677_;
v___y_2533_ = v___y_2679_;
v___y_2534_ = v___y_2667_;
v___y_2535_ = v___y_2680_;
v___y_2536_ = v___y_2668_;
v___y_2537_ = v___y_2681_;
goto v___jp_2513_;
}
else
{
lean_object* v_a_2689_; uint8_t v___x_2690_; 
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
lean_inc(v_a_2689_);
lean_dec_ref(v___x_2688_);
v___x_2690_ = l_Lean_Exception_isInterrupt(v_a_2689_);
if (v___x_2690_ == 0)
{
lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2691_ = l_Lean_Exception_toMessageData(v_a_2689_);
v___x_2692_ = l_Lean_logError___at___00main_spec__13(v___x_2691_, v___y_2679_, v___y_2676_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_dec_ref(v___x_2692_);
v___y_2514_ = v___y_2650_;
v___y_2515_ = v___y_2653_;
v___y_2516_ = v___y_2652_;
v___y_2517_ = v___y_2651_;
v___y_2518_ = v___y_2655_;
v___y_2519_ = v___y_2654_;
v___y_2520_ = v___y_2657_;
v___y_2521_ = v___y_2656_;
v___y_2522_ = v___y_2658_;
v___y_2523_ = v___y_2659_;
v___y_2524_ = v___y_2661_;
v___y_2525_ = v___y_2660_;
v___y_2526_ = v___y_2676_;
v___y_2527_ = v___y_2662_;
v___y_2528_ = v___y_2663_;
v___y_2529_ = v___y_2664_;
v___y_2530_ = v___y_2665_;
v___y_2531_ = v___y_2666_;
v___y_2532_ = v___y_2677_;
v___y_2533_ = v___y_2679_;
v___y_2534_ = v___y_2667_;
v___y_2535_ = v___y_2680_;
v___y_2536_ = v___y_2668_;
v___y_2537_ = v___y_2681_;
goto v___jp_2513_;
}
else
{
lean_object* v___x_2693_; 
lean_dec_ref(v___x_2692_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2667_);
lean_dec(v___y_2664_);
lean_dec(v___y_2657_);
lean_dec(v___y_2651_);
lean_dec_ref(v___x_2512_);
lean_dec(v_name_2490_);
lean_dec(v_head_2483_);
lean_dec(v_head_2482_);
v___x_2693_ = l_Lean_addTraceAsMessages___at___00main_spec__8(v___y_2679_, v___y_2676_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2679_);
lean_dec_ref(v___x_2693_);
goto v___jp_2476_;
}
}
else
{
lean_dec(v_a_2689_);
v___y_2514_ = v___y_2650_;
v___y_2515_ = v___y_2653_;
v___y_2516_ = v___y_2652_;
v___y_2517_ = v___y_2651_;
v___y_2518_ = v___y_2655_;
v___y_2519_ = v___y_2654_;
v___y_2520_ = v___y_2657_;
v___y_2521_ = v___y_2656_;
v___y_2522_ = v___y_2658_;
v___y_2523_ = v___y_2659_;
v___y_2524_ = v___y_2661_;
v___y_2525_ = v___y_2660_;
v___y_2526_ = v___y_2676_;
v___y_2527_ = v___y_2662_;
v___y_2528_ = v___y_2663_;
v___y_2529_ = v___y_2664_;
v___y_2530_ = v___y_2665_;
v___y_2531_ = v___y_2666_;
v___y_2532_ = v___y_2677_;
v___y_2533_ = v___y_2679_;
v___y_2534_ = v___y_2667_;
v___y_2535_ = v___y_2680_;
v___y_2536_ = v___y_2668_;
v___y_2537_ = v___y_2681_;
goto v___jp_2513_;
}
}
}
}
v___jp_2694_:
{
lean_object* v___x_2721_; lean_object* v_fileName_2722_; lean_object* v_fileMap_2723_; lean_object* v_currRecDepth_2724_; lean_object* v_ref_2725_; lean_object* v_currNamespace_2726_; lean_object* v_openDecls_2727_; lean_object* v_initHeartbeats_2728_; lean_object* v_maxHeartbeats_2729_; lean_object* v_quotContext_2730_; lean_object* v_currMacroScope_2731_; lean_object* v_cancelTk_x3f_2732_; uint8_t v_suppressElabErrors_2733_; lean_object* v_inheritedTraceOptions_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2764_; 
v___x_2721_ = lean_st_ref_take(v___y_2720_);
v_fileName_2722_ = lean_ctor_get(v___y_2719_, 0);
v_fileMap_2723_ = lean_ctor_get(v___y_2719_, 1);
v_currRecDepth_2724_ = lean_ctor_get(v___y_2719_, 3);
v_ref_2725_ = lean_ctor_get(v___y_2719_, 5);
v_currNamespace_2726_ = lean_ctor_get(v___y_2719_, 6);
v_openDecls_2727_ = lean_ctor_get(v___y_2719_, 7);
v_initHeartbeats_2728_ = lean_ctor_get(v___y_2719_, 8);
v_maxHeartbeats_2729_ = lean_ctor_get(v___y_2719_, 9);
v_quotContext_2730_ = lean_ctor_get(v___y_2719_, 10);
v_currMacroScope_2731_ = lean_ctor_get(v___y_2719_, 11);
v_cancelTk_x3f_2732_ = lean_ctor_get(v___y_2719_, 12);
v_suppressElabErrors_2733_ = lean_ctor_get_uint8(v___y_2719_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2734_ = lean_ctor_get(v___y_2719_, 13);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___y_2719_);
if (v_isSharedCheck_2764_ == 0)
{
lean_object* v_unused_2765_; lean_object* v_unused_2766_; 
v_unused_2765_ = lean_ctor_get(v___y_2719_, 4);
lean_dec(v_unused_2765_);
v_unused_2766_ = lean_ctor_get(v___y_2719_, 2);
lean_dec(v_unused_2766_);
v___x_2736_ = v___y_2719_;
v_isShared_2737_ = v_isSharedCheck_2764_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_inheritedTraceOptions_2734_);
lean_inc(v_cancelTk_x3f_2732_);
lean_inc(v_currMacroScope_2731_);
lean_inc(v_quotContext_2730_);
lean_inc(v_maxHeartbeats_2729_);
lean_inc(v_initHeartbeats_2728_);
lean_inc(v_openDecls_2727_);
lean_inc(v_currNamespace_2726_);
lean_inc(v_ref_2725_);
lean_inc(v_currRecDepth_2724_);
lean_inc(v_fileMap_2723_);
lean_inc(v_fileName_2722_);
lean_dec(v___y_2719_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2764_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v_env_2738_; lean_object* v_nextMacroScope_2739_; lean_object* v_ngen_2740_; lean_object* v_auxDeclNGen_2741_; lean_object* v_traceState_2742_; lean_object* v_messages_2743_; lean_object* v_infoState_2744_; lean_object* v_snapshotTasks_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2749_; 
v_env_2738_ = lean_ctor_get(v___x_2721_, 0);
lean_inc_ref(v_env_2738_);
v_nextMacroScope_2739_ = lean_ctor_get(v___x_2721_, 1);
lean_inc(v_nextMacroScope_2739_);
v_ngen_2740_ = lean_ctor_get(v___x_2721_, 2);
lean_inc_ref(v_ngen_2740_);
v_auxDeclNGen_2741_ = lean_ctor_get(v___x_2721_, 3);
lean_inc_ref(v_auxDeclNGen_2741_);
v_traceState_2742_ = lean_ctor_get(v___x_2721_, 4);
lean_inc_ref(v_traceState_2742_);
v_messages_2743_ = lean_ctor_get(v___x_2721_, 6);
lean_inc_ref(v_messages_2743_);
v_infoState_2744_ = lean_ctor_get(v___x_2721_, 7);
lean_inc_ref(v_infoState_2744_);
v_snapshotTasks_2745_ = lean_ctor_get(v___x_2721_, 8);
lean_inc_ref(v_snapshotTasks_2745_);
lean_dec(v___x_2721_);
v___x_2746_ = l_Lean_maxRecDepth;
v___x_2747_ = l_Lean_Option_get___at___00main_spec__7(v___x_2512_, v___x_2746_);
lean_inc_ref(v___x_2512_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 4, v___x_2747_);
lean_ctor_set(v___x_2736_, 2, v___x_2512_);
v___x_2749_ = v___x_2736_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_fileName_2722_);
lean_ctor_set(v_reuseFailAlloc_2763_, 1, v_fileMap_2723_);
lean_ctor_set(v_reuseFailAlloc_2763_, 2, v___x_2512_);
lean_ctor_set(v_reuseFailAlloc_2763_, 3, v_currRecDepth_2724_);
lean_ctor_set(v_reuseFailAlloc_2763_, 4, v___x_2747_);
lean_ctor_set(v_reuseFailAlloc_2763_, 5, v_ref_2725_);
lean_ctor_set(v_reuseFailAlloc_2763_, 6, v_currNamespace_2726_);
lean_ctor_set(v_reuseFailAlloc_2763_, 7, v_openDecls_2727_);
lean_ctor_set(v_reuseFailAlloc_2763_, 8, v_initHeartbeats_2728_);
lean_ctor_set(v_reuseFailAlloc_2763_, 9, v_maxHeartbeats_2729_);
lean_ctor_set(v_reuseFailAlloc_2763_, 10, v_quotContext_2730_);
lean_ctor_set(v_reuseFailAlloc_2763_, 11, v_currMacroScope_2731_);
lean_ctor_set(v_reuseFailAlloc_2763_, 12, v_cancelTk_x3f_2732_);
lean_ctor_set(v_reuseFailAlloc_2763_, 13, v_inheritedTraceOptions_2734_);
lean_ctor_set_uint8(v_reuseFailAlloc_2763_, sizeof(void*)*14 + 1, v_suppressElabErrors_2733_);
v___x_2749_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
lean_object* v___x_2750_; uint8_t v___x_2751_; 
lean_ctor_set_uint8(v___x_2749_, sizeof(void*)*14, v___y_2713_);
v___x_2750_ = lean_array_get_size(v___y_2715_);
v___x_2751_ = lean_nat_dec_lt(v___x_2511_, v___x_2750_);
if (v___x_2751_ == 0)
{
lean_object* v___x_2752_; 
lean_inc_ref(v___y_2716_);
v___x_2752_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_2716_, v_env_2738_, v___x_2505_);
v___y_2650_ = v___y_2695_;
v___y_2651_ = v___y_2696_;
v___y_2652_ = v___y_2697_;
v___y_2653_ = v___y_2698_;
v___y_2654_ = v___y_2699_;
v___y_2655_ = v___y_2700_;
v___y_2656_ = v___y_2701_;
v___y_2657_ = v___y_2702_;
v___y_2658_ = v___y_2703_;
v___y_2659_ = v___y_2704_;
v___y_2660_ = v___y_2705_;
v___y_2661_ = v___x_2746_;
v___y_2662_ = v___y_2706_;
v___y_2663_ = v___y_2707_;
v___y_2664_ = v___y_2708_;
v___y_2665_ = v___y_2709_;
v___y_2666_ = v___y_2710_;
v___y_2667_ = v___y_2711_;
v___y_2668_ = v___y_2712_;
v_nextMacroScope_2669_ = v_nextMacroScope_2739_;
v_ngen_2670_ = v_ngen_2740_;
v_auxDeclNGen_2671_ = v_auxDeclNGen_2741_;
v_traceState_2672_ = v_traceState_2742_;
v_messages_2673_ = v_messages_2743_;
v_infoState_2674_ = v_infoState_2744_;
v_snapshotTasks_2675_ = v_snapshotTasks_2745_;
v___y_2676_ = v___y_2720_;
v___y_2677_ = v___y_2714_;
v___y_2678_ = v___y_2715_;
v___y_2679_ = v___x_2749_;
v___y_2680_ = v___y_2717_;
v___y_2681_ = v___y_2718_;
v___y_2682_ = v___x_2752_;
goto v___jp_2649_;
}
else
{
uint8_t v___x_2753_; 
v___x_2753_ = lean_nat_dec_le(v___x_2750_, v___x_2750_);
if (v___x_2753_ == 0)
{
if (v___x_2751_ == 0)
{
lean_object* v___x_2754_; 
lean_inc_ref(v___y_2716_);
v___x_2754_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_2716_, v_env_2738_, v___x_2505_);
v___y_2650_ = v___y_2695_;
v___y_2651_ = v___y_2696_;
v___y_2652_ = v___y_2697_;
v___y_2653_ = v___y_2698_;
v___y_2654_ = v___y_2699_;
v___y_2655_ = v___y_2700_;
v___y_2656_ = v___y_2701_;
v___y_2657_ = v___y_2702_;
v___y_2658_ = v___y_2703_;
v___y_2659_ = v___y_2704_;
v___y_2660_ = v___y_2705_;
v___y_2661_ = v___x_2746_;
v___y_2662_ = v___y_2706_;
v___y_2663_ = v___y_2707_;
v___y_2664_ = v___y_2708_;
v___y_2665_ = v___y_2709_;
v___y_2666_ = v___y_2710_;
v___y_2667_ = v___y_2711_;
v___y_2668_ = v___y_2712_;
v_nextMacroScope_2669_ = v_nextMacroScope_2739_;
v_ngen_2670_ = v_ngen_2740_;
v_auxDeclNGen_2671_ = v_auxDeclNGen_2741_;
v_traceState_2672_ = v_traceState_2742_;
v_messages_2673_ = v_messages_2743_;
v_infoState_2674_ = v_infoState_2744_;
v_snapshotTasks_2675_ = v_snapshotTasks_2745_;
v___y_2676_ = v___y_2720_;
v___y_2677_ = v___y_2714_;
v___y_2678_ = v___y_2715_;
v___y_2679_ = v___x_2749_;
v___y_2680_ = v___y_2717_;
v___y_2681_ = v___y_2718_;
v___y_2682_ = v___x_2754_;
goto v___jp_2649_;
}
else
{
size_t v___x_2755_; size_t v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2755_ = ((size_t)0ULL);
v___x_2756_ = lean_usize_of_nat(v___x_2750_);
v___x_2757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v___y_2715_, v___x_2755_, v___x_2756_, v___x_2505_);
lean_inc_ref(v___y_2716_);
v___x_2758_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_2716_, v_env_2738_, v___x_2757_);
v___y_2650_ = v___y_2695_;
v___y_2651_ = v___y_2696_;
v___y_2652_ = v___y_2697_;
v___y_2653_ = v___y_2698_;
v___y_2654_ = v___y_2699_;
v___y_2655_ = v___y_2700_;
v___y_2656_ = v___y_2701_;
v___y_2657_ = v___y_2702_;
v___y_2658_ = v___y_2703_;
v___y_2659_ = v___y_2704_;
v___y_2660_ = v___y_2705_;
v___y_2661_ = v___x_2746_;
v___y_2662_ = v___y_2706_;
v___y_2663_ = v___y_2707_;
v___y_2664_ = v___y_2708_;
v___y_2665_ = v___y_2709_;
v___y_2666_ = v___y_2710_;
v___y_2667_ = v___y_2711_;
v___y_2668_ = v___y_2712_;
v_nextMacroScope_2669_ = v_nextMacroScope_2739_;
v_ngen_2670_ = v_ngen_2740_;
v_auxDeclNGen_2671_ = v_auxDeclNGen_2741_;
v_traceState_2672_ = v_traceState_2742_;
v_messages_2673_ = v_messages_2743_;
v_infoState_2674_ = v_infoState_2744_;
v_snapshotTasks_2675_ = v_snapshotTasks_2745_;
v___y_2676_ = v___y_2720_;
v___y_2677_ = v___y_2714_;
v___y_2678_ = v___y_2715_;
v___y_2679_ = v___x_2749_;
v___y_2680_ = v___y_2717_;
v___y_2681_ = v___y_2718_;
v___y_2682_ = v___x_2758_;
goto v___jp_2649_;
}
}
else
{
size_t v___x_2759_; size_t v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2759_ = ((size_t)0ULL);
v___x_2760_ = lean_usize_of_nat(v___x_2750_);
v___x_2761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__14(v___y_2715_, v___x_2759_, v___x_2760_, v___x_2505_);
lean_inc_ref(v___y_2716_);
v___x_2762_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_2716_, v_env_2738_, v___x_2761_);
v___y_2650_ = v___y_2695_;
v___y_2651_ = v___y_2696_;
v___y_2652_ = v___y_2697_;
v___y_2653_ = v___y_2698_;
v___y_2654_ = v___y_2699_;
v___y_2655_ = v___y_2700_;
v___y_2656_ = v___y_2701_;
v___y_2657_ = v___y_2702_;
v___y_2658_ = v___y_2703_;
v___y_2659_ = v___y_2704_;
v___y_2660_ = v___y_2705_;
v___y_2661_ = v___x_2746_;
v___y_2662_ = v___y_2706_;
v___y_2663_ = v___y_2707_;
v___y_2664_ = v___y_2708_;
v___y_2665_ = v___y_2709_;
v___y_2666_ = v___y_2710_;
v___y_2667_ = v___y_2711_;
v___y_2668_ = v___y_2712_;
v_nextMacroScope_2669_ = v_nextMacroScope_2739_;
v_ngen_2670_ = v_ngen_2740_;
v_auxDeclNGen_2671_ = v_auxDeclNGen_2741_;
v_traceState_2672_ = v_traceState_2742_;
v_messages_2673_ = v_messages_2743_;
v_infoState_2674_ = v_infoState_2744_;
v_snapshotTasks_2675_ = v_snapshotTasks_2745_;
v___y_2676_ = v___y_2720_;
v___y_2677_ = v___y_2714_;
v___y_2678_ = v___y_2715_;
v___y_2679_ = v___x_2749_;
v___y_2680_ = v___y_2717_;
v___y_2681_ = v___y_2718_;
v___y_2682_ = v___x_2762_;
goto v___jp_2649_;
}
}
}
}
}
v___jp_2767_:
{
if (v___y_2793_ == 0)
{
lean_object* v___x_2794_; lean_object* v_env_2795_; lean_object* v_nextMacroScope_2796_; lean_object* v_ngen_2797_; lean_object* v_auxDeclNGen_2798_; lean_object* v_traceState_2799_; lean_object* v_messages_2800_; lean_object* v_infoState_2801_; lean_object* v_snapshotTasks_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2811_; 
v___x_2794_ = lean_st_ref_take(v___y_2779_);
v_env_2795_ = lean_ctor_get(v___x_2794_, 0);
v_nextMacroScope_2796_ = lean_ctor_get(v___x_2794_, 1);
v_ngen_2797_ = lean_ctor_get(v___x_2794_, 2);
v_auxDeclNGen_2798_ = lean_ctor_get(v___x_2794_, 3);
v_traceState_2799_ = lean_ctor_get(v___x_2794_, 4);
v_messages_2800_ = lean_ctor_get(v___x_2794_, 6);
v_infoState_2801_ = lean_ctor_get(v___x_2794_, 7);
v_snapshotTasks_2802_ = lean_ctor_get(v___x_2794_, 8);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2811_ == 0)
{
lean_object* v_unused_2812_; 
v_unused_2812_ = lean_ctor_get(v___x_2794_, 5);
lean_dec(v_unused_2812_);
v___x_2804_ = v___x_2794_;
v_isShared_2805_ = v_isSharedCheck_2811_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_snapshotTasks_2802_);
lean_inc(v_infoState_2801_);
lean_inc(v_messages_2800_);
lean_inc(v_traceState_2799_);
lean_inc(v_auxDeclNGen_2798_);
lean_inc(v_ngen_2797_);
lean_inc(v_nextMacroScope_2796_);
lean_inc(v_env_2795_);
lean_dec(v___x_2794_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2811_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2806_; lean_object* v___x_2808_; 
v___x_2806_ = l_Lean_Kernel_enableDiag(v_env_2795_, v___y_2786_);
lean_inc_ref(v___y_2787_);
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 5, v___y_2787_);
lean_ctor_set(v___x_2804_, 0, v___x_2806_);
v___x_2808_ = v___x_2804_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v___x_2806_);
lean_ctor_set(v_reuseFailAlloc_2810_, 1, v_nextMacroScope_2796_);
lean_ctor_set(v_reuseFailAlloc_2810_, 2, v_ngen_2797_);
lean_ctor_set(v_reuseFailAlloc_2810_, 3, v_auxDeclNGen_2798_);
lean_ctor_set(v_reuseFailAlloc_2810_, 4, v_traceState_2799_);
lean_ctor_set(v_reuseFailAlloc_2810_, 5, v___y_2787_);
lean_ctor_set(v_reuseFailAlloc_2810_, 6, v_messages_2800_);
lean_ctor_set(v_reuseFailAlloc_2810_, 7, v_infoState_2801_);
lean_ctor_set(v_reuseFailAlloc_2810_, 8, v_snapshotTasks_2802_);
v___x_2808_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
lean_object* v___x_2809_; 
v___x_2809_ = lean_st_ref_set(v___y_2779_, v___x_2808_);
lean_inc(v___y_2779_);
v___y_2695_ = v___y_2768_;
v___y_2696_ = v___y_2771_;
v___y_2697_ = v___y_2770_;
v___y_2698_ = v___y_2769_;
v___y_2699_ = v___y_2773_;
v___y_2700_ = v___y_2772_;
v___y_2701_ = v___y_2775_;
v___y_2702_ = v___y_2774_;
v___y_2703_ = v___y_2776_;
v___y_2704_ = v___y_2777_;
v___y_2705_ = v___y_2778_;
v___y_2706_ = v___y_2780_;
v___y_2707_ = v___y_2781_;
v___y_2708_ = v___y_2779_;
v___y_2709_ = v___y_2782_;
v___y_2710_ = v___y_2783_;
v___y_2711_ = v___y_2784_;
v___y_2712_ = v___y_2785_;
v___y_2713_ = v___y_2786_;
v___y_2714_ = v___y_2787_;
v___y_2715_ = v___y_2788_;
v___y_2716_ = v___y_2789_;
v___y_2717_ = v___y_2790_;
v___y_2718_ = v___y_2791_;
v___y_2719_ = v___y_2792_;
v___y_2720_ = v___y_2779_;
goto v___jp_2694_;
}
}
}
else
{
lean_inc(v___y_2779_);
v___y_2695_ = v___y_2768_;
v___y_2696_ = v___y_2771_;
v___y_2697_ = v___y_2770_;
v___y_2698_ = v___y_2769_;
v___y_2699_ = v___y_2773_;
v___y_2700_ = v___y_2772_;
v___y_2701_ = v___y_2775_;
v___y_2702_ = v___y_2774_;
v___y_2703_ = v___y_2776_;
v___y_2704_ = v___y_2777_;
v___y_2705_ = v___y_2778_;
v___y_2706_ = v___y_2780_;
v___y_2707_ = v___y_2781_;
v___y_2708_ = v___y_2779_;
v___y_2709_ = v___y_2782_;
v___y_2710_ = v___y_2783_;
v___y_2711_ = v___y_2784_;
v___y_2712_ = v___y_2785_;
v___y_2713_ = v___y_2786_;
v___y_2714_ = v___y_2787_;
v___y_2715_ = v___y_2788_;
v___y_2716_ = v___y_2789_;
v___y_2717_ = v___y_2790_;
v___y_2718_ = v___y_2791_;
v___y_2719_ = v___y_2792_;
v___y_2720_ = v___y_2779_;
goto v___jp_2694_;
}
}
v___jp_2816_:
{
lean_object* v___x_2826_; 
if (v_isShared_2487_ == 0)
{
lean_ctor_set_tag(v___x_2486_, 0);
lean_ctor_set(v___x_2486_, 1, v___y_2824_);
lean_ctor_set(v___x_2486_, 0, v___y_2819_);
v___x_2826_ = v___x_2486_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v___y_2819_);
lean_ctor_set(v_reuseFailAlloc_2922_, 1, v___y_2824_);
v___x_2826_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v_moduleData_2830_; lean_object* v___x_2831_; uint8_t v___x_2832_; 
v___x_2827_ = lean_box(0);
lean_inc_ref(v___y_2822_);
v___x_2828_ = l_Lean_EnvExtension_setState___redArg(v___y_2822_, v___y_2823_, v___x_2826_, v___x_2827_);
v___x_2829_ = l_Lean_Environment_header(v___x_2828_);
v_moduleData_2830_ = lean_ctor_get(v___x_2829_, 6);
lean_inc_ref(v_moduleData_2830_);
lean_dec_ref(v___x_2829_);
v___x_2831_ = lean_array_get_size(v_moduleData_2830_);
v___x_2832_ = lean_nat_dec_lt(v___y_2820_, v___x_2831_);
if (v___x_2832_ == 0)
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
lean_dec_ref(v_moduleData_2830_);
lean_dec_ref(v___x_2828_);
lean_dec(v___y_2821_);
lean_dec(v___y_2820_);
lean_dec(v___y_2817_);
lean_dec_ref(v___x_2512_);
lean_dec(v_name_2490_);
lean_dec(v_head_2483_);
lean_dec(v_head_2482_);
v___x_2833_ = lean_obj_once(&l_main___closed__21, &l_main___closed__21_once, _init_l_main___closed__21);
v___x_2834_ = l_panic___at___00main_spec__1(v___x_2833_);
return v___x_2834_;
}
else
{
lean_object* v_base_2835_; lean_object* v_private_2836_; lean_object* v_header_2837_; lean_object* v_serverBaseExts_2838_; lean_object* v_checked_2839_; lean_object* v_asyncConstsMap_2840_; lean_object* v_asyncCtx_x3f_2841_; lean_object* v_importRealizationCtx_x3f_2842_; lean_object* v_localRealizationCtxMap_2843_; lean_object* v_allRealizations_2844_; uint8_t v_isExporting_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2920_; 
v_base_2835_ = lean_ctor_get(v___x_2828_, 0);
lean_inc_ref(v_base_2835_);
v_private_2836_ = lean_ctor_get(v_base_2835_, 0);
lean_inc(v_private_2836_);
v_header_2837_ = lean_ctor_get(v_private_2836_, 5);
lean_inc_ref(v_header_2837_);
v_serverBaseExts_2838_ = lean_ctor_get(v___x_2828_, 1);
v_checked_2839_ = lean_ctor_get(v___x_2828_, 2);
v_asyncConstsMap_2840_ = lean_ctor_get(v___x_2828_, 3);
v_asyncCtx_x3f_2841_ = lean_ctor_get(v___x_2828_, 4);
v_importRealizationCtx_x3f_2842_ = lean_ctor_get(v___x_2828_, 5);
v_localRealizationCtxMap_2843_ = lean_ctor_get(v___x_2828_, 6);
v_allRealizations_2844_ = lean_ctor_get(v___x_2828_, 7);
v_isExporting_2845_ = lean_ctor_get_uint8(v___x_2828_, sizeof(void*)*8);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2920_ == 0)
{
lean_object* v_unused_2921_; 
v_unused_2921_ = lean_ctor_get(v___x_2828_, 0);
lean_dec(v_unused_2921_);
v___x_2847_ = v___x_2828_;
v_isShared_2848_ = v_isSharedCheck_2920_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_allRealizations_2844_);
lean_inc(v_localRealizationCtxMap_2843_);
lean_inc(v_importRealizationCtx_x3f_2842_);
lean_inc(v_asyncCtx_x3f_2841_);
lean_inc(v_asyncConstsMap_2840_);
lean_inc(v_checked_2839_);
lean_inc(v_serverBaseExts_2838_);
lean_dec(v___x_2828_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2920_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v_public_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2918_; 
v_public_2849_ = lean_ctor_get(v_base_2835_, 1);
v_isSharedCheck_2918_ = !lean_is_exclusive(v_base_2835_);
if (v_isSharedCheck_2918_ == 0)
{
lean_object* v_unused_2919_; 
v_unused_2919_ = lean_ctor_get(v_base_2835_, 0);
lean_dec(v_unused_2919_);
v___x_2851_ = v_base_2835_;
v_isShared_2852_ = v_isSharedCheck_2918_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_public_2849_);
lean_dec(v_base_2835_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2918_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v_constants_2853_; uint8_t v_quotInit_2854_; lean_object* v_diagnostics_2855_; lean_object* v_const2ModIdx_2856_; lean_object* v_extensions_2857_; lean_object* v_irBaseExts_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2916_; 
v_constants_2853_ = lean_ctor_get(v_private_2836_, 0);
v_quotInit_2854_ = lean_ctor_get_uint8(v_private_2836_, sizeof(void*)*6);
v_diagnostics_2855_ = lean_ctor_get(v_private_2836_, 1);
v_const2ModIdx_2856_ = lean_ctor_get(v_private_2836_, 2);
v_extensions_2857_ = lean_ctor_get(v_private_2836_, 3);
v_irBaseExts_2858_ = lean_ctor_get(v_private_2836_, 4);
v_isSharedCheck_2916_ = !lean_is_exclusive(v_private_2836_);
if (v_isSharedCheck_2916_ == 0)
{
lean_object* v_unused_2917_; 
v_unused_2917_ = lean_ctor_get(v_private_2836_, 5);
lean_dec(v_unused_2917_);
v___x_2860_ = v_private_2836_;
v_isShared_2861_ = v_isSharedCheck_2916_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_irBaseExts_2858_);
lean_inc(v_extensions_2857_);
lean_inc(v_const2ModIdx_2856_);
lean_inc(v_diagnostics_2855_);
lean_inc(v_constants_2853_);
lean_dec(v_private_2836_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2916_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
uint32_t v_trustLevel_2862_; lean_object* v_mainModule_2863_; uint8_t v_isModule_2864_; lean_object* v_regions_2865_; lean_object* v_modules_2866_; lean_object* v_moduleName2Idx_2867_; lean_object* v_importAllModules_2868_; lean_object* v_moduleData_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2914_; 
v_trustLevel_2862_ = lean_ctor_get_uint32(v_header_2837_, sizeof(void*)*7);
v_mainModule_2863_ = lean_ctor_get(v_header_2837_, 0);
v_isModule_2864_ = lean_ctor_get_uint8(v_header_2837_, sizeof(void*)*7 + 4);
v_regions_2865_ = lean_ctor_get(v_header_2837_, 2);
v_modules_2866_ = lean_ctor_get(v_header_2837_, 3);
v_moduleName2Idx_2867_ = lean_ctor_get(v_header_2837_, 4);
v_importAllModules_2868_ = lean_ctor_get(v_header_2837_, 5);
v_moduleData_2869_ = lean_ctor_get(v_header_2837_, 6);
v_isSharedCheck_2914_ = !lean_is_exclusive(v_header_2837_);
if (v_isSharedCheck_2914_ == 0)
{
lean_object* v_unused_2915_; 
v_unused_2915_ = lean_ctor_get(v_header_2837_, 1);
lean_dec(v_unused_2915_);
v___x_2871_ = v_header_2837_;
v_isShared_2872_ = v_isSharedCheck_2914_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_moduleData_2869_);
lean_inc(v_importAllModules_2868_);
lean_inc(v_moduleName2Idx_2867_);
lean_inc(v_modules_2866_);
lean_inc(v_regions_2865_);
lean_inc(v_mainModule_2863_);
lean_dec(v_header_2837_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2914_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2873_; lean_object* v_imports_2874_; lean_object* v___x_2876_; 
v___x_2873_ = lean_array_fget(v_moduleData_2830_, v___y_2820_);
lean_dec_ref(v_moduleData_2830_);
v_imports_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc_ref(v_imports_2874_);
lean_dec(v___x_2873_);
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 1, v_imports_2874_);
v___x_2876_ = v___x_2871_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 7, 5);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_mainModule_2863_);
lean_ctor_set(v_reuseFailAlloc_2913_, 1, v_imports_2874_);
lean_ctor_set(v_reuseFailAlloc_2913_, 2, v_regions_2865_);
lean_ctor_set(v_reuseFailAlloc_2913_, 3, v_modules_2866_);
lean_ctor_set(v_reuseFailAlloc_2913_, 4, v_moduleName2Idx_2867_);
lean_ctor_set(v_reuseFailAlloc_2913_, 5, v_importAllModules_2868_);
lean_ctor_set(v_reuseFailAlloc_2913_, 6, v_moduleData_2869_);
lean_ctor_set_uint32(v_reuseFailAlloc_2913_, sizeof(void*)*7, v_trustLevel_2862_);
lean_ctor_set_uint8(v_reuseFailAlloc_2913_, sizeof(void*)*7 + 4, v_isModule_2864_);
v___x_2876_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
lean_object* v___x_2878_; 
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 5, v___x_2876_);
v___x_2878_ = v___x_2860_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_constants_2853_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v_diagnostics_2855_);
lean_ctor_set(v_reuseFailAlloc_2912_, 2, v_const2ModIdx_2856_);
lean_ctor_set(v_reuseFailAlloc_2912_, 3, v_extensions_2857_);
lean_ctor_set(v_reuseFailAlloc_2912_, 4, v_irBaseExts_2858_);
lean_ctor_set(v_reuseFailAlloc_2912_, 5, v___x_2876_);
lean_ctor_set_uint8(v_reuseFailAlloc_2912_, sizeof(void*)*6, v_quotInit_2854_);
v___x_2878_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
lean_object* v___x_2880_; 
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 0, v___x_2878_);
v___x_2880_ = v___x_2851_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2878_);
lean_ctor_set(v_reuseFailAlloc_2911_, 1, v_public_2849_);
v___x_2880_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
lean_object* v___x_2882_; 
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 0, v___x_2880_);
v___x_2882_ = v___x_2847_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2880_);
lean_ctor_set(v_reuseFailAlloc_2910_, 1, v_serverBaseExts_2838_);
lean_ctor_set(v_reuseFailAlloc_2910_, 2, v_checked_2839_);
lean_ctor_set(v_reuseFailAlloc_2910_, 3, v_asyncConstsMap_2840_);
lean_ctor_set(v_reuseFailAlloc_2910_, 4, v_asyncCtx_x3f_2841_);
lean_ctor_set(v_reuseFailAlloc_2910_, 5, v_importRealizationCtx_x3f_2842_);
lean_ctor_set(v_reuseFailAlloc_2910_, 6, v_localRealizationCtxMap_2843_);
lean_ctor_set(v_reuseFailAlloc_2910_, 7, v_allRealizations_2844_);
lean_ctor_set_uint8(v_reuseFailAlloc_2910_, sizeof(void*)*8, v_isExporting_2845_);
v___x_2882_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; uint8_t v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v_env_2906_; lean_object* v___x_2907_; uint8_t v___x_2908_; uint8_t v___x_2909_; 
v___x_2883_ = l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
v___x_2884_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2506_, v___x_2883_, v___x_2882_, v___y_2820_, v___y_2818_);
lean_dec(v___y_2820_);
v___x_2885_ = l_Lean_firstFrontendMacroScope;
v___x_2886_ = lean_obj_once(&l_main___closed__22, &l_main___closed__22_once, _init_l_main___closed__22);
v___x_2887_ = ((lean_object*)(l_main___closed__25));
lean_inc_n(v___y_2821_, 3);
v___x_2888_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2888_, 0, v___y_2821_);
lean_ctor_set(v___x_2888_, 1, v___x_2815_);
lean_ctor_set(v___x_2888_, 2, v___x_2497_);
v___x_2889_ = lean_obj_once(&l_main___closed__26, &l_main___closed__26_once, _init_l_main___closed__26);
v___x_2890_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_2891_ = lean_obj_once(&l_main___closed__30, &l_main___closed__30_once, _init_l_main___closed__30);
v___x_2892_ = lean_obj_once(&l_main___closed__31, &l_main___closed__31_once, _init_l_main___closed__31);
v___x_2893_ = ((lean_object*)(l_main___closed__32));
lean_inc_ref(v___x_2888_);
v___x_2894_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2882_);
lean_ctor_set(v___x_2894_, 1, v___x_2886_);
lean_ctor_set(v___x_2894_, 2, v___x_2887_);
lean_ctor_set(v___x_2894_, 3, v___x_2888_);
lean_ctor_set(v___x_2894_, 4, v___x_2889_);
lean_ctor_set(v___x_2894_, 5, v___x_2890_);
lean_ctor_set(v___x_2894_, 6, v___x_2891_);
lean_ctor_set(v___x_2894_, 7, v___x_2892_);
lean_ctor_set(v___x_2894_, 8, v___x_2893_);
v___x_2895_ = lean_st_mk_ref(v___x_2894_);
v___x_2896_ = l_Lean_inheritedTraceOptions;
v___x_2897_ = lean_st_ref_get(v___x_2896_);
v___x_2898_ = lean_st_ref_get(v___x_2895_);
v___x_2899_ = l_Lean_instInhabitedFileMap_default;
v___x_2900_ = lean_unsigned_to_nat(1000u);
v___x_2901_ = lean_box(0);
v___x_2902_ = l_Lean_Core_getMaxHeartbeats(v___x_2512_);
v___x_2903_ = 0;
v___x_2904_ = lean_box(0);
lean_inc_ref(v___x_2512_);
lean_inc(v_head_2482_);
v___x_2905_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2905_, 0, v_head_2482_);
lean_ctor_set(v___x_2905_, 1, v___x_2899_);
lean_ctor_set(v___x_2905_, 2, v___x_2512_);
lean_ctor_set(v___x_2905_, 3, v___x_2511_);
lean_ctor_set(v___x_2905_, 4, v___x_2900_);
lean_ctor_set(v___x_2905_, 5, v___x_2901_);
lean_ctor_set(v___x_2905_, 6, v___y_2821_);
lean_ctor_set(v___x_2905_, 7, v___x_2497_);
lean_ctor_set(v___x_2905_, 8, v___x_2511_);
lean_ctor_set(v___x_2905_, 9, v___x_2902_);
lean_ctor_set(v___x_2905_, 10, v___y_2821_);
lean_ctor_set(v___x_2905_, 11, v___x_2885_);
lean_ctor_set(v___x_2905_, 12, v___x_2904_);
lean_ctor_set(v___x_2905_, 13, v___x_2897_);
lean_ctor_set_uint8(v___x_2905_, sizeof(void*)*14, v___x_2903_);
lean_ctor_set_uint8(v___x_2905_, sizeof(void*)*14 + 1, v___x_2903_);
v_env_2906_ = lean_ctor_get(v___x_2898_, 0);
lean_inc_ref(v_env_2906_);
lean_dec(v___x_2898_);
v___x_2907_ = l_Lean_diagnostics;
v___x_2908_ = l_Lean_Option_get___at___00main_spec__6(v___x_2512_, v___x_2907_);
v___x_2909_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2906_);
lean_dec_ref(v_env_2906_);
if (v___x_2909_ == 0)
{
if (v___x_2908_ == 0)
{
v___y_2768_ = v___x_2904_;
v___y_2769_ = v___x_2832_;
v___y_2770_ = v___x_2885_;
v___y_2771_ = v___x_2497_;
v___y_2772_ = v___x_2903_;
v___y_2773_ = v___x_2890_;
v___y_2774_ = v___y_2817_;
v___y_2775_ = v___x_2907_;
v___y_2776_ = v___x_2901_;
v___y_2777_ = v___x_2899_;
v___y_2778_ = v___x_2896_;
v___y_2779_ = v___x_2895_;
v___y_2780_ = v___x_2892_;
v___y_2781_ = v___x_2889_;
v___y_2782_ = v___x_2887_;
v___y_2783_ = v___x_2893_;
v___y_2784_ = v___y_2821_;
v___y_2785_ = v___x_2886_;
v___y_2786_ = v___x_2908_;
v___y_2787_ = v___x_2890_;
v___y_2788_ = v___x_2884_;
v___y_2789_ = v___x_2883_;
v___y_2790_ = v___x_2888_;
v___y_2791_ = v___x_2891_;
v___y_2792_ = v___x_2905_;
v___y_2793_ = v___x_2832_;
goto v___jp_2767_;
}
else
{
v___y_2768_ = v___x_2904_;
v___y_2769_ = v___x_2832_;
v___y_2770_ = v___x_2885_;
v___y_2771_ = v___x_2497_;
v___y_2772_ = v___x_2903_;
v___y_2773_ = v___x_2890_;
v___y_2774_ = v___y_2817_;
v___y_2775_ = v___x_2907_;
v___y_2776_ = v___x_2901_;
v___y_2777_ = v___x_2899_;
v___y_2778_ = v___x_2896_;
v___y_2779_ = v___x_2895_;
v___y_2780_ = v___x_2892_;
v___y_2781_ = v___x_2889_;
v___y_2782_ = v___x_2887_;
v___y_2783_ = v___x_2893_;
v___y_2784_ = v___y_2821_;
v___y_2785_ = v___x_2886_;
v___y_2786_ = v___x_2908_;
v___y_2787_ = v___x_2890_;
v___y_2788_ = v___x_2884_;
v___y_2789_ = v___x_2883_;
v___y_2790_ = v___x_2888_;
v___y_2791_ = v___x_2891_;
v___y_2792_ = v___x_2905_;
v___y_2793_ = v___x_2909_;
goto v___jp_2767_;
}
}
else
{
v___y_2768_ = v___x_2904_;
v___y_2769_ = v___x_2832_;
v___y_2770_ = v___x_2885_;
v___y_2771_ = v___x_2497_;
v___y_2772_ = v___x_2903_;
v___y_2773_ = v___x_2890_;
v___y_2774_ = v___y_2817_;
v___y_2775_ = v___x_2907_;
v___y_2776_ = v___x_2901_;
v___y_2777_ = v___x_2899_;
v___y_2778_ = v___x_2896_;
v___y_2779_ = v___x_2895_;
v___y_2780_ = v___x_2892_;
v___y_2781_ = v___x_2889_;
v___y_2782_ = v___x_2887_;
v___y_2783_ = v___x_2893_;
v___y_2784_ = v___y_2821_;
v___y_2785_ = v___x_2886_;
v___y_2786_ = v___x_2908_;
v___y_2787_ = v___x_2890_;
v___y_2788_ = v___x_2884_;
v___y_2789_ = v___x_2883_;
v___y_2790_ = v___x_2888_;
v___y_2791_ = v___x_2891_;
v___y_2792_ = v___x_2905_;
v___y_2793_ = v___x_2908_;
goto v___jp_2767_;
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
v___jp_2923_:
{
lean_object* v___x_2929_; lean_object* v_toEnvExtension_2930_; lean_object* v_asyncMode_2931_; lean_object* v___x_2932_; lean_object* v_importedEntries_2933_; lean_object* v_state_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; uint8_t v___x_2937_; 
v___x_2929_ = l_Lean_IR_declMapExt;
v_toEnvExtension_2930_ = lean_ctor_get(v___x_2929_, 0);
v_asyncMode_2931_ = lean_ctor_get(v_toEnvExtension_2930_, 2);
lean_inc(v___y_2927_);
lean_inc_ref(v___y_2928_);
v___x_2932_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2503_, v_toEnvExtension_2930_, v___y_2928_, v_asyncMode_2931_, v___y_2927_);
v_importedEntries_2933_ = lean_ctor_get(v___x_2932_, 0);
lean_inc_ref(v_importedEntries_2933_);
v_state_2934_ = lean_ctor_get(v___x_2932_, 1);
lean_inc(v_state_2934_);
lean_dec(v___x_2932_);
v___x_2935_ = lean_array_get_borrowed(v___x_2504_, v_importedEntries_2933_, v___y_2926_);
v___x_2936_ = lean_array_get_size(v___x_2935_);
v___x_2937_ = lean_nat_dec_lt(v___x_2511_, v___x_2936_);
if (v___x_2937_ == 0)
{
v___y_2817_ = v___y_2924_;
v___y_2818_ = v___y_2925_;
v___y_2819_ = v_importedEntries_2933_;
v___y_2820_ = v___y_2926_;
v___y_2821_ = v___y_2927_;
v___y_2822_ = v_toEnvExtension_2930_;
v___y_2823_ = v___y_2928_;
v___y_2824_ = v_state_2934_;
goto v___jp_2816_;
}
else
{
uint8_t v___x_2938_; 
v___x_2938_ = lean_nat_dec_le(v___x_2936_, v___x_2936_);
if (v___x_2938_ == 0)
{
if (v___x_2937_ == 0)
{
v___y_2817_ = v___y_2924_;
v___y_2818_ = v___y_2925_;
v___y_2819_ = v_importedEntries_2933_;
v___y_2820_ = v___y_2926_;
v___y_2821_ = v___y_2927_;
v___y_2822_ = v_toEnvExtension_2930_;
v___y_2823_ = v___y_2928_;
v___y_2824_ = v_state_2934_;
goto v___jp_2816_;
}
else
{
size_t v___x_2939_; size_t v___x_2940_; lean_object* v___x_2941_; 
v___x_2939_ = ((size_t)0ULL);
v___x_2940_ = lean_usize_of_nat(v___x_2936_);
lean_inc_ref(v___y_2928_);
v___x_2941_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_2928_, v___x_2935_, v___x_2939_, v___x_2940_, v_state_2934_);
v___y_2817_ = v___y_2924_;
v___y_2818_ = v___y_2925_;
v___y_2819_ = v_importedEntries_2933_;
v___y_2820_ = v___y_2926_;
v___y_2821_ = v___y_2927_;
v___y_2822_ = v_toEnvExtension_2930_;
v___y_2823_ = v___y_2928_;
v___y_2824_ = v___x_2941_;
goto v___jp_2816_;
}
}
else
{
size_t v___x_2942_; size_t v___x_2943_; lean_object* v___x_2944_; 
v___x_2942_ = ((size_t)0ULL);
v___x_2943_ = lean_usize_of_nat(v___x_2936_);
lean_inc_ref(v___y_2928_);
v___x_2944_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_2928_, v___x_2935_, v___x_2942_, v___x_2943_, v_state_2934_);
v___y_2817_ = v___y_2924_;
v___y_2818_ = v___y_2925_;
v___y_2819_ = v_importedEntries_2933_;
v___y_2820_ = v___y_2926_;
v___y_2821_ = v___y_2927_;
v___y_2822_ = v_toEnvExtension_2930_;
v___y_2823_ = v___y_2928_;
v___y_2824_ = v___x_2944_;
goto v___jp_2816_;
}
}
}
v___jp_2945_:
{
uint8_t v___x_2953_; 
v___x_2953_ = lean_nat_dec_lt(v___x_2511_, v___y_2951_);
if (v___x_2953_ == 0)
{
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2949_);
v___y_2924_ = v___y_2946_;
v___y_2925_ = v___y_2947_;
v___y_2926_ = v___y_2948_;
v___y_2927_ = v___y_2950_;
v___y_2928_ = v___y_2952_;
goto v___jp_2923_;
}
else
{
uint8_t v___x_2954_; 
v___x_2954_ = lean_nat_dec_le(v___y_2951_, v___y_2951_);
if (v___x_2954_ == 0)
{
if (v___x_2953_ == 0)
{
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2949_);
v___y_2924_ = v___y_2946_;
v___y_2925_ = v___y_2947_;
v___y_2926_ = v___y_2948_;
v___y_2927_ = v___y_2950_;
v___y_2928_ = v___y_2952_;
goto v___jp_2923_;
}
else
{
size_t v___x_2955_; size_t v___x_2956_; lean_object* v___x_2957_; 
v___x_2955_ = ((size_t)0ULL);
v___x_2956_ = lean_usize_of_nat(v___y_2951_);
lean_dec(v___y_2951_);
v___x_2957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_2949_, v___x_2955_, v___x_2956_, v___y_2952_);
lean_dec_ref(v___y_2949_);
v___y_2924_ = v___y_2946_;
v___y_2925_ = v___y_2947_;
v___y_2926_ = v___y_2948_;
v___y_2927_ = v___y_2950_;
v___y_2928_ = v___x_2957_;
goto v___jp_2923_;
}
}
else
{
size_t v___x_2958_; size_t v___x_2959_; lean_object* v___x_2960_; 
v___x_2958_ = ((size_t)0ULL);
v___x_2959_ = lean_usize_of_nat(v___y_2951_);
lean_dec(v___y_2951_);
v___x_2960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_2949_, v___x_2958_, v___x_2959_, v___y_2952_);
lean_dec_ref(v___y_2949_);
v___y_2924_ = v___y_2946_;
v___y_2925_ = v___y_2947_;
v___y_2926_ = v___y_2948_;
v___y_2927_ = v___y_2950_;
v___y_2928_ = v___x_2960_;
goto v___jp_2923_;
}
}
}
v___jp_2961_:
{
lean_object* v___x_2968_; uint8_t v___x_2969_; 
v___x_2968_ = lean_array_get_size(v___y_2967_);
v___x_2969_ = lean_nat_dec_lt(v___x_2511_, v___x_2968_);
if (v___x_2969_ == 0)
{
v___y_2946_ = v___y_2963_;
v___y_2947_ = v___y_2965_;
v___y_2948_ = v___y_2962_;
v___y_2949_ = v___y_2967_;
v___y_2950_ = v___y_2966_;
v___y_2951_ = v___x_2968_;
v___y_2952_ = v___y_2964_;
goto v___jp_2945_;
}
else
{
uint8_t v___x_2970_; 
v___x_2970_ = lean_nat_dec_le(v___x_2968_, v___x_2968_);
if (v___x_2970_ == 0)
{
if (v___x_2969_ == 0)
{
v___y_2946_ = v___y_2963_;
v___y_2947_ = v___y_2965_;
v___y_2948_ = v___y_2962_;
v___y_2949_ = v___y_2967_;
v___y_2950_ = v___y_2966_;
v___y_2951_ = v___x_2968_;
v___y_2952_ = v___y_2964_;
goto v___jp_2945_;
}
else
{
size_t v___x_2971_; size_t v___x_2972_; lean_object* v___x_2973_; 
v___x_2971_ = ((size_t)0ULL);
v___x_2972_ = lean_usize_of_nat(v___x_2968_);
v___x_2973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_2967_, v___x_2971_, v___x_2972_, v___y_2964_);
v___y_2946_ = v___y_2963_;
v___y_2947_ = v___y_2965_;
v___y_2948_ = v___y_2962_;
v___y_2949_ = v___y_2967_;
v___y_2950_ = v___y_2966_;
v___y_2951_ = v___x_2968_;
v___y_2952_ = v___x_2973_;
goto v___jp_2945_;
}
}
else
{
size_t v___x_2974_; size_t v___x_2975_; lean_object* v___x_2976_; 
v___x_2974_ = ((size_t)0ULL);
v___x_2975_ = lean_usize_of_nat(v___x_2968_);
v___x_2976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_2967_, v___x_2974_, v___x_2975_, v___y_2964_);
v___y_2946_ = v___y_2963_;
v___y_2947_ = v___y_2965_;
v___y_2948_ = v___y_2962_;
v___y_2949_ = v___y_2967_;
v___y_2950_ = v___y_2966_;
v___y_2951_ = v___x_2968_;
v___y_2952_ = v___x_2976_;
goto v___jp_2945_;
}
}
}
v___jp_2980_:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___f_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2982_ = l_Lean_instInhabitedImportState_default;
v___x_2983_ = lean_box(v___x_2979_);
v___x_2984_ = lean_box(v___y_2981_);
v___x_2985_ = lean_box(v___x_2508_);
lean_inc_ref(v___x_2512_);
lean_inc(v_name_2490_);
v___f_2986_ = lean_alloc_closure((void*)(l_main___lam__0___boxed), 9, 8);
lean_closure_set(v___f_2986_, 0, v___x_2982_);
lean_closure_set(v___f_2986_, 1, v___x_2978_);
lean_closure_set(v___f_2986_, 2, v___x_2983_);
lean_closure_set(v___f_2986_, 3, v___x_2505_);
lean_closure_set(v___f_2986_, 4, v___x_2984_);
lean_closure_set(v___f_2986_, 5, v_name_2490_);
lean_closure_set(v___f_2986_, 6, v___x_2512_);
lean_closure_set(v___f_2986_, 7, v___x_2985_);
v___x_2987_ = lean_alloc_closure((void*)(l_Lean_withImporting___boxed), 3, 2);
lean_closure_set(v___x_2987_, 0, lean_box(0));
lean_closure_set(v___x_2987_, 1, v___f_2986_);
v___x_2988_ = lean_box(0);
v___x_2989_ = l_Lean_profileitIOUnsafe___redArg(v___x_2813_, v___x_2512_, v___x_2987_, v___x_2988_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2991_; lean_object* v_ext_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_a_2990_);
lean_dec_ref(v___x_2989_);
v___x_2991_ = l_Lean_Compiler_CSimp_ext;
v_ext_2992_ = lean_ctor_get(v___x_2991_, 1);
lean_inc(v_name_2490_);
v___x_2993_ = l_Lean_Environment_setMainModule(v_a_2990_, v_name_2490_);
lean_inc_ref(v_ext_2992_);
v___x_2994_ = l_main___elam__0___redArg(v___x_2988_, v___x_2499_, v_ext_2992_, v___x_2993_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v_a_2995_; lean_object* v___x_2996_; lean_object* v_ext_2997_; lean_object* v___x_2998_; 
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
lean_inc(v_a_2995_);
lean_dec_ref(v___x_2994_);
v___x_2996_ = l_Lean_Meta_instanceExtension;
v_ext_2997_ = lean_ctor_get(v___x_2996_, 1);
lean_inc_ref(v_ext_2997_);
v___x_2998_ = l_main___elam__0___redArg(v___x_2988_, v___x_2499_, v_ext_2997_, v_a_2995_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_a_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_a_2999_);
lean_dec_ref(v___x_2998_);
v___x_3000_ = l_Lean_classExtension;
v___x_3001_ = l_main___elam__0___redArg(v___x_2988_, v___x_2500_, v___x_3000_, v_a_2999_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_a_3002_);
lean_dec_ref(v___x_3001_);
v___x_3003_ = l_Lean_Meta_Match_Extension_extension;
v___x_3004_ = l_main___elam__0___redArg(v___x_2988_, v___x_2501_, v___x_3003_, v_a_3002_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3033_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3007_ = v___x_3004_;
v_isShared_3008_ = v_isSharedCheck_3033_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_3004_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3033_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3009_; 
v___x_3009_ = l_Lean_Environment_getModuleIdx_x3f(v_a_3005_, v_name_2490_);
if (lean_obj_tag(v___x_3009_) == 1)
{
lean_object* v_val_3010_; lean_object* v___x_3011_; uint8_t v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; uint8_t v___x_3016_; 
lean_del_object(v___x_3007_);
v_val_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_val_3010_);
lean_dec_ref(v___x_3009_);
v___x_3011_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_3012_ = 0;
v___x_3013_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2502_, v___x_3011_, v_a_3005_, v_val_3010_, v___x_3012_);
v___x_3014_ = lean_array_get_size(v___x_3013_);
v___x_3015_ = ((lean_object*)(l_main___closed__33));
v___x_3016_ = lean_nat_dec_lt(v___x_2511_, v___x_3014_);
if (v___x_3016_ == 0)
{
lean_dec_ref(v___x_3013_);
v___y_2962_ = v_val_3010_;
v___y_2963_ = v___x_2988_;
v___y_2964_ = v_a_3005_;
v___y_2965_ = v___x_3012_;
v___y_2966_ = v___x_2988_;
v___y_2967_ = v___x_3015_;
goto v___jp_2961_;
}
else
{
uint8_t v___x_3017_; 
v___x_3017_ = lean_nat_dec_le(v___x_3014_, v___x_3014_);
if (v___x_3017_ == 0)
{
if (v___x_3016_ == 0)
{
lean_dec_ref(v___x_3013_);
v___y_2962_ = v_val_3010_;
v___y_2963_ = v___x_2988_;
v___y_2964_ = v_a_3005_;
v___y_2965_ = v___x_3012_;
v___y_2966_ = v___x_2988_;
v___y_2967_ = v___x_3015_;
goto v___jp_2961_;
}
else
{
size_t v___x_3018_; size_t v___x_3019_; lean_object* v___x_3020_; 
v___x_3018_ = ((size_t)0ULL);
v___x_3019_ = lean_usize_of_nat(v___x_3014_);
lean_inc(v_a_3005_);
v___x_3020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_3005_, v___x_3013_, v___x_3018_, v___x_3019_, v___x_3015_);
lean_dec_ref(v___x_3013_);
v___y_2962_ = v_val_3010_;
v___y_2963_ = v___x_2988_;
v___y_2964_ = v_a_3005_;
v___y_2965_ = v___x_3012_;
v___y_2966_ = v___x_2988_;
v___y_2967_ = v___x_3020_;
goto v___jp_2961_;
}
}
else
{
size_t v___x_3021_; size_t v___x_3022_; lean_object* v___x_3023_; 
v___x_3021_ = ((size_t)0ULL);
v___x_3022_ = lean_usize_of_nat(v___x_3014_);
lean_inc(v_a_3005_);
v___x_3023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_a_3005_, v___x_3013_, v___x_3021_, v___x_3022_, v___x_3015_);
lean_dec_ref(v___x_3013_);
v___y_2962_ = v_val_3010_;
v___y_2963_ = v___x_2988_;
v___y_2964_ = v_a_3005_;
v___y_2965_ = v___x_3012_;
v___y_2966_ = v___x_2988_;
v___y_2967_ = v___x_3023_;
goto v___jp_2961_;
}
}
}
else
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3031_; 
lean_dec(v___x_3009_);
lean_dec(v_a_3005_);
lean_dec_ref(v___x_2512_);
lean_del_object(v___x_2486_);
lean_dec(v_head_2483_);
lean_dec(v_head_2482_);
v___x_3024_ = ((lean_object*)(l_main___closed__34));
v___x_3025_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2490_, v___x_2508_);
v___x_3026_ = lean_string_append(v___x_3024_, v___x_3025_);
lean_dec_ref(v___x_3025_);
v___x_3027_ = ((lean_object*)(l_main___closed__35));
v___x_3028_ = lean_string_append(v___x_3026_, v___x_3027_);
v___x_3029_ = lean_mk_io_user_error(v___x_3028_);
if (v_isShared_3008_ == 0)
{
lean_ctor_set_tag(v___x_3007_, 1);
lean_ctor_set(v___x_3007_, 0, v___x_3029_);
v___x_3031_ = v___x_3007_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v___x_3029_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec_ref(v___x_2512_);
lean_dec(v_name_2490_);
lean_del_object(v___x_2486_);
lean_dec(v_head_2483_);
lean_dec(v_head_2482_);
v_a_3034_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_3004_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3004_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
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
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
lean_dec_ref(v___x_2512_);
lean_dec(v_name_2490_);
lean_del_object(v___x_2486_);
lean_dec(v_head_2483_);
lean_dec(v_head_2482_);
v_a_3042_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___x_3001_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3001_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3042_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
lean_dec_ref(v___x_2512_);
lean_dec(v_name_2490_);
lean_del_object(v___x_2486_);
lean_dec(v_head_2483_);
lean_dec(v_head_2482_);
v_a_3050_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_2998_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_2998_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3050_);
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
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
lean_dec_ref(v___x_2512_);
lean_dec(v_name_2490_);
lean_del_object(v___x_2486_);
lean_dec(v_head_2483_);
lean_dec(v_head_2482_);
v_a_3058_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_2994_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_2994_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
lean_dec_ref(v___x_2512_);
lean_dec(v_name_2490_);
lean_del_object(v___x_2486_);
lean_dec(v_head_2483_);
lean_dec(v_head_2482_);
v_a_3066_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_2989_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_2989_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3066_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
}
else
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
lean_dec(v_a_2494_);
lean_dec(v_name_2490_);
lean_del_object(v___x_2486_);
lean_dec(v_head_2483_);
lean_dec(v_head_2482_);
v_a_3076_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_2498_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_2498_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec(v_a_2494_);
lean_dec(v_name_2490_);
lean_del_object(v___x_2486_);
lean_dec(v_head_2483_);
lean_dec(v_head_2482_);
v_a_3084_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_2495_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_2495_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
lean_dec(v_name_2490_);
lean_del_object(v___x_2486_);
lean_dec(v_head_2483_);
lean_dec(v_head_2482_);
v_a_3092_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3094_ = v___x_2493_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_2493_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3097_; 
if (v_isShared_3095_ == 0)
{
v___x_3097_ = v___x_3094_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_a_3092_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
}
else
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3107_; 
lean_del_object(v___x_2486_);
lean_dec(v_tail_2484_);
lean_dec(v_head_2483_);
lean_dec(v_head_2482_);
v_a_3100_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3102_ = v___x_2488_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_2488_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3105_; 
if (v_isShared_3103_ == 0)
{
v___x_3105_ = v___x_3102_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_a_3100_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
}
}
else
{
lean_dec_ref(v_tail_2479_);
lean_dec(v_tail_2480_);
lean_dec_ref(v_args_2454_);
goto v___jp_2456_;
}
}
else
{
lean_dec_ref(v_args_2454_);
lean_dec(v_tail_2479_);
goto v___jp_2456_;
}
}
else
{
lean_dec(v_args_2454_);
goto v___jp_2456_;
}
v___jp_2456_:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = ((lean_object*)(l_main___closed__0));
v___x_2458_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_2457_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2466_; 
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2466_ == 0)
{
lean_object* v_unused_2467_; 
v_unused_2467_ = lean_ctor_get(v___x_2458_, 0);
lean_dec(v_unused_2467_);
v___x_2460_ = v___x_2458_;
v_isShared_2461_ = v_isSharedCheck_2466_;
goto v_resetjp_2459_;
}
else
{
lean_dec(v___x_2458_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2466_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2462_; lean_object* v___x_2464_; 
v___x_2462_ = l_main___boxed__const__1;
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 0, v___x_2462_);
v___x_2464_ = v___x_2460_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2462_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
v_a_2468_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2458_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2458_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
v___jp_2476_:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2477_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2478_ = l_panic___at___00main_spec__1(v___x_2477_);
return v___x_2478_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_3109_, lean_object* v_a_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = _lean_main(v_args_3109_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2(lean_object* v_as_3112_, lean_object* v_as_x27_3113_, lean_object* v_b_3114_, lean_object* v_a_3115_){
_start:
{
lean_object* v___x_3117_; 
v___x_3117_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v_as_x27_3113_, v_b_3114_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___boxed(lean_object* v_as_3118_, lean_object* v_as_x27_3119_, lean_object* v_b_3120_, lean_object* v_a_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l_List_forIn_x27_loop___at___00main_spec__2(v_as_3118_, v_as_x27_3119_, v_b_3120_, v_a_3121_);
lean_dec(v_as_3118_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11(lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v___x_3127_; 
v___x_3127_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___redArg(v___y_3125_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11___boxed(lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__11(v___y_3128_, v___y_3129_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12(lean_object* v_00_u03b2_3132_, lean_object* v_m_3133_, lean_object* v_a_3134_, lean_object* v_fallback_3135_){
_start:
{
lean_object* v___x_3136_; 
v___x_3136_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12___redArg(v_m_3133_, v_a_3134_, v_fallback_3135_);
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12___boxed(lean_object* v_00_u03b2_3137_, lean_object* v_m_3138_, lean_object* v_a_3139_, lean_object* v_fallback_3140_){
_start:
{
lean_object* v_res_3141_; 
v_res_3141_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12(v_00_u03b2_3137_, v_m_3138_, v_a_3139_, v_fallback_3140_);
lean_dec(v_fallback_3140_);
lean_dec_ref(v_a_3139_);
lean_dec_ref(v_m_3138_);
return v_res_3141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13(lean_object* v_00_u03b2_3142_, lean_object* v_m_3143_, lean_object* v_a_3144_, lean_object* v_b_3145_){
_start:
{
lean_object* v___x_3146_; 
v___x_3146_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13___redArg(v_m_3143_, v_a_3144_, v_b_3145_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16(lean_object* v_n_3147_, lean_object* v_as_3148_, lean_object* v_lo_3149_, lean_object* v_hi_3150_, lean_object* v_w_3151_, lean_object* v_hlo_3152_, lean_object* v_hhi_3153_){
_start:
{
lean_object* v___x_3154_; 
v___x_3154_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___redArg(v_as_3148_, v_lo_3149_, v_hi_3150_);
return v___x_3154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16___boxed(lean_object* v_n_3155_, lean_object* v_as_3156_, lean_object* v_lo_3157_, lean_object* v_hi_3158_, lean_object* v_w_3159_, lean_object* v_hlo_3160_, lean_object* v_hhi_3161_){
_start:
{
lean_object* v_res_3162_; 
v_res_3162_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__16(v_n_3155_, v_as_3156_, v_lo_3157_, v_hi_3158_, v_w_3159_, v_hlo_3160_, v_hhi_3161_);
lean_dec(v_hi_3158_);
lean_dec(v_n_3155_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12_spec__13(lean_object* v_00_u03b2_3163_, lean_object* v_a_3164_, lean_object* v_fallback_3165_, lean_object* v_x_3166_){
_start:
{
lean_object* v___x_3167_; 
v___x_3167_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12_spec__13___redArg(v_a_3164_, v_fallback_3165_, v_x_3166_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12_spec__13___boxed(lean_object* v_00_u03b2_3168_, lean_object* v_a_3169_, lean_object* v_fallback_3170_, lean_object* v_x_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__12_spec__13(v_00_u03b2_3168_, v_a_3169_, v_fallback_3170_, v_x_3171_);
lean_dec(v_x_3171_);
lean_dec(v_fallback_3170_);
lean_dec_ref(v_a_3169_);
return v_res_3172_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__15(lean_object* v_00_u03b2_3173_, lean_object* v_a_3174_, lean_object* v_x_3175_){
_start:
{
uint8_t v___x_3176_; 
v___x_3176_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__15___redArg(v_a_3174_, v_x_3175_);
return v___x_3176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__15___boxed(lean_object* v_00_u03b2_3177_, lean_object* v_a_3178_, lean_object* v_x_3179_){
_start:
{
uint8_t v_res_3180_; lean_object* v_r_3181_; 
v_res_3180_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__15(v_00_u03b2_3177_, v_a_3178_, v_x_3179_);
lean_dec(v_x_3179_);
lean_dec_ref(v_a_3178_);
v_r_3181_ = lean_box(v_res_3180_);
return v_r_3181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16(lean_object* v_00_u03b2_3182_, lean_object* v_data_3183_){
_start:
{
lean_object* v___x_3184_; 
v___x_3184_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16___redArg(v_data_3183_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__17(lean_object* v_00_u03b2_3185_, lean_object* v_a_3186_, lean_object* v_b_3187_, lean_object* v_x_3188_){
_start:
{
lean_object* v___x_3189_; 
v___x_3189_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__17___redArg(v_a_3186_, v_b_3187_, v_x_3188_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16_spec__28(lean_object* v_00_u03b2_3190_, lean_object* v_i_3191_, lean_object* v_source_3192_, lean_object* v_target_3193_){
_start:
{
lean_object* v___x_3194_; 
v___x_3194_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16_spec__28___redArg(v_i_3191_, v_source_3192_, v_target_3193_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20_spec__35(uint8_t v___x_3195_, lean_object* v_as_3196_, size_t v_sz_3197_, size_t v_i_3198_, lean_object* v_b_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_){
_start:
{
lean_object* v___x_3203_; 
v___x_3203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20_spec__35___redArg(v___x_3195_, v_as_3196_, v_sz_3197_, v_i_3198_, v_b_3199_, v___y_3200_);
return v___x_3203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20_spec__35___boxed(lean_object* v___x_3204_, lean_object* v_as_3205_, lean_object* v_sz_3206_, lean_object* v_i_3207_, lean_object* v_b_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
uint8_t v___x_36503__boxed_3212_; size_t v_sz_boxed_3213_; size_t v_i_boxed_3214_; lean_object* v_res_3215_; 
v___x_36503__boxed_3212_ = lean_unbox(v___x_3204_);
v_sz_boxed_3213_ = lean_unbox_usize(v_sz_3206_);
lean_dec(v_sz_3206_);
v_i_boxed_3214_ = lean_unbox_usize(v_i_3207_);
lean_dec(v_i_3207_);
v_res_3215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__20_spec__35(v___x_36503__boxed_3212_, v_as_3205_, v_sz_boxed_3213_, v_i_boxed_3214_, v_b_3208_, v___y_3209_, v___y_3210_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
lean_dec_ref(v_as_3205_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16_spec__28_spec__37(lean_object* v_00_u03b2_3216_, lean_object* v_x_3217_, lean_object* v_x_3218_){
_start:
{
lean_object* v___x_3219_; 
v___x_3219_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__13_spec__16_spec__28_spec__37___redArg(v_x_3217_, v_x_3218_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42(uint8_t v___x_3220_, lean_object* v_as_3221_, size_t v_sz_3222_, size_t v_i_3223_, lean_object* v_b_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
lean_object* v___x_3228_; 
v___x_3228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42___redArg(v___x_3220_, v_as_3221_, v_sz_3222_, v_i_3223_, v_b_3224_, v___y_3225_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42___boxed(lean_object* v___x_3229_, lean_object* v_as_3230_, lean_object* v_sz_3231_, lean_object* v_i_3232_, lean_object* v_b_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
uint8_t v___x_36523__boxed_3237_; size_t v_sz_boxed_3238_; size_t v_i_boxed_3239_; lean_object* v_res_3240_; 
v___x_36523__boxed_3237_ = lean_unbox(v___x_3229_);
v_sz_boxed_3238_ = lean_unbox_usize(v_sz_3231_);
lean_dec(v_sz_3231_);
v_i_boxed_3239_ = lean_unbox_usize(v_i_3232_);
lean_dec(v_i_3232_);
v_res_3240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__8_spec__14_spec__19_spec__33_spec__42(v___x_36523__boxed_3237_, v_as_3230_, v_sz_boxed_3238_, v_i_boxed_3239_, v_b_3233_, v___y_3234_, v___y_3235_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec_ref(v_as_3230_);
return v_res_3240_;
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
