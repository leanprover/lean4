// Lean compiler output
// Module: Lean.Elab.Tactic.AutoTry
// Imports: import Init.Try import Lean.Linter.Basic import Lean.Server.InfoUtils import Lean.Elab.Tactic.Try import Lean.Elab.Tactic.Meta import Lean.Elab.BuiltinTerm
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
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_Range_includes(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Try_collectTryCoreSuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isMaxRecDepth(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_io_get_num_heartbeats();
extern lean_object* l_Lean_firstFrontendMacroScope;
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_append(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
extern lean_object* l_Lean_diagnostics;
extern lean_object* l_Lean_maxRecDepth;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Syntax_instHashableRange_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_ofPosition(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_List_head_x3f___redArg(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_foldInfo___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_List_replicateTR___redArg(lean_object*, lean_object*);
lean_object* lean_string_mk(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_runTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_Range_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageLog_reportedPlusUnreported(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_withSetOptionIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "autoTry"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "onEmptyProof"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(163, 27, 117, 182, 216, 95, 83, 170)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(246, 66, 211, 114, 249, 119, 53, 144)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "run `try\?` on empty proofs and empty subproofs and report any suggestions"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__5_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__5_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__5_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__6_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__5_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__6_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__6_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__8_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__6_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__8_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__8_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__9_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__9_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__9_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__10_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__8_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__9_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__10_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__10_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__12_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__10_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__12_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__12_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__13_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "AutoTry"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__13_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__13_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__14_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__12_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__13_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(123, 158, 41, 193, 164, 214, 205, 50)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__14_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__14_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__15_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__14_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(134, 107, 19, 219, 142, 120, 71, 103)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__15_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__15_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__16_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__15_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(143, 231, 72, 247, 126, 9, 135, 248)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__16_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__16_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__17_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__16_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__9_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(177, 8, 71, 56, 242, 58, 39, 172)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__17_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__17_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__18_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__17_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(56, 117, 79, 29, 89, 186, 57, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__18_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__18_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__19_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__18_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__13_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 64, 103, 152, 252, 208, 234, 111)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__19_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__19_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__20_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__19_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(238, 179, 17, 120, 45, 125, 47, 248)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__20_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__20_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__21_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__20_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(207, 38, 249, 99, 24, 26, 215, 145)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__21_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__21_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "tryOnEmptyBy"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(157, 147, 145, 244, 86, 29, 251, 255)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "deprecated alias for `autoTry.onEmptyProof`"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "2026-06-29"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__5_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "use `autoTry.onEmptyProof` instead"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__5_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__5_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__6_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__5_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__6_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__6_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__6_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__8_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__8_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__8_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__9_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__8_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__9_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__9_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__10_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__19_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(46, 131, 101, 225, 212, 78, 145, 106)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__10_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__10_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__10_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(116, 35, 199, 123, 211, 20, 145, 177)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "onUnsolvedGoal"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(163, 27, 117, 182, 216, 95, 83, 170)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(227, 35, 177, 27, 37, 159, 95, 227)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 90, .m_capacity = 90, .m_length = 89, .m_data = "run `try\?` on each proof or subproof that left a goal unsolved and report any suggestions"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__20_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(226, 125, 75, 37, 214, 50, 216, 179)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "onSorry"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(163, 27, 117, 182, 216, 95, 83, 170)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(114, 120, 5, 251, 211, 194, 145, 174)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "run `try\?` on each `sorry` tactic and report any suggestions"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__20_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(243, 152, 110, 4, 119, 174, 78, 244)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "showEdits"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(40, 215, 222, 176, 152, 52, 0, 225)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(20, 21, 81, 144, 12, 72, 243, 203)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(17, 28, 27, 160, 121, 115, 26, 139)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 155, .m_capacity = 155, .m_length = 154, .m_data = "if set, autoTry logs an info message per emitted suggestion showing the edit's source range and the literal replacement text (for testing the widget data)"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__5_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__19_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(29, 204, 20, 75, 31, 132, 119, 169)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__5_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__5_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__6_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__5_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(69, 93, 158, 104, 42, 66, 94, 233)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__6_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__6_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__6_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(12, 153, 76, 12, 100, 0, 9, 151)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_debug_autoTry_showEdits;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(163, 27, 117, 182, 216, 95, 83, 170)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__19_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(191, 70, 59, 26, 74, 166, 147, 107)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(74, 139, 48, 72, 56, 123, 120, 146)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__5_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 21, 162, 206, 138, 91, 239, 46)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__5_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__5_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__6_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__5_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__9_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(29, 163, 242, 57, 142, 233, 206, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__6_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__6_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__6_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(4, 255, 74, 69, 64, 33, 149, 223)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__8_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__13_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(102, 105, 242, 12, 167, 164, 120, 157)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__8_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__8_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__9_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__8_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value),((lean_object*)(((size_t)(938150806) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(180, 57, 244, 78, 41, 42, 251, 188)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__9_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__9_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__10_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__10_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__10_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__9_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__10_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(187, 82, 166, 189, 92, 2, 80, 56)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__12_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__12_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__12_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__13_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__12_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(27, 225, 145, 109, 89, 49, 216, 44)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__13_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__13_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__14_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__13_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(110, 154, 234, 233, 174, 233, 200, 29)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__14_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__14_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__2;
static const lean_array_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__6;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__7;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__14_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__16_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "internal exception "};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20_value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21_value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " (unknown)"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__22 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__22_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tacticSorry"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tacticAdmit"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__2_value;
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_unsolvedGoal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_unsolvedGoal_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_sorryTactic_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_sorryTactic_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "; "};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeqBracketed"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10___lam__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 205, 46, 93, 234, 75, 44, 75)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 55, 102, 232, 177, 170, 100, 130)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10___lam__0___closed__1_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10___lam__0___boxed(lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 145, .m_capacity = 145, .m_length = 144, .m_data = "Tactic.unsolvedGoals message yielded no (msgCtx, namingCtx, goal) tuples; producer not following the `withContext`/`withNamingContext` contract\?"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "no tacticSeq body found for unsolved-goals message at "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__9;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "; unrecognised seq variant\?"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__11;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10_spec__14(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__2;
static const lean_closure_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__3_value;
static const lean_array_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "try\? raised: "};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "term elab raised: "};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__1_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(8) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 1, 0, 1, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__4_value;
static const lean_array_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 16, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__5_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Try these:"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Try this:"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Try this: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "autoTry edit: insert "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " at +"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "tryTrace"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 128, 230, 128, 87, 180, 97, 21)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "try\?"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "suppressed: InfoView at insert point does not show exactly one goal state with one goal"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "trigger points: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " onSorry="};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " onUnsolved="};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "running: onEmpty="};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "skipping: command has non-unsolved-goal errors"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_withSetOptionIn___boxed, .m_arity = 6, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___closed__0_value)} };
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "autoTryHook"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__19_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___closed__2_value),LEAN_SCALAR_PTR_LITERAL(234, 31, 149, 163, 211, 218, 138, 113)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___closed__1_value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___closed__3_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___closed__4_value;
LEAN_EXPORT const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_87_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_88_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_89_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__21_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_90_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__spec__0(v___x_87_, v___x_88_, v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4____boxed(lean_object* v_a_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_();
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_121_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_));
v___x_122_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__9_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_));
v___x_123_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_));
v___x_124_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__spec__0(v___x_121_, v___x_122_, v___x_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4____boxed(lean_object* v_a_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_();
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_141_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4_));
v___x_142_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4_));
v___x_143_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4_));
v___x_144_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__spec__0(v___x_141_, v___x_142_, v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4____boxed(lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4_();
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_161_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4_));
v___x_162_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4_));
v___x_163_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4_));
v___x_164_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__spec__0(v___x_161_, v___x_162_, v___x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4____boxed(lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4_();
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_189_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4_));
v___x_190_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4_));
v___x_191_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4_));
v___x_192_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__spec__0(v___x_189_, v___x_190_, v___x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4____boxed(lean_object* v_a_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4_();
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_232_; uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_232_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_233_ = 0;
v___x_234_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__14_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_235_ = l_Lean_registerTraceClass(v___x_232_, v___x_233_, v___x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2____boxed(lean_object* v_a_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_();
return v_res_237_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(lean_object* v_opts_238_, lean_object* v_opt_239_){
_start:
{
lean_object* v_name_240_; lean_object* v_defValue_241_; lean_object* v_map_242_; lean_object* v___x_243_; 
v_name_240_ = lean_ctor_get(v_opt_239_, 0);
v_defValue_241_ = lean_ctor_get(v_opt_239_, 1);
v_map_242_ = lean_ctor_get(v_opts_238_, 0);
v___x_243_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_242_, v_name_240_);
if (lean_obj_tag(v___x_243_) == 0)
{
uint8_t v___x_244_; 
v___x_244_ = lean_unbox(v_defValue_241_);
return v___x_244_;
}
else
{
lean_object* v_val_245_; 
v_val_245_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_val_245_);
lean_dec_ref_known(v___x_243_, 1);
if (lean_obj_tag(v_val_245_) == 1)
{
uint8_t v_v_246_; 
v_v_246_ = lean_ctor_get_uint8(v_val_245_, 0);
lean_dec_ref_known(v_val_245_, 0);
return v_v_246_;
}
else
{
uint8_t v___x_247_; 
lean_dec(v_val_245_);
v___x_247_ = lean_unbox(v_defValue_241_);
return v___x_247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0___boxed(lean_object* v_opts_248_, lean_object* v_opt_249_){
_start:
{
uint8_t v_res_250_; lean_object* v_r_251_; 
v_res_250_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_248_, v_opt_249_);
lean_dec_ref(v_opt_249_);
lean_dec_ref(v_opts_248_);
v_r_251_ = lean_box(v_res_250_);
return v_r_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__1(lean_object* v_opts_252_, lean_object* v_opt_253_){
_start:
{
lean_object* v_name_254_; lean_object* v_defValue_255_; lean_object* v_map_256_; lean_object* v___x_257_; 
v_name_254_ = lean_ctor_get(v_opt_253_, 0);
v_defValue_255_ = lean_ctor_get(v_opt_253_, 1);
v_map_256_ = lean_ctor_get(v_opts_252_, 0);
v___x_257_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_256_, v_name_254_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_inc(v_defValue_255_);
return v_defValue_255_;
}
else
{
lean_object* v_val_258_; 
v_val_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_val_258_);
lean_dec_ref_known(v___x_257_, 1);
if (lean_obj_tag(v_val_258_) == 3)
{
lean_object* v_v_259_; 
v_v_259_ = lean_ctor_get(v_val_258_, 0);
lean_inc(v_v_259_);
lean_dec_ref_known(v_val_258_, 1);
return v_v_259_;
}
else
{
lean_dec(v_val_258_);
lean_inc(v_defValue_255_);
return v_defValue_255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__1___boxed(lean_object* v_opts_260_, lean_object* v_opt_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__1(v_opts_260_, v_opt_261_);
lean_dec_ref(v_opt_261_);
lean_dec_ref(v_opts_260_);
return v_res_262_;
}
}
static uint64_t _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__1(void){
_start:
{
lean_object* v___x_269_; uint64_t v___x_270_; 
v___x_269_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__0));
v___x_270_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_269_);
return v___x_270_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__2(void){
_start:
{
uint64_t v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = lean_uint64_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__1);
v___x_272_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__0));
v___x_273_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set_uint64(v___x_273_, sizeof(void*)*1, v___x_271_);
return v___x_273_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4(void){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_276_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4);
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
return v___x_278_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__6(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5);
v___x_280_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
lean_ctor_set(v___x_280_, 2, v___x_279_);
lean_ctor_set(v___x_280_, 3, v___x_279_);
lean_ctor_set(v___x_280_, 4, v___x_279_);
lean_ctor_set(v___x_280_, 5, v___x_279_);
return v___x_280_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__7(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_281_ = lean_unsigned_to_nat(32u);
v___x_282_ = lean_mk_empty_array_with_capacity(v___x_281_);
v___x_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
return v___x_283_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8(void){
_start:
{
size_t v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_284_ = ((size_t)5ULL);
v___x_285_ = lean_unsigned_to_nat(0u);
v___x_286_ = lean_unsigned_to_nat(32u);
v___x_287_ = lean_mk_empty_array_with_capacity(v___x_286_);
v___x_288_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__7, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__7);
v___x_289_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v___x_287_);
lean_ctor_set(v___x_289_, 2, v___x_285_);
lean_ctor_set(v___x_289_, 3, v___x_285_);
lean_ctor_set_usize(v___x_289_, 4, v___x_284_);
return v___x_289_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5);
v___x_291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
lean_ctor_set(v___x_291_, 2, v___x_290_);
lean_ctor_set(v___x_291_, 3, v___x_290_);
lean_ctor_set(v___x_291_, 4, v___x_290_);
return v___x_291_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5);
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
return v___x_293_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_294_ = l_Lean_NameSet_empty;
v___x_295_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8);
v___x_296_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
lean_ctor_set(v___x_296_, 2, v___x_294_);
return v___x_296_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_297_ = lean_unsigned_to_nat(1u);
v___x_298_ = l_Lean_firstFrontendMacroScope;
v___x_299_ = lean_nat_add(v___x_298_, v___x_297_);
return v___x_299_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17(void){
_start:
{
lean_object* v___x_310_; uint64_t v___x_311_; lean_object* v___x_312_; 
v___x_310_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8);
v___x_311_ = 0ULL;
v___x_312_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set_uint64(v___x_312_, sizeof(void*)*1, v___x_311_);
return v___x_312_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; lean_object* v___x_316_; 
v___x_313_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8);
v___x_314_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5);
v___x_315_ = 1;
v___x_316_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set(v___x_316_, 1, v___x_314_);
lean_ctor_set(v___x_316_, 2, v___x_313_);
lean_ctor_set_uint8(v___x_316_, sizeof(void*)*3, v___x_315_);
return v___x_316_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = l_Lean_Options_empty;
v___x_318_ = l_Lean_Core_getMaxHeartbeats(v___x_317_);
return v___x_318_;
}
}
static uint8_t _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_322_ = l_Lean_diagnostics;
v___x_323_ = l_Lean_Options_empty;
v___x_324_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v___x_323_, v___x_322_);
return v___x_324_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_325_ = l_Lean_maxRecDepth;
v___x_326_ = l_Lean_Options_empty;
v___x_327_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__1(v___x_326_, v___x_325_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(lean_object* v_env_328_, lean_object* v_mctx_329_, lean_object* v_lctx_330_, lean_object* v_opts_331_, lean_object* v_namingCtx_332_, lean_object* v_x_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v___x_337_; uint8_t v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v_fileName_364_; lean_object* v_fileMap_365_; lean_object* v_ref_366_; lean_object* v_cancelTk_x3f_367_; lean_object* v_a_369_; lean_object* v_a_376_; lean_object* v_currNamespace_378_; lean_object* v_openDecls_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v_env_385_; lean_object* v___x_386_; lean_object* v___y_388_; uint8_t v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_479_; uint8_t v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; uint8_t v___y_483_; lean_object* v___x_503_; uint8_t v___x_504_; lean_object* v___y_506_; lean_object* v___y_507_; uint8_t v___y_537_; uint8_t v___x_557_; 
v___x_337_ = lean_box(1);
v___x_338_ = 0;
v___x_339_ = l_Lean_Environment_setExporting(v_env_328_, v___x_338_);
v___x_340_ = 1;
v___x_341_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__2, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__2_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__2);
v___x_342_ = lean_unsigned_to_nat(0u);
v___x_343_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__3));
v___x_344_ = lean_box(0);
v___x_345_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_345_, 0, v___x_341_);
lean_ctor_set(v___x_345_, 1, v___x_337_);
lean_ctor_set(v___x_345_, 2, v_lctx_330_);
lean_ctor_set(v___x_345_, 3, v___x_343_);
lean_ctor_set(v___x_345_, 4, v___x_344_);
lean_ctor_set(v___x_345_, 5, v___x_342_);
lean_ctor_set(v___x_345_, 6, v___x_344_);
lean_ctor_set_uint8(v___x_345_, sizeof(void*)*7, v___x_338_);
lean_ctor_set_uint8(v___x_345_, sizeof(void*)*7 + 1, v___x_338_);
lean_ctor_set_uint8(v___x_345_, sizeof(void*)*7 + 2, v___x_338_);
lean_ctor_set_uint8(v___x_345_, sizeof(void*)*7 + 3, v___x_340_);
v___x_346_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__6, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__6_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__6);
v___x_347_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8);
v___x_348_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9);
v___x_349_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10);
v___x_350_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11);
v___x_351_ = lean_io_get_num_heartbeats();
v___x_352_ = l_Lean_firstFrontendMacroScope;
v___x_353_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12);
v___x_354_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__15));
v___x_355_ = lean_box(0);
v___x_356_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__16));
v___x_357_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17);
v___x_358_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18);
v___x_359_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_359_, 0, v___x_339_);
lean_ctor_set(v___x_359_, 1, v___x_353_);
lean_ctor_set(v___x_359_, 2, v___x_354_);
lean_ctor_set(v___x_359_, 3, v___x_356_);
lean_ctor_set(v___x_359_, 4, v___x_357_);
lean_ctor_set(v___x_359_, 5, v___x_349_);
lean_ctor_set(v___x_359_, 6, v___x_350_);
lean_ctor_set(v___x_359_, 7, v___x_358_);
lean_ctor_set(v___x_359_, 8, v___x_343_);
v___x_360_ = lean_st_mk_ref(v___x_359_);
v___x_361_ = l_Lean_inheritedTraceOptions;
v___x_362_ = lean_st_ref_get(v___x_361_);
v___x_363_ = lean_st_ref_get(v___x_360_);
v_fileName_364_ = lean_ctor_get(v_a_334_, 0);
v_fileMap_365_ = lean_ctor_get(v_a_334_, 1);
v_ref_366_ = lean_ctor_get(v_a_334_, 7);
v_cancelTk_x3f_367_ = lean_ctor_get(v_a_334_, 9);
v_currNamespace_378_ = lean_ctor_get(v_namingCtx_332_, 0);
v_openDecls_379_ = lean_ctor_get(v_namingCtx_332_, 1);
v___x_380_ = l_Lean_Options_empty;
v___x_381_ = lean_unsigned_to_nat(1000u);
v___x_382_ = lean_box(0);
v___x_383_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19);
lean_inc(v_cancelTk_x3f_367_);
lean_inc(v_openDecls_379_);
lean_inc(v_currNamespace_378_);
lean_inc_ref(v_fileMap_365_);
lean_inc_ref(v_fileName_364_);
v___x_384_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_384_, 0, v_fileName_364_);
lean_ctor_set(v___x_384_, 1, v_fileMap_365_);
lean_ctor_set(v___x_384_, 2, v___x_380_);
lean_ctor_set(v___x_384_, 3, v___x_342_);
lean_ctor_set(v___x_384_, 4, v___x_381_);
lean_ctor_set(v___x_384_, 5, v___x_382_);
lean_ctor_set(v___x_384_, 6, v_currNamespace_378_);
lean_ctor_set(v___x_384_, 7, v_openDecls_379_);
lean_ctor_set(v___x_384_, 8, v___x_351_);
lean_ctor_set(v___x_384_, 9, v___x_383_);
lean_ctor_set(v___x_384_, 10, v___x_355_);
lean_ctor_set(v___x_384_, 11, v___x_352_);
lean_ctor_set(v___x_384_, 12, v_cancelTk_x3f_367_);
lean_ctor_set(v___x_384_, 13, v___x_362_);
lean_ctor_set_uint8(v___x_384_, sizeof(void*)*14, v___x_338_);
lean_ctor_set_uint8(v___x_384_, sizeof(void*)*14 + 1, v___x_338_);
v_env_385_ = lean_ctor_get(v___x_363_, 0);
lean_inc_ref(v_env_385_);
lean_dec(v___x_363_);
v___x_386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_386_, 0, v_mctx_329_);
lean_ctor_set(v___x_386_, 1, v___x_346_);
lean_ctor_set(v___x_386_, 2, v___x_337_);
lean_ctor_set(v___x_386_, 3, v___x_347_);
lean_ctor_set(v___x_386_, 4, v___x_348_);
v___x_503_ = l_Lean_diagnostics;
v___x_504_ = lean_uint8_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23);
v___x_557_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_385_);
lean_dec_ref(v_env_385_);
if (v___x_557_ == 0)
{
if (v___x_504_ == 0)
{
lean_inc(v___x_360_);
v___y_506_ = v___x_384_;
v___y_507_ = v___x_360_;
goto v___jp_505_;
}
else
{
v___y_537_ = v___x_557_;
goto v___jp_536_;
}
}
else
{
v___y_537_ = v___x_504_;
goto v___jp_536_;
}
v___jp_368_:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_370_ = lean_io_error_to_string(v_a_369_);
v___x_371_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
v___x_372_ = l_Lean_MessageData_ofFormat(v___x_371_);
lean_inc(v_ref_366_);
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v_ref_366_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
v___x_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
return v___x_374_;
}
v___jp_375_:
{
lean_object* v___x_377_; 
v___x_377_ = lean_mk_io_user_error(v_a_376_);
v_a_369_ = v___x_377_;
goto v___jp_368_;
}
v___jp_387_:
{
lean_object* v___x_392_; lean_object* v_fileName_393_; lean_object* v_fileMap_394_; lean_object* v_currRecDepth_395_; lean_object* v_ref_396_; lean_object* v_currNamespace_397_; lean_object* v_openDecls_398_; lean_object* v_initHeartbeats_399_; lean_object* v_maxHeartbeats_400_; lean_object* v_quotContext_401_; lean_object* v_currMacroScope_402_; lean_object* v_cancelTk_x3f_403_; uint8_t v_suppressElabErrors_404_; lean_object* v_inheritedTraceOptions_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_475_; 
v___x_392_ = lean_st_mk_ref(v___x_386_);
v_fileName_393_ = lean_ctor_get(v___y_390_, 0);
v_fileMap_394_ = lean_ctor_get(v___y_390_, 1);
v_currRecDepth_395_ = lean_ctor_get(v___y_390_, 3);
v_ref_396_ = lean_ctor_get(v___y_390_, 5);
v_currNamespace_397_ = lean_ctor_get(v___y_390_, 6);
v_openDecls_398_ = lean_ctor_get(v___y_390_, 7);
v_initHeartbeats_399_ = lean_ctor_get(v___y_390_, 8);
v_maxHeartbeats_400_ = lean_ctor_get(v___y_390_, 9);
v_quotContext_401_ = lean_ctor_get(v___y_390_, 10);
v_currMacroScope_402_ = lean_ctor_get(v___y_390_, 11);
v_cancelTk_x3f_403_ = lean_ctor_get(v___y_390_, 12);
v_suppressElabErrors_404_ = lean_ctor_get_uint8(v___y_390_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_405_ = lean_ctor_get(v___y_390_, 13);
v_isSharedCheck_475_ = !lean_is_exclusive(v___y_390_);
if (v_isSharedCheck_475_ == 0)
{
lean_object* v_unused_476_; lean_object* v_unused_477_; 
v_unused_476_ = lean_ctor_get(v___y_390_, 4);
lean_dec(v_unused_476_);
v_unused_477_ = lean_ctor_get(v___y_390_, 2);
lean_dec(v_unused_477_);
v___x_407_ = v___y_390_;
v_isShared_408_ = v_isSharedCheck_475_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_inheritedTraceOptions_405_);
lean_inc(v_cancelTk_x3f_403_);
lean_inc(v_currMacroScope_402_);
lean_inc(v_quotContext_401_);
lean_inc(v_maxHeartbeats_400_);
lean_inc(v_initHeartbeats_399_);
lean_inc(v_openDecls_398_);
lean_inc(v_currNamespace_397_);
lean_inc(v_ref_396_);
lean_inc(v_currRecDepth_395_);
lean_inc(v_fileMap_394_);
lean_inc(v_fileName_393_);
lean_dec(v___y_390_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_475_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v___x_411_; 
v___x_409_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__1(v_opts_331_, v___y_388_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 4, v___x_409_);
lean_ctor_set(v___x_407_, 2, v_opts_331_);
v___x_411_ = v___x_407_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_fileName_393_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_fileMap_394_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v_opts_331_);
lean_ctor_set(v_reuseFailAlloc_474_, 3, v_currRecDepth_395_);
lean_ctor_set(v_reuseFailAlloc_474_, 4, v___x_409_);
lean_ctor_set(v_reuseFailAlloc_474_, 5, v_ref_396_);
lean_ctor_set(v_reuseFailAlloc_474_, 6, v_currNamespace_397_);
lean_ctor_set(v_reuseFailAlloc_474_, 7, v_openDecls_398_);
lean_ctor_set(v_reuseFailAlloc_474_, 8, v_initHeartbeats_399_);
lean_ctor_set(v_reuseFailAlloc_474_, 9, v_maxHeartbeats_400_);
lean_ctor_set(v_reuseFailAlloc_474_, 10, v_quotContext_401_);
lean_ctor_set(v_reuseFailAlloc_474_, 11, v_currMacroScope_402_);
lean_ctor_set(v_reuseFailAlloc_474_, 12, v_cancelTk_x3f_403_);
lean_ctor_set(v_reuseFailAlloc_474_, 13, v_inheritedTraceOptions_405_);
lean_ctor_set_uint8(v_reuseFailAlloc_474_, sizeof(void*)*14 + 1, v_suppressElabErrors_404_);
v___x_411_ = v_reuseFailAlloc_474_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
lean_object* v___x_412_; 
lean_ctor_set_uint8(v___x_411_, sizeof(void*)*14, v___y_389_);
lean_inc(v___x_392_);
v___x_412_ = lean_apply_5(v_x_333_, v___x_345_, v___x_392_, v___x_411_, v___y_391_, lean_box(0));
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_458_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_458_ == 0)
{
v___x_415_ = v___x_412_;
v_isShared_416_ = v_isSharedCheck_458_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_412_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_458_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v_traceState_420_; lean_object* v_traceState_421_; lean_object* v_env_422_; lean_object* v_messages_423_; lean_object* v_scopes_424_; lean_object* v_usedQuotCtxts_425_; lean_object* v_nextMacroScope_426_; lean_object* v_maxRecDepth_427_; lean_object* v_ngen_428_; lean_object* v_auxDeclNGen_429_; lean_object* v_infoState_430_; lean_object* v_snapshotTasks_431_; lean_object* v_prevLinterStates_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_456_; 
v___x_417_ = lean_st_ref_get(v___x_392_);
lean_dec(v___x_392_);
lean_dec(v___x_417_);
v___x_418_ = lean_st_ref_get(v___x_360_);
lean_dec(v___x_360_);
v___x_419_ = lean_st_ref_take(v_a_335_);
v_traceState_420_ = lean_ctor_get(v___x_419_, 9);
lean_inc_ref(v_traceState_420_);
v_traceState_421_ = lean_ctor_get(v___x_418_, 4);
lean_inc_ref(v_traceState_421_);
v_env_422_ = lean_ctor_get(v___x_419_, 0);
v_messages_423_ = lean_ctor_get(v___x_419_, 1);
v_scopes_424_ = lean_ctor_get(v___x_419_, 2);
v_usedQuotCtxts_425_ = lean_ctor_get(v___x_419_, 3);
v_nextMacroScope_426_ = lean_ctor_get(v___x_419_, 4);
v_maxRecDepth_427_ = lean_ctor_get(v___x_419_, 5);
v_ngen_428_ = lean_ctor_get(v___x_419_, 6);
v_auxDeclNGen_429_ = lean_ctor_get(v___x_419_, 7);
v_infoState_430_ = lean_ctor_get(v___x_419_, 8);
v_snapshotTasks_431_ = lean_ctor_get(v___x_419_, 10);
v_prevLinterStates_432_ = lean_ctor_get(v___x_419_, 11);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_456_ == 0)
{
lean_object* v_unused_457_; 
v_unused_457_ = lean_ctor_get(v___x_419_, 9);
lean_dec(v_unused_457_);
v___x_434_ = v___x_419_;
v_isShared_435_ = v_isSharedCheck_456_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_prevLinterStates_432_);
lean_inc(v_snapshotTasks_431_);
lean_inc(v_infoState_430_);
lean_inc(v_auxDeclNGen_429_);
lean_inc(v_ngen_428_);
lean_inc(v_maxRecDepth_427_);
lean_inc(v_nextMacroScope_426_);
lean_inc(v_usedQuotCtxts_425_);
lean_inc(v_scopes_424_);
lean_inc(v_messages_423_);
lean_inc(v_env_422_);
lean_dec(v___x_419_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_456_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v_messages_436_; uint64_t v_tid_437_; lean_object* v_traces_438_; lean_object* v_traces_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_455_; 
v_messages_436_ = lean_ctor_get(v___x_418_, 6);
lean_inc_ref(v_messages_436_);
lean_dec(v___x_418_);
v_tid_437_ = lean_ctor_get_uint64(v_traceState_420_, sizeof(void*)*1);
v_traces_438_ = lean_ctor_get(v_traceState_420_, 0);
lean_inc_ref(v_traces_438_);
lean_dec_ref(v_traceState_420_);
v_traces_439_ = lean_ctor_get(v_traceState_421_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v_traceState_421_);
if (v_isSharedCheck_455_ == 0)
{
v___x_441_ = v_traceState_421_;
v_isShared_442_ = v_isSharedCheck_455_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_traces_439_);
lean_dec(v_traceState_421_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_455_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_443_ = l_Lean_MessageLog_append(v_messages_423_, v_messages_436_);
v___x_444_ = l_Lean_PersistentArray_append___redArg(v_traces_438_, v_traces_439_);
lean_dec_ref(v_traces_439_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_444_);
v___x_446_ = v___x_441_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_444_);
v___x_446_ = v_reuseFailAlloc_454_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_448_; 
lean_ctor_set_uint64(v___x_446_, sizeof(void*)*1, v_tid_437_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 9, v___x_446_);
lean_ctor_set(v___x_434_, 1, v___x_443_);
v___x_448_ = v___x_434_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_env_422_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v___x_443_);
lean_ctor_set(v_reuseFailAlloc_453_, 2, v_scopes_424_);
lean_ctor_set(v_reuseFailAlloc_453_, 3, v_usedQuotCtxts_425_);
lean_ctor_set(v_reuseFailAlloc_453_, 4, v_nextMacroScope_426_);
lean_ctor_set(v_reuseFailAlloc_453_, 5, v_maxRecDepth_427_);
lean_ctor_set(v_reuseFailAlloc_453_, 6, v_ngen_428_);
lean_ctor_set(v_reuseFailAlloc_453_, 7, v_auxDeclNGen_429_);
lean_ctor_set(v_reuseFailAlloc_453_, 8, v_infoState_430_);
lean_ctor_set(v_reuseFailAlloc_453_, 9, v___x_446_);
lean_ctor_set(v_reuseFailAlloc_453_, 10, v_snapshotTasks_431_);
lean_ctor_set(v_reuseFailAlloc_453_, 11, v_prevLinterStates_432_);
v___x_448_ = v_reuseFailAlloc_453_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_449_ = lean_st_ref_put(v_a_335_, v___x_448_);
if (v_isShared_416_ == 0)
{
v___x_451_ = v___x_415_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_413_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_459_; 
lean_dec(v___x_392_);
lean_dec(v___x_360_);
v_a_459_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_459_);
lean_dec_ref_known(v___x_412_, 1);
if (lean_obj_tag(v_a_459_) == 0)
{
lean_object* v_msg_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_msg_460_ = lean_ctor_get(v_a_459_, 1);
lean_inc_ref(v_msg_460_);
lean_dec_ref_known(v_a_459_, 2);
v___x_461_ = l_Lean_MessageData_toString(v_msg_460_);
v___x_462_ = lean_mk_io_user_error(v___x_461_);
v_a_369_ = v___x_462_;
goto v___jp_368_;
}
else
{
lean_object* v_id_463_; lean_object* v___x_464_; 
v_id_463_ = lean_ctor_get(v_a_459_, 0);
lean_inc(v_id_463_);
lean_dec_ref_known(v_a_459_, 2);
v___x_464_ = l_Lean_InternalExceptionId_getName(v_id_463_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
lean_dec(v_id_463_);
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_465_);
lean_dec_ref_known(v___x_464_, 1);
v___x_466_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20));
v___x_467_ = l_Lean_Name_toString(v_a_465_, v___x_340_);
v___x_468_ = lean_string_append(v___x_466_, v___x_467_);
lean_dec_ref(v___x_467_);
v_a_376_ = v___x_468_;
goto v___jp_375_;
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
lean_dec_ref_known(v___x_464_, 1);
v___x_469_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21));
v___x_470_ = l_Nat_reprFast(v_id_463_);
v___x_471_ = lean_string_append(v___x_469_, v___x_470_);
lean_dec_ref(v___x_470_);
v___x_472_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__22));
v___x_473_ = lean_string_append(v___x_471_, v___x_472_);
v_a_376_ = v___x_473_;
goto v___jp_375_;
}
}
}
}
}
}
v___jp_478_:
{
if (v___y_483_ == 0)
{
lean_object* v___x_484_; lean_object* v_env_485_; lean_object* v_nextMacroScope_486_; lean_object* v_ngen_487_; lean_object* v_auxDeclNGen_488_; lean_object* v_traceState_489_; lean_object* v_messages_490_; lean_object* v_infoState_491_; lean_object* v_snapshotTasks_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_501_; 
v___x_484_ = lean_st_ref_take(v___y_482_);
v_env_485_ = lean_ctor_get(v___x_484_, 0);
v_nextMacroScope_486_ = lean_ctor_get(v___x_484_, 1);
v_ngen_487_ = lean_ctor_get(v___x_484_, 2);
v_auxDeclNGen_488_ = lean_ctor_get(v___x_484_, 3);
v_traceState_489_ = lean_ctor_get(v___x_484_, 4);
v_messages_490_ = lean_ctor_get(v___x_484_, 6);
v_infoState_491_ = lean_ctor_get(v___x_484_, 7);
v_snapshotTasks_492_ = lean_ctor_get(v___x_484_, 8);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_501_ == 0)
{
lean_object* v_unused_502_; 
v_unused_502_ = lean_ctor_get(v___x_484_, 5);
lean_dec(v_unused_502_);
v___x_494_ = v___x_484_;
v_isShared_495_ = v_isSharedCheck_501_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_snapshotTasks_492_);
lean_inc(v_infoState_491_);
lean_inc(v_messages_490_);
lean_inc(v_traceState_489_);
lean_inc(v_auxDeclNGen_488_);
lean_inc(v_ngen_487_);
lean_inc(v_nextMacroScope_486_);
lean_inc(v_env_485_);
lean_dec(v___x_484_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_501_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_496_ = l_Lean_Kernel_enableDiag(v_env_485_, v___y_480_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 5, v___x_349_);
lean_ctor_set(v___x_494_, 0, v___x_496_);
v___x_498_ = v___x_494_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_496_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_nextMacroScope_486_);
lean_ctor_set(v_reuseFailAlloc_500_, 2, v_ngen_487_);
lean_ctor_set(v_reuseFailAlloc_500_, 3, v_auxDeclNGen_488_);
lean_ctor_set(v_reuseFailAlloc_500_, 4, v_traceState_489_);
lean_ctor_set(v_reuseFailAlloc_500_, 5, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_500_, 6, v_messages_490_);
lean_ctor_set(v_reuseFailAlloc_500_, 7, v_infoState_491_);
lean_ctor_set(v_reuseFailAlloc_500_, 8, v_snapshotTasks_492_);
v___x_498_ = v_reuseFailAlloc_500_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_499_; 
v___x_499_ = lean_st_ref_put(v___y_482_, v___x_498_);
v___y_388_ = v___y_479_;
v___y_389_ = v___y_480_;
v___y_390_ = v___y_481_;
v___y_391_ = v___y_482_;
goto v___jp_387_;
}
}
}
else
{
v___y_388_ = v___y_479_;
v___y_389_ = v___y_480_;
v___y_390_ = v___y_481_;
v___y_391_ = v___y_482_;
goto v___jp_387_;
}
}
v___jp_505_:
{
lean_object* v___x_508_; lean_object* v_fileName_509_; lean_object* v_fileMap_510_; lean_object* v_currRecDepth_511_; lean_object* v_ref_512_; lean_object* v_currNamespace_513_; lean_object* v_openDecls_514_; lean_object* v_initHeartbeats_515_; lean_object* v_maxHeartbeats_516_; lean_object* v_quotContext_517_; lean_object* v_currMacroScope_518_; lean_object* v_cancelTk_x3f_519_; uint8_t v_suppressElabErrors_520_; lean_object* v_inheritedTraceOptions_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_533_; 
v___x_508_ = lean_st_ref_get(v___y_507_);
v_fileName_509_ = lean_ctor_get(v___y_506_, 0);
v_fileMap_510_ = lean_ctor_get(v___y_506_, 1);
v_currRecDepth_511_ = lean_ctor_get(v___y_506_, 3);
v_ref_512_ = lean_ctor_get(v___y_506_, 5);
v_currNamespace_513_ = lean_ctor_get(v___y_506_, 6);
v_openDecls_514_ = lean_ctor_get(v___y_506_, 7);
v_initHeartbeats_515_ = lean_ctor_get(v___y_506_, 8);
v_maxHeartbeats_516_ = lean_ctor_get(v___y_506_, 9);
v_quotContext_517_ = lean_ctor_get(v___y_506_, 10);
v_currMacroScope_518_ = lean_ctor_get(v___y_506_, 11);
v_cancelTk_x3f_519_ = lean_ctor_get(v___y_506_, 12);
v_suppressElabErrors_520_ = lean_ctor_get_uint8(v___y_506_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_521_ = lean_ctor_get(v___y_506_, 13);
v_isSharedCheck_533_ = !lean_is_exclusive(v___y_506_);
if (v_isSharedCheck_533_ == 0)
{
lean_object* v_unused_534_; lean_object* v_unused_535_; 
v_unused_534_ = lean_ctor_get(v___y_506_, 4);
lean_dec(v_unused_534_);
v_unused_535_ = lean_ctor_get(v___y_506_, 2);
lean_dec(v_unused_535_);
v___x_523_ = v___y_506_;
v_isShared_524_ = v_isSharedCheck_533_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_inheritedTraceOptions_521_);
lean_inc(v_cancelTk_x3f_519_);
lean_inc(v_currMacroScope_518_);
lean_inc(v_quotContext_517_);
lean_inc(v_maxHeartbeats_516_);
lean_inc(v_initHeartbeats_515_);
lean_inc(v_openDecls_514_);
lean_inc(v_currNamespace_513_);
lean_inc(v_ref_512_);
lean_inc(v_currRecDepth_511_);
lean_inc(v_fileMap_510_);
lean_inc(v_fileName_509_);
lean_dec(v___y_506_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_533_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v_env_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v_env_525_ = lean_ctor_get(v___x_508_, 0);
lean_inc_ref(v_env_525_);
lean_dec(v___x_508_);
v___x_526_ = l_Lean_maxRecDepth;
v___x_527_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 4, v___x_527_);
lean_ctor_set(v___x_523_, 2, v___x_380_);
v___x_529_ = v___x_523_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_fileName_509_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_fileMap_510_);
lean_ctor_set(v_reuseFailAlloc_532_, 2, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_532_, 3, v_currRecDepth_511_);
lean_ctor_set(v_reuseFailAlloc_532_, 4, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_532_, 5, v_ref_512_);
lean_ctor_set(v_reuseFailAlloc_532_, 6, v_currNamespace_513_);
lean_ctor_set(v_reuseFailAlloc_532_, 7, v_openDecls_514_);
lean_ctor_set(v_reuseFailAlloc_532_, 8, v_initHeartbeats_515_);
lean_ctor_set(v_reuseFailAlloc_532_, 9, v_maxHeartbeats_516_);
lean_ctor_set(v_reuseFailAlloc_532_, 10, v_quotContext_517_);
lean_ctor_set(v_reuseFailAlloc_532_, 11, v_currMacroScope_518_);
lean_ctor_set(v_reuseFailAlloc_532_, 12, v_cancelTk_x3f_519_);
lean_ctor_set(v_reuseFailAlloc_532_, 13, v_inheritedTraceOptions_521_);
lean_ctor_set_uint8(v_reuseFailAlloc_532_, sizeof(void*)*14 + 1, v_suppressElabErrors_520_);
v___x_529_ = v_reuseFailAlloc_532_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
uint8_t v___x_530_; uint8_t v___x_531_; 
lean_ctor_set_uint8(v___x_529_, sizeof(void*)*14, v___x_504_);
v___x_530_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_331_, v___x_503_);
v___x_531_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_525_);
lean_dec_ref(v_env_525_);
if (v___x_531_ == 0)
{
if (v___x_530_ == 0)
{
v___y_388_ = v___x_526_;
v___y_389_ = v___x_530_;
v___y_390_ = v___x_529_;
v___y_391_ = v___y_507_;
goto v___jp_387_;
}
else
{
v___y_479_ = v___x_526_;
v___y_480_ = v___x_530_;
v___y_481_ = v___x_529_;
v___y_482_ = v___y_507_;
v___y_483_ = v___x_531_;
goto v___jp_478_;
}
}
else
{
v___y_479_ = v___x_526_;
v___y_480_ = v___x_530_;
v___y_481_ = v___x_529_;
v___y_482_ = v___y_507_;
v___y_483_ = v___x_530_;
goto v___jp_478_;
}
}
}
}
v___jp_536_:
{
if (v___y_537_ == 0)
{
lean_object* v___x_538_; lean_object* v_env_539_; lean_object* v_nextMacroScope_540_; lean_object* v_ngen_541_; lean_object* v_auxDeclNGen_542_; lean_object* v_traceState_543_; lean_object* v_messages_544_; lean_object* v_infoState_545_; lean_object* v_snapshotTasks_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_555_; 
v___x_538_ = lean_st_ref_take(v___x_360_);
v_env_539_ = lean_ctor_get(v___x_538_, 0);
v_nextMacroScope_540_ = lean_ctor_get(v___x_538_, 1);
v_ngen_541_ = lean_ctor_get(v___x_538_, 2);
v_auxDeclNGen_542_ = lean_ctor_get(v___x_538_, 3);
v_traceState_543_ = lean_ctor_get(v___x_538_, 4);
v_messages_544_ = lean_ctor_get(v___x_538_, 6);
v_infoState_545_ = lean_ctor_get(v___x_538_, 7);
v_snapshotTasks_546_ = lean_ctor_get(v___x_538_, 8);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; 
v_unused_556_ = lean_ctor_get(v___x_538_, 5);
lean_dec(v_unused_556_);
v___x_548_ = v___x_538_;
v_isShared_549_ = v_isSharedCheck_555_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_snapshotTasks_546_);
lean_inc(v_infoState_545_);
lean_inc(v_messages_544_);
lean_inc(v_traceState_543_);
lean_inc(v_auxDeclNGen_542_);
lean_inc(v_ngen_541_);
lean_inc(v_nextMacroScope_540_);
lean_inc(v_env_539_);
lean_dec(v___x_538_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_555_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_550_ = l_Lean_Kernel_enableDiag(v_env_539_, v___x_504_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 5, v___x_349_);
lean_ctor_set(v___x_548_, 0, v___x_550_);
v___x_552_ = v___x_548_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_nextMacroScope_540_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v_ngen_541_);
lean_ctor_set(v_reuseFailAlloc_554_, 3, v_auxDeclNGen_542_);
lean_ctor_set(v_reuseFailAlloc_554_, 4, v_traceState_543_);
lean_ctor_set(v_reuseFailAlloc_554_, 5, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_554_, 6, v_messages_544_);
lean_ctor_set(v_reuseFailAlloc_554_, 7, v_infoState_545_);
lean_ctor_set(v_reuseFailAlloc_554_, 8, v_snapshotTasks_546_);
v___x_552_ = v_reuseFailAlloc_554_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_553_; 
v___x_553_ = lean_st_ref_put(v___x_360_, v___x_552_);
lean_inc(v___x_360_);
v___y_506_ = v___x_384_;
v___y_507_ = v___x_360_;
goto v___jp_505_;
}
}
}
else
{
lean_inc(v___x_360_);
v___y_506_ = v___x_384_;
v___y_507_ = v___x_360_;
goto v___jp_505_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___boxed(lean_object* v_env_558_, lean_object* v_mctx_559_, lean_object* v_lctx_560_, lean_object* v_opts_561_, lean_object* v_namingCtx_562_, lean_object* v_x_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_558_, v_mctx_559_, v_lctx_560_, v_opts_561_, v_namingCtx_562_, v_x_563_, v_a_564_, v_a_565_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec_ref(v_namingCtx_562_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope(lean_object* v_00_u03b1_568_, lean_object* v_env_569_, lean_object* v_mctx_570_, lean_object* v_lctx_571_, lean_object* v_opts_572_, lean_object* v_namingCtx_573_, lean_object* v_x_574_, lean_object* v_a_575_, lean_object* v_a_576_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_569_, v_mctx_570_, v_lctx_571_, v_opts_572_, v_namingCtx_573_, v_x_574_, v_a_575_, v_a_576_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___boxed(lean_object* v_00_u03b1_579_, lean_object* v_env_580_, lean_object* v_mctx_581_, lean_object* v_lctx_582_, lean_object* v_opts_583_, lean_object* v_namingCtx_584_, lean_object* v_x_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope(v_00_u03b1_579_, v_env_580_, v_mctx_581_, v_lctx_582_, v_opts_583_, v_namingCtx_584_, v_x_585_, v_a_586_, v_a_587_);
lean_dec(v_a_587_);
lean_dec_ref(v_a_586_);
lean_dec_ref(v_namingCtx_584_);
return v_res_589_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(lean_object* v_stx_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_Syntax_getKind(v_stx_593_);
if (lean_obj_tag(v___x_594_) == 1)
{
lean_object* v_pre_595_; 
v_pre_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_pre_595_);
if (lean_obj_tag(v_pre_595_) == 1)
{
lean_object* v_pre_596_; 
v_pre_596_ = lean_ctor_get(v_pre_595_, 0);
lean_inc(v_pre_596_);
if (lean_obj_tag(v_pre_596_) == 1)
{
lean_object* v_pre_597_; 
v_pre_597_ = lean_ctor_get(v_pre_596_, 0);
lean_inc(v_pre_597_);
if (lean_obj_tag(v_pre_597_) == 1)
{
lean_object* v_pre_598_; 
v_pre_598_ = lean_ctor_get(v_pre_597_, 0);
if (lean_obj_tag(v_pre_598_) == 0)
{
lean_object* v_str_599_; lean_object* v_str_600_; lean_object* v_str_601_; lean_object* v_str_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v_str_599_ = lean_ctor_get(v___x_594_, 1);
lean_inc_ref(v_str_599_);
lean_dec_ref_known(v___x_594_, 2);
v_str_600_ = lean_ctor_get(v_pre_595_, 1);
lean_inc_ref(v_str_600_);
lean_dec_ref_known(v_pre_595_, 2);
v_str_601_ = lean_ctor_get(v_pre_596_, 1);
lean_inc_ref(v_str_601_);
lean_dec_ref_known(v_pre_596_, 2);
v_str_602_ = lean_ctor_get(v_pre_597_, 1);
lean_inc_ref(v_str_602_);
lean_dec_ref_known(v_pre_597_, 2);
v___x_603_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_604_ = lean_string_dec_eq(v_str_602_, v___x_603_);
lean_dec_ref(v_str_602_);
if (v___x_604_ == 0)
{
lean_dec_ref(v_str_601_);
lean_dec_ref(v_str_600_);
lean_dec_ref(v_str_599_);
return v___x_604_;
}
else
{
lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_605_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0));
v___x_606_ = lean_string_dec_eq(v_str_601_, v___x_605_);
lean_dec_ref(v_str_601_);
if (v___x_606_ == 0)
{
lean_dec_ref(v_str_600_);
lean_dec_ref(v_str_599_);
return v___x_606_;
}
else
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_608_ = lean_string_dec_eq(v_str_600_, v___x_607_);
lean_dec_ref(v_str_600_);
if (v___x_608_ == 0)
{
lean_dec_ref(v_str_599_);
return v___x_608_;
}
else
{
lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_609_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__1));
v___x_610_ = lean_string_dec_eq(v_str_599_, v___x_609_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_611_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__2));
v___x_612_ = lean_string_dec_eq(v_str_599_, v___x_611_);
lean_dec_ref(v_str_599_);
return v___x_612_;
}
else
{
lean_dec_ref(v_str_599_);
return v___x_610_;
}
}
}
}
}
else
{
uint8_t v___x_613_; 
lean_dec_ref_known(v_pre_597_, 2);
lean_dec_ref_known(v_pre_596_, 2);
lean_dec_ref_known(v_pre_595_, 2);
lean_dec_ref_known(v___x_594_, 2);
v___x_613_ = 0;
return v___x_613_;
}
}
else
{
uint8_t v___x_614_; 
lean_dec(v_pre_597_);
lean_dec_ref_known(v_pre_596_, 2);
lean_dec_ref_known(v_pre_595_, 2);
lean_dec_ref_known(v___x_594_, 2);
v___x_614_ = 0;
return v___x_614_;
}
}
else
{
uint8_t v___x_615_; 
lean_dec_ref_known(v_pre_595_, 2);
lean_dec(v_pre_596_);
lean_dec_ref_known(v___x_594_, 2);
v___x_615_ = 0;
return v___x_615_;
}
}
else
{
uint8_t v___x_616_; 
lean_dec(v_pre_595_);
lean_dec_ref_known(v___x_594_, 2);
v___x_616_ = 0;
return v___x_616_;
}
}
else
{
uint8_t v___x_617_; 
lean_dec(v___x_594_);
v___x_617_ = 0;
return v___x_617_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___boxed(lean_object* v_stx_618_){
_start:
{
uint8_t v_res_619_; lean_object* v_r_620_; 
v_res_619_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(v_stx_618_);
v_r_620_ = lean_box(v_res_619_);
return v_r_620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx(lean_object* v_x_621_){
_start:
{
if (lean_obj_tag(v_x_621_) == 0)
{
lean_object* v___x_622_; 
v___x_622_ = lean_unsigned_to_nat(0u);
return v___x_622_;
}
else
{
lean_object* v___x_623_; 
v___x_623_ = lean_unsigned_to_nat(1u);
return v___x_623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx___boxed(lean_object* v_x_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx(v_x_624_);
lean_dec(v_x_624_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(lean_object* v_t_626_, lean_object* v_k_627_){
_start:
{
if (lean_obj_tag(v_t_626_) == 0)
{
lean_object* v_tacticSeq_628_; lean_object* v_insertPos_629_; lean_object* v___x_630_; 
v_tacticSeq_628_ = lean_ctor_get(v_t_626_, 0);
lean_inc(v_tacticSeq_628_);
v_insertPos_629_ = lean_ctor_get(v_t_626_, 1);
lean_inc(v_insertPos_629_);
lean_dec_ref_known(v_t_626_, 2);
v___x_630_ = lean_apply_2(v_k_627_, v_tacticSeq_628_, v_insertPos_629_);
return v___x_630_;
}
else
{
return v_k_627_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim(lean_object* v_motive_631_, lean_object* v_ctorIdx_632_, lean_object* v_t_633_, lean_object* v_h_634_, lean_object* v_k_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_633_, v_k_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___boxed(lean_object* v_motive_637_, lean_object* v_ctorIdx_638_, lean_object* v_t_639_, lean_object* v_h_640_, lean_object* v_k_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim(v_motive_637_, v_ctorIdx_638_, v_t_639_, v_h_640_, v_k_641_);
lean_dec(v_ctorIdx_638_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_unsolvedGoal_elim___redArg(lean_object* v_t_643_, lean_object* v_unsolvedGoal_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_643_, v_unsolvedGoal_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_unsolvedGoal_elim(lean_object* v_motive_646_, lean_object* v_t_647_, lean_object* v_h_648_, lean_object* v_unsolvedGoal_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_647_, v_unsolvedGoal_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_sorryTactic_elim___redArg(lean_object* v_t_651_, lean_object* v_sorryTactic_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_651_, v_sorryTactic_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_sorryTactic_elim(lean_object* v_motive_654_, lean_object* v_t_655_, lean_object* v_h_656_, lean_object* v_sorryTactic_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_655_, v_sorryTactic_657_);
return v___x_658_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed__const__1(void){
_start:
{
uint32_t v___x_662_; lean_object* v___x_663_; 
v___x_662_ = 32;
v___x_663_ = lean_box_uint32(v___x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(lean_object* v_tacticSeq_664_, lean_object* v_fileMap_665_){
_start:
{
uint8_t v___x_666_; lean_object* v___x_667_; 
v___x_666_ = 0;
v___x_667_ = l_Lean_Syntax_getPos_x3f(v_tacticSeq_664_, v___x_666_);
if (lean_obj_tag(v___x_667_) == 1)
{
lean_object* v_val_668_; lean_object* v___x_669_; 
v_val_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_val_668_);
lean_dec_ref_known(v___x_667_, 1);
v___x_669_ = l_Lean_Syntax_getTailPos_x3f(v_tacticSeq_664_, v___x_666_);
if (lean_obj_tag(v___x_669_) == 1)
{
lean_object* v_val_670_; lean_object* v_startPos_671_; lean_object* v_line_672_; lean_object* v_column_673_; lean_object* v_endPos_674_; lean_object* v_line_675_; uint8_t v___x_676_; 
v_val_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_val_670_);
lean_dec_ref_known(v___x_669_, 1);
lean_inc_ref(v_fileMap_665_);
v_startPos_671_ = l_Lean_FileMap_toPosition(v_fileMap_665_, v_val_668_);
lean_dec(v_val_668_);
v_line_672_ = lean_ctor_get(v_startPos_671_, 0);
lean_inc(v_line_672_);
v_column_673_ = lean_ctor_get(v_startPos_671_, 1);
lean_inc(v_column_673_);
lean_dec_ref(v_startPos_671_);
v_endPos_674_ = l_Lean_FileMap_toPosition(v_fileMap_665_, v_val_670_);
lean_dec(v_val_670_);
v_line_675_ = lean_ctor_get(v_endPos_674_, 0);
lean_inc(v_line_675_);
lean_dec_ref(v_endPos_674_);
v___x_676_ = lean_nat_dec_eq(v_line_672_, v_line_675_);
lean_dec(v_line_675_);
lean_dec(v_line_672_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_677_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__0));
v___x_678_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed__const__1;
v___x_679_ = l_List_replicateTR___redArg(v_column_673_, v___x_678_);
v___x_680_ = lean_string_mk(v___x_679_);
v___x_681_ = lean_string_append(v___x_677_, v___x_680_);
lean_dec_ref(v___x_680_);
return v___x_681_;
}
else
{
lean_object* v___x_682_; 
lean_dec(v_column_673_);
v___x_682_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__1));
return v___x_682_;
}
}
else
{
lean_object* v___x_683_; 
lean_dec(v___x_669_);
lean_dec(v_val_668_);
lean_dec_ref(v_fileMap_665_);
v___x_683_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__2));
return v___x_683_;
}
}
else
{
lean_object* v___x_684_; 
lean_dec(v___x_667_);
lean_dec_ref(v_fileMap_665_);
v___x_684_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__2));
return v___x_684_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed(lean_object* v_tacticSeq_685_, lean_object* v_fileMap_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(v_tacticSeq_685_, v_fileMap_686_);
lean_dec(v_tacticSeq_685_);
return v_res_687_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_690_ = lean_string_utf8_byte_size(v___x_689_);
return v___x_690_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_691_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1);
v___x_692_ = lean_unsigned_to_nat(0u);
v___x_693_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_694_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
lean_ctor_set(v___x_694_, 1, v___x_692_);
lean_ctor_set(v___x_694_, 2, v___x_691_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx(lean_object* v_p_695_){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_696_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_697_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2);
lean_inc(v_p_695_);
v___x_698_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set(v___x_698_, 1, v_p_695_);
lean_ctor_set(v___x_698_, 2, v___x_697_);
lean_ctor_set(v___x_698_, 3, v_p_695_);
v___x_699_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
lean_ctor_set(v___x_699_, 1, v___x_696_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(lean_object* v_range_700_){
_start:
{
lean_object* v_start_701_; lean_object* v_stop_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_712_; 
v_start_701_ = lean_ctor_get(v_range_700_, 0);
v_stop_702_ = lean_ctor_get(v_range_700_, 1);
v_isSharedCheck_712_ = !lean_is_exclusive(v_range_700_);
if (v_isSharedCheck_712_ == 0)
{
v___x_704_ = v_range_700_;
v_isShared_705_ = v_isSharedCheck_712_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_stop_702_);
lean_inc(v_start_701_);
lean_dec(v_range_700_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_712_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_706_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_707_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2);
v___x_708_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
lean_ctor_set(v___x_708_, 1, v_start_701_);
lean_ctor_set(v___x_708_, 2, v___x_707_);
lean_ctor_set(v___x_708_, 3, v_stop_702_);
if (v_isShared_705_ == 0)
{
lean_ctor_set_tag(v___x_704_, 2);
lean_ctor_set(v___x_704_, 1, v___x_706_);
lean_ctor_set(v___x_704_, 0, v___x_708_);
v___x_710_ = v___x_704_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_708_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v___x_706_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(lean_object* v_mc_x3f_713_, lean_object* v_nc_x3f_714_, lean_object* v_msg_715_, lean_object* v_acc_716_){
_start:
{
switch(lean_obj_tag(v_msg_715_))
{
case 3:
{
lean_object* v_a_717_; lean_object* v_a_718_; lean_object* v___x_719_; 
lean_dec(v_mc_x3f_713_);
v_a_717_ = lean_ctor_get(v_msg_715_, 0);
v_a_718_ = lean_ctor_get(v_msg_715_, 1);
lean_inc_ref(v_a_717_);
v___x_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_719_, 0, v_a_717_);
v_mc_x3f_713_ = v___x_719_;
v_msg_715_ = v_a_718_;
goto _start;
}
case 4:
{
lean_object* v_a_721_; lean_object* v_a_722_; lean_object* v___x_723_; 
lean_dec(v_nc_x3f_714_);
v_a_721_ = lean_ctor_get(v_msg_715_, 0);
v_a_722_ = lean_ctor_get(v_msg_715_, 1);
lean_inc_ref(v_a_721_);
v___x_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_723_, 0, v_a_721_);
v_nc_x3f_714_ = v___x_723_;
v_msg_715_ = v_a_722_;
goto _start;
}
case 5:
{
lean_object* v_a_725_; 
v_a_725_ = lean_ctor_get(v_msg_715_, 1);
v_msg_715_ = v_a_725_;
goto _start;
}
case 6:
{
lean_object* v_a_727_; 
v_a_727_ = lean_ctor_get(v_msg_715_, 0);
v_msg_715_ = v_a_727_;
goto _start;
}
case 8:
{
lean_object* v_a_729_; 
v_a_729_ = lean_ctor_get(v_msg_715_, 1);
v_msg_715_ = v_a_729_;
goto _start;
}
case 7:
{
lean_object* v_a_731_; lean_object* v_a_732_; lean_object* v___x_733_; 
v_a_731_ = lean_ctor_get(v_msg_715_, 0);
v_a_732_ = lean_ctor_get(v_msg_715_, 1);
lean_inc(v_nc_x3f_714_);
lean_inc(v_mc_x3f_713_);
v___x_733_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_713_, v_nc_x3f_714_, v_a_731_, v_acc_716_);
v_msg_715_ = v_a_732_;
v_acc_716_ = v___x_733_;
goto _start;
}
case 2:
{
lean_object* v_a_735_; 
v_a_735_ = lean_ctor_get(v_msg_715_, 1);
v_msg_715_ = v_a_735_;
goto _start;
}
case 9:
{
lean_object* v_msg_737_; lean_object* v_children_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v_msg_737_ = lean_ctor_get(v_msg_715_, 1);
v_children_738_ = lean_ctor_get(v_msg_715_, 2);
lean_inc(v_nc_x3f_714_);
lean_inc(v_mc_x3f_713_);
v___x_739_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_713_, v_nc_x3f_714_, v_msg_737_, v_acc_716_);
v___x_740_ = lean_unsigned_to_nat(0u);
v___x_741_ = lean_array_get_size(v_children_738_);
v___x_742_ = lean_nat_dec_lt(v___x_740_, v___x_741_);
if (v___x_742_ == 0)
{
lean_dec(v_nc_x3f_714_);
lean_dec(v_mc_x3f_713_);
return v___x_739_;
}
else
{
uint8_t v___x_743_; 
v___x_743_ = lean_nat_dec_le(v___x_741_, v___x_741_);
if (v___x_743_ == 0)
{
if (v___x_742_ == 0)
{
lean_dec(v_nc_x3f_714_);
lean_dec(v_mc_x3f_713_);
return v___x_739_;
}
else
{
size_t v___x_744_; size_t v___x_745_; lean_object* v___x_746_; 
v___x_744_ = ((size_t)0ULL);
v___x_745_ = lean_usize_of_nat(v___x_741_);
v___x_746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_713_, v_nc_x3f_714_, v_children_738_, v___x_744_, v___x_745_, v___x_739_);
return v___x_746_;
}
}
else
{
size_t v___x_747_; size_t v___x_748_; lean_object* v___x_749_; 
v___x_747_ = ((size_t)0ULL);
v___x_748_ = lean_usize_of_nat(v___x_741_);
v___x_749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_713_, v_nc_x3f_714_, v_children_738_, v___x_747_, v___x_748_, v___x_739_);
return v___x_749_;
}
}
}
case 1:
{
if (lean_obj_tag(v_mc_x3f_713_) == 1)
{
if (lean_obj_tag(v_nc_x3f_714_) == 1)
{
lean_object* v_a_750_; lean_object* v_val_751_; lean_object* v_val_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v_a_750_ = lean_ctor_get(v_msg_715_, 0);
v_val_751_ = lean_ctor_get(v_mc_x3f_713_, 0);
lean_inc(v_val_751_);
lean_dec_ref_known(v_mc_x3f_713_, 1);
v_val_752_ = lean_ctor_get(v_nc_x3f_714_, 0);
lean_inc(v_val_752_);
lean_dec_ref_known(v_nc_x3f_714_, 1);
lean_inc(v_a_750_);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v_val_752_);
lean_ctor_set(v___x_753_, 1, v_a_750_);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v_val_751_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___x_755_ = lean_array_push(v_acc_716_, v___x_754_);
return v___x_755_;
}
else
{
lean_dec_ref_known(v_mc_x3f_713_, 1);
lean_dec(v_nc_x3f_714_);
return v_acc_716_;
}
}
else
{
lean_dec(v_nc_x3f_714_);
lean_dec(v_mc_x3f_713_);
return v_acc_716_;
}
}
default: 
{
lean_dec(v_nc_x3f_714_);
lean_dec(v_mc_x3f_713_);
return v_acc_716_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(lean_object* v_mc_x3f_756_, lean_object* v_nc_x3f_757_, lean_object* v_as_758_, size_t v_i_759_, size_t v_stop_760_, lean_object* v_b_761_){
_start:
{
uint8_t v___x_762_; 
v___x_762_ = lean_usize_dec_eq(v_i_759_, v_stop_760_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_764_; size_t v___x_765_; size_t v___x_766_; 
v___x_763_ = lean_array_uget_borrowed(v_as_758_, v_i_759_);
lean_inc(v_nc_x3f_757_);
lean_inc(v_mc_x3f_756_);
v___x_764_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_756_, v_nc_x3f_757_, v___x_763_, v_b_761_);
v___x_765_ = ((size_t)1ULL);
v___x_766_ = lean_usize_add(v_i_759_, v___x_765_);
v_i_759_ = v___x_766_;
v_b_761_ = v___x_764_;
goto _start;
}
else
{
lean_dec(v_nc_x3f_757_);
lean_dec(v_mc_x3f_756_);
return v_b_761_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0___boxed(lean_object* v_mc_x3f_768_, lean_object* v_nc_x3f_769_, lean_object* v_as_770_, lean_object* v_i_771_, lean_object* v_stop_772_, lean_object* v_b_773_){
_start:
{
size_t v_i_boxed_774_; size_t v_stop_boxed_775_; lean_object* v_res_776_; 
v_i_boxed_774_ = lean_unbox_usize(v_i_771_);
lean_dec(v_i_771_);
v_stop_boxed_775_ = lean_unbox_usize(v_stop_772_);
lean_dec(v_stop_772_);
v_res_776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_768_, v_nc_x3f_769_, v_as_770_, v_i_boxed_774_, v_stop_boxed_775_, v_b_773_);
lean_dec_ref(v_as_770_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go___boxed(lean_object* v_mc_x3f_777_, lean_object* v_nc_x3f_778_, lean_object* v_msg_779_, lean_object* v_acc_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_777_, v_nc_x3f_778_, v_msg_779_, v_acc_780_);
lean_dec_ref(v_msg_779_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(lean_object* v_msg_784_){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_785_ = lean_box(0);
v___x_786_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___closed__0));
v___x_787_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v___x_785_, v___x_785_, v_msg_784_, v___x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___boxed(lean_object* v_msg_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_msg_788_);
lean_dec_ref(v_msg_788_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f(lean_object* v_range_792_, lean_object* v_stx_793_){
_start:
{
lean_object* v___x_794_; 
lean_inc(v_stx_793_);
v___x_794_ = l_Lean_Syntax_getKind(v_stx_793_);
if (lean_obj_tag(v___x_794_) == 1)
{
lean_object* v_pre_795_; 
v_pre_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_pre_795_);
if (lean_obj_tag(v_pre_795_) == 1)
{
lean_object* v_pre_796_; 
v_pre_796_ = lean_ctor_get(v_pre_795_, 0);
lean_inc(v_pre_796_);
if (lean_obj_tag(v_pre_796_) == 1)
{
lean_object* v_pre_797_; 
v_pre_797_ = lean_ctor_get(v_pre_796_, 0);
lean_inc(v_pre_797_);
if (lean_obj_tag(v_pre_797_) == 1)
{
lean_object* v_pre_798_; 
v_pre_798_ = lean_ctor_get(v_pre_797_, 0);
if (lean_obj_tag(v_pre_798_) == 0)
{
lean_object* v_str_799_; lean_object* v_str_800_; lean_object* v_str_801_; lean_object* v_str_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v_str_799_ = lean_ctor_get(v___x_794_, 1);
lean_inc_ref(v_str_799_);
lean_dec_ref_known(v___x_794_, 2);
v_str_800_ = lean_ctor_get(v_pre_795_, 1);
lean_inc_ref(v_str_800_);
lean_dec_ref_known(v_pre_795_, 2);
v_str_801_ = lean_ctor_get(v_pre_796_, 1);
lean_inc_ref(v_str_801_);
lean_dec_ref_known(v_pre_796_, 2);
v_str_802_ = lean_ctor_get(v_pre_797_, 1);
lean_inc_ref(v_str_802_);
lean_dec_ref_known(v_pre_797_, 2);
v___x_803_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_804_ = lean_string_dec_eq(v_str_802_, v___x_803_);
lean_dec_ref(v_str_802_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; 
lean_dec_ref(v_str_801_);
lean_dec_ref(v_str_800_);
lean_dec_ref(v_str_799_);
lean_dec(v_stx_793_);
lean_dec_ref(v_range_792_);
v___x_805_ = lean_box(0);
return v___x_805_;
}
else
{
lean_object* v___x_806_; uint8_t v___x_807_; 
v___x_806_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0));
v___x_807_ = lean_string_dec_eq(v_str_801_, v___x_806_);
lean_dec_ref(v_str_801_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; 
lean_dec_ref(v_str_800_);
lean_dec_ref(v_str_799_);
lean_dec(v_stx_793_);
lean_dec_ref(v_range_792_);
v___x_808_ = lean_box(0);
return v___x_808_;
}
else
{
lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_809_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_810_ = lean_string_dec_eq(v_str_800_, v___x_809_);
lean_dec_ref(v_str_800_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; 
lean_dec_ref(v_str_799_);
lean_dec(v_stx_793_);
lean_dec_ref(v_range_792_);
v___x_811_ = lean_box(0);
return v___x_811_;
}
else
{
lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_812_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__0));
v___x_813_ = lean_string_dec_eq(v_str_799_, v___x_812_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_814_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__1));
v___x_815_ = lean_string_dec_eq(v_str_799_, v___x_814_);
lean_dec_ref(v_str_799_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; 
lean_dec(v_stx_793_);
lean_dec_ref(v_range_792_);
v___x_816_ = lean_box(0);
return v___x_816_;
}
else
{
lean_object* v___x_817_; lean_object* v_body_818_; lean_object* v___y_820_; lean_object* v___x_823_; 
v___x_817_ = lean_unsigned_to_nat(1u);
v_body_818_ = l_Lean_Syntax_getArg(v_stx_793_, v___x_817_);
v___x_823_ = l_Lean_Syntax_getTailPos_x3f(v_body_818_, v___x_813_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_824_ = lean_unsigned_to_nat(2u);
v___x_825_ = l_Lean_Syntax_getArg(v_stx_793_, v___x_824_);
lean_dec(v_stx_793_);
v___x_826_ = l_Lean_Syntax_getPos_x3f(v___x_825_, v___x_813_);
lean_dec(v___x_825_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_stop_827_; 
v_stop_827_ = lean_ctor_get(v_range_792_, 1);
lean_inc(v_stop_827_);
lean_dec_ref(v_range_792_);
v___y_820_ = v_stop_827_;
goto v___jp_819_;
}
else
{
lean_object* v_val_828_; 
lean_dec_ref(v_range_792_);
v_val_828_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_val_828_);
lean_dec_ref_known(v___x_826_, 1);
v___y_820_ = v_val_828_;
goto v___jp_819_;
}
}
else
{
lean_object* v_val_829_; 
lean_dec(v_stx_793_);
lean_dec_ref(v_range_792_);
v_val_829_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_val_829_);
lean_dec_ref_known(v___x_823_, 1);
v___y_820_ = v_val_829_;
goto v___jp_819_;
}
v___jp_819_:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v_body_818_);
lean_ctor_set(v___x_821_, 1, v___y_820_);
v___x_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
return v___x_822_;
}
}
}
else
{
lean_object* v___x_830_; lean_object* v_body_831_; lean_object* v___y_833_; uint8_t v___x_836_; lean_object* v___x_837_; 
lean_dec_ref(v_str_799_);
v___x_830_ = lean_unsigned_to_nat(0u);
v_body_831_ = l_Lean_Syntax_getArg(v_stx_793_, v___x_830_);
lean_dec(v_stx_793_);
v___x_836_ = 0;
v___x_837_ = l_Lean_Syntax_getTailPos_x3f(v_body_831_, v___x_836_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_stop_838_; 
v_stop_838_ = lean_ctor_get(v_range_792_, 1);
lean_inc(v_stop_838_);
lean_dec_ref(v_range_792_);
v___y_833_ = v_stop_838_;
goto v___jp_832_;
}
else
{
lean_object* v_val_839_; 
lean_dec_ref(v_range_792_);
v_val_839_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_val_839_);
lean_dec_ref_known(v___x_837_, 1);
v___y_833_ = v_val_839_;
goto v___jp_832_;
}
v___jp_832_:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v_body_831_);
lean_ctor_set(v___x_834_, 1, v___y_833_);
v___x_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
return v___x_835_;
}
}
}
}
}
}
else
{
lean_object* v___x_840_; 
lean_dec_ref_known(v_pre_797_, 2);
lean_dec_ref_known(v_pre_796_, 2);
lean_dec_ref_known(v_pre_795_, 2);
lean_dec_ref_known(v___x_794_, 2);
lean_dec(v_stx_793_);
lean_dec_ref(v_range_792_);
v___x_840_ = lean_box(0);
return v___x_840_;
}
}
else
{
lean_object* v___x_841_; 
lean_dec(v_pre_797_);
lean_dec_ref_known(v_pre_796_, 2);
lean_dec_ref_known(v_pre_795_, 2);
lean_dec_ref_known(v___x_794_, 2);
lean_dec(v_stx_793_);
lean_dec_ref(v_range_792_);
v___x_841_ = lean_box(0);
return v___x_841_;
}
}
else
{
lean_object* v___x_842_; 
lean_dec_ref_known(v_pre_795_, 2);
lean_dec(v_pre_796_);
lean_dec_ref_known(v___x_794_, 2);
lean_dec(v_stx_793_);
lean_dec_ref(v_range_792_);
v___x_842_ = lean_box(0);
return v___x_842_;
}
}
else
{
lean_object* v___x_843_; 
lean_dec_ref_known(v___x_794_, 2);
lean_dec(v_pre_795_);
lean_dec(v_stx_793_);
lean_dec_ref(v_range_792_);
v___x_843_ = lean_box(0);
return v___x_843_;
}
}
else
{
lean_object* v___x_844_; 
lean_dec(v___x_794_);
lean_dec(v_stx_793_);
lean_dec_ref(v_range_792_);
v___x_844_ = lean_box(0);
return v___x_844_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(lean_object* v_range_848_, lean_object* v_stx_849_){
_start:
{
lean_object* v___x_850_; 
lean_inc(v_stx_849_);
lean_inc_ref(v_range_848_);
v___x_850_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f(v_range_848_, v_stx_849_);
if (lean_obj_tag(v___x_850_) == 1)
{
lean_dec(v_stx_849_);
lean_dec_ref(v_range_848_);
return v___x_850_;
}
else
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; size_t v_sz_854_; size_t v___x_855_; lean_object* v___x_856_; lean_object* v_fst_857_; 
lean_dec(v___x_850_);
v___x_851_ = l_Lean_Syntax_getArgs(v_stx_849_);
lean_dec(v_stx_849_);
v___x_852_ = lean_box(0);
v___x_853_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v_sz_854_ = lean_array_size(v___x_851_);
v___x_855_ = ((size_t)0ULL);
v___x_856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(v_range_848_, v___x_851_, v_sz_854_, v___x_855_, v___x_853_);
lean_dec_ref(v___x_851_);
v_fst_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_fst_857_);
lean_dec_ref(v___x_856_);
if (lean_obj_tag(v_fst_857_) == 0)
{
return v___x_852_;
}
else
{
lean_object* v_val_858_; 
v_val_858_ = lean_ctor_get(v_fst_857_, 0);
lean_inc(v_val_858_);
lean_dec_ref_known(v_fst_857_, 1);
return v_val_858_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(lean_object* v_range_859_, lean_object* v_as_860_, size_t v_sz_861_, size_t v_i_862_, lean_object* v_b_863_){
_start:
{
uint8_t v___x_864_; 
v___x_864_ = lean_usize_dec_lt(v_i_862_, v_sz_861_);
if (v___x_864_ == 0)
{
lean_dec_ref(v_range_859_);
lean_inc_ref(v_b_863_);
return v_b_863_;
}
else
{
lean_object* v___x_865_; lean_object* v_a_866_; lean_object* v___x_867_; 
v___x_865_ = lean_box(0);
v_a_866_ = lean_array_uget_borrowed(v_as_860_, v_i_862_);
lean_inc(v_a_866_);
lean_inc_ref(v_range_859_);
v___x_867_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(v_range_859_, v_a_866_);
if (lean_obj_tag(v___x_867_) == 1)
{
lean_object* v___x_868_; lean_object* v___x_869_; 
lean_dec_ref(v_range_859_);
v___x_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
v___x_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
lean_ctor_set(v___x_869_, 1, v___x_865_);
return v___x_869_;
}
else
{
lean_object* v___x_870_; size_t v___x_871_; size_t v___x_872_; 
lean_dec(v___x_867_);
v___x_870_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v___x_871_ = ((size_t)1ULL);
v___x_872_ = lean_usize_add(v_i_862_, v___x_871_);
v_i_862_ = v___x_872_;
v_b_863_ = v___x_870_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___boxed(lean_object* v_range_874_, lean_object* v_as_875_, lean_object* v_sz_876_, lean_object* v_i_877_, lean_object* v_b_878_){
_start:
{
size_t v_sz_boxed_879_; size_t v_i_boxed_880_; lean_object* v_res_881_; 
v_sz_boxed_879_ = lean_unbox_usize(v_sz_876_);
lean_dec(v_sz_876_);
v_i_boxed_880_ = lean_unbox_usize(v_i_877_);
lean_dec(v_i_877_);
v_res_881_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(v_range_874_, v_as_875_, v_sz_boxed_879_, v_i_boxed_880_, v_b_878_);
lean_dec_ref(v_b_878_);
lean_dec_ref(v_as_875_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(lean_object* v_range_882_, lean_object* v_stx_883_){
_start:
{
uint8_t v___x_884_; lean_object* v___x_885_; 
v___x_884_ = 0;
v___x_885_ = l_Lean_Syntax_getRange_x3f(v_stx_883_, v___x_884_);
if (lean_obj_tag(v___x_885_) == 1)
{
lean_object* v_val_886_; uint8_t v___x_887_; 
v_val_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_val_886_);
lean_dec_ref_known(v___x_885_, 1);
v___x_887_ = l_Lean_Syntax_Range_includes(v_val_886_, v_range_882_, v___x_884_, v___x_884_);
lean_dec(v_val_886_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; 
lean_dec(v_stx_883_);
lean_dec_ref(v_range_882_);
v___x_888_ = lean_box(0);
return v___x_888_;
}
else
{
lean_object* v___x_889_; lean_object* v___x_890_; size_t v_sz_891_; size_t v___x_892_; lean_object* v___x_893_; lean_object* v_fst_894_; 
v___x_889_ = l_Lean_Syntax_getArgs(v_stx_883_);
v___x_890_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v_sz_891_ = lean_array_size(v___x_889_);
v___x_892_ = ((size_t)0ULL);
lean_inc_ref(v_range_882_);
v___x_893_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(v_range_882_, v___x_889_, v_sz_891_, v___x_892_, v___x_890_);
lean_dec_ref(v___x_889_);
v_fst_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_fst_894_);
lean_dec_ref(v___x_893_);
if (lean_obj_tag(v_fst_894_) == 0)
{
lean_object* v___x_895_; 
v___x_895_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(v_range_882_, v_stx_883_);
return v___x_895_;
}
else
{
lean_object* v_val_896_; 
lean_dec(v_stx_883_);
lean_dec_ref(v_range_882_);
v_val_896_ = lean_ctor_get(v_fst_894_, 0);
lean_inc(v_val_896_);
lean_dec_ref_known(v_fst_894_, 1);
return v_val_896_;
}
}
}
else
{
lean_object* v___x_897_; 
lean_dec(v___x_885_);
lean_dec(v_stx_883_);
lean_dec_ref(v_range_882_);
v___x_897_ = lean_box(0);
return v___x_897_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(lean_object* v_range_898_, lean_object* v_as_899_, size_t v_sz_900_, size_t v_i_901_, lean_object* v_b_902_){
_start:
{
uint8_t v___x_903_; 
v___x_903_ = lean_usize_dec_lt(v_i_901_, v_sz_900_);
if (v___x_903_ == 0)
{
lean_dec_ref(v_range_898_);
lean_inc_ref(v_b_902_);
return v_b_902_;
}
else
{
lean_object* v___x_904_; lean_object* v_a_905_; lean_object* v___x_906_; 
v___x_904_ = lean_box(0);
v_a_905_ = lean_array_uget_borrowed(v_as_899_, v_i_901_);
lean_inc(v_a_905_);
lean_inc_ref(v_range_898_);
v___x_906_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v_range_898_, v_a_905_);
if (lean_obj_tag(v___x_906_) == 1)
{
lean_object* v___x_907_; lean_object* v___x_908_; 
lean_dec_ref(v_range_898_);
v___x_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
v___x_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
lean_ctor_set(v___x_908_, 1, v___x_904_);
return v___x_908_;
}
else
{
lean_object* v___x_909_; size_t v___x_910_; size_t v___x_911_; 
lean_dec(v___x_906_);
v___x_909_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v___x_910_ = ((size_t)1ULL);
v___x_911_ = lean_usize_add(v_i_901_, v___x_910_);
v_i_901_ = v___x_911_;
v_b_902_ = v___x_909_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0___boxed(lean_object* v_range_913_, lean_object* v_as_914_, lean_object* v_sz_915_, lean_object* v_i_916_, lean_object* v_b_917_){
_start:
{
size_t v_sz_boxed_918_; size_t v_i_boxed_919_; lean_object* v_res_920_; 
v_sz_boxed_918_ = lean_unbox_usize(v_sz_915_);
lean_dec(v_sz_915_);
v_i_boxed_919_ = lean_unbox_usize(v_i_916_);
lean_dec(v_i_916_);
v_res_920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(v_range_913_, v_as_914_, v_sz_boxed_918_, v_i_boxed_919_, v_b_917_);
lean_dec_ref(v_b_917_);
lean_dec_ref(v_as_914_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody(lean_object* v_cmd_921_, lean_object* v_range_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v_range_922_, v_cmd_921_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0(lean_object* v_ctx_924_, lean_object* v_info_925_, lean_object* v_acc_926_){
_start:
{
if (lean_obj_tag(v_info_925_) == 0)
{
lean_object* v_i_927_; lean_object* v_toElabInfo_928_; lean_object* v_mctxBefore_929_; lean_object* v_goalsBefore_930_; lean_object* v_stx_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_949_; 
v_i_927_ = lean_ctor_get(v_info_925_, 0);
lean_inc_ref(v_i_927_);
lean_dec_ref_known(v_info_925_, 1);
v_toElabInfo_928_ = lean_ctor_get(v_i_927_, 0);
lean_inc_ref(v_toElabInfo_928_);
v_mctxBefore_929_ = lean_ctor_get(v_i_927_, 1);
lean_inc_ref(v_mctxBefore_929_);
v_goalsBefore_930_ = lean_ctor_get(v_i_927_, 2);
lean_inc(v_goalsBefore_930_);
lean_dec_ref(v_i_927_);
v_stx_931_ = lean_ctor_get(v_toElabInfo_928_, 1);
v_isSharedCheck_949_ = !lean_is_exclusive(v_toElabInfo_928_);
if (v_isSharedCheck_949_ == 0)
{
lean_object* v_unused_950_; 
v_unused_950_ = lean_ctor_get(v_toElabInfo_928_, 0);
lean_dec(v_unused_950_);
v___x_933_ = v_toElabInfo_928_;
v_isShared_934_ = v_isSharedCheck_949_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_stx_931_);
lean_dec(v_toElabInfo_928_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_949_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
uint8_t v___x_935_; 
lean_inc(v_stx_931_);
v___x_935_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(v_stx_931_);
if (v___x_935_ == 0)
{
lean_del_object(v___x_933_);
lean_dec(v_stx_931_);
lean_dec(v_goalsBefore_930_);
lean_dec_ref(v_mctxBefore_929_);
return v_acc_926_;
}
else
{
lean_object* v___x_936_; 
v___x_936_ = l_List_head_x3f___redArg(v_goalsBefore_930_);
lean_dec(v_goalsBefore_930_);
if (lean_obj_tag(v___x_936_) == 1)
{
lean_object* v_toCommandContextInfo_937_; lean_object* v_val_938_; lean_object* v_env_939_; lean_object* v_options_940_; lean_object* v_currNamespace_941_; lean_object* v_openDecls_942_; lean_object* v_namingCtx_944_; 
v_toCommandContextInfo_937_ = lean_ctor_get(v_ctx_924_, 0);
v_val_938_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_val_938_);
lean_dec_ref_known(v___x_936_, 1);
v_env_939_ = lean_ctor_get(v_toCommandContextInfo_937_, 0);
v_options_940_ = lean_ctor_get(v_toCommandContextInfo_937_, 4);
v_currNamespace_941_ = lean_ctor_get(v_toCommandContextInfo_937_, 5);
v_openDecls_942_ = lean_ctor_get(v_toCommandContextInfo_937_, 6);
lean_inc(v_openDecls_942_);
lean_inc(v_currNamespace_941_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v_openDecls_942_);
lean_ctor_set(v___x_933_, 0, v_currNamespace_941_);
v_namingCtx_944_ = v___x_933_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_currNamespace_941_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_openDecls_942_);
v_namingCtx_944_ = v_reuseFailAlloc_948_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_945_ = lean_box(1);
lean_inc_ref(v_options_940_);
lean_inc_ref(v_env_939_);
v___x_946_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v_stx_931_);
lean_ctor_set(v___x_946_, 2, v_env_939_);
lean_ctor_set(v___x_946_, 3, v_mctxBefore_929_);
lean_ctor_set(v___x_946_, 4, v_options_940_);
lean_ctor_set(v___x_946_, 5, v_namingCtx_944_);
lean_ctor_set(v___x_946_, 6, v_val_938_);
v___x_947_ = lean_array_push(v_acc_926_, v___x_946_);
return v___x_947_;
}
}
else
{
lean_dec(v___x_936_);
lean_del_object(v___x_933_);
lean_dec(v_stx_931_);
lean_dec_ref(v_mctxBefore_929_);
return v_acc_926_;
}
}
}
}
else
{
lean_dec_ref(v_info_925_);
return v_acc_926_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0___boxed(lean_object* v_ctx_951_, lean_object* v_info_952_, lean_object* v_acc_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0(v_ctx_951_, v_info_952_, v_acc_953_);
lean_dec_ref(v_ctx_951_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2___redArg(lean_object* v_m_955_, lean_object* v_query_956_, lean_object* v_x_957_, lean_object* v_x_958_, lean_object* v_x_959_){
_start:
{
lean_object* v_zero_960_; uint8_t v_isZero_961_; 
v_zero_960_ = lean_unsigned_to_nat(0u);
v_isZero_961_ = lean_nat_dec_eq(v_x_958_, v_zero_960_);
if (v_isZero_961_ == 1)
{
lean_dec(v_x_959_);
lean_dec(v_x_958_);
if (lean_obj_tag(v_x_957_) == 0)
{
lean_object* v___x_962_; 
v___x_962_ = lean_box(2);
return v___x_962_;
}
else
{
lean_object* v_val_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
v_val_963_ = lean_ctor_get(v_x_957_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v_x_957_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v_x_957_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_val_963_);
lean_dec(v_x_957_);
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
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_val_963_);
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
else
{
lean_object* v_keyArray_971_; lean_object* v_valueArray_972_; lean_object* v___x_973_; uint8_t v_isSome_974_; 
v_keyArray_971_ = lean_ctor_get(v_m_955_, 1);
v_valueArray_972_ = lean_ctor_get(v_m_955_, 2);
v___x_973_ = lean_array_fget_borrowed(v_keyArray_971_, v_x_959_);
v_isSome_974_ = lean_noption_is_some(v___x_973_);
if (v_isSome_974_ == 0)
{
lean_dec(v_x_958_);
if (lean_obj_tag(v_x_957_) == 0)
{
lean_object* v___x_975_; 
v___x_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_975_, 0, v_x_959_);
return v___x_975_;
}
else
{
lean_object* v_val_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec(v_x_959_);
v_val_976_ = lean_ctor_get(v_x_957_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v_x_957_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v_x_957_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_val_976_);
lean_dec(v_x_957_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_val_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
else
{
lean_object* v_one_984_; lean_object* v_n_985_; lean_object* v___y_987_; 
v_one_984_ = lean_unsigned_to_nat(1u);
v_n_985_ = lean_nat_sub(v_x_958_, v_one_984_);
lean_dec(v_x_958_);
if (v_isSome_974_ == 0)
{
goto v___jp_993_;
}
else
{
lean_object* v___x_995_; uint8_t v_isSome_996_; 
v___x_995_ = lean_array_fget_borrowed(v_valueArray_972_, v_x_959_);
v_isSome_996_ = lean_noption_is_some(v___x_995_);
if (v_isSome_996_ == 0)
{
goto v___jp_993_;
}
else
{
lean_object* v_val_997_; lean_object* v_fst_998_; lean_object* v_snd_999_; lean_object* v_fst_1000_; lean_object* v_snd_1001_; lean_object* v_val_1002_; uint8_t v___y_1004_; uint8_t v___x_1011_; 
lean_inc(v___x_973_);
v_val_997_ = lean_noption_get(v___x_973_);
v_fst_998_ = lean_ctor_get(v_val_997_, 0);
lean_inc(v_fst_998_);
v_snd_999_ = lean_ctor_get(v_val_997_, 1);
lean_inc(v_snd_999_);
v_fst_1000_ = lean_ctor_get(v_query_956_, 0);
v_snd_1001_ = lean_ctor_get(v_query_956_, 1);
lean_inc(v___x_995_);
v_val_1002_ = lean_noption_get(v___x_995_);
v___x_1011_ = l_Lean_Syntax_instBEqRange_beq(v_fst_998_, v_fst_1000_);
lean_dec(v_fst_998_);
if (v___x_1011_ == 0)
{
lean_dec(v_snd_999_);
v___y_1004_ = v___x_1011_;
goto v___jp_1003_;
}
else
{
uint8_t v___x_1012_; 
v___x_1012_ = l_Lean_instBEqMVarId_beq(v_snd_999_, v_snd_1001_);
lean_dec(v_snd_999_);
v___y_1004_ = v___x_1012_;
goto v___jp_1003_;
}
v___jp_1003_:
{
if (v___y_1004_ == 0)
{
lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
lean_dec(v_val_1002_);
lean_dec(v_val_997_);
v___x_1005_ = lean_array_get_size(v_keyArray_971_);
v___x_1006_ = lean_nat_add(v_x_959_, v_one_984_);
lean_dec(v_x_959_);
v___x_1007_ = lean_nat_dec_lt(v___x_1006_, v___x_1005_);
if (v___x_1007_ == 0)
{
lean_dec(v___x_1006_);
v_x_958_ = v_n_985_;
v_x_959_ = v_zero_960_;
goto _start;
}
else
{
v_x_958_ = v_n_985_;
v_x_959_ = v___x_1006_;
goto _start;
}
}
else
{
lean_object* v___x_1010_; 
lean_dec(v_n_985_);
lean_dec(v_x_957_);
v___x_1010_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1010_, 0, v_x_959_);
lean_ctor_set(v___x_1010_, 1, v_val_997_);
lean_ctor_set(v___x_1010_, 2, v_val_1002_);
return v___x_1010_;
}
}
}
}
v___jp_986_:
{
lean_object* v___x_988_; lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_988_ = lean_array_get_size(v_keyArray_971_);
v___x_989_ = lean_nat_add(v_x_959_, v_one_984_);
lean_dec(v_x_959_);
v___x_990_ = lean_nat_dec_lt(v___x_989_, v___x_988_);
if (v___x_990_ == 0)
{
lean_dec(v___x_989_);
v_x_957_ = v___y_987_;
v_x_958_ = v_n_985_;
v_x_959_ = v_zero_960_;
goto _start;
}
else
{
v_x_957_ = v___y_987_;
v_x_958_ = v_n_985_;
v_x_959_ = v___x_989_;
goto _start;
}
}
v___jp_993_:
{
if (lean_obj_tag(v_x_957_) == 0)
{
lean_object* v___x_994_; 
lean_inc(v_x_959_);
v___x_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_994_, 0, v_x_959_);
v___y_987_ = v___x_994_;
goto v___jp_986_;
}
else
{
v___y_987_ = v_x_957_;
goto v___jp_986_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2___redArg___boxed(lean_object* v_m_1013_, lean_object* v_query_1014_, lean_object* v_x_1015_, lean_object* v_x_1016_, lean_object* v_x_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2___redArg(v_m_1013_, v_query_1014_, v_x_1015_, v_x_1016_, v_x_1017_);
lean_dec_ref(v_query_1014_);
lean_dec_ref(v_m_1013_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(lean_object* v_m_1019_, lean_object* v_query_1020_){
_start:
{
lean_object* v_keyArray_1021_; lean_object* v_fst_1022_; lean_object* v_snd_1023_; lean_object* v___x_1024_; uint64_t v___x_1025_; uint64_t v___x_1026_; uint64_t v___x_1027_; uint64_t v___x_1028_; uint64_t v___x_1029_; uint64_t v_fold_1030_; uint64_t v___x_1031_; uint64_t v___x_1032_; uint64_t v___x_1033_; size_t v___x_1034_; size_t v___x_1035_; size_t v___x_1036_; size_t v___x_1037_; size_t v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v_keyArray_1021_ = lean_ctor_get(v_m_1019_, 1);
v_fst_1022_ = lean_ctor_get(v_query_1020_, 0);
v_snd_1023_ = lean_ctor_get(v_query_1020_, 1);
v___x_1024_ = lean_array_get_size(v_keyArray_1021_);
v___x_1025_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1022_);
v___x_1026_ = l_Lean_instHashableMVarId_hash(v_snd_1023_);
v___x_1027_ = lean_uint64_mix_hash(v___x_1025_, v___x_1026_);
v___x_1028_ = 32ULL;
v___x_1029_ = lean_uint64_shift_right(v___x_1027_, v___x_1028_);
v_fold_1030_ = lean_uint64_xor(v___x_1027_, v___x_1029_);
v___x_1031_ = 16ULL;
v___x_1032_ = lean_uint64_shift_right(v_fold_1030_, v___x_1031_);
v___x_1033_ = lean_uint64_xor(v_fold_1030_, v___x_1032_);
v___x_1034_ = lean_uint64_to_usize(v___x_1033_);
v___x_1035_ = lean_usize_of_nat(v___x_1024_);
v___x_1036_ = ((size_t)1ULL);
v___x_1037_ = lean_usize_sub(v___x_1035_, v___x_1036_);
v___x_1038_ = lean_usize_land(v___x_1034_, v___x_1037_);
v___x_1039_ = lean_usize_to_nat(v___x_1038_);
v___x_1040_ = lean_box(0);
v___x_1041_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2___redArg(v_m_1019_, v_query_1020_, v___x_1040_, v___x_1024_, v___x_1039_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg___boxed(lean_object* v_m_1042_, lean_object* v_query_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_m_1042_, v_query_1043_);
lean_dec_ref(v_query_1043_);
lean_dec_ref(v_m_1042_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(lean_object* v_m_1045_, lean_object* v_query_1046_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_m_1045_, v_query_1046_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_index_1048_; lean_object* v_key_1049_; lean_object* v_value_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
v_index_1048_ = lean_ctor_get(v___x_1047_, 0);
v_key_1049_ = lean_ctor_get(v___x_1047_, 1);
v_value_1050_ = lean_ctor_get(v___x_1047_, 2);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1047_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_value_1050_);
lean_inc(v_key_1049_);
lean_inc(v_index_1048_);
lean_dec(v___x_1047_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_index_1048_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_key_1049_);
lean_ctor_set(v_reuseFailAlloc_1056_, 2, v_value_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
else
{
lean_object* v___x_1058_; 
lean_dec(v___x_1047_);
v___x_1058_ = lean_box(1);
return v___x_1058_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg___boxed(lean_object* v_m_1059_, lean_object* v_query_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(v_m_1059_, v_query_1060_);
lean_dec_ref(v_query_1060_);
lean_dec_ref(v_m_1059_);
return v_res_1061_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(lean_object* v_m_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(v_m_1062_, v_a_1063_);
if (lean_obj_tag(v___x_1064_) == 0)
{
uint8_t v___x_1065_; 
lean_dec_ref_known(v___x_1064_, 3);
v___x_1065_ = 1;
return v___x_1065_;
}
else
{
uint8_t v___x_1066_; 
v___x_1066_ = 0;
return v___x_1066_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg___boxed(lean_object* v_m_1067_, lean_object* v_a_1068_){
_start:
{
uint8_t v_res_1069_; lean_object* v_r_1070_; 
v_res_1069_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(v_m_1067_, v_a_1068_);
lean_dec_ref(v_a_1068_);
lean_dec_ref(v_m_1067_);
v_r_1070_ = lean_box(v_res_1069_);
return v_r_1070_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__4_spec__5___redArg(lean_object* v_b_1071_, lean_object* v_acc_1072_, lean_object* v_i_1073_){
_start:
{
lean_object* v___y_1075_; lean_object* v_keyArray_1083_; lean_object* v_valueArray_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
v_keyArray_1083_ = lean_ctor_get(v_b_1071_, 1);
v_valueArray_1084_ = lean_ctor_get(v_b_1071_, 2);
v___x_1085_ = lean_array_get_size(v_keyArray_1083_);
v___x_1086_ = lean_nat_dec_lt(v_i_1073_, v___x_1085_);
if (v___x_1086_ == 0)
{
lean_dec(v_i_1073_);
return v_acc_1072_;
}
else
{
lean_object* v___x_1087_; uint8_t v_isSome_1088_; 
v___x_1087_ = lean_array_fget_borrowed(v_keyArray_1083_, v_i_1073_);
v_isSome_1088_ = lean_noption_is_some(v___x_1087_);
if (v_isSome_1088_ == 0)
{
goto v___jp_1079_;
}
else
{
lean_object* v___x_1089_; uint8_t v_isSome_1090_; 
v___x_1089_ = lean_array_fget_borrowed(v_valueArray_1084_, v_i_1073_);
v_isSome_1090_ = lean_noption_is_some(v___x_1089_);
if (v_isSome_1090_ == 0)
{
goto v___jp_1079_;
}
else
{
lean_object* v_val_1091_; lean_object* v_val_1092_; lean_object* v_i_1094_; lean_object* v___x_1099_; 
lean_inc(v___x_1087_);
v_val_1091_ = lean_noption_get(v___x_1087_);
lean_inc(v___x_1089_);
v_val_1092_ = lean_noption_get(v___x_1089_);
v___x_1099_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_acc_1072_, v_val_1091_);
switch(lean_obj_tag(v___x_1099_))
{
case 0:
{
lean_object* v_index_1100_; lean_object* v_size_1101_; lean_object* v___x_1102_; 
v_index_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_index_1100_);
lean_dec_ref_known(v___x_1099_, 3);
v_size_1101_ = lean_ctor_get(v_acc_1072_, 0);
lean_inc(v_size_1101_);
v___x_1102_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1072_, v_size_1101_, v_index_1100_, v_val_1091_, v_val_1092_);
lean_dec(v_index_1100_);
v___y_1075_ = v___x_1102_;
goto v___jp_1074_;
}
case 1:
{
lean_object* v_index_1103_; 
v_index_1103_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_index_1103_);
lean_dec_ref_known(v___x_1099_, 1);
v_i_1094_ = v_index_1103_;
goto v___jp_1093_;
}
default: 
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_unsigned_to_nat(0u);
v___x_1105_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1072_, v___x_1104_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_index_1106_; 
v_index_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_index_1106_);
lean_dec_ref_known(v___x_1105_, 1);
v_i_1094_ = v_index_1106_;
goto v___jp_1093_;
}
else
{
lean_dec(v_val_1092_);
lean_dec(v_val_1091_);
v___y_1075_ = v_acc_1072_;
goto v___jp_1074_;
}
}
}
v___jp_1093_:
{
lean_object* v_size_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v_size_1095_ = lean_ctor_get(v_acc_1072_, 0);
v___x_1096_ = lean_unsigned_to_nat(1u);
v___x_1097_ = lean_nat_add(v_size_1095_, v___x_1096_);
v___x_1098_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1072_, v___x_1097_, v_i_1094_, v_val_1091_, v_val_1092_);
lean_dec(v_i_1094_);
v___y_1075_ = v___x_1098_;
goto v___jp_1074_;
}
}
}
}
v___jp_1074_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = lean_unsigned_to_nat(1u);
v___x_1077_ = lean_nat_add(v_i_1073_, v___x_1076_);
lean_dec(v_i_1073_);
v_acc_1072_ = v___y_1075_;
v_i_1073_ = v___x_1077_;
goto _start;
}
v___jp_1079_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = lean_unsigned_to_nat(1u);
v___x_1081_ = lean_nat_add(v_i_1073_, v___x_1080_);
lean_dec(v_i_1073_);
v_i_1073_ = v___x_1081_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_b_1107_, lean_object* v_acc_1108_, lean_object* v_i_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__4_spec__5___redArg(v_b_1107_, v_acc_1108_, v_i_1109_);
lean_dec_ref(v_b_1107_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__4___redArg(lean_object* v_init_1111_, lean_object* v_b_1112_){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = lean_unsigned_to_nat(0u);
v___x_1114_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__4_spec__5___redArg(v_b_1112_, v_init_1111_, v___x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__4___redArg___boxed(lean_object* v_init_1115_, lean_object* v_b_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__4___redArg(v_init_1115_, v_b_1116_);
lean_dec_ref(v_b_1116_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(lean_object* v_m_1118_){
_start:
{
lean_object* v_keyArray_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v_cellCount_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v_target_1126_; lean_object* v___x_1127_; 
v_keyArray_1119_ = lean_ctor_get(v_m_1118_, 1);
v___x_1120_ = lean_array_get_size(v_keyArray_1119_);
v___x_1121_ = lean_unsigned_to_nat(2u);
v_cellCount_1122_ = lean_nat_mul(v___x_1120_, v___x_1121_);
v___x_1123_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1122_);
v___x_1124_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1122_);
v___x_1125_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1122_);
v_target_1126_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1126_, 0, v___x_1123_);
lean_ctor_set(v_target_1126_, 1, v___x_1124_);
lean_ctor_set(v_target_1126_, 2, v___x_1125_);
v___x_1127_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__4___redArg(v_target_1126_, v_m_1118_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg___boxed(lean_object* v_m_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v_m_1128_);
lean_dec_ref(v_m_1128_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(lean_object* v_fst_1130_, lean_object* v_snd_1131_, lean_object* v___x_1132_, lean_object* v___x_1133_, lean_object* v_as_1134_, size_t v_sz_1135_, size_t v_i_1136_, lean_object* v_b_1137_){
_start:
{
lean_object* v_a_1140_; uint8_t v___x_1144_; 
v___x_1144_ = lean_usize_dec_lt(v_i_1136_, v_sz_1135_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; 
lean_dec_ref(v___x_1133_);
lean_dec(v___x_1132_);
lean_dec(v_snd_1131_);
lean_dec(v_fst_1130_);
v___x_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1145_, 0, v_b_1137_);
return v___x_1145_;
}
else
{
lean_object* v_a_1146_; lean_object* v_snd_1147_; lean_object* v_fst_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1244_; 
v_a_1146_ = lean_array_uget(v_as_1134_, v_i_1136_);
v_snd_1147_ = lean_ctor_get(v_a_1146_, 1);
v_fst_1148_ = lean_ctor_get(v_a_1146_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_a_1146_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1150_ = v_a_1146_;
v_isShared_1151_ = v_isSharedCheck_1244_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_snd_1147_);
lean_inc(v_fst_1148_);
lean_dec(v_a_1146_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1244_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v_fst_1152_; lean_object* v_snd_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1243_; 
v_fst_1152_ = lean_ctor_get(v_snd_1147_, 0);
v_snd_1153_ = lean_ctor_get(v_snd_1147_, 1);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_snd_1147_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1155_ = v_snd_1147_;
v_isShared_1156_ = v_isSharedCheck_1243_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_snd_1153_);
lean_inc(v_fst_1152_);
lean_dec(v_snd_1147_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1243_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v_fst_1157_; lean_object* v_snd_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1242_; 
v_fst_1157_ = lean_ctor_get(v_b_1137_, 0);
v_snd_1158_ = lean_ctor_get(v_b_1137_, 1);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_b_1137_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1160_ = v_b_1137_;
v_isShared_1161_ = v_isSharedCheck_1242_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_snd_1158_);
lean_inc(v_fst_1157_);
lean_dec(v_b_1137_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1242_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___y_1163_; lean_object* v___x_1174_; 
lean_inc(v_snd_1153_);
lean_inc_ref(v___x_1133_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 0, v___x_1133_);
v___x_1174_ = v___x_1155_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1133_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_snd_1153_);
v___x_1174_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1173_;
}
v___jp_1162_:
{
lean_object* v_env_1164_; lean_object* v_mctx_1165_; lean_object* v_opts_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1171_; 
v_env_1164_ = lean_ctor_get(v_fst_1148_, 0);
lean_inc_ref(v_env_1164_);
v_mctx_1165_ = lean_ctor_get(v_fst_1148_, 1);
lean_inc_ref(v_mctx_1165_);
v_opts_1166_ = lean_ctor_get(v_fst_1148_, 3);
lean_inc_ref(v_opts_1166_);
lean_dec(v_fst_1148_);
lean_inc(v_snd_1131_);
lean_inc(v_fst_1130_);
v___x_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1167_, 0, v_fst_1130_);
lean_ctor_set(v___x_1167_, 1, v_snd_1131_);
lean_inc(v___x_1132_);
v___x_1168_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
lean_ctor_set(v___x_1168_, 1, v___x_1132_);
lean_ctor_set(v___x_1168_, 2, v_env_1164_);
lean_ctor_set(v___x_1168_, 3, v_mctx_1165_);
lean_ctor_set(v___x_1168_, 4, v_opts_1166_);
lean_ctor_set(v___x_1168_, 5, v_fst_1152_);
lean_ctor_set(v___x_1168_, 6, v_snd_1153_);
v___x_1169_ = lean_array_push(v_fst_1157_, v___x_1168_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 1, v___y_1163_);
lean_ctor_set(v___x_1160_, 0, v___x_1169_);
v___x_1171_ = v___x_1160_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1169_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v___y_1163_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
v_a_1140_ = v___x_1171_;
goto v___jp_1139_;
}
}
v_reusejp_1173_:
{
uint8_t v___x_1175_; 
v___x_1175_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(v_snd_1158_, v___x_1174_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; lean_object* v___y_1178_; lean_object* v_i_1179_; lean_object* v___y_1185_; lean_object* v___y_1195_; lean_object* v_i_1196_; lean_object* v___x_1211_; 
lean_del_object(v___x_1150_);
v___x_1176_ = lean_box(0);
v___x_1211_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_snd_1158_, v___x_1174_);
switch(lean_obj_tag(v___x_1211_))
{
case 0:
{
lean_dec_ref_known(v___x_1211_, 3);
lean_dec_ref(v___x_1174_);
v___y_1163_ = v_snd_1158_;
goto v___jp_1162_;
}
case 1:
{
lean_object* v_index_1212_; lean_object* v_size_1213_; lean_object* v_keyArray_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; uint8_t v___x_1218_; 
v_index_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_index_1212_);
lean_dec_ref_known(v___x_1211_, 1);
v_size_1213_ = lean_ctor_get(v_snd_1158_, 0);
v_keyArray_1214_ = lean_ctor_get(v_snd_1158_, 1);
v___x_1215_ = lean_unsigned_to_nat(1u);
v___x_1216_ = lean_nat_add(v_size_1213_, v___x_1215_);
v___x_1217_ = lean_array_get_size(v_keyArray_1214_);
v___x_1218_ = lean_nat_dec_lt(v___x_1216_, v___x_1217_);
if (v___x_1218_ == 0)
{
lean_dec(v___x_1216_);
lean_dec(v_index_1212_);
goto v___jp_1201_;
}
else
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1219_ = lean_unsigned_to_nat(4u);
v___x_1220_ = lean_nat_mul(v___x_1216_, v___x_1219_);
v___x_1221_ = lean_unsigned_to_nat(3u);
v___x_1222_ = lean_nat_mul(v___x_1217_, v___x_1221_);
v___x_1223_ = lean_nat_dec_le(v___x_1220_, v___x_1222_);
lean_dec(v___x_1222_);
lean_dec(v___x_1220_);
if (v___x_1223_ == 0)
{
lean_dec(v___x_1216_);
lean_dec(v_index_1212_);
goto v___jp_1201_;
}
else
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_1158_, v___x_1216_, v_index_1212_, v___x_1174_, v___x_1176_);
lean_dec(v_index_1212_);
v___y_1163_ = v___x_1224_;
goto v___jp_1162_;
}
}
}
default: 
{
lean_object* v_size_1225_; lean_object* v_keyArray_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
v_size_1225_ = lean_ctor_get(v_snd_1158_, 0);
v_keyArray_1226_ = lean_ctor_get(v_snd_1158_, 1);
v___x_1227_ = lean_unsigned_to_nat(1u);
v___x_1228_ = lean_nat_add(v_size_1225_, v___x_1227_);
v___x_1229_ = lean_array_get_size(v_keyArray_1226_);
v___x_1230_ = lean_nat_dec_lt(v___x_1228_, v___x_1229_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; 
lean_dec(v___x_1228_);
v___x_1231_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v_snd_1158_);
lean_dec(v_snd_1158_);
v___y_1185_ = v___x_1231_;
goto v___jp_1184_;
}
else
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1232_ = lean_unsigned_to_nat(4u);
v___x_1233_ = lean_nat_mul(v___x_1228_, v___x_1232_);
lean_dec(v___x_1228_);
v___x_1234_ = lean_unsigned_to_nat(3u);
v___x_1235_ = lean_nat_mul(v___x_1229_, v___x_1234_);
v___x_1236_ = lean_nat_dec_le(v___x_1233_, v___x_1235_);
lean_dec(v___x_1235_);
lean_dec(v___x_1233_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v_snd_1158_);
lean_dec(v_snd_1158_);
v___y_1185_ = v___x_1237_;
goto v___jp_1184_;
}
else
{
v___y_1185_ = v_snd_1158_;
goto v___jp_1184_;
}
}
}
}
v___jp_1177_:
{
lean_object* v_size_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v_size_1180_ = lean_ctor_get(v___y_1178_, 0);
v___x_1181_ = lean_unsigned_to_nat(1u);
v___x_1182_ = lean_nat_add(v_size_1180_, v___x_1181_);
v___x_1183_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1178_, v___x_1182_, v_i_1179_, v___x_1174_, v___x_1176_);
lean_dec(v_i_1179_);
v___y_1163_ = v___x_1183_;
goto v___jp_1162_;
}
v___jp_1184_:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v___y_1185_, v___x_1174_);
switch(lean_obj_tag(v___x_1186_))
{
case 0:
{
lean_object* v_index_1187_; lean_object* v_size_1188_; lean_object* v___x_1189_; 
v_index_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_index_1187_);
lean_dec_ref_known(v___x_1186_, 3);
v_size_1188_ = lean_ctor_get(v___y_1185_, 0);
lean_inc(v_size_1188_);
v___x_1189_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1185_, v_size_1188_, v_index_1187_, v___x_1174_, v___x_1176_);
lean_dec(v_index_1187_);
v___y_1163_ = v___x_1189_;
goto v___jp_1162_;
}
case 1:
{
lean_object* v_index_1190_; 
v_index_1190_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_index_1190_);
lean_dec_ref_known(v___x_1186_, 1);
v___y_1178_ = v___y_1185_;
v_i_1179_ = v_index_1190_;
goto v___jp_1177_;
}
default: 
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_unsigned_to_nat(0u);
v___x_1192_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1185_, v___x_1191_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_index_1193_; 
v_index_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_index_1193_);
lean_dec_ref_known(v___x_1192_, 1);
v___y_1178_ = v___y_1185_;
v_i_1179_ = v_index_1193_;
goto v___jp_1177_;
}
else
{
lean_dec_ref(v___x_1174_);
v___y_1163_ = v___y_1185_;
goto v___jp_1162_;
}
}
}
}
v___jp_1194_:
{
lean_object* v_size_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v_size_1197_ = lean_ctor_get(v___y_1195_, 0);
v___x_1198_ = lean_unsigned_to_nat(1u);
v___x_1199_ = lean_nat_add(v_size_1197_, v___x_1198_);
v___x_1200_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1195_, v___x_1199_, v_i_1196_, v___x_1174_, v___x_1176_);
lean_dec(v_i_1196_);
v___y_1163_ = v___x_1200_;
goto v___jp_1162_;
}
v___jp_1201_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v_snd_1158_);
lean_dec(v_snd_1158_);
v___x_1203_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v___x_1202_, v___x_1174_);
switch(lean_obj_tag(v___x_1203_))
{
case 0:
{
lean_object* v_index_1204_; lean_object* v_size_1205_; lean_object* v___x_1206_; 
v_index_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_index_1204_);
lean_dec_ref_known(v___x_1203_, 3);
v_size_1205_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_size_1205_);
v___x_1206_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1202_, v_size_1205_, v_index_1204_, v___x_1174_, v___x_1176_);
lean_dec(v_index_1204_);
v___y_1163_ = v___x_1206_;
goto v___jp_1162_;
}
case 1:
{
lean_object* v_index_1207_; 
v_index_1207_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_index_1207_);
lean_dec_ref_known(v___x_1203_, 1);
v___y_1195_ = v___x_1202_;
v_i_1196_ = v_index_1207_;
goto v___jp_1194_;
}
default: 
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = lean_unsigned_to_nat(0u);
v___x_1209_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1202_, v___x_1208_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_index_1210_; 
v_index_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_index_1210_);
lean_dec_ref_known(v___x_1209_, 1);
v___y_1195_ = v___x_1202_;
v_i_1196_ = v_index_1210_;
goto v___jp_1194_;
}
else
{
lean_dec_ref(v___x_1174_);
v___y_1163_ = v___x_1202_;
goto v___jp_1162_;
}
}
}
}
}
else
{
lean_object* v___x_1239_; 
lean_dec_ref(v___x_1174_);
lean_del_object(v___x_1160_);
lean_dec(v_snd_1153_);
lean_dec(v_fst_1152_);
lean_dec(v_fst_1148_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 1, v_snd_1158_);
lean_ctor_set(v___x_1150_, 0, v_fst_1157_);
v___x_1239_ = v___x_1150_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_fst_1157_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_snd_1158_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
v_a_1140_ = v___x_1239_;
goto v___jp_1139_;
}
}
}
}
}
}
}
v___jp_1139_:
{
size_t v___x_1141_; size_t v___x_1142_; 
v___x_1141_ = ((size_t)1ULL);
v___x_1142_ = lean_usize_add(v_i_1136_, v___x_1141_);
v_i_1136_ = v___x_1142_;
v_b_1137_ = v_a_1140_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg___boxed(lean_object* v_fst_1245_, lean_object* v_snd_1246_, lean_object* v___x_1247_, lean_object* v___x_1248_, lean_object* v_as_1249_, lean_object* v_sz_1250_, lean_object* v_i_1251_, lean_object* v_b_1252_, lean_object* v___y_1253_){
_start:
{
size_t v_sz_boxed_1254_; size_t v_i_boxed_1255_; lean_object* v_res_1256_; 
v_sz_boxed_1254_ = lean_unbox_usize(v_sz_1250_);
lean_dec(v_sz_1250_);
v_i_boxed_1255_ = lean_unbox_usize(v_i_1251_);
lean_dec(v_i_1251_);
v_res_1256_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v_fst_1245_, v_snd_1246_, v___x_1247_, v___x_1248_, v_as_1249_, v_sz_boxed_1254_, v_i_boxed_1255_, v_b_1252_);
lean_dec_ref(v_as_1249_);
return v_res_1256_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10___lam__0(lean_object* v_x_1261_){
_start:
{
lean_object* v___x_1262_; uint8_t v___x_1263_; 
v___x_1262_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10___lam__0___closed__1));
v___x_1263_ = lean_name_eq(v_x_1261_, v___x_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10___lam__0___boxed(lean_object* v_x_1264_){
_start:
{
uint8_t v_res_1265_; lean_object* v_r_1266_; 
v_res_1265_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10___lam__0(v_x_1264_);
lean_dec(v_x_1264_);
v_r_1266_ = lean_box(v_res_1265_);
return v_r_1266_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1267_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__0);
v___x_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
return v___x_1269_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__1);
v___x_1271_ = lean_unsigned_to_nat(0u);
v___x_1272_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
lean_ctor_set(v___x_1272_, 2, v___x_1271_);
lean_ctor_set(v___x_1272_, 3, v___x_1271_);
lean_ctor_set(v___x_1272_, 4, v___x_1270_);
lean_ctor_set(v___x_1272_, 5, v___x_1270_);
lean_ctor_set(v___x_1272_, 6, v___x_1270_);
lean_ctor_set(v___x_1272_, 7, v___x_1270_);
lean_ctor_set(v___x_1272_, 8, v___x_1270_);
lean_ctor_set(v___x_1272_, 9, v___x_1270_);
lean_ctor_set(v___x_1272_, 10, v___x_1270_);
return v___x_1272_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = lean_unsigned_to_nat(32u);
v___x_1274_ = lean_mk_empty_array_with_capacity(v___x_1273_);
v___x_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
return v___x_1275_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__4(void){
_start:
{
size_t v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1276_ = ((size_t)5ULL);
v___x_1277_ = lean_unsigned_to_nat(0u);
v___x_1278_ = lean_unsigned_to_nat(32u);
v___x_1279_ = lean_mk_empty_array_with_capacity(v___x_1278_);
v___x_1280_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__3);
v___x_1281_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
lean_ctor_set(v___x_1281_, 1, v___x_1279_);
lean_ctor_set(v___x_1281_, 2, v___x_1277_);
lean_ctor_set(v___x_1281_, 3, v___x_1277_);
lean_ctor_set_usize(v___x_1281_, 4, v___x_1276_);
return v___x_1281_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1282_ = lean_box(1);
v___x_1283_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__4);
v___x_1284_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__1);
v___x_1285_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1284_);
lean_ctor_set(v___x_1285_, 1, v___x_1283_);
lean_ctor_set(v___x_1285_, 2, v___x_1282_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg(lean_object* v_msgData_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v___x_1289_; lean_object* v_env_1290_; lean_object* v___x_1291_; lean_object* v_scopes_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v_opts_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1289_ = lean_st_ref_get(v___y_1287_);
v_env_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc_ref(v_env_1290_);
lean_dec(v___x_1289_);
v___x_1291_ = lean_st_ref_get(v___y_1287_);
v_scopes_1292_ = lean_ctor_get(v___x_1291_, 2);
lean_inc(v_scopes_1292_);
lean_dec(v___x_1291_);
v___x_1293_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1294_ = l_List_head_x21___redArg(v___x_1293_, v_scopes_1292_);
lean_dec(v_scopes_1292_);
v_opts_1295_ = lean_ctor_get(v___x_1294_, 1);
lean_inc_ref(v_opts_1295_);
lean_dec(v___x_1294_);
v___x_1296_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__2);
v___x_1297_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___closed__5);
v___x_1298_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1298_, 0, v_env_1290_);
lean_ctor_set(v___x_1298_, 1, v___x_1296_);
lean_ctor_set(v___x_1298_, 2, v___x_1297_);
lean_ctor_set(v___x_1298_, 3, v_opts_1295_);
v___x_1299_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
lean_ctor_set(v___x_1299_, 1, v_msgData_1286_);
v___x_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg___boxed(lean_object* v_msgData_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg(v_msgData_1301_, v___y_1302_);
lean_dec(v___y_1302_);
return v_res_1304_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1305_; double v___x_1306_; 
v___x_1305_ = lean_unsigned_to_nat(0u);
v___x_1306_ = lean_float_of_nat(v___x_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(lean_object* v_cls_1309_, lean_object* v_msg_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_Elab_Command_getRef___redArg(v___y_1311_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1316_; lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1364_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_a_1315_);
lean_dec_ref_known(v___x_1314_, 1);
v___x_1316_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg(v_msg_1310_, v___y_1312_);
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1319_ = v___x_1316_;
v_isShared_1320_ = v_isSharedCheck_1364_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1316_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1364_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; lean_object* v_traceState_1322_; lean_object* v_env_1323_; lean_object* v_messages_1324_; lean_object* v_scopes_1325_; lean_object* v_usedQuotCtxts_1326_; lean_object* v_nextMacroScope_1327_; lean_object* v_maxRecDepth_1328_; lean_object* v_ngen_1329_; lean_object* v_auxDeclNGen_1330_; lean_object* v_infoState_1331_; lean_object* v_snapshotTasks_1332_; lean_object* v_prevLinterStates_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1363_; 
v___x_1321_ = lean_st_ref_take(v___y_1312_);
v_traceState_1322_ = lean_ctor_get(v___x_1321_, 9);
v_env_1323_ = lean_ctor_get(v___x_1321_, 0);
v_messages_1324_ = lean_ctor_get(v___x_1321_, 1);
v_scopes_1325_ = lean_ctor_get(v___x_1321_, 2);
v_usedQuotCtxts_1326_ = lean_ctor_get(v___x_1321_, 3);
v_nextMacroScope_1327_ = lean_ctor_get(v___x_1321_, 4);
v_maxRecDepth_1328_ = lean_ctor_get(v___x_1321_, 5);
v_ngen_1329_ = lean_ctor_get(v___x_1321_, 6);
v_auxDeclNGen_1330_ = lean_ctor_get(v___x_1321_, 7);
v_infoState_1331_ = lean_ctor_get(v___x_1321_, 8);
v_snapshotTasks_1332_ = lean_ctor_get(v___x_1321_, 10);
v_prevLinterStates_1333_ = lean_ctor_get(v___x_1321_, 11);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1335_ = v___x_1321_;
v_isShared_1336_ = v_isSharedCheck_1363_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_prevLinterStates_1333_);
lean_inc(v_snapshotTasks_1332_);
lean_inc(v_traceState_1322_);
lean_inc(v_infoState_1331_);
lean_inc(v_auxDeclNGen_1330_);
lean_inc(v_ngen_1329_);
lean_inc(v_maxRecDepth_1328_);
lean_inc(v_nextMacroScope_1327_);
lean_inc(v_usedQuotCtxts_1326_);
lean_inc(v_scopes_1325_);
lean_inc(v_messages_1324_);
lean_inc(v_env_1323_);
lean_dec(v___x_1321_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1363_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
uint64_t v_tid_1337_; lean_object* v_traces_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1362_; 
v_tid_1337_ = lean_ctor_get_uint64(v_traceState_1322_, sizeof(void*)*1);
v_traces_1338_ = lean_ctor_get(v_traceState_1322_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v_traceState_1322_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1340_ = v_traceState_1322_;
v_isShared_1341_ = v_isSharedCheck_1362_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_traces_1338_);
lean_dec(v_traceState_1322_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1362_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1342_; double v___x_1343_; uint8_t v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1352_; 
v___x_1342_ = lean_box(0);
v___x_1343_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0);
v___x_1344_ = 0;
v___x_1345_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_1346_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1346_, 0, v_cls_1309_);
lean_ctor_set(v___x_1346_, 1, v___x_1342_);
lean_ctor_set(v___x_1346_, 2, v___x_1345_);
lean_ctor_set_float(v___x_1346_, sizeof(void*)*3, v___x_1343_);
lean_ctor_set_float(v___x_1346_, sizeof(void*)*3 + 8, v___x_1343_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 16, v___x_1344_);
v___x_1347_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1));
v___x_1348_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1346_);
lean_ctor_set(v___x_1348_, 1, v_a_1317_);
lean_ctor_set(v___x_1348_, 2, v___x_1347_);
v___x_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1349_, 0, v_a_1315_);
lean_ctor_set(v___x_1349_, 1, v___x_1348_);
v___x_1350_ = l_Lean_PersistentArray_push___redArg(v_traces_1338_, v___x_1349_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v___x_1350_);
v___x_1352_ = v___x_1340_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1350_);
lean_ctor_set_uint64(v_reuseFailAlloc_1361_, sizeof(void*)*1, v_tid_1337_);
v___x_1352_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1354_; 
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 9, v___x_1352_);
v___x_1354_ = v___x_1335_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_env_1323_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_messages_1324_);
lean_ctor_set(v_reuseFailAlloc_1360_, 2, v_scopes_1325_);
lean_ctor_set(v_reuseFailAlloc_1360_, 3, v_usedQuotCtxts_1326_);
lean_ctor_set(v_reuseFailAlloc_1360_, 4, v_nextMacroScope_1327_);
lean_ctor_set(v_reuseFailAlloc_1360_, 5, v_maxRecDepth_1328_);
lean_ctor_set(v_reuseFailAlloc_1360_, 6, v_ngen_1329_);
lean_ctor_set(v_reuseFailAlloc_1360_, 7, v_auxDeclNGen_1330_);
lean_ctor_set(v_reuseFailAlloc_1360_, 8, v_infoState_1331_);
lean_ctor_set(v_reuseFailAlloc_1360_, 9, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1360_, 10, v_snapshotTasks_1332_);
lean_ctor_set(v_reuseFailAlloc_1360_, 11, v_prevLinterStates_1333_);
v___x_1354_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1355_ = lean_st_ref_put(v___y_1312_, v___x_1354_);
v___x_1356_ = lean_box(0);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 0, v___x_1356_);
v___x_1358_ = v___x_1319_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec_ref(v_msg_1310_);
lean_dec(v_cls_1309_);
v_a_1365_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1314_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1314_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___boxed(lean_object* v_cls_1373_, lean_object* v_msg_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v_cls_1373_, v_msg_1374_, v___y_1375_, v___y_1376_);
lean_dec(v___y_1376_);
lean_dec_ref(v___y_1375_);
return v_res_1378_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3(void){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1383_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1384_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__2));
v___x_1385_ = l_Lean_Name_append(v___x_1384_, v___x_1383_);
return v___x_1385_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__5(void){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__4));
v___x_1388_ = l_Lean_stringToMessageData(v___x_1387_);
return v___x_1388_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__7(void){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__6));
v___x_1391_ = l_Lean_stringToMessageData(v___x_1390_);
return v___x_1391_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__9(void){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__8));
v___x_1394_ = l_Lean_stringToMessageData(v___x_1393_);
return v___x_1394_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__11(void){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__10));
v___x_1397_ = l_Lean_stringToMessageData(v___x_1396_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13(lean_object* v___x_1398_, lean_object* v_val_1399_, lean_object* v_cmd_1400_, uint8_t v_onUnsolved_1401_, uint8_t v___y_1402_, lean_object* v_as_1403_, size_t v_sz_1404_, size_t v_i_1405_, lean_object* v_b_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
uint8_t v___x_1410_; 
v___x_1410_ = lean_usize_dec_lt(v_i_1405_, v_sz_1404_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; 
lean_dec(v_cmd_1400_);
v___x_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1411_, 0, v_b_1406_);
return v___x_1411_;
}
else
{
lean_object* v_snd_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1560_; 
v_snd_1412_ = lean_ctor_get(v_b_1406_, 1);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_b_1406_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; 
v_unused_1561_ = lean_ctor_get(v_b_1406_, 0);
lean_dec(v_unused_1561_);
v___x_1414_ = v_b_1406_;
v_isShared_1415_ = v_isSharedCheck_1560_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_snd_1412_);
lean_dec(v_b_1406_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1560_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v_fst_1416_; lean_object* v_snd_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1559_; 
v_fst_1416_ = lean_ctor_get(v_snd_1412_, 0);
v_snd_1417_ = lean_ctor_get(v_snd_1412_, 1);
v_isSharedCheck_1559_ = !lean_is_exclusive(v_snd_1412_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1419_ = v_snd_1412_;
v_isShared_1420_ = v_isSharedCheck_1559_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_snd_1417_);
lean_inc(v_fst_1416_);
lean_dec(v_snd_1412_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1559_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v_a_1421_; lean_object* v_pos_1422_; lean_object* v_endPos_1423_; uint8_t v_severity_1424_; lean_object* v_data_1425_; lean_object* v___x_1426_; lean_object* v_a_1428_; 
v_a_1421_ = lean_array_uget_borrowed(v_as_1403_, v_i_1405_);
v_pos_1422_ = lean_ctor_get(v_a_1421_, 1);
v_endPos_1423_ = lean_ctor_get(v_a_1421_, 2);
lean_inc(v_endPos_1423_);
v_severity_1424_ = lean_ctor_get_uint8(v_a_1421_, sizeof(void*)*5 + 1);
v_data_1425_ = lean_ctor_get(v_a_1421_, 4);
v___x_1426_ = lean_box(0);
if (v_severity_1424_ == 2)
{
lean_object* v___f_1441_; uint8_t v___x_1442_; 
v___f_1441_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__0));
lean_inc(v_data_1425_);
v___x_1442_ = l_Lean_MessageData_hasTag(v___f_1441_, v_data_1425_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; 
lean_dec(v_endPos_1423_);
lean_del_object(v___x_1414_);
v___x_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1443_, 0, v_fst_1416_);
lean_ctor_set(v___x_1443_, 1, v_snd_1417_);
v_a_1428_ = v___x_1443_;
goto v___jp_1427_;
}
else
{
if (lean_obj_tag(v_endPos_1423_) == 1)
{
lean_object* v_val_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1556_; 
v_val_1444_ = lean_ctor_get(v_endPos_1423_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v_endPos_1423_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1446_ = v_endPos_1423_;
v_isShared_1447_ = v_isSharedCheck_1556_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_val_1444_);
lean_dec(v_endPos_1423_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1556_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; uint8_t v___x_1452_; 
lean_inc_ref(v_pos_1422_);
v___x_1448_ = l_Lean_FileMap_ofPosition(v___x_1398_, v_pos_1422_);
v___x_1449_ = l_Lean_FileMap_ofPosition(v___x_1398_, v_val_1444_);
lean_inc(v___x_1449_);
lean_inc(v___x_1448_);
v___x_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1448_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
v___x_1451_ = 0;
v___x_1452_ = l_Lean_Syntax_Range_includes(v_val_1399_, v___x_1450_, v___x_1451_, v___x_1451_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; 
lean_dec_ref_known(v___x_1450_, 2);
lean_dec(v___x_1449_);
lean_dec(v___x_1448_);
lean_del_object(v___x_1446_);
lean_del_object(v___x_1414_);
v___x_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1453_, 0, v_fst_1416_);
lean_ctor_set(v___x_1453_, 1, v_snd_1417_);
v_a_1428_ = v___x_1453_;
goto v___jp_1427_;
}
else
{
lean_object* v___x_1454_; 
lean_inc(v_cmd_1400_);
lean_inc_ref(v___x_1450_);
v___x_1454_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1450_, v_cmd_1400_);
if (lean_obj_tag(v___x_1454_) == 1)
{
lean_object* v_val_1455_; lean_object* v_fst_1456_; lean_object* v_snd_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1520_; 
lean_dec(v___x_1449_);
lean_dec(v___x_1448_);
lean_del_object(v___x_1446_);
v_val_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_val_1455_);
lean_dec_ref_known(v___x_1454_, 1);
v_fst_1456_ = lean_ctor_get(v_val_1455_, 0);
v_snd_1457_ = lean_ctor_get(v_val_1455_, 1);
v_isSharedCheck_1520_ = !lean_is_exclusive(v_val_1455_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1459_ = v_val_1455_;
v_isShared_1460_ = v_isSharedCheck_1520_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_snd_1457_);
lean_inc(v_fst_1456_);
lean_dec(v_val_1455_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1520_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; uint8_t v___y_1518_; lean_object* v___x_1519_; 
v___x_1519_ = l_Lean_Syntax_getPos_x3f(v_fst_1456_, v___x_1451_);
if (lean_obj_tag(v___x_1519_) == 0)
{
v___y_1518_ = v___x_1452_;
goto v___jp_1517_;
}
else
{
lean_dec_ref_known(v___x_1519_, 1);
v___y_1518_ = v___x_1451_;
goto v___jp_1517_;
}
v___jp_1461_:
{
lean_object* v___x_1467_; 
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 1, v_snd_1417_);
lean_ctor_set(v___x_1459_, 0, v_fst_1416_);
v___x_1467_ = v___x_1459_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_fst_1416_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_snd_1417_);
v___x_1467_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
size_t v_sz_1468_; size_t v___x_1469_; lean_object* v___x_1470_; 
v_sz_1468_ = lean_array_size(v___y_1463_);
v___x_1469_ = ((size_t)0ULL);
v___x_1470_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v_fst_1456_, v_snd_1457_, v___y_1462_, v___x_1450_, v___y_1463_, v_sz_1468_, v___x_1469_, v___x_1467_);
lean_dec_ref(v___y_1463_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v_fst_1472_; lean_object* v_snd_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___x_1470_, 1);
v_fst_1472_ = lean_ctor_get(v_a_1471_, 0);
v_snd_1473_ = lean_ctor_get(v_a_1471_, 1);
v_isSharedCheck_1480_ = !lean_is_exclusive(v_a_1471_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v_a_1471_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_snd_1473_);
lean_inc(v_fst_1472_);
lean_dec(v_a_1471_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_fst_1472_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_snd_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
v_a_1428_ = v___x_1478_;
goto v___jp_1427_;
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_del_object(v___x_1419_);
lean_dec(v_cmd_1400_);
v_a_1481_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1470_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1470_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
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
v___jp_1490_:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; uint8_t v___x_1495_; 
lean_inc_ref(v___x_1450_);
v___x_1491_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1450_);
v___x_1492_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1425_);
v___x_1493_ = lean_array_get_size(v___x_1492_);
v___x_1494_ = lean_unsigned_to_nat(0u);
v___x_1495_ = lean_nat_dec_eq(v___x_1493_, v___x_1494_);
if (v___x_1495_ == 0)
{
v___y_1462_ = v___x_1491_;
v___y_1463_ = v___x_1492_;
v___y_1464_ = v___y_1407_;
v___y_1465_ = v___y_1408_;
goto v___jp_1461_;
}
else
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v_scopes_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v_opts_1502_; uint8_t v_hasTrace_1503_; 
v___x_1496_ = l_Lean_inheritedTraceOptions;
v___x_1497_ = lean_st_ref_get(v___x_1496_);
v___x_1498_ = lean_st_ref_get(v___y_1408_);
v_scopes_1499_ = lean_ctor_get(v___x_1498_, 2);
lean_inc(v_scopes_1499_);
lean_dec(v___x_1498_);
v___x_1500_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1501_ = l_List_head_x21___redArg(v___x_1500_, v_scopes_1499_);
lean_dec(v_scopes_1499_);
v_opts_1502_ = lean_ctor_get(v___x_1501_, 1);
lean_inc_ref(v_opts_1502_);
lean_dec(v___x_1501_);
v_hasTrace_1503_ = lean_ctor_get_uint8(v_opts_1502_, sizeof(void*)*1);
if (v_hasTrace_1503_ == 0)
{
lean_dec_ref(v_opts_1502_);
lean_dec(v___x_1497_);
v___y_1462_ = v___x_1491_;
v___y_1463_ = v___x_1492_;
v___y_1464_ = v___y_1407_;
v___y_1465_ = v___y_1408_;
goto v___jp_1461_;
}
else
{
lean_object* v___x_1504_; lean_object* v___x_1505_; uint8_t v___x_1506_; 
v___x_1504_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1505_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3);
v___x_1506_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1497_, v_opts_1502_, v___x_1505_);
lean_dec_ref(v_opts_1502_);
lean_dec(v___x_1497_);
if (v___x_1506_ == 0)
{
v___y_1462_ = v___x_1491_;
v___y_1463_ = v___x_1492_;
v___y_1464_ = v___y_1407_;
v___y_1465_ = v___y_1408_;
goto v___jp_1461_;
}
else
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__5);
v___x_1508_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1504_, v___x_1507_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_dec_ref_known(v___x_1508_, 1);
v___y_1462_ = v___x_1491_;
v___y_1463_ = v___x_1492_;
v___y_1464_ = v___y_1407_;
v___y_1465_ = v___y_1408_;
goto v___jp_1461_;
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
lean_dec_ref(v___x_1492_);
lean_dec(v___x_1491_);
lean_del_object(v___x_1459_);
lean_dec(v_snd_1457_);
lean_dec(v_fst_1456_);
lean_dec_ref_known(v___x_1450_, 2);
lean_del_object(v___x_1419_);
lean_dec(v_snd_1417_);
lean_dec(v_fst_1416_);
lean_dec(v_cmd_1400_);
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1508_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1508_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
}
}
}
v___jp_1517_:
{
if (v_onUnsolved_1401_ == 0)
{
if (v___y_1402_ == 0)
{
lean_del_object(v___x_1459_);
lean_dec(v_snd_1457_);
lean_dec(v_fst_1456_);
lean_dec_ref_known(v___x_1450_, 2);
goto v___jp_1435_;
}
else
{
if (v___y_1518_ == 0)
{
lean_del_object(v___x_1459_);
lean_dec(v_snd_1457_);
lean_dec(v_fst_1456_);
lean_dec_ref_known(v___x_1450_, 2);
goto v___jp_1435_;
}
else
{
lean_del_object(v___x_1414_);
goto v___jp_1490_;
}
}
}
else
{
lean_del_object(v___x_1414_);
goto v___jp_1490_;
}
}
}
}
else
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v_scopes_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v_opts_1527_; uint8_t v_hasTrace_1528_; 
lean_dec(v___x_1454_);
lean_dec_ref_known(v___x_1450_, 2);
lean_del_object(v___x_1414_);
v___x_1521_ = l_Lean_inheritedTraceOptions;
v___x_1522_ = lean_st_ref_get(v___x_1521_);
v___x_1523_ = lean_st_ref_get(v___y_1408_);
v_scopes_1524_ = lean_ctor_get(v___x_1523_, 2);
lean_inc(v_scopes_1524_);
lean_dec(v___x_1523_);
v___x_1525_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1526_ = l_List_head_x21___redArg(v___x_1525_, v_scopes_1524_);
lean_dec(v_scopes_1524_);
v_opts_1527_ = lean_ctor_get(v___x_1526_, 1);
lean_inc_ref(v_opts_1527_);
lean_dec(v___x_1526_);
v_hasTrace_1528_ = lean_ctor_get_uint8(v_opts_1527_, sizeof(void*)*1);
if (v_hasTrace_1528_ == 0)
{
lean_dec_ref(v_opts_1527_);
lean_dec(v___x_1522_);
lean_dec(v___x_1449_);
lean_dec(v___x_1448_);
lean_del_object(v___x_1446_);
goto v___jp_1439_;
}
else
{
lean_object* v___x_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
v___x_1529_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1530_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3);
v___x_1531_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1522_, v_opts_1527_, v___x_1530_);
lean_dec_ref(v_opts_1527_);
lean_dec(v___x_1522_);
if (v___x_1531_ == 0)
{
lean_dec(v___x_1449_);
lean_dec(v___x_1448_);
lean_del_object(v___x_1446_);
goto v___jp_1439_;
}
else
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1535_; 
v___x_1532_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__7);
v___x_1533_ = l_Nat_reprFast(v___x_1448_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set_tag(v___x_1446_, 3);
lean_ctor_set(v___x_1446_, 0, v___x_1533_);
v___x_1535_ = v___x_1446_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1536_ = l_Lean_MessageData_ofFormat(v___x_1535_);
v___x_1537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1532_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
v___x_1538_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__9);
v___x_1539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1537_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
v___x_1540_ = l_Nat_reprFast(v___x_1449_);
v___x_1541_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
v___x_1542_ = l_Lean_MessageData_ofFormat(v___x_1541_);
v___x_1543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1539_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
v___x_1544_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__11);
v___x_1545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1543_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v___x_1546_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1529_, v___x_1545_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_dec_ref_known(v___x_1546_, 1);
goto v___jp_1439_;
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_del_object(v___x_1419_);
lean_dec(v_snd_1417_);
lean_dec(v_fst_1416_);
lean_dec(v_cmd_1400_);
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1546_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1546_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
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
else
{
lean_object* v___x_1557_; 
lean_dec(v_endPos_1423_);
lean_del_object(v___x_1414_);
v___x_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1557_, 0, v_fst_1416_);
lean_ctor_set(v___x_1557_, 1, v_snd_1417_);
v_a_1428_ = v___x_1557_;
goto v___jp_1427_;
}
}
}
else
{
lean_object* v___x_1558_; 
lean_dec(v_endPos_1423_);
lean_del_object(v___x_1414_);
v___x_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1558_, 0, v_fst_1416_);
lean_ctor_set(v___x_1558_, 1, v_snd_1417_);
v_a_1428_ = v___x_1558_;
goto v___jp_1427_;
}
v___jp_1427_:
{
lean_object* v___x_1430_; 
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 1, v_a_1428_);
lean_ctor_set(v___x_1419_, 0, v___x_1426_);
v___x_1430_ = v___x_1419_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_a_1428_);
v___x_1430_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
size_t v___x_1431_; size_t v___x_1432_; 
v___x_1431_ = ((size_t)1ULL);
v___x_1432_ = lean_usize_add(v_i_1405_, v___x_1431_);
v_i_1405_ = v___x_1432_;
v_b_1406_ = v___x_1430_;
goto _start;
}
}
v___jp_1435_:
{
lean_object* v___x_1437_; 
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 1, v_snd_1417_);
lean_ctor_set(v___x_1414_, 0, v_fst_1416_);
v___x_1437_ = v___x_1414_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_fst_1416_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_snd_1417_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
v_a_1428_ = v___x_1437_;
goto v___jp_1427_;
}
}
v___jp_1439_:
{
lean_object* v___x_1440_; 
v___x_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1440_, 0, v_fst_1416_);
lean_ctor_set(v___x_1440_, 1, v_snd_1417_);
v_a_1428_ = v___x_1440_;
goto v___jp_1427_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___boxed(lean_object* v___x_1562_, lean_object* v_val_1563_, lean_object* v_cmd_1564_, lean_object* v_onUnsolved_1565_, lean_object* v___y_1566_, lean_object* v_as_1567_, lean_object* v_sz_1568_, lean_object* v_i_1569_, lean_object* v_b_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
uint8_t v_onUnsolved_boxed_1574_; uint8_t v___y_17564__boxed_1575_; size_t v_sz_boxed_1576_; size_t v_i_boxed_1577_; lean_object* v_res_1578_; 
v_onUnsolved_boxed_1574_ = lean_unbox(v_onUnsolved_1565_);
v___y_17564__boxed_1575_ = lean_unbox(v___y_1566_);
v_sz_boxed_1576_ = lean_unbox_usize(v_sz_1568_);
lean_dec(v_sz_1568_);
v_i_boxed_1577_ = lean_unbox_usize(v_i_1569_);
lean_dec(v_i_1569_);
v_res_1578_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13(v___x_1562_, v_val_1563_, v_cmd_1564_, v_onUnsolved_boxed_1574_, v___y_17564__boxed_1575_, v_as_1567_, v_sz_boxed_1576_, v_i_boxed_1577_, v_b_1570_, v___y_1571_, v___y_1572_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec_ref(v_as_1567_);
lean_dec_ref(v_val_1563_);
lean_dec_ref(v___x_1562_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12(lean_object* v___x_1579_, lean_object* v_val_1580_, lean_object* v_cmd_1581_, uint8_t v_onUnsolved_1582_, uint8_t v___y_1583_, lean_object* v_as_1584_, size_t v_sz_1585_, size_t v_i_1586_, lean_object* v_b_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
uint8_t v___x_1591_; 
v___x_1591_ = lean_usize_dec_lt(v_i_1586_, v_sz_1585_);
if (v___x_1591_ == 0)
{
lean_object* v___x_1592_; 
lean_dec(v_cmd_1581_);
v___x_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1592_, 0, v_b_1587_);
return v___x_1592_;
}
else
{
lean_object* v_snd_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1741_; 
v_snd_1593_ = lean_ctor_get(v_b_1587_, 1);
v_isSharedCheck_1741_ = !lean_is_exclusive(v_b_1587_);
if (v_isSharedCheck_1741_ == 0)
{
lean_object* v_unused_1742_; 
v_unused_1742_ = lean_ctor_get(v_b_1587_, 0);
lean_dec(v_unused_1742_);
v___x_1595_ = v_b_1587_;
v_isShared_1596_ = v_isSharedCheck_1741_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_snd_1593_);
lean_dec(v_b_1587_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1741_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v_fst_1597_; lean_object* v_snd_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1740_; 
v_fst_1597_ = lean_ctor_get(v_snd_1593_, 0);
v_snd_1598_ = lean_ctor_get(v_snd_1593_, 1);
v_isSharedCheck_1740_ = !lean_is_exclusive(v_snd_1593_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1600_ = v_snd_1593_;
v_isShared_1601_ = v_isSharedCheck_1740_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_snd_1598_);
lean_inc(v_fst_1597_);
lean_dec(v_snd_1593_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1740_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v_a_1602_; lean_object* v_pos_1603_; lean_object* v_endPos_1604_; uint8_t v_severity_1605_; lean_object* v_data_1606_; lean_object* v___x_1607_; lean_object* v_a_1609_; 
v_a_1602_ = lean_array_uget_borrowed(v_as_1584_, v_i_1586_);
v_pos_1603_ = lean_ctor_get(v_a_1602_, 1);
v_endPos_1604_ = lean_ctor_get(v_a_1602_, 2);
lean_inc(v_endPos_1604_);
v_severity_1605_ = lean_ctor_get_uint8(v_a_1602_, sizeof(void*)*5 + 1);
v_data_1606_ = lean_ctor_get(v_a_1602_, 4);
v___x_1607_ = lean_box(0);
if (v_severity_1605_ == 2)
{
lean_object* v___f_1622_; uint8_t v___x_1623_; 
v___f_1622_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__0));
lean_inc(v_data_1606_);
v___x_1623_ = l_Lean_MessageData_hasTag(v___f_1622_, v_data_1606_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; 
lean_dec(v_endPos_1604_);
lean_del_object(v___x_1595_);
v___x_1624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1624_, 0, v_fst_1597_);
lean_ctor_set(v___x_1624_, 1, v_snd_1598_);
v_a_1609_ = v___x_1624_;
goto v___jp_1608_;
}
else
{
if (lean_obj_tag(v_endPos_1604_) == 1)
{
lean_object* v_val_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1737_; 
v_val_1625_ = lean_ctor_get(v_endPos_1604_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v_endPos_1604_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1627_ = v_endPos_1604_;
v_isShared_1628_ = v_isSharedCheck_1737_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_val_1625_);
lean_dec(v_endPos_1604_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1737_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; uint8_t v___x_1632_; uint8_t v___x_1633_; 
lean_inc_ref(v_pos_1603_);
v___x_1629_ = l_Lean_FileMap_ofPosition(v___x_1579_, v_pos_1603_);
v___x_1630_ = l_Lean_FileMap_ofPosition(v___x_1579_, v_val_1625_);
lean_inc(v___x_1630_);
lean_inc(v___x_1629_);
v___x_1631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1629_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = 0;
v___x_1633_ = l_Lean_Syntax_Range_includes(v_val_1580_, v___x_1631_, v___x_1632_, v___x_1632_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; 
lean_dec_ref_known(v___x_1631_, 2);
lean_dec(v___x_1630_);
lean_dec(v___x_1629_);
lean_del_object(v___x_1627_);
lean_del_object(v___x_1595_);
v___x_1634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1634_, 0, v_fst_1597_);
lean_ctor_set(v___x_1634_, 1, v_snd_1598_);
v_a_1609_ = v___x_1634_;
goto v___jp_1608_;
}
else
{
lean_object* v___x_1635_; 
lean_inc(v_cmd_1581_);
lean_inc_ref(v___x_1631_);
v___x_1635_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1631_, v_cmd_1581_);
if (lean_obj_tag(v___x_1635_) == 1)
{
lean_object* v_val_1636_; lean_object* v_fst_1637_; lean_object* v_snd_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1701_; 
lean_dec(v___x_1630_);
lean_dec(v___x_1629_);
lean_del_object(v___x_1627_);
v_val_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_val_1636_);
lean_dec_ref_known(v___x_1635_, 1);
v_fst_1637_ = lean_ctor_get(v_val_1636_, 0);
v_snd_1638_ = lean_ctor_get(v_val_1636_, 1);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_val_1636_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1640_ = v_val_1636_;
v_isShared_1641_ = v_isSharedCheck_1701_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_snd_1638_);
lean_inc(v_fst_1637_);
lean_dec(v_val_1636_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1701_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; uint8_t v___y_1699_; lean_object* v___x_1700_; 
v___x_1700_ = l_Lean_Syntax_getPos_x3f(v_fst_1637_, v___x_1632_);
if (lean_obj_tag(v___x_1700_) == 0)
{
v___y_1699_ = v___x_1633_;
goto v___jp_1698_;
}
else
{
lean_dec_ref_known(v___x_1700_, 1);
v___y_1699_ = v___x_1632_;
goto v___jp_1698_;
}
v___jp_1642_:
{
lean_object* v___x_1648_; 
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 1, v_snd_1598_);
lean_ctor_set(v___x_1640_, 0, v_fst_1597_);
v___x_1648_ = v___x_1640_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_fst_1597_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v_snd_1598_);
v___x_1648_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
size_t v_sz_1649_; size_t v___x_1650_; lean_object* v___x_1651_; 
v_sz_1649_ = lean_array_size(v___y_1643_);
v___x_1650_ = ((size_t)0ULL);
v___x_1651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v_fst_1637_, v_snd_1638_, v___y_1644_, v___x_1631_, v___y_1643_, v_sz_1649_, v___x_1650_, v___x_1648_);
lean_dec_ref(v___y_1643_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; lean_object* v_fst_1653_; lean_object* v_snd_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_a_1652_);
lean_dec_ref_known(v___x_1651_, 1);
v_fst_1653_ = lean_ctor_get(v_a_1652_, 0);
v_snd_1654_ = lean_ctor_get(v_a_1652_, 1);
v_isSharedCheck_1661_ = !lean_is_exclusive(v_a_1652_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v_a_1652_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_snd_1654_);
lean_inc(v_fst_1653_);
lean_dec(v_a_1652_);
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
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_fst_1653_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_snd_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
v_a_1609_ = v___x_1659_;
goto v___jp_1608_;
}
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_del_object(v___x_1600_);
lean_dec(v_cmd_1581_);
v_a_1662_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1651_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1651_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
}
v___jp_1671_:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; uint8_t v___x_1676_; 
lean_inc_ref(v___x_1631_);
v___x_1672_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1631_);
v___x_1673_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1606_);
v___x_1674_ = lean_array_get_size(v___x_1673_);
v___x_1675_ = lean_unsigned_to_nat(0u);
v___x_1676_ = lean_nat_dec_eq(v___x_1674_, v___x_1675_);
if (v___x_1676_ == 0)
{
v___y_1643_ = v___x_1673_;
v___y_1644_ = v___x_1672_;
v___y_1645_ = v___y_1588_;
v___y_1646_ = v___y_1589_;
goto v___jp_1642_;
}
else
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v_scopes_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v_opts_1683_; uint8_t v_hasTrace_1684_; 
v___x_1677_ = l_Lean_inheritedTraceOptions;
v___x_1678_ = lean_st_ref_get(v___x_1677_);
v___x_1679_ = lean_st_ref_get(v___y_1589_);
v_scopes_1680_ = lean_ctor_get(v___x_1679_, 2);
lean_inc(v_scopes_1680_);
lean_dec(v___x_1679_);
v___x_1681_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1682_ = l_List_head_x21___redArg(v___x_1681_, v_scopes_1680_);
lean_dec(v_scopes_1680_);
v_opts_1683_ = lean_ctor_get(v___x_1682_, 1);
lean_inc_ref(v_opts_1683_);
lean_dec(v___x_1682_);
v_hasTrace_1684_ = lean_ctor_get_uint8(v_opts_1683_, sizeof(void*)*1);
if (v_hasTrace_1684_ == 0)
{
lean_dec_ref(v_opts_1683_);
lean_dec(v___x_1678_);
v___y_1643_ = v___x_1673_;
v___y_1644_ = v___x_1672_;
v___y_1645_ = v___y_1588_;
v___y_1646_ = v___y_1589_;
goto v___jp_1642_;
}
else
{
lean_object* v___x_1685_; lean_object* v___x_1686_; uint8_t v___x_1687_; 
v___x_1685_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1686_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3);
v___x_1687_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1678_, v_opts_1683_, v___x_1686_);
lean_dec_ref(v_opts_1683_);
lean_dec(v___x_1678_);
if (v___x_1687_ == 0)
{
v___y_1643_ = v___x_1673_;
v___y_1644_ = v___x_1672_;
v___y_1645_ = v___y_1588_;
v___y_1646_ = v___y_1589_;
goto v___jp_1642_;
}
else
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__5);
v___x_1689_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1685_, v___x_1688_, v___y_1588_, v___y_1589_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_dec_ref_known(v___x_1689_, 1);
v___y_1643_ = v___x_1673_;
v___y_1644_ = v___x_1672_;
v___y_1645_ = v___y_1588_;
v___y_1646_ = v___y_1589_;
goto v___jp_1642_;
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
lean_dec_ref(v___x_1673_);
lean_dec(v___x_1672_);
lean_del_object(v___x_1640_);
lean_dec(v_snd_1638_);
lean_dec(v_fst_1637_);
lean_dec_ref_known(v___x_1631_, 2);
lean_del_object(v___x_1600_);
lean_dec(v_snd_1598_);
lean_dec(v_fst_1597_);
lean_dec(v_cmd_1581_);
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1689_);
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
}
v___jp_1698_:
{
if (v_onUnsolved_1582_ == 0)
{
if (v___y_1583_ == 0)
{
lean_del_object(v___x_1640_);
lean_dec(v_snd_1638_);
lean_dec(v_fst_1637_);
lean_dec_ref_known(v___x_1631_, 2);
goto v___jp_1616_;
}
else
{
if (v___y_1699_ == 0)
{
lean_del_object(v___x_1640_);
lean_dec(v_snd_1638_);
lean_dec(v_fst_1637_);
lean_dec_ref_known(v___x_1631_, 2);
goto v___jp_1616_;
}
else
{
lean_del_object(v___x_1595_);
goto v___jp_1671_;
}
}
}
else
{
lean_del_object(v___x_1595_);
goto v___jp_1671_;
}
}
}
}
else
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v_scopes_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v_opts_1708_; uint8_t v_hasTrace_1709_; 
lean_dec(v___x_1635_);
lean_dec_ref_known(v___x_1631_, 2);
lean_del_object(v___x_1595_);
v___x_1702_ = l_Lean_inheritedTraceOptions;
v___x_1703_ = lean_st_ref_get(v___x_1702_);
v___x_1704_ = lean_st_ref_get(v___y_1589_);
v_scopes_1705_ = lean_ctor_get(v___x_1704_, 2);
lean_inc(v_scopes_1705_);
lean_dec(v___x_1704_);
v___x_1706_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1707_ = l_List_head_x21___redArg(v___x_1706_, v_scopes_1705_);
lean_dec(v_scopes_1705_);
v_opts_1708_ = lean_ctor_get(v___x_1707_, 1);
lean_inc_ref(v_opts_1708_);
lean_dec(v___x_1707_);
v_hasTrace_1709_ = lean_ctor_get_uint8(v_opts_1708_, sizeof(void*)*1);
if (v_hasTrace_1709_ == 0)
{
lean_dec_ref(v_opts_1708_);
lean_dec(v___x_1703_);
lean_dec(v___x_1630_);
lean_dec(v___x_1629_);
lean_del_object(v___x_1627_);
goto v___jp_1620_;
}
else
{
lean_object* v___x_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
v___x_1710_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1711_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3);
v___x_1712_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1703_, v_opts_1708_, v___x_1711_);
lean_dec_ref(v_opts_1708_);
lean_dec(v___x_1703_);
if (v___x_1712_ == 0)
{
lean_dec(v___x_1630_);
lean_dec(v___x_1629_);
lean_del_object(v___x_1627_);
goto v___jp_1620_;
}
else
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1716_; 
v___x_1713_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__7);
v___x_1714_ = l_Nat_reprFast(v___x_1629_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set_tag(v___x_1627_, 3);
lean_ctor_set(v___x_1627_, 0, v___x_1714_);
v___x_1716_ = v___x_1627_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1714_);
v___x_1716_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1717_ = l_Lean_MessageData_ofFormat(v___x_1716_);
v___x_1718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1713_);
lean_ctor_set(v___x_1718_, 1, v___x_1717_);
v___x_1719_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__9);
v___x_1720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1718_);
lean_ctor_set(v___x_1720_, 1, v___x_1719_);
v___x_1721_ = l_Nat_reprFast(v___x_1630_);
v___x_1722_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
v___x_1723_ = l_Lean_MessageData_ofFormat(v___x_1722_);
v___x_1724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1720_);
lean_ctor_set(v___x_1724_, 1, v___x_1723_);
v___x_1725_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__11);
v___x_1726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1724_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
v___x_1727_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1710_, v___x_1726_, v___y_1588_, v___y_1589_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_dec_ref_known(v___x_1727_, 1);
goto v___jp_1620_;
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
lean_del_object(v___x_1600_);
lean_dec(v_snd_1598_);
lean_dec(v_fst_1597_);
lean_dec(v_cmd_1581_);
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1727_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1727_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
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
else
{
lean_object* v___x_1738_; 
lean_dec(v_endPos_1604_);
lean_del_object(v___x_1595_);
v___x_1738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1738_, 0, v_fst_1597_);
lean_ctor_set(v___x_1738_, 1, v_snd_1598_);
v_a_1609_ = v___x_1738_;
goto v___jp_1608_;
}
}
}
else
{
lean_object* v___x_1739_; 
lean_dec(v_endPos_1604_);
lean_del_object(v___x_1595_);
v___x_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1739_, 0, v_fst_1597_);
lean_ctor_set(v___x_1739_, 1, v_snd_1598_);
v_a_1609_ = v___x_1739_;
goto v___jp_1608_;
}
v___jp_1608_:
{
lean_object* v___x_1611_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 1, v_a_1609_);
lean_ctor_set(v___x_1600_, 0, v___x_1607_);
v___x_1611_ = v___x_1600_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1607_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_a_1609_);
v___x_1611_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
size_t v___x_1612_; size_t v___x_1613_; lean_object* v___x_1614_; 
v___x_1612_ = ((size_t)1ULL);
v___x_1613_ = lean_usize_add(v_i_1586_, v___x_1612_);
v___x_1614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13(v___x_1579_, v_val_1580_, v_cmd_1581_, v_onUnsolved_1582_, v___y_1583_, v_as_1584_, v_sz_1585_, v___x_1613_, v___x_1611_, v___y_1588_, v___y_1589_);
return v___x_1614_;
}
}
v___jp_1616_:
{
lean_object* v___x_1618_; 
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 1, v_snd_1598_);
lean_ctor_set(v___x_1595_, 0, v_fst_1597_);
v___x_1618_ = v___x_1595_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_fst_1597_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_snd_1598_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
v_a_1609_ = v___x_1618_;
goto v___jp_1608_;
}
}
v___jp_1620_:
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1621_, 0, v_fst_1597_);
lean_ctor_set(v___x_1621_, 1, v_snd_1598_);
v_a_1609_ = v___x_1621_;
goto v___jp_1608_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12___boxed(lean_object* v___x_1743_, lean_object* v_val_1744_, lean_object* v_cmd_1745_, lean_object* v_onUnsolved_1746_, lean_object* v___y_1747_, lean_object* v_as_1748_, lean_object* v_sz_1749_, lean_object* v_i_1750_, lean_object* v_b_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
uint8_t v_onUnsolved_boxed_1755_; uint8_t v___y_17905__boxed_1756_; size_t v_sz_boxed_1757_; size_t v_i_boxed_1758_; lean_object* v_res_1759_; 
v_onUnsolved_boxed_1755_ = lean_unbox(v_onUnsolved_1746_);
v___y_17905__boxed_1756_ = lean_unbox(v___y_1747_);
v_sz_boxed_1757_ = lean_unbox_usize(v_sz_1749_);
lean_dec(v_sz_1749_);
v_i_boxed_1758_ = lean_unbox_usize(v_i_1750_);
lean_dec(v_i_1750_);
v_res_1759_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12(v___x_1743_, v_val_1744_, v_cmd_1745_, v_onUnsolved_boxed_1755_, v___y_17905__boxed_1756_, v_as_1748_, v_sz_boxed_1757_, v_i_boxed_1758_, v_b_1751_, v___y_1752_, v___y_1753_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec_ref(v_as_1748_);
lean_dec_ref(v_val_1744_);
lean_dec_ref(v___x_1743_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(lean_object* v_init_1760_, lean_object* v___x_1761_, lean_object* v_val_1762_, lean_object* v_cmd_1763_, uint8_t v_onUnsolved_1764_, uint8_t v___y_1765_, lean_object* v_n_1766_, lean_object* v_b_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
if (lean_obj_tag(v_n_1766_) == 0)
{
lean_object* v_cs_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; size_t v_sz_1774_; size_t v___x_1775_; lean_object* v___x_1776_; 
v_cs_1771_ = lean_ctor_get(v_n_1766_, 0);
v___x_1772_ = lean_box(0);
v___x_1773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
lean_ctor_set(v___x_1773_, 1, v_b_1767_);
v_sz_1774_ = lean_array_size(v_cs_1771_);
v___x_1775_ = ((size_t)0ULL);
v___x_1776_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__11(v_init_1760_, v___x_1761_, v_val_1762_, v_cmd_1763_, v_onUnsolved_1764_, v___y_1765_, v_cs_1771_, v_sz_1774_, v___x_1775_, v___x_1773_, v___y_1768_, v___y_1769_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1791_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1779_ = v___x_1776_;
v_isShared_1780_ = v_isSharedCheck_1791_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1776_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1791_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v_fst_1781_; 
v_fst_1781_ = lean_ctor_get(v_a_1777_, 0);
if (lean_obj_tag(v_fst_1781_) == 0)
{
lean_object* v_snd_1782_; lean_object* v___x_1783_; lean_object* v___x_1785_; 
v_snd_1782_ = lean_ctor_get(v_a_1777_, 1);
lean_inc(v_snd_1782_);
lean_dec(v_a_1777_);
v___x_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1783_, 0, v_snd_1782_);
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1783_);
v___x_1785_ = v___x_1779_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
else
{
lean_object* v_val_1787_; lean_object* v___x_1789_; 
lean_inc_ref(v_fst_1781_);
lean_dec(v_a_1777_);
v_val_1787_ = lean_ctor_get(v_fst_1781_, 0);
lean_inc(v_val_1787_);
lean_dec_ref_known(v_fst_1781_, 1);
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v_val_1787_);
v___x_1789_ = v___x_1779_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_val_1787_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
v_a_1792_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1776_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1776_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
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
lean_object* v_vs_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; size_t v_sz_1803_; size_t v___x_1804_; lean_object* v___x_1805_; 
v_vs_1800_ = lean_ctor_get(v_n_1766_, 0);
v___x_1801_ = lean_box(0);
v___x_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1801_);
lean_ctor_set(v___x_1802_, 1, v_b_1767_);
v_sz_1803_ = lean_array_size(v_vs_1800_);
v___x_1804_ = ((size_t)0ULL);
v___x_1805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12(v___x_1761_, v_val_1762_, v_cmd_1763_, v_onUnsolved_1764_, v___y_1765_, v_vs_1800_, v_sz_1803_, v___x_1804_, v___x_1802_, v___y_1768_, v___y_1769_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1820_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1808_ = v___x_1805_;
v_isShared_1809_ = v_isSharedCheck_1820_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1805_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1820_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v_fst_1810_; 
v_fst_1810_ = lean_ctor_get(v_a_1806_, 0);
if (lean_obj_tag(v_fst_1810_) == 0)
{
lean_object* v_snd_1811_; lean_object* v___x_1812_; lean_object* v___x_1814_; 
v_snd_1811_ = lean_ctor_get(v_a_1806_, 1);
lean_inc(v_snd_1811_);
lean_dec(v_a_1806_);
v___x_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1812_, 0, v_snd_1811_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v___x_1812_);
v___x_1814_ = v___x_1808_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
else
{
lean_object* v_val_1816_; lean_object* v___x_1818_; 
lean_inc_ref(v_fst_1810_);
lean_dec(v_a_1806_);
v_val_1816_ = lean_ctor_get(v_fst_1810_, 0);
lean_inc(v_val_1816_);
lean_dec_ref_known(v_fst_1810_, 1);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v_val_1816_);
v___x_1818_ = v___x_1808_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_val_1816_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
v_a_1821_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1805_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1805_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__11(lean_object* v_init_1829_, lean_object* v___x_1830_, lean_object* v_val_1831_, lean_object* v_cmd_1832_, uint8_t v_onUnsolved_1833_, uint8_t v___y_1834_, lean_object* v_as_1835_, size_t v_sz_1836_, size_t v_i_1837_, lean_object* v_b_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
uint8_t v___x_1842_; 
v___x_1842_ = lean_usize_dec_lt(v_i_1837_, v_sz_1836_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; 
lean_dec(v_cmd_1832_);
v___x_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1843_, 0, v_b_1838_);
return v___x_1843_;
}
else
{
lean_object* v_snd_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1878_; 
v_snd_1844_ = lean_ctor_get(v_b_1838_, 1);
v_isSharedCheck_1878_ = !lean_is_exclusive(v_b_1838_);
if (v_isSharedCheck_1878_ == 0)
{
lean_object* v_unused_1879_; 
v_unused_1879_ = lean_ctor_get(v_b_1838_, 0);
lean_dec(v_unused_1879_);
v___x_1846_ = v_b_1838_;
v_isShared_1847_ = v_isSharedCheck_1878_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_snd_1844_);
lean_dec(v_b_1838_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1878_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v_a_1848_; lean_object* v___x_1849_; 
v_a_1848_ = lean_array_uget_borrowed(v_as_1835_, v_i_1837_);
lean_inc(v_snd_1844_);
lean_inc(v_cmd_1832_);
v___x_1849_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(v_init_1829_, v___x_1830_, v_val_1831_, v_cmd_1832_, v_onUnsolved_1833_, v___y_1834_, v_a_1848_, v_snd_1844_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1869_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1852_ = v___x_1849_;
v_isShared_1853_ = v_isSharedCheck_1869_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1849_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1869_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
if (lean_obj_tag(v_a_1850_) == 0)
{
lean_object* v___x_1854_; lean_object* v___x_1856_; 
lean_dec(v_cmd_1832_);
v___x_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1854_, 0, v_a_1850_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1854_);
v___x_1856_ = v___x_1846_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1854_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v_snd_1844_);
v___x_1856_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1858_; 
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v___x_1856_);
v___x_1858_ = v___x_1852_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1856_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1862_; lean_object* v___x_1864_; 
lean_del_object(v___x_1852_);
lean_dec(v_snd_1844_);
v_a_1861_ = lean_ctor_get(v_a_1850_, 0);
lean_inc(v_a_1861_);
lean_dec_ref_known(v_a_1850_, 1);
v___x_1862_ = lean_box(0);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 1, v_a_1861_);
lean_ctor_set(v___x_1846_, 0, v___x_1862_);
v___x_1864_ = v___x_1846_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1862_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v_a_1861_);
v___x_1864_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
size_t v___x_1865_; size_t v___x_1866_; 
v___x_1865_ = ((size_t)1ULL);
v___x_1866_ = lean_usize_add(v_i_1837_, v___x_1865_);
v_i_1837_ = v___x_1866_;
v_b_1838_ = v___x_1864_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_del_object(v___x_1846_);
lean_dec(v_snd_1844_);
lean_dec(v_cmd_1832_);
v_a_1870_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1849_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1849_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__11___boxed(lean_object* v_init_1880_, lean_object* v___x_1881_, lean_object* v_val_1882_, lean_object* v_cmd_1883_, lean_object* v_onUnsolved_1884_, lean_object* v___y_1885_, lean_object* v_as_1886_, lean_object* v_sz_1887_, lean_object* v_i_1888_, lean_object* v_b_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
uint8_t v_onUnsolved_boxed_1893_; uint8_t v___y_18206__boxed_1894_; size_t v_sz_boxed_1895_; size_t v_i_boxed_1896_; lean_object* v_res_1897_; 
v_onUnsolved_boxed_1893_ = lean_unbox(v_onUnsolved_1884_);
v___y_18206__boxed_1894_ = lean_unbox(v___y_1885_);
v_sz_boxed_1895_ = lean_unbox_usize(v_sz_1887_);
lean_dec(v_sz_1887_);
v_i_boxed_1896_ = lean_unbox_usize(v_i_1888_);
lean_dec(v_i_1888_);
v_res_1897_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__11(v_init_1880_, v___x_1881_, v_val_1882_, v_cmd_1883_, v_onUnsolved_boxed_1893_, v___y_18206__boxed_1894_, v_as_1886_, v_sz_boxed_1895_, v_i_boxed_1896_, v_b_1889_, v___y_1890_, v___y_1891_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec_ref(v_as_1886_);
lean_dec_ref(v_val_1882_);
lean_dec_ref(v___x_1881_);
lean_dec_ref(v_init_1880_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___boxed(lean_object* v_init_1898_, lean_object* v___x_1899_, lean_object* v_val_1900_, lean_object* v_cmd_1901_, lean_object* v_onUnsolved_1902_, lean_object* v___y_1903_, lean_object* v_n_1904_, lean_object* v_b_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
uint8_t v_onUnsolved_boxed_1909_; uint8_t v___y_18228__boxed_1910_; lean_object* v_res_1911_; 
v_onUnsolved_boxed_1909_ = lean_unbox(v_onUnsolved_1902_);
v___y_18228__boxed_1910_ = lean_unbox(v___y_1903_);
v_res_1911_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(v_init_1898_, v___x_1899_, v_val_1900_, v_cmd_1901_, v_onUnsolved_boxed_1909_, v___y_18228__boxed_1910_, v_n_1904_, v_b_1905_, v___y_1906_, v___y_1907_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec_ref(v_n_1904_);
lean_dec_ref(v_val_1900_);
lean_dec_ref(v___x_1899_);
lean_dec_ref(v_init_1898_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10_spec__14(lean_object* v___x_1912_, lean_object* v_val_1913_, lean_object* v_cmd_1914_, uint8_t v_onUnsolved_1915_, uint8_t v___y_1916_, lean_object* v_as_1917_, size_t v_sz_1918_, size_t v_i_1919_, lean_object* v_b_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
uint8_t v___x_1924_; 
v___x_1924_ = lean_usize_dec_lt(v_i_1919_, v_sz_1918_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; 
lean_dec(v_cmd_1914_);
v___x_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1925_, 0, v_b_1920_);
return v___x_1925_;
}
else
{
lean_object* v_snd_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_2074_; 
v_snd_1926_ = lean_ctor_get(v_b_1920_, 1);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_b_1920_);
if (v_isSharedCheck_2074_ == 0)
{
lean_object* v_unused_2075_; 
v_unused_2075_ = lean_ctor_get(v_b_1920_, 0);
lean_dec(v_unused_2075_);
v___x_1928_ = v_b_1920_;
v_isShared_1929_ = v_isSharedCheck_2074_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_snd_1926_);
lean_dec(v_b_1920_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_2074_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v_fst_1930_; lean_object* v_snd_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_2073_; 
v_fst_1930_ = lean_ctor_get(v_snd_1926_, 0);
v_snd_1931_ = lean_ctor_get(v_snd_1926_, 1);
v_isSharedCheck_2073_ = !lean_is_exclusive(v_snd_1926_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_1933_ = v_snd_1926_;
v_isShared_1934_ = v_isSharedCheck_2073_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_snd_1931_);
lean_inc(v_fst_1930_);
lean_dec(v_snd_1926_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_2073_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v_a_1935_; lean_object* v_pos_1936_; lean_object* v_endPos_1937_; uint8_t v_severity_1938_; lean_object* v_data_1939_; lean_object* v___x_1940_; lean_object* v_a_1942_; 
v_a_1935_ = lean_array_uget_borrowed(v_as_1917_, v_i_1919_);
v_pos_1936_ = lean_ctor_get(v_a_1935_, 1);
v_endPos_1937_ = lean_ctor_get(v_a_1935_, 2);
lean_inc(v_endPos_1937_);
v_severity_1938_ = lean_ctor_get_uint8(v_a_1935_, sizeof(void*)*5 + 1);
v_data_1939_ = lean_ctor_get(v_a_1935_, 4);
v___x_1940_ = lean_box(0);
if (v_severity_1938_ == 2)
{
lean_object* v___f_1955_; uint8_t v___x_1956_; 
v___f_1955_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__0));
lean_inc(v_data_1939_);
v___x_1956_ = l_Lean_MessageData_hasTag(v___f_1955_, v_data_1939_);
if (v___x_1956_ == 0)
{
lean_object* v___x_1957_; 
lean_dec(v_endPos_1937_);
lean_del_object(v___x_1928_);
v___x_1957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1957_, 0, v_fst_1930_);
lean_ctor_set(v___x_1957_, 1, v_snd_1931_);
v_a_1942_ = v___x_1957_;
goto v___jp_1941_;
}
else
{
if (lean_obj_tag(v_endPos_1937_) == 1)
{
lean_object* v_val_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_2070_; 
v_val_1958_ = lean_ctor_get(v_endPos_1937_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v_endPos_1937_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_1960_ = v_endPos_1937_;
v_isShared_1961_ = v_isSharedCheck_2070_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_val_1958_);
lean_dec(v_endPos_1937_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_2070_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; uint8_t v___x_1965_; uint8_t v___x_1966_; 
lean_inc_ref(v_pos_1936_);
v___x_1962_ = l_Lean_FileMap_ofPosition(v___x_1912_, v_pos_1936_);
v___x_1963_ = l_Lean_FileMap_ofPosition(v___x_1912_, v_val_1958_);
lean_inc(v___x_1963_);
lean_inc(v___x_1962_);
v___x_1964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1962_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = 0;
v___x_1966_ = l_Lean_Syntax_Range_includes(v_val_1913_, v___x_1964_, v___x_1965_, v___x_1965_);
if (v___x_1966_ == 0)
{
lean_object* v___x_1967_; 
lean_dec_ref_known(v___x_1964_, 2);
lean_dec(v___x_1963_);
lean_dec(v___x_1962_);
lean_del_object(v___x_1960_);
lean_del_object(v___x_1928_);
v___x_1967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1967_, 0, v_fst_1930_);
lean_ctor_set(v___x_1967_, 1, v_snd_1931_);
v_a_1942_ = v___x_1967_;
goto v___jp_1941_;
}
else
{
lean_object* v___x_1968_; 
lean_inc(v_cmd_1914_);
lean_inc_ref(v___x_1964_);
v___x_1968_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1964_, v_cmd_1914_);
if (lean_obj_tag(v___x_1968_) == 1)
{
lean_object* v_val_1969_; lean_object* v_fst_1970_; lean_object* v_snd_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_2034_; 
lean_dec(v___x_1963_);
lean_dec(v___x_1962_);
lean_del_object(v___x_1960_);
v_val_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_val_1969_);
lean_dec_ref_known(v___x_1968_, 1);
v_fst_1970_ = lean_ctor_get(v_val_1969_, 0);
v_snd_1971_ = lean_ctor_get(v_val_1969_, 1);
v_isSharedCheck_2034_ = !lean_is_exclusive(v_val_1969_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_1973_ = v_val_1969_;
v_isShared_1974_ = v_isSharedCheck_2034_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_snd_1971_);
lean_inc(v_fst_1970_);
lean_dec(v_val_1969_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_2034_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; uint8_t v___y_2032_; lean_object* v___x_2033_; 
v___x_2033_ = l_Lean_Syntax_getPos_x3f(v_fst_1970_, v___x_1965_);
if (lean_obj_tag(v___x_2033_) == 0)
{
v___y_2032_ = v___x_1966_;
goto v___jp_2031_;
}
else
{
lean_dec_ref_known(v___x_2033_, 1);
v___y_2032_ = v___x_1965_;
goto v___jp_2031_;
}
v___jp_1975_:
{
lean_object* v___x_1981_; 
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 1, v_snd_1931_);
lean_ctor_set(v___x_1973_, 0, v_fst_1930_);
v___x_1981_ = v___x_1973_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_fst_1930_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_snd_1931_);
v___x_1981_ = v_reuseFailAlloc_2003_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
size_t v_sz_1982_; size_t v___x_1983_; lean_object* v___x_1984_; 
v_sz_1982_ = lean_array_size(v___y_1977_);
v___x_1983_ = ((size_t)0ULL);
v___x_1984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v_fst_1970_, v_snd_1971_, v___y_1976_, v___x_1964_, v___y_1977_, v_sz_1982_, v___x_1983_, v___x_1981_);
lean_dec_ref(v___y_1977_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; lean_object* v_fst_1986_; lean_object* v_snd_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_a_1985_);
lean_dec_ref_known(v___x_1984_, 1);
v_fst_1986_ = lean_ctor_get(v_a_1985_, 0);
v_snd_1987_ = lean_ctor_get(v_a_1985_, 1);
v_isSharedCheck_1994_ = !lean_is_exclusive(v_a_1985_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v_a_1985_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_snd_1987_);
lean_inc(v_fst_1986_);
lean_dec(v_a_1985_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_fst_1986_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_snd_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
v_a_1942_ = v___x_1992_;
goto v___jp_1941_;
}
}
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
lean_del_object(v___x_1933_);
lean_dec(v_cmd_1914_);
v_a_1995_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1984_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1984_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
v___jp_2004_:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; uint8_t v___x_2009_; 
lean_inc_ref(v___x_1964_);
v___x_2005_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1964_);
v___x_2006_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1939_);
v___x_2007_ = lean_array_get_size(v___x_2006_);
v___x_2008_ = lean_unsigned_to_nat(0u);
v___x_2009_ = lean_nat_dec_eq(v___x_2007_, v___x_2008_);
if (v___x_2009_ == 0)
{
v___y_1976_ = v___x_2005_;
v___y_1977_ = v___x_2006_;
v___y_1978_ = v___y_1921_;
v___y_1979_ = v___y_1922_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v_scopes_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v_opts_2016_; uint8_t v_hasTrace_2017_; 
v___x_2010_ = l_Lean_inheritedTraceOptions;
v___x_2011_ = lean_st_ref_get(v___x_2010_);
v___x_2012_ = lean_st_ref_get(v___y_1922_);
v_scopes_2013_ = lean_ctor_get(v___x_2012_, 2);
lean_inc(v_scopes_2013_);
lean_dec(v___x_2012_);
v___x_2014_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2015_ = l_List_head_x21___redArg(v___x_2014_, v_scopes_2013_);
lean_dec(v_scopes_2013_);
v_opts_2016_ = lean_ctor_get(v___x_2015_, 1);
lean_inc_ref(v_opts_2016_);
lean_dec(v___x_2015_);
v_hasTrace_2017_ = lean_ctor_get_uint8(v_opts_2016_, sizeof(void*)*1);
if (v_hasTrace_2017_ == 0)
{
lean_dec_ref(v_opts_2016_);
lean_dec(v___x_2011_);
v___y_1976_ = v___x_2005_;
v___y_1977_ = v___x_2006_;
v___y_1978_ = v___y_1921_;
v___y_1979_ = v___y_1922_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_2018_; lean_object* v___x_2019_; uint8_t v___x_2020_; 
v___x_2018_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2019_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3);
v___x_2020_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2011_, v_opts_2016_, v___x_2019_);
lean_dec_ref(v_opts_2016_);
lean_dec(v___x_2011_);
if (v___x_2020_ == 0)
{
v___y_1976_ = v___x_2005_;
v___y_1977_ = v___x_2006_;
v___y_1978_ = v___y_1921_;
v___y_1979_ = v___y_1922_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2021_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__5);
v___x_2022_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_2018_, v___x_2021_, v___y_1921_, v___y_1922_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_dec_ref_known(v___x_2022_, 1);
v___y_1976_ = v___x_2005_;
v___y_1977_ = v___x_2006_;
v___y_1978_ = v___y_1921_;
v___y_1979_ = v___y_1922_;
goto v___jp_1975_;
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
lean_dec_ref(v___x_2006_);
lean_dec(v___x_2005_);
lean_del_object(v___x_1973_);
lean_dec(v_snd_1971_);
lean_dec(v_fst_1970_);
lean_dec_ref_known(v___x_1964_, 2);
lean_del_object(v___x_1933_);
lean_dec(v_snd_1931_);
lean_dec(v_fst_1930_);
lean_dec(v_cmd_1914_);
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___x_2022_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_2022_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
}
}
}
v___jp_2031_:
{
if (v_onUnsolved_1915_ == 0)
{
if (v___y_1916_ == 0)
{
lean_del_object(v___x_1973_);
lean_dec(v_snd_1971_);
lean_dec(v_fst_1970_);
lean_dec_ref_known(v___x_1964_, 2);
goto v___jp_1949_;
}
else
{
if (v___y_2032_ == 0)
{
lean_del_object(v___x_1973_);
lean_dec(v_snd_1971_);
lean_dec(v_fst_1970_);
lean_dec_ref_known(v___x_1964_, 2);
goto v___jp_1949_;
}
else
{
lean_del_object(v___x_1928_);
goto v___jp_2004_;
}
}
}
else
{
lean_del_object(v___x_1928_);
goto v___jp_2004_;
}
}
}
}
else
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v_scopes_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v_opts_2041_; uint8_t v_hasTrace_2042_; 
lean_dec(v___x_1968_);
lean_dec_ref_known(v___x_1964_, 2);
lean_del_object(v___x_1928_);
v___x_2035_ = l_Lean_inheritedTraceOptions;
v___x_2036_ = lean_st_ref_get(v___x_2035_);
v___x_2037_ = lean_st_ref_get(v___y_1922_);
v_scopes_2038_ = lean_ctor_get(v___x_2037_, 2);
lean_inc(v_scopes_2038_);
lean_dec(v___x_2037_);
v___x_2039_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2040_ = l_List_head_x21___redArg(v___x_2039_, v_scopes_2038_);
lean_dec(v_scopes_2038_);
v_opts_2041_ = lean_ctor_get(v___x_2040_, 1);
lean_inc_ref(v_opts_2041_);
lean_dec(v___x_2040_);
v_hasTrace_2042_ = lean_ctor_get_uint8(v_opts_2041_, sizeof(void*)*1);
if (v_hasTrace_2042_ == 0)
{
lean_dec_ref(v_opts_2041_);
lean_dec(v___x_2036_);
lean_dec(v___x_1963_);
lean_dec(v___x_1962_);
lean_del_object(v___x_1960_);
goto v___jp_1953_;
}
else
{
lean_object* v___x_2043_; lean_object* v___x_2044_; uint8_t v___x_2045_; 
v___x_2043_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2044_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3);
v___x_2045_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2036_, v_opts_2041_, v___x_2044_);
lean_dec_ref(v_opts_2041_);
lean_dec(v___x_2036_);
if (v___x_2045_ == 0)
{
lean_dec(v___x_1963_);
lean_dec(v___x_1962_);
lean_del_object(v___x_1960_);
goto v___jp_1953_;
}
else
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2049_; 
v___x_2046_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__7);
v___x_2047_ = l_Nat_reprFast(v___x_1962_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set_tag(v___x_1960_, 3);
lean_ctor_set(v___x_1960_, 0, v___x_2047_);
v___x_2049_ = v___x_1960_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2047_);
v___x_2049_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2050_ = l_Lean_MessageData_ofFormat(v___x_2049_);
v___x_2051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2046_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
v___x_2052_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__9);
v___x_2053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2051_);
lean_ctor_set(v___x_2053_, 1, v___x_2052_);
v___x_2054_ = l_Nat_reprFast(v___x_1963_);
v___x_2055_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
v___x_2056_ = l_Lean_MessageData_ofFormat(v___x_2055_);
v___x_2057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2053_);
lean_ctor_set(v___x_2057_, 1, v___x_2056_);
v___x_2058_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__11);
v___x_2059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2057_);
lean_ctor_set(v___x_2059_, 1, v___x_2058_);
v___x_2060_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_2043_, v___x_2059_, v___y_1921_, v___y_1922_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_dec_ref_known(v___x_2060_, 1);
goto v___jp_1953_;
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_del_object(v___x_1933_);
lean_dec(v_snd_1931_);
lean_dec(v_fst_1930_);
lean_dec(v_cmd_1914_);
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2060_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2060_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
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
else
{
lean_object* v___x_2071_; 
lean_dec(v_endPos_1937_);
lean_del_object(v___x_1928_);
v___x_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2071_, 0, v_fst_1930_);
lean_ctor_set(v___x_2071_, 1, v_snd_1931_);
v_a_1942_ = v___x_2071_;
goto v___jp_1941_;
}
}
}
else
{
lean_object* v___x_2072_; 
lean_dec(v_endPos_1937_);
lean_del_object(v___x_1928_);
v___x_2072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2072_, 0, v_fst_1930_);
lean_ctor_set(v___x_2072_, 1, v_snd_1931_);
v_a_1942_ = v___x_2072_;
goto v___jp_1941_;
}
v___jp_1941_:
{
lean_object* v___x_1944_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 1, v_a_1942_);
lean_ctor_set(v___x_1933_, 0, v___x_1940_);
v___x_1944_ = v___x_1933_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1940_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_a_1942_);
v___x_1944_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
size_t v___x_1945_; size_t v___x_1946_; 
v___x_1945_ = ((size_t)1ULL);
v___x_1946_ = lean_usize_add(v_i_1919_, v___x_1945_);
v_i_1919_ = v___x_1946_;
v_b_1920_ = v___x_1944_;
goto _start;
}
}
v___jp_1949_:
{
lean_object* v___x_1951_; 
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 1, v_snd_1931_);
lean_ctor_set(v___x_1928_, 0, v_fst_1930_);
v___x_1951_ = v___x_1928_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_fst_1930_);
lean_ctor_set(v_reuseFailAlloc_1952_, 1, v_snd_1931_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
v_a_1942_ = v___x_1951_;
goto v___jp_1941_;
}
}
v___jp_1953_:
{
lean_object* v___x_1954_; 
v___x_1954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1954_, 0, v_fst_1930_);
lean_ctor_set(v___x_1954_, 1, v_snd_1931_);
v_a_1942_ = v___x_1954_;
goto v___jp_1941_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10_spec__14___boxed(lean_object* v___x_2076_, lean_object* v_val_2077_, lean_object* v_cmd_2078_, lean_object* v_onUnsolved_2079_, lean_object* v___y_2080_, lean_object* v_as_2081_, lean_object* v_sz_2082_, lean_object* v_i_2083_, lean_object* v_b_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
uint8_t v_onUnsolved_boxed_2088_; uint8_t v___y_18450__boxed_2089_; size_t v_sz_boxed_2090_; size_t v_i_boxed_2091_; lean_object* v_res_2092_; 
v_onUnsolved_boxed_2088_ = lean_unbox(v_onUnsolved_2079_);
v___y_18450__boxed_2089_ = lean_unbox(v___y_2080_);
v_sz_boxed_2090_ = lean_unbox_usize(v_sz_2082_);
lean_dec(v_sz_2082_);
v_i_boxed_2091_ = lean_unbox_usize(v_i_2083_);
lean_dec(v_i_2083_);
v_res_2092_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10_spec__14(v___x_2076_, v_val_2077_, v_cmd_2078_, v_onUnsolved_boxed_2088_, v___y_18450__boxed_2089_, v_as_2081_, v_sz_boxed_2090_, v_i_boxed_2091_, v_b_2084_, v___y_2085_, v___y_2086_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
lean_dec_ref(v_as_2081_);
lean_dec_ref(v_val_2077_);
lean_dec_ref(v___x_2076_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10(lean_object* v___x_2093_, lean_object* v_val_2094_, lean_object* v_cmd_2095_, uint8_t v_onUnsolved_2096_, uint8_t v___y_2097_, lean_object* v_as_2098_, size_t v_sz_2099_, size_t v_i_2100_, lean_object* v_b_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
uint8_t v___x_2105_; 
v___x_2105_ = lean_usize_dec_lt(v_i_2100_, v_sz_2099_);
if (v___x_2105_ == 0)
{
lean_object* v___x_2106_; 
lean_dec(v_cmd_2095_);
v___x_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2106_, 0, v_b_2101_);
return v___x_2106_;
}
else
{
lean_object* v_snd_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2255_; 
v_snd_2107_ = lean_ctor_get(v_b_2101_, 1);
v_isSharedCheck_2255_ = !lean_is_exclusive(v_b_2101_);
if (v_isSharedCheck_2255_ == 0)
{
lean_object* v_unused_2256_; 
v_unused_2256_ = lean_ctor_get(v_b_2101_, 0);
lean_dec(v_unused_2256_);
v___x_2109_ = v_b_2101_;
v_isShared_2110_ = v_isSharedCheck_2255_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_snd_2107_);
lean_dec(v_b_2101_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2255_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v_fst_2111_; lean_object* v_snd_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2254_; 
v_fst_2111_ = lean_ctor_get(v_snd_2107_, 0);
v_snd_2112_ = lean_ctor_get(v_snd_2107_, 1);
v_isSharedCheck_2254_ = !lean_is_exclusive(v_snd_2107_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2114_ = v_snd_2107_;
v_isShared_2115_ = v_isSharedCheck_2254_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_snd_2112_);
lean_inc(v_fst_2111_);
lean_dec(v_snd_2107_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2254_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v_a_2116_; lean_object* v_pos_2117_; lean_object* v_endPos_2118_; uint8_t v_severity_2119_; lean_object* v_data_2120_; lean_object* v___x_2121_; lean_object* v_a_2123_; 
v_a_2116_ = lean_array_uget_borrowed(v_as_2098_, v_i_2100_);
v_pos_2117_ = lean_ctor_get(v_a_2116_, 1);
v_endPos_2118_ = lean_ctor_get(v_a_2116_, 2);
lean_inc(v_endPos_2118_);
v_severity_2119_ = lean_ctor_get_uint8(v_a_2116_, sizeof(void*)*5 + 1);
v_data_2120_ = lean_ctor_get(v_a_2116_, 4);
v___x_2121_ = lean_box(0);
if (v_severity_2119_ == 2)
{
lean_object* v___f_2136_; uint8_t v___x_2137_; 
v___f_2136_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__0));
lean_inc(v_data_2120_);
v___x_2137_ = l_Lean_MessageData_hasTag(v___f_2136_, v_data_2120_);
if (v___x_2137_ == 0)
{
lean_object* v___x_2138_; 
lean_dec(v_endPos_2118_);
lean_del_object(v___x_2109_);
v___x_2138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2138_, 0, v_fst_2111_);
lean_ctor_set(v___x_2138_, 1, v_snd_2112_);
v_a_2123_ = v___x_2138_;
goto v___jp_2122_;
}
else
{
if (lean_obj_tag(v_endPos_2118_) == 1)
{
lean_object* v_val_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2251_; 
v_val_2139_ = lean_ctor_get(v_endPos_2118_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v_endPos_2118_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2141_ = v_endPos_2118_;
v_isShared_2142_ = v_isSharedCheck_2251_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_val_2139_);
lean_dec(v_endPos_2118_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2251_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; uint8_t v___x_2147_; 
lean_inc_ref(v_pos_2117_);
v___x_2143_ = l_Lean_FileMap_ofPosition(v___x_2093_, v_pos_2117_);
v___x_2144_ = l_Lean_FileMap_ofPosition(v___x_2093_, v_val_2139_);
lean_inc(v___x_2144_);
lean_inc(v___x_2143_);
v___x_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2143_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = 0;
v___x_2147_ = l_Lean_Syntax_Range_includes(v_val_2094_, v___x_2145_, v___x_2146_, v___x_2146_);
if (v___x_2147_ == 0)
{
lean_object* v___x_2148_; 
lean_dec_ref_known(v___x_2145_, 2);
lean_dec(v___x_2144_);
lean_dec(v___x_2143_);
lean_del_object(v___x_2141_);
lean_del_object(v___x_2109_);
v___x_2148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2148_, 0, v_fst_2111_);
lean_ctor_set(v___x_2148_, 1, v_snd_2112_);
v_a_2123_ = v___x_2148_;
goto v___jp_2122_;
}
else
{
lean_object* v___x_2149_; 
lean_inc(v_cmd_2095_);
lean_inc_ref(v___x_2145_);
v___x_2149_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_2145_, v_cmd_2095_);
if (lean_obj_tag(v___x_2149_) == 1)
{
lean_object* v_val_2150_; lean_object* v_fst_2151_; lean_object* v_snd_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2215_; 
lean_dec(v___x_2144_);
lean_dec(v___x_2143_);
lean_del_object(v___x_2141_);
v_val_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_val_2150_);
lean_dec_ref_known(v___x_2149_, 1);
v_fst_2151_ = lean_ctor_get(v_val_2150_, 0);
v_snd_2152_ = lean_ctor_get(v_val_2150_, 1);
v_isSharedCheck_2215_ = !lean_is_exclusive(v_val_2150_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2154_ = v_val_2150_;
v_isShared_2155_ = v_isSharedCheck_2215_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_snd_2152_);
lean_inc(v_fst_2151_);
lean_dec(v_val_2150_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2215_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; uint8_t v___y_2213_; lean_object* v___x_2214_; 
v___x_2214_ = l_Lean_Syntax_getPos_x3f(v_fst_2151_, v___x_2146_);
if (lean_obj_tag(v___x_2214_) == 0)
{
v___y_2213_ = v___x_2147_;
goto v___jp_2212_;
}
else
{
lean_dec_ref_known(v___x_2214_, 1);
v___y_2213_ = v___x_2146_;
goto v___jp_2212_;
}
v___jp_2156_:
{
lean_object* v___x_2162_; 
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 1, v_snd_2112_);
lean_ctor_set(v___x_2154_, 0, v_fst_2111_);
v___x_2162_ = v___x_2154_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_fst_2111_);
lean_ctor_set(v_reuseFailAlloc_2184_, 1, v_snd_2112_);
v___x_2162_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
size_t v_sz_2163_; size_t v___x_2164_; lean_object* v___x_2165_; 
v_sz_2163_ = lean_array_size(v___y_2157_);
v___x_2164_ = ((size_t)0ULL);
v___x_2165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v_fst_2151_, v_snd_2152_, v___y_2158_, v___x_2145_, v___y_2157_, v_sz_2163_, v___x_2164_, v___x_2162_);
lean_dec_ref(v___y_2157_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_a_2166_; lean_object* v_fst_2167_; lean_object* v_snd_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_a_2166_);
lean_dec_ref_known(v___x_2165_, 1);
v_fst_2167_ = lean_ctor_get(v_a_2166_, 0);
v_snd_2168_ = lean_ctor_get(v_a_2166_, 1);
v_isSharedCheck_2175_ = !lean_is_exclusive(v_a_2166_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v_a_2166_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_snd_2168_);
lean_inc(v_fst_2167_);
lean_dec(v_a_2166_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_fst_2167_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v_snd_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
v_a_2123_ = v___x_2173_;
goto v___jp_2122_;
}
}
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_del_object(v___x_2114_);
lean_dec(v_cmd_2095_);
v_a_2176_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2165_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2165_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
}
v___jp_2185_:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; 
lean_inc_ref(v___x_2145_);
v___x_2186_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_2145_);
v___x_2187_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_2120_);
v___x_2188_ = lean_array_get_size(v___x_2187_);
v___x_2189_ = lean_unsigned_to_nat(0u);
v___x_2190_ = lean_nat_dec_eq(v___x_2188_, v___x_2189_);
if (v___x_2190_ == 0)
{
v___y_2157_ = v___x_2187_;
v___y_2158_ = v___x_2186_;
v___y_2159_ = v___y_2102_;
v___y_2160_ = v___y_2103_;
goto v___jp_2156_;
}
else
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v_scopes_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v_opts_2197_; uint8_t v_hasTrace_2198_; 
v___x_2191_ = l_Lean_inheritedTraceOptions;
v___x_2192_ = lean_st_ref_get(v___x_2191_);
v___x_2193_ = lean_st_ref_get(v___y_2103_);
v_scopes_2194_ = lean_ctor_get(v___x_2193_, 2);
lean_inc(v_scopes_2194_);
lean_dec(v___x_2193_);
v___x_2195_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2196_ = l_List_head_x21___redArg(v___x_2195_, v_scopes_2194_);
lean_dec(v_scopes_2194_);
v_opts_2197_ = lean_ctor_get(v___x_2196_, 1);
lean_inc_ref(v_opts_2197_);
lean_dec(v___x_2196_);
v_hasTrace_2198_ = lean_ctor_get_uint8(v_opts_2197_, sizeof(void*)*1);
if (v_hasTrace_2198_ == 0)
{
lean_dec_ref(v_opts_2197_);
lean_dec(v___x_2192_);
v___y_2157_ = v___x_2187_;
v___y_2158_ = v___x_2186_;
v___y_2159_ = v___y_2102_;
v___y_2160_ = v___y_2103_;
goto v___jp_2156_;
}
else
{
lean_object* v___x_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; 
v___x_2199_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2200_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3);
v___x_2201_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2192_, v_opts_2197_, v___x_2200_);
lean_dec_ref(v_opts_2197_);
lean_dec(v___x_2192_);
if (v___x_2201_ == 0)
{
v___y_2157_ = v___x_2187_;
v___y_2158_ = v___x_2186_;
v___y_2159_ = v___y_2102_;
v___y_2160_ = v___y_2103_;
goto v___jp_2156_;
}
else
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__5);
v___x_2203_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_2199_, v___x_2202_, v___y_2102_, v___y_2103_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_dec_ref_known(v___x_2203_, 1);
v___y_2157_ = v___x_2187_;
v___y_2158_ = v___x_2186_;
v___y_2159_ = v___y_2102_;
v___y_2160_ = v___y_2103_;
goto v___jp_2156_;
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
lean_dec_ref(v___x_2187_);
lean_dec(v___x_2186_);
lean_del_object(v___x_2154_);
lean_dec(v_snd_2152_);
lean_dec(v_fst_2151_);
lean_dec_ref_known(v___x_2145_, 2);
lean_del_object(v___x_2114_);
lean_dec(v_snd_2112_);
lean_dec(v_fst_2111_);
lean_dec(v_cmd_2095_);
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2203_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2203_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
}
}
}
v___jp_2212_:
{
if (v_onUnsolved_2096_ == 0)
{
if (v___y_2097_ == 0)
{
lean_del_object(v___x_2154_);
lean_dec(v_snd_2152_);
lean_dec(v_fst_2151_);
lean_dec_ref_known(v___x_2145_, 2);
goto v___jp_2130_;
}
else
{
if (v___y_2213_ == 0)
{
lean_del_object(v___x_2154_);
lean_dec(v_snd_2152_);
lean_dec(v_fst_2151_);
lean_dec_ref_known(v___x_2145_, 2);
goto v___jp_2130_;
}
else
{
lean_del_object(v___x_2109_);
goto v___jp_2185_;
}
}
}
else
{
lean_del_object(v___x_2109_);
goto v___jp_2185_;
}
}
}
}
else
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v_scopes_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v_opts_2222_; uint8_t v_hasTrace_2223_; 
lean_dec(v___x_2149_);
lean_dec_ref_known(v___x_2145_, 2);
lean_del_object(v___x_2109_);
v___x_2216_ = l_Lean_inheritedTraceOptions;
v___x_2217_ = lean_st_ref_get(v___x_2216_);
v___x_2218_ = lean_st_ref_get(v___y_2103_);
v_scopes_2219_ = lean_ctor_get(v___x_2218_, 2);
lean_inc(v_scopes_2219_);
lean_dec(v___x_2218_);
v___x_2220_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2221_ = l_List_head_x21___redArg(v___x_2220_, v_scopes_2219_);
lean_dec(v_scopes_2219_);
v_opts_2222_ = lean_ctor_get(v___x_2221_, 1);
lean_inc_ref(v_opts_2222_);
lean_dec(v___x_2221_);
v_hasTrace_2223_ = lean_ctor_get_uint8(v_opts_2222_, sizeof(void*)*1);
if (v_hasTrace_2223_ == 0)
{
lean_dec_ref(v_opts_2222_);
lean_dec(v___x_2217_);
lean_dec(v___x_2144_);
lean_dec(v___x_2143_);
lean_del_object(v___x_2141_);
goto v___jp_2134_;
}
else
{
lean_object* v___x_2224_; lean_object* v___x_2225_; uint8_t v___x_2226_; 
v___x_2224_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2225_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3);
v___x_2226_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2217_, v_opts_2222_, v___x_2225_);
lean_dec_ref(v_opts_2222_);
lean_dec(v___x_2217_);
if (v___x_2226_ == 0)
{
lean_dec(v___x_2144_);
lean_dec(v___x_2143_);
lean_del_object(v___x_2141_);
goto v___jp_2134_;
}
else
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2230_; 
v___x_2227_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__7);
v___x_2228_ = l_Nat_reprFast(v___x_2143_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set_tag(v___x_2141_, 3);
lean_ctor_set(v___x_2141_, 0, v___x_2228_);
v___x_2230_ = v___x_2141_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v___x_2228_);
v___x_2230_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2231_ = l_Lean_MessageData_ofFormat(v___x_2230_);
v___x_2232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2227_);
lean_ctor_set(v___x_2232_, 1, v___x_2231_);
v___x_2233_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__9);
v___x_2234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2232_);
lean_ctor_set(v___x_2234_, 1, v___x_2233_);
v___x_2235_ = l_Nat_reprFast(v___x_2144_);
v___x_2236_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
v___x_2237_ = l_Lean_MessageData_ofFormat(v___x_2236_);
v___x_2238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2234_);
lean_ctor_set(v___x_2238_, 1, v___x_2237_);
v___x_2239_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__11);
v___x_2240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2238_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
v___x_2241_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_2224_, v___x_2240_, v___y_2102_, v___y_2103_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_dec_ref_known(v___x_2241_, 1);
goto v___jp_2134_;
}
else
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
lean_del_object(v___x_2114_);
lean_dec(v_snd_2112_);
lean_dec(v_fst_2111_);
lean_dec(v_cmd_2095_);
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2244_ = v___x_2241_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2241_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
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
else
{
lean_object* v___x_2252_; 
lean_dec(v_endPos_2118_);
lean_del_object(v___x_2109_);
v___x_2252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2252_, 0, v_fst_2111_);
lean_ctor_set(v___x_2252_, 1, v_snd_2112_);
v_a_2123_ = v___x_2252_;
goto v___jp_2122_;
}
}
}
else
{
lean_object* v___x_2253_; 
lean_dec(v_endPos_2118_);
lean_del_object(v___x_2109_);
v___x_2253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2253_, 0, v_fst_2111_);
lean_ctor_set(v___x_2253_, 1, v_snd_2112_);
v_a_2123_ = v___x_2253_;
goto v___jp_2122_;
}
v___jp_2122_:
{
lean_object* v___x_2125_; 
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 1, v_a_2123_);
lean_ctor_set(v___x_2114_, 0, v___x_2121_);
v___x_2125_ = v___x_2114_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2121_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_a_2123_);
v___x_2125_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
size_t v___x_2126_; size_t v___x_2127_; lean_object* v___x_2128_; 
v___x_2126_ = ((size_t)1ULL);
v___x_2127_ = lean_usize_add(v_i_2100_, v___x_2126_);
v___x_2128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10_spec__14(v___x_2093_, v_val_2094_, v_cmd_2095_, v_onUnsolved_2096_, v___y_2097_, v_as_2098_, v_sz_2099_, v___x_2127_, v___x_2125_, v___y_2102_, v___y_2103_);
return v___x_2128_;
}
}
v___jp_2130_:
{
lean_object* v___x_2132_; 
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 1, v_snd_2112_);
lean_ctor_set(v___x_2109_, 0, v_fst_2111_);
v___x_2132_ = v___x_2109_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_fst_2111_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_snd_2112_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
v_a_2123_ = v___x_2132_;
goto v___jp_2122_;
}
}
v___jp_2134_:
{
lean_object* v___x_2135_; 
v___x_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2135_, 0, v_fst_2111_);
lean_ctor_set(v___x_2135_, 1, v_snd_2112_);
v_a_2123_ = v___x_2135_;
goto v___jp_2122_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10___boxed(lean_object* v___x_2257_, lean_object* v_val_2258_, lean_object* v_cmd_2259_, lean_object* v_onUnsolved_2260_, lean_object* v___y_2261_, lean_object* v_as_2262_, lean_object* v_sz_2263_, lean_object* v_i_2264_, lean_object* v_b_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
uint8_t v_onUnsolved_boxed_2269_; uint8_t v___y_18782__boxed_2270_; size_t v_sz_boxed_2271_; size_t v_i_boxed_2272_; lean_object* v_res_2273_; 
v_onUnsolved_boxed_2269_ = lean_unbox(v_onUnsolved_2260_);
v___y_18782__boxed_2270_ = lean_unbox(v___y_2261_);
v_sz_boxed_2271_ = lean_unbox_usize(v_sz_2263_);
lean_dec(v_sz_2263_);
v_i_boxed_2272_ = lean_unbox_usize(v_i_2264_);
lean_dec(v_i_2264_);
v_res_2273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10(v___x_2257_, v_val_2258_, v_cmd_2259_, v_onUnsolved_boxed_2269_, v___y_18782__boxed_2270_, v_as_2262_, v_sz_boxed_2271_, v_i_boxed_2272_, v_b_2265_, v___y_2266_, v___y_2267_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec_ref(v_as_2262_);
lean_dec_ref(v_val_2258_);
lean_dec_ref(v___x_2257_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5(lean_object* v___x_2274_, lean_object* v_val_2275_, lean_object* v_cmd_2276_, uint8_t v_onUnsolved_2277_, uint8_t v___y_2278_, lean_object* v_t_2279_, lean_object* v_init_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v_root_2284_; lean_object* v_tail_2285_; lean_object* v___x_2286_; 
v_root_2284_ = lean_ctor_get(v_t_2279_, 0);
v_tail_2285_ = lean_ctor_get(v_t_2279_, 1);
lean_inc(v_cmd_2276_);
lean_inc_ref(v_init_2280_);
v___x_2286_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(v_init_2280_, v___x_2274_, v_val_2275_, v_cmd_2276_, v_onUnsolved_2277_, v___y_2278_, v_root_2284_, v_init_2280_, v___y_2281_, v___y_2282_);
lean_dec_ref(v_init_2280_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2323_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2289_ = v___x_2286_;
v_isShared_2290_ = v_isSharedCheck_2323_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2286_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2323_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
if (lean_obj_tag(v_a_2287_) == 0)
{
lean_object* v_a_2291_; lean_object* v___x_2293_; 
lean_dec(v_cmd_2276_);
v_a_2291_ = lean_ctor_get(v_a_2287_, 0);
lean_inc(v_a_2291_);
lean_dec_ref_known(v_a_2287_, 1);
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 0, v_a_2291_);
v___x_2293_ = v___x_2289_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2291_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
else
{
lean_object* v_a_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; size_t v_sz_2298_; size_t v___x_2299_; lean_object* v___x_2300_; 
lean_del_object(v___x_2289_);
v_a_2295_ = lean_ctor_get(v_a_2287_, 0);
lean_inc(v_a_2295_);
lean_dec_ref_known(v_a_2287_, 1);
v___x_2296_ = lean_box(0);
v___x_2297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
lean_ctor_set(v___x_2297_, 1, v_a_2295_);
v_sz_2298_ = lean_array_size(v_tail_2285_);
v___x_2299_ = ((size_t)0ULL);
v___x_2300_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__10(v___x_2274_, v_val_2275_, v_cmd_2276_, v_onUnsolved_2277_, v___y_2278_, v_tail_2285_, v_sz_2298_, v___x_2299_, v___x_2297_, v___y_2281_, v___y_2282_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2314_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2303_ = v___x_2300_;
v_isShared_2304_ = v_isSharedCheck_2314_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2300_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2314_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v_fst_2305_; 
v_fst_2305_ = lean_ctor_get(v_a_2301_, 0);
if (lean_obj_tag(v_fst_2305_) == 0)
{
lean_object* v_snd_2306_; lean_object* v___x_2308_; 
v_snd_2306_ = lean_ctor_get(v_a_2301_, 1);
lean_inc(v_snd_2306_);
lean_dec(v_a_2301_);
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 0, v_snd_2306_);
v___x_2308_ = v___x_2303_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_snd_2306_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
else
{
lean_object* v_val_2310_; lean_object* v___x_2312_; 
lean_inc_ref(v_fst_2305_);
lean_dec(v_a_2301_);
v_val_2310_ = lean_ctor_get(v_fst_2305_, 0);
lean_inc(v_val_2310_);
lean_dec_ref_known(v_fst_2305_, 1);
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 0, v_val_2310_);
v___x_2312_ = v___x_2303_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_val_2310_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
v_a_2315_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2300_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2300_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
}
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec(v_cmd_2276_);
v_a_2324_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2286_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2286_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5___boxed(lean_object* v___x_2332_, lean_object* v_val_2333_, lean_object* v_cmd_2334_, lean_object* v_onUnsolved_2335_, lean_object* v___y_2336_, lean_object* v_t_2337_, lean_object* v_init_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
uint8_t v_onUnsolved_boxed_2342_; uint8_t v___y_19083__boxed_2343_; lean_object* v_res_2344_; 
v_onUnsolved_boxed_2342_ = lean_unbox(v_onUnsolved_2335_);
v___y_19083__boxed_2343_ = lean_unbox(v___y_2336_);
v_res_2344_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5(v___x_2332_, v_val_2333_, v_cmd_2334_, v_onUnsolved_boxed_2342_, v___y_19083__boxed_2343_, v_t_2337_, v_init_2338_, v___y_2339_, v___y_2340_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec_ref(v_t_2337_);
lean_dec_ref(v_val_2333_);
lean_dec_ref(v___x_2332_);
return v_res_2344_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0(void){
_start:
{
lean_object* v_cellCount_2345_; lean_object* v___x_2346_; 
v_cellCount_2345_ = lean_unsigned_to_nat(16u);
v___x_2346_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2345_);
return v___x_2346_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1(void){
_start:
{
lean_object* v_cellCount_2347_; lean_object* v___x_2348_; 
v_cellCount_2347_ = lean_unsigned_to_nat(16u);
v___x_2348_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2347_);
return v___x_2348_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__2(void){
_start:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2349_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1);
v___x_2350_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0);
v___x_2351_ = lean_unsigned_to_nat(0u);
v___x_2352_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2351_);
lean_ctor_set(v___x_2352_, 1, v___x_2350_);
lean_ctor_set(v___x_2352_, 2, v___x_2349_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(lean_object* v_cmd_2356_, lean_object* v_opts_2357_, lean_object* v_tree_2358_, lean_object* v_msgs_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_){
_start:
{
lean_object* v___y_2364_; uint8_t v___y_2365_; uint8_t v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2368_; uint8_t v___y_2369_; uint8_t v___y_2395_; uint8_t v___y_2396_; lean_object* v_acc_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___f_2401_; uint8_t v___y_2403_; lean_object* v___x_2410_; uint8_t v___x_2411_; 
v___f_2401_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__3));
v___x_2410_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_2411_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2357_, v___x_2410_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; uint8_t v___x_2413_; 
v___x_2412_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_2413_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2357_, v___x_2412_);
v___y_2403_ = v___x_2413_;
goto v___jp_2402_;
}
else
{
v___y_2403_ = v___x_2411_;
goto v___jp_2402_;
}
v___jp_2363_:
{
lean_object* v___x_2370_; 
v___x_2370_ = l_Lean_Syntax_getRange_x3f(v_cmd_2356_, v___y_2369_);
if (lean_obj_tag(v___x_2370_) == 1)
{
lean_object* v_val_2371_; lean_object* v_fileMap_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v_val_2371_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_val_2371_);
lean_dec_ref_known(v___x_2370_, 1);
v_fileMap_2372_ = lean_ctor_get(v___y_2368_, 1);
v___x_2373_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__2, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__2_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__2);
v___x_2374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___y_2367_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5(v_fileMap_2372_, v_val_2371_, v_cmd_2356_, v___y_2365_, v___y_2366_, v_msgs_2359_, v___x_2374_, v___y_2368_, v___y_2364_);
lean_dec(v_val_2371_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2384_; 
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2378_ = v___x_2375_;
v_isShared_2379_ = v_isSharedCheck_2384_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2375_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2384_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v_fst_2380_; lean_object* v___x_2382_; 
v_fst_2380_ = lean_ctor_get(v_a_2376_, 0);
lean_inc(v_fst_2380_);
lean_dec(v_a_2376_);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 0, v_fst_2380_);
v___x_2382_ = v___x_2378_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_fst_2380_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2392_; 
v_a_2385_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2387_ = v___x_2375_;
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2375_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2385_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
else
{
lean_object* v___x_2393_; 
lean_dec(v___x_2370_);
lean_dec(v_cmd_2356_);
v___x_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2393_, 0, v___y_2367_);
return v___x_2393_;
}
}
v___jp_2394_:
{
if (v___y_2395_ == 0)
{
if (v___y_2396_ == 0)
{
lean_object* v___x_2400_; 
lean_dec(v_cmd_2356_);
v___x_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2400_, 0, v_acc_2397_);
return v___x_2400_;
}
else
{
v___y_2364_ = v___y_2399_;
v___y_2365_ = v___y_2395_;
v___y_2366_ = v___y_2396_;
v___y_2367_ = v_acc_2397_;
v___y_2368_ = v___y_2398_;
v___y_2369_ = v___y_2396_;
goto v___jp_2363_;
}
}
else
{
v___y_2364_ = v___y_2399_;
v___y_2365_ = v___y_2395_;
v___y_2366_ = v___y_2396_;
v___y_2367_ = v_acc_2397_;
v___y_2368_ = v___y_2398_;
v___y_2369_ = v___y_2395_;
goto v___jp_2363_;
}
}
v___jp_2402_:
{
lean_object* v___x_2404_; uint8_t v_onUnsolved_2405_; lean_object* v___x_2406_; uint8_t v_onSorry_2407_; lean_object* v_acc_2408_; 
v___x_2404_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
v_onUnsolved_2405_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2357_, v___x_2404_);
v___x_2406_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v_onSorry_2407_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2357_, v___x_2406_);
v_acc_2408_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__4));
if (v_onSorry_2407_ == 0)
{
lean_dec_ref(v_tree_2358_);
v___y_2395_ = v_onUnsolved_2405_;
v___y_2396_ = v___y_2403_;
v_acc_2397_ = v_acc_2408_;
v___y_2398_ = v_a_2360_;
v___y_2399_ = v_a_2361_;
goto v___jp_2394_;
}
else
{
lean_object* v_acc_2409_; 
v_acc_2409_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_2401_, v_acc_2408_, v_tree_2358_);
v___y_2395_ = v_onUnsolved_2405_;
v___y_2396_ = v___y_2403_;
v_acc_2397_ = v_acc_2409_;
v___y_2398_ = v_a_2360_;
v___y_2399_ = v_a_2361_;
goto v___jp_2394_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___boxed(lean_object* v_cmd_2414_, lean_object* v_opts_2415_, lean_object* v_tree_2416_, lean_object* v_msgs_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_cmd_2414_, v_opts_2415_, v_tree_2416_, v_msgs_2417_, v_a_2418_, v_a_2419_);
lean_dec(v_a_2419_);
lean_dec_ref(v_a_2418_);
lean_dec_ref(v_msgs_2417_);
lean_dec_ref(v_opts_2415_);
return v_res_2421_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(lean_object* v_00_u03b2_2422_, lean_object* v_m_2423_, lean_object* v_a_2424_){
_start:
{
uint8_t v___x_2425_; 
v___x_2425_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(v_m_2423_, v_a_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___boxed(lean_object* v_00_u03b2_2426_, lean_object* v_m_2427_, lean_object* v_a_2428_){
_start:
{
uint8_t v_res_2429_; lean_object* v_r_2430_; 
v_res_2429_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_00_u03b2_2426_, v_m_2427_, v_a_2428_);
lean_dec_ref(v_a_2428_);
lean_dec_ref(v_m_2427_);
v_r_2430_ = lean_box(v_res_2429_);
return v_r_2430_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1(lean_object* v_00_u03b2_2431_, lean_object* v_m_2432_, lean_object* v_query_2433_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_m_2432_, v_query_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___boxed(lean_object* v_00_u03b2_2435_, lean_object* v_m_2436_, lean_object* v_query_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1(v_00_u03b2_2435_, v_m_2436_, v_query_2437_);
lean_dec_ref(v_query_2437_);
lean_dec_ref(v_m_2436_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2(lean_object* v_00_u03b2_2439_, lean_object* v_m_2440_){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v_m_2440_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___boxed(lean_object* v_00_u03b2_2442_, lean_object* v_m_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2(v_00_u03b2_2442_, v_m_2443_);
lean_dec_ref(v_m_2443_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(lean_object* v_fst_2445_, lean_object* v_snd_2446_, lean_object* v___x_2447_, lean_object* v___x_2448_, lean_object* v_as_2449_, size_t v_sz_2450_, size_t v_i_2451_, lean_object* v_b_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v___x_2456_; 
v___x_2456_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v_fst_2445_, v_snd_2446_, v___x_2447_, v___x_2448_, v_as_2449_, v_sz_2450_, v_i_2451_, v_b_2452_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___boxed(lean_object* v_fst_2457_, lean_object* v_snd_2458_, lean_object* v___x_2459_, lean_object* v___x_2460_, lean_object* v_as_2461_, lean_object* v_sz_2462_, lean_object* v_i_2463_, lean_object* v_b_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
size_t v_sz_boxed_2468_; size_t v_i_boxed_2469_; lean_object* v_res_2470_; 
v_sz_boxed_2468_ = lean_unbox_usize(v_sz_2462_);
lean_dec(v_sz_2462_);
v_i_boxed_2469_ = lean_unbox_usize(v_i_2463_);
lean_dec(v_i_2463_);
v_res_2470_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v_fst_2457_, v_snd_2458_, v___x_2459_, v___x_2460_, v_as_2461_, v_sz_boxed_2468_, v_i_boxed_2469_, v_b_2464_, v___y_2465_, v___y_2466_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
lean_dec_ref(v_as_2461_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(lean_object* v_msgData_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg(v_msgData_2471_, v___y_2473_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___boxed(lean_object* v_msgData_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(v_msgData_2476_, v___y_2477_, v___y_2478_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0(lean_object* v_00_u03b2_2481_, lean_object* v_m_2482_, lean_object* v_query_2483_){
_start:
{
lean_object* v___x_2484_; 
v___x_2484_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(v_m_2482_, v_query_2483_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2485_, lean_object* v_m_2486_, lean_object* v_query_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0(v_00_u03b2_2485_, v_m_2486_, v_query_2487_);
lean_dec_ref(v_query_2487_);
lean_dec_ref(v_m_2486_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2(lean_object* v_00_u03b2_2489_, lean_object* v_m_2490_, lean_object* v_query_2491_, lean_object* v_x_2492_, lean_object* v_x_2493_, lean_object* v_x_2494_, lean_object* v_x_2495_){
_start:
{
lean_object* v___x_2496_; 
v___x_2496_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2___redArg(v_m_2490_, v_query_2491_, v_x_2492_, v_x_2493_, v_x_2494_);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2497_, lean_object* v_m_2498_, lean_object* v_query_2499_, lean_object* v_x_2500_, lean_object* v_x_2501_, lean_object* v_x_2502_, lean_object* v_x_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2(v_00_u03b2_2497_, v_m_2498_, v_query_2499_, v_x_2500_, v_x_2501_, v_x_2502_, v_x_2503_);
lean_dec_ref(v_query_2499_);
lean_dec_ref(v_m_2498_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__4(lean_object* v_00_u03b2_2505_, lean_object* v_init_2506_, lean_object* v_b_2507_){
_start:
{
lean_object* v___x_2508_; 
v___x_2508_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__4___redArg(v_init_2506_, v_b_2507_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2509_, lean_object* v_init_2510_, lean_object* v_b_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__4(v_00_u03b2_2509_, v_init_2510_, v_b_2511_);
lean_dec_ref(v_b_2511_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2513_, lean_object* v_b_2514_, lean_object* v_acc_2515_, lean_object* v_i_2516_){
_start:
{
lean_object* v___x_2517_; 
v___x_2517_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__4_spec__5___redArg(v_b_2514_, v_acc_2515_, v_i_2516_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_2518_, lean_object* v_b_2519_, lean_object* v_acc_2520_, lean_object* v_i_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__4_spec__5(v_00_u03b2_2518_, v_b_2519_, v_acc_2520_, v_i_2521_);
lean_dec_ref(v_b_2519_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(lean_object* v_x_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v___x_2531_; 
lean_inc(v___y_2525_);
lean_inc_ref(v___y_2524_);
v___x_2531_ = lean_apply_7(v_x_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, lean_box(0));
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed(lean_object* v_x_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(v_x_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(lean_object* v_mvarId_2541_, lean_object* v_x_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v___f_2550_; lean_object* v___x_2551_; 
lean_inc(v___y_2544_);
lean_inc_ref(v___y_2543_);
v___f_2550_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2550_, 0, v_x_2542_);
lean_closure_set(v___f_2550_, 1, v___y_2543_);
lean_closure_set(v___f_2550_, 2, v___y_2544_);
v___x_2551_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2541_, v___f_2550_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
if (lean_obj_tag(v___x_2551_) == 0)
{
return v___x_2551_;
}
else
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2554_ = v___x_2551_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2551_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___boxed(lean_object* v_mvarId_2560_, lean_object* v_x_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2560_, v_x_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(lean_object* v_00_u03b1_2570_, lean_object* v_mvarId_2571_, lean_object* v_x_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v___x_2580_; 
v___x_2580_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2571_, v_x_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed(lean_object* v_00_u03b1_2581_, lean_object* v_mvarId_2582_, lean_object* v_x_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(v_00_u03b1_2581_, v_mvarId_2582_, v_x_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(lean_object* v_____r_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2606_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2606_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___boxed(lean_object* v_____r_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(v_____r_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(lean_object* v_____r_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2625_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1___boxed(lean_object* v_____r_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(v_____r_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
return v_res_2633_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(uint8_t v___x_2634_, lean_object* v_x_2635_){
_start:
{
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2___boxed(lean_object* v___x_2636_, lean_object* v_x_2637_){
_start:
{
uint8_t v___x_11848__boxed_2638_; uint8_t v_res_2639_; lean_object* v_r_2640_; 
v___x_11848__boxed_2638_ = lean_unbox(v___x_2636_);
v_res_2639_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(v___x_11848__boxed_2638_, v_x_2637_);
lean_dec(v_x_2637_);
v_r_2640_ = lean_box(v_res_2639_);
return v_r_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(lean_object* v_msgData_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v___x_2647_; lean_object* v_env_2648_; lean_object* v___x_2649_; lean_object* v_mctx_2650_; lean_object* v_lctx_2651_; lean_object* v_options_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2647_ = lean_st_ref_get(v___y_2645_);
v_env_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc_ref(v_env_2648_);
lean_dec(v___x_2647_);
v___x_2649_ = lean_st_ref_get(v___y_2643_);
v_mctx_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc_ref(v_mctx_2650_);
lean_dec(v___x_2649_);
v_lctx_2651_ = lean_ctor_get(v___y_2642_, 2);
v_options_2652_ = lean_ctor_get(v___y_2644_, 2);
lean_inc_ref(v_options_2652_);
lean_inc_ref(v_lctx_2651_);
v___x_2653_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2653_, 0, v_env_2648_);
lean_ctor_set(v___x_2653_, 1, v_mctx_2650_);
lean_ctor_set(v___x_2653_, 2, v_lctx_2651_);
lean_ctor_set(v___x_2653_, 3, v_options_2652_);
v___x_2654_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2653_);
lean_ctor_set(v___x_2654_, 1, v_msgData_2641_);
v___x_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2654_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2___boxed(lean_object* v_msgData_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msgData_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(lean_object* v_cls_2663_, lean_object* v_msg_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v_ref_2670_; lean_object* v___x_2671_; lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2716_; 
v_ref_2670_ = lean_ctor_get(v___y_2667_, 5);
v___x_2671_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2674_ = v___x_2671_;
v_isShared_2675_ = v_isSharedCheck_2716_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2671_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2716_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2676_; lean_object* v_traceState_2677_; lean_object* v_env_2678_; lean_object* v_nextMacroScope_2679_; lean_object* v_ngen_2680_; lean_object* v_auxDeclNGen_2681_; lean_object* v_cache_2682_; lean_object* v_messages_2683_; lean_object* v_infoState_2684_; lean_object* v_snapshotTasks_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2715_; 
v___x_2676_ = lean_st_ref_take(v___y_2668_);
v_traceState_2677_ = lean_ctor_get(v___x_2676_, 4);
v_env_2678_ = lean_ctor_get(v___x_2676_, 0);
v_nextMacroScope_2679_ = lean_ctor_get(v___x_2676_, 1);
v_ngen_2680_ = lean_ctor_get(v___x_2676_, 2);
v_auxDeclNGen_2681_ = lean_ctor_get(v___x_2676_, 3);
v_cache_2682_ = lean_ctor_get(v___x_2676_, 5);
v_messages_2683_ = lean_ctor_get(v___x_2676_, 6);
v_infoState_2684_ = lean_ctor_get(v___x_2676_, 7);
v_snapshotTasks_2685_ = lean_ctor_get(v___x_2676_, 8);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2687_ = v___x_2676_;
v_isShared_2688_ = v_isSharedCheck_2715_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_snapshotTasks_2685_);
lean_inc(v_infoState_2684_);
lean_inc(v_messages_2683_);
lean_inc(v_cache_2682_);
lean_inc(v_traceState_2677_);
lean_inc(v_auxDeclNGen_2681_);
lean_inc(v_ngen_2680_);
lean_inc(v_nextMacroScope_2679_);
lean_inc(v_env_2678_);
lean_dec(v___x_2676_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2715_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
uint64_t v_tid_2689_; lean_object* v_traces_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2714_; 
v_tid_2689_ = lean_ctor_get_uint64(v_traceState_2677_, sizeof(void*)*1);
v_traces_2690_ = lean_ctor_get(v_traceState_2677_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v_traceState_2677_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2692_ = v_traceState_2677_;
v_isShared_2693_ = v_isSharedCheck_2714_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_traces_2690_);
lean_dec(v_traceState_2677_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2714_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2694_; double v___x_2695_; uint8_t v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2704_; 
v___x_2694_ = lean_box(0);
v___x_2695_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0);
v___x_2696_ = 0;
v___x_2697_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2698_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2698_, 0, v_cls_2663_);
lean_ctor_set(v___x_2698_, 1, v___x_2694_);
lean_ctor_set(v___x_2698_, 2, v___x_2697_);
lean_ctor_set_float(v___x_2698_, sizeof(void*)*3, v___x_2695_);
lean_ctor_set_float(v___x_2698_, sizeof(void*)*3 + 8, v___x_2695_);
lean_ctor_set_uint8(v___x_2698_, sizeof(void*)*3 + 16, v___x_2696_);
v___x_2699_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1));
v___x_2700_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2698_);
lean_ctor_set(v___x_2700_, 1, v_a_2672_);
lean_ctor_set(v___x_2700_, 2, v___x_2699_);
lean_inc(v_ref_2670_);
v___x_2701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2701_, 0, v_ref_2670_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
v___x_2702_ = l_Lean_PersistentArray_push___redArg(v_traces_2690_, v___x_2701_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v___x_2702_);
v___x_2704_ = v___x_2692_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2702_);
lean_ctor_set_uint64(v_reuseFailAlloc_2713_, sizeof(void*)*1, v_tid_2689_);
v___x_2704_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
lean_object* v___x_2706_; 
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 4, v___x_2704_);
v___x_2706_ = v___x_2687_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_env_2678_);
lean_ctor_set(v_reuseFailAlloc_2712_, 1, v_nextMacroScope_2679_);
lean_ctor_set(v_reuseFailAlloc_2712_, 2, v_ngen_2680_);
lean_ctor_set(v_reuseFailAlloc_2712_, 3, v_auxDeclNGen_2681_);
lean_ctor_set(v_reuseFailAlloc_2712_, 4, v___x_2704_);
lean_ctor_set(v_reuseFailAlloc_2712_, 5, v_cache_2682_);
lean_ctor_set(v_reuseFailAlloc_2712_, 6, v_messages_2683_);
lean_ctor_set(v_reuseFailAlloc_2712_, 7, v_infoState_2684_);
lean_ctor_set(v_reuseFailAlloc_2712_, 8, v_snapshotTasks_2685_);
v___x_2706_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2710_; 
v___x_2707_ = lean_st_ref_put(v___y_2668_, v___x_2706_);
v___x_2708_ = lean_box(0);
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v___x_2708_);
v___x_2710_ = v___x_2674_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2708_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg___boxed(lean_object* v_cls_2717_, lean_object* v_msg_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_2717_, v_msg_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
return v_res_2724_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2726_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__0));
v___x_2727_ = l_Lean_stringToMessageData(v___x_2726_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(lean_object* v___x_2728_, lean_object* v___x_2729_, lean_object* v___x_2730_, lean_object* v___f_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v___x_2739_; lean_object* v_a_2741_; lean_object* v___y_2745_; lean_object* v___x_2759_; 
v___x_2739_ = lean_st_mk_ref(v___x_2728_);
v___x_2759_ = l_Lean_Elab_Tactic_saveState___redArg(v___x_2739_, v___y_2733_, v___y_2735_, v___y_2737_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v___x_2761_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_a_2760_);
lean_dec_ref_known(v___x_2759_, 1);
v___x_2761_ = l_Lean_Elab_Tactic_Try_collectTryCoreSuggestions(v___x_2729_, v___x_2730_, v___x_2739_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; 
lean_dec(v_a_2760_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec_ref(v___f_2731_);
lean_dec_ref(v___x_2730_);
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
lean_inc(v_a_2762_);
lean_dec_ref_known(v___x_2761_, 1);
v_a_2741_ = v_a_2762_;
goto v___jp_2740_;
}
else
{
lean_object* v_a_2763_; uint8_t v___y_2765_; uint8_t v___x_2808_; 
v_a_2763_ = lean_ctor_get(v___x_2761_, 0);
lean_inc(v_a_2763_);
v___x_2808_ = l_Lean_Exception_isInterrupt(v_a_2763_);
if (v___x_2808_ == 0)
{
uint8_t v___x_2809_; 
lean_inc(v_a_2763_);
v___x_2809_ = l_Lean_Exception_isRuntime(v_a_2763_);
v___y_2765_ = v___x_2809_;
goto v___jp_2764_;
}
else
{
v___y_2765_ = v___x_2808_;
goto v___jp_2764_;
}
v___jp_2764_:
{
if (v___y_2765_ == 0)
{
lean_object* v___x_2766_; 
lean_dec_ref_known(v___x_2761_, 1);
v___x_2766_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2760_, v___y_2765_, v___x_2739_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2798_; 
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2798_ == 0)
{
lean_object* v_unused_2799_; 
v_unused_2799_ = lean_ctor_get(v___x_2766_, 0);
lean_dec(v_unused_2799_);
v___x_2768_ = v___x_2766_;
v_isShared_2769_ = v_isSharedCheck_2798_;
goto v_resetjp_2767_;
}
else
{
lean_dec(v___x_2766_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2798_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
uint8_t v___x_2770_; 
v___x_2770_ = l_Lean_Exception_isInterrupt(v_a_2763_);
if (v___x_2770_ == 0)
{
uint8_t v___x_2771_; 
lean_inc(v_a_2763_);
v___x_2771_ = l_Lean_Exception_isMaxRecDepth(v_a_2763_);
if (v___x_2771_ == 0)
{
lean_object* v_options_2772_; uint8_t v_hasTrace_2773_; 
lean_del_object(v___x_2768_);
v_options_2772_ = lean_ctor_get(v___y_2736_, 2);
v_hasTrace_2773_ = lean_ctor_get_uint8(v_options_2772_, sizeof(void*)*1);
if (v_hasTrace_2773_ == 0)
{
lean_dec(v_a_2763_);
goto v___jp_2756_;
}
else
{
lean_object* v_inheritedTraceOptions_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; uint8_t v___x_2777_; 
v_inheritedTraceOptions_2774_ = lean_ctor_get(v___y_2736_, 13);
v___x_2775_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2776_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3);
v___x_2777_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2774_, v_options_2772_, v___x_2776_);
if (v___x_2777_ == 0)
{
lean_dec(v_a_2763_);
goto v___jp_2756_;
}
else
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2778_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_2779_ = l_Lean_Exception_toMessageData(v_a_2763_);
v___x_2780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2778_);
lean_ctor_set(v___x_2780_, 1, v___x_2779_);
v___x_2781_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v___x_2775_, v___x_2780_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2783_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_a_2782_);
lean_dec_ref_known(v___x_2781_, 1);
lean_inc(v___x_2739_);
v___x_2783_ = lean_apply_10(v___f_2731_, v_a_2782_, v___x_2730_, v___x_2739_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, lean_box(0));
v___y_2745_ = v___x_2783_;
goto v___jp_2744_;
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_dec(v___x_2739_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec_ref(v___f_2731_);
lean_dec_ref(v___x_2730_);
v_a_2784_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2781_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2781_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
}
}
else
{
lean_object* v___x_2793_; 
lean_dec(v___x_2739_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec_ref(v___f_2731_);
lean_dec_ref(v___x_2730_);
if (v_isShared_2769_ == 0)
{
lean_ctor_set_tag(v___x_2768_, 1);
lean_ctor_set(v___x_2768_, 0, v_a_2763_);
v___x_2793_ = v___x_2768_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2763_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
else
{
lean_object* v___x_2796_; 
lean_dec(v___x_2739_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec_ref(v___f_2731_);
lean_dec_ref(v___x_2730_);
if (v_isShared_2769_ == 0)
{
lean_ctor_set_tag(v___x_2768_, 1);
lean_ctor_set(v___x_2768_, 0, v_a_2763_);
v___x_2796_ = v___x_2768_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2763_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
lean_dec(v_a_2763_);
lean_dec(v___x_2739_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec_ref(v___f_2731_);
lean_dec_ref(v___x_2730_);
v_a_2800_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2766_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2766_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
else
{
lean_dec(v_a_2763_);
lean_dec(v_a_2760_);
lean_dec(v___x_2739_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec_ref(v___f_2731_);
lean_dec_ref(v___x_2730_);
return v___x_2761_;
}
}
}
}
else
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
lean_dec(v___x_2739_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec_ref(v___f_2731_);
lean_dec_ref(v___x_2730_);
lean_dec_ref(v___x_2729_);
v_a_2810_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v___x_2759_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2759_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
v___jp_2740_:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2742_ = lean_st_ref_get(v___x_2739_);
lean_dec(v___x_2739_);
lean_dec(v___x_2742_);
v___x_2743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2743_, 0, v_a_2741_);
return v___x_2743_;
}
v___jp_2744_:
{
if (lean_obj_tag(v___y_2745_) == 0)
{
lean_object* v_a_2746_; lean_object* v_a_2747_; 
v_a_2746_ = lean_ctor_get(v___y_2745_, 0);
lean_inc(v_a_2746_);
lean_dec_ref_known(v___y_2745_, 1);
v_a_2747_ = lean_ctor_get(v_a_2746_, 0);
lean_inc(v_a_2747_);
lean_dec(v_a_2746_);
v_a_2741_ = v_a_2747_;
goto v___jp_2740_;
}
else
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2755_; 
lean_dec(v___x_2739_);
v_a_2748_ = lean_ctor_get(v___y_2745_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___y_2745_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2750_ = v___y_2745_;
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___y_2745_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2753_; 
if (v_isShared_2751_ == 0)
{
v___x_2753_ = v___x_2750_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_a_2748_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
v___jp_2756_:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2757_ = lean_box(0);
lean_inc(v___x_2739_);
v___x_2758_ = lean_apply_10(v___f_2731_, v___x_2757_, v___x_2730_, v___x_2739_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, lean_box(0));
v___y_2745_ = v___x_2758_;
goto v___jp_2744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed(lean_object* v___x_2818_, lean_object* v___x_2819_, lean_object* v___x_2820_, lean_object* v___f_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(v___x_2818_, v___x_2819_, v___x_2820_, v___f_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(lean_object* v___x_2830_, uint8_t v___x_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v___x_2839_; 
v___x_2839_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2830_, v___x_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed(lean_object* v___x_2840_, lean_object* v___x_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
uint8_t v___x_12177__boxed_2849_; lean_object* v_res_2850_; 
v___x_12177__boxed_2849_ = lean_unbox(v___x_2841_);
v_res_2850_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(v___x_2840_, v___x_12177__boxed_2849_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(lean_object* v_cls_2851_, lean_object* v_msg_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v_ref_2858_; lean_object* v___x_2859_; lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2904_; 
v_ref_2858_ = lean_ctor_get(v___y_2855_, 5);
v___x_2859_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2862_ = v___x_2859_;
v_isShared_2863_ = v_isSharedCheck_2904_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2859_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2904_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2864_; lean_object* v_traceState_2865_; lean_object* v_env_2866_; lean_object* v_nextMacroScope_2867_; lean_object* v_ngen_2868_; lean_object* v_auxDeclNGen_2869_; lean_object* v_cache_2870_; lean_object* v_messages_2871_; lean_object* v_infoState_2872_; lean_object* v_snapshotTasks_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2903_; 
v___x_2864_ = lean_st_ref_take(v___y_2856_);
v_traceState_2865_ = lean_ctor_get(v___x_2864_, 4);
v_env_2866_ = lean_ctor_get(v___x_2864_, 0);
v_nextMacroScope_2867_ = lean_ctor_get(v___x_2864_, 1);
v_ngen_2868_ = lean_ctor_get(v___x_2864_, 2);
v_auxDeclNGen_2869_ = lean_ctor_get(v___x_2864_, 3);
v_cache_2870_ = lean_ctor_get(v___x_2864_, 5);
v_messages_2871_ = lean_ctor_get(v___x_2864_, 6);
v_infoState_2872_ = lean_ctor_get(v___x_2864_, 7);
v_snapshotTasks_2873_ = lean_ctor_get(v___x_2864_, 8);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2875_ = v___x_2864_;
v_isShared_2876_ = v_isSharedCheck_2903_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_snapshotTasks_2873_);
lean_inc(v_infoState_2872_);
lean_inc(v_messages_2871_);
lean_inc(v_cache_2870_);
lean_inc(v_traceState_2865_);
lean_inc(v_auxDeclNGen_2869_);
lean_inc(v_ngen_2868_);
lean_inc(v_nextMacroScope_2867_);
lean_inc(v_env_2866_);
lean_dec(v___x_2864_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2903_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
uint64_t v_tid_2877_; lean_object* v_traces_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2902_; 
v_tid_2877_ = lean_ctor_get_uint64(v_traceState_2865_, sizeof(void*)*1);
v_traces_2878_ = lean_ctor_get(v_traceState_2865_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v_traceState_2865_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2880_ = v_traceState_2865_;
v_isShared_2881_ = v_isSharedCheck_2902_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_traces_2878_);
lean_dec(v_traceState_2865_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2902_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2882_; double v___x_2883_; uint8_t v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2892_; 
v___x_2882_ = lean_box(0);
v___x_2883_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0);
v___x_2884_ = 0;
v___x_2885_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2886_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2886_, 0, v_cls_2851_);
lean_ctor_set(v___x_2886_, 1, v___x_2882_);
lean_ctor_set(v___x_2886_, 2, v___x_2885_);
lean_ctor_set_float(v___x_2886_, sizeof(void*)*3, v___x_2883_);
lean_ctor_set_float(v___x_2886_, sizeof(void*)*3 + 8, v___x_2883_);
lean_ctor_set_uint8(v___x_2886_, sizeof(void*)*3 + 16, v___x_2884_);
v___x_2887_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1));
v___x_2888_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2886_);
lean_ctor_set(v___x_2888_, 1, v_a_2860_);
lean_ctor_set(v___x_2888_, 2, v___x_2887_);
lean_inc(v_ref_2858_);
v___x_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2889_, 0, v_ref_2858_);
lean_ctor_set(v___x_2889_, 1, v___x_2888_);
v___x_2890_ = l_Lean_PersistentArray_push___redArg(v_traces_2878_, v___x_2889_);
if (v_isShared_2881_ == 0)
{
lean_ctor_set(v___x_2880_, 0, v___x_2890_);
v___x_2892_ = v___x_2880_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2890_);
lean_ctor_set_uint64(v_reuseFailAlloc_2901_, sizeof(void*)*1, v_tid_2877_);
v___x_2892_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
lean_object* v___x_2894_; 
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 4, v___x_2892_);
v___x_2894_ = v___x_2875_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_env_2866_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v_nextMacroScope_2867_);
lean_ctor_set(v_reuseFailAlloc_2900_, 2, v_ngen_2868_);
lean_ctor_set(v_reuseFailAlloc_2900_, 3, v_auxDeclNGen_2869_);
lean_ctor_set(v_reuseFailAlloc_2900_, 4, v___x_2892_);
lean_ctor_set(v_reuseFailAlloc_2900_, 5, v_cache_2870_);
lean_ctor_set(v_reuseFailAlloc_2900_, 6, v_messages_2871_);
lean_ctor_set(v_reuseFailAlloc_2900_, 7, v_infoState_2872_);
lean_ctor_set(v_reuseFailAlloc_2900_, 8, v_snapshotTasks_2873_);
v___x_2894_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2898_; 
v___x_2895_ = lean_st_ref_put(v___y_2856_, v___x_2894_);
v___x_2896_ = lean_box(0);
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 0, v___x_2896_);
v___x_2898_ = v___x_2862_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2896_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3___boxed(lean_object* v_cls_2905_, lean_object* v_msg_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v_cls_2905_, v_msg_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
return v_res_2912_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2914_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__0));
v___x_2915_ = l_Lean_stringToMessageData(v___x_2914_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(lean_object* v_term_2916_, lean_object* v___x_2917_, lean_object* v___x_2918_, lean_object* v___f_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
lean_object* v___y_2926_; lean_object* v___x_2944_; 
v___x_2944_ = l_Lean_Elab_Term_TermElabM_run___redArg(v_term_2916_, v___x_2917_, v___x_2918_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2953_; 
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec_ref(v___f_2919_);
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2947_ = v___x_2944_;
v_isShared_2948_ = v_isSharedCheck_2953_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2944_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2953_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v_fst_2949_; lean_object* v___x_2951_; 
v_fst_2949_ = lean_ctor_get(v_a_2945_, 0);
lean_inc(v_fst_2949_);
lean_dec(v_a_2945_);
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 0, v_fst_2949_);
v___x_2951_ = v___x_2947_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_fst_2949_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
else
{
lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2996_; 
v_a_2954_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2956_ = v___x_2944_;
v_isShared_2957_ = v_isSharedCheck_2996_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2944_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2996_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
uint8_t v___y_2962_; uint8_t v___x_2994_; 
v___x_2994_ = l_Lean_Exception_isInterrupt(v_a_2954_);
if (v___x_2994_ == 0)
{
uint8_t v___x_2995_; 
lean_inc(v_a_2954_);
v___x_2995_ = l_Lean_Exception_isRuntime(v_a_2954_);
v___y_2962_ = v___x_2995_;
goto v___jp_2961_;
}
else
{
v___y_2962_ = v___x_2994_;
goto v___jp_2961_;
}
v___jp_2958_:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2959_ = lean_box(0);
v___x_2960_ = lean_apply_6(v___f_2919_, v___x_2959_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, lean_box(0));
v___y_2926_ = v___x_2960_;
goto v___jp_2925_;
}
v___jp_2961_:
{
if (v___y_2962_ == 0)
{
uint8_t v___x_2963_; 
v___x_2963_ = l_Lean_Exception_isInterrupt(v_a_2954_);
if (v___x_2963_ == 0)
{
uint8_t v___x_2964_; 
lean_inc(v_a_2954_);
v___x_2964_ = l_Lean_Exception_isMaxRecDepth(v_a_2954_);
if (v___x_2964_ == 0)
{
lean_object* v_options_2965_; uint8_t v_hasTrace_2966_; 
lean_del_object(v___x_2956_);
v_options_2965_ = lean_ctor_get(v___y_2922_, 2);
v_hasTrace_2966_ = lean_ctor_get_uint8(v_options_2965_, sizeof(void*)*1);
if (v_hasTrace_2966_ == 0)
{
lean_dec(v_a_2954_);
goto v___jp_2958_;
}
else
{
lean_object* v_inheritedTraceOptions_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; uint8_t v___x_2970_; 
v_inheritedTraceOptions_2967_ = lean_ctor_get(v___y_2922_, 13);
v___x_2968_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2969_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3);
v___x_2970_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2967_, v_options_2965_, v___x_2969_);
if (v___x_2970_ == 0)
{
lean_dec(v_a_2954_);
goto v___jp_2958_;
}
else
{
lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2971_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1);
v___x_2972_ = l_Lean_Exception_toMessageData(v_a_2954_);
v___x_2973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2971_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
v___x_2974_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_2968_, v___x_2973_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_a_2975_; lean_object* v___x_2976_; 
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
lean_inc(v_a_2975_);
lean_dec_ref_known(v___x_2974_, 1);
v___x_2976_ = lean_apply_6(v___f_2919_, v_a_2975_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, lean_box(0));
v___y_2926_ = v___x_2976_;
goto v___jp_2925_;
}
else
{
lean_object* v_a_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2984_; 
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec_ref(v___f_2919_);
v_a_2977_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2979_ = v___x_2974_;
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_a_2977_);
lean_dec(v___x_2974_);
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
}
else
{
lean_object* v___x_2986_; 
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec_ref(v___f_2919_);
if (v_isShared_2957_ == 0)
{
v___x_2986_ = v___x_2956_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_a_2954_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
else
{
lean_object* v___x_2989_; 
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec_ref(v___f_2919_);
if (v_isShared_2957_ == 0)
{
v___x_2989_ = v___x_2956_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_a_2954_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
else
{
lean_object* v___x_2992_; 
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec_ref(v___f_2919_);
if (v_isShared_2957_ == 0)
{
v___x_2992_ = v___x_2956_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_a_2954_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
}
}
}
v___jp_2925_:
{
if (lean_obj_tag(v___y_2926_) == 0)
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2935_; 
v_a_2927_ = lean_ctor_get(v___y_2926_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___y_2926_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2929_ = v___y_2926_;
v_isShared_2930_ = v_isSharedCheck_2935_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___y_2926_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2935_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v_a_2931_; lean_object* v___x_2933_; 
v_a_2931_ = lean_ctor_get(v_a_2927_, 0);
lean_inc(v_a_2931_);
lean_dec(v_a_2927_);
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 0, v_a_2931_);
v___x_2933_ = v___x_2929_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2931_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
else
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2943_; 
v_a_2936_ = lean_ctor_get(v___y_2926_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___y_2926_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2938_ = v___y_2926_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___y_2926_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2941_; 
if (v_isShared_2939_ == 0)
{
v___x_2941_ = v___x_2938_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2936_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___boxed(lean_object* v_term_2997_, lean_object* v___x_2998_, lean_object* v___x_2999_, lean_object* v___f_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(v_term_2997_, v___x_2998_, v___x_2999_, v___f_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_3007_, lean_object* v_vals_3008_, lean_object* v_i_3009_, lean_object* v_k_3010_){
_start:
{
lean_object* v___x_3011_; uint8_t v___x_3012_; 
v___x_3011_ = lean_array_get_size(v_keys_3007_);
v___x_3012_ = lean_nat_dec_lt(v_i_3009_, v___x_3011_);
if (v___x_3012_ == 0)
{
lean_object* v___x_3013_; 
lean_dec(v_i_3009_);
v___x_3013_ = lean_box(0);
return v___x_3013_;
}
else
{
lean_object* v_k_x27_3014_; uint8_t v___x_3015_; 
v_k_x27_3014_ = lean_array_fget_borrowed(v_keys_3007_, v_i_3009_);
v___x_3015_ = l_Lean_instBEqMVarId_beq(v_k_3010_, v_k_x27_3014_);
if (v___x_3015_ == 0)
{
lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3016_ = lean_unsigned_to_nat(1u);
v___x_3017_ = lean_nat_add(v_i_3009_, v___x_3016_);
lean_dec(v_i_3009_);
v_i_3009_ = v___x_3017_;
goto _start;
}
else
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3019_ = lean_array_fget_borrowed(v_vals_3008_, v_i_3009_);
lean_dec(v_i_3009_);
lean_inc(v___x_3019_);
v___x_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3019_);
return v___x_3020_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_3021_, lean_object* v_vals_3022_, lean_object* v_i_3023_, lean_object* v_k_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_keys_3021_, v_vals_3022_, v_i_3023_, v_k_3024_);
lean_dec(v_k_3024_);
lean_dec_ref(v_vals_3022_);
lean_dec_ref(v_keys_3021_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(lean_object* v_x_3026_, size_t v_x_3027_, lean_object* v_x_3028_){
_start:
{
if (lean_obj_tag(v_x_3026_) == 0)
{
lean_object* v_es_3029_; lean_object* v___x_3030_; size_t v___x_3031_; size_t v___x_3032_; lean_object* v_j_3033_; lean_object* v___x_3034_; 
v_es_3029_ = lean_ctor_get(v_x_3026_, 0);
v___x_3030_ = lean_box(2);
v___x_3031_ = ((size_t)31ULL);
v___x_3032_ = lean_usize_land(v_x_3027_, v___x_3031_);
v_j_3033_ = lean_usize_to_nat(v___x_3032_);
v___x_3034_ = lean_array_get_borrowed(v___x_3030_, v_es_3029_, v_j_3033_);
lean_dec(v_j_3033_);
switch(lean_obj_tag(v___x_3034_))
{
case 0:
{
lean_object* v_key_3035_; lean_object* v_val_3036_; uint8_t v___x_3037_; 
v_key_3035_ = lean_ctor_get(v___x_3034_, 0);
v_val_3036_ = lean_ctor_get(v___x_3034_, 1);
v___x_3037_ = l_Lean_instBEqMVarId_beq(v_x_3028_, v_key_3035_);
if (v___x_3037_ == 0)
{
lean_object* v___x_3038_; 
v___x_3038_ = lean_box(0);
return v___x_3038_;
}
else
{
lean_object* v___x_3039_; 
lean_inc(v_val_3036_);
v___x_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3039_, 0, v_val_3036_);
return v___x_3039_;
}
}
case 1:
{
lean_object* v_node_3040_; size_t v___x_3041_; size_t v___x_3042_; 
v_node_3040_ = lean_ctor_get(v___x_3034_, 0);
v___x_3041_ = ((size_t)5ULL);
v___x_3042_ = lean_usize_shift_right(v_x_3027_, v___x_3041_);
v_x_3026_ = v_node_3040_;
v_x_3027_ = v___x_3042_;
goto _start;
}
default: 
{
lean_object* v___x_3044_; 
v___x_3044_ = lean_box(0);
return v___x_3044_;
}
}
}
else
{
lean_object* v_ks_3045_; lean_object* v_vs_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v_ks_3045_ = lean_ctor_get(v_x_3026_, 0);
v_vs_3046_ = lean_ctor_get(v_x_3026_, 1);
v___x_3047_ = lean_unsigned_to_nat(0u);
v___x_3048_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_ks_3045_, v_vs_3046_, v___x_3047_, v_x_3028_);
return v___x_3048_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg___boxed(lean_object* v_x_3049_, lean_object* v_x_3050_, lean_object* v_x_3051_){
_start:
{
size_t v_x_12496__boxed_3052_; lean_object* v_res_3053_; 
v_x_12496__boxed_3052_ = lean_unbox_usize(v_x_3050_);
lean_dec(v_x_3050_);
v_res_3053_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_3049_, v_x_12496__boxed_3052_, v_x_3051_);
lean_dec(v_x_3051_);
lean_dec_ref(v_x_3049_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(lean_object* v_x_3054_, lean_object* v_x_3055_){
_start:
{
uint64_t v___x_3056_; size_t v___x_3057_; lean_object* v___x_3058_; 
v___x_3056_ = l_Lean_instHashableMVarId_hash(v_x_3055_);
v___x_3057_ = lean_uint64_to_usize(v___x_3056_);
v___x_3058_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_3054_, v___x_3057_, v_x_3055_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg___boxed(lean_object* v_x_3059_, lean_object* v_x_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_x_3059_, v_x_3060_);
lean_dec(v_x_3060_);
lean_dec_ref(v_x_3059_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(lean_object* v_c_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_){
_start:
{
lean_object* v_mctx_3091_; lean_object* v_env_3092_; lean_object* v_opts_3093_; lean_object* v_namingCtx_3094_; lean_object* v_goal_3095_; lean_object* v_decls_3096_; lean_object* v___x_3097_; 
v_mctx_3091_ = lean_ctor_get(v_c_3087_, 3);
lean_inc_ref(v_mctx_3091_);
v_env_3092_ = lean_ctor_get(v_c_3087_, 2);
lean_inc_ref(v_env_3092_);
v_opts_3093_ = lean_ctor_get(v_c_3087_, 4);
lean_inc_ref(v_opts_3093_);
v_namingCtx_3094_ = lean_ctor_get(v_c_3087_, 5);
lean_inc_ref(v_namingCtx_3094_);
v_goal_3095_ = lean_ctor_get(v_c_3087_, 6);
lean_inc(v_goal_3095_);
lean_dec_ref(v_c_3087_);
v_decls_3096_ = lean_ctor_get(v_mctx_3091_, 5);
v___x_3097_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_decls_3096_, v_goal_3095_);
if (lean_obj_tag(v___x_3097_) == 1)
{
lean_object* v_val_3098_; lean_object* v_lctx_3099_; lean_object* v___f_3100_; lean_object* v___f_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___f_3106_; lean_object* v___x_3107_; uint8_t v___x_3108_; lean_object* v___x_3109_; lean_object* v_term_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___f_3113_; lean_object* v___x_3114_; 
v_val_3098_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_val_3098_);
lean_dec_ref_known(v___x_3097_, 1);
v_lctx_3099_ = lean_ctor_get(v_val_3098_, 1);
lean_inc_ref(v_lctx_3099_);
lean_dec(v_val_3098_);
v___f_3100_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__0));
v___f_3101_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__1));
v___x_3102_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__3));
v___x_3103_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__4));
v___x_3104_ = lean_box(0);
lean_inc(v_goal_3095_);
v___x_3105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3105_, 0, v_goal_3095_);
lean_ctor_set(v___x_3105_, 1, v___x_3104_);
v___f_3106_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed), 11, 4);
lean_closure_set(v___f_3106_, 0, v___x_3105_);
lean_closure_set(v___f_3106_, 1, v___x_3102_);
lean_closure_set(v___f_3106_, 2, v___x_3103_);
lean_closure_set(v___f_3106_, 3, v___f_3100_);
v___x_3107_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed), 10, 3);
lean_closure_set(v___x_3107_, 0, lean_box(0));
lean_closure_set(v___x_3107_, 1, v_goal_3095_);
lean_closure_set(v___x_3107_, 2, v___f_3106_);
v___x_3108_ = 1;
v___x_3109_ = lean_box(v___x_3108_);
v_term_3110_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed), 9, 2);
lean_closure_set(v_term_3110_, 0, v___x_3107_);
lean_closure_set(v_term_3110_, 1, v___x_3109_);
v___x_3111_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__6));
v___x_3112_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__7));
v___f_3113_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___boxed), 9, 4);
lean_closure_set(v___f_3113_, 0, v_term_3110_);
lean_closure_set(v___f_3113_, 1, v___x_3111_);
lean_closure_set(v___f_3113_, 2, v___x_3112_);
lean_closure_set(v___f_3113_, 3, v___f_3101_);
v___x_3114_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_3092_, v_mctx_3091_, v_lctx_3099_, v_opts_3093_, v_namingCtx_3094_, v___f_3113_, v_a_3088_, v_a_3089_);
lean_dec_ref(v_namingCtx_3094_);
return v___x_3114_;
}
else
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
lean_dec(v___x_3097_);
lean_dec(v_goal_3095_);
lean_dec_ref(v_namingCtx_3094_);
lean_dec_ref(v_opts_3093_);
lean_dec_ref(v_env_3092_);
lean_dec_ref(v_mctx_3091_);
v___x_3115_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__0));
v___x_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3115_);
return v___x_3116_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___boxed(lean_object* v_c_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_){
_start:
{
lean_object* v_res_3121_; 
v_res_3121_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(v_c_3117_, v_a_3118_, v_a_3119_);
lean_dec(v_a_3119_);
lean_dec_ref(v_a_3118_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0(lean_object* v_00_u03b2_3122_, lean_object* v_x_3123_, lean_object* v_x_3124_){
_start:
{
lean_object* v___x_3125_; 
v___x_3125_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_x_3123_, v_x_3124_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___boxed(lean_object* v_00_u03b2_3126_, lean_object* v_x_3127_, lean_object* v_x_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0(v_00_u03b2_3126_, v_x_3127_, v_x_3128_);
lean_dec(v_x_3128_);
lean_dec_ref(v_x_3127_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(lean_object* v_cls_3130_, lean_object* v_msg_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v___x_3141_; 
v___x_3141_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_3130_, v_msg_3131_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_);
return v___x_3141_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___boxed(lean_object* v_cls_3142_, lean_object* v_msg_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(v_cls_3142_, v_msg_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(lean_object* v_00_u03b2_3154_, lean_object* v_x_3155_, size_t v_x_3156_, lean_object* v_x_3157_){
_start:
{
lean_object* v___x_3158_; 
v___x_3158_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_3155_, v_x_3156_, v_x_3157_);
return v___x_3158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3159_, lean_object* v_x_3160_, lean_object* v_x_3161_, lean_object* v_x_3162_){
_start:
{
size_t v_x_12753__boxed_3163_; lean_object* v_res_3164_; 
v_x_12753__boxed_3163_ = lean_unbox_usize(v_x_3161_);
lean_dec(v_x_3161_);
v_res_3164_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(v_00_u03b2_3159_, v_x_3160_, v_x_12753__boxed_3163_, v_x_3162_);
lean_dec(v_x_3162_);
lean_dec_ref(v_x_3160_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3165_, lean_object* v_keys_3166_, lean_object* v_vals_3167_, lean_object* v_heq_3168_, lean_object* v_i_3169_, lean_object* v_k_3170_){
_start:
{
lean_object* v___x_3171_; 
v___x_3171_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_keys_3166_, v_vals_3167_, v_i_3169_, v_k_3170_);
return v___x_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3172_, lean_object* v_keys_3173_, lean_object* v_vals_3174_, lean_object* v_heq_3175_, lean_object* v_i_3176_, lean_object* v_k_3177_){
_start:
{
lean_object* v_res_3178_; 
v_res_3178_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2(v_00_u03b2_3172_, v_keys_3173_, v_vals_3174_, v_heq_3175_, v_i_3176_, v_k_3177_);
lean_dec(v_k_3177_);
lean_dec_ref(v_vals_3174_);
lean_dec_ref(v_keys_3173_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(uint8_t v___x_3181_, lean_object* v___x_3182_, lean_object* v_ref_3183_, lean_object* v_a_3184_, lean_object* v___x_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
if (v___x_3181_ == 0)
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; uint8_t v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3182_);
v___x_3190_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__0));
v___x_3191_ = lean_box(0);
v___x_3192_ = 4;
v___x_3193_ = l_Lean_MessageData_nil;
v___x_3194_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_3183_, v_a_3184_, v___x_3189_, v___x_3190_, v___x_3191_, v___x_3192_, v___x_3193_, v___y_3186_, v___y_3187_);
return v___x_3194_;
}
else
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; uint8_t v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3195_ = l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default;
v___x_3196_ = lean_array_get(v___x_3195_, v_a_3184_, v___x_3185_);
lean_dec_ref(v_a_3184_);
v___x_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3182_);
v___x_3198_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__1));
v___x_3199_ = lean_box(0);
v___x_3200_ = 4;
v___x_3201_ = l_Lean_MessageData_nil;
v___x_3202_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_3183_, v___x_3196_, v___x_3197_, v___x_3198_, v___x_3199_, v___x_3200_, v___x_3201_, v___y_3186_, v___y_3187_);
return v___x_3202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed(lean_object* v___x_3203_, lean_object* v___x_3204_, lean_object* v_ref_3205_, lean_object* v_a_3206_, lean_object* v___x_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
uint8_t v___x_3935__boxed_3211_; lean_object* v_res_3212_; 
v___x_3935__boxed_3211_ = lean_unbox(v___x_3203_);
v_res_3212_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(v___x_3935__boxed_3211_, v___x_3204_, v_ref_3205_, v_a_3206_, v___x_3207_, v___y_3208_, v___y_3209_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec(v___x_3207_);
return v_res_3212_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(uint8_t v___y_3213_, uint8_t v_suppressElabErrors_3214_, lean_object* v_x_3215_){
_start:
{
if (lean_obj_tag(v_x_3215_) == 1)
{
lean_object* v_pre_3216_; 
v_pre_3216_ = lean_ctor_get(v_x_3215_, 0);
if (lean_obj_tag(v_pre_3216_) == 0)
{
lean_object* v_str_3217_; lean_object* v___x_3218_; uint8_t v___x_3219_; 
v_str_3217_ = lean_ctor_get(v_x_3215_, 1);
v___x_3218_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__1));
v___x_3219_ = lean_string_dec_eq(v_str_3217_, v___x_3218_);
if (v___x_3219_ == 0)
{
return v___y_3213_;
}
else
{
return v_suppressElabErrors_3214_;
}
}
else
{
return v___y_3213_;
}
}
else
{
return v___y_3213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed(lean_object* v___y_3220_, lean_object* v_suppressElabErrors_3221_, lean_object* v_x_3222_){
_start:
{
uint8_t v___y_3987__boxed_3223_; uint8_t v_suppressElabErrors_boxed_3224_; uint8_t v_res_3225_; lean_object* v_r_3226_; 
v___y_3987__boxed_3223_ = lean_unbox(v___y_3220_);
v_suppressElabErrors_boxed_3224_ = lean_unbox(v_suppressElabErrors_3221_);
v_res_3225_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(v___y_3987__boxed_3223_, v_suppressElabErrors_boxed_3224_, v_x_3222_);
lean_dec(v_x_3222_);
v_r_3226_ = lean_box(v_res_3225_);
return v_r_3226_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(lean_object* v_ref_3227_, lean_object* v_msgData_3228_, uint8_t v_severity_3229_, uint8_t v_isSilent_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v___y_3235_; lean_object* v___y_3236_; uint8_t v___y_3237_; lean_object* v___y_3238_; uint8_t v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; uint8_t v___y_3299_; uint8_t v___y_3300_; lean_object* v___y_3301_; uint8_t v___y_3302_; lean_object* v___y_3303_; uint8_t v___y_3327_; uint8_t v___y_3328_; lean_object* v___y_3329_; uint8_t v___y_3330_; lean_object* v___y_3331_; uint8_t v___y_3335_; uint8_t v___y_3336_; uint8_t v___y_3337_; uint8_t v___x_3352_; uint8_t v___y_3354_; uint8_t v___y_3355_; uint8_t v___y_3356_; uint8_t v___y_3358_; uint8_t v___x_3370_; 
v___x_3352_ = 2;
v___x_3370_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3229_, v___x_3352_);
if (v___x_3370_ == 0)
{
v___y_3358_ = v___x_3370_;
goto v___jp_3357_;
}
else
{
uint8_t v___x_3371_; 
lean_inc_ref(v_msgData_3228_);
v___x_3371_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3228_);
v___y_3358_ = v___x_3371_;
goto v___jp_3357_;
}
v___jp_3234_:
{
lean_object* v___x_3243_; 
v___x_3243_ = l_Lean_Elab_Command_getScope___redArg(v___y_3242_);
if (lean_obj_tag(v___x_3243_) == 0)
{
lean_object* v_a_3244_; lean_object* v___x_3245_; 
v_a_3244_ = lean_ctor_get(v___x_3243_, 0);
lean_inc(v_a_3244_);
lean_dec_ref_known(v___x_3243_, 1);
v___x_3245_ = l_Lean_Elab_Command_getScope___redArg(v___y_3242_);
if (lean_obj_tag(v___x_3245_) == 0)
{
lean_object* v_a_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3281_; 
v_a_3246_ = lean_ctor_get(v___x_3245_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3248_ = v___x_3245_;
v_isShared_3249_ = v_isSharedCheck_3281_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_a_3246_);
lean_dec(v___x_3245_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3281_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3250_; lean_object* v_currNamespace_3251_; lean_object* v_openDecls_3252_; lean_object* v_env_3253_; lean_object* v_messages_3254_; lean_object* v_scopes_3255_; lean_object* v_usedQuotCtxts_3256_; lean_object* v_nextMacroScope_3257_; lean_object* v_maxRecDepth_3258_; lean_object* v_ngen_3259_; lean_object* v_auxDeclNGen_3260_; lean_object* v_infoState_3261_; lean_object* v_traceState_3262_; lean_object* v_snapshotTasks_3263_; lean_object* v_prevLinterStates_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3280_; 
v___x_3250_ = lean_st_ref_take(v___y_3242_);
v_currNamespace_3251_ = lean_ctor_get(v_a_3244_, 2);
lean_inc(v_currNamespace_3251_);
lean_dec(v_a_3244_);
v_openDecls_3252_ = lean_ctor_get(v_a_3246_, 3);
lean_inc(v_openDecls_3252_);
lean_dec(v_a_3246_);
v_env_3253_ = lean_ctor_get(v___x_3250_, 0);
v_messages_3254_ = lean_ctor_get(v___x_3250_, 1);
v_scopes_3255_ = lean_ctor_get(v___x_3250_, 2);
v_usedQuotCtxts_3256_ = lean_ctor_get(v___x_3250_, 3);
v_nextMacroScope_3257_ = lean_ctor_get(v___x_3250_, 4);
v_maxRecDepth_3258_ = lean_ctor_get(v___x_3250_, 5);
v_ngen_3259_ = lean_ctor_get(v___x_3250_, 6);
v_auxDeclNGen_3260_ = lean_ctor_get(v___x_3250_, 7);
v_infoState_3261_ = lean_ctor_get(v___x_3250_, 8);
v_traceState_3262_ = lean_ctor_get(v___x_3250_, 9);
v_snapshotTasks_3263_ = lean_ctor_get(v___x_3250_, 10);
v_prevLinterStates_3264_ = lean_ctor_get(v___x_3250_, 11);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3266_ = v___x_3250_;
v_isShared_3267_ = v_isSharedCheck_3280_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_prevLinterStates_3264_);
lean_inc(v_snapshotTasks_3263_);
lean_inc(v_traceState_3262_);
lean_inc(v_infoState_3261_);
lean_inc(v_auxDeclNGen_3260_);
lean_inc(v_ngen_3259_);
lean_inc(v_maxRecDepth_3258_);
lean_inc(v_nextMacroScope_3257_);
lean_inc(v_usedQuotCtxts_3256_);
lean_inc(v_scopes_3255_);
lean_inc(v_messages_3254_);
lean_inc(v_env_3253_);
lean_dec(v___x_3250_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3280_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3273_; 
v___x_3268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3268_, 0, v_currNamespace_3251_);
lean_ctor_set(v___x_3268_, 1, v_openDecls_3252_);
v___x_3269_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3268_);
lean_ctor_set(v___x_3269_, 1, v___y_3236_);
lean_inc_ref(v___y_3241_);
lean_inc_ref(v___y_3235_);
v___x_3270_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3270_, 0, v___y_3235_);
lean_ctor_set(v___x_3270_, 1, v___y_3238_);
lean_ctor_set(v___x_3270_, 2, v___y_3240_);
lean_ctor_set(v___x_3270_, 3, v___y_3241_);
lean_ctor_set(v___x_3270_, 4, v___x_3269_);
lean_ctor_set_uint8(v___x_3270_, sizeof(void*)*5, v___y_3239_);
lean_ctor_set_uint8(v___x_3270_, sizeof(void*)*5 + 1, v___y_3237_);
lean_ctor_set_uint8(v___x_3270_, sizeof(void*)*5 + 2, v_isSilent_3230_);
v___x_3271_ = l_Lean_MessageLog_add(v___x_3270_, v_messages_3254_);
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 1, v___x_3271_);
v___x_3273_ = v___x_3266_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_env_3253_);
lean_ctor_set(v_reuseFailAlloc_3279_, 1, v___x_3271_);
lean_ctor_set(v_reuseFailAlloc_3279_, 2, v_scopes_3255_);
lean_ctor_set(v_reuseFailAlloc_3279_, 3, v_usedQuotCtxts_3256_);
lean_ctor_set(v_reuseFailAlloc_3279_, 4, v_nextMacroScope_3257_);
lean_ctor_set(v_reuseFailAlloc_3279_, 5, v_maxRecDepth_3258_);
lean_ctor_set(v_reuseFailAlloc_3279_, 6, v_ngen_3259_);
lean_ctor_set(v_reuseFailAlloc_3279_, 7, v_auxDeclNGen_3260_);
lean_ctor_set(v_reuseFailAlloc_3279_, 8, v_infoState_3261_);
lean_ctor_set(v_reuseFailAlloc_3279_, 9, v_traceState_3262_);
lean_ctor_set(v_reuseFailAlloc_3279_, 10, v_snapshotTasks_3263_);
lean_ctor_set(v_reuseFailAlloc_3279_, 11, v_prevLinterStates_3264_);
v___x_3273_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3277_; 
v___x_3274_ = lean_st_ref_put(v___y_3242_, v___x_3273_);
v___x_3275_ = lean_box(0);
if (v_isShared_3249_ == 0)
{
lean_ctor_set(v___x_3248_, 0, v___x_3275_);
v___x_3277_ = v___x_3248_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v___x_3275_);
v___x_3277_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
return v___x_3277_;
}
}
}
}
}
else
{
lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3289_; 
lean_dec(v_a_3244_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3238_);
lean_dec_ref(v___y_3236_);
v_a_3282_ = lean_ctor_get(v___x_3245_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3284_ = v___x_3245_;
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_a_3282_);
lean_dec(v___x_3245_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3287_; 
if (v_isShared_3285_ == 0)
{
v___x_3287_ = v___x_3284_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_a_3282_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
}
else
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3297_; 
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3238_);
lean_dec_ref(v___y_3236_);
v_a_3290_ = lean_ctor_get(v___x_3243_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3292_ = v___x_3243_;
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3243_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3295_; 
if (v_isShared_3293_ == 0)
{
v___x_3295_ = v___x_3292_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_a_3290_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
}
v___jp_3298_:
{
lean_object* v_fileName_3304_; lean_object* v_fileMap_3305_; uint8_t v_suppressElabErrors_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3325_; 
v_fileName_3304_ = lean_ctor_get(v___y_3231_, 0);
v_fileMap_3305_ = lean_ctor_get(v___y_3231_, 1);
v_suppressElabErrors_3306_ = lean_ctor_get_uint8(v___y_3231_, sizeof(void*)*10);
v___x_3307_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3228_);
v___x_3308_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___redArg(v___x_3307_, v___y_3232_);
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3311_ = v___x_3308_;
v_isShared_3312_ = v_isSharedCheck_3325_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3308_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3325_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
lean_inc_ref_n(v_fileMap_3305_, 2);
v___x_3313_ = l_Lean_FileMap_toPosition(v_fileMap_3305_, v___y_3301_);
lean_dec(v___y_3301_);
v___x_3314_ = l_Lean_FileMap_toPosition(v_fileMap_3305_, v___y_3303_);
lean_dec(v___y_3303_);
v___x_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3314_);
v___x_3316_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
if (v_suppressElabErrors_3306_ == 0)
{
lean_del_object(v___x_3311_);
v___y_3235_ = v_fileName_3304_;
v___y_3236_ = v_a_3309_;
v___y_3237_ = v___y_3300_;
v___y_3238_ = v___x_3313_;
v___y_3239_ = v___y_3302_;
v___y_3240_ = v___x_3315_;
v___y_3241_ = v___x_3316_;
v___y_3242_ = v___y_3232_;
goto v___jp_3234_;
}
else
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___f_3319_; uint8_t v___x_3320_; 
v___x_3317_ = lean_box(v___y_3299_);
v___x_3318_ = lean_box(v_suppressElabErrors_3306_);
v___f_3319_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3319_, 0, v___x_3317_);
lean_closure_set(v___f_3319_, 1, v___x_3318_);
lean_inc(v_a_3309_);
v___x_3320_ = l_Lean_MessageData_hasTag(v___f_3319_, v_a_3309_);
if (v___x_3320_ == 0)
{
lean_object* v___x_3321_; lean_object* v___x_3323_; 
lean_dec_ref_known(v___x_3315_, 1);
lean_dec_ref(v___x_3313_);
lean_dec(v_a_3309_);
v___x_3321_ = lean_box(0);
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 0, v___x_3321_);
v___x_3323_ = v___x_3311_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v___x_3321_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
else
{
lean_del_object(v___x_3311_);
v___y_3235_ = v_fileName_3304_;
v___y_3236_ = v_a_3309_;
v___y_3237_ = v___y_3300_;
v___y_3238_ = v___x_3313_;
v___y_3239_ = v___y_3302_;
v___y_3240_ = v___x_3315_;
v___y_3241_ = v___x_3316_;
v___y_3242_ = v___y_3232_;
goto v___jp_3234_;
}
}
}
}
v___jp_3326_:
{
lean_object* v___x_3332_; 
v___x_3332_ = l_Lean_Syntax_getTailPos_x3f(v___y_3329_, v___y_3330_);
lean_dec(v___y_3329_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_inc(v___y_3331_);
v___y_3299_ = v___y_3327_;
v___y_3300_ = v___y_3328_;
v___y_3301_ = v___y_3331_;
v___y_3302_ = v___y_3330_;
v___y_3303_ = v___y_3331_;
goto v___jp_3298_;
}
else
{
lean_object* v_val_3333_; 
v_val_3333_ = lean_ctor_get(v___x_3332_, 0);
lean_inc(v_val_3333_);
lean_dec_ref_known(v___x_3332_, 1);
v___y_3299_ = v___y_3327_;
v___y_3300_ = v___y_3328_;
v___y_3301_ = v___y_3331_;
v___y_3302_ = v___y_3330_;
v___y_3303_ = v_val_3333_;
goto v___jp_3298_;
}
}
v___jp_3334_:
{
lean_object* v___x_3338_; 
v___x_3338_ = l_Lean_Elab_Command_getRef___redArg(v___y_3231_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_a_3339_; lean_object* v_ref_3340_; lean_object* v___x_3341_; 
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_a_3339_);
lean_dec_ref_known(v___x_3338_, 1);
v_ref_3340_ = l_Lean_replaceRef(v_ref_3227_, v_a_3339_);
lean_dec(v_a_3339_);
v___x_3341_ = l_Lean_Syntax_getPos_x3f(v_ref_3340_, v___y_3336_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v___x_3342_; 
v___x_3342_ = lean_unsigned_to_nat(0u);
v___y_3327_ = v___y_3335_;
v___y_3328_ = v___y_3337_;
v___y_3329_ = v_ref_3340_;
v___y_3330_ = v___y_3336_;
v___y_3331_ = v___x_3342_;
goto v___jp_3326_;
}
else
{
lean_object* v_val_3343_; 
v_val_3343_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_val_3343_);
lean_dec_ref_known(v___x_3341_, 1);
v___y_3327_ = v___y_3335_;
v___y_3328_ = v___y_3337_;
v___y_3329_ = v_ref_3340_;
v___y_3330_ = v___y_3336_;
v___y_3331_ = v_val_3343_;
goto v___jp_3326_;
}
}
else
{
lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3351_; 
lean_dec_ref(v_msgData_3228_);
v_a_3344_ = lean_ctor_get(v___x_3338_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3346_ = v___x_3338_;
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3338_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3349_; 
if (v_isShared_3347_ == 0)
{
v___x_3349_ = v___x_3346_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_a_3344_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
}
}
v___jp_3353_:
{
if (v___y_3356_ == 0)
{
v___y_3335_ = v___y_3354_;
v___y_3336_ = v___y_3355_;
v___y_3337_ = v_severity_3229_;
goto v___jp_3334_;
}
else
{
v___y_3335_ = v___y_3354_;
v___y_3336_ = v___y_3355_;
v___y_3337_ = v___x_3352_;
goto v___jp_3334_;
}
}
v___jp_3357_:
{
if (v___y_3358_ == 0)
{
lean_object* v___x_3359_; lean_object* v_scopes_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v_opts_3363_; uint8_t v___x_3364_; uint8_t v___x_3365_; 
v___x_3359_ = lean_st_ref_get(v___y_3232_);
v_scopes_3360_ = lean_ctor_get(v___x_3359_, 2);
lean_inc(v_scopes_3360_);
lean_dec(v___x_3359_);
v___x_3361_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3362_ = l_List_head_x21___redArg(v___x_3361_, v_scopes_3360_);
lean_dec(v_scopes_3360_);
v_opts_3363_ = lean_ctor_get(v___x_3362_, 1);
lean_inc_ref(v_opts_3363_);
lean_dec(v___x_3362_);
v___x_3364_ = 1;
v___x_3365_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3229_, v___x_3364_);
if (v___x_3365_ == 0)
{
lean_dec_ref(v_opts_3363_);
v___y_3354_ = v___y_3358_;
v___y_3355_ = v___y_3358_;
v___y_3356_ = v___x_3365_;
goto v___jp_3353_;
}
else
{
lean_object* v___x_3366_; uint8_t v___x_3367_; 
v___x_3366_ = l_Lean_warningAsError;
v___x_3367_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_3363_, v___x_3366_);
lean_dec_ref(v_opts_3363_);
v___y_3354_ = v___y_3358_;
v___y_3355_ = v___y_3358_;
v___y_3356_ = v___x_3367_;
goto v___jp_3353_;
}
}
else
{
lean_object* v___x_3368_; lean_object* v___x_3369_; 
lean_dec_ref(v_msgData_3228_);
v___x_3368_ = lean_box(0);
v___x_3369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3368_);
return v___x_3369_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___boxed(lean_object* v_ref_3372_, lean_object* v_msgData_3373_, lean_object* v_severity_3374_, lean_object* v_isSilent_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
uint8_t v_severity_boxed_3379_; uint8_t v_isSilent_boxed_3380_; lean_object* v_res_3381_; 
v_severity_boxed_3379_ = lean_unbox(v_severity_3374_);
v_isSilent_boxed_3380_ = lean_unbox(v_isSilent_3375_);
v_res_3381_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3372_, v_msgData_3373_, v_severity_boxed_3379_, v_isSilent_boxed_3380_, v___y_3376_, v___y_3377_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec(v_ref_3372_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(lean_object* v_ref_3382_, lean_object* v_msgData_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
uint8_t v___x_3387_; uint8_t v___x_3388_; lean_object* v___x_3389_; 
v___x_3387_ = 0;
v___x_3388_ = 0;
v___x_3389_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3382_, v_msgData_3383_, v___x_3387_, v___x_3388_, v___y_3384_, v___y_3385_);
return v___x_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0___boxed(lean_object* v_ref_3390_, lean_object* v_msgData_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3390_, v_msgData_3391_, v___y_3392_, v___y_3393_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v_ref_3390_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(lean_object* v___x_3397_, lean_object* v_x_3398_){
_start:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3399_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___closed__0));
v___x_3400_ = lean_string_append(v___x_3399_, v___x_3397_);
return v___x_3400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed(lean_object* v___x_3401_, lean_object* v_x_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(v___x_3401_, v_x_3402_);
lean_dec_ref(v_x_3402_);
lean_dec_ref(v___x_3401_);
return v_res_3403_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3405_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__0));
v___x_3406_ = l_Lean_stringToMessageData(v___x_3405_);
return v___x_3406_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; 
v___x_3408_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__2));
v___x_3409_ = l_Lean_stringToMessageData(v___x_3408_);
return v___x_3409_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3411_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__4));
v___x_3412_ = l_Lean_stringToMessageData(v___x_3411_);
return v___x_3412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(lean_object* v___x_3413_, uint8_t v___x_3414_, lean_object* v___x_3415_, lean_object* v_insertPos_3416_, lean_object* v_cmdLine_3417_, lean_object* v_ref_3418_, size_t v_sz_3419_, size_t v_i_3420_, lean_object* v_bs_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
_start:
{
uint8_t v___x_3425_; 
v___x_3425_ = lean_usize_dec_lt(v_i_3420_, v_sz_3419_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3426_; 
lean_dec_ref(v___x_3415_);
lean_dec_ref(v___x_3413_);
v___x_3426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3426_, 0, v_bs_3421_);
return v___x_3426_;
}
else
{
lean_object* v_v_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
v_v_3427_ = lean_array_uget(v_bs_3421_, v_i_3420_);
lean_inc(v_v_3427_);
v___x_3428_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppTactic___boxed), 4, 1);
lean_closure_set(v___x_3428_, 0, v_v_3427_);
v___x_3429_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_3428_, v___y_3422_, v___y_3423_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v_a_3430_; lean_object* v___x_3431_; lean_object* v_bs_x27_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___f_3435_; lean_object* v___x_3436_; 
v_a_3430_ = lean_ctor_get(v___x_3429_, 0);
lean_inc(v_a_3430_);
lean_dec_ref_known(v___x_3429_, 1);
v___x_3431_ = lean_unsigned_to_nat(0u);
v_bs_x27_3432_ = lean_array_uset(v_bs_3421_, v_i_3420_, v___x_3431_);
v___x_3433_ = l_Std_Format_defWidth;
v___x_3434_ = l_Std_Format_pretty(v_a_3430_, v___x_3433_, v___x_3431_, v___x_3431_);
lean_inc_ref(v___x_3434_);
v___f_3435_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3435_, 0, v___x_3434_);
lean_inc_ref(v___x_3413_);
v___x_3436_ = lean_string_append(v___x_3413_, v___x_3434_);
lean_dec_ref(v___x_3434_);
if (v___x_3414_ == 0)
{
goto v___jp_3437_;
}
else
{
lean_object* v___x_3448_; lean_object* v_line_3449_; lean_object* v_column_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3485_; 
lean_inc_ref(v___x_3415_);
v___x_3448_ = l_Lean_FileMap_toPosition(v___x_3415_, v_insertPos_3416_);
v_line_3449_ = lean_ctor_get(v___x_3448_, 0);
v_column_3450_ = lean_ctor_get(v___x_3448_, 1);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3452_ = v___x_3448_;
v_isShared_3453_ = v_isSharedCheck_3485_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_column_3450_);
lean_inc(v_line_3449_);
lean_dec(v___x_3448_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3485_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3462_; 
v___x_3454_ = lean_nat_sub(v_line_3449_, v_cmdLine_3417_);
lean_dec(v_line_3449_);
v___x_3455_ = lean_unsigned_to_nat(1u);
v___x_3456_ = lean_nat_add(v___x_3454_, v___x_3455_);
lean_dec(v___x_3454_);
v___x_3457_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1);
lean_inc_ref(v___x_3436_);
v___x_3458_ = l_String_quote(v___x_3436_);
v___x_3459_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3458_);
v___x_3460_ = l_Lean_MessageData_ofFormat(v___x_3459_);
if (v_isShared_3453_ == 0)
{
lean_ctor_set_tag(v___x_3452_, 7);
lean_ctor_set(v___x_3452_, 1, v___x_3460_);
lean_ctor_set(v___x_3452_, 0, v___x_3457_);
v___x_3462_ = v___x_3452_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v___x_3457_);
lean_ctor_set(v_reuseFailAlloc_3484_, 1, v___x_3460_);
v___x_3462_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3463_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3);
v___x_3464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3462_);
lean_ctor_set(v___x_3464_, 1, v___x_3463_);
v___x_3465_ = l_Nat_reprFast(v___x_3456_);
v___x_3466_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3465_);
v___x_3467_ = l_Lean_MessageData_ofFormat(v___x_3466_);
v___x_3468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3464_);
lean_ctor_set(v___x_3468_, 1, v___x_3467_);
v___x_3469_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5);
v___x_3470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3468_);
lean_ctor_set(v___x_3470_, 1, v___x_3469_);
v___x_3471_ = l_Nat_reprFast(v_column_3450_);
v___x_3472_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3471_);
v___x_3473_ = l_Lean_MessageData_ofFormat(v___x_3472_);
v___x_3474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3470_);
lean_ctor_set(v___x_3474_, 1, v___x_3473_);
v___x_3475_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3418_, v___x_3474_, v___y_3422_, v___y_3423_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_dec_ref_known(v___x_3475_, 1);
goto v___jp_3437_;
}
else
{
lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3483_; 
lean_dec_ref(v___x_3436_);
lean_dec_ref(v___f_3435_);
lean_dec_ref(v_bs_x27_3432_);
lean_dec(v_v_3427_);
lean_dec_ref(v___x_3415_);
lean_dec_ref(v___x_3413_);
v_a_3476_ = lean_ctor_get(v___x_3475_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3478_ = v___x_3475_;
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v___x_3475_);
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
}
}
v___jp_3437_:
{
lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; size_t v___x_3444_; size_t v___x_3445_; lean_object* v___x_3446_; 
v___x_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3436_);
v___x_3439_ = lean_box(0);
v___x_3440_ = l_Lean_MessageData_ofSyntax(v_v_3427_);
v___x_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3440_);
v___x_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3442_, 0, v___f_3435_);
v___x_3443_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3438_);
lean_ctor_set(v___x_3443_, 1, v___x_3439_);
lean_ctor_set(v___x_3443_, 2, v___x_3439_);
lean_ctor_set(v___x_3443_, 3, v___x_3439_);
lean_ctor_set(v___x_3443_, 4, v___x_3441_);
lean_ctor_set(v___x_3443_, 5, v___x_3442_);
v___x_3444_ = ((size_t)1ULL);
v___x_3445_ = lean_usize_add(v_i_3420_, v___x_3444_);
v___x_3446_ = lean_array_uset(v_bs_x27_3432_, v_i_3420_, v___x_3443_);
v_i_3420_ = v___x_3445_;
v_bs_3421_ = v___x_3446_;
goto _start;
}
}
else
{
lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3493_; 
lean_dec(v_v_3427_);
lean_dec_ref(v_bs_3421_);
lean_dec_ref(v___x_3415_);
lean_dec_ref(v___x_3413_);
v_a_3486_ = lean_ctor_get(v___x_3429_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3488_ = v___x_3429_;
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___x_3429_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___boxed(lean_object* v___x_3494_, lean_object* v___x_3495_, lean_object* v___x_3496_, lean_object* v_insertPos_3497_, lean_object* v_cmdLine_3498_, lean_object* v_ref_3499_, lean_object* v_sz_3500_, lean_object* v_i_3501_, lean_object* v_bs_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_){
_start:
{
uint8_t v___x_4299__boxed_3506_; size_t v_sz_boxed_3507_; size_t v_i_boxed_3508_; lean_object* v_res_3509_; 
v___x_4299__boxed_3506_ = lean_unbox(v___x_3495_);
v_sz_boxed_3507_ = lean_unbox_usize(v_sz_3500_);
lean_dec(v_sz_3500_);
v_i_boxed_3508_ = lean_unbox_usize(v_i_3501_);
lean_dec(v_i_3501_);
v_res_3509_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3494_, v___x_4299__boxed_3506_, v___x_3496_, v_insertPos_3497_, v_cmdLine_3498_, v_ref_3499_, v_sz_boxed_3507_, v_i_boxed_3508_, v_bs_3502_, v___y_3503_, v___y_3504_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec(v_ref_3499_);
lean_dec(v_cmdLine_3498_);
lean_dec(v_insertPos_3497_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(lean_object* v_tacticSeq_3510_, lean_object* v_ref_3511_, lean_object* v_insertPos_3512_, lean_object* v_suggs_3513_, lean_object* v_cmdLine_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; uint8_t v___x_3520_; 
v___x_3518_ = lean_array_get_size(v_suggs_3513_);
v___x_3519_ = lean_unsigned_to_nat(0u);
v___x_3520_ = lean_nat_dec_eq(v___x_3518_, v___x_3519_);
if (v___x_3520_ == 0)
{
lean_object* v___x_3521_; lean_object* v_fileMap_3522_; lean_object* v_scopes_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v_opts_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; uint8_t v___x_3529_; size_t v_sz_3530_; size_t v___x_3531_; lean_object* v___x_3532_; 
v___x_3521_ = lean_st_ref_get(v_a_3516_);
v_fileMap_3522_ = lean_ctor_get(v_a_3515_, 1);
v_scopes_3523_ = lean_ctor_get(v___x_3521_, 2);
lean_inc(v_scopes_3523_);
lean_dec(v___x_3521_);
v___x_3524_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3525_ = l_List_head_x21___redArg(v___x_3524_, v_scopes_3523_);
lean_dec(v_scopes_3523_);
v_opts_3526_ = lean_ctor_get(v___x_3525_, 1);
lean_inc_ref(v_opts_3526_);
lean_dec(v___x_3525_);
lean_inc_ref_n(v_fileMap_3522_, 2);
v___x_3527_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(v_tacticSeq_3510_, v_fileMap_3522_);
v___x_3528_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_debug_autoTry_showEdits;
v___x_3529_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_3526_, v___x_3528_);
lean_dec_ref(v_opts_3526_);
v_sz_3530_ = lean_array_size(v_suggs_3513_);
v___x_3531_ = ((size_t)0ULL);
v___x_3532_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3527_, v___x_3529_, v_fileMap_3522_, v_insertPos_3512_, v_cmdLine_3514_, v_ref_3511_, v_sz_3530_, v___x_3531_, v_suggs_3513_, v_a_3515_, v_a_3516_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v_a_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; uint8_t v___x_3537_; lean_object* v___x_3538_; lean_object* v___y_3539_; lean_object* v___x_3540_; 
v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
lean_inc(v_a_3533_);
lean_dec_ref_known(v___x_3532_, 1);
v___x_3534_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx(v_insertPos_3512_);
v___x_3535_ = lean_array_get_size(v_a_3533_);
v___x_3536_ = lean_unsigned_to_nat(1u);
v___x_3537_ = lean_nat_dec_eq(v___x_3535_, v___x_3536_);
v___x_3538_ = lean_box(v___x_3537_);
v___y_3539_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed), 8, 5);
lean_closure_set(v___y_3539_, 0, v___x_3538_);
lean_closure_set(v___y_3539_, 1, v___x_3534_);
lean_closure_set(v___y_3539_, 2, v_ref_3511_);
lean_closure_set(v___y_3539_, 3, v_a_3533_);
lean_closure_set(v___y_3539_, 4, v___x_3519_);
v___x_3540_ = l_Lean_Elab_Command_liftCoreM___redArg(v___y_3539_, v_a_3515_, v_a_3516_);
return v___x_3540_;
}
else
{
lean_object* v_a_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3548_; 
lean_dec(v_insertPos_3512_);
lean_dec(v_ref_3511_);
v_a_3541_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3543_ = v___x_3532_;
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_a_3541_);
lean_dec(v___x_3532_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3546_; 
if (v_isShared_3544_ == 0)
{
v___x_3546_ = v___x_3543_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3541_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
else
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
lean_dec_ref(v_suggs_3513_);
lean_dec(v_insertPos_3512_);
lean_dec(v_ref_3511_);
v___x_3549_ = lean_box(0);
v___x_3550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3549_);
return v___x_3550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___boxed(lean_object* v_tacticSeq_3551_, lean_object* v_ref_3552_, lean_object* v_insertPos_3553_, lean_object* v_suggs_3554_, lean_object* v_cmdLine_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_){
_start:
{
lean_object* v_res_3559_; 
v_res_3559_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(v_tacticSeq_3551_, v_ref_3552_, v_insertPos_3553_, v_suggs_3554_, v_cmdLine_3555_, v_a_3556_, v_a_3557_);
lean_dec(v_a_3557_);
lean_dec_ref(v_a_3556_);
lean_dec(v_cmdLine_3555_);
lean_dec(v_tacticSeq_3551_);
return v_res_3559_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(lean_object* v_x_3560_){
_start:
{
uint8_t v___x_3561_; 
v___x_3561_ = 0;
return v___x_3561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0___boxed(lean_object* v_x_3562_){
_start:
{
uint8_t v_res_3563_; lean_object* v_r_3564_; 
v_res_3563_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(v_x_3562_);
lean_dec(v_x_3562_);
v_r_3564_ = lean_box(v_res_3563_);
return v_r_3564_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7(void){
_start:
{
lean_object* v___x_3581_; 
v___x_3581_ = l_Array_mkArray0(lean_box(0));
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(lean_object* v___f_3585_, lean_object* v_ref_3586_, lean_object* v_goal_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_){
_start:
{
lean_object* v_fileName_3593_; lean_object* v_fileMap_3594_; lean_object* v_options_3595_; lean_object* v_currRecDepth_3596_; lean_object* v_maxRecDepth_3597_; lean_object* v_ref_3598_; lean_object* v_currNamespace_3599_; lean_object* v_openDecls_3600_; lean_object* v_initHeartbeats_3601_; lean_object* v_maxHeartbeats_3602_; lean_object* v_quotContext_3603_; lean_object* v_currMacroScope_3604_; uint8_t v_diag_3605_; lean_object* v_cancelTk_x3f_3606_; uint8_t v_suppressElabErrors_3607_; lean_object* v_inheritedTraceOptions_3608_; uint8_t v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; uint8_t v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v_ref_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; 
v_fileName_3593_ = lean_ctor_get(v___y_3590_, 0);
v_fileMap_3594_ = lean_ctor_get(v___y_3590_, 1);
v_options_3595_ = lean_ctor_get(v___y_3590_, 2);
v_currRecDepth_3596_ = lean_ctor_get(v___y_3590_, 3);
v_maxRecDepth_3597_ = lean_ctor_get(v___y_3590_, 4);
v_ref_3598_ = lean_ctor_get(v___y_3590_, 5);
v_currNamespace_3599_ = lean_ctor_get(v___y_3590_, 6);
v_openDecls_3600_ = lean_ctor_get(v___y_3590_, 7);
v_initHeartbeats_3601_ = lean_ctor_get(v___y_3590_, 8);
v_maxHeartbeats_3602_ = lean_ctor_get(v___y_3590_, 9);
v_quotContext_3603_ = lean_ctor_get(v___y_3590_, 10);
v_currMacroScope_3604_ = lean_ctor_get(v___y_3590_, 11);
v_diag_3605_ = lean_ctor_get_uint8(v___y_3590_, sizeof(void*)*14);
v_cancelTk_x3f_3606_ = lean_ctor_get(v___y_3590_, 12);
v_suppressElabErrors_3607_ = lean_ctor_get_uint8(v___y_3590_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3608_ = lean_ctor_get(v___y_3590_, 13);
v___x_3609_ = 0;
v___x_3610_ = l_Lean_SourceInfo_fromRef(v_ref_3598_, v___x_3609_);
v___x_3611_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__1));
v___x_3612_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__2));
lean_inc_n(v___x_3610_, 3);
v___x_3613_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3610_);
lean_ctor_set(v___x_3613_, 1, v___x_3612_);
v___x_3614_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__4));
v___x_3615_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__6));
v___x_3616_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7);
v___x_3617_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3610_);
lean_ctor_set(v___x_3617_, 1, v___x_3615_);
lean_ctor_set(v___x_3617_, 2, v___x_3616_);
v___x_3618_ = l_Lean_Syntax_node1(v___x_3610_, v___x_3614_, v___x_3617_);
v___x_3619_ = l_Lean_Syntax_node2(v___x_3610_, v___x_3611_, v___x_3613_, v___x_3618_);
v___x_3620_ = lean_box(0);
v___x_3621_ = lean_box(0);
v___x_3622_ = 1;
v___x_3623_ = lean_box(1);
v___x_3624_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__5));
v___x_3625_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_3625_, 0, v___x_3620_);
lean_ctor_set(v___x_3625_, 1, v___x_3621_);
lean_ctor_set(v___x_3625_, 2, v___x_3620_);
lean_ctor_set(v___x_3625_, 3, v___f_3585_);
lean_ctor_set(v___x_3625_, 4, v___x_3623_);
lean_ctor_set(v___x_3625_, 5, v___x_3623_);
lean_ctor_set(v___x_3625_, 6, v___x_3620_);
lean_ctor_set(v___x_3625_, 7, v___x_3624_);
lean_ctor_set_uint8(v___x_3625_, sizeof(void*)*8, v___x_3622_);
lean_ctor_set_uint8(v___x_3625_, sizeof(void*)*8 + 1, v___x_3622_);
lean_ctor_set_uint8(v___x_3625_, sizeof(void*)*8 + 2, v___x_3622_);
lean_ctor_set_uint8(v___x_3625_, sizeof(void*)*8 + 3, v___x_3622_);
lean_ctor_set_uint8(v___x_3625_, sizeof(void*)*8 + 4, v___x_3609_);
lean_ctor_set_uint8(v___x_3625_, sizeof(void*)*8 + 5, v___x_3609_);
lean_ctor_set_uint8(v___x_3625_, sizeof(void*)*8 + 6, v___x_3609_);
lean_ctor_set_uint8(v___x_3625_, sizeof(void*)*8 + 7, v___x_3609_);
lean_ctor_set_uint8(v___x_3625_, sizeof(void*)*8 + 8, v___x_3622_);
lean_ctor_set_uint8(v___x_3625_, sizeof(void*)*8 + 9, v___x_3609_);
lean_ctor_set_uint8(v___x_3625_, sizeof(void*)*8 + 10, v___x_3622_);
v___x_3626_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__8));
v_ref_3627_ = l_Lean_replaceRef(v_ref_3586_, v_ref_3598_);
lean_inc_ref(v_inheritedTraceOptions_3608_);
lean_inc(v_cancelTk_x3f_3606_);
lean_inc(v_currMacroScope_3604_);
lean_inc(v_quotContext_3603_);
lean_inc(v_maxHeartbeats_3602_);
lean_inc(v_initHeartbeats_3601_);
lean_inc(v_openDecls_3600_);
lean_inc(v_currNamespace_3599_);
lean_inc(v_maxRecDepth_3597_);
lean_inc(v_currRecDepth_3596_);
lean_inc_ref(v_options_3595_);
lean_inc_ref(v_fileMap_3594_);
lean_inc_ref(v_fileName_3593_);
v___x_3628_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3628_, 0, v_fileName_3593_);
lean_ctor_set(v___x_3628_, 1, v_fileMap_3594_);
lean_ctor_set(v___x_3628_, 2, v_options_3595_);
lean_ctor_set(v___x_3628_, 3, v_currRecDepth_3596_);
lean_ctor_set(v___x_3628_, 4, v_maxRecDepth_3597_);
lean_ctor_set(v___x_3628_, 5, v_ref_3627_);
lean_ctor_set(v___x_3628_, 6, v_currNamespace_3599_);
lean_ctor_set(v___x_3628_, 7, v_openDecls_3600_);
lean_ctor_set(v___x_3628_, 8, v_initHeartbeats_3601_);
lean_ctor_set(v___x_3628_, 9, v_maxHeartbeats_3602_);
lean_ctor_set(v___x_3628_, 10, v_quotContext_3603_);
lean_ctor_set(v___x_3628_, 11, v_currMacroScope_3604_);
lean_ctor_set(v___x_3628_, 12, v_cancelTk_x3f_3606_);
lean_ctor_set(v___x_3628_, 13, v_inheritedTraceOptions_3608_);
lean_ctor_set_uint8(v___x_3628_, sizeof(void*)*14, v_diag_3605_);
lean_ctor_set_uint8(v___x_3628_, sizeof(void*)*14 + 1, v_suppressElabErrors_3607_);
v___x_3629_ = l_Lean_Elab_runTactic(v_goal_3587_, v___x_3619_, v___x_3625_, v___x_3626_, v___y_3588_, v___y_3589_, v___x_3628_, v___y_3591_);
lean_dec_ref_known(v___x_3628_, 14);
if (lean_obj_tag(v___x_3629_) == 0)
{
lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3637_; 
v_isSharedCheck_3637_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3637_ == 0)
{
lean_object* v_unused_3638_; 
v_unused_3638_ = lean_ctor_get(v___x_3629_, 0);
lean_dec(v_unused_3638_);
v___x_3631_ = v___x_3629_;
v_isShared_3632_ = v_isSharedCheck_3637_;
goto v_resetjp_3630_;
}
else
{
lean_dec(v___x_3629_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3637_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3633_; lean_object* v___x_3635_; 
v___x_3633_ = lean_box(0);
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 0, v___x_3633_);
v___x_3635_ = v___x_3631_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v___x_3633_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
else
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3665_; 
v_a_3639_ = lean_ctor_get(v___x_3629_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3641_ = v___x_3629_;
v_isShared_3642_ = v_isSharedCheck_3665_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3629_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3665_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3648_; uint8_t v___y_3650_; uint8_t v___y_3660_; uint8_t v___x_3663_; 
lean_inc(v_a_3639_);
v___x_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3648_, 0, v_a_3639_);
v___x_3663_ = l_Lean_Exception_isInterrupt(v_a_3639_);
if (v___x_3663_ == 0)
{
uint8_t v___x_3664_; 
lean_inc(v_a_3639_);
v___x_3664_ = l_Lean_Exception_isRuntime(v_a_3639_);
v___y_3660_ = v___x_3664_;
goto v___jp_3659_;
}
else
{
v___y_3660_ = v___x_3663_;
goto v___jp_3659_;
}
v___jp_3643_:
{
lean_object* v___x_3644_; lean_object* v___x_3646_; 
v___x_3644_ = lean_box(0);
if (v_isShared_3642_ == 0)
{
lean_ctor_set_tag(v___x_3641_, 0);
lean_ctor_set(v___x_3641_, 0, v___x_3644_);
v___x_3646_ = v___x_3641_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v___x_3644_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
v___jp_3649_:
{
if (v___y_3650_ == 0)
{
uint8_t v_hasTrace_3651_; 
lean_dec_ref_known(v___x_3648_, 1);
v_hasTrace_3651_ = lean_ctor_get_uint8(v_options_3595_, sizeof(void*)*1);
if (v_hasTrace_3651_ == 0)
{
lean_dec(v_a_3639_);
goto v___jp_3643_;
}
else
{
lean_object* v___x_3652_; lean_object* v___x_3653_; uint8_t v___x_3654_; 
v___x_3652_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3653_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3);
v___x_3654_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3608_, v_options_3595_, v___x_3653_);
if (v___x_3654_ == 0)
{
lean_dec(v_a_3639_);
goto v___jp_3643_;
}
else
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
lean_del_object(v___x_3641_);
v___x_3655_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_3656_ = l_Lean_Exception_toMessageData(v_a_3639_);
v___x_3657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3655_);
lean_ctor_set(v___x_3657_, 1, v___x_3656_);
v___x_3658_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_3652_, v___x_3657_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_);
return v___x_3658_;
}
}
}
else
{
lean_del_object(v___x_3641_);
lean_dec(v_a_3639_);
return v___x_3648_;
}
}
v___jp_3659_:
{
if (v___y_3660_ == 0)
{
uint8_t v___x_3661_; 
v___x_3661_ = l_Lean_Exception_isInterrupt(v_a_3639_);
if (v___x_3661_ == 0)
{
uint8_t v___x_3662_; 
lean_inc(v_a_3639_);
v___x_3662_ = l_Lean_Exception_isMaxRecDepth(v_a_3639_);
v___y_3650_ = v___x_3662_;
goto v___jp_3649_;
}
else
{
v___y_3650_ = v___x_3661_;
goto v___jp_3649_;
}
}
else
{
lean_del_object(v___x_3641_);
lean_dec(v_a_3639_);
return v___x_3648_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___boxed(lean_object* v___f_3666_, lean_object* v_ref_3667_, lean_object* v_goal_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(v___f_3666_, v_ref_3667_, v_goal_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec(v_ref_3667_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(lean_object* v_c_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_){
_start:
{
lean_object* v_mctx_3680_; lean_object* v_ref_3681_; lean_object* v_env_3682_; lean_object* v_opts_3683_; lean_object* v_namingCtx_3684_; lean_object* v_goal_3685_; lean_object* v_decls_3686_; lean_object* v___x_3687_; 
v_mctx_3680_ = lean_ctor_get(v_c_3676_, 3);
lean_inc_ref(v_mctx_3680_);
v_ref_3681_ = lean_ctor_get(v_c_3676_, 1);
lean_inc(v_ref_3681_);
v_env_3682_ = lean_ctor_get(v_c_3676_, 2);
lean_inc_ref(v_env_3682_);
v_opts_3683_ = lean_ctor_get(v_c_3676_, 4);
lean_inc_ref(v_opts_3683_);
v_namingCtx_3684_ = lean_ctor_get(v_c_3676_, 5);
lean_inc_ref(v_namingCtx_3684_);
v_goal_3685_ = lean_ctor_get(v_c_3676_, 6);
lean_inc(v_goal_3685_);
lean_dec_ref(v_c_3676_);
v_decls_3686_ = lean_ctor_get(v_mctx_3680_, 5);
v___x_3687_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_decls_3686_, v_goal_3685_);
if (lean_obj_tag(v___x_3687_) == 1)
{
lean_object* v_val_3688_; lean_object* v_lctx_3689_; lean_object* v___f_3690_; lean_object* v___f_3691_; lean_object* v___x_3692_; 
v_val_3688_ = lean_ctor_get(v___x_3687_, 0);
lean_inc(v_val_3688_);
lean_dec_ref_known(v___x_3687_, 1);
v_lctx_3689_ = lean_ctor_get(v_val_3688_, 1);
lean_inc_ref(v_lctx_3689_);
lean_dec(v_val_3688_);
v___f_3690_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___closed__0));
v___f_3691_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___boxed), 8, 3);
lean_closure_set(v___f_3691_, 0, v___f_3690_);
lean_closure_set(v___f_3691_, 1, v_ref_3681_);
lean_closure_set(v___f_3691_, 2, v_goal_3685_);
v___x_3692_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_3682_, v_mctx_3680_, v_lctx_3689_, v_opts_3683_, v_namingCtx_3684_, v___f_3691_, v_a_3677_, v_a_3678_);
lean_dec_ref(v_namingCtx_3684_);
return v___x_3692_;
}
else
{
lean_object* v___x_3693_; lean_object* v___x_3694_; 
lean_dec(v___x_3687_);
lean_dec(v_goal_3685_);
lean_dec_ref(v_namingCtx_3684_);
lean_dec_ref(v_opts_3683_);
lean_dec_ref(v_env_3682_);
lean_dec(v_ref_3681_);
lean_dec_ref(v_mctx_3680_);
v___x_3693_ = lean_box(0);
v___x_3694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3693_);
return v___x_3694_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___boxed(lean_object* v_c_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_){
_start:
{
lean_object* v_res_3699_; 
v_res_3699_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(v_c_3695_, v_a_3696_, v_a_3697_);
lean_dec(v_a_3697_);
lean_dec_ref(v_a_3696_);
return v_res_3699_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(lean_object* v___x_3700_, lean_object* v_val_3701_, lean_object* v_as_3702_, size_t v_i_3703_, size_t v_stop_3704_){
_start:
{
uint8_t v___x_3709_; uint8_t v___x_3710_; 
v___x_3709_ = 0;
v___x_3710_ = lean_usize_dec_eq(v_i_3703_, v_stop_3704_);
if (v___x_3710_ == 0)
{
lean_object* v___x_3711_; lean_object* v_pos_3712_; uint8_t v_severity_3713_; lean_object* v_data_3714_; lean_object* v___f_3715_; uint8_t v___x_3716_; lean_object* v___x_3717_; uint8_t v___x_3718_; uint8_t v___y_3720_; 
v___x_3711_ = lean_array_uget_borrowed(v_as_3702_, v_i_3703_);
v_pos_3712_ = lean_ctor_get(v___x_3711_, 1);
v_severity_3713_ = lean_ctor_get_uint8(v___x_3711_, sizeof(void*)*5 + 1);
v_data_3714_ = lean_ctor_get(v___x_3711_, 4);
v___f_3715_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__0));
v___x_3716_ = 1;
lean_inc_ref(v_pos_3712_);
v___x_3717_ = l_Lean_FileMap_ofPosition(v___x_3700_, v_pos_3712_);
v___x_3718_ = l_Lean_Syntax_Range_contains(v_val_3701_, v___x_3717_, v___x_3716_);
lean_dec(v___x_3717_);
if (v_severity_3713_ == 2)
{
v___y_3720_ = v___x_3716_;
goto v___jp_3719_;
}
else
{
v___y_3720_ = v___x_3709_;
goto v___jp_3719_;
}
v___jp_3719_:
{
if (v___x_3718_ == 0)
{
goto v___jp_3705_;
}
else
{
if (v___y_3720_ == 0)
{
goto v___jp_3705_;
}
else
{
uint8_t v___x_3721_; 
lean_inc(v_data_3714_);
v___x_3721_ = l_Lean_MessageData_hasTag(v___f_3715_, v_data_3714_);
if (v___x_3721_ == 0)
{
return v___x_3716_;
}
else
{
if (v___x_3710_ == 0)
{
goto v___jp_3705_;
}
else
{
return v___x_3716_;
}
}
}
}
}
}
else
{
return v___x_3709_;
}
v___jp_3705_:
{
size_t v___x_3706_; size_t v___x_3707_; 
v___x_3706_ = ((size_t)1ULL);
v___x_3707_ = lean_usize_add(v_i_3703_, v___x_3706_);
v_i_3703_ = v___x_3707_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1___boxed(lean_object* v___x_3722_, lean_object* v_val_3723_, lean_object* v_as_3724_, lean_object* v_i_3725_, lean_object* v_stop_3726_){
_start:
{
size_t v_i_boxed_3727_; size_t v_stop_boxed_3728_; uint8_t v_res_3729_; lean_object* v_r_3730_; 
v_i_boxed_3727_ = lean_unbox_usize(v_i_3725_);
lean_dec(v_i_3725_);
v_stop_boxed_3728_ = lean_unbox_usize(v_stop_3726_);
lean_dec(v_stop_3726_);
v_res_3729_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3722_, v_val_3723_, v_as_3724_, v_i_boxed_3727_, v_stop_boxed_3728_);
lean_dec_ref(v_as_3724_);
lean_dec_ref(v_val_3723_);
lean_dec_ref(v___x_3722_);
v_r_3730_ = lean_box(v_res_3729_);
return v_r_3730_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(lean_object* v___x_3731_, lean_object* v_val_3732_, lean_object* v_x_3733_){
_start:
{
if (lean_obj_tag(v_x_3733_) == 0)
{
lean_object* v_cs_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; uint8_t v___x_3737_; 
v_cs_3734_ = lean_ctor_get(v_x_3733_, 0);
v___x_3735_ = lean_unsigned_to_nat(0u);
v___x_3736_ = lean_array_get_size(v_cs_3734_);
v___x_3737_ = lean_nat_dec_lt(v___x_3735_, v___x_3736_);
if (v___x_3737_ == 0)
{
return v___x_3737_;
}
else
{
if (v___x_3737_ == 0)
{
return v___x_3737_;
}
else
{
size_t v___x_3738_; size_t v___x_3739_; uint8_t v___x_3740_; 
v___x_3738_ = ((size_t)0ULL);
v___x_3739_ = lean_usize_of_nat(v___x_3736_);
v___x_3740_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3731_, v_val_3732_, v_cs_3734_, v___x_3738_, v___x_3739_);
return v___x_3740_;
}
}
}
else
{
lean_object* v_vs_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; uint8_t v___x_3744_; 
v_vs_3741_ = lean_ctor_get(v_x_3733_, 0);
v___x_3742_ = lean_unsigned_to_nat(0u);
v___x_3743_ = lean_array_get_size(v_vs_3741_);
v___x_3744_ = lean_nat_dec_lt(v___x_3742_, v___x_3743_);
if (v___x_3744_ == 0)
{
return v___x_3744_;
}
else
{
if (v___x_3744_ == 0)
{
return v___x_3744_;
}
else
{
size_t v___x_3745_; size_t v___x_3746_; uint8_t v___x_3747_; 
v___x_3745_ = ((size_t)0ULL);
v___x_3746_ = lean_usize_of_nat(v___x_3743_);
v___x_3747_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3731_, v_val_3732_, v_vs_3741_, v___x_3745_, v___x_3746_);
return v___x_3747_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(lean_object* v___x_3748_, lean_object* v_val_3749_, lean_object* v_as_3750_, size_t v_i_3751_, size_t v_stop_3752_){
_start:
{
uint8_t v___x_3753_; 
v___x_3753_ = lean_usize_dec_eq(v_i_3751_, v_stop_3752_);
if (v___x_3753_ == 0)
{
lean_object* v___x_3754_; uint8_t v___x_3755_; 
v___x_3754_ = lean_array_uget_borrowed(v_as_3750_, v_i_3751_);
v___x_3755_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3748_, v_val_3749_, v___x_3754_);
if (v___x_3755_ == 0)
{
size_t v___x_3756_; size_t v___x_3757_; 
v___x_3756_ = ((size_t)1ULL);
v___x_3757_ = lean_usize_add(v_i_3751_, v___x_3756_);
v_i_3751_ = v___x_3757_;
goto _start;
}
else
{
return v___x_3755_;
}
}
else
{
uint8_t v___x_3759_; 
v___x_3759_ = 0;
return v___x_3759_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3760_, lean_object* v_val_3761_, lean_object* v_as_3762_, lean_object* v_i_3763_, lean_object* v_stop_3764_){
_start:
{
size_t v_i_boxed_3765_; size_t v_stop_boxed_3766_; uint8_t v_res_3767_; lean_object* v_r_3768_; 
v_i_boxed_3765_ = lean_unbox_usize(v_i_3763_);
lean_dec(v_i_3763_);
v_stop_boxed_3766_ = lean_unbox_usize(v_stop_3764_);
lean_dec(v_stop_3764_);
v_res_3767_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3760_, v_val_3761_, v_as_3762_, v_i_boxed_3765_, v_stop_boxed_3766_);
lean_dec_ref(v_as_3762_);
lean_dec_ref(v_val_3761_);
lean_dec_ref(v___x_3760_);
v_r_3768_ = lean_box(v_res_3767_);
return v_r_3768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0___boxed(lean_object* v___x_3769_, lean_object* v_val_3770_, lean_object* v_x_3771_){
_start:
{
uint8_t v_res_3772_; lean_object* v_r_3773_; 
v_res_3772_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3769_, v_val_3770_, v_x_3771_);
lean_dec_ref(v_x_3771_);
lean_dec_ref(v_val_3770_);
lean_dec_ref(v___x_3769_);
v_r_3773_ = lean_box(v_res_3772_);
return v_r_3773_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(lean_object* v___x_3774_, lean_object* v_val_3775_, lean_object* v_t_3776_){
_start:
{
lean_object* v_root_3777_; lean_object* v_tail_3778_; uint8_t v___x_3779_; 
v_root_3777_ = lean_ctor_get(v_t_3776_, 0);
v_tail_3778_ = lean_ctor_get(v_t_3776_, 1);
v___x_3779_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3774_, v_val_3775_, v_root_3777_);
if (v___x_3779_ == 0)
{
lean_object* v___x_3780_; lean_object* v___x_3781_; uint8_t v___x_3782_; 
v___x_3780_ = lean_unsigned_to_nat(0u);
v___x_3781_ = lean_array_get_size(v_tail_3778_);
v___x_3782_ = lean_nat_dec_lt(v___x_3780_, v___x_3781_);
if (v___x_3782_ == 0)
{
return v___x_3779_;
}
else
{
if (v___x_3782_ == 0)
{
return v___x_3779_;
}
else
{
size_t v___x_3783_; size_t v___x_3784_; uint8_t v___x_3785_; 
v___x_3783_ = ((size_t)0ULL);
v___x_3784_ = lean_usize_of_nat(v___x_3781_);
v___x_3785_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3774_, v_val_3775_, v_tail_3778_, v___x_3783_, v___x_3784_);
return v___x_3785_;
}
}
}
else
{
return v___x_3779_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0___boxed(lean_object* v___x_3786_, lean_object* v_val_3787_, lean_object* v_t_3788_){
_start:
{
uint8_t v_res_3789_; lean_object* v_r_3790_; 
v_res_3789_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v___x_3786_, v_val_3787_, v_t_3788_);
lean_dec_ref(v_t_3788_);
lean_dec_ref(v_val_3787_);
lean_dec_ref(v___x_3786_);
v_r_3790_ = lean_box(v_res_3789_);
return v_r_3790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(lean_object* v_stx_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_){
_start:
{
uint8_t v___x_3795_; lean_object* v___x_3796_; 
v___x_3795_ = 0;
v___x_3796_ = l_Lean_Syntax_getRange_x3f(v_stx_3791_, v___x_3795_);
if (lean_obj_tag(v___x_3796_) == 1)
{
lean_object* v_val_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3810_; 
v_val_3797_ = lean_ctor_get(v___x_3796_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3799_ = v___x_3796_;
v_isShared_3800_ = v_isSharedCheck_3810_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_val_3797_);
lean_dec(v___x_3796_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3810_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3801_; lean_object* v_fileMap_3802_; lean_object* v_messages_3803_; lean_object* v___x_3804_; uint8_t v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3808_; 
v___x_3801_ = lean_st_ref_get(v_a_3793_);
v_fileMap_3802_ = lean_ctor_get(v_a_3792_, 1);
v_messages_3803_ = lean_ctor_get(v___x_3801_, 1);
lean_inc_ref(v_messages_3803_);
lean_dec(v___x_3801_);
v___x_3804_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_3803_);
v___x_3805_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v_fileMap_3802_, v_val_3797_, v___x_3804_);
lean_dec_ref(v___x_3804_);
lean_dec(v_val_3797_);
v___x_3806_ = lean_box(v___x_3805_);
if (v_isShared_3800_ == 0)
{
lean_ctor_set_tag(v___x_3799_, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3806_);
v___x_3808_ = v___x_3799_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3806_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
else
{
lean_object* v___x_3811_; lean_object* v___x_3812_; 
lean_dec(v___x_3796_);
v___x_3811_ = lean_box(v___x_3795_);
v___x_3812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3811_);
return v___x_3812_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError___boxed(lean_object* v_stx_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(v_stx_3813_, v_a_3814_, v_a_3815_);
lean_dec(v_a_3815_);
lean_dec_ref(v_a_3814_);
lean_dec(v_stx_3813_);
return v_res_3817_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(lean_object* v_tree_3818_, lean_object* v_fileMap_3819_, lean_object* v_c_3820_){
_start:
{
lean_object* v___y_3822_; lean_object* v_kind_3826_; lean_object* v_ref_3827_; lean_object* v___y_3829_; 
v_kind_3826_ = lean_ctor_get(v_c_3820_, 0);
lean_inc(v_kind_3826_);
v_ref_3827_ = lean_ctor_get(v_c_3820_, 1);
lean_inc(v_ref_3827_);
lean_dec_ref(v_c_3820_);
if (lean_obj_tag(v_kind_3826_) == 0)
{
lean_object* v_insertPos_3845_; 
lean_dec(v_ref_3827_);
v_insertPos_3845_ = lean_ctor_get(v_kind_3826_, 1);
lean_inc(v_insertPos_3845_);
v___y_3829_ = v_insertPos_3845_;
goto v___jp_3828_;
}
else
{
uint8_t v___x_3846_; lean_object* v___x_3847_; 
v___x_3846_ = 0;
v___x_3847_ = l_Lean_Syntax_getPos_x3f(v_ref_3827_, v___x_3846_);
lean_dec(v_ref_3827_);
if (lean_obj_tag(v___x_3847_) == 0)
{
lean_object* v___x_3848_; 
v___x_3848_ = lean_unsigned_to_nat(0u);
v___y_3829_ = v___x_3848_;
goto v___jp_3828_;
}
else
{
lean_object* v_val_3849_; 
v_val_3849_ = lean_ctor_get(v___x_3847_, 0);
lean_inc(v_val_3849_);
lean_dec_ref_known(v___x_3847_, 1);
v___y_3829_ = v_val_3849_;
goto v___jp_3828_;
}
}
v___jp_3821_:
{
lean_object* v___x_3823_; lean_object* v___x_3824_; uint8_t v___x_3825_; 
v___x_3823_ = l_List_lengthTR___redArg(v___y_3822_);
lean_dec(v___y_3822_);
v___x_3824_ = lean_unsigned_to_nat(1u);
v___x_3825_ = lean_nat_dec_eq(v___x_3823_, v___x_3824_);
lean_dec(v___x_3823_);
return v___x_3825_;
}
v___jp_3828_:
{
lean_object* v___x_3830_; 
v___x_3830_ = l_Lean_Elab_InfoTree_goalsAt_x3f(v_fileMap_3819_, v_tree_3818_, v___y_3829_);
if (lean_obj_tag(v___x_3830_) == 1)
{
lean_object* v_tail_3831_; 
v_tail_3831_ = lean_ctor_get(v___x_3830_, 1);
lean_inc(v_tail_3831_);
if (lean_obj_tag(v_tail_3831_) == 0)
{
if (lean_obj_tag(v_kind_3826_) == 0)
{
lean_object* v_head_3832_; lean_object* v_tacticSeq_3833_; uint8_t v___x_3834_; lean_object* v___x_3835_; 
v_head_3832_ = lean_ctor_get(v___x_3830_, 0);
lean_inc(v_head_3832_);
lean_dec_ref_known(v___x_3830_, 2);
v_tacticSeq_3833_ = lean_ctor_get(v_kind_3826_, 0);
lean_inc(v_tacticSeq_3833_);
lean_dec_ref_known(v_kind_3826_, 2);
v___x_3834_ = 0;
v___x_3835_ = l_Lean_Syntax_getPos_x3f(v_tacticSeq_3833_, v___x_3834_);
lean_dec(v_tacticSeq_3833_);
if (lean_obj_tag(v___x_3835_) == 0)
{
lean_object* v_tacticInfo_3836_; lean_object* v_goalsBefore_3837_; 
v_tacticInfo_3836_ = lean_ctor_get(v_head_3832_, 1);
lean_inc_ref(v_tacticInfo_3836_);
lean_dec(v_head_3832_);
v_goalsBefore_3837_ = lean_ctor_get(v_tacticInfo_3836_, 2);
lean_inc(v_goalsBefore_3837_);
lean_dec_ref(v_tacticInfo_3836_);
v___y_3822_ = v_goalsBefore_3837_;
goto v___jp_3821_;
}
else
{
lean_object* v_tacticInfo_3838_; lean_object* v_goalsAfter_3839_; 
lean_dec_ref_known(v___x_3835_, 1);
v_tacticInfo_3838_ = lean_ctor_get(v_head_3832_, 1);
lean_inc_ref(v_tacticInfo_3838_);
lean_dec(v_head_3832_);
v_goalsAfter_3839_ = lean_ctor_get(v_tacticInfo_3838_, 4);
lean_inc(v_goalsAfter_3839_);
lean_dec_ref(v_tacticInfo_3838_);
v___y_3822_ = v_goalsAfter_3839_;
goto v___jp_3821_;
}
}
else
{
lean_object* v_head_3840_; lean_object* v_tacticInfo_3841_; lean_object* v_goalsBefore_3842_; 
v_head_3840_ = lean_ctor_get(v___x_3830_, 0);
lean_inc(v_head_3840_);
lean_dec_ref_known(v___x_3830_, 2);
v_tacticInfo_3841_ = lean_ctor_get(v_head_3840_, 1);
lean_inc_ref(v_tacticInfo_3841_);
lean_dec(v_head_3840_);
v_goalsBefore_3842_ = lean_ctor_get(v_tacticInfo_3841_, 2);
lean_inc(v_goalsBefore_3842_);
lean_dec_ref(v_tacticInfo_3841_);
v___y_3822_ = v_goalsBefore_3842_;
goto v___jp_3821_;
}
}
else
{
uint8_t v___x_3843_; 
lean_dec_ref_known(v___x_3830_, 2);
lean_dec(v_tail_3831_);
lean_dec(v_kind_3826_);
v___x_3843_ = 0;
return v___x_3843_;
}
}
else
{
uint8_t v___x_3844_; 
lean_dec(v___x_3830_);
lean_dec(v_kind_3826_);
v___x_3844_ = 0;
return v___x_3844_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos___boxed(lean_object* v_tree_3850_, lean_object* v_fileMap_3851_, lean_object* v_c_3852_){
_start:
{
uint8_t v_res_3853_; lean_object* v_r_3854_; 
v_res_3853_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(v_tree_3850_, v_fileMap_3851_, v_c_3852_);
v_r_3854_ = lean_box(v_res_3853_);
return v_r_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(lean_object* v___y_3855_){
_start:
{
lean_object* v___x_3857_; lean_object* v_infoState_3858_; lean_object* v_trees_3859_; lean_object* v___x_3860_; 
v___x_3857_ = lean_st_ref_get(v___y_3855_);
v_infoState_3858_ = lean_ctor_get(v___x_3857_, 8);
lean_inc_ref(v_infoState_3858_);
lean_dec(v___x_3857_);
v_trees_3859_ = lean_ctor_get(v_infoState_3858_, 2);
lean_inc_ref(v_trees_3859_);
lean_dec_ref(v_infoState_3858_);
v___x_3860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3860_, 0, v_trees_3859_);
return v___x_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg___boxed(lean_object* v___y_3861_, lean_object* v___y_3862_){
_start:
{
lean_object* v_res_3863_; 
v_res_3863_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_3861_);
lean_dec(v___y_3861_);
return v_res_3863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
lean_object* v___x_3867_; 
v___x_3867_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_3865_);
return v___x_3867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___boxed(lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_){
_start:
{
lean_object* v_res_3871_; 
v_res_3871_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(v___y_3868_, v___y_3869_);
lean_dec(v___y_3869_);
lean_dec_ref(v___y_3868_);
return v_res_3871_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3873_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__0));
v___x_3874_ = l_Lean_stringToMessageData(v___x_3873_);
return v___x_3874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(lean_object* v_tree_3875_, lean_object* v___x_3876_, lean_object* v___x_3877_, lean_object* v_as_3878_, size_t v_sz_3879_, size_t v_i_3880_, lean_object* v_b_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_){
_start:
{
lean_object* v_a_3886_; uint8_t v___x_3890_; 
v___x_3890_ = lean_usize_dec_lt(v_i_3880_, v_sz_3879_);
if (v___x_3890_ == 0)
{
lean_object* v___x_3891_; 
lean_dec_ref(v___x_3876_);
lean_dec_ref(v_tree_3875_);
v___x_3891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3891_, 0, v_b_3881_);
return v___x_3891_;
}
else
{
lean_object* v___x_3892_; lean_object* v_a_3893_; uint8_t v___x_3894_; 
v___x_3892_ = lean_box(0);
v_a_3893_ = lean_array_uget_borrowed(v_as_3878_, v_i_3880_);
lean_inc(v_a_3893_);
lean_inc_ref(v___x_3876_);
lean_inc_ref(v_tree_3875_);
v___x_3894_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(v_tree_3875_, v___x_3876_, v_a_3893_);
if (v___x_3894_ == 0)
{
lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v_scopes_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v_opts_3901_; uint8_t v_hasTrace_3902_; 
v___x_3895_ = l_Lean_inheritedTraceOptions;
v___x_3896_ = lean_st_ref_get(v___x_3895_);
v___x_3897_ = lean_st_ref_get(v___y_3883_);
v_scopes_3898_ = lean_ctor_get(v___x_3897_, 2);
lean_inc(v_scopes_3898_);
lean_dec(v___x_3897_);
v___x_3899_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3900_ = l_List_head_x21___redArg(v___x_3899_, v_scopes_3898_);
lean_dec(v_scopes_3898_);
v_opts_3901_ = lean_ctor_get(v___x_3900_, 1);
lean_inc_ref(v_opts_3901_);
lean_dec(v___x_3900_);
v_hasTrace_3902_ = lean_ctor_get_uint8(v_opts_3901_, sizeof(void*)*1);
if (v_hasTrace_3902_ == 0)
{
lean_dec_ref(v_opts_3901_);
lean_dec(v___x_3896_);
v_a_3886_ = v___x_3892_;
goto v___jp_3885_;
}
else
{
lean_object* v___x_3903_; lean_object* v___x_3904_; uint8_t v___x_3905_; 
v___x_3903_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3904_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3);
v___x_3905_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3896_, v_opts_3901_, v___x_3904_);
lean_dec_ref(v_opts_3901_);
lean_dec(v___x_3896_);
if (v___x_3905_ == 0)
{
v_a_3886_ = v___x_3892_;
goto v___jp_3885_;
}
else
{
lean_object* v___x_3906_; lean_object* v___x_3907_; 
v___x_3906_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1);
v___x_3907_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_3903_, v___x_3906_, v___y_3882_, v___y_3883_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_dec_ref_known(v___x_3907_, 1);
v_a_3886_ = v___x_3892_;
goto v___jp_3885_;
}
else
{
lean_dec_ref(v___x_3876_);
lean_dec_ref(v_tree_3875_);
return v___x_3907_;
}
}
}
}
else
{
lean_object* v_kind_3908_; 
v_kind_3908_ = lean_ctor_get(v_a_3893_, 0);
if (lean_obj_tag(v_kind_3908_) == 0)
{
lean_object* v_ref_3909_; lean_object* v_tacticSeq_3910_; lean_object* v_insertPos_3911_; lean_object* v___x_3912_; 
v_ref_3909_ = lean_ctor_get(v_a_3893_, 1);
v_tacticSeq_3910_ = lean_ctor_get(v_kind_3908_, 0);
v_insertPos_3911_ = lean_ctor_get(v_kind_3908_, 1);
lean_inc(v_a_3893_);
v___x_3912_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(v_a_3893_, v___y_3882_, v___y_3883_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_object* v_a_3913_; lean_object* v___x_3914_; 
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_a_3913_);
lean_dec_ref_known(v___x_3912_, 1);
lean_inc(v_insertPos_3911_);
lean_inc(v_ref_3909_);
v___x_3914_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(v_tacticSeq_3910_, v_ref_3909_, v_insertPos_3911_, v_a_3913_, v___x_3877_, v___y_3882_, v___y_3883_);
if (lean_obj_tag(v___x_3914_) == 0)
{
lean_dec_ref_known(v___x_3914_, 1);
v_a_3886_ = v___x_3892_;
goto v___jp_3885_;
}
else
{
lean_dec_ref(v___x_3876_);
lean_dec_ref(v_tree_3875_);
return v___x_3914_;
}
}
else
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
lean_dec_ref(v___x_3876_);
lean_dec_ref(v_tree_3875_);
v_a_3915_ = lean_ctor_get(v___x_3912_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3912_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3912_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3912_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3920_; 
if (v_isShared_3918_ == 0)
{
v___x_3920_ = v___x_3917_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
}
else
{
lean_object* v___x_3923_; 
lean_inc(v_a_3893_);
v___x_3923_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(v_a_3893_, v___y_3882_, v___y_3883_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_dec_ref_known(v___x_3923_, 1);
v_a_3886_ = v___x_3892_;
goto v___jp_3885_;
}
else
{
lean_dec_ref(v___x_3876_);
lean_dec_ref(v_tree_3875_);
return v___x_3923_;
}
}
}
}
v___jp_3885_:
{
size_t v___x_3887_; size_t v___x_3888_; 
v___x_3887_ = ((size_t)1ULL);
v___x_3888_ = lean_usize_add(v_i_3880_, v___x_3887_);
v_i_3880_ = v___x_3888_;
v_b_3881_ = v_a_3886_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___boxed(lean_object* v_tree_3924_, lean_object* v___x_3925_, lean_object* v___x_3926_, lean_object* v_as_3927_, lean_object* v_sz_3928_, lean_object* v_i_3929_, lean_object* v_b_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_){
_start:
{
size_t v_sz_boxed_3934_; size_t v_i_boxed_3935_; lean_object* v_res_3936_; 
v_sz_boxed_3934_ = lean_unbox_usize(v_sz_3928_);
lean_dec(v_sz_3928_);
v_i_boxed_3935_ = lean_unbox_usize(v_i_3929_);
lean_dec(v_i_3929_);
v_res_3936_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_tree_3924_, v___x_3925_, v___x_3926_, v_as_3927_, v_sz_boxed_3934_, v_i_boxed_3935_, v_b_3930_, v___y_3931_, v___y_3932_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
lean_dec_ref(v_as_3927_);
lean_dec(v___x_3926_);
return v_res_3936_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__2(void){
_start:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; 
v___x_3941_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3942_ = l_Lean_stringToMessageData(v___x_3941_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(lean_object* v_stx_3943_, lean_object* v___x_3944_, lean_object* v___x_3945_, lean_object* v___x_3946_, lean_object* v___x_3947_, lean_object* v_as_3948_, size_t v_sz_3949_, size_t v_i_3950_, lean_object* v_b_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_){
_start:
{
uint8_t v___x_3955_; 
v___x_3955_ = lean_usize_dec_lt(v_i_3950_, v_sz_3949_);
if (v___x_3955_ == 0)
{
lean_object* v___x_3956_; 
lean_dec_ref(v___x_3946_);
lean_dec(v_stx_3943_);
v___x_3956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3956_, 0, v_b_3951_);
return v___x_3956_;
}
else
{
lean_object* v_a_3957_; lean_object* v___x_3958_; 
lean_dec_ref(v_b_3951_);
v_a_3957_ = lean_array_uget_borrowed(v_as_3948_, v_i_3950_);
lean_inc(v_a_3957_);
lean_inc(v_stx_3943_);
v___x_3958_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3943_, v___x_3944_, v_a_3957_, v___x_3945_, v___y_3952_, v___y_3953_);
if (lean_obj_tag(v___x_3958_) == 0)
{
lean_object* v_a_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v_scopes_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v_opts_3966_; uint8_t v_hasTrace_3967_; lean_object* v___x_3968_; lean_object* v___y_3970_; lean_object* v___y_3971_; 
v_a_3959_ = lean_ctor_get(v___x_3958_, 0);
lean_inc(v_a_3959_);
lean_dec_ref_known(v___x_3958_, 1);
v___x_3960_ = l_Lean_inheritedTraceOptions;
v___x_3961_ = lean_st_ref_get(v___x_3960_);
v___x_3962_ = lean_st_ref_get(v___y_3953_);
v_scopes_3963_ = lean_ctor_get(v___x_3962_, 2);
lean_inc(v_scopes_3963_);
lean_dec(v___x_3962_);
v___x_3964_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3965_ = l_List_head_x21___redArg(v___x_3964_, v_scopes_3963_);
lean_dec(v_scopes_3963_);
v_opts_3966_ = lean_ctor_get(v___x_3965_, 1);
lean_inc_ref(v_opts_3966_);
lean_dec(v___x_3965_);
v_hasTrace_3967_ = lean_ctor_get_uint8(v_opts_3966_, sizeof(void*)*1);
v___x_3968_ = lean_box(0);
if (v_hasTrace_3967_ == 0)
{
lean_dec_ref(v_opts_3966_);
lean_dec(v___x_3961_);
v___y_3970_ = v___y_3952_;
v___y_3971_ = v___y_3953_;
goto v___jp_3969_;
}
else
{
lean_object* v___x_3987_; lean_object* v___x_3988_; uint8_t v___x_3989_; 
v___x_3987_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3988_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3);
v___x_3989_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3961_, v_opts_3966_, v___x_3988_);
lean_dec_ref(v_opts_3966_);
lean_dec(v___x_3961_);
if (v___x_3989_ == 0)
{
v___y_3970_ = v___y_3952_;
v___y_3971_ = v___y_3953_;
goto v___jp_3969_;
}
else
{
lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; 
v___x_3990_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__2);
v___x_3991_ = lean_array_get_size(v_a_3959_);
v___x_3992_ = l_Nat_reprFast(v___x_3991_);
v___x_3993_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3992_);
v___x_3994_ = l_Lean_MessageData_ofFormat(v___x_3993_);
v___x_3995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3990_);
lean_ctor_set(v___x_3995_, 1, v___x_3994_);
v___x_3996_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_3987_, v___x_3995_, v___y_3952_, v___y_3953_);
if (lean_obj_tag(v___x_3996_) == 0)
{
lean_dec_ref_known(v___x_3996_, 1);
v___y_3970_ = v___y_3952_;
v___y_3971_ = v___y_3953_;
goto v___jp_3969_;
}
else
{
lean_object* v_a_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4004_; 
lean_dec(v_a_3959_);
lean_dec_ref(v___x_3946_);
lean_dec(v_stx_3943_);
v_a_3997_ = lean_ctor_get(v___x_3996_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3999_ = v___x_3996_;
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_a_3997_);
lean_dec(v___x_3996_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v___x_4002_; 
if (v_isShared_4000_ == 0)
{
v___x_4002_ = v___x_3999_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_a_3997_);
v___x_4002_ = v_reuseFailAlloc_4003_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
return v___x_4002_;
}
}
}
}
}
v___jp_3969_:
{
size_t v_sz_3972_; size_t v___x_3973_; lean_object* v___x_3974_; 
v_sz_3972_ = lean_array_size(v_a_3959_);
v___x_3973_ = ((size_t)0ULL);
lean_inc_ref(v___x_3946_);
lean_inc(v_a_3957_);
v___x_3974_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_3957_, v___x_3946_, v___x_3947_, v_a_3959_, v_sz_3972_, v___x_3973_, v___x_3968_, v___y_3970_, v___y_3971_);
lean_dec(v_a_3959_);
if (lean_obj_tag(v___x_3974_) == 0)
{
lean_object* v___x_3975_; size_t v___x_3976_; size_t v___x_3977_; 
lean_dec_ref_known(v___x_3974_, 1);
v___x_3975_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_3976_ = ((size_t)1ULL);
v___x_3977_ = lean_usize_add(v_i_3950_, v___x_3976_);
v_i_3950_ = v___x_3977_;
v_b_3951_ = v___x_3975_;
goto _start;
}
else
{
lean_object* v_a_3979_; lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_3986_; 
lean_dec_ref(v___x_3946_);
lean_dec(v_stx_3943_);
v_a_3979_ = lean_ctor_get(v___x_3974_, 0);
v_isSharedCheck_3986_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_3986_ == 0)
{
v___x_3981_ = v___x_3974_;
v_isShared_3982_ = v_isSharedCheck_3986_;
goto v_resetjp_3980_;
}
else
{
lean_inc(v_a_3979_);
lean_dec(v___x_3974_);
v___x_3981_ = lean_box(0);
v_isShared_3982_ = v_isSharedCheck_3986_;
goto v_resetjp_3980_;
}
v_resetjp_3980_:
{
lean_object* v___x_3984_; 
if (v_isShared_3982_ == 0)
{
v___x_3984_ = v___x_3981_;
goto v_reusejp_3983_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v_a_3979_);
v___x_3984_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3983_;
}
v_reusejp_3983_:
{
return v___x_3984_;
}
}
}
}
}
else
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4012_; 
lean_dec_ref(v___x_3946_);
lean_dec(v_stx_3943_);
v_a_4005_ = lean_ctor_get(v___x_3958_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4007_ = v___x_3958_;
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___x_3958_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4010_; 
if (v_isShared_4008_ == 0)
{
v___x_4010_ = v___x_4007_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_4005_);
v___x_4010_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
return v___x_4010_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_stx_4013_, lean_object* v___x_4014_, lean_object* v___x_4015_, lean_object* v___x_4016_, lean_object* v___x_4017_, lean_object* v_as_4018_, lean_object* v_sz_4019_, lean_object* v_i_4020_, lean_object* v_b_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_){
_start:
{
size_t v_sz_boxed_4025_; size_t v_i_boxed_4026_; lean_object* v_res_4027_; 
v_sz_boxed_4025_ = lean_unbox_usize(v_sz_4019_);
lean_dec(v_sz_4019_);
v_i_boxed_4026_ = lean_unbox_usize(v_i_4020_);
lean_dec(v_i_4020_);
v_res_4027_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4013_, v___x_4014_, v___x_4015_, v___x_4016_, v___x_4017_, v_as_4018_, v_sz_boxed_4025_, v_i_boxed_4026_, v_b_4021_, v___y_4022_, v___y_4023_);
lean_dec(v___y_4023_);
lean_dec_ref(v___y_4022_);
lean_dec_ref(v_as_4018_);
lean_dec(v___x_4017_);
lean_dec_ref(v___x_4015_);
lean_dec_ref(v___x_4014_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(lean_object* v_stx_4028_, lean_object* v___x_4029_, lean_object* v___x_4030_, lean_object* v___x_4031_, lean_object* v___x_4032_, lean_object* v_as_4033_, size_t v_sz_4034_, size_t v_i_4035_, lean_object* v_b_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_){
_start:
{
uint8_t v___x_4040_; 
v___x_4040_ = lean_usize_dec_lt(v_i_4035_, v_sz_4034_);
if (v___x_4040_ == 0)
{
lean_object* v___x_4041_; 
lean_dec_ref(v___x_4031_);
lean_dec(v_stx_4028_);
v___x_4041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4041_, 0, v_b_4036_);
return v___x_4041_;
}
else
{
lean_object* v_a_4042_; lean_object* v___x_4043_; 
lean_dec_ref(v_b_4036_);
v_a_4042_ = lean_array_uget_borrowed(v_as_4033_, v_i_4035_);
lean_inc(v_a_4042_);
lean_inc(v_stx_4028_);
v___x_4043_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_4028_, v___x_4029_, v_a_4042_, v___x_4030_, v___y_4037_, v___y_4038_);
if (lean_obj_tag(v___x_4043_) == 0)
{
lean_object* v_a_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v_scopes_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v_opts_4051_; uint8_t v_hasTrace_4052_; lean_object* v___x_4053_; lean_object* v___y_4055_; lean_object* v___y_4056_; 
v_a_4044_ = lean_ctor_get(v___x_4043_, 0);
lean_inc(v_a_4044_);
lean_dec_ref_known(v___x_4043_, 1);
v___x_4045_ = l_Lean_inheritedTraceOptions;
v___x_4046_ = lean_st_ref_get(v___x_4045_);
v___x_4047_ = lean_st_ref_get(v___y_4038_);
v_scopes_4048_ = lean_ctor_get(v___x_4047_, 2);
lean_inc(v_scopes_4048_);
lean_dec(v___x_4047_);
v___x_4049_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4050_ = l_List_head_x21___redArg(v___x_4049_, v_scopes_4048_);
lean_dec(v_scopes_4048_);
v_opts_4051_ = lean_ctor_get(v___x_4050_, 1);
lean_inc_ref(v_opts_4051_);
lean_dec(v___x_4050_);
v_hasTrace_4052_ = lean_ctor_get_uint8(v_opts_4051_, sizeof(void*)*1);
v___x_4053_ = lean_box(0);
if (v_hasTrace_4052_ == 0)
{
lean_dec_ref(v_opts_4051_);
lean_dec(v___x_4046_);
v___y_4055_ = v___y_4037_;
v___y_4056_ = v___y_4038_;
goto v___jp_4054_;
}
else
{
lean_object* v___x_4072_; lean_object* v___x_4073_; uint8_t v___x_4074_; 
v___x_4072_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4073_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3);
v___x_4074_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4046_, v_opts_4051_, v___x_4073_);
lean_dec_ref(v_opts_4051_);
lean_dec(v___x_4046_);
if (v___x_4074_ == 0)
{
v___y_4055_ = v___y_4037_;
v___y_4056_ = v___y_4038_;
goto v___jp_4054_;
}
else
{
lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4075_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__2);
v___x_4076_ = lean_array_get_size(v_a_4044_);
v___x_4077_ = l_Nat_reprFast(v___x_4076_);
v___x_4078_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4078_, 0, v___x_4077_);
v___x_4079_ = l_Lean_MessageData_ofFormat(v___x_4078_);
v___x_4080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4075_);
lean_ctor_set(v___x_4080_, 1, v___x_4079_);
v___x_4081_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_4072_, v___x_4080_, v___y_4037_, v___y_4038_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_dec_ref_known(v___x_4081_, 1);
v___y_4055_ = v___y_4037_;
v___y_4056_ = v___y_4038_;
goto v___jp_4054_;
}
else
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4089_; 
lean_dec(v_a_4044_);
lean_dec_ref(v___x_4031_);
lean_dec(v_stx_4028_);
v_a_4082_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_4084_ = v___x_4081_;
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v___x_4081_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4087_; 
if (v_isShared_4085_ == 0)
{
v___x_4087_ = v___x_4084_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_a_4082_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
}
}
}
}
}
v___jp_4054_:
{
size_t v_sz_4057_; size_t v___x_4058_; lean_object* v___x_4059_; 
v_sz_4057_ = lean_array_size(v_a_4044_);
v___x_4058_ = ((size_t)0ULL);
lean_inc_ref(v___x_4031_);
lean_inc(v_a_4042_);
v___x_4059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4042_, v___x_4031_, v___x_4032_, v_a_4044_, v_sz_4057_, v___x_4058_, v___x_4053_, v___y_4055_, v___y_4056_);
lean_dec(v_a_4044_);
if (lean_obj_tag(v___x_4059_) == 0)
{
lean_object* v___x_4060_; size_t v___x_4061_; size_t v___x_4062_; lean_object* v___x_4063_; 
lean_dec_ref_known(v___x_4059_, 1);
v___x_4060_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_4061_ = ((size_t)1ULL);
v___x_4062_ = lean_usize_add(v_i_4035_, v___x_4061_);
v___x_4063_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4028_, v___x_4029_, v___x_4030_, v___x_4031_, v___x_4032_, v_as_4033_, v_sz_4034_, v___x_4062_, v___x_4060_, v___y_4037_, v___y_4038_);
return v___x_4063_;
}
else
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4071_; 
lean_dec_ref(v___x_4031_);
lean_dec(v_stx_4028_);
v_a_4064_ = lean_ctor_get(v___x_4059_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4059_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4066_ = v___x_4059_;
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4059_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4069_; 
if (v_isShared_4067_ == 0)
{
v___x_4069_ = v___x_4066_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4064_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
}
}
}
else
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4097_; 
lean_dec_ref(v___x_4031_);
lean_dec(v_stx_4028_);
v_a_4090_ = lean_ctor_get(v___x_4043_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___x_4043_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4092_ = v___x_4043_;
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v___x_4043_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4095_; 
if (v_isShared_4093_ == 0)
{
v___x_4095_ = v___x_4092_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_a_4090_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
return v___x_4095_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4___boxed(lean_object* v_stx_4098_, lean_object* v___x_4099_, lean_object* v___x_4100_, lean_object* v___x_4101_, lean_object* v___x_4102_, lean_object* v_as_4103_, lean_object* v_sz_4104_, lean_object* v_i_4105_, lean_object* v_b_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
size_t v_sz_boxed_4110_; size_t v_i_boxed_4111_; lean_object* v_res_4112_; 
v_sz_boxed_4110_ = lean_unbox_usize(v_sz_4104_);
lean_dec(v_sz_4104_);
v_i_boxed_4111_ = lean_unbox_usize(v_i_4105_);
lean_dec(v_i_4105_);
v_res_4112_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(v_stx_4098_, v___x_4099_, v___x_4100_, v___x_4101_, v___x_4102_, v_as_4103_, v_sz_boxed_4110_, v_i_boxed_4111_, v_b_4106_, v___y_4107_, v___y_4108_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
lean_dec_ref(v_as_4103_);
lean_dec(v___x_4102_);
lean_dec_ref(v___x_4100_);
lean_dec_ref(v___x_4099_);
return v_res_4112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(lean_object* v_init_4113_, lean_object* v_stx_4114_, lean_object* v___x_4115_, lean_object* v___x_4116_, lean_object* v___x_4117_, lean_object* v___x_4118_, lean_object* v_n_4119_, lean_object* v_b_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_){
_start:
{
if (lean_obj_tag(v_n_4119_) == 0)
{
lean_object* v_cs_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; size_t v_sz_4127_; size_t v___x_4128_; lean_object* v___x_4129_; 
v_cs_4124_ = lean_ctor_get(v_n_4119_, 0);
v___x_4125_ = lean_box(0);
v___x_4126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4125_);
lean_ctor_set(v___x_4126_, 1, v_b_4120_);
v_sz_4127_ = lean_array_size(v_cs_4124_);
v___x_4128_ = ((size_t)0ULL);
v___x_4129_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(v_init_4113_, v_stx_4114_, v___x_4115_, v___x_4116_, v___x_4117_, v___x_4118_, v_cs_4124_, v_sz_4127_, v___x_4128_, v___x_4126_, v___y_4121_, v___y_4122_);
if (lean_obj_tag(v___x_4129_) == 0)
{
lean_object* v_a_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4144_; 
v_a_4130_ = lean_ctor_get(v___x_4129_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_4129_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4132_ = v___x_4129_;
v_isShared_4133_ = v_isSharedCheck_4144_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_a_4130_);
lean_dec(v___x_4129_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4144_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v_fst_4134_; 
v_fst_4134_ = lean_ctor_get(v_a_4130_, 0);
if (lean_obj_tag(v_fst_4134_) == 0)
{
lean_object* v_snd_4135_; lean_object* v___x_4136_; lean_object* v___x_4138_; 
v_snd_4135_ = lean_ctor_get(v_a_4130_, 1);
lean_inc(v_snd_4135_);
lean_dec(v_a_4130_);
v___x_4136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4136_, 0, v_snd_4135_);
if (v_isShared_4133_ == 0)
{
lean_ctor_set(v___x_4132_, 0, v___x_4136_);
v___x_4138_ = v___x_4132_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v___x_4136_);
v___x_4138_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
return v___x_4138_;
}
}
else
{
lean_object* v_val_4140_; lean_object* v___x_4142_; 
lean_inc_ref(v_fst_4134_);
lean_dec(v_a_4130_);
v_val_4140_ = lean_ctor_get(v_fst_4134_, 0);
lean_inc(v_val_4140_);
lean_dec_ref_known(v_fst_4134_, 1);
if (v_isShared_4133_ == 0)
{
lean_ctor_set(v___x_4132_, 0, v_val_4140_);
v___x_4142_ = v___x_4132_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_val_4140_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
return v___x_4142_;
}
}
}
}
else
{
lean_object* v_a_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4152_; 
v_a_4145_ = lean_ctor_get(v___x_4129_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_4129_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4147_ = v___x_4129_;
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_a_4145_);
lean_dec(v___x_4129_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4150_; 
if (v_isShared_4148_ == 0)
{
v___x_4150_ = v___x_4147_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_a_4145_);
v___x_4150_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
return v___x_4150_;
}
}
}
}
else
{
lean_object* v_vs_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; size_t v_sz_4156_; size_t v___x_4157_; lean_object* v___x_4158_; 
v_vs_4153_ = lean_ctor_get(v_n_4119_, 0);
v___x_4154_ = lean_box(0);
v___x_4155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4155_, 0, v___x_4154_);
lean_ctor_set(v___x_4155_, 1, v_b_4120_);
v_sz_4156_ = lean_array_size(v_vs_4153_);
v___x_4157_ = ((size_t)0ULL);
v___x_4158_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(v_stx_4114_, v___x_4115_, v___x_4116_, v___x_4117_, v___x_4118_, v_vs_4153_, v_sz_4156_, v___x_4157_, v___x_4155_, v___y_4121_, v___y_4122_);
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_object* v_a_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4173_; 
v_a_4159_ = lean_ctor_get(v___x_4158_, 0);
v_isSharedCheck_4173_ = !lean_is_exclusive(v___x_4158_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4161_ = v___x_4158_;
v_isShared_4162_ = v_isSharedCheck_4173_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_a_4159_);
lean_dec(v___x_4158_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4173_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v_fst_4163_; 
v_fst_4163_ = lean_ctor_get(v_a_4159_, 0);
if (lean_obj_tag(v_fst_4163_) == 0)
{
lean_object* v_snd_4164_; lean_object* v___x_4165_; lean_object* v___x_4167_; 
v_snd_4164_ = lean_ctor_get(v_a_4159_, 1);
lean_inc(v_snd_4164_);
lean_dec(v_a_4159_);
v___x_4165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4165_, 0, v_snd_4164_);
if (v_isShared_4162_ == 0)
{
lean_ctor_set(v___x_4161_, 0, v___x_4165_);
v___x_4167_ = v___x_4161_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v___x_4165_);
v___x_4167_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
return v___x_4167_;
}
}
else
{
lean_object* v_val_4169_; lean_object* v___x_4171_; 
lean_inc_ref(v_fst_4163_);
lean_dec(v_a_4159_);
v_val_4169_ = lean_ctor_get(v_fst_4163_, 0);
lean_inc(v_val_4169_);
lean_dec_ref_known(v_fst_4163_, 1);
if (v_isShared_4162_ == 0)
{
lean_ctor_set(v___x_4161_, 0, v_val_4169_);
v___x_4171_ = v___x_4161_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_val_4169_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
}
else
{
lean_object* v_a_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4181_; 
v_a_4174_ = lean_ctor_get(v___x_4158_, 0);
v_isSharedCheck_4181_ = !lean_is_exclusive(v___x_4158_);
if (v_isSharedCheck_4181_ == 0)
{
v___x_4176_ = v___x_4158_;
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_a_4174_);
lean_dec(v___x_4158_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v___x_4179_; 
if (v_isShared_4177_ == 0)
{
v___x_4179_ = v___x_4176_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_a_4174_);
v___x_4179_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
return v___x_4179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(lean_object* v_init_4182_, lean_object* v_stx_4183_, lean_object* v___x_4184_, lean_object* v___x_4185_, lean_object* v___x_4186_, lean_object* v___x_4187_, lean_object* v_as_4188_, size_t v_sz_4189_, size_t v_i_4190_, lean_object* v_b_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_){
_start:
{
uint8_t v___x_4195_; 
v___x_4195_ = lean_usize_dec_lt(v_i_4190_, v_sz_4189_);
if (v___x_4195_ == 0)
{
lean_object* v___x_4196_; 
lean_dec_ref(v___x_4186_);
lean_dec(v_stx_4183_);
v___x_4196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4196_, 0, v_b_4191_);
return v___x_4196_;
}
else
{
lean_object* v_snd_4197_; lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4231_; 
v_snd_4197_ = lean_ctor_get(v_b_4191_, 1);
v_isSharedCheck_4231_ = !lean_is_exclusive(v_b_4191_);
if (v_isSharedCheck_4231_ == 0)
{
lean_object* v_unused_4232_; 
v_unused_4232_ = lean_ctor_get(v_b_4191_, 0);
lean_dec(v_unused_4232_);
v___x_4199_ = v_b_4191_;
v_isShared_4200_ = v_isSharedCheck_4231_;
goto v_resetjp_4198_;
}
else
{
lean_inc(v_snd_4197_);
lean_dec(v_b_4191_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4231_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
lean_object* v_a_4201_; lean_object* v___x_4202_; 
v_a_4201_ = lean_array_uget_borrowed(v_as_4188_, v_i_4190_);
lean_inc(v_snd_4197_);
lean_inc_ref(v___x_4186_);
lean_inc(v_stx_4183_);
v___x_4202_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4182_, v_stx_4183_, v___x_4184_, v___x_4185_, v___x_4186_, v___x_4187_, v_a_4201_, v_snd_4197_, v___y_4192_, v___y_4193_);
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_object* v_a_4203_; lean_object* v___x_4205_; uint8_t v_isShared_4206_; uint8_t v_isSharedCheck_4222_; 
v_a_4203_ = lean_ctor_get(v___x_4202_, 0);
v_isSharedCheck_4222_ = !lean_is_exclusive(v___x_4202_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4205_ = v___x_4202_;
v_isShared_4206_ = v_isSharedCheck_4222_;
goto v_resetjp_4204_;
}
else
{
lean_inc(v_a_4203_);
lean_dec(v___x_4202_);
v___x_4205_ = lean_box(0);
v_isShared_4206_ = v_isSharedCheck_4222_;
goto v_resetjp_4204_;
}
v_resetjp_4204_:
{
if (lean_obj_tag(v_a_4203_) == 0)
{
lean_object* v___x_4207_; lean_object* v___x_4209_; 
lean_dec_ref(v___x_4186_);
lean_dec(v_stx_4183_);
v___x_4207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4207_, 0, v_a_4203_);
if (v_isShared_4200_ == 0)
{
lean_ctor_set(v___x_4199_, 0, v___x_4207_);
v___x_4209_ = v___x_4199_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v___x_4207_);
lean_ctor_set(v_reuseFailAlloc_4213_, 1, v_snd_4197_);
v___x_4209_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
lean_object* v___x_4211_; 
if (v_isShared_4206_ == 0)
{
lean_ctor_set(v___x_4205_, 0, v___x_4209_);
v___x_4211_ = v___x_4205_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v___x_4209_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
}
else
{
lean_object* v_a_4214_; lean_object* v___x_4215_; lean_object* v___x_4217_; 
lean_del_object(v___x_4205_);
lean_dec(v_snd_4197_);
v_a_4214_ = lean_ctor_get(v_a_4203_, 0);
lean_inc(v_a_4214_);
lean_dec_ref_known(v_a_4203_, 1);
v___x_4215_ = lean_box(0);
if (v_isShared_4200_ == 0)
{
lean_ctor_set(v___x_4199_, 1, v_a_4214_);
lean_ctor_set(v___x_4199_, 0, v___x_4215_);
v___x_4217_ = v___x_4199_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v___x_4215_);
lean_ctor_set(v_reuseFailAlloc_4221_, 1, v_a_4214_);
v___x_4217_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
size_t v___x_4218_; size_t v___x_4219_; 
v___x_4218_ = ((size_t)1ULL);
v___x_4219_ = lean_usize_add(v_i_4190_, v___x_4218_);
v_i_4190_ = v___x_4219_;
v_b_4191_ = v___x_4217_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4230_; 
lean_del_object(v___x_4199_);
lean_dec(v_snd_4197_);
lean_dec_ref(v___x_4186_);
lean_dec(v_stx_4183_);
v_a_4223_ = lean_ctor_get(v___x_4202_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___x_4202_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4225_ = v___x_4202_;
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___x_4202_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4228_; 
if (v_isShared_4226_ == 0)
{
v___x_4228_ = v___x_4225_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_a_4223_);
v___x_4228_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
return v___x_4228_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3___boxed(lean_object* v_init_4233_, lean_object* v_stx_4234_, lean_object* v___x_4235_, lean_object* v___x_4236_, lean_object* v___x_4237_, lean_object* v___x_4238_, lean_object* v_as_4239_, lean_object* v_sz_4240_, lean_object* v_i_4241_, lean_object* v_b_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_){
_start:
{
size_t v_sz_boxed_4246_; size_t v_i_boxed_4247_; lean_object* v_res_4248_; 
v_sz_boxed_4246_ = lean_unbox_usize(v_sz_4240_);
lean_dec(v_sz_4240_);
v_i_boxed_4247_ = lean_unbox_usize(v_i_4241_);
lean_dec(v_i_4241_);
v_res_4248_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(v_init_4233_, v_stx_4234_, v___x_4235_, v___x_4236_, v___x_4237_, v___x_4238_, v_as_4239_, v_sz_boxed_4246_, v_i_boxed_4247_, v_b_4242_, v___y_4243_, v___y_4244_);
lean_dec(v___y_4244_);
lean_dec_ref(v___y_4243_);
lean_dec_ref(v_as_4239_);
lean_dec(v___x_4238_);
lean_dec_ref(v___x_4236_);
lean_dec_ref(v___x_4235_);
return v_res_4248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2___boxed(lean_object* v_init_4249_, lean_object* v_stx_4250_, lean_object* v___x_4251_, lean_object* v___x_4252_, lean_object* v___x_4253_, lean_object* v___x_4254_, lean_object* v_n_4255_, lean_object* v_b_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
lean_object* v_res_4260_; 
v_res_4260_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4249_, v_stx_4250_, v___x_4251_, v___x_4252_, v___x_4253_, v___x_4254_, v_n_4255_, v_b_4256_, v___y_4257_, v___y_4258_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
lean_dec_ref(v_n_4255_);
lean_dec(v___x_4254_);
lean_dec_ref(v___x_4252_);
lean_dec_ref(v___x_4251_);
return v_res_4260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(lean_object* v_stx_4264_, lean_object* v___x_4265_, lean_object* v___x_4266_, lean_object* v___x_4267_, lean_object* v___x_4268_, lean_object* v_as_4269_, size_t v_sz_4270_, size_t v_i_4271_, lean_object* v_b_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_){
_start:
{
uint8_t v___x_4276_; 
v___x_4276_ = lean_usize_dec_lt(v_i_4271_, v_sz_4270_);
if (v___x_4276_ == 0)
{
lean_object* v___x_4277_; 
lean_dec_ref(v___x_4267_);
lean_dec(v_stx_4264_);
v___x_4277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4277_, 0, v_b_4272_);
return v___x_4277_;
}
else
{
lean_object* v_a_4278_; lean_object* v___x_4279_; 
lean_dec_ref(v_b_4272_);
v_a_4278_ = lean_array_uget_borrowed(v_as_4269_, v_i_4271_);
lean_inc(v_a_4278_);
lean_inc(v_stx_4264_);
v___x_4279_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_4264_, v___x_4265_, v_a_4278_, v___x_4266_, v___y_4273_, v___y_4274_);
if (lean_obj_tag(v___x_4279_) == 0)
{
lean_object* v_a_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v_scopes_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v_opts_4287_; uint8_t v_hasTrace_4288_; lean_object* v___x_4289_; lean_object* v___y_4291_; lean_object* v___y_4292_; 
v_a_4280_ = lean_ctor_get(v___x_4279_, 0);
lean_inc(v_a_4280_);
lean_dec_ref_known(v___x_4279_, 1);
v___x_4281_ = l_Lean_inheritedTraceOptions;
v___x_4282_ = lean_st_ref_get(v___x_4281_);
v___x_4283_ = lean_st_ref_get(v___y_4274_);
v_scopes_4284_ = lean_ctor_get(v___x_4283_, 2);
lean_inc(v_scopes_4284_);
lean_dec(v___x_4283_);
v___x_4285_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4286_ = l_List_head_x21___redArg(v___x_4285_, v_scopes_4284_);
lean_dec(v_scopes_4284_);
v_opts_4287_ = lean_ctor_get(v___x_4286_, 1);
lean_inc_ref(v_opts_4287_);
lean_dec(v___x_4286_);
v_hasTrace_4288_ = lean_ctor_get_uint8(v_opts_4287_, sizeof(void*)*1);
v___x_4289_ = lean_box(0);
if (v_hasTrace_4288_ == 0)
{
lean_dec_ref(v_opts_4287_);
lean_dec(v___x_4282_);
v___y_4291_ = v___y_4273_;
v___y_4292_ = v___y_4274_;
goto v___jp_4290_;
}
else
{
lean_object* v___x_4308_; lean_object* v___x_4309_; uint8_t v___x_4310_; 
v___x_4308_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4309_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3);
v___x_4310_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4282_, v_opts_4287_, v___x_4309_);
lean_dec_ref(v_opts_4287_);
lean_dec(v___x_4282_);
if (v___x_4310_ == 0)
{
v___y_4291_ = v___y_4273_;
v___y_4292_ = v___y_4274_;
goto v___jp_4290_;
}
else
{
lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
v___x_4311_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__2);
v___x_4312_ = lean_array_get_size(v_a_4280_);
v___x_4313_ = l_Nat_reprFast(v___x_4312_);
v___x_4314_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4313_);
v___x_4315_ = l_Lean_MessageData_ofFormat(v___x_4314_);
v___x_4316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4316_, 0, v___x_4311_);
lean_ctor_set(v___x_4316_, 1, v___x_4315_);
v___x_4317_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_4308_, v___x_4316_, v___y_4273_, v___y_4274_);
if (lean_obj_tag(v___x_4317_) == 0)
{
lean_dec_ref_known(v___x_4317_, 1);
v___y_4291_ = v___y_4273_;
v___y_4292_ = v___y_4274_;
goto v___jp_4290_;
}
else
{
lean_object* v_a_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4325_; 
lean_dec(v_a_4280_);
lean_dec_ref(v___x_4267_);
lean_dec(v_stx_4264_);
v_a_4318_ = lean_ctor_get(v___x_4317_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___x_4317_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4320_ = v___x_4317_;
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_a_4318_);
lean_dec(v___x_4317_);
v___x_4320_ = lean_box(0);
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
v_resetjp_4319_:
{
lean_object* v___x_4323_; 
if (v_isShared_4321_ == 0)
{
v___x_4323_ = v___x_4320_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v_a_4318_);
v___x_4323_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
return v___x_4323_;
}
}
}
}
}
v___jp_4290_:
{
size_t v_sz_4293_; size_t v___x_4294_; lean_object* v___x_4295_; 
v_sz_4293_ = lean_array_size(v_a_4280_);
v___x_4294_ = ((size_t)0ULL);
lean_inc_ref(v___x_4267_);
lean_inc(v_a_4278_);
v___x_4295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4278_, v___x_4267_, v___x_4268_, v_a_4280_, v_sz_4293_, v___x_4294_, v___x_4289_, v___y_4291_, v___y_4292_);
lean_dec(v_a_4280_);
if (lean_obj_tag(v___x_4295_) == 0)
{
lean_object* v___x_4296_; size_t v___x_4297_; size_t v___x_4298_; 
lean_dec_ref_known(v___x_4295_, 1);
v___x_4296_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_4297_ = ((size_t)1ULL);
v___x_4298_ = lean_usize_add(v_i_4271_, v___x_4297_);
v_i_4271_ = v___x_4298_;
v_b_4272_ = v___x_4296_;
goto _start;
}
else
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4307_; 
lean_dec_ref(v___x_4267_);
lean_dec(v_stx_4264_);
v_a_4300_ = lean_ctor_get(v___x_4295_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4295_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4302_ = v___x_4295_;
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___x_4295_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v___x_4305_; 
if (v_isShared_4303_ == 0)
{
v___x_4305_ = v___x_4302_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v_a_4300_);
v___x_4305_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
return v___x_4305_;
}
}
}
}
}
else
{
lean_object* v_a_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4333_; 
lean_dec_ref(v___x_4267_);
lean_dec(v_stx_4264_);
v_a_4326_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4333_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4333_ == 0)
{
v___x_4328_ = v___x_4279_;
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_a_4326_);
lean_dec(v___x_4279_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v___x_4331_; 
if (v_isShared_4329_ == 0)
{
v___x_4331_ = v___x_4328_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v_a_4326_);
v___x_4331_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
return v___x_4331_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___boxed(lean_object* v_stx_4334_, lean_object* v___x_4335_, lean_object* v___x_4336_, lean_object* v___x_4337_, lean_object* v___x_4338_, lean_object* v_as_4339_, lean_object* v_sz_4340_, lean_object* v_i_4341_, lean_object* v_b_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_){
_start:
{
size_t v_sz_boxed_4346_; size_t v_i_boxed_4347_; lean_object* v_res_4348_; 
v_sz_boxed_4346_ = lean_unbox_usize(v_sz_4340_);
lean_dec(v_sz_4340_);
v_i_boxed_4347_ = lean_unbox_usize(v_i_4341_);
lean_dec(v_i_4341_);
v_res_4348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_4334_, v___x_4335_, v___x_4336_, v___x_4337_, v___x_4338_, v_as_4339_, v_sz_boxed_4346_, v_i_boxed_4347_, v_b_4342_, v___y_4343_, v___y_4344_);
lean_dec(v___y_4344_);
lean_dec_ref(v___y_4343_);
lean_dec_ref(v_as_4339_);
lean_dec(v___x_4338_);
lean_dec_ref(v___x_4336_);
lean_dec_ref(v___x_4335_);
return v_res_4348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(lean_object* v_stx_4349_, lean_object* v___x_4350_, lean_object* v___x_4351_, lean_object* v___x_4352_, lean_object* v___x_4353_, lean_object* v_as_4354_, size_t v_sz_4355_, size_t v_i_4356_, lean_object* v_b_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_){
_start:
{
uint8_t v___x_4361_; 
v___x_4361_ = lean_usize_dec_lt(v_i_4356_, v_sz_4355_);
if (v___x_4361_ == 0)
{
lean_object* v___x_4362_; 
lean_dec_ref(v___x_4352_);
lean_dec(v_stx_4349_);
v___x_4362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4362_, 0, v_b_4357_);
return v___x_4362_;
}
else
{
lean_object* v_a_4363_; lean_object* v___x_4364_; 
lean_dec_ref(v_b_4357_);
v_a_4363_ = lean_array_uget_borrowed(v_as_4354_, v_i_4356_);
lean_inc(v_a_4363_);
lean_inc(v_stx_4349_);
v___x_4364_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_4349_, v___x_4350_, v_a_4363_, v___x_4351_, v___y_4358_, v___y_4359_);
if (lean_obj_tag(v___x_4364_) == 0)
{
lean_object* v_a_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v_scopes_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v_opts_4372_; uint8_t v_hasTrace_4373_; lean_object* v___x_4374_; lean_object* v___y_4376_; lean_object* v___y_4377_; 
v_a_4365_ = lean_ctor_get(v___x_4364_, 0);
lean_inc(v_a_4365_);
lean_dec_ref_known(v___x_4364_, 1);
v___x_4366_ = l_Lean_inheritedTraceOptions;
v___x_4367_ = lean_st_ref_get(v___x_4366_);
v___x_4368_ = lean_st_ref_get(v___y_4359_);
v_scopes_4369_ = lean_ctor_get(v___x_4368_, 2);
lean_inc(v_scopes_4369_);
lean_dec(v___x_4368_);
v___x_4370_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4371_ = l_List_head_x21___redArg(v___x_4370_, v_scopes_4369_);
lean_dec(v_scopes_4369_);
v_opts_4372_ = lean_ctor_get(v___x_4371_, 1);
lean_inc_ref(v_opts_4372_);
lean_dec(v___x_4371_);
v_hasTrace_4373_ = lean_ctor_get_uint8(v_opts_4372_, sizeof(void*)*1);
v___x_4374_ = lean_box(0);
if (v_hasTrace_4373_ == 0)
{
lean_dec_ref(v_opts_4372_);
lean_dec(v___x_4367_);
v___y_4376_ = v___y_4358_;
v___y_4377_ = v___y_4359_;
goto v___jp_4375_;
}
else
{
lean_object* v___x_4393_; lean_object* v___x_4394_; uint8_t v___x_4395_; 
v___x_4393_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4394_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3);
v___x_4395_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4367_, v_opts_4372_, v___x_4394_);
lean_dec_ref(v_opts_4372_);
lean_dec(v___x_4367_);
if (v___x_4395_ == 0)
{
v___y_4376_ = v___y_4358_;
v___y_4377_ = v___y_4359_;
goto v___jp_4375_;
}
else
{
lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; 
v___x_4396_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__2);
v___x_4397_ = lean_array_get_size(v_a_4365_);
v___x_4398_ = l_Nat_reprFast(v___x_4397_);
v___x_4399_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4399_, 0, v___x_4398_);
v___x_4400_ = l_Lean_MessageData_ofFormat(v___x_4399_);
v___x_4401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4401_, 0, v___x_4396_);
lean_ctor_set(v___x_4401_, 1, v___x_4400_);
v___x_4402_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_4393_, v___x_4401_, v___y_4358_, v___y_4359_);
if (lean_obj_tag(v___x_4402_) == 0)
{
lean_dec_ref_known(v___x_4402_, 1);
v___y_4376_ = v___y_4358_;
v___y_4377_ = v___y_4359_;
goto v___jp_4375_;
}
else
{
lean_object* v_a_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4410_; 
lean_dec(v_a_4365_);
lean_dec_ref(v___x_4352_);
lean_dec(v_stx_4349_);
v_a_4403_ = lean_ctor_get(v___x_4402_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4402_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4405_ = v___x_4402_;
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_a_4403_);
lean_dec(v___x_4402_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4408_; 
if (v_isShared_4406_ == 0)
{
v___x_4408_ = v___x_4405_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_a_4403_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
}
}
v___jp_4375_:
{
size_t v_sz_4378_; size_t v___x_4379_; lean_object* v___x_4380_; 
v_sz_4378_ = lean_array_size(v_a_4365_);
v___x_4379_ = ((size_t)0ULL);
lean_inc_ref(v___x_4352_);
lean_inc(v_a_4363_);
v___x_4380_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4363_, v___x_4352_, v___x_4353_, v_a_4365_, v_sz_4378_, v___x_4379_, v___x_4374_, v___y_4376_, v___y_4377_);
lean_dec(v_a_4365_);
if (lean_obj_tag(v___x_4380_) == 0)
{
lean_object* v___x_4381_; size_t v___x_4382_; size_t v___x_4383_; lean_object* v___x_4384_; 
lean_dec_ref_known(v___x_4380_, 1);
v___x_4381_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_4382_ = ((size_t)1ULL);
v___x_4383_ = lean_usize_add(v_i_4356_, v___x_4382_);
v___x_4384_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_4349_, v___x_4350_, v___x_4351_, v___x_4352_, v___x_4353_, v_as_4354_, v_sz_4355_, v___x_4383_, v___x_4381_, v___y_4358_, v___y_4359_);
return v___x_4384_;
}
else
{
lean_object* v_a_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4392_; 
lean_dec_ref(v___x_4352_);
lean_dec(v_stx_4349_);
v_a_4385_ = lean_ctor_get(v___x_4380_, 0);
v_isSharedCheck_4392_ = !lean_is_exclusive(v___x_4380_);
if (v_isSharedCheck_4392_ == 0)
{
v___x_4387_ = v___x_4380_;
v_isShared_4388_ = v_isSharedCheck_4392_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_a_4385_);
lean_dec(v___x_4380_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4392_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
lean_object* v___x_4390_; 
if (v_isShared_4388_ == 0)
{
v___x_4390_ = v___x_4387_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4391_; 
v_reuseFailAlloc_4391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4391_, 0, v_a_4385_);
v___x_4390_ = v_reuseFailAlloc_4391_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
return v___x_4390_;
}
}
}
}
}
else
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
lean_dec_ref(v___x_4352_);
lean_dec(v_stx_4349_);
v_a_4411_ = lean_ctor_get(v___x_4364_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4364_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4364_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4364_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_a_4411_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3___boxed(lean_object* v_stx_4419_, lean_object* v___x_4420_, lean_object* v___x_4421_, lean_object* v___x_4422_, lean_object* v___x_4423_, lean_object* v_as_4424_, lean_object* v_sz_4425_, lean_object* v_i_4426_, lean_object* v_b_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_){
_start:
{
size_t v_sz_boxed_4431_; size_t v_i_boxed_4432_; lean_object* v_res_4433_; 
v_sz_boxed_4431_ = lean_unbox_usize(v_sz_4425_);
lean_dec(v_sz_4425_);
v_i_boxed_4432_ = lean_unbox_usize(v_i_4426_);
lean_dec(v_i_4426_);
v_res_4433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(v_stx_4419_, v___x_4420_, v___x_4421_, v___x_4422_, v___x_4423_, v_as_4424_, v_sz_boxed_4431_, v_i_boxed_4432_, v_b_4427_, v___y_4428_, v___y_4429_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
lean_dec_ref(v_as_4424_);
lean_dec(v___x_4423_);
lean_dec_ref(v___x_4421_);
lean_dec_ref(v___x_4420_);
return v_res_4433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(lean_object* v___x_4434_, lean_object* v___x_4435_, lean_object* v_stx_4436_, lean_object* v___x_4437_, lean_object* v___x_4438_, lean_object* v_t_4439_, lean_object* v_init_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
lean_object* v_root_4444_; lean_object* v_tail_4445_; lean_object* v___x_4446_; 
v_root_4444_ = lean_ctor_get(v_t_4439_, 0);
v_tail_4445_ = lean_ctor_get(v_t_4439_, 1);
lean_inc_ref(v___x_4434_);
lean_inc(v_stx_4436_);
v___x_4446_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4440_, v_stx_4436_, v___x_4437_, v___x_4438_, v___x_4434_, v___x_4435_, v_root_4444_, v_init_4440_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4446_) == 0)
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4483_; 
v_a_4447_ = lean_ctor_get(v___x_4446_, 0);
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4449_ = v___x_4446_;
v_isShared_4450_ = v_isSharedCheck_4483_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4446_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4483_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
if (lean_obj_tag(v_a_4447_) == 0)
{
lean_object* v_a_4451_; lean_object* v___x_4453_; 
lean_dec(v_stx_4436_);
lean_dec_ref(v___x_4434_);
v_a_4451_ = lean_ctor_get(v_a_4447_, 0);
lean_inc(v_a_4451_);
lean_dec_ref_known(v_a_4447_, 1);
if (v_isShared_4450_ == 0)
{
lean_ctor_set(v___x_4449_, 0, v_a_4451_);
v___x_4453_ = v___x_4449_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4454_; 
v_reuseFailAlloc_4454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4454_, 0, v_a_4451_);
v___x_4453_ = v_reuseFailAlloc_4454_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
return v___x_4453_;
}
}
else
{
lean_object* v_a_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; size_t v_sz_4458_; size_t v___x_4459_; lean_object* v___x_4460_; 
lean_del_object(v___x_4449_);
v_a_4455_ = lean_ctor_get(v_a_4447_, 0);
lean_inc(v_a_4455_);
lean_dec_ref_known(v_a_4447_, 1);
v___x_4456_ = lean_box(0);
v___x_4457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4457_, 0, v___x_4456_);
lean_ctor_set(v___x_4457_, 1, v_a_4455_);
v_sz_4458_ = lean_array_size(v_tail_4445_);
v___x_4459_ = ((size_t)0ULL);
v___x_4460_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(v_stx_4436_, v___x_4437_, v___x_4438_, v___x_4434_, v___x_4435_, v_tail_4445_, v_sz_4458_, v___x_4459_, v___x_4457_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_object* v_a_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4474_; 
v_a_4461_ = lean_ctor_get(v___x_4460_, 0);
v_isSharedCheck_4474_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4474_ == 0)
{
v___x_4463_ = v___x_4460_;
v_isShared_4464_ = v_isSharedCheck_4474_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_dec(v___x_4460_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4474_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v_fst_4465_; 
v_fst_4465_ = lean_ctor_get(v_a_4461_, 0);
if (lean_obj_tag(v_fst_4465_) == 0)
{
lean_object* v_snd_4466_; lean_object* v___x_4468_; 
v_snd_4466_ = lean_ctor_get(v_a_4461_, 1);
lean_inc(v_snd_4466_);
lean_dec(v_a_4461_);
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 0, v_snd_4466_);
v___x_4468_ = v___x_4463_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v_snd_4466_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
return v___x_4468_;
}
}
else
{
lean_object* v_val_4470_; lean_object* v___x_4472_; 
lean_inc_ref(v_fst_4465_);
lean_dec(v_a_4461_);
v_val_4470_ = lean_ctor_get(v_fst_4465_, 0);
lean_inc(v_val_4470_);
lean_dec_ref_known(v_fst_4465_, 1);
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 0, v_val_4470_);
v___x_4472_ = v___x_4463_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4473_; 
v_reuseFailAlloc_4473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4473_, 0, v_val_4470_);
v___x_4472_ = v_reuseFailAlloc_4473_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
return v___x_4472_;
}
}
}
}
else
{
lean_object* v_a_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4482_; 
v_a_4475_ = lean_ctor_get(v___x_4460_, 0);
v_isSharedCheck_4482_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4482_ == 0)
{
v___x_4477_ = v___x_4460_;
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_a_4475_);
lean_dec(v___x_4460_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v___x_4480_; 
if (v_isShared_4478_ == 0)
{
v___x_4480_ = v___x_4477_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v_a_4475_);
v___x_4480_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
return v___x_4480_;
}
}
}
}
}
}
else
{
lean_object* v_a_4484_; lean_object* v___x_4486_; uint8_t v_isShared_4487_; uint8_t v_isSharedCheck_4491_; 
lean_dec(v_stx_4436_);
lean_dec_ref(v___x_4434_);
v_a_4484_ = lean_ctor_get(v___x_4446_, 0);
v_isSharedCheck_4491_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4491_ == 0)
{
v___x_4486_ = v___x_4446_;
v_isShared_4487_ = v_isSharedCheck_4491_;
goto v_resetjp_4485_;
}
else
{
lean_inc(v_a_4484_);
lean_dec(v___x_4446_);
v___x_4486_ = lean_box(0);
v_isShared_4487_ = v_isSharedCheck_4491_;
goto v_resetjp_4485_;
}
v_resetjp_4485_:
{
lean_object* v___x_4489_; 
if (v_isShared_4487_ == 0)
{
v___x_4489_ = v___x_4486_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v_a_4484_);
v___x_4489_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
return v___x_4489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2___boxed(lean_object* v___x_4492_, lean_object* v___x_4493_, lean_object* v_stx_4494_, lean_object* v___x_4495_, lean_object* v___x_4496_, lean_object* v_t_4497_, lean_object* v_init_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_){
_start:
{
lean_object* v_res_4502_; 
v_res_4502_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___x_4492_, v___x_4493_, v_stx_4494_, v___x_4495_, v___x_4496_, v_t_4497_, v_init_4498_, v___y_4499_, v___y_4500_);
lean_dec(v___y_4500_);
lean_dec_ref(v___y_4499_);
lean_dec_ref(v_t_4497_);
lean_dec_ref(v___x_4496_);
lean_dec_ref(v___x_4495_);
lean_dec(v___x_4493_);
return v_res_4502_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; 
v___x_4504_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__0));
v___x_4505_ = l_Lean_stringToMessageData(v___x_4504_);
return v___x_4505_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4509_; lean_object* v___x_4510_; 
v___x_4509_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__4));
v___x_4510_ = l_Lean_stringToMessageData(v___x_4509_);
return v___x_4510_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4512_; lean_object* v___x_4513_; 
v___x_4512_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__6));
v___x_4513_ = l_Lean_stringToMessageData(v___x_4512_);
return v___x_4513_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9(void){
_start:
{
lean_object* v___x_4515_; lean_object* v___x_4516_; 
v___x_4515_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__8));
v___x_4516_ = l_Lean_stringToMessageData(v___x_4515_);
return v___x_4516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(lean_object* v_stx_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_){
_start:
{
lean_object* v___x_4524_; lean_object* v_scopes_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v_opts_4528_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4533_; uint8_t v___y_4552_; lean_object* v___y_4553_; lean_object* v___y_4554_; uint8_t v___y_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4563_; uint8_t v___y_4569_; lean_object* v___y_4570_; uint8_t v___y_4571_; lean_object* v___y_4572_; lean_object* v___y_4573_; uint8_t v___y_4582_; uint8_t v___y_4583_; lean_object* v___y_4584_; uint8_t v___y_4585_; lean_object* v___y_4586_; lean_object* v___y_4587_; uint8_t v___y_4596_; uint8_t v___y_4597_; uint8_t v___y_4598_; uint8_t v___y_4632_; lean_object* v___x_4639_; uint8_t v___x_4640_; 
v___x_4524_ = lean_st_ref_get(v___y_4519_);
v_scopes_4525_ = lean_ctor_get(v___x_4524_, 2);
lean_inc(v_scopes_4525_);
lean_dec(v___x_4524_);
v___x_4526_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4527_ = l_List_head_x21___redArg(v___x_4526_, v_scopes_4525_);
lean_dec(v_scopes_4525_);
v_opts_4528_ = lean_ctor_get(v___x_4527_, 1);
lean_inc_ref(v_opts_4528_);
lean_dec(v___x_4527_);
v___x_4639_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_4640_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4528_, v___x_4639_);
if (v___x_4640_ == 0)
{
lean_object* v___x_4641_; uint8_t v___x_4642_; 
v___x_4641_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_4642_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4528_, v___x_4641_);
v___y_4632_ = v___x_4642_;
goto v___jp_4631_;
}
else
{
v___y_4632_ = v___x_4640_;
goto v___jp_4631_;
}
v___jp_4521_:
{
lean_object* v___x_4522_; lean_object* v___x_4523_; 
v___x_4522_ = lean_box(0);
v___x_4523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4523_, 0, v___x_4522_);
return v___x_4523_;
}
v___jp_4529_:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v_a_4536_; lean_object* v___x_4537_; lean_object* v_line_4538_; lean_object* v_messages_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4534_ = lean_st_ref_get(v___y_4532_);
v___x_4535_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_4532_);
v_a_4536_ = lean_ctor_get(v___x_4535_, 0);
lean_inc(v_a_4536_);
lean_dec_ref(v___x_4535_);
lean_inc_ref_n(v___y_4530_, 2);
v___x_4537_ = l_Lean_FileMap_toPosition(v___y_4530_, v___y_4533_);
lean_dec(v___y_4533_);
v_line_4538_ = lean_ctor_get(v___x_4537_, 0);
lean_inc(v_line_4538_);
lean_dec_ref(v___x_4537_);
v_messages_4539_ = lean_ctor_get(v___x_4534_, 1);
lean_inc_ref(v_messages_4539_);
lean_dec(v___x_4534_);
v___x_4540_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_4539_);
v___x_4541_ = lean_box(0);
v___x_4542_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___y_4530_, v_line_4538_, v_stx_4517_, v_opts_4528_, v___x_4540_, v_a_4536_, v___x_4541_, v___y_4531_, v___y_4532_);
lean_dec(v_a_4536_);
lean_dec_ref(v___x_4540_);
lean_dec_ref(v_opts_4528_);
lean_dec(v_line_4538_);
if (lean_obj_tag(v___x_4542_) == 0)
{
lean_object* v___x_4544_; uint8_t v_isShared_4545_; uint8_t v_isSharedCheck_4549_; 
v_isSharedCheck_4549_ = !lean_is_exclusive(v___x_4542_);
if (v_isSharedCheck_4549_ == 0)
{
lean_object* v_unused_4550_; 
v_unused_4550_ = lean_ctor_get(v___x_4542_, 0);
lean_dec(v_unused_4550_);
v___x_4544_ = v___x_4542_;
v_isShared_4545_ = v_isSharedCheck_4549_;
goto v_resetjp_4543_;
}
else
{
lean_dec(v___x_4542_);
v___x_4544_ = lean_box(0);
v_isShared_4545_ = v_isSharedCheck_4549_;
goto v_resetjp_4543_;
}
v_resetjp_4543_:
{
lean_object* v___x_4547_; 
if (v_isShared_4545_ == 0)
{
lean_ctor_set(v___x_4544_, 0, v___x_4541_);
v___x_4547_ = v___x_4544_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v___x_4541_);
v___x_4547_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4546_;
}
v_reusejp_4546_:
{
return v___x_4547_;
}
}
}
else
{
return v___x_4542_;
}
}
v___jp_4551_:
{
lean_object* v_fileMap_4555_; lean_object* v___x_4556_; 
v_fileMap_4555_ = lean_ctor_get(v___y_4553_, 1);
v___x_4556_ = l_Lean_Syntax_getPos_x3f(v_stx_4517_, v___y_4552_);
if (lean_obj_tag(v___x_4556_) == 0)
{
lean_object* v___x_4557_; 
v___x_4557_ = lean_unsigned_to_nat(0u);
v___y_4530_ = v_fileMap_4555_;
v___y_4531_ = v___y_4553_;
v___y_4532_ = v___y_4554_;
v___y_4533_ = v___x_4557_;
goto v___jp_4529_;
}
else
{
lean_object* v_val_4558_; 
v_val_4558_ = lean_ctor_get(v___x_4556_, 0);
lean_inc(v_val_4558_);
lean_dec_ref_known(v___x_4556_, 1);
v___y_4530_ = v_fileMap_4555_;
v___y_4531_ = v___y_4553_;
v___y_4532_ = v___y_4554_;
v___y_4533_ = v_val_4558_;
goto v___jp_4529_;
}
}
v___jp_4559_:
{
lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; 
lean_inc_ref(v___y_4563_);
v___x_4564_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4564_, 0, v___y_4563_);
v___x_4565_ = l_Lean_MessageData_ofFormat(v___x_4564_);
v___x_4566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4566_, 0, v___y_4562_);
lean_ctor_set(v___x_4566_, 1, v___x_4565_);
lean_inc(v___y_4561_);
v___x_4567_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___y_4561_, v___x_4566_, v___y_4518_, v___y_4519_);
if (lean_obj_tag(v___x_4567_) == 0)
{
lean_dec_ref_known(v___x_4567_, 1);
v___y_4552_ = v___y_4560_;
v___y_4553_ = v___y_4518_;
v___y_4554_ = v___y_4519_;
goto v___jp_4551_;
}
else
{
lean_dec_ref(v_opts_4528_);
lean_dec(v_stx_4517_);
return v___x_4567_;
}
}
v___jp_4568_:
{
lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; 
lean_inc_ref(v___y_4573_);
v___x_4574_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4574_, 0, v___y_4573_);
v___x_4575_ = l_Lean_MessageData_ofFormat(v___x_4574_);
v___x_4576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4576_, 0, v___y_4572_);
lean_ctor_set(v___x_4576_, 1, v___x_4575_);
v___x_4577_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1);
v___x_4578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4578_, 0, v___x_4576_);
lean_ctor_set(v___x_4578_, 1, v___x_4577_);
if (v___y_4571_ == 0)
{
lean_object* v___x_4579_; 
v___x_4579_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4560_ = v___y_4569_;
v___y_4561_ = v___y_4570_;
v___y_4562_ = v___x_4578_;
v___y_4563_ = v___x_4579_;
goto v___jp_4559_;
}
else
{
lean_object* v___x_4580_; 
v___x_4580_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4560_ = v___y_4569_;
v___y_4561_ = v___y_4570_;
v___y_4562_ = v___x_4578_;
v___y_4563_ = v___x_4580_;
goto v___jp_4559_;
}
}
v___jp_4581_:
{
lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; 
lean_inc_ref(v___y_4587_);
v___x_4588_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4588_, 0, v___y_4587_);
v___x_4589_ = l_Lean_MessageData_ofFormat(v___x_4588_);
lean_inc_ref(v___y_4586_);
v___x_4590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4590_, 0, v___y_4586_);
lean_ctor_set(v___x_4590_, 1, v___x_4589_);
v___x_4591_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5);
v___x_4592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4592_, 0, v___x_4590_);
lean_ctor_set(v___x_4592_, 1, v___x_4591_);
if (v___y_4583_ == 0)
{
lean_object* v___x_4593_; 
v___x_4593_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4569_ = v___y_4582_;
v___y_4570_ = v___y_4584_;
v___y_4571_ = v___y_4585_;
v___y_4572_ = v___x_4592_;
v___y_4573_ = v___x_4593_;
goto v___jp_4568_;
}
else
{
lean_object* v___x_4594_; 
v___x_4594_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4569_ = v___y_4582_;
v___y_4570_ = v___y_4584_;
v___y_4571_ = v___y_4585_;
v___y_4572_ = v___x_4592_;
v___y_4573_ = v___x_4594_;
goto v___jp_4568_;
}
}
v___jp_4595_:
{
lean_object* v___x_4599_; lean_object* v_a_4600_; uint8_t v___x_4601_; 
v___x_4599_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(v_stx_4517_, v___y_4518_, v___y_4519_);
v_a_4600_ = lean_ctor_get(v___x_4599_, 0);
lean_inc(v_a_4600_);
lean_dec_ref(v___x_4599_);
v___x_4601_ = lean_unbox(v_a_4600_);
if (v___x_4601_ == 0)
{
lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v_scopes_4605_; lean_object* v___x_4606_; lean_object* v_opts_4607_; uint8_t v_hasTrace_4608_; 
v___x_4602_ = l_Lean_inheritedTraceOptions;
v___x_4603_ = lean_st_ref_get(v___x_4602_);
v___x_4604_ = lean_st_ref_get(v___y_4519_);
v_scopes_4605_ = lean_ctor_get(v___x_4604_, 2);
lean_inc(v_scopes_4605_);
lean_dec(v___x_4604_);
v___x_4606_ = l_List_head_x21___redArg(v___x_4526_, v_scopes_4605_);
lean_dec(v_scopes_4605_);
v_opts_4607_ = lean_ctor_get(v___x_4606_, 1);
lean_inc_ref(v_opts_4607_);
lean_dec(v___x_4606_);
v_hasTrace_4608_ = lean_ctor_get_uint8(v_opts_4607_, sizeof(void*)*1);
if (v_hasTrace_4608_ == 0)
{
uint8_t v___x_4609_; 
lean_dec_ref(v_opts_4607_);
lean_dec(v___x_4603_);
v___x_4609_ = lean_unbox(v_a_4600_);
lean_dec(v_a_4600_);
v___y_4552_ = v___x_4609_;
v___y_4553_ = v___y_4518_;
v___y_4554_ = v___y_4519_;
goto v___jp_4551_;
}
else
{
lean_object* v___x_4610_; lean_object* v___x_4611_; uint8_t v___x_4612_; 
v___x_4610_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4611_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3);
v___x_4612_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4603_, v_opts_4607_, v___x_4611_);
lean_dec_ref(v_opts_4607_);
lean_dec(v___x_4603_);
if (v___x_4612_ == 0)
{
uint8_t v___x_4613_; 
v___x_4613_ = lean_unbox(v_a_4600_);
lean_dec(v_a_4600_);
v___y_4552_ = v___x_4613_;
v___y_4553_ = v___y_4518_;
v___y_4554_ = v___y_4519_;
goto v___jp_4551_;
}
else
{
lean_object* v___x_4614_; 
v___x_4614_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7);
if (v___y_4597_ == 0)
{
lean_object* v___x_4615_; uint8_t v___x_4616_; 
v___x_4615_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___x_4616_ = lean_unbox(v_a_4600_);
lean_dec(v_a_4600_);
v___y_4582_ = v___x_4616_;
v___y_4583_ = v___y_4596_;
v___y_4584_ = v___x_4610_;
v___y_4585_ = v___y_4598_;
v___y_4586_ = v___x_4614_;
v___y_4587_ = v___x_4615_;
goto v___jp_4581_;
}
else
{
lean_object* v___x_4617_; uint8_t v___x_4618_; 
v___x_4617_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___x_4618_ = lean_unbox(v_a_4600_);
lean_dec(v_a_4600_);
v___y_4582_ = v___x_4618_;
v___y_4583_ = v___y_4596_;
v___y_4584_ = v___x_4610_;
v___y_4585_ = v___y_4598_;
v___y_4586_ = v___x_4614_;
v___y_4587_ = v___x_4617_;
goto v___jp_4581_;
}
}
}
}
else
{
lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v_scopes_4622_; lean_object* v___x_4623_; lean_object* v_opts_4624_; uint8_t v_hasTrace_4625_; 
lean_dec(v_a_4600_);
lean_dec_ref(v_opts_4528_);
lean_dec(v_stx_4517_);
v___x_4619_ = l_Lean_inheritedTraceOptions;
v___x_4620_ = lean_st_ref_get(v___x_4619_);
v___x_4621_ = lean_st_ref_get(v___y_4519_);
v_scopes_4622_ = lean_ctor_get(v___x_4621_, 2);
lean_inc(v_scopes_4622_);
lean_dec(v___x_4621_);
v___x_4623_ = l_List_head_x21___redArg(v___x_4526_, v_scopes_4622_);
lean_dec(v_scopes_4622_);
v_opts_4624_ = lean_ctor_get(v___x_4623_, 1);
lean_inc_ref(v_opts_4624_);
lean_dec(v___x_4623_);
v_hasTrace_4625_ = lean_ctor_get_uint8(v_opts_4624_, sizeof(void*)*1);
if (v_hasTrace_4625_ == 0)
{
lean_dec_ref(v_opts_4624_);
lean_dec(v___x_4620_);
goto v___jp_4521_;
}
else
{
lean_object* v___x_4626_; lean_object* v___x_4627_; uint8_t v___x_4628_; 
v___x_4626_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4627_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__12_spec__13___closed__3);
v___x_4628_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4620_, v_opts_4624_, v___x_4627_);
lean_dec_ref(v_opts_4624_);
lean_dec(v___x_4620_);
if (v___x_4628_ == 0)
{
goto v___jp_4521_;
}
else
{
lean_object* v___x_4629_; lean_object* v___x_4630_; 
v___x_4629_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9);
v___x_4630_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_4626_, v___x_4629_, v___y_4518_, v___y_4519_);
if (lean_obj_tag(v___x_4630_) == 0)
{
lean_dec_ref_known(v___x_4630_, 1);
goto v___jp_4521_;
}
else
{
return v___x_4630_;
}
}
}
}
}
v___jp_4631_:
{
lean_object* v___x_4633_; uint8_t v___x_4634_; lean_object* v___x_4635_; uint8_t v___x_4636_; 
v___x_4633_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
v___x_4634_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4528_, v___x_4633_);
v___x_4635_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v___x_4636_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4528_, v___x_4635_);
if (v___y_4632_ == 0)
{
if (v___x_4634_ == 0)
{
if (v___x_4636_ == 0)
{
lean_object* v___x_4637_; lean_object* v___x_4638_; 
lean_dec_ref(v_opts_4528_);
lean_dec(v_stx_4517_);
v___x_4637_ = lean_box(0);
v___x_4638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4638_, 0, v___x_4637_);
return v___x_4638_;
}
else
{
v___y_4596_ = v___x_4634_;
v___y_4597_ = v___y_4632_;
v___y_4598_ = v___x_4636_;
goto v___jp_4595_;
}
}
else
{
v___y_4596_ = v___x_4634_;
v___y_4597_ = v___y_4632_;
v___y_4598_ = v___x_4636_;
goto v___jp_4595_;
}
}
else
{
v___y_4596_ = v___x_4634_;
v___y_4597_ = v___y_4632_;
v___y_4598_ = v___x_4636_;
goto v___jp_4595_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___boxed(lean_object* v_stx_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_){
_start:
{
lean_object* v_res_4647_; 
v_res_4647_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(v_stx_4643_, v___y_4644_, v___y_4645_);
lean_dec(v___y_4645_);
lean_dec_ref(v___y_4644_);
return v_res_4647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4660_; lean_object* v___x_4661_; 
v___x_4660_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook));
v___x_4661_ = l_Lean_Elab_Command_addLinter(v___x_4660_);
return v___x_4661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2____boxed(lean_object* v_a_4662_){
_start:
{
lean_object* v_res_4663_; 
v_res_4663_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_();
return v_res_4663_;
}
}
lean_object* runtime_initialize_Init_Try(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_InfoUtils(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Try(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Meta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_BuiltinTerm(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_AutoTry(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Try(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_InfoUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Try(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_BuiltinTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof);
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy);
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal);
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry);
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_debug_autoTry_showEdits = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_debug_autoTry_showEdits);
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed__const__1 = _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed__const__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed__const__1);
res = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_AutoTry(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Try(uint8_t builtin);
lean_object* initialize_Lean_Linter_Basic(uint8_t builtin);
lean_object* initialize_Lean_Server_InfoUtils(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Try(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Meta(uint8_t builtin);
lean_object* initialize_Lean_Elab_BuiltinTerm(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_AutoTry(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Try(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_InfoUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Try(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_AutoTry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_AutoTry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_AutoTry(builtin);
}
#ifdef __cplusplus
}
#endif
