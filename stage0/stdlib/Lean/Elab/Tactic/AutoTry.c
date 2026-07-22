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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Syntax_instHashableRange_hash(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_Range_includes(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Try_collectTryCoreSuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isMaxRecDepth(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_ofPosition(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
lean_object* l_Lean_withSetOptionIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__6_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__value)}};
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
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 205, 46, 93, 234, 75, 44, 75)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 55, 102, 232, 177, 170, 100, 130)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0___closed__1_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 145, .m_capacity = 145, .m_length = 144, .m_data = "Tactic.unsolvedGoals message yielded no (msgCtx, namingCtx, goal) tuples; producer not following the `withContext`/`withNamingContext` contract\?"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "no tacticSeq body found for unsolved-goals message at "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "; unrecognised seq variant\?"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10_spec__12(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1;
static const lean_closure_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__2_value;
static const lean_array_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3_spec__8(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "trigger points: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_withSetOptionIn___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___closed__0_value)} };
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
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_120_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_));
v___x_121_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__9_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_));
v___x_122_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_));
v___x_123_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__spec__0(v___x_120_, v___x_121_, v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4____boxed(lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_();
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_140_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4_));
v___x_141_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4_));
v___x_142_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4_));
v___x_143_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__spec__0(v___x_140_, v___x_141_, v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4____boxed(lean_object* v_a_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4_();
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_160_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4_));
v___x_161_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4_));
v___x_162_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4_));
v___x_163_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__spec__0(v___x_160_, v___x_161_, v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4____boxed(lean_object* v_a_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4_();
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_188_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4_));
v___x_189_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4_));
v___x_190_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4_));
v___x_191_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__spec__0(v___x_188_, v___x_189_, v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4____boxed(lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4_();
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_231_; uint8_t v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_231_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_232_ = 0;
v___x_233_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__14_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_234_ = l_Lean_registerTraceClass(v___x_231_, v___x_232_, v___x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2____boxed(lean_object* v_a_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_();
return v_res_236_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(lean_object* v_opts_237_, lean_object* v_opt_238_){
_start:
{
lean_object* v_name_239_; lean_object* v_defValue_240_; lean_object* v_map_241_; lean_object* v___x_242_; 
v_name_239_ = lean_ctor_get(v_opt_238_, 0);
v_defValue_240_ = lean_ctor_get(v_opt_238_, 1);
v_map_241_ = lean_ctor_get(v_opts_237_, 0);
v___x_242_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_241_, v_name_239_);
if (lean_obj_tag(v___x_242_) == 0)
{
uint8_t v___x_243_; 
v___x_243_ = lean_unbox(v_defValue_240_);
return v___x_243_;
}
else
{
lean_object* v_val_244_; 
v_val_244_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_val_244_);
lean_dec_ref_known(v___x_242_, 1);
if (lean_obj_tag(v_val_244_) == 1)
{
uint8_t v_v_245_; 
v_v_245_ = lean_ctor_get_uint8(v_val_244_, 0);
lean_dec_ref_known(v_val_244_, 0);
return v_v_245_;
}
else
{
uint8_t v___x_246_; 
lean_dec(v_val_244_);
v___x_246_ = lean_unbox(v_defValue_240_);
return v___x_246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0___boxed(lean_object* v_opts_247_, lean_object* v_opt_248_){
_start:
{
uint8_t v_res_249_; lean_object* v_r_250_; 
v_res_249_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_247_, v_opt_248_);
lean_dec_ref(v_opt_248_);
lean_dec_ref(v_opts_247_);
v_r_250_ = lean_box(v_res_249_);
return v_r_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__1(lean_object* v_opts_251_, lean_object* v_opt_252_){
_start:
{
lean_object* v_name_253_; lean_object* v_defValue_254_; lean_object* v_map_255_; lean_object* v___x_256_; 
v_name_253_ = lean_ctor_get(v_opt_252_, 0);
v_defValue_254_ = lean_ctor_get(v_opt_252_, 1);
v_map_255_ = lean_ctor_get(v_opts_251_, 0);
v___x_256_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_255_, v_name_253_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_inc(v_defValue_254_);
return v_defValue_254_;
}
else
{
lean_object* v_val_257_; 
v_val_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_val_257_);
lean_dec_ref_known(v___x_256_, 1);
if (lean_obj_tag(v_val_257_) == 3)
{
lean_object* v_v_258_; 
v_v_258_ = lean_ctor_get(v_val_257_, 0);
lean_inc(v_v_258_);
lean_dec_ref_known(v_val_257_, 1);
return v_v_258_;
}
else
{
lean_dec(v_val_257_);
lean_inc(v_defValue_254_);
return v_defValue_254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__1___boxed(lean_object* v_opts_259_, lean_object* v_opt_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__1(v_opts_259_, v_opt_260_);
lean_dec_ref(v_opt_260_);
lean_dec_ref(v_opts_259_);
return v_res_261_;
}
}
static uint64_t _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__1(void){
_start:
{
lean_object* v___x_268_; uint64_t v___x_269_; 
v___x_268_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__0));
v___x_269_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_268_);
return v___x_269_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__2(void){
_start:
{
uint64_t v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_270_ = lean_uint64_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__1);
v___x_271_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__0));
v___x_272_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set_uint64(v___x_272_, sizeof(void*)*1, v___x_270_);
return v___x_272_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4(void){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_275_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
return v___x_277_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__6(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5);
v___x_279_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
lean_ctor_set(v___x_279_, 2, v___x_278_);
lean_ctor_set(v___x_279_, 3, v___x_278_);
lean_ctor_set(v___x_279_, 4, v___x_278_);
lean_ctor_set(v___x_279_, 5, v___x_278_);
return v___x_279_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__7(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = lean_unsigned_to_nat(32u);
v___x_281_ = lean_mk_empty_array_with_capacity(v___x_280_);
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
return v___x_282_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8(void){
_start:
{
size_t v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_283_ = ((size_t)5ULL);
v___x_284_ = lean_unsigned_to_nat(0u);
v___x_285_ = lean_unsigned_to_nat(32u);
v___x_286_ = lean_mk_empty_array_with_capacity(v___x_285_);
v___x_287_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__7, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__7);
v___x_288_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v___x_286_);
lean_ctor_set(v___x_288_, 2, v___x_284_);
lean_ctor_set(v___x_288_, 3, v___x_284_);
lean_ctor_set_usize(v___x_288_, 4, v___x_283_);
return v___x_288_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5);
v___x_290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
lean_ctor_set(v___x_290_, 2, v___x_289_);
lean_ctor_set(v___x_290_, 3, v___x_289_);
lean_ctor_set(v___x_290_, 4, v___x_289_);
return v___x_290_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5);
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
return v___x_292_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = l_Lean_NameSet_empty;
v___x_294_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8);
v___x_295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
lean_ctor_set(v___x_295_, 2, v___x_293_);
return v___x_295_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = lean_unsigned_to_nat(1u);
v___x_297_ = l_Lean_firstFrontendMacroScope;
v___x_298_ = lean_nat_add(v___x_297_, v___x_296_);
return v___x_298_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17(void){
_start:
{
lean_object* v___x_309_; uint64_t v___x_310_; lean_object* v___x_311_; 
v___x_309_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8);
v___x_310_ = 0ULL;
v___x_311_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_311_, 0, v___x_309_);
lean_ctor_set_uint64(v___x_311_, sizeof(void*)*1, v___x_310_);
return v___x_311_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; uint8_t v___x_314_; lean_object* v___x_315_; 
v___x_312_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8);
v___x_313_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5);
v___x_314_ = 1;
v___x_315_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_315_, 0, v___x_313_);
lean_ctor_set(v___x_315_, 1, v___x_313_);
lean_ctor_set(v___x_315_, 2, v___x_312_);
lean_ctor_set_uint8(v___x_315_, sizeof(void*)*3, v___x_314_);
return v___x_315_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = l_Lean_Options_empty;
v___x_317_ = l_Lean_Core_getMaxHeartbeats(v___x_316_);
return v___x_317_;
}
}
static uint8_t _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_321_ = l_Lean_diagnostics;
v___x_322_ = l_Lean_Options_empty;
v___x_323_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v___x_322_, v___x_321_);
return v___x_323_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_324_ = l_Lean_maxRecDepth;
v___x_325_ = l_Lean_Options_empty;
v___x_326_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__1(v___x_325_, v___x_324_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(lean_object* v_env_327_, lean_object* v_mctx_328_, lean_object* v_lctx_329_, lean_object* v_opts_330_, lean_object* v_namingCtx_331_, lean_object* v_x_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v___x_336_; uint8_t v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v_fileName_363_; lean_object* v_fileMap_364_; lean_object* v_ref_365_; lean_object* v_cancelTk_x3f_366_; lean_object* v_a_368_; lean_object* v_a_375_; lean_object* v_currNamespace_377_; lean_object* v_openDecls_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v_env_384_; lean_object* v___x_385_; lean_object* v___y_387_; uint8_t v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_478_; uint8_t v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; uint8_t v___y_482_; lean_object* v___x_502_; uint8_t v___x_503_; lean_object* v___y_505_; lean_object* v___y_506_; uint8_t v___y_536_; uint8_t v___x_556_; 
v___x_336_ = lean_box(1);
v___x_337_ = 0;
v___x_338_ = l_Lean_Environment_setExporting(v_env_327_, v___x_337_);
v___x_339_ = 1;
v___x_340_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__2, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__2_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__2);
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__3));
v___x_343_ = lean_box(0);
v___x_344_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_344_, 0, v___x_340_);
lean_ctor_set(v___x_344_, 1, v___x_336_);
lean_ctor_set(v___x_344_, 2, v_lctx_329_);
lean_ctor_set(v___x_344_, 3, v___x_342_);
lean_ctor_set(v___x_344_, 4, v___x_343_);
lean_ctor_set(v___x_344_, 5, v___x_341_);
lean_ctor_set(v___x_344_, 6, v___x_343_);
lean_ctor_set_uint8(v___x_344_, sizeof(void*)*7, v___x_337_);
lean_ctor_set_uint8(v___x_344_, sizeof(void*)*7 + 1, v___x_337_);
lean_ctor_set_uint8(v___x_344_, sizeof(void*)*7 + 2, v___x_337_);
lean_ctor_set_uint8(v___x_344_, sizeof(void*)*7 + 3, v___x_339_);
v___x_345_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__6, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__6_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__6);
v___x_346_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8);
v___x_347_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9);
v___x_348_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10);
v___x_349_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11);
v___x_350_ = lean_io_get_num_heartbeats();
v___x_351_ = l_Lean_firstFrontendMacroScope;
v___x_352_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12);
v___x_353_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__15));
v___x_354_ = lean_box(0);
v___x_355_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__16));
v___x_356_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17);
v___x_357_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18);
v___x_358_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_358_, 0, v___x_338_);
lean_ctor_set(v___x_358_, 1, v___x_352_);
lean_ctor_set(v___x_358_, 2, v___x_353_);
lean_ctor_set(v___x_358_, 3, v___x_355_);
lean_ctor_set(v___x_358_, 4, v___x_356_);
lean_ctor_set(v___x_358_, 5, v___x_348_);
lean_ctor_set(v___x_358_, 6, v___x_349_);
lean_ctor_set(v___x_358_, 7, v___x_357_);
lean_ctor_set(v___x_358_, 8, v___x_342_);
v___x_359_ = lean_st_mk_ref(v___x_358_);
v___x_360_ = l_Lean_inheritedTraceOptions;
v___x_361_ = lean_st_ref_get(v___x_360_);
v___x_362_ = lean_st_ref_get(v___x_359_);
v_fileName_363_ = lean_ctor_get(v_a_333_, 0);
v_fileMap_364_ = lean_ctor_get(v_a_333_, 1);
v_ref_365_ = lean_ctor_get(v_a_333_, 7);
v_cancelTk_x3f_366_ = lean_ctor_get(v_a_333_, 9);
v_currNamespace_377_ = lean_ctor_get(v_namingCtx_331_, 0);
v_openDecls_378_ = lean_ctor_get(v_namingCtx_331_, 1);
v___x_379_ = l_Lean_Options_empty;
v___x_380_ = lean_unsigned_to_nat(1000u);
v___x_381_ = lean_box(0);
v___x_382_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19);
lean_inc(v_cancelTk_x3f_366_);
lean_inc(v_openDecls_378_);
lean_inc(v_currNamespace_377_);
lean_inc_ref(v_fileMap_364_);
lean_inc_ref(v_fileName_363_);
v___x_383_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_383_, 0, v_fileName_363_);
lean_ctor_set(v___x_383_, 1, v_fileMap_364_);
lean_ctor_set(v___x_383_, 2, v___x_379_);
lean_ctor_set(v___x_383_, 3, v___x_341_);
lean_ctor_set(v___x_383_, 4, v___x_380_);
lean_ctor_set(v___x_383_, 5, v___x_381_);
lean_ctor_set(v___x_383_, 6, v_currNamespace_377_);
lean_ctor_set(v___x_383_, 7, v_openDecls_378_);
lean_ctor_set(v___x_383_, 8, v___x_350_);
lean_ctor_set(v___x_383_, 9, v___x_382_);
lean_ctor_set(v___x_383_, 10, v___x_354_);
lean_ctor_set(v___x_383_, 11, v___x_351_);
lean_ctor_set(v___x_383_, 12, v_cancelTk_x3f_366_);
lean_ctor_set(v___x_383_, 13, v___x_361_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*14, v___x_337_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*14 + 1, v___x_337_);
v_env_384_ = lean_ctor_get(v___x_362_, 0);
lean_inc_ref(v_env_384_);
lean_dec(v___x_362_);
v___x_385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_385_, 0, v_mctx_328_);
lean_ctor_set(v___x_385_, 1, v___x_345_);
lean_ctor_set(v___x_385_, 2, v___x_336_);
lean_ctor_set(v___x_385_, 3, v___x_346_);
lean_ctor_set(v___x_385_, 4, v___x_347_);
v___x_502_ = l_Lean_diagnostics;
v___x_503_ = lean_uint8_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23);
v___x_556_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_384_);
lean_dec_ref(v_env_384_);
if (v___x_556_ == 0)
{
if (v___x_503_ == 0)
{
lean_inc(v___x_359_);
v___y_505_ = v___x_383_;
v___y_506_ = v___x_359_;
goto v___jp_504_;
}
else
{
v___y_536_ = v___x_556_;
goto v___jp_535_;
}
}
else
{
v___y_536_ = v___x_503_;
goto v___jp_535_;
}
v___jp_367_:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_369_ = lean_io_error_to_string(v_a_368_);
v___x_370_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
v___x_371_ = l_Lean_MessageData_ofFormat(v___x_370_);
lean_inc(v_ref_365_);
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v_ref_365_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
v___x_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
return v___x_373_;
}
v___jp_374_:
{
lean_object* v___x_376_; 
v___x_376_ = lean_mk_io_user_error(v_a_375_);
v_a_368_ = v___x_376_;
goto v___jp_367_;
}
v___jp_386_:
{
lean_object* v___x_391_; lean_object* v_fileName_392_; lean_object* v_fileMap_393_; lean_object* v_currRecDepth_394_; lean_object* v_ref_395_; lean_object* v_currNamespace_396_; lean_object* v_openDecls_397_; lean_object* v_initHeartbeats_398_; lean_object* v_maxHeartbeats_399_; lean_object* v_quotContext_400_; lean_object* v_currMacroScope_401_; lean_object* v_cancelTk_x3f_402_; uint8_t v_suppressElabErrors_403_; lean_object* v_inheritedTraceOptions_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_474_; 
v___x_391_ = lean_st_mk_ref(v___x_385_);
v_fileName_392_ = lean_ctor_get(v___y_389_, 0);
v_fileMap_393_ = lean_ctor_get(v___y_389_, 1);
v_currRecDepth_394_ = lean_ctor_get(v___y_389_, 3);
v_ref_395_ = lean_ctor_get(v___y_389_, 5);
v_currNamespace_396_ = lean_ctor_get(v___y_389_, 6);
v_openDecls_397_ = lean_ctor_get(v___y_389_, 7);
v_initHeartbeats_398_ = lean_ctor_get(v___y_389_, 8);
v_maxHeartbeats_399_ = lean_ctor_get(v___y_389_, 9);
v_quotContext_400_ = lean_ctor_get(v___y_389_, 10);
v_currMacroScope_401_ = lean_ctor_get(v___y_389_, 11);
v_cancelTk_x3f_402_ = lean_ctor_get(v___y_389_, 12);
v_suppressElabErrors_403_ = lean_ctor_get_uint8(v___y_389_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_404_ = lean_ctor_get(v___y_389_, 13);
v_isSharedCheck_474_ = !lean_is_exclusive(v___y_389_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; lean_object* v_unused_476_; 
v_unused_475_ = lean_ctor_get(v___y_389_, 4);
lean_dec(v_unused_475_);
v_unused_476_ = lean_ctor_get(v___y_389_, 2);
lean_dec(v_unused_476_);
v___x_406_ = v___y_389_;
v_isShared_407_ = v_isSharedCheck_474_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_inheritedTraceOptions_404_);
lean_inc(v_cancelTk_x3f_402_);
lean_inc(v_currMacroScope_401_);
lean_inc(v_quotContext_400_);
lean_inc(v_maxHeartbeats_399_);
lean_inc(v_initHeartbeats_398_);
lean_inc(v_openDecls_397_);
lean_inc(v_currNamespace_396_);
lean_inc(v_ref_395_);
lean_inc(v_currRecDepth_394_);
lean_inc(v_fileMap_393_);
lean_inc(v_fileName_392_);
lean_dec(v___y_389_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_474_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_408_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__1(v_opts_330_, v___y_387_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 4, v___x_408_);
lean_ctor_set(v___x_406_, 2, v_opts_330_);
v___x_410_ = v___x_406_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_fileName_392_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_fileMap_393_);
lean_ctor_set(v_reuseFailAlloc_473_, 2, v_opts_330_);
lean_ctor_set(v_reuseFailAlloc_473_, 3, v_currRecDepth_394_);
lean_ctor_set(v_reuseFailAlloc_473_, 4, v___x_408_);
lean_ctor_set(v_reuseFailAlloc_473_, 5, v_ref_395_);
lean_ctor_set(v_reuseFailAlloc_473_, 6, v_currNamespace_396_);
lean_ctor_set(v_reuseFailAlloc_473_, 7, v_openDecls_397_);
lean_ctor_set(v_reuseFailAlloc_473_, 8, v_initHeartbeats_398_);
lean_ctor_set(v_reuseFailAlloc_473_, 9, v_maxHeartbeats_399_);
lean_ctor_set(v_reuseFailAlloc_473_, 10, v_quotContext_400_);
lean_ctor_set(v_reuseFailAlloc_473_, 11, v_currMacroScope_401_);
lean_ctor_set(v_reuseFailAlloc_473_, 12, v_cancelTk_x3f_402_);
lean_ctor_set(v_reuseFailAlloc_473_, 13, v_inheritedTraceOptions_404_);
lean_ctor_set_uint8(v_reuseFailAlloc_473_, sizeof(void*)*14 + 1, v_suppressElabErrors_403_);
v___x_410_ = v_reuseFailAlloc_473_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_411_; 
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*14, v___y_388_);
lean_inc(v___x_391_);
v___x_411_ = lean_apply_5(v_x_332_, v___x_344_, v___x_391_, v___x_410_, v___y_390_, lean_box(0));
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_457_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_457_ == 0)
{
v___x_414_ = v___x_411_;
v_isShared_415_ = v_isSharedCheck_457_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_457_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v_traceState_419_; lean_object* v_traceState_420_; lean_object* v_env_421_; lean_object* v_messages_422_; lean_object* v_scopes_423_; lean_object* v_usedQuotCtxts_424_; lean_object* v_nextMacroScope_425_; lean_object* v_maxRecDepth_426_; lean_object* v_ngen_427_; lean_object* v_auxDeclNGen_428_; lean_object* v_infoState_429_; lean_object* v_snapshotTasks_430_; lean_object* v_prevLinterStates_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_455_; 
v___x_416_ = lean_st_ref_get(v___x_391_);
lean_dec(v___x_391_);
lean_dec(v___x_416_);
v___x_417_ = lean_st_ref_get(v___x_359_);
lean_dec(v___x_359_);
v___x_418_ = lean_st_ref_take(v_a_334_);
v_traceState_419_ = lean_ctor_get(v___x_418_, 9);
lean_inc_ref(v_traceState_419_);
v_traceState_420_ = lean_ctor_get(v___x_417_, 4);
lean_inc_ref(v_traceState_420_);
v_env_421_ = lean_ctor_get(v___x_418_, 0);
v_messages_422_ = lean_ctor_get(v___x_418_, 1);
v_scopes_423_ = lean_ctor_get(v___x_418_, 2);
v_usedQuotCtxts_424_ = lean_ctor_get(v___x_418_, 3);
v_nextMacroScope_425_ = lean_ctor_get(v___x_418_, 4);
v_maxRecDepth_426_ = lean_ctor_get(v___x_418_, 5);
v_ngen_427_ = lean_ctor_get(v___x_418_, 6);
v_auxDeclNGen_428_ = lean_ctor_get(v___x_418_, 7);
v_infoState_429_ = lean_ctor_get(v___x_418_, 8);
v_snapshotTasks_430_ = lean_ctor_get(v___x_418_, 10);
v_prevLinterStates_431_ = lean_ctor_get(v___x_418_, 11);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_455_ == 0)
{
lean_object* v_unused_456_; 
v_unused_456_ = lean_ctor_get(v___x_418_, 9);
lean_dec(v_unused_456_);
v___x_433_ = v___x_418_;
v_isShared_434_ = v_isSharedCheck_455_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_prevLinterStates_431_);
lean_inc(v_snapshotTasks_430_);
lean_inc(v_infoState_429_);
lean_inc(v_auxDeclNGen_428_);
lean_inc(v_ngen_427_);
lean_inc(v_maxRecDepth_426_);
lean_inc(v_nextMacroScope_425_);
lean_inc(v_usedQuotCtxts_424_);
lean_inc(v_scopes_423_);
lean_inc(v_messages_422_);
lean_inc(v_env_421_);
lean_dec(v___x_418_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_455_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v_messages_435_; uint64_t v_tid_436_; lean_object* v_traces_437_; lean_object* v_traces_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_454_; 
v_messages_435_ = lean_ctor_get(v___x_417_, 6);
lean_inc_ref(v_messages_435_);
lean_dec(v___x_417_);
v_tid_436_ = lean_ctor_get_uint64(v_traceState_419_, sizeof(void*)*1);
v_traces_437_ = lean_ctor_get(v_traceState_419_, 0);
lean_inc_ref(v_traces_437_);
lean_dec_ref(v_traceState_419_);
v_traces_438_ = lean_ctor_get(v_traceState_420_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v_traceState_420_);
if (v_isSharedCheck_454_ == 0)
{
v___x_440_ = v_traceState_420_;
v_isShared_441_ = v_isSharedCheck_454_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_traces_438_);
lean_dec(v_traceState_420_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_454_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_445_; 
v___x_442_ = l_Lean_MessageLog_append(v_messages_422_, v_messages_435_);
v___x_443_ = l_Lean_PersistentArray_append___redArg(v_traces_437_, v_traces_438_);
lean_dec_ref(v_traces_438_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_443_);
v___x_445_ = v___x_440_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_443_);
v___x_445_ = v_reuseFailAlloc_453_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_447_; 
lean_ctor_set_uint64(v___x_445_, sizeof(void*)*1, v_tid_436_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 9, v___x_445_);
lean_ctor_set(v___x_433_, 1, v___x_442_);
v___x_447_ = v___x_433_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_env_421_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_452_, 2, v_scopes_423_);
lean_ctor_set(v_reuseFailAlloc_452_, 3, v_usedQuotCtxts_424_);
lean_ctor_set(v_reuseFailAlloc_452_, 4, v_nextMacroScope_425_);
lean_ctor_set(v_reuseFailAlloc_452_, 5, v_maxRecDepth_426_);
lean_ctor_set(v_reuseFailAlloc_452_, 6, v_ngen_427_);
lean_ctor_set(v_reuseFailAlloc_452_, 7, v_auxDeclNGen_428_);
lean_ctor_set(v_reuseFailAlloc_452_, 8, v_infoState_429_);
lean_ctor_set(v_reuseFailAlloc_452_, 9, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_452_, 10, v_snapshotTasks_430_);
lean_ctor_set(v_reuseFailAlloc_452_, 11, v_prevLinterStates_431_);
v___x_447_ = v_reuseFailAlloc_452_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_448_ = lean_st_ref_set(v_a_334_, v___x_447_);
if (v_isShared_415_ == 0)
{
v___x_450_ = v___x_414_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_412_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_458_; 
lean_dec(v___x_391_);
lean_dec(v___x_359_);
v_a_458_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_458_);
lean_dec_ref_known(v___x_411_, 1);
if (lean_obj_tag(v_a_458_) == 0)
{
lean_object* v_msg_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v_msg_459_ = lean_ctor_get(v_a_458_, 1);
lean_inc_ref(v_msg_459_);
lean_dec_ref_known(v_a_458_, 2);
v___x_460_ = l_Lean_MessageData_toString(v_msg_459_);
v___x_461_ = lean_mk_io_user_error(v___x_460_);
v_a_368_ = v___x_461_;
goto v___jp_367_;
}
else
{
lean_object* v_id_462_; lean_object* v___x_463_; 
v_id_462_ = lean_ctor_get(v_a_458_, 0);
lean_inc(v_id_462_);
lean_dec_ref_known(v_a_458_, 2);
v___x_463_ = l_Lean_InternalExceptionId_getName(v_id_462_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
lean_dec(v_id_462_);
v_a_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_a_464_);
lean_dec_ref_known(v___x_463_, 1);
v___x_465_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20));
v___x_466_ = l_Lean_Name_toString(v_a_464_, v___x_339_);
v___x_467_ = lean_string_append(v___x_465_, v___x_466_);
lean_dec_ref(v___x_466_);
v_a_375_ = v___x_467_;
goto v___jp_374_;
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
lean_dec_ref_known(v___x_463_, 1);
v___x_468_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21));
v___x_469_ = l_Nat_reprFast(v_id_462_);
v___x_470_ = lean_string_append(v___x_468_, v___x_469_);
lean_dec_ref(v___x_469_);
v___x_471_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__22));
v___x_472_ = lean_string_append(v___x_470_, v___x_471_);
v_a_375_ = v___x_472_;
goto v___jp_374_;
}
}
}
}
}
}
v___jp_477_:
{
if (v___y_482_ == 0)
{
lean_object* v___x_483_; lean_object* v_env_484_; lean_object* v_nextMacroScope_485_; lean_object* v_ngen_486_; lean_object* v_auxDeclNGen_487_; lean_object* v_traceState_488_; lean_object* v_messages_489_; lean_object* v_infoState_490_; lean_object* v_snapshotTasks_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_500_; 
v___x_483_ = lean_st_ref_take(v___y_481_);
v_env_484_ = lean_ctor_get(v___x_483_, 0);
v_nextMacroScope_485_ = lean_ctor_get(v___x_483_, 1);
v_ngen_486_ = lean_ctor_get(v___x_483_, 2);
v_auxDeclNGen_487_ = lean_ctor_get(v___x_483_, 3);
v_traceState_488_ = lean_ctor_get(v___x_483_, 4);
v_messages_489_ = lean_ctor_get(v___x_483_, 6);
v_infoState_490_ = lean_ctor_get(v___x_483_, 7);
v_snapshotTasks_491_ = lean_ctor_get(v___x_483_, 8);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_500_ == 0)
{
lean_object* v_unused_501_; 
v_unused_501_ = lean_ctor_get(v___x_483_, 5);
lean_dec(v_unused_501_);
v___x_493_ = v___x_483_;
v_isShared_494_ = v_isSharedCheck_500_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_snapshotTasks_491_);
lean_inc(v_infoState_490_);
lean_inc(v_messages_489_);
lean_inc(v_traceState_488_);
lean_inc(v_auxDeclNGen_487_);
lean_inc(v_ngen_486_);
lean_inc(v_nextMacroScope_485_);
lean_inc(v_env_484_);
lean_dec(v___x_483_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_500_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___x_497_; 
v___x_495_ = l_Lean_Kernel_enableDiag(v_env_484_, v___y_479_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 5, v___x_348_);
lean_ctor_set(v___x_493_, 0, v___x_495_);
v___x_497_ = v___x_493_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_495_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_nextMacroScope_485_);
lean_ctor_set(v_reuseFailAlloc_499_, 2, v_ngen_486_);
lean_ctor_set(v_reuseFailAlloc_499_, 3, v_auxDeclNGen_487_);
lean_ctor_set(v_reuseFailAlloc_499_, 4, v_traceState_488_);
lean_ctor_set(v_reuseFailAlloc_499_, 5, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_499_, 6, v_messages_489_);
lean_ctor_set(v_reuseFailAlloc_499_, 7, v_infoState_490_);
lean_ctor_set(v_reuseFailAlloc_499_, 8, v_snapshotTasks_491_);
v___x_497_ = v_reuseFailAlloc_499_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
lean_object* v___x_498_; 
v___x_498_ = lean_st_ref_set(v___y_481_, v___x_497_);
v___y_387_ = v___y_478_;
v___y_388_ = v___y_479_;
v___y_389_ = v___y_480_;
v___y_390_ = v___y_481_;
goto v___jp_386_;
}
}
}
else
{
v___y_387_ = v___y_478_;
v___y_388_ = v___y_479_;
v___y_389_ = v___y_480_;
v___y_390_ = v___y_481_;
goto v___jp_386_;
}
}
v___jp_504_:
{
lean_object* v___x_507_; lean_object* v_fileName_508_; lean_object* v_fileMap_509_; lean_object* v_currRecDepth_510_; lean_object* v_ref_511_; lean_object* v_currNamespace_512_; lean_object* v_openDecls_513_; lean_object* v_initHeartbeats_514_; lean_object* v_maxHeartbeats_515_; lean_object* v_quotContext_516_; lean_object* v_currMacroScope_517_; lean_object* v_cancelTk_x3f_518_; uint8_t v_suppressElabErrors_519_; lean_object* v_inheritedTraceOptions_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_532_; 
v___x_507_ = lean_st_ref_get(v___y_506_);
v_fileName_508_ = lean_ctor_get(v___y_505_, 0);
v_fileMap_509_ = lean_ctor_get(v___y_505_, 1);
v_currRecDepth_510_ = lean_ctor_get(v___y_505_, 3);
v_ref_511_ = lean_ctor_get(v___y_505_, 5);
v_currNamespace_512_ = lean_ctor_get(v___y_505_, 6);
v_openDecls_513_ = lean_ctor_get(v___y_505_, 7);
v_initHeartbeats_514_ = lean_ctor_get(v___y_505_, 8);
v_maxHeartbeats_515_ = lean_ctor_get(v___y_505_, 9);
v_quotContext_516_ = lean_ctor_get(v___y_505_, 10);
v_currMacroScope_517_ = lean_ctor_get(v___y_505_, 11);
v_cancelTk_x3f_518_ = lean_ctor_get(v___y_505_, 12);
v_suppressElabErrors_519_ = lean_ctor_get_uint8(v___y_505_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_520_ = lean_ctor_get(v___y_505_, 13);
v_isSharedCheck_532_ = !lean_is_exclusive(v___y_505_);
if (v_isSharedCheck_532_ == 0)
{
lean_object* v_unused_533_; lean_object* v_unused_534_; 
v_unused_533_ = lean_ctor_get(v___y_505_, 4);
lean_dec(v_unused_533_);
v_unused_534_ = lean_ctor_get(v___y_505_, 2);
lean_dec(v_unused_534_);
v___x_522_ = v___y_505_;
v_isShared_523_ = v_isSharedCheck_532_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_inheritedTraceOptions_520_);
lean_inc(v_cancelTk_x3f_518_);
lean_inc(v_currMacroScope_517_);
lean_inc(v_quotContext_516_);
lean_inc(v_maxHeartbeats_515_);
lean_inc(v_initHeartbeats_514_);
lean_inc(v_openDecls_513_);
lean_inc(v_currNamespace_512_);
lean_inc(v_ref_511_);
lean_inc(v_currRecDepth_510_);
lean_inc(v_fileMap_509_);
lean_inc(v_fileName_508_);
lean_dec(v___y_505_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_532_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v_env_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
v_env_524_ = lean_ctor_get(v___x_507_, 0);
lean_inc_ref(v_env_524_);
lean_dec(v___x_507_);
v___x_525_ = l_Lean_maxRecDepth;
v___x_526_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 4, v___x_526_);
lean_ctor_set(v___x_522_, 2, v___x_379_);
v___x_528_ = v___x_522_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_fileName_508_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_fileMap_509_);
lean_ctor_set(v_reuseFailAlloc_531_, 2, v___x_379_);
lean_ctor_set(v_reuseFailAlloc_531_, 3, v_currRecDepth_510_);
lean_ctor_set(v_reuseFailAlloc_531_, 4, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_531_, 5, v_ref_511_);
lean_ctor_set(v_reuseFailAlloc_531_, 6, v_currNamespace_512_);
lean_ctor_set(v_reuseFailAlloc_531_, 7, v_openDecls_513_);
lean_ctor_set(v_reuseFailAlloc_531_, 8, v_initHeartbeats_514_);
lean_ctor_set(v_reuseFailAlloc_531_, 9, v_maxHeartbeats_515_);
lean_ctor_set(v_reuseFailAlloc_531_, 10, v_quotContext_516_);
lean_ctor_set(v_reuseFailAlloc_531_, 11, v_currMacroScope_517_);
lean_ctor_set(v_reuseFailAlloc_531_, 12, v_cancelTk_x3f_518_);
lean_ctor_set(v_reuseFailAlloc_531_, 13, v_inheritedTraceOptions_520_);
lean_ctor_set_uint8(v_reuseFailAlloc_531_, sizeof(void*)*14 + 1, v_suppressElabErrors_519_);
v___x_528_ = v_reuseFailAlloc_531_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
uint8_t v___x_529_; uint8_t v___x_530_; 
lean_ctor_set_uint8(v___x_528_, sizeof(void*)*14, v___x_503_);
v___x_529_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_330_, v___x_502_);
v___x_530_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_524_);
lean_dec_ref(v_env_524_);
if (v___x_530_ == 0)
{
if (v___x_529_ == 0)
{
v___y_387_ = v___x_525_;
v___y_388_ = v___x_529_;
v___y_389_ = v___x_528_;
v___y_390_ = v___y_506_;
goto v___jp_386_;
}
else
{
v___y_478_ = v___x_525_;
v___y_479_ = v___x_529_;
v___y_480_ = v___x_528_;
v___y_481_ = v___y_506_;
v___y_482_ = v___x_530_;
goto v___jp_477_;
}
}
else
{
v___y_478_ = v___x_525_;
v___y_479_ = v___x_529_;
v___y_480_ = v___x_528_;
v___y_481_ = v___y_506_;
v___y_482_ = v___x_529_;
goto v___jp_477_;
}
}
}
}
v___jp_535_:
{
if (v___y_536_ == 0)
{
lean_object* v___x_537_; lean_object* v_env_538_; lean_object* v_nextMacroScope_539_; lean_object* v_ngen_540_; lean_object* v_auxDeclNGen_541_; lean_object* v_traceState_542_; lean_object* v_messages_543_; lean_object* v_infoState_544_; lean_object* v_snapshotTasks_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_554_; 
v___x_537_ = lean_st_ref_take(v___x_359_);
v_env_538_ = lean_ctor_get(v___x_537_, 0);
v_nextMacroScope_539_ = lean_ctor_get(v___x_537_, 1);
v_ngen_540_ = lean_ctor_get(v___x_537_, 2);
v_auxDeclNGen_541_ = lean_ctor_get(v___x_537_, 3);
v_traceState_542_ = lean_ctor_get(v___x_537_, 4);
v_messages_543_ = lean_ctor_get(v___x_537_, 6);
v_infoState_544_ = lean_ctor_get(v___x_537_, 7);
v_snapshotTasks_545_ = lean_ctor_get(v___x_537_, 8);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; 
v_unused_555_ = lean_ctor_get(v___x_537_, 5);
lean_dec(v_unused_555_);
v___x_547_ = v___x_537_;
v_isShared_548_ = v_isSharedCheck_554_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_snapshotTasks_545_);
lean_inc(v_infoState_544_);
lean_inc(v_messages_543_);
lean_inc(v_traceState_542_);
lean_inc(v_auxDeclNGen_541_);
lean_inc(v_ngen_540_);
lean_inc(v_nextMacroScope_539_);
lean_inc(v_env_538_);
lean_dec(v___x_537_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_554_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_549_ = l_Lean_Kernel_enableDiag(v_env_538_, v___x_503_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 5, v___x_348_);
lean_ctor_set(v___x_547_, 0, v___x_549_);
v___x_551_ = v___x_547_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_nextMacroScope_539_);
lean_ctor_set(v_reuseFailAlloc_553_, 2, v_ngen_540_);
lean_ctor_set(v_reuseFailAlloc_553_, 3, v_auxDeclNGen_541_);
lean_ctor_set(v_reuseFailAlloc_553_, 4, v_traceState_542_);
lean_ctor_set(v_reuseFailAlloc_553_, 5, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_553_, 6, v_messages_543_);
lean_ctor_set(v_reuseFailAlloc_553_, 7, v_infoState_544_);
lean_ctor_set(v_reuseFailAlloc_553_, 8, v_snapshotTasks_545_);
v___x_551_ = v_reuseFailAlloc_553_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; 
v___x_552_ = lean_st_ref_set(v___x_359_, v___x_551_);
lean_inc(v___x_359_);
v___y_505_ = v___x_383_;
v___y_506_ = v___x_359_;
goto v___jp_504_;
}
}
}
else
{
lean_inc(v___x_359_);
v___y_505_ = v___x_383_;
v___y_506_ = v___x_359_;
goto v___jp_504_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___boxed(lean_object* v_env_557_, lean_object* v_mctx_558_, lean_object* v_lctx_559_, lean_object* v_opts_560_, lean_object* v_namingCtx_561_, lean_object* v_x_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_557_, v_mctx_558_, v_lctx_559_, v_opts_560_, v_namingCtx_561_, v_x_562_, v_a_563_, v_a_564_);
lean_dec(v_a_564_);
lean_dec_ref(v_a_563_);
lean_dec_ref(v_namingCtx_561_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope(lean_object* v_00_u03b1_567_, lean_object* v_env_568_, lean_object* v_mctx_569_, lean_object* v_lctx_570_, lean_object* v_opts_571_, lean_object* v_namingCtx_572_, lean_object* v_x_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_568_, v_mctx_569_, v_lctx_570_, v_opts_571_, v_namingCtx_572_, v_x_573_, v_a_574_, v_a_575_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___boxed(lean_object* v_00_u03b1_578_, lean_object* v_env_579_, lean_object* v_mctx_580_, lean_object* v_lctx_581_, lean_object* v_opts_582_, lean_object* v_namingCtx_583_, lean_object* v_x_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope(v_00_u03b1_578_, v_env_579_, v_mctx_580_, v_lctx_581_, v_opts_582_, v_namingCtx_583_, v_x_584_, v_a_585_, v_a_586_);
lean_dec(v_a_586_);
lean_dec_ref(v_a_585_);
lean_dec_ref(v_namingCtx_583_);
return v_res_588_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(lean_object* v_stx_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_Syntax_getKind(v_stx_592_);
if (lean_obj_tag(v___x_593_) == 1)
{
lean_object* v_pre_594_; 
v_pre_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_pre_594_);
if (lean_obj_tag(v_pre_594_) == 1)
{
lean_object* v_pre_595_; 
v_pre_595_ = lean_ctor_get(v_pre_594_, 0);
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
if (lean_obj_tag(v_pre_597_) == 0)
{
lean_object* v_str_598_; lean_object* v_str_599_; lean_object* v_str_600_; lean_object* v_str_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v_str_598_ = lean_ctor_get(v___x_593_, 1);
lean_inc_ref(v_str_598_);
lean_dec_ref_known(v___x_593_, 2);
v_str_599_ = lean_ctor_get(v_pre_594_, 1);
lean_inc_ref(v_str_599_);
lean_dec_ref_known(v_pre_594_, 2);
v_str_600_ = lean_ctor_get(v_pre_595_, 1);
lean_inc_ref(v_str_600_);
lean_dec_ref_known(v_pre_595_, 2);
v_str_601_ = lean_ctor_get(v_pre_596_, 1);
lean_inc_ref(v_str_601_);
lean_dec_ref_known(v_pre_596_, 2);
v___x_602_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_603_ = lean_string_dec_eq(v_str_601_, v___x_602_);
lean_dec_ref(v_str_601_);
if (v___x_603_ == 0)
{
lean_dec_ref(v_str_600_);
lean_dec_ref(v_str_599_);
lean_dec_ref(v_str_598_);
return v___x_603_;
}
else
{
lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_604_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0));
v___x_605_ = lean_string_dec_eq(v_str_600_, v___x_604_);
lean_dec_ref(v_str_600_);
if (v___x_605_ == 0)
{
lean_dec_ref(v_str_599_);
lean_dec_ref(v_str_598_);
return v___x_605_;
}
else
{
lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_606_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_607_ = lean_string_dec_eq(v_str_599_, v___x_606_);
lean_dec_ref(v_str_599_);
if (v___x_607_ == 0)
{
lean_dec_ref(v_str_598_);
return v___x_607_;
}
else
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__1));
v___x_609_ = lean_string_dec_eq(v_str_598_, v___x_608_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__2));
v___x_611_ = lean_string_dec_eq(v_str_598_, v___x_610_);
lean_dec_ref(v_str_598_);
return v___x_611_;
}
else
{
lean_dec_ref(v_str_598_);
return v___x_609_;
}
}
}
}
}
else
{
uint8_t v___x_612_; 
lean_dec_ref_known(v_pre_596_, 2);
lean_dec_ref_known(v_pre_595_, 2);
lean_dec_ref_known(v_pre_594_, 2);
lean_dec_ref_known(v___x_593_, 2);
v___x_612_ = 0;
return v___x_612_;
}
}
else
{
uint8_t v___x_613_; 
lean_dec(v_pre_596_);
lean_dec_ref_known(v_pre_595_, 2);
lean_dec_ref_known(v_pre_594_, 2);
lean_dec_ref_known(v___x_593_, 2);
v___x_613_ = 0;
return v___x_613_;
}
}
else
{
uint8_t v___x_614_; 
lean_dec(v_pre_595_);
lean_dec_ref_known(v_pre_594_, 2);
lean_dec_ref_known(v___x_593_, 2);
v___x_614_ = 0;
return v___x_614_;
}
}
else
{
uint8_t v___x_615_; 
lean_dec_ref_known(v___x_593_, 2);
lean_dec(v_pre_594_);
v___x_615_ = 0;
return v___x_615_;
}
}
else
{
uint8_t v___x_616_; 
lean_dec(v___x_593_);
v___x_616_ = 0;
return v___x_616_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___boxed(lean_object* v_stx_617_){
_start:
{
uint8_t v_res_618_; lean_object* v_r_619_; 
v_res_618_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(v_stx_617_);
v_r_619_ = lean_box(v_res_618_);
return v_r_619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx(lean_object* v_x_620_){
_start:
{
if (lean_obj_tag(v_x_620_) == 0)
{
lean_object* v___x_621_; 
v___x_621_ = lean_unsigned_to_nat(0u);
return v___x_621_;
}
else
{
lean_object* v___x_622_; 
v___x_622_ = lean_unsigned_to_nat(1u);
return v___x_622_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx___boxed(lean_object* v_x_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx(v_x_623_);
lean_dec(v_x_623_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(lean_object* v_t_625_, lean_object* v_k_626_){
_start:
{
if (lean_obj_tag(v_t_625_) == 0)
{
lean_object* v_tacticSeq_627_; lean_object* v_insertPos_628_; lean_object* v___x_629_; 
v_tacticSeq_627_ = lean_ctor_get(v_t_625_, 0);
lean_inc(v_tacticSeq_627_);
v_insertPos_628_ = lean_ctor_get(v_t_625_, 1);
lean_inc(v_insertPos_628_);
lean_dec_ref_known(v_t_625_, 2);
v___x_629_ = lean_apply_2(v_k_626_, v_tacticSeq_627_, v_insertPos_628_);
return v___x_629_;
}
else
{
return v_k_626_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim(lean_object* v_motive_630_, lean_object* v_ctorIdx_631_, lean_object* v_t_632_, lean_object* v_h_633_, lean_object* v_k_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_632_, v_k_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___boxed(lean_object* v_motive_636_, lean_object* v_ctorIdx_637_, lean_object* v_t_638_, lean_object* v_h_639_, lean_object* v_k_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim(v_motive_636_, v_ctorIdx_637_, v_t_638_, v_h_639_, v_k_640_);
lean_dec(v_ctorIdx_637_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_unsolvedGoal_elim___redArg(lean_object* v_t_642_, lean_object* v_unsolvedGoal_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_642_, v_unsolvedGoal_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_unsolvedGoal_elim(lean_object* v_motive_645_, lean_object* v_t_646_, lean_object* v_h_647_, lean_object* v_unsolvedGoal_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_646_, v_unsolvedGoal_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_sorryTactic_elim___redArg(lean_object* v_t_650_, lean_object* v_sorryTactic_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_650_, v_sorryTactic_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_sorryTactic_elim(lean_object* v_motive_653_, lean_object* v_t_654_, lean_object* v_h_655_, lean_object* v_sorryTactic_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_654_, v_sorryTactic_656_);
return v___x_657_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed__const__1(void){
_start:
{
uint32_t v___x_661_; lean_object* v___x_662_; 
v___x_661_ = 32;
v___x_662_ = lean_box_uint32(v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(lean_object* v_tacticSeq_663_, lean_object* v_fileMap_664_){
_start:
{
uint8_t v___x_665_; lean_object* v___x_666_; 
v___x_665_ = 0;
v___x_666_ = l_Lean_Syntax_getPos_x3f(v_tacticSeq_663_, v___x_665_);
if (lean_obj_tag(v___x_666_) == 1)
{
lean_object* v_val_667_; lean_object* v___x_668_; 
v_val_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_val_667_);
lean_dec_ref_known(v___x_666_, 1);
v___x_668_ = l_Lean_Syntax_getTailPos_x3f(v_tacticSeq_663_, v___x_665_);
if (lean_obj_tag(v___x_668_) == 1)
{
lean_object* v_val_669_; lean_object* v_startPos_670_; lean_object* v_line_671_; lean_object* v_column_672_; lean_object* v_endPos_673_; lean_object* v_line_674_; uint8_t v___x_675_; 
v_val_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_val_669_);
lean_dec_ref_known(v___x_668_, 1);
lean_inc_ref(v_fileMap_664_);
v_startPos_670_ = l_Lean_FileMap_toPosition(v_fileMap_664_, v_val_667_);
lean_dec(v_val_667_);
v_line_671_ = lean_ctor_get(v_startPos_670_, 0);
lean_inc(v_line_671_);
v_column_672_ = lean_ctor_get(v_startPos_670_, 1);
lean_inc(v_column_672_);
lean_dec_ref(v_startPos_670_);
v_endPos_673_ = l_Lean_FileMap_toPosition(v_fileMap_664_, v_val_669_);
lean_dec(v_val_669_);
v_line_674_ = lean_ctor_get(v_endPos_673_, 0);
lean_inc(v_line_674_);
lean_dec_ref(v_endPos_673_);
v___x_675_ = lean_nat_dec_eq(v_line_671_, v_line_674_);
lean_dec(v_line_674_);
lean_dec(v_line_671_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_676_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__0));
v___x_677_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed__const__1;
v___x_678_ = l_List_replicateTR___redArg(v_column_672_, v___x_677_);
v___x_679_ = lean_string_mk(v___x_678_);
v___x_680_ = lean_string_append(v___x_676_, v___x_679_);
lean_dec_ref(v___x_679_);
return v___x_680_;
}
else
{
lean_object* v___x_681_; 
lean_dec(v_column_672_);
v___x_681_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__1));
return v___x_681_;
}
}
else
{
lean_object* v___x_682_; 
lean_dec(v___x_668_);
lean_dec(v_val_667_);
lean_dec_ref(v_fileMap_664_);
v___x_682_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__2));
return v___x_682_;
}
}
else
{
lean_object* v___x_683_; 
lean_dec(v___x_666_);
lean_dec_ref(v_fileMap_664_);
v___x_683_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__2));
return v___x_683_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed(lean_object* v_tacticSeq_684_, lean_object* v_fileMap_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(v_tacticSeq_684_, v_fileMap_685_);
lean_dec(v_tacticSeq_684_);
return v_res_686_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_689_ = lean_string_utf8_byte_size(v___x_688_);
return v___x_689_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_690_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1);
v___x_691_ = lean_unsigned_to_nat(0u);
v___x_692_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_693_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
lean_ctor_set(v___x_693_, 1, v___x_691_);
lean_ctor_set(v___x_693_, 2, v___x_690_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx(lean_object* v_p_694_){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_695_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_696_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2);
lean_inc(v_p_694_);
v___x_697_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
lean_ctor_set(v___x_697_, 1, v_p_694_);
lean_ctor_set(v___x_697_, 2, v___x_696_);
lean_ctor_set(v___x_697_, 3, v_p_694_);
v___x_698_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set(v___x_698_, 1, v___x_695_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(lean_object* v_range_699_){
_start:
{
lean_object* v_start_700_; lean_object* v_stop_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_711_; 
v_start_700_ = lean_ctor_get(v_range_699_, 0);
v_stop_701_ = lean_ctor_get(v_range_699_, 1);
v_isSharedCheck_711_ = !lean_is_exclusive(v_range_699_);
if (v_isSharedCheck_711_ == 0)
{
v___x_703_ = v_range_699_;
v_isShared_704_ = v_isSharedCheck_711_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_stop_701_);
lean_inc(v_start_700_);
lean_dec(v_range_699_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_711_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_705_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_706_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2);
v___x_707_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
lean_ctor_set(v___x_707_, 1, v_start_700_);
lean_ctor_set(v___x_707_, 2, v___x_706_);
lean_ctor_set(v___x_707_, 3, v_stop_701_);
if (v_isShared_704_ == 0)
{
lean_ctor_set_tag(v___x_703_, 2);
lean_ctor_set(v___x_703_, 1, v___x_705_);
lean_ctor_set(v___x_703_, 0, v___x_707_);
v___x_709_ = v___x_703_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___x_705_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(lean_object* v_mc_x3f_712_, lean_object* v_nc_x3f_713_, lean_object* v_msg_714_, lean_object* v_acc_715_){
_start:
{
switch(lean_obj_tag(v_msg_714_))
{
case 3:
{
lean_object* v_a_716_; lean_object* v_a_717_; lean_object* v___x_718_; 
lean_dec(v_mc_x3f_712_);
v_a_716_ = lean_ctor_get(v_msg_714_, 0);
v_a_717_ = lean_ctor_get(v_msg_714_, 1);
lean_inc_ref(v_a_716_);
v___x_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_718_, 0, v_a_716_);
v_mc_x3f_712_ = v___x_718_;
v_msg_714_ = v_a_717_;
goto _start;
}
case 4:
{
lean_object* v_a_720_; lean_object* v_a_721_; lean_object* v___x_722_; 
lean_dec(v_nc_x3f_713_);
v_a_720_ = lean_ctor_get(v_msg_714_, 0);
v_a_721_ = lean_ctor_get(v_msg_714_, 1);
lean_inc_ref(v_a_720_);
v___x_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_722_, 0, v_a_720_);
v_nc_x3f_713_ = v___x_722_;
v_msg_714_ = v_a_721_;
goto _start;
}
case 5:
{
lean_object* v_a_724_; 
v_a_724_ = lean_ctor_get(v_msg_714_, 1);
v_msg_714_ = v_a_724_;
goto _start;
}
case 6:
{
lean_object* v_a_726_; 
v_a_726_ = lean_ctor_get(v_msg_714_, 0);
v_msg_714_ = v_a_726_;
goto _start;
}
case 8:
{
lean_object* v_a_728_; 
v_a_728_ = lean_ctor_get(v_msg_714_, 1);
v_msg_714_ = v_a_728_;
goto _start;
}
case 7:
{
lean_object* v_a_730_; lean_object* v_a_731_; lean_object* v___x_732_; 
v_a_730_ = lean_ctor_get(v_msg_714_, 0);
v_a_731_ = lean_ctor_get(v_msg_714_, 1);
lean_inc(v_nc_x3f_713_);
lean_inc(v_mc_x3f_712_);
v___x_732_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_712_, v_nc_x3f_713_, v_a_730_, v_acc_715_);
v_msg_714_ = v_a_731_;
v_acc_715_ = v___x_732_;
goto _start;
}
case 2:
{
lean_object* v_a_734_; 
v_a_734_ = lean_ctor_get(v_msg_714_, 1);
v_msg_714_ = v_a_734_;
goto _start;
}
case 9:
{
lean_object* v_msg_736_; lean_object* v_children_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v_msg_736_ = lean_ctor_get(v_msg_714_, 1);
v_children_737_ = lean_ctor_get(v_msg_714_, 2);
lean_inc(v_nc_x3f_713_);
lean_inc(v_mc_x3f_712_);
v___x_738_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_712_, v_nc_x3f_713_, v_msg_736_, v_acc_715_);
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = lean_array_get_size(v_children_737_);
v___x_741_ = lean_nat_dec_lt(v___x_739_, v___x_740_);
if (v___x_741_ == 0)
{
lean_dec(v_nc_x3f_713_);
lean_dec(v_mc_x3f_712_);
return v___x_738_;
}
else
{
uint8_t v___x_742_; 
v___x_742_ = lean_nat_dec_le(v___x_740_, v___x_740_);
if (v___x_742_ == 0)
{
if (v___x_741_ == 0)
{
lean_dec(v_nc_x3f_713_);
lean_dec(v_mc_x3f_712_);
return v___x_738_;
}
else
{
size_t v___x_743_; size_t v___x_744_; lean_object* v___x_745_; 
v___x_743_ = ((size_t)0ULL);
v___x_744_ = lean_usize_of_nat(v___x_740_);
v___x_745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_712_, v_nc_x3f_713_, v_children_737_, v___x_743_, v___x_744_, v___x_738_);
return v___x_745_;
}
}
else
{
size_t v___x_746_; size_t v___x_747_; lean_object* v___x_748_; 
v___x_746_ = ((size_t)0ULL);
v___x_747_ = lean_usize_of_nat(v___x_740_);
v___x_748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_712_, v_nc_x3f_713_, v_children_737_, v___x_746_, v___x_747_, v___x_738_);
return v___x_748_;
}
}
}
case 1:
{
if (lean_obj_tag(v_mc_x3f_712_) == 1)
{
if (lean_obj_tag(v_nc_x3f_713_) == 1)
{
lean_object* v_a_749_; lean_object* v_val_750_; lean_object* v_val_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v_a_749_ = lean_ctor_get(v_msg_714_, 0);
v_val_750_ = lean_ctor_get(v_mc_x3f_712_, 0);
lean_inc(v_val_750_);
lean_dec_ref_known(v_mc_x3f_712_, 1);
v_val_751_ = lean_ctor_get(v_nc_x3f_713_, 0);
lean_inc(v_val_751_);
lean_dec_ref_known(v_nc_x3f_713_, 1);
lean_inc(v_a_749_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v_val_751_);
lean_ctor_set(v___x_752_, 1, v_a_749_);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v_val_750_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = lean_array_push(v_acc_715_, v___x_753_);
return v___x_754_;
}
else
{
lean_dec_ref_known(v_mc_x3f_712_, 1);
lean_dec(v_nc_x3f_713_);
return v_acc_715_;
}
}
else
{
lean_dec(v_nc_x3f_713_);
lean_dec(v_mc_x3f_712_);
return v_acc_715_;
}
}
default: 
{
lean_dec(v_nc_x3f_713_);
lean_dec(v_mc_x3f_712_);
return v_acc_715_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(lean_object* v_mc_x3f_755_, lean_object* v_nc_x3f_756_, lean_object* v_as_757_, size_t v_i_758_, size_t v_stop_759_, lean_object* v_b_760_){
_start:
{
uint8_t v___x_761_; 
v___x_761_ = lean_usize_dec_eq(v_i_758_, v_stop_759_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; lean_object* v___x_763_; size_t v___x_764_; size_t v___x_765_; 
v___x_762_ = lean_array_uget_borrowed(v_as_757_, v_i_758_);
lean_inc(v_nc_x3f_756_);
lean_inc(v_mc_x3f_755_);
v___x_763_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_755_, v_nc_x3f_756_, v___x_762_, v_b_760_);
v___x_764_ = ((size_t)1ULL);
v___x_765_ = lean_usize_add(v_i_758_, v___x_764_);
v_i_758_ = v___x_765_;
v_b_760_ = v___x_763_;
goto _start;
}
else
{
lean_dec(v_nc_x3f_756_);
lean_dec(v_mc_x3f_755_);
return v_b_760_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0___boxed(lean_object* v_mc_x3f_767_, lean_object* v_nc_x3f_768_, lean_object* v_as_769_, lean_object* v_i_770_, lean_object* v_stop_771_, lean_object* v_b_772_){
_start:
{
size_t v_i_boxed_773_; size_t v_stop_boxed_774_; lean_object* v_res_775_; 
v_i_boxed_773_ = lean_unbox_usize(v_i_770_);
lean_dec(v_i_770_);
v_stop_boxed_774_ = lean_unbox_usize(v_stop_771_);
lean_dec(v_stop_771_);
v_res_775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_767_, v_nc_x3f_768_, v_as_769_, v_i_boxed_773_, v_stop_boxed_774_, v_b_772_);
lean_dec_ref(v_as_769_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go___boxed(lean_object* v_mc_x3f_776_, lean_object* v_nc_x3f_777_, lean_object* v_msg_778_, lean_object* v_acc_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_776_, v_nc_x3f_777_, v_msg_778_, v_acc_779_);
lean_dec_ref(v_msg_778_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(lean_object* v_msg_783_){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_784_ = lean_box(0);
v___x_785_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___closed__0));
v___x_786_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v___x_784_, v___x_784_, v_msg_783_, v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___boxed(lean_object* v_msg_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_msg_787_);
lean_dec_ref(v_msg_787_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f(lean_object* v_range_791_, lean_object* v_stx_792_){
_start:
{
lean_object* v___x_793_; 
lean_inc(v_stx_792_);
v___x_793_ = l_Lean_Syntax_getKind(v_stx_792_);
if (lean_obj_tag(v___x_793_) == 1)
{
lean_object* v_pre_794_; 
v_pre_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_pre_794_);
if (lean_obj_tag(v_pre_794_) == 1)
{
lean_object* v_pre_795_; 
v_pre_795_ = lean_ctor_get(v_pre_794_, 0);
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
if (lean_obj_tag(v_pre_797_) == 0)
{
lean_object* v_str_798_; lean_object* v_str_799_; lean_object* v_str_800_; lean_object* v_str_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v_str_798_ = lean_ctor_get(v___x_793_, 1);
lean_inc_ref(v_str_798_);
lean_dec_ref_known(v___x_793_, 2);
v_str_799_ = lean_ctor_get(v_pre_794_, 1);
lean_inc_ref(v_str_799_);
lean_dec_ref_known(v_pre_794_, 2);
v_str_800_ = lean_ctor_get(v_pre_795_, 1);
lean_inc_ref(v_str_800_);
lean_dec_ref_known(v_pre_795_, 2);
v_str_801_ = lean_ctor_get(v_pre_796_, 1);
lean_inc_ref(v_str_801_);
lean_dec_ref_known(v_pre_796_, 2);
v___x_802_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_803_ = lean_string_dec_eq(v_str_801_, v___x_802_);
lean_dec_ref(v_str_801_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; 
lean_dec_ref(v_str_800_);
lean_dec_ref(v_str_799_);
lean_dec_ref(v_str_798_);
lean_dec(v_stx_792_);
lean_dec_ref(v_range_791_);
v___x_804_ = lean_box(0);
return v___x_804_;
}
else
{
lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_805_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0));
v___x_806_ = lean_string_dec_eq(v_str_800_, v___x_805_);
lean_dec_ref(v_str_800_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; 
lean_dec_ref(v_str_799_);
lean_dec_ref(v_str_798_);
lean_dec(v_stx_792_);
lean_dec_ref(v_range_791_);
v___x_807_ = lean_box(0);
return v___x_807_;
}
else
{
lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_808_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_809_ = lean_string_dec_eq(v_str_799_, v___x_808_);
lean_dec_ref(v_str_799_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; 
lean_dec_ref(v_str_798_);
lean_dec(v_stx_792_);
lean_dec_ref(v_range_791_);
v___x_810_ = lean_box(0);
return v___x_810_;
}
else
{
lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_811_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__0));
v___x_812_ = lean_string_dec_eq(v_str_798_, v___x_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_813_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__1));
v___x_814_ = lean_string_dec_eq(v_str_798_, v___x_813_);
lean_dec_ref(v_str_798_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; 
lean_dec(v_stx_792_);
lean_dec_ref(v_range_791_);
v___x_815_ = lean_box(0);
return v___x_815_;
}
else
{
lean_object* v___x_816_; lean_object* v_body_817_; lean_object* v___y_819_; lean_object* v___x_822_; 
v___x_816_ = lean_unsigned_to_nat(1u);
v_body_817_ = l_Lean_Syntax_getArg(v_stx_792_, v___x_816_);
v___x_822_ = l_Lean_Syntax_getTailPos_x3f(v_body_817_, v___x_812_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_823_ = lean_unsigned_to_nat(2u);
v___x_824_ = l_Lean_Syntax_getArg(v_stx_792_, v___x_823_);
lean_dec(v_stx_792_);
v___x_825_ = l_Lean_Syntax_getPos_x3f(v___x_824_, v___x_812_);
lean_dec(v___x_824_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_stop_826_; 
v_stop_826_ = lean_ctor_get(v_range_791_, 1);
lean_inc(v_stop_826_);
lean_dec_ref(v_range_791_);
v___y_819_ = v_stop_826_;
goto v___jp_818_;
}
else
{
lean_object* v_val_827_; 
lean_dec_ref(v_range_791_);
v_val_827_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_val_827_);
lean_dec_ref_known(v___x_825_, 1);
v___y_819_ = v_val_827_;
goto v___jp_818_;
}
}
else
{
lean_object* v_val_828_; 
lean_dec(v_stx_792_);
lean_dec_ref(v_range_791_);
v_val_828_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_val_828_);
lean_dec_ref_known(v___x_822_, 1);
v___y_819_ = v_val_828_;
goto v___jp_818_;
}
v___jp_818_:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v_body_817_);
lean_ctor_set(v___x_820_, 1, v___y_819_);
v___x_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
return v___x_821_;
}
}
}
else
{
lean_object* v___x_829_; lean_object* v_body_830_; lean_object* v___y_832_; uint8_t v___x_835_; lean_object* v___x_836_; 
lean_dec_ref(v_str_798_);
v___x_829_ = lean_unsigned_to_nat(0u);
v_body_830_ = l_Lean_Syntax_getArg(v_stx_792_, v___x_829_);
lean_dec(v_stx_792_);
v___x_835_ = 0;
v___x_836_ = l_Lean_Syntax_getTailPos_x3f(v_body_830_, v___x_835_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_stop_837_; 
v_stop_837_ = lean_ctor_get(v_range_791_, 1);
lean_inc(v_stop_837_);
lean_dec_ref(v_range_791_);
v___y_832_ = v_stop_837_;
goto v___jp_831_;
}
else
{
lean_object* v_val_838_; 
lean_dec_ref(v_range_791_);
v_val_838_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_val_838_);
lean_dec_ref_known(v___x_836_, 1);
v___y_832_ = v_val_838_;
goto v___jp_831_;
}
v___jp_831_:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_833_, 0, v_body_830_);
lean_ctor_set(v___x_833_, 1, v___y_832_);
v___x_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
return v___x_834_;
}
}
}
}
}
}
else
{
lean_object* v___x_839_; 
lean_dec_ref_known(v_pre_796_, 2);
lean_dec_ref_known(v_pre_795_, 2);
lean_dec_ref_known(v_pre_794_, 2);
lean_dec_ref_known(v___x_793_, 2);
lean_dec(v_stx_792_);
lean_dec_ref(v_range_791_);
v___x_839_ = lean_box(0);
return v___x_839_;
}
}
else
{
lean_object* v___x_840_; 
lean_dec_ref_known(v_pre_795_, 2);
lean_dec(v_pre_796_);
lean_dec_ref_known(v_pre_794_, 2);
lean_dec_ref_known(v___x_793_, 2);
lean_dec(v_stx_792_);
lean_dec_ref(v_range_791_);
v___x_840_ = lean_box(0);
return v___x_840_;
}
}
else
{
lean_object* v___x_841_; 
lean_dec(v_pre_795_);
lean_dec_ref_known(v_pre_794_, 2);
lean_dec_ref_known(v___x_793_, 2);
lean_dec(v_stx_792_);
lean_dec_ref(v_range_791_);
v___x_841_ = lean_box(0);
return v___x_841_;
}
}
else
{
lean_object* v___x_842_; 
lean_dec(v_pre_794_);
lean_dec_ref_known(v___x_793_, 2);
lean_dec(v_stx_792_);
lean_dec_ref(v_range_791_);
v___x_842_ = lean_box(0);
return v___x_842_;
}
}
else
{
lean_object* v___x_843_; 
lean_dec(v___x_793_);
lean_dec(v_stx_792_);
lean_dec_ref(v_range_791_);
v___x_843_ = lean_box(0);
return v___x_843_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(lean_object* v_range_847_, lean_object* v_stx_848_){
_start:
{
lean_object* v___x_849_; 
lean_inc(v_stx_848_);
lean_inc_ref(v_range_847_);
v___x_849_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f(v_range_847_, v_stx_848_);
if (lean_obj_tag(v___x_849_) == 1)
{
lean_dec(v_stx_848_);
lean_dec_ref(v_range_847_);
return v___x_849_;
}
else
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; size_t v_sz_853_; size_t v___x_854_; lean_object* v___x_855_; lean_object* v_fst_856_; 
lean_dec(v___x_849_);
v___x_850_ = l_Lean_Syntax_getArgs(v_stx_848_);
lean_dec(v_stx_848_);
v___x_851_ = lean_box(0);
v___x_852_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v_sz_853_ = lean_array_size(v___x_850_);
v___x_854_ = ((size_t)0ULL);
v___x_855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(v_range_847_, v___x_850_, v_sz_853_, v___x_854_, v___x_852_);
lean_dec_ref(v___x_850_);
v_fst_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_fst_856_);
lean_dec_ref(v___x_855_);
if (lean_obj_tag(v_fst_856_) == 0)
{
return v___x_851_;
}
else
{
lean_object* v_val_857_; 
v_val_857_ = lean_ctor_get(v_fst_856_, 0);
lean_inc(v_val_857_);
lean_dec_ref_known(v_fst_856_, 1);
return v_val_857_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(lean_object* v_range_858_, lean_object* v_as_859_, size_t v_sz_860_, size_t v_i_861_, lean_object* v_b_862_){
_start:
{
uint8_t v___x_863_; 
v___x_863_ = lean_usize_dec_lt(v_i_861_, v_sz_860_);
if (v___x_863_ == 0)
{
lean_dec_ref(v_range_858_);
lean_inc_ref(v_b_862_);
return v_b_862_;
}
else
{
lean_object* v___x_864_; lean_object* v_a_865_; lean_object* v___x_866_; 
v___x_864_ = lean_box(0);
v_a_865_ = lean_array_uget_borrowed(v_as_859_, v_i_861_);
lean_inc(v_a_865_);
lean_inc_ref(v_range_858_);
v___x_866_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(v_range_858_, v_a_865_);
if (lean_obj_tag(v___x_866_) == 1)
{
lean_object* v___x_867_; lean_object* v___x_868_; 
lean_dec_ref(v_range_858_);
v___x_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
v___x_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
lean_ctor_set(v___x_868_, 1, v___x_864_);
return v___x_868_;
}
else
{
lean_object* v___x_869_; size_t v___x_870_; size_t v___x_871_; 
lean_dec(v___x_866_);
v___x_869_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v___x_870_ = ((size_t)1ULL);
v___x_871_ = lean_usize_add(v_i_861_, v___x_870_);
v_i_861_ = v___x_871_;
v_b_862_ = v___x_869_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___boxed(lean_object* v_range_873_, lean_object* v_as_874_, lean_object* v_sz_875_, lean_object* v_i_876_, lean_object* v_b_877_){
_start:
{
size_t v_sz_boxed_878_; size_t v_i_boxed_879_; lean_object* v_res_880_; 
v_sz_boxed_878_ = lean_unbox_usize(v_sz_875_);
lean_dec(v_sz_875_);
v_i_boxed_879_ = lean_unbox_usize(v_i_876_);
lean_dec(v_i_876_);
v_res_880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(v_range_873_, v_as_874_, v_sz_boxed_878_, v_i_boxed_879_, v_b_877_);
lean_dec_ref(v_b_877_);
lean_dec_ref(v_as_874_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(lean_object* v_range_881_, lean_object* v_stx_882_){
_start:
{
uint8_t v___x_883_; lean_object* v___x_884_; 
v___x_883_ = 0;
v___x_884_ = l_Lean_Syntax_getRange_x3f(v_stx_882_, v___x_883_);
if (lean_obj_tag(v___x_884_) == 1)
{
lean_object* v_val_885_; uint8_t v___x_886_; 
v_val_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_val_885_);
lean_dec_ref_known(v___x_884_, 1);
v___x_886_ = l_Lean_Syntax_Range_includes(v_val_885_, v_range_881_, v___x_883_, v___x_883_);
lean_dec(v_val_885_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; 
lean_dec(v_stx_882_);
lean_dec_ref(v_range_881_);
v___x_887_ = lean_box(0);
return v___x_887_;
}
else
{
lean_object* v___x_888_; lean_object* v___x_889_; size_t v_sz_890_; size_t v___x_891_; lean_object* v___x_892_; lean_object* v_fst_893_; 
v___x_888_ = l_Lean_Syntax_getArgs(v_stx_882_);
v___x_889_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v_sz_890_ = lean_array_size(v___x_888_);
v___x_891_ = ((size_t)0ULL);
lean_inc_ref(v_range_881_);
v___x_892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(v_range_881_, v___x_888_, v_sz_890_, v___x_891_, v___x_889_);
lean_dec_ref(v___x_888_);
v_fst_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_fst_893_);
lean_dec_ref(v___x_892_);
if (lean_obj_tag(v_fst_893_) == 0)
{
lean_object* v___x_894_; 
v___x_894_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(v_range_881_, v_stx_882_);
return v___x_894_;
}
else
{
lean_object* v_val_895_; 
lean_dec(v_stx_882_);
lean_dec_ref(v_range_881_);
v_val_895_ = lean_ctor_get(v_fst_893_, 0);
lean_inc(v_val_895_);
lean_dec_ref_known(v_fst_893_, 1);
return v_val_895_;
}
}
}
else
{
lean_object* v___x_896_; 
lean_dec(v___x_884_);
lean_dec(v_stx_882_);
lean_dec_ref(v_range_881_);
v___x_896_ = lean_box(0);
return v___x_896_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(lean_object* v_range_897_, lean_object* v_as_898_, size_t v_sz_899_, size_t v_i_900_, lean_object* v_b_901_){
_start:
{
uint8_t v___x_902_; 
v___x_902_ = lean_usize_dec_lt(v_i_900_, v_sz_899_);
if (v___x_902_ == 0)
{
lean_dec_ref(v_range_897_);
lean_inc_ref(v_b_901_);
return v_b_901_;
}
else
{
lean_object* v___x_903_; lean_object* v_a_904_; lean_object* v___x_905_; 
v___x_903_ = lean_box(0);
v_a_904_ = lean_array_uget_borrowed(v_as_898_, v_i_900_);
lean_inc(v_a_904_);
lean_inc_ref(v_range_897_);
v___x_905_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v_range_897_, v_a_904_);
if (lean_obj_tag(v___x_905_) == 1)
{
lean_object* v___x_906_; lean_object* v___x_907_; 
lean_dec_ref(v_range_897_);
v___x_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
v___x_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
lean_ctor_set(v___x_907_, 1, v___x_903_);
return v___x_907_;
}
else
{
lean_object* v___x_908_; size_t v___x_909_; size_t v___x_910_; 
lean_dec(v___x_905_);
v___x_908_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v___x_909_ = ((size_t)1ULL);
v___x_910_ = lean_usize_add(v_i_900_, v___x_909_);
v_i_900_ = v___x_910_;
v_b_901_ = v___x_908_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0___boxed(lean_object* v_range_912_, lean_object* v_as_913_, lean_object* v_sz_914_, lean_object* v_i_915_, lean_object* v_b_916_){
_start:
{
size_t v_sz_boxed_917_; size_t v_i_boxed_918_; lean_object* v_res_919_; 
v_sz_boxed_917_ = lean_unbox_usize(v_sz_914_);
lean_dec(v_sz_914_);
v_i_boxed_918_ = lean_unbox_usize(v_i_915_);
lean_dec(v_i_915_);
v_res_919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(v_range_912_, v_as_913_, v_sz_boxed_917_, v_i_boxed_918_, v_b_916_);
lean_dec_ref(v_b_916_);
lean_dec_ref(v_as_913_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody(lean_object* v_cmd_920_, lean_object* v_range_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v_range_921_, v_cmd_920_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0(lean_object* v_ctx_923_, lean_object* v_info_924_, lean_object* v_acc_925_){
_start:
{
if (lean_obj_tag(v_info_924_) == 0)
{
lean_object* v_i_926_; lean_object* v_toElabInfo_927_; lean_object* v_mctxBefore_928_; lean_object* v_goalsBefore_929_; lean_object* v_stx_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_948_; 
v_i_926_ = lean_ctor_get(v_info_924_, 0);
lean_inc_ref(v_i_926_);
lean_dec_ref_known(v_info_924_, 1);
v_toElabInfo_927_ = lean_ctor_get(v_i_926_, 0);
lean_inc_ref(v_toElabInfo_927_);
v_mctxBefore_928_ = lean_ctor_get(v_i_926_, 1);
lean_inc_ref(v_mctxBefore_928_);
v_goalsBefore_929_ = lean_ctor_get(v_i_926_, 2);
lean_inc(v_goalsBefore_929_);
lean_dec_ref(v_i_926_);
v_stx_930_ = lean_ctor_get(v_toElabInfo_927_, 1);
v_isSharedCheck_948_ = !lean_is_exclusive(v_toElabInfo_927_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; 
v_unused_949_ = lean_ctor_get(v_toElabInfo_927_, 0);
lean_dec(v_unused_949_);
v___x_932_ = v_toElabInfo_927_;
v_isShared_933_ = v_isSharedCheck_948_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_stx_930_);
lean_dec(v_toElabInfo_927_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_948_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
uint8_t v___x_934_; 
lean_inc(v_stx_930_);
v___x_934_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(v_stx_930_);
if (v___x_934_ == 0)
{
lean_del_object(v___x_932_);
lean_dec(v_stx_930_);
lean_dec(v_goalsBefore_929_);
lean_dec_ref(v_mctxBefore_928_);
return v_acc_925_;
}
else
{
lean_object* v___x_935_; 
v___x_935_ = l_List_head_x3f___redArg(v_goalsBefore_929_);
lean_dec(v_goalsBefore_929_);
if (lean_obj_tag(v___x_935_) == 1)
{
lean_object* v_toCommandContextInfo_936_; lean_object* v_val_937_; lean_object* v_env_938_; lean_object* v_options_939_; lean_object* v_currNamespace_940_; lean_object* v_openDecls_941_; lean_object* v_namingCtx_943_; 
v_toCommandContextInfo_936_ = lean_ctor_get(v_ctx_923_, 0);
v_val_937_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_val_937_);
lean_dec_ref_known(v___x_935_, 1);
v_env_938_ = lean_ctor_get(v_toCommandContextInfo_936_, 0);
v_options_939_ = lean_ctor_get(v_toCommandContextInfo_936_, 4);
v_currNamespace_940_ = lean_ctor_get(v_toCommandContextInfo_936_, 5);
v_openDecls_941_ = lean_ctor_get(v_toCommandContextInfo_936_, 6);
lean_inc(v_openDecls_941_);
lean_inc(v_currNamespace_940_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 1, v_openDecls_941_);
lean_ctor_set(v___x_932_, 0, v_currNamespace_940_);
v_namingCtx_943_ = v___x_932_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_currNamespace_940_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_openDecls_941_);
v_namingCtx_943_ = v_reuseFailAlloc_947_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_944_ = lean_box(1);
lean_inc_ref(v_options_939_);
lean_inc_ref(v_env_938_);
v___x_945_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v_stx_930_);
lean_ctor_set(v___x_945_, 2, v_env_938_);
lean_ctor_set(v___x_945_, 3, v_mctxBefore_928_);
lean_ctor_set(v___x_945_, 4, v_options_939_);
lean_ctor_set(v___x_945_, 5, v_namingCtx_943_);
lean_ctor_set(v___x_945_, 6, v_val_937_);
v___x_946_ = lean_array_push(v_acc_925_, v___x_945_);
return v___x_946_;
}
}
else
{
lean_dec(v___x_935_);
lean_del_object(v___x_932_);
lean_dec(v_stx_930_);
lean_dec_ref(v_mctxBefore_928_);
return v_acc_925_;
}
}
}
}
else
{
lean_dec_ref(v_info_924_);
return v_acc_925_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0___boxed(lean_object* v_ctx_950_, lean_object* v_info_951_, lean_object* v_acc_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0(v_ctx_950_, v_info_951_, v_acc_952_);
lean_dec_ref(v_ctx_950_);
return v_res_953_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_954_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__0);
v___x_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
return v___x_956_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_957_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1);
v___x_958_ = lean_unsigned_to_nat(0u);
v___x_959_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
lean_ctor_set(v___x_959_, 2, v___x_958_);
lean_ctor_set(v___x_959_, 3, v___x_958_);
lean_ctor_set(v___x_959_, 4, v___x_957_);
lean_ctor_set(v___x_959_, 5, v___x_957_);
lean_ctor_set(v___x_959_, 6, v___x_957_);
lean_ctor_set(v___x_959_, 7, v___x_957_);
lean_ctor_set(v___x_959_, 8, v___x_957_);
lean_ctor_set(v___x_959_, 9, v___x_957_);
return v___x_959_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_960_ = lean_unsigned_to_nat(32u);
v___x_961_ = lean_mk_empty_array_with_capacity(v___x_960_);
v___x_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
return v___x_962_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_963_ = ((size_t)5ULL);
v___x_964_ = lean_unsigned_to_nat(0u);
v___x_965_ = lean_unsigned_to_nat(32u);
v___x_966_ = lean_mk_empty_array_with_capacity(v___x_965_);
v___x_967_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__3);
v___x_968_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v___x_966_);
lean_ctor_set(v___x_968_, 2, v___x_964_);
lean_ctor_set(v___x_968_, 3, v___x_964_);
lean_ctor_set_usize(v___x_968_, 4, v___x_963_);
return v___x_968_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_969_ = lean_box(1);
v___x_970_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__4);
v___x_971_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1);
v___x_972_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
lean_ctor_set(v___x_972_, 1, v___x_970_);
lean_ctor_set(v___x_972_, 2, v___x_969_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(lean_object* v_msgData_973_, lean_object* v___y_974_){
_start:
{
lean_object* v___x_976_; lean_object* v_env_977_; lean_object* v___x_978_; lean_object* v_scopes_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v_opts_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_976_ = lean_st_ref_get(v___y_974_);
v_env_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc_ref(v_env_977_);
lean_dec(v___x_976_);
v___x_978_ = lean_st_ref_get(v___y_974_);
v_scopes_979_ = lean_ctor_get(v___x_978_, 2);
lean_inc(v_scopes_979_);
lean_dec(v___x_978_);
v___x_980_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_981_ = l_List_head_x21___redArg(v___x_980_, v_scopes_979_);
lean_dec(v_scopes_979_);
v_opts_982_ = lean_ctor_get(v___x_981_, 1);
lean_inc_ref(v_opts_982_);
lean_dec(v___x_981_);
v___x_983_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__2);
v___x_984_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__5);
v___x_985_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_985_, 0, v_env_977_);
lean_ctor_set(v___x_985_, 1, v___x_983_);
lean_ctor_set(v___x_985_, 2, v___x_984_);
lean_ctor_set(v___x_985_, 3, v_opts_982_);
v___x_986_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
lean_ctor_set(v___x_986_, 1, v_msgData_973_);
v___x_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___boxed(lean_object* v_msgData_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(v_msgData_988_, v___y_989_);
lean_dec(v___y_989_);
return v_res_991_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0(void){
_start:
{
lean_object* v___x_992_; double v___x_993_; 
v___x_992_ = lean_unsigned_to_nat(0u);
v___x_993_ = lean_float_of_nat(v___x_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(lean_object* v_cls_996_, lean_object* v_msg_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Lean_Elab_Command_getRef___redArg(v___y_998_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1003_; lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1051_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_1001_, 1);
v___x_1003_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(v_msg_997_, v___y_999_);
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1006_ = v___x_1003_;
v_isShared_1007_ = v_isSharedCheck_1051_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1051_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1008_; lean_object* v_traceState_1009_; lean_object* v_env_1010_; lean_object* v_messages_1011_; lean_object* v_scopes_1012_; lean_object* v_usedQuotCtxts_1013_; lean_object* v_nextMacroScope_1014_; lean_object* v_maxRecDepth_1015_; lean_object* v_ngen_1016_; lean_object* v_auxDeclNGen_1017_; lean_object* v_infoState_1018_; lean_object* v_snapshotTasks_1019_; lean_object* v_prevLinterStates_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1050_; 
v___x_1008_ = lean_st_ref_take(v___y_999_);
v_traceState_1009_ = lean_ctor_get(v___x_1008_, 9);
v_env_1010_ = lean_ctor_get(v___x_1008_, 0);
v_messages_1011_ = lean_ctor_get(v___x_1008_, 1);
v_scopes_1012_ = lean_ctor_get(v___x_1008_, 2);
v_usedQuotCtxts_1013_ = lean_ctor_get(v___x_1008_, 3);
v_nextMacroScope_1014_ = lean_ctor_get(v___x_1008_, 4);
v_maxRecDepth_1015_ = lean_ctor_get(v___x_1008_, 5);
v_ngen_1016_ = lean_ctor_get(v___x_1008_, 6);
v_auxDeclNGen_1017_ = lean_ctor_get(v___x_1008_, 7);
v_infoState_1018_ = lean_ctor_get(v___x_1008_, 8);
v_snapshotTasks_1019_ = lean_ctor_get(v___x_1008_, 10);
v_prevLinterStates_1020_ = lean_ctor_get(v___x_1008_, 11);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1022_ = v___x_1008_;
v_isShared_1023_ = v_isSharedCheck_1050_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_prevLinterStates_1020_);
lean_inc(v_snapshotTasks_1019_);
lean_inc(v_traceState_1009_);
lean_inc(v_infoState_1018_);
lean_inc(v_auxDeclNGen_1017_);
lean_inc(v_ngen_1016_);
lean_inc(v_maxRecDepth_1015_);
lean_inc(v_nextMacroScope_1014_);
lean_inc(v_usedQuotCtxts_1013_);
lean_inc(v_scopes_1012_);
lean_inc(v_messages_1011_);
lean_inc(v_env_1010_);
lean_dec(v___x_1008_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1050_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
uint64_t v_tid_1024_; lean_object* v_traces_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1049_; 
v_tid_1024_ = lean_ctor_get_uint64(v_traceState_1009_, sizeof(void*)*1);
v_traces_1025_ = lean_ctor_get(v_traceState_1009_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_traceState_1009_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1027_ = v_traceState_1009_;
v_isShared_1028_ = v_isSharedCheck_1049_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_traces_1025_);
lean_dec(v_traceState_1009_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1049_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1029_; double v___x_1030_; uint8_t v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1029_ = lean_box(0);
v___x_1030_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0);
v___x_1031_ = 0;
v___x_1032_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_1033_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1033_, 0, v_cls_996_);
lean_ctor_set(v___x_1033_, 1, v___x_1029_);
lean_ctor_set(v___x_1033_, 2, v___x_1032_);
lean_ctor_set_float(v___x_1033_, sizeof(void*)*3, v___x_1030_);
lean_ctor_set_float(v___x_1033_, sizeof(void*)*3 + 8, v___x_1030_);
lean_ctor_set_uint8(v___x_1033_, sizeof(void*)*3 + 16, v___x_1031_);
v___x_1034_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__1));
v___x_1035_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set(v___x_1035_, 1, v_a_1004_);
lean_ctor_set(v___x_1035_, 2, v___x_1034_);
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v_a_1002_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = l_Lean_PersistentArray_push___redArg(v_traces_1025_, v___x_1036_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1037_);
v___x_1039_ = v___x_1027_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1037_);
lean_ctor_set_uint64(v_reuseFailAlloc_1048_, sizeof(void*)*1, v_tid_1024_);
v___x_1039_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1041_; 
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 9, v___x_1039_);
v___x_1041_ = v___x_1022_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_env_1010_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v_messages_1011_);
lean_ctor_set(v_reuseFailAlloc_1047_, 2, v_scopes_1012_);
lean_ctor_set(v_reuseFailAlloc_1047_, 3, v_usedQuotCtxts_1013_);
lean_ctor_set(v_reuseFailAlloc_1047_, 4, v_nextMacroScope_1014_);
lean_ctor_set(v_reuseFailAlloc_1047_, 5, v_maxRecDepth_1015_);
lean_ctor_set(v_reuseFailAlloc_1047_, 6, v_ngen_1016_);
lean_ctor_set(v_reuseFailAlloc_1047_, 7, v_auxDeclNGen_1017_);
lean_ctor_set(v_reuseFailAlloc_1047_, 8, v_infoState_1018_);
lean_ctor_set(v_reuseFailAlloc_1047_, 9, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1047_, 10, v_snapshotTasks_1019_);
lean_ctor_set(v_reuseFailAlloc_1047_, 11, v_prevLinterStates_1020_);
v___x_1041_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1045_; 
v___x_1042_ = lean_st_ref_set(v___y_999_, v___x_1041_);
v___x_1043_ = lean_box(0);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v___x_1043_);
v___x_1045_ = v___x_1006_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_dec_ref(v_msg_997_);
lean_dec(v_cls_996_);
v_a_1052_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1001_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1001_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___boxed(lean_object* v_cls_1060_, lean_object* v_msg_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v_cls_1060_, v_msg_1061_, v___y_1062_, v___y_1063_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
return v_res_1065_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0(lean_object* v_x_1070_){
_start:
{
lean_object* v___x_1071_; uint8_t v___x_1072_; 
v___x_1071_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0___closed__1));
v___x_1072_ = lean_name_eq(v_x_1070_, v___x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0___boxed(lean_object* v_x_1073_){
_start:
{
uint8_t v_res_1074_; lean_object* v_r_1075_; 
v_res_1074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0(v_x_1073_);
lean_dec(v_x_1073_);
v_r_1075_ = lean_box(v_res_1074_);
return v_r_1075_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(lean_object* v_a_1076_, lean_object* v_x_1077_){
_start:
{
if (lean_obj_tag(v_x_1077_) == 0)
{
uint8_t v___x_1078_; 
v___x_1078_ = 0;
return v___x_1078_;
}
else
{
lean_object* v_key_1079_; lean_object* v_tail_1080_; uint8_t v___y_1082_; lean_object* v_fst_1084_; lean_object* v_snd_1085_; lean_object* v_fst_1086_; lean_object* v_snd_1087_; uint8_t v___x_1088_; 
v_key_1079_ = lean_ctor_get(v_x_1077_, 0);
v_tail_1080_ = lean_ctor_get(v_x_1077_, 2);
v_fst_1084_ = lean_ctor_get(v_key_1079_, 0);
v_snd_1085_ = lean_ctor_get(v_key_1079_, 1);
v_fst_1086_ = lean_ctor_get(v_a_1076_, 0);
v_snd_1087_ = lean_ctor_get(v_a_1076_, 1);
v___x_1088_ = l_Lean_Syntax_instBEqRange_beq(v_fst_1084_, v_fst_1086_);
if (v___x_1088_ == 0)
{
v___y_1082_ = v___x_1088_;
goto v___jp_1081_;
}
else
{
uint8_t v___x_1089_; 
v___x_1089_ = l_Lean_instBEqMVarId_beq(v_snd_1085_, v_snd_1087_);
v___y_1082_ = v___x_1089_;
goto v___jp_1081_;
}
v___jp_1081_:
{
if (v___y_1082_ == 0)
{
v_x_1077_ = v_tail_1080_;
goto _start;
}
else
{
return v___y_1082_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg___boxed(lean_object* v_a_1090_, lean_object* v_x_1091_){
_start:
{
uint8_t v_res_1092_; lean_object* v_r_1093_; 
v_res_1092_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(v_a_1090_, v_x_1091_);
lean_dec(v_x_1091_);
lean_dec_ref(v_a_1090_);
v_r_1093_ = lean_box(v_res_1092_);
return v_r_1093_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(lean_object* v_m_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v_buckets_1096_; lean_object* v_fst_1097_; lean_object* v_snd_1098_; lean_object* v___x_1099_; uint64_t v___x_1100_; uint64_t v___x_1101_; uint64_t v___x_1102_; uint64_t v___x_1103_; uint64_t v___x_1104_; uint64_t v_fold_1105_; uint64_t v___x_1106_; uint64_t v___x_1107_; uint64_t v___x_1108_; size_t v___x_1109_; size_t v___x_1110_; size_t v___x_1111_; size_t v___x_1112_; size_t v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v_buckets_1096_ = lean_ctor_get(v_m_1094_, 1);
v_fst_1097_ = lean_ctor_get(v_a_1095_, 0);
v_snd_1098_ = lean_ctor_get(v_a_1095_, 1);
v___x_1099_ = lean_array_get_size(v_buckets_1096_);
v___x_1100_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1097_);
v___x_1101_ = l_Lean_instHashableMVarId_hash(v_snd_1098_);
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
v___x_1114_ = lean_array_uget_borrowed(v_buckets_1096_, v___x_1113_);
v___x_1115_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(v_a_1095_, v___x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg___boxed(lean_object* v_m_1116_, lean_object* v_a_1117_){
_start:
{
uint8_t v_res_1118_; lean_object* v_r_1119_; 
v_res_1118_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(v_m_1116_, v_a_1117_);
lean_dec_ref(v_a_1117_);
lean_dec_ref(v_m_1116_);
v_r_1119_ = lean_box(v_res_1118_);
return v_r_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3_spec__8___redArg(lean_object* v_x_1120_, lean_object* v_x_1121_){
_start:
{
if (lean_obj_tag(v_x_1121_) == 0)
{
return v_x_1120_;
}
else
{
lean_object* v_key_1122_; lean_object* v_value_1123_; lean_object* v_tail_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1151_; 
v_key_1122_ = lean_ctor_get(v_x_1121_, 0);
v_value_1123_ = lean_ctor_get(v_x_1121_, 1);
v_tail_1124_ = lean_ctor_get(v_x_1121_, 2);
v_isSharedCheck_1151_ = !lean_is_exclusive(v_x_1121_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1126_ = v_x_1121_;
v_isShared_1127_ = v_isSharedCheck_1151_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_tail_1124_);
lean_inc(v_value_1123_);
lean_inc(v_key_1122_);
lean_dec(v_x_1121_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1151_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v_fst_1128_; lean_object* v_snd_1129_; lean_object* v___x_1130_; uint64_t v___x_1131_; uint64_t v___x_1132_; uint64_t v___x_1133_; uint64_t v___x_1134_; uint64_t v___x_1135_; uint64_t v_fold_1136_; uint64_t v___x_1137_; uint64_t v___x_1138_; uint64_t v___x_1139_; size_t v___x_1140_; size_t v___x_1141_; size_t v___x_1142_; size_t v___x_1143_; size_t v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1147_; 
v_fst_1128_ = lean_ctor_get(v_key_1122_, 0);
v_snd_1129_ = lean_ctor_get(v_key_1122_, 1);
v___x_1130_ = lean_array_get_size(v_x_1120_);
v___x_1131_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1128_);
v___x_1132_ = l_Lean_instHashableMVarId_hash(v_snd_1129_);
v___x_1133_ = lean_uint64_mix_hash(v___x_1131_, v___x_1132_);
v___x_1134_ = 32ULL;
v___x_1135_ = lean_uint64_shift_right(v___x_1133_, v___x_1134_);
v_fold_1136_ = lean_uint64_xor(v___x_1133_, v___x_1135_);
v___x_1137_ = 16ULL;
v___x_1138_ = lean_uint64_shift_right(v_fold_1136_, v___x_1137_);
v___x_1139_ = lean_uint64_xor(v_fold_1136_, v___x_1138_);
v___x_1140_ = lean_uint64_to_usize(v___x_1139_);
v___x_1141_ = lean_usize_of_nat(v___x_1130_);
v___x_1142_ = ((size_t)1ULL);
v___x_1143_ = lean_usize_sub(v___x_1141_, v___x_1142_);
v___x_1144_ = lean_usize_land(v___x_1140_, v___x_1143_);
v___x_1145_ = lean_array_uget_borrowed(v_x_1120_, v___x_1144_);
lean_inc(v___x_1145_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 2, v___x_1145_);
v___x_1147_ = v___x_1126_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_key_1122_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v_value_1123_);
lean_ctor_set(v_reuseFailAlloc_1150_, 2, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1148_; 
v___x_1148_ = lean_array_uset(v_x_1120_, v___x_1144_, v___x_1147_);
v_x_1120_ = v___x_1148_;
v_x_1121_ = v_tail_1124_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3___redArg(lean_object* v_i_1152_, lean_object* v_source_1153_, lean_object* v_target_1154_){
_start:
{
lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = lean_array_get_size(v_source_1153_);
v___x_1156_ = lean_nat_dec_lt(v_i_1152_, v___x_1155_);
if (v___x_1156_ == 0)
{
lean_dec_ref(v_source_1153_);
lean_dec(v_i_1152_);
return v_target_1154_;
}
else
{
lean_object* v_es_1157_; lean_object* v___x_1158_; lean_object* v_source_1159_; lean_object* v_target_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v_es_1157_ = lean_array_fget(v_source_1153_, v_i_1152_);
v___x_1158_ = lean_box(0);
v_source_1159_ = lean_array_fset(v_source_1153_, v_i_1152_, v___x_1158_);
v_target_1160_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3_spec__8___redArg(v_target_1154_, v_es_1157_);
v___x_1161_ = lean_unsigned_to_nat(1u);
v___x_1162_ = lean_nat_add(v_i_1152_, v___x_1161_);
lean_dec(v_i_1152_);
v_i_1152_ = v___x_1162_;
v_source_1153_ = v_source_1159_;
v_target_1154_ = v_target_1160_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2___redArg(lean_object* v_data_1164_){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v_nbuckets_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1165_ = lean_array_get_size(v_data_1164_);
v___x_1166_ = lean_unsigned_to_nat(2u);
v_nbuckets_1167_ = lean_nat_mul(v___x_1165_, v___x_1166_);
v___x_1168_ = lean_unsigned_to_nat(0u);
v___x_1169_ = lean_box(0);
v___x_1170_ = lean_mk_array(v_nbuckets_1167_, v___x_1169_);
v___x_1171_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3___redArg(v___x_1168_, v_data_1164_, v___x_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(lean_object* v_m_1172_, lean_object* v_a_1173_, lean_object* v_b_1174_){
_start:
{
lean_object* v_size_1175_; lean_object* v_buckets_1176_; lean_object* v_fst_1177_; lean_object* v_snd_1178_; lean_object* v___x_1179_; uint64_t v___x_1180_; uint64_t v___x_1181_; uint64_t v___x_1182_; uint64_t v___x_1183_; uint64_t v___x_1184_; uint64_t v_fold_1185_; uint64_t v___x_1186_; uint64_t v___x_1187_; uint64_t v___x_1188_; size_t v___x_1189_; size_t v___x_1190_; size_t v___x_1191_; size_t v___x_1192_; size_t v___x_1193_; lean_object* v_bkt_1194_; uint8_t v___x_1195_; 
v_size_1175_ = lean_ctor_get(v_m_1172_, 0);
v_buckets_1176_ = lean_ctor_get(v_m_1172_, 1);
v_fst_1177_ = lean_ctor_get(v_a_1173_, 0);
v_snd_1178_ = lean_ctor_get(v_a_1173_, 1);
v___x_1179_ = lean_array_get_size(v_buckets_1176_);
v___x_1180_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1177_);
v___x_1181_ = l_Lean_instHashableMVarId_hash(v_snd_1178_);
v___x_1182_ = lean_uint64_mix_hash(v___x_1180_, v___x_1181_);
v___x_1183_ = 32ULL;
v___x_1184_ = lean_uint64_shift_right(v___x_1182_, v___x_1183_);
v_fold_1185_ = lean_uint64_xor(v___x_1182_, v___x_1184_);
v___x_1186_ = 16ULL;
v___x_1187_ = lean_uint64_shift_right(v_fold_1185_, v___x_1186_);
v___x_1188_ = lean_uint64_xor(v_fold_1185_, v___x_1187_);
v___x_1189_ = lean_uint64_to_usize(v___x_1188_);
v___x_1190_ = lean_usize_of_nat(v___x_1179_);
v___x_1191_ = ((size_t)1ULL);
v___x_1192_ = lean_usize_sub(v___x_1190_, v___x_1191_);
v___x_1193_ = lean_usize_land(v___x_1189_, v___x_1192_);
v_bkt_1194_ = lean_array_uget_borrowed(v_buckets_1176_, v___x_1193_);
v___x_1195_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(v_a_1173_, v_bkt_1194_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1216_; 
lean_inc_ref(v_buckets_1176_);
lean_inc(v_size_1175_);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_m_1172_);
if (v_isSharedCheck_1216_ == 0)
{
lean_object* v_unused_1217_; lean_object* v_unused_1218_; 
v_unused_1217_ = lean_ctor_get(v_m_1172_, 1);
lean_dec(v_unused_1217_);
v_unused_1218_ = lean_ctor_get(v_m_1172_, 0);
lean_dec(v_unused_1218_);
v___x_1197_ = v_m_1172_;
v_isShared_1198_ = v_isSharedCheck_1216_;
goto v_resetjp_1196_;
}
else
{
lean_dec(v_m_1172_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1216_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1199_; lean_object* v_size_x27_1200_; lean_object* v___x_1201_; lean_object* v_buckets_x27_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; 
v___x_1199_ = lean_unsigned_to_nat(1u);
v_size_x27_1200_ = lean_nat_add(v_size_1175_, v___x_1199_);
lean_dec(v_size_1175_);
lean_inc(v_bkt_1194_);
v___x_1201_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1201_, 0, v_a_1173_);
lean_ctor_set(v___x_1201_, 1, v_b_1174_);
lean_ctor_set(v___x_1201_, 2, v_bkt_1194_);
v_buckets_x27_1202_ = lean_array_uset(v_buckets_1176_, v___x_1193_, v___x_1201_);
v___x_1203_ = lean_unsigned_to_nat(4u);
v___x_1204_ = lean_nat_mul(v_size_x27_1200_, v___x_1203_);
v___x_1205_ = lean_unsigned_to_nat(3u);
v___x_1206_ = lean_nat_div(v___x_1204_, v___x_1205_);
lean_dec(v___x_1204_);
v___x_1207_ = lean_array_get_size(v_buckets_x27_1202_);
v___x_1208_ = lean_nat_dec_le(v___x_1206_, v___x_1207_);
lean_dec(v___x_1206_);
if (v___x_1208_ == 0)
{
lean_object* v_val_1209_; lean_object* v___x_1211_; 
v_val_1209_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2___redArg(v_buckets_x27_1202_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 1, v_val_1209_);
lean_ctor_set(v___x_1197_, 0, v_size_x27_1200_);
v___x_1211_ = v___x_1197_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_size_x27_1200_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_val_1209_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
else
{
lean_object* v___x_1214_; 
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 1, v_buckets_x27_1202_);
lean_ctor_set(v___x_1197_, 0, v_size_x27_1200_);
v___x_1214_ = v___x_1197_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_size_x27_1200_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v_buckets_x27_1202_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
else
{
lean_dec(v_b_1174_);
lean_dec_ref(v_a_1173_);
return v_m_1172_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(lean_object* v___x_1219_, lean_object* v_fst_1220_, lean_object* v_snd_1221_, lean_object* v___x_1222_, lean_object* v_as_1223_, size_t v_sz_1224_, size_t v_i_1225_, lean_object* v_b_1226_){
_start:
{
lean_object* v_a_1229_; uint8_t v___x_1233_; 
v___x_1233_ = lean_usize_dec_lt(v_i_1225_, v_sz_1224_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; 
lean_dec(v___x_1222_);
lean_dec(v_snd_1221_);
lean_dec(v_fst_1220_);
lean_dec_ref(v___x_1219_);
v___x_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1234_, 0, v_b_1226_);
return v___x_1234_;
}
else
{
lean_object* v_a_1235_; lean_object* v_snd_1236_; lean_object* v_fst_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1273_; 
v_a_1235_ = lean_array_uget(v_as_1223_, v_i_1225_);
v_snd_1236_ = lean_ctor_get(v_a_1235_, 1);
v_fst_1237_ = lean_ctor_get(v_a_1235_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_a_1235_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1239_ = v_a_1235_;
v_isShared_1240_ = v_isSharedCheck_1273_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_snd_1236_);
lean_inc(v_fst_1237_);
lean_dec(v_a_1235_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1273_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v_fst_1241_; lean_object* v_snd_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1272_; 
v_fst_1241_ = lean_ctor_get(v_snd_1236_, 0);
v_snd_1242_ = lean_ctor_get(v_snd_1236_, 1);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_snd_1236_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1244_ = v_snd_1236_;
v_isShared_1245_ = v_isSharedCheck_1272_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_snd_1242_);
lean_inc(v_fst_1241_);
lean_dec(v_snd_1236_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1272_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v_fst_1246_; lean_object* v_snd_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1271_; 
v_fst_1246_ = lean_ctor_get(v_b_1226_, 0);
v_snd_1247_ = lean_ctor_get(v_b_1226_, 1);
v_isSharedCheck_1271_ = !lean_is_exclusive(v_b_1226_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1249_ = v_b_1226_;
v_isShared_1250_ = v_isSharedCheck_1271_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_snd_1247_);
lean_inc(v_fst_1246_);
lean_dec(v_b_1226_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1271_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
lean_inc(v_snd_1242_);
lean_inc_ref(v___x_1219_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 1, v_snd_1242_);
lean_ctor_set(v___x_1249_, 0, v___x_1219_);
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_snd_1242_);
v___x_1252_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
uint8_t v___x_1253_; 
v___x_1253_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(v_snd_1247_, v___x_1252_);
if (v___x_1253_ == 0)
{
lean_object* v_env_1254_; lean_object* v_mctx_1255_; lean_object* v_opts_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1260_; 
v_env_1254_ = lean_ctor_get(v_fst_1237_, 0);
lean_inc_ref(v_env_1254_);
v_mctx_1255_ = lean_ctor_get(v_fst_1237_, 1);
lean_inc_ref(v_mctx_1255_);
v_opts_1256_ = lean_ctor_get(v_fst_1237_, 3);
lean_inc_ref(v_opts_1256_);
lean_dec(v_fst_1237_);
v___x_1257_ = lean_box(0);
v___x_1258_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_snd_1247_, v___x_1252_, v___x_1257_);
lean_inc(v_snd_1221_);
lean_inc(v_fst_1220_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 1, v_snd_1221_);
lean_ctor_set(v___x_1239_, 0, v_fst_1220_);
v___x_1260_ = v___x_1239_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_fst_1220_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v_snd_1221_);
v___x_1260_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1264_; 
lean_inc(v___x_1222_);
v___x_1261_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
lean_ctor_set(v___x_1261_, 1, v___x_1222_);
lean_ctor_set(v___x_1261_, 2, v_env_1254_);
lean_ctor_set(v___x_1261_, 3, v_mctx_1255_);
lean_ctor_set(v___x_1261_, 4, v_opts_1256_);
lean_ctor_set(v___x_1261_, 5, v_fst_1241_);
lean_ctor_set(v___x_1261_, 6, v_snd_1242_);
v___x_1262_ = lean_array_push(v_fst_1246_, v___x_1261_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v___x_1258_);
lean_ctor_set(v___x_1244_, 0, v___x_1262_);
v___x_1264_ = v___x_1244_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1262_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v___x_1258_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
v_a_1229_ = v___x_1264_;
goto v___jp_1228_;
}
}
}
else
{
lean_object* v___x_1268_; 
lean_dec_ref(v___x_1252_);
lean_dec(v_snd_1242_);
lean_dec(v_fst_1241_);
lean_del_object(v___x_1239_);
lean_dec(v_fst_1237_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v_snd_1247_);
lean_ctor_set(v___x_1244_, 0, v_fst_1246_);
v___x_1268_ = v___x_1244_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_fst_1246_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v_snd_1247_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
v_a_1229_ = v___x_1268_;
goto v___jp_1228_;
}
}
}
}
}
}
}
v___jp_1228_:
{
size_t v___x_1230_; size_t v___x_1231_; 
v___x_1230_ = ((size_t)1ULL);
v___x_1231_ = lean_usize_add(v_i_1225_, v___x_1230_);
v_i_1225_ = v___x_1231_;
v_b_1226_ = v_a_1229_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg___boxed(lean_object* v___x_1274_, lean_object* v_fst_1275_, lean_object* v_snd_1276_, lean_object* v___x_1277_, lean_object* v_as_1278_, lean_object* v_sz_1279_, lean_object* v_i_1280_, lean_object* v_b_1281_, lean_object* v___y_1282_){
_start:
{
size_t v_sz_boxed_1283_; size_t v_i_boxed_1284_; lean_object* v_res_1285_; 
v_sz_boxed_1283_ = lean_unbox_usize(v_sz_1279_);
lean_dec(v_sz_1279_);
v_i_boxed_1284_ = lean_unbox_usize(v_i_1280_);
lean_dec(v_i_1280_);
v_res_1285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1274_, v_fst_1275_, v_snd_1276_, v___x_1277_, v_as_1278_, v_sz_boxed_1283_, v_i_boxed_1284_, v_b_1281_);
lean_dec_ref(v_as_1278_);
return v_res_1285_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1290_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1291_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__2));
v___x_1292_ = l_Lean_Name_append(v___x_1291_, v___x_1290_);
return v___x_1292_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__4));
v___x_1295_ = l_Lean_stringToMessageData(v___x_1294_);
return v___x_1295_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__6));
v___x_1298_ = l_Lean_stringToMessageData(v___x_1297_);
return v___x_1298_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9(void){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__8));
v___x_1301_ = l_Lean_stringToMessageData(v___x_1300_);
return v___x_1301_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__10));
v___x_1304_ = l_Lean_stringToMessageData(v___x_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12(lean_object* v___x_1305_, lean_object* v_val_1306_, lean_object* v_cmd_1307_, uint8_t v_onUnsolved_1308_, uint8_t v___y_1309_, lean_object* v_as_1310_, size_t v_sz_1311_, size_t v_i_1312_, lean_object* v_b_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
uint8_t v___x_1317_; 
v___x_1317_ = lean_usize_dec_lt(v_i_1312_, v_sz_1311_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; 
lean_dec(v_cmd_1307_);
v___x_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1318_, 0, v_b_1313_);
return v___x_1318_;
}
else
{
lean_object* v_snd_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1467_; 
v_snd_1319_ = lean_ctor_get(v_b_1313_, 1);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_b_1313_);
if (v_isSharedCheck_1467_ == 0)
{
lean_object* v_unused_1468_; 
v_unused_1468_ = lean_ctor_get(v_b_1313_, 0);
lean_dec(v_unused_1468_);
v___x_1321_ = v_b_1313_;
v_isShared_1322_ = v_isSharedCheck_1467_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_snd_1319_);
lean_dec(v_b_1313_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1467_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v_fst_1323_; lean_object* v_snd_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1466_; 
v_fst_1323_ = lean_ctor_get(v_snd_1319_, 0);
v_snd_1324_ = lean_ctor_get(v_snd_1319_, 1);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_snd_1319_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1326_ = v_snd_1319_;
v_isShared_1327_ = v_isSharedCheck_1466_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_snd_1324_);
lean_inc(v_fst_1323_);
lean_dec(v_snd_1319_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1466_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v_a_1328_; lean_object* v_pos_1329_; lean_object* v_endPos_1330_; uint8_t v_severity_1331_; lean_object* v_data_1332_; lean_object* v___x_1333_; lean_object* v_a_1335_; 
v_a_1328_ = lean_array_uget_borrowed(v_as_1310_, v_i_1312_);
v_pos_1329_ = lean_ctor_get(v_a_1328_, 1);
v_endPos_1330_ = lean_ctor_get(v_a_1328_, 2);
lean_inc(v_endPos_1330_);
v_severity_1331_ = lean_ctor_get_uint8(v_a_1328_, sizeof(void*)*5 + 1);
v_data_1332_ = lean_ctor_get(v_a_1328_, 4);
v___x_1333_ = lean_box(0);
if (v_severity_1331_ == 2)
{
lean_object* v___f_1348_; uint8_t v___x_1349_; 
v___f_1348_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
lean_inc(v_data_1332_);
v___x_1349_ = l_Lean_MessageData_hasTag(v___f_1348_, v_data_1332_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; 
lean_dec(v_endPos_1330_);
lean_del_object(v___x_1321_);
v___x_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1350_, 0, v_fst_1323_);
lean_ctor_set(v___x_1350_, 1, v_snd_1324_);
v_a_1335_ = v___x_1350_;
goto v___jp_1334_;
}
else
{
if (lean_obj_tag(v_endPos_1330_) == 1)
{
lean_object* v_val_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1463_; 
v_val_1351_ = lean_ctor_get(v_endPos_1330_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_endPos_1330_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1353_ = v_endPos_1330_;
v_isShared_1354_ = v_isSharedCheck_1463_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_val_1351_);
lean_dec(v_endPos_1330_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1463_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; uint8_t v___x_1359_; 
lean_inc_ref(v_pos_1329_);
v___x_1355_ = l_Lean_FileMap_ofPosition(v___x_1305_, v_pos_1329_);
v___x_1356_ = l_Lean_FileMap_ofPosition(v___x_1305_, v_val_1351_);
lean_inc(v___x_1356_);
lean_inc(v___x_1355_);
v___x_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1355_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = 0;
v___x_1359_ = l_Lean_Syntax_Range_includes(v_val_1306_, v___x_1357_, v___x_1358_, v___x_1358_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; 
lean_dec_ref_known(v___x_1357_, 2);
lean_dec(v___x_1356_);
lean_dec(v___x_1355_);
lean_del_object(v___x_1353_);
lean_del_object(v___x_1321_);
v___x_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1360_, 0, v_fst_1323_);
lean_ctor_set(v___x_1360_, 1, v_snd_1324_);
v_a_1335_ = v___x_1360_;
goto v___jp_1334_;
}
else
{
lean_object* v___x_1361_; 
lean_inc(v_cmd_1307_);
lean_inc_ref(v___x_1357_);
v___x_1361_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1357_, v_cmd_1307_);
if (lean_obj_tag(v___x_1361_) == 1)
{
lean_object* v_val_1362_; lean_object* v_fst_1363_; lean_object* v_snd_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1427_; 
lean_dec(v___x_1356_);
lean_dec(v___x_1355_);
lean_del_object(v___x_1353_);
v_val_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_val_1362_);
lean_dec_ref_known(v___x_1361_, 1);
v_fst_1363_ = lean_ctor_get(v_val_1362_, 0);
v_snd_1364_ = lean_ctor_get(v_val_1362_, 1);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_val_1362_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1366_ = v_val_1362_;
v_isShared_1367_ = v_isSharedCheck_1427_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_snd_1364_);
lean_inc(v_fst_1363_);
lean_dec(v_val_1362_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1427_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; uint8_t v___y_1425_; lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_Syntax_getPos_x3f(v_fst_1363_, v___x_1358_);
if (lean_obj_tag(v___x_1426_) == 0)
{
v___y_1425_ = v___x_1359_;
goto v___jp_1424_;
}
else
{
lean_dec_ref_known(v___x_1426_, 1);
v___y_1425_ = v___x_1358_;
goto v___jp_1424_;
}
v___jp_1368_:
{
lean_object* v___x_1374_; 
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 1, v_snd_1324_);
lean_ctor_set(v___x_1366_, 0, v_fst_1323_);
v___x_1374_ = v___x_1366_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_fst_1323_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_snd_1324_);
v___x_1374_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
size_t v_sz_1375_; size_t v___x_1376_; lean_object* v___x_1377_; 
v_sz_1375_ = lean_array_size(v___y_1370_);
v___x_1376_ = ((size_t)0ULL);
v___x_1377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1357_, v_fst_1363_, v_snd_1364_, v___y_1369_, v___y_1370_, v_sz_1375_, v___x_1376_, v___x_1374_);
lean_dec_ref(v___y_1370_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v_fst_1379_; lean_object* v_snd_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
lean_dec_ref_known(v___x_1377_, 1);
v_fst_1379_ = lean_ctor_get(v_a_1378_, 0);
v_snd_1380_ = lean_ctor_get(v_a_1378_, 1);
v_isSharedCheck_1387_ = !lean_is_exclusive(v_a_1378_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v_a_1378_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_snd_1380_);
lean_inc(v_fst_1379_);
lean_dec(v_a_1378_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_fst_1379_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_snd_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
v_a_1335_ = v___x_1385_;
goto v___jp_1334_;
}
}
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
lean_del_object(v___x_1326_);
lean_dec(v_cmd_1307_);
v_a_1388_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1377_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1377_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
}
v___jp_1397_:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
lean_inc_ref(v___x_1357_);
v___x_1398_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1357_);
v___x_1399_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1332_);
v___x_1400_ = lean_array_get_size(v___x_1399_);
v___x_1401_ = lean_unsigned_to_nat(0u);
v___x_1402_ = lean_nat_dec_eq(v___x_1400_, v___x_1401_);
if (v___x_1402_ == 0)
{
v___y_1369_ = v___x_1398_;
v___y_1370_ = v___x_1399_;
v___y_1371_ = v___y_1314_;
v___y_1372_ = v___y_1315_;
goto v___jp_1368_;
}
else
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v_scopes_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v_opts_1409_; uint8_t v_hasTrace_1410_; 
v___x_1403_ = l_Lean_inheritedTraceOptions;
v___x_1404_ = lean_st_ref_get(v___x_1403_);
v___x_1405_ = lean_st_ref_get(v___y_1315_);
v_scopes_1406_ = lean_ctor_get(v___x_1405_, 2);
lean_inc(v_scopes_1406_);
lean_dec(v___x_1405_);
v___x_1407_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1408_ = l_List_head_x21___redArg(v___x_1407_, v_scopes_1406_);
lean_dec(v_scopes_1406_);
v_opts_1409_ = lean_ctor_get(v___x_1408_, 1);
lean_inc_ref(v_opts_1409_);
lean_dec(v___x_1408_);
v_hasTrace_1410_ = lean_ctor_get_uint8(v_opts_1409_, sizeof(void*)*1);
if (v_hasTrace_1410_ == 0)
{
lean_dec_ref(v_opts_1409_);
lean_dec(v___x_1404_);
v___y_1369_ = v___x_1398_;
v___y_1370_ = v___x_1399_;
v___y_1371_ = v___y_1314_;
v___y_1372_ = v___y_1315_;
goto v___jp_1368_;
}
else
{
lean_object* v___x_1411_; lean_object* v___x_1412_; uint8_t v___x_1413_; 
v___x_1411_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1412_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1413_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1404_, v_opts_1409_, v___x_1412_);
lean_dec_ref(v_opts_1409_);
lean_dec(v___x_1404_);
if (v___x_1413_ == 0)
{
v___y_1369_ = v___x_1398_;
v___y_1370_ = v___x_1399_;
v___y_1371_ = v___y_1314_;
v___y_1372_ = v___y_1315_;
goto v___jp_1368_;
}
else
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5);
v___x_1415_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1411_, v___x_1414_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_dec_ref_known(v___x_1415_, 1);
v___y_1369_ = v___x_1398_;
v___y_1370_ = v___x_1399_;
v___y_1371_ = v___y_1314_;
v___y_1372_ = v___y_1315_;
goto v___jp_1368_;
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
lean_dec_ref(v___x_1399_);
lean_dec(v___x_1398_);
lean_del_object(v___x_1366_);
lean_dec(v_snd_1364_);
lean_dec(v_fst_1363_);
lean_dec_ref_known(v___x_1357_, 2);
lean_del_object(v___x_1326_);
lean_dec(v_snd_1324_);
lean_dec(v_fst_1323_);
lean_dec(v_cmd_1307_);
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
}
}
}
v___jp_1424_:
{
if (v_onUnsolved_1308_ == 0)
{
if (v___y_1309_ == 0)
{
lean_del_object(v___x_1366_);
lean_dec(v_snd_1364_);
lean_dec(v_fst_1363_);
lean_dec_ref_known(v___x_1357_, 2);
goto v___jp_1342_;
}
else
{
if (v___y_1425_ == 0)
{
lean_del_object(v___x_1366_);
lean_dec(v_snd_1364_);
lean_dec(v_fst_1363_);
lean_dec_ref_known(v___x_1357_, 2);
goto v___jp_1342_;
}
else
{
lean_del_object(v___x_1321_);
goto v___jp_1397_;
}
}
}
else
{
lean_del_object(v___x_1321_);
goto v___jp_1397_;
}
}
}
}
else
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v_scopes_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v_opts_1434_; uint8_t v_hasTrace_1435_; 
lean_dec(v___x_1361_);
lean_dec_ref_known(v___x_1357_, 2);
lean_del_object(v___x_1321_);
v___x_1428_ = l_Lean_inheritedTraceOptions;
v___x_1429_ = lean_st_ref_get(v___x_1428_);
v___x_1430_ = lean_st_ref_get(v___y_1315_);
v_scopes_1431_ = lean_ctor_get(v___x_1430_, 2);
lean_inc(v_scopes_1431_);
lean_dec(v___x_1430_);
v___x_1432_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1433_ = l_List_head_x21___redArg(v___x_1432_, v_scopes_1431_);
lean_dec(v_scopes_1431_);
v_opts_1434_ = lean_ctor_get(v___x_1433_, 1);
lean_inc_ref(v_opts_1434_);
lean_dec(v___x_1433_);
v_hasTrace_1435_ = lean_ctor_get_uint8(v_opts_1434_, sizeof(void*)*1);
if (v_hasTrace_1435_ == 0)
{
lean_dec_ref(v_opts_1434_);
lean_dec(v___x_1429_);
lean_dec(v___x_1356_);
lean_dec(v___x_1355_);
lean_del_object(v___x_1353_);
goto v___jp_1346_;
}
else
{
lean_object* v___x_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; 
v___x_1436_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1437_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1438_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1429_, v_opts_1434_, v___x_1437_);
lean_dec_ref(v_opts_1434_);
lean_dec(v___x_1429_);
if (v___x_1438_ == 0)
{
lean_dec(v___x_1356_);
lean_dec(v___x_1355_);
lean_del_object(v___x_1353_);
goto v___jp_1346_;
}
else
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1442_; 
v___x_1439_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7);
v___x_1440_ = l_Nat_reprFast(v___x_1355_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set_tag(v___x_1353_, 3);
lean_ctor_set(v___x_1353_, 0, v___x_1440_);
v___x_1442_ = v___x_1353_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1440_);
v___x_1442_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1443_ = l_Lean_MessageData_ofFormat(v___x_1442_);
v___x_1444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1439_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
v___x_1445_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9);
v___x_1446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1444_);
lean_ctor_set(v___x_1446_, 1, v___x_1445_);
v___x_1447_ = l_Nat_reprFast(v___x_1356_);
v___x_1448_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
v___x_1449_ = l_Lean_MessageData_ofFormat(v___x_1448_);
v___x_1450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1446_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
v___x_1451_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11);
v___x_1452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1450_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
v___x_1453_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1436_, v___x_1452_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_dec_ref_known(v___x_1453_, 1);
goto v___jp_1346_;
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_del_object(v___x_1326_);
lean_dec(v_snd_1324_);
lean_dec(v_fst_1323_);
lean_dec(v_cmd_1307_);
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1453_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1453_);
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
}
}
}
else
{
lean_object* v___x_1464_; 
lean_dec(v_endPos_1330_);
lean_del_object(v___x_1321_);
v___x_1464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1464_, 0, v_fst_1323_);
lean_ctor_set(v___x_1464_, 1, v_snd_1324_);
v_a_1335_ = v___x_1464_;
goto v___jp_1334_;
}
}
}
else
{
lean_object* v___x_1465_; 
lean_dec(v_endPos_1330_);
lean_del_object(v___x_1321_);
v___x_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1465_, 0, v_fst_1323_);
lean_ctor_set(v___x_1465_, 1, v_snd_1324_);
v_a_1335_ = v___x_1465_;
goto v___jp_1334_;
}
v___jp_1334_:
{
lean_object* v___x_1337_; 
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 1, v_a_1335_);
lean_ctor_set(v___x_1326_, 0, v___x_1333_);
v___x_1337_ = v___x_1326_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1333_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v_a_1335_);
v___x_1337_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
size_t v___x_1338_; size_t v___x_1339_; 
v___x_1338_ = ((size_t)1ULL);
v___x_1339_ = lean_usize_add(v_i_1312_, v___x_1338_);
v_i_1312_ = v___x_1339_;
v_b_1313_ = v___x_1337_;
goto _start;
}
}
v___jp_1342_:
{
lean_object* v___x_1344_; 
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 1, v_snd_1324_);
lean_ctor_set(v___x_1321_, 0, v_fst_1323_);
v___x_1344_ = v___x_1321_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_fst_1323_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v_snd_1324_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
v_a_1335_ = v___x_1344_;
goto v___jp_1334_;
}
}
v___jp_1346_:
{
lean_object* v___x_1347_; 
v___x_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1347_, 0, v_fst_1323_);
lean_ctor_set(v___x_1347_, 1, v_snd_1324_);
v_a_1335_ = v___x_1347_;
goto v___jp_1334_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___boxed(lean_object* v___x_1469_, lean_object* v_val_1470_, lean_object* v_cmd_1471_, lean_object* v_onUnsolved_1472_, lean_object* v___y_1473_, lean_object* v_as_1474_, lean_object* v_sz_1475_, lean_object* v_i_1476_, lean_object* v_b_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
uint8_t v_onUnsolved_boxed_1481_; uint8_t v___y_14962__boxed_1482_; size_t v_sz_boxed_1483_; size_t v_i_boxed_1484_; lean_object* v_res_1485_; 
v_onUnsolved_boxed_1481_ = lean_unbox(v_onUnsolved_1472_);
v___y_14962__boxed_1482_ = lean_unbox(v___y_1473_);
v_sz_boxed_1483_ = lean_unbox_usize(v_sz_1475_);
lean_dec(v_sz_1475_);
v_i_boxed_1484_ = lean_unbox_usize(v_i_1476_);
lean_dec(v_i_1476_);
v_res_1485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12(v___x_1469_, v_val_1470_, v_cmd_1471_, v_onUnsolved_boxed_1481_, v___y_14962__boxed_1482_, v_as_1474_, v_sz_boxed_1483_, v_i_boxed_1484_, v_b_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec_ref(v_as_1474_);
lean_dec_ref(v_val_1470_);
lean_dec_ref(v___x_1469_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8(lean_object* v___x_1486_, lean_object* v_val_1487_, lean_object* v_cmd_1488_, uint8_t v_onUnsolved_1489_, uint8_t v___y_1490_, lean_object* v_as_1491_, size_t v_sz_1492_, size_t v_i_1493_, lean_object* v_b_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
uint8_t v___x_1498_; 
v___x_1498_ = lean_usize_dec_lt(v_i_1493_, v_sz_1492_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; 
lean_dec(v_cmd_1488_);
v___x_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1499_, 0, v_b_1494_);
return v___x_1499_;
}
else
{
lean_object* v_snd_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1648_; 
v_snd_1500_ = lean_ctor_get(v_b_1494_, 1);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_b_1494_);
if (v_isSharedCheck_1648_ == 0)
{
lean_object* v_unused_1649_; 
v_unused_1649_ = lean_ctor_get(v_b_1494_, 0);
lean_dec(v_unused_1649_);
v___x_1502_ = v_b_1494_;
v_isShared_1503_ = v_isSharedCheck_1648_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_snd_1500_);
lean_dec(v_b_1494_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1648_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v_fst_1504_; lean_object* v_snd_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1647_; 
v_fst_1504_ = lean_ctor_get(v_snd_1500_, 0);
v_snd_1505_ = lean_ctor_get(v_snd_1500_, 1);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_snd_1500_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1507_ = v_snd_1500_;
v_isShared_1508_ = v_isSharedCheck_1647_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_snd_1505_);
lean_inc(v_fst_1504_);
lean_dec(v_snd_1500_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1647_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v_a_1509_; lean_object* v_pos_1510_; lean_object* v_endPos_1511_; uint8_t v_severity_1512_; lean_object* v_data_1513_; lean_object* v___x_1514_; lean_object* v_a_1516_; 
v_a_1509_ = lean_array_uget_borrowed(v_as_1491_, v_i_1493_);
v_pos_1510_ = lean_ctor_get(v_a_1509_, 1);
v_endPos_1511_ = lean_ctor_get(v_a_1509_, 2);
lean_inc(v_endPos_1511_);
v_severity_1512_ = lean_ctor_get_uint8(v_a_1509_, sizeof(void*)*5 + 1);
v_data_1513_ = lean_ctor_get(v_a_1509_, 4);
v___x_1514_ = lean_box(0);
if (v_severity_1512_ == 2)
{
lean_object* v___f_1529_; uint8_t v___x_1530_; 
v___f_1529_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
lean_inc(v_data_1513_);
v___x_1530_ = l_Lean_MessageData_hasTag(v___f_1529_, v_data_1513_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; 
lean_dec(v_endPos_1511_);
lean_del_object(v___x_1502_);
v___x_1531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1531_, 0, v_fst_1504_);
lean_ctor_set(v___x_1531_, 1, v_snd_1505_);
v_a_1516_ = v___x_1531_;
goto v___jp_1515_;
}
else
{
if (lean_obj_tag(v_endPos_1511_) == 1)
{
lean_object* v_val_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1644_; 
v_val_1532_ = lean_ctor_get(v_endPos_1511_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v_endPos_1511_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1534_ = v_endPos_1511_;
v_isShared_1535_ = v_isSharedCheck_1644_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_val_1532_);
lean_dec(v_endPos_1511_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1644_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; uint8_t v___x_1540_; 
lean_inc_ref(v_pos_1510_);
v___x_1536_ = l_Lean_FileMap_ofPosition(v___x_1486_, v_pos_1510_);
v___x_1537_ = l_Lean_FileMap_ofPosition(v___x_1486_, v_val_1532_);
lean_inc(v___x_1537_);
lean_inc(v___x_1536_);
v___x_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1536_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = 0;
v___x_1540_ = l_Lean_Syntax_Range_includes(v_val_1487_, v___x_1538_, v___x_1539_, v___x_1539_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; 
lean_dec_ref_known(v___x_1538_, 2);
lean_dec(v___x_1537_);
lean_dec(v___x_1536_);
lean_del_object(v___x_1534_);
lean_del_object(v___x_1502_);
v___x_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1541_, 0, v_fst_1504_);
lean_ctor_set(v___x_1541_, 1, v_snd_1505_);
v_a_1516_ = v___x_1541_;
goto v___jp_1515_;
}
else
{
lean_object* v___x_1542_; 
lean_inc(v_cmd_1488_);
lean_inc_ref(v___x_1538_);
v___x_1542_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1538_, v_cmd_1488_);
if (lean_obj_tag(v___x_1542_) == 1)
{
lean_object* v_val_1543_; lean_object* v_fst_1544_; lean_object* v_snd_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1608_; 
lean_dec(v___x_1537_);
lean_dec(v___x_1536_);
lean_del_object(v___x_1534_);
v_val_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_val_1543_);
lean_dec_ref_known(v___x_1542_, 1);
v_fst_1544_ = lean_ctor_get(v_val_1543_, 0);
v_snd_1545_ = lean_ctor_get(v_val_1543_, 1);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_val_1543_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1547_ = v_val_1543_;
v_isShared_1548_ = v_isSharedCheck_1608_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_snd_1545_);
lean_inc(v_fst_1544_);
lean_dec(v_val_1543_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1608_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; uint8_t v___y_1606_; lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_Syntax_getPos_x3f(v_fst_1544_, v___x_1539_);
if (lean_obj_tag(v___x_1607_) == 0)
{
v___y_1606_ = v___x_1540_;
goto v___jp_1605_;
}
else
{
lean_dec_ref_known(v___x_1607_, 1);
v___y_1606_ = v___x_1539_;
goto v___jp_1605_;
}
v___jp_1549_:
{
lean_object* v___x_1555_; 
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 1, v_snd_1505_);
lean_ctor_set(v___x_1547_, 0, v_fst_1504_);
v___x_1555_ = v___x_1547_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_fst_1504_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_snd_1505_);
v___x_1555_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
size_t v_sz_1556_; size_t v___x_1557_; lean_object* v___x_1558_; 
v_sz_1556_ = lean_array_size(v___y_1550_);
v___x_1557_ = ((size_t)0ULL);
v___x_1558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1538_, v_fst_1544_, v_snd_1545_, v___y_1551_, v___y_1550_, v_sz_1556_, v___x_1557_, v___x_1555_);
lean_dec_ref(v___y_1550_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v_fst_1560_; lean_object* v_snd_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1559_);
lean_dec_ref_known(v___x_1558_, 1);
v_fst_1560_ = lean_ctor_get(v_a_1559_, 0);
v_snd_1561_ = lean_ctor_get(v_a_1559_, 1);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_a_1559_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v_a_1559_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_snd_1561_);
lean_inc(v_fst_1560_);
lean_dec(v_a_1559_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_fst_1560_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_snd_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
v_a_1516_ = v___x_1566_;
goto v___jp_1515_;
}
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_del_object(v___x_1507_);
lean_dec(v_cmd_1488_);
v_a_1569_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1558_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1558_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
}
v___jp_1578_:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; 
lean_inc_ref(v___x_1538_);
v___x_1579_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1538_);
v___x_1580_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1513_);
v___x_1581_ = lean_array_get_size(v___x_1580_);
v___x_1582_ = lean_unsigned_to_nat(0u);
v___x_1583_ = lean_nat_dec_eq(v___x_1581_, v___x_1582_);
if (v___x_1583_ == 0)
{
v___y_1550_ = v___x_1580_;
v___y_1551_ = v___x_1579_;
v___y_1552_ = v___y_1495_;
v___y_1553_ = v___y_1496_;
goto v___jp_1549_;
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v_scopes_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v_opts_1590_; uint8_t v_hasTrace_1591_; 
v___x_1584_ = l_Lean_inheritedTraceOptions;
v___x_1585_ = lean_st_ref_get(v___x_1584_);
v___x_1586_ = lean_st_ref_get(v___y_1496_);
v_scopes_1587_ = lean_ctor_get(v___x_1586_, 2);
lean_inc(v_scopes_1587_);
lean_dec(v___x_1586_);
v___x_1588_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1589_ = l_List_head_x21___redArg(v___x_1588_, v_scopes_1587_);
lean_dec(v_scopes_1587_);
v_opts_1590_ = lean_ctor_get(v___x_1589_, 1);
lean_inc_ref(v_opts_1590_);
lean_dec(v___x_1589_);
v_hasTrace_1591_ = lean_ctor_get_uint8(v_opts_1590_, sizeof(void*)*1);
if (v_hasTrace_1591_ == 0)
{
lean_dec_ref(v_opts_1590_);
lean_dec(v___x_1585_);
v___y_1550_ = v___x_1580_;
v___y_1551_ = v___x_1579_;
v___y_1552_ = v___y_1495_;
v___y_1553_ = v___y_1496_;
goto v___jp_1549_;
}
else
{
lean_object* v___x_1592_; lean_object* v___x_1593_; uint8_t v___x_1594_; 
v___x_1592_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1593_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1594_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1585_, v_opts_1590_, v___x_1593_);
lean_dec_ref(v_opts_1590_);
lean_dec(v___x_1585_);
if (v___x_1594_ == 0)
{
v___y_1550_ = v___x_1580_;
v___y_1551_ = v___x_1579_;
v___y_1552_ = v___y_1495_;
v___y_1553_ = v___y_1496_;
goto v___jp_1549_;
}
else
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1595_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5);
v___x_1596_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1592_, v___x_1595_, v___y_1495_, v___y_1496_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_dec_ref_known(v___x_1596_, 1);
v___y_1550_ = v___x_1580_;
v___y_1551_ = v___x_1579_;
v___y_1552_ = v___y_1495_;
v___y_1553_ = v___y_1496_;
goto v___jp_1549_;
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
lean_dec_ref(v___x_1580_);
lean_dec(v___x_1579_);
lean_del_object(v___x_1547_);
lean_dec(v_snd_1545_);
lean_dec(v_fst_1544_);
lean_dec_ref_known(v___x_1538_, 2);
lean_del_object(v___x_1507_);
lean_dec(v_snd_1505_);
lean_dec(v_fst_1504_);
lean_dec(v_cmd_1488_);
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1596_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1596_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
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
}
}
}
v___jp_1605_:
{
if (v_onUnsolved_1489_ == 0)
{
if (v___y_1490_ == 0)
{
lean_del_object(v___x_1547_);
lean_dec(v_snd_1545_);
lean_dec(v_fst_1544_);
lean_dec_ref_known(v___x_1538_, 2);
goto v___jp_1523_;
}
else
{
if (v___y_1606_ == 0)
{
lean_del_object(v___x_1547_);
lean_dec(v_snd_1545_);
lean_dec(v_fst_1544_);
lean_dec_ref_known(v___x_1538_, 2);
goto v___jp_1523_;
}
else
{
lean_del_object(v___x_1502_);
goto v___jp_1578_;
}
}
}
else
{
lean_del_object(v___x_1502_);
goto v___jp_1578_;
}
}
}
}
else
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v_scopes_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v_opts_1615_; uint8_t v_hasTrace_1616_; 
lean_dec(v___x_1542_);
lean_dec_ref_known(v___x_1538_, 2);
lean_del_object(v___x_1502_);
v___x_1609_ = l_Lean_inheritedTraceOptions;
v___x_1610_ = lean_st_ref_get(v___x_1609_);
v___x_1611_ = lean_st_ref_get(v___y_1496_);
v_scopes_1612_ = lean_ctor_get(v___x_1611_, 2);
lean_inc(v_scopes_1612_);
lean_dec(v___x_1611_);
v___x_1613_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1614_ = l_List_head_x21___redArg(v___x_1613_, v_scopes_1612_);
lean_dec(v_scopes_1612_);
v_opts_1615_ = lean_ctor_get(v___x_1614_, 1);
lean_inc_ref(v_opts_1615_);
lean_dec(v___x_1614_);
v_hasTrace_1616_ = lean_ctor_get_uint8(v_opts_1615_, sizeof(void*)*1);
if (v_hasTrace_1616_ == 0)
{
lean_dec_ref(v_opts_1615_);
lean_dec(v___x_1610_);
lean_dec(v___x_1537_);
lean_dec(v___x_1536_);
lean_del_object(v___x_1534_);
goto v___jp_1527_;
}
else
{
lean_object* v___x_1617_; lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1617_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1618_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1619_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1610_, v_opts_1615_, v___x_1618_);
lean_dec_ref(v_opts_1615_);
lean_dec(v___x_1610_);
if (v___x_1619_ == 0)
{
lean_dec(v___x_1537_);
lean_dec(v___x_1536_);
lean_del_object(v___x_1534_);
goto v___jp_1527_;
}
else
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1623_; 
v___x_1620_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7);
v___x_1621_ = l_Nat_reprFast(v___x_1536_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set_tag(v___x_1534_, 3);
lean_ctor_set(v___x_1534_, 0, v___x_1621_);
v___x_1623_ = v___x_1534_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1624_ = l_Lean_MessageData_ofFormat(v___x_1623_);
v___x_1625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1620_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
v___x_1626_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9);
v___x_1627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1625_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
v___x_1628_ = l_Nat_reprFast(v___x_1537_);
v___x_1629_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
v___x_1630_ = l_Lean_MessageData_ofFormat(v___x_1629_);
v___x_1631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1627_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11);
v___x_1633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1631_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1617_, v___x_1633_, v___y_1495_, v___y_1496_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_dec_ref_known(v___x_1634_, 1);
goto v___jp_1527_;
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
lean_del_object(v___x_1507_);
lean_dec(v_snd_1505_);
lean_dec(v_fst_1504_);
lean_dec(v_cmd_1488_);
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
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
lean_object* v___x_1645_; 
lean_dec(v_endPos_1511_);
lean_del_object(v___x_1502_);
v___x_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1645_, 0, v_fst_1504_);
lean_ctor_set(v___x_1645_, 1, v_snd_1505_);
v_a_1516_ = v___x_1645_;
goto v___jp_1515_;
}
}
}
else
{
lean_object* v___x_1646_; 
lean_dec(v_endPos_1511_);
lean_del_object(v___x_1502_);
v___x_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1646_, 0, v_fst_1504_);
lean_ctor_set(v___x_1646_, 1, v_snd_1505_);
v_a_1516_ = v___x_1646_;
goto v___jp_1515_;
}
v___jp_1515_:
{
lean_object* v___x_1518_; 
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 1, v_a_1516_);
lean_ctor_set(v___x_1507_, 0, v___x_1514_);
v___x_1518_ = v___x_1507_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_a_1516_);
v___x_1518_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
size_t v___x_1519_; size_t v___x_1520_; lean_object* v___x_1521_; 
v___x_1519_ = ((size_t)1ULL);
v___x_1520_ = lean_usize_add(v_i_1493_, v___x_1519_);
v___x_1521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12(v___x_1486_, v_val_1487_, v_cmd_1488_, v_onUnsolved_1489_, v___y_1490_, v_as_1491_, v_sz_1492_, v___x_1520_, v___x_1518_, v___y_1495_, v___y_1496_);
return v___x_1521_;
}
}
v___jp_1523_:
{
lean_object* v___x_1525_; 
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 1, v_snd_1505_);
lean_ctor_set(v___x_1502_, 0, v_fst_1504_);
v___x_1525_ = v___x_1502_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_fst_1504_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v_snd_1505_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
v_a_1516_ = v___x_1525_;
goto v___jp_1515_;
}
}
v___jp_1527_:
{
lean_object* v___x_1528_; 
v___x_1528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1528_, 0, v_fst_1504_);
lean_ctor_set(v___x_1528_, 1, v_snd_1505_);
v_a_1516_ = v___x_1528_;
goto v___jp_1515_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___boxed(lean_object* v___x_1650_, lean_object* v_val_1651_, lean_object* v_cmd_1652_, lean_object* v_onUnsolved_1653_, lean_object* v___y_1654_, lean_object* v_as_1655_, lean_object* v_sz_1656_, lean_object* v_i_1657_, lean_object* v_b_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
uint8_t v_onUnsolved_boxed_1662_; uint8_t v___y_15303__boxed_1663_; size_t v_sz_boxed_1664_; size_t v_i_boxed_1665_; lean_object* v_res_1666_; 
v_onUnsolved_boxed_1662_ = lean_unbox(v_onUnsolved_1653_);
v___y_15303__boxed_1663_ = lean_unbox(v___y_1654_);
v_sz_boxed_1664_ = lean_unbox_usize(v_sz_1656_);
lean_dec(v_sz_1656_);
v_i_boxed_1665_ = lean_unbox_usize(v_i_1657_);
lean_dec(v_i_1657_);
v_res_1666_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8(v___x_1650_, v_val_1651_, v_cmd_1652_, v_onUnsolved_boxed_1662_, v___y_15303__boxed_1663_, v_as_1655_, v_sz_boxed_1664_, v_i_boxed_1665_, v_b_1658_, v___y_1659_, v___y_1660_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec_ref(v_as_1655_);
lean_dec_ref(v_val_1651_);
lean_dec_ref(v___x_1650_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10_spec__12(lean_object* v___x_1667_, lean_object* v_val_1668_, lean_object* v_cmd_1669_, uint8_t v_onUnsolved_1670_, uint8_t v___y_1671_, lean_object* v_as_1672_, size_t v_sz_1673_, size_t v_i_1674_, lean_object* v_b_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
uint8_t v___x_1679_; 
v___x_1679_ = lean_usize_dec_lt(v_i_1674_, v_sz_1673_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; 
lean_dec(v_cmd_1669_);
v___x_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1680_, 0, v_b_1675_);
return v___x_1680_;
}
else
{
lean_object* v_snd_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1829_; 
v_snd_1681_ = lean_ctor_get(v_b_1675_, 1);
v_isSharedCheck_1829_ = !lean_is_exclusive(v_b_1675_);
if (v_isSharedCheck_1829_ == 0)
{
lean_object* v_unused_1830_; 
v_unused_1830_ = lean_ctor_get(v_b_1675_, 0);
lean_dec(v_unused_1830_);
v___x_1683_ = v_b_1675_;
v_isShared_1684_ = v_isSharedCheck_1829_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_snd_1681_);
lean_dec(v_b_1675_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1829_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v_fst_1685_; lean_object* v_snd_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1828_; 
v_fst_1685_ = lean_ctor_get(v_snd_1681_, 0);
v_snd_1686_ = lean_ctor_get(v_snd_1681_, 1);
v_isSharedCheck_1828_ = !lean_is_exclusive(v_snd_1681_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1688_ = v_snd_1681_;
v_isShared_1689_ = v_isSharedCheck_1828_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_snd_1686_);
lean_inc(v_fst_1685_);
lean_dec(v_snd_1681_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1828_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v_a_1690_; lean_object* v_pos_1691_; lean_object* v_endPos_1692_; uint8_t v_severity_1693_; lean_object* v_data_1694_; lean_object* v___x_1695_; lean_object* v_a_1697_; 
v_a_1690_ = lean_array_uget_borrowed(v_as_1672_, v_i_1674_);
v_pos_1691_ = lean_ctor_get(v_a_1690_, 1);
v_endPos_1692_ = lean_ctor_get(v_a_1690_, 2);
lean_inc(v_endPos_1692_);
v_severity_1693_ = lean_ctor_get_uint8(v_a_1690_, sizeof(void*)*5 + 1);
v_data_1694_ = lean_ctor_get(v_a_1690_, 4);
v___x_1695_ = lean_box(0);
if (v_severity_1693_ == 2)
{
lean_object* v___f_1710_; uint8_t v___x_1711_; 
v___f_1710_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
lean_inc(v_data_1694_);
v___x_1711_ = l_Lean_MessageData_hasTag(v___f_1710_, v_data_1694_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; 
lean_dec(v_endPos_1692_);
lean_del_object(v___x_1683_);
v___x_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1712_, 0, v_fst_1685_);
lean_ctor_set(v___x_1712_, 1, v_snd_1686_);
v_a_1697_ = v___x_1712_;
goto v___jp_1696_;
}
else
{
if (lean_obj_tag(v_endPos_1692_) == 1)
{
lean_object* v_val_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1825_; 
v_val_1713_ = lean_ctor_get(v_endPos_1692_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v_endPos_1692_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1715_ = v_endPos_1692_;
v_isShared_1716_ = v_isSharedCheck_1825_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_val_1713_);
lean_dec(v_endPos_1692_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1825_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; uint8_t v___x_1720_; uint8_t v___x_1721_; 
lean_inc_ref(v_pos_1691_);
v___x_1717_ = l_Lean_FileMap_ofPosition(v___x_1667_, v_pos_1691_);
v___x_1718_ = l_Lean_FileMap_ofPosition(v___x_1667_, v_val_1713_);
lean_inc(v___x_1718_);
lean_inc(v___x_1717_);
v___x_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1717_);
lean_ctor_set(v___x_1719_, 1, v___x_1718_);
v___x_1720_ = 0;
v___x_1721_ = l_Lean_Syntax_Range_includes(v_val_1668_, v___x_1719_, v___x_1720_, v___x_1720_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1722_; 
lean_dec_ref_known(v___x_1719_, 2);
lean_dec(v___x_1718_);
lean_dec(v___x_1717_);
lean_del_object(v___x_1715_);
lean_del_object(v___x_1683_);
v___x_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1722_, 0, v_fst_1685_);
lean_ctor_set(v___x_1722_, 1, v_snd_1686_);
v_a_1697_ = v___x_1722_;
goto v___jp_1696_;
}
else
{
lean_object* v___x_1723_; 
lean_inc(v_cmd_1669_);
lean_inc_ref(v___x_1719_);
v___x_1723_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1719_, v_cmd_1669_);
if (lean_obj_tag(v___x_1723_) == 1)
{
lean_object* v_val_1724_; lean_object* v_fst_1725_; lean_object* v_snd_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1789_; 
lean_dec(v___x_1718_);
lean_dec(v___x_1717_);
lean_del_object(v___x_1715_);
v_val_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_val_1724_);
lean_dec_ref_known(v___x_1723_, 1);
v_fst_1725_ = lean_ctor_get(v_val_1724_, 0);
v_snd_1726_ = lean_ctor_get(v_val_1724_, 1);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_val_1724_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1728_ = v_val_1724_;
v_isShared_1729_ = v_isSharedCheck_1789_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_snd_1726_);
lean_inc(v_fst_1725_);
lean_dec(v_val_1724_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1789_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; uint8_t v___y_1787_; lean_object* v___x_1788_; 
v___x_1788_ = l_Lean_Syntax_getPos_x3f(v_fst_1725_, v___x_1720_);
if (lean_obj_tag(v___x_1788_) == 0)
{
v___y_1787_ = v___x_1721_;
goto v___jp_1786_;
}
else
{
lean_dec_ref_known(v___x_1788_, 1);
v___y_1787_ = v___x_1720_;
goto v___jp_1786_;
}
v___jp_1730_:
{
lean_object* v___x_1736_; 
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 1, v_snd_1686_);
lean_ctor_set(v___x_1728_, 0, v_fst_1685_);
v___x_1736_ = v___x_1728_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_fst_1685_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_snd_1686_);
v___x_1736_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
size_t v_sz_1737_; size_t v___x_1738_; lean_object* v___x_1739_; 
v_sz_1737_ = lean_array_size(v___y_1732_);
v___x_1738_ = ((size_t)0ULL);
v___x_1739_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1719_, v_fst_1725_, v_snd_1726_, v___y_1731_, v___y_1732_, v_sz_1737_, v___x_1738_, v___x_1736_);
lean_dec_ref(v___y_1732_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v_fst_1741_; lean_object* v_snd_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___x_1739_, 1);
v_fst_1741_ = lean_ctor_get(v_a_1740_, 0);
v_snd_1742_ = lean_ctor_get(v_a_1740_, 1);
v_isSharedCheck_1749_ = !lean_is_exclusive(v_a_1740_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v_a_1740_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_snd_1742_);
lean_inc(v_fst_1741_);
lean_dec(v_a_1740_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_fst_1741_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v_snd_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
v_a_1697_ = v___x_1747_;
goto v___jp_1696_;
}
}
}
else
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
lean_del_object(v___x_1688_);
lean_dec(v_cmd_1669_);
v_a_1750_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1739_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1739_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1750_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
}
v___jp_1759_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
lean_inc_ref(v___x_1719_);
v___x_1760_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1719_);
v___x_1761_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1694_);
v___x_1762_ = lean_array_get_size(v___x_1761_);
v___x_1763_ = lean_unsigned_to_nat(0u);
v___x_1764_ = lean_nat_dec_eq(v___x_1762_, v___x_1763_);
if (v___x_1764_ == 0)
{
v___y_1731_ = v___x_1760_;
v___y_1732_ = v___x_1761_;
v___y_1733_ = v___y_1676_;
v___y_1734_ = v___y_1677_;
goto v___jp_1730_;
}
else
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v_scopes_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v_opts_1771_; uint8_t v_hasTrace_1772_; 
v___x_1765_ = l_Lean_inheritedTraceOptions;
v___x_1766_ = lean_st_ref_get(v___x_1765_);
v___x_1767_ = lean_st_ref_get(v___y_1677_);
v_scopes_1768_ = lean_ctor_get(v___x_1767_, 2);
lean_inc(v_scopes_1768_);
lean_dec(v___x_1767_);
v___x_1769_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1770_ = l_List_head_x21___redArg(v___x_1769_, v_scopes_1768_);
lean_dec(v_scopes_1768_);
v_opts_1771_ = lean_ctor_get(v___x_1770_, 1);
lean_inc_ref(v_opts_1771_);
lean_dec(v___x_1770_);
v_hasTrace_1772_ = lean_ctor_get_uint8(v_opts_1771_, sizeof(void*)*1);
if (v_hasTrace_1772_ == 0)
{
lean_dec_ref(v_opts_1771_);
lean_dec(v___x_1766_);
v___y_1731_ = v___x_1760_;
v___y_1732_ = v___x_1761_;
v___y_1733_ = v___y_1676_;
v___y_1734_ = v___y_1677_;
goto v___jp_1730_;
}
else
{
lean_object* v___x_1773_; lean_object* v___x_1774_; uint8_t v___x_1775_; 
v___x_1773_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1774_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1775_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1766_, v_opts_1771_, v___x_1774_);
lean_dec_ref(v_opts_1771_);
lean_dec(v___x_1766_);
if (v___x_1775_ == 0)
{
v___y_1731_ = v___x_1760_;
v___y_1732_ = v___x_1761_;
v___y_1733_ = v___y_1676_;
v___y_1734_ = v___y_1677_;
goto v___jp_1730_;
}
else
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5);
v___x_1777_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1773_, v___x_1776_, v___y_1676_, v___y_1677_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_dec_ref_known(v___x_1777_, 1);
v___y_1731_ = v___x_1760_;
v___y_1732_ = v___x_1761_;
v___y_1733_ = v___y_1676_;
v___y_1734_ = v___y_1677_;
goto v___jp_1730_;
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_dec_ref(v___x_1761_);
lean_dec(v___x_1760_);
lean_del_object(v___x_1728_);
lean_dec(v_snd_1726_);
lean_dec(v_fst_1725_);
lean_dec_ref_known(v___x_1719_, 2);
lean_del_object(v___x_1688_);
lean_dec(v_snd_1686_);
lean_dec(v_fst_1685_);
lean_dec(v_cmd_1669_);
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1777_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
}
}
}
v___jp_1786_:
{
if (v_onUnsolved_1670_ == 0)
{
if (v___y_1671_ == 0)
{
lean_del_object(v___x_1728_);
lean_dec(v_snd_1726_);
lean_dec(v_fst_1725_);
lean_dec_ref_known(v___x_1719_, 2);
goto v___jp_1704_;
}
else
{
if (v___y_1787_ == 0)
{
lean_del_object(v___x_1728_);
lean_dec(v_snd_1726_);
lean_dec(v_fst_1725_);
lean_dec_ref_known(v___x_1719_, 2);
goto v___jp_1704_;
}
else
{
lean_del_object(v___x_1683_);
goto v___jp_1759_;
}
}
}
else
{
lean_del_object(v___x_1683_);
goto v___jp_1759_;
}
}
}
}
else
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v_scopes_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v_opts_1796_; uint8_t v_hasTrace_1797_; 
lean_dec(v___x_1723_);
lean_dec_ref_known(v___x_1719_, 2);
lean_del_object(v___x_1683_);
v___x_1790_ = l_Lean_inheritedTraceOptions;
v___x_1791_ = lean_st_ref_get(v___x_1790_);
v___x_1792_ = lean_st_ref_get(v___y_1677_);
v_scopes_1793_ = lean_ctor_get(v___x_1792_, 2);
lean_inc(v_scopes_1793_);
lean_dec(v___x_1792_);
v___x_1794_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1795_ = l_List_head_x21___redArg(v___x_1794_, v_scopes_1793_);
lean_dec(v_scopes_1793_);
v_opts_1796_ = lean_ctor_get(v___x_1795_, 1);
lean_inc_ref(v_opts_1796_);
lean_dec(v___x_1795_);
v_hasTrace_1797_ = lean_ctor_get_uint8(v_opts_1796_, sizeof(void*)*1);
if (v_hasTrace_1797_ == 0)
{
lean_dec_ref(v_opts_1796_);
lean_dec(v___x_1791_);
lean_dec(v___x_1718_);
lean_dec(v___x_1717_);
lean_del_object(v___x_1715_);
goto v___jp_1708_;
}
else
{
lean_object* v___x_1798_; lean_object* v___x_1799_; uint8_t v___x_1800_; 
v___x_1798_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1799_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1800_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1791_, v_opts_1796_, v___x_1799_);
lean_dec_ref(v_opts_1796_);
lean_dec(v___x_1791_);
if (v___x_1800_ == 0)
{
lean_dec(v___x_1718_);
lean_dec(v___x_1717_);
lean_del_object(v___x_1715_);
goto v___jp_1708_;
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1804_; 
v___x_1801_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7);
v___x_1802_ = l_Nat_reprFast(v___x_1717_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set_tag(v___x_1715_, 3);
lean_ctor_set(v___x_1715_, 0, v___x_1802_);
v___x_1804_ = v___x_1715_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1805_ = l_Lean_MessageData_ofFormat(v___x_1804_);
v___x_1806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1801_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v___x_1807_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9);
v___x_1808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1806_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
v___x_1809_ = l_Nat_reprFast(v___x_1718_);
v___x_1810_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
v___x_1811_ = l_Lean_MessageData_ofFormat(v___x_1810_);
v___x_1812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1808_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11);
v___x_1814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1812_);
lean_ctor_set(v___x_1814_, 1, v___x_1813_);
v___x_1815_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1798_, v___x_1814_, v___y_1676_, v___y_1677_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_dec_ref_known(v___x_1815_, 1);
goto v___jp_1708_;
}
else
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
lean_del_object(v___x_1688_);
lean_dec(v_snd_1686_);
lean_dec(v_fst_1685_);
lean_dec(v_cmd_1669_);
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1818_ = v___x_1815_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1816_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
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
lean_object* v___x_1826_; 
lean_dec(v_endPos_1692_);
lean_del_object(v___x_1683_);
v___x_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1826_, 0, v_fst_1685_);
lean_ctor_set(v___x_1826_, 1, v_snd_1686_);
v_a_1697_ = v___x_1826_;
goto v___jp_1696_;
}
}
}
else
{
lean_object* v___x_1827_; 
lean_dec(v_endPos_1692_);
lean_del_object(v___x_1683_);
v___x_1827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1827_, 0, v_fst_1685_);
lean_ctor_set(v___x_1827_, 1, v_snd_1686_);
v_a_1697_ = v___x_1827_;
goto v___jp_1696_;
}
v___jp_1696_:
{
lean_object* v___x_1699_; 
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 1, v_a_1697_);
lean_ctor_set(v___x_1688_, 0, v___x_1695_);
v___x_1699_ = v___x_1688_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1695_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v_a_1697_);
v___x_1699_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
size_t v___x_1700_; size_t v___x_1701_; 
v___x_1700_ = ((size_t)1ULL);
v___x_1701_ = lean_usize_add(v_i_1674_, v___x_1700_);
v_i_1674_ = v___x_1701_;
v_b_1675_ = v___x_1699_;
goto _start;
}
}
v___jp_1704_:
{
lean_object* v___x_1706_; 
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 1, v_snd_1686_);
lean_ctor_set(v___x_1683_, 0, v_fst_1685_);
v___x_1706_ = v___x_1683_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_fst_1685_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_snd_1686_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
v_a_1697_ = v___x_1706_;
goto v___jp_1696_;
}
}
v___jp_1708_:
{
lean_object* v___x_1709_; 
v___x_1709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1709_, 0, v_fst_1685_);
lean_ctor_set(v___x_1709_, 1, v_snd_1686_);
v_a_1697_ = v___x_1709_;
goto v___jp_1696_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10_spec__12___boxed(lean_object* v___x_1831_, lean_object* v_val_1832_, lean_object* v_cmd_1833_, lean_object* v_onUnsolved_1834_, lean_object* v___y_1835_, lean_object* v_as_1836_, lean_object* v_sz_1837_, lean_object* v_i_1838_, lean_object* v_b_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
uint8_t v_onUnsolved_boxed_1843_; uint8_t v___y_15635__boxed_1844_; size_t v_sz_boxed_1845_; size_t v_i_boxed_1846_; lean_object* v_res_1847_; 
v_onUnsolved_boxed_1843_ = lean_unbox(v_onUnsolved_1834_);
v___y_15635__boxed_1844_ = lean_unbox(v___y_1835_);
v_sz_boxed_1845_ = lean_unbox_usize(v_sz_1837_);
lean_dec(v_sz_1837_);
v_i_boxed_1846_ = lean_unbox_usize(v_i_1838_);
lean_dec(v_i_1838_);
v_res_1847_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10_spec__12(v___x_1831_, v_val_1832_, v_cmd_1833_, v_onUnsolved_boxed_1843_, v___y_15635__boxed_1844_, v_as_1836_, v_sz_boxed_1845_, v_i_boxed_1846_, v_b_1839_, v___y_1840_, v___y_1841_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec_ref(v_as_1836_);
lean_dec_ref(v_val_1832_);
lean_dec_ref(v___x_1831_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10(lean_object* v___x_1848_, lean_object* v_val_1849_, lean_object* v_cmd_1850_, uint8_t v_onUnsolved_1851_, uint8_t v___y_1852_, lean_object* v_as_1853_, size_t v_sz_1854_, size_t v_i_1855_, lean_object* v_b_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
uint8_t v___x_1860_; 
v___x_1860_ = lean_usize_dec_lt(v_i_1855_, v_sz_1854_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; 
lean_dec(v_cmd_1850_);
v___x_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1861_, 0, v_b_1856_);
return v___x_1861_;
}
else
{
lean_object* v_snd_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_2010_; 
v_snd_1862_ = lean_ctor_get(v_b_1856_, 1);
v_isSharedCheck_2010_ = !lean_is_exclusive(v_b_1856_);
if (v_isSharedCheck_2010_ == 0)
{
lean_object* v_unused_2011_; 
v_unused_2011_ = lean_ctor_get(v_b_1856_, 0);
lean_dec(v_unused_2011_);
v___x_1864_ = v_b_1856_;
v_isShared_1865_ = v_isSharedCheck_2010_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_snd_1862_);
lean_dec(v_b_1856_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_2010_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v_fst_1866_; lean_object* v_snd_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_2009_; 
v_fst_1866_ = lean_ctor_get(v_snd_1862_, 0);
v_snd_1867_ = lean_ctor_get(v_snd_1862_, 1);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_snd_1862_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_1869_ = v_snd_1862_;
v_isShared_1870_ = v_isSharedCheck_2009_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_snd_1867_);
lean_inc(v_fst_1866_);
lean_dec(v_snd_1862_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_2009_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v_a_1871_; lean_object* v_pos_1872_; lean_object* v_endPos_1873_; uint8_t v_severity_1874_; lean_object* v_data_1875_; lean_object* v___x_1876_; lean_object* v_a_1878_; 
v_a_1871_ = lean_array_uget_borrowed(v_as_1853_, v_i_1855_);
v_pos_1872_ = lean_ctor_get(v_a_1871_, 1);
v_endPos_1873_ = lean_ctor_get(v_a_1871_, 2);
lean_inc(v_endPos_1873_);
v_severity_1874_ = lean_ctor_get_uint8(v_a_1871_, sizeof(void*)*5 + 1);
v_data_1875_ = lean_ctor_get(v_a_1871_, 4);
v___x_1876_ = lean_box(0);
if (v_severity_1874_ == 2)
{
lean_object* v___f_1891_; uint8_t v___x_1892_; 
v___f_1891_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
lean_inc(v_data_1875_);
v___x_1892_ = l_Lean_MessageData_hasTag(v___f_1891_, v_data_1875_);
if (v___x_1892_ == 0)
{
lean_object* v___x_1893_; 
lean_dec(v_endPos_1873_);
lean_del_object(v___x_1864_);
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v_fst_1866_);
lean_ctor_set(v___x_1893_, 1, v_snd_1867_);
v_a_1878_ = v___x_1893_;
goto v___jp_1877_;
}
else
{
if (lean_obj_tag(v_endPos_1873_) == 1)
{
lean_object* v_val_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_2006_; 
v_val_1894_ = lean_ctor_get(v_endPos_1873_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v_endPos_1873_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_1896_ = v_endPos_1873_;
v_isShared_1897_ = v_isSharedCheck_2006_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_val_1894_);
lean_dec(v_endPos_1873_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_2006_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; uint8_t v___x_1901_; uint8_t v___x_1902_; 
lean_inc_ref(v_pos_1872_);
v___x_1898_ = l_Lean_FileMap_ofPosition(v___x_1848_, v_pos_1872_);
v___x_1899_ = l_Lean_FileMap_ofPosition(v___x_1848_, v_val_1894_);
lean_inc(v___x_1899_);
lean_inc(v___x_1898_);
v___x_1900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1898_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v___x_1901_ = 0;
v___x_1902_ = l_Lean_Syntax_Range_includes(v_val_1849_, v___x_1900_, v___x_1901_, v___x_1901_);
if (v___x_1902_ == 0)
{
lean_object* v___x_1903_; 
lean_dec_ref_known(v___x_1900_, 2);
lean_dec(v___x_1899_);
lean_dec(v___x_1898_);
lean_del_object(v___x_1896_);
lean_del_object(v___x_1864_);
v___x_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1903_, 0, v_fst_1866_);
lean_ctor_set(v___x_1903_, 1, v_snd_1867_);
v_a_1878_ = v___x_1903_;
goto v___jp_1877_;
}
else
{
lean_object* v___x_1904_; 
lean_inc(v_cmd_1850_);
lean_inc_ref(v___x_1900_);
v___x_1904_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1900_, v_cmd_1850_);
if (lean_obj_tag(v___x_1904_) == 1)
{
lean_object* v_val_1905_; lean_object* v_fst_1906_; lean_object* v_snd_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1970_; 
lean_dec(v___x_1899_);
lean_dec(v___x_1898_);
lean_del_object(v___x_1896_);
v_val_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_val_1905_);
lean_dec_ref_known(v___x_1904_, 1);
v_fst_1906_ = lean_ctor_get(v_val_1905_, 0);
v_snd_1907_ = lean_ctor_get(v_val_1905_, 1);
v_isSharedCheck_1970_ = !lean_is_exclusive(v_val_1905_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1909_ = v_val_1905_;
v_isShared_1910_ = v_isSharedCheck_1970_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_snd_1907_);
lean_inc(v_fst_1906_);
lean_dec(v_val_1905_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1970_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; uint8_t v___y_1968_; lean_object* v___x_1969_; 
v___x_1969_ = l_Lean_Syntax_getPos_x3f(v_fst_1906_, v___x_1901_);
if (lean_obj_tag(v___x_1969_) == 0)
{
v___y_1968_ = v___x_1902_;
goto v___jp_1967_;
}
else
{
lean_dec_ref_known(v___x_1969_, 1);
v___y_1968_ = v___x_1901_;
goto v___jp_1967_;
}
v___jp_1911_:
{
lean_object* v___x_1917_; 
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 1, v_snd_1867_);
lean_ctor_set(v___x_1909_, 0, v_fst_1866_);
v___x_1917_ = v___x_1909_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_fst_1866_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_snd_1867_);
v___x_1917_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
size_t v_sz_1918_; size_t v___x_1919_; lean_object* v___x_1920_; 
v_sz_1918_ = lean_array_size(v___y_1913_);
v___x_1919_ = ((size_t)0ULL);
v___x_1920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1900_, v_fst_1906_, v_snd_1907_, v___y_1912_, v___y_1913_, v_sz_1918_, v___x_1919_, v___x_1917_);
lean_dec_ref(v___y_1913_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v_fst_1922_; lean_object* v_snd_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref_known(v___x_1920_, 1);
v_fst_1922_ = lean_ctor_get(v_a_1921_, 0);
v_snd_1923_ = lean_ctor_get(v_a_1921_, 1);
v_isSharedCheck_1930_ = !lean_is_exclusive(v_a_1921_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v_a_1921_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_snd_1923_);
lean_inc(v_fst_1922_);
lean_dec(v_a_1921_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_fst_1922_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v_snd_1923_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
v_a_1878_ = v___x_1928_;
goto v___jp_1877_;
}
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_del_object(v___x_1869_);
lean_dec(v_cmd_1850_);
v_a_1931_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1920_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1920_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
}
v___jp_1940_:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; 
lean_inc_ref(v___x_1900_);
v___x_1941_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1900_);
v___x_1942_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1875_);
v___x_1943_ = lean_array_get_size(v___x_1942_);
v___x_1944_ = lean_unsigned_to_nat(0u);
v___x_1945_ = lean_nat_dec_eq(v___x_1943_, v___x_1944_);
if (v___x_1945_ == 0)
{
v___y_1912_ = v___x_1941_;
v___y_1913_ = v___x_1942_;
v___y_1914_ = v___y_1857_;
v___y_1915_ = v___y_1858_;
goto v___jp_1911_;
}
else
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v_scopes_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v_opts_1952_; uint8_t v_hasTrace_1953_; 
v___x_1946_ = l_Lean_inheritedTraceOptions;
v___x_1947_ = lean_st_ref_get(v___x_1946_);
v___x_1948_ = lean_st_ref_get(v___y_1858_);
v_scopes_1949_ = lean_ctor_get(v___x_1948_, 2);
lean_inc(v_scopes_1949_);
lean_dec(v___x_1948_);
v___x_1950_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1951_ = l_List_head_x21___redArg(v___x_1950_, v_scopes_1949_);
lean_dec(v_scopes_1949_);
v_opts_1952_ = lean_ctor_get(v___x_1951_, 1);
lean_inc_ref(v_opts_1952_);
lean_dec(v___x_1951_);
v_hasTrace_1953_ = lean_ctor_get_uint8(v_opts_1952_, sizeof(void*)*1);
if (v_hasTrace_1953_ == 0)
{
lean_dec_ref(v_opts_1952_);
lean_dec(v___x_1947_);
v___y_1912_ = v___x_1941_;
v___y_1913_ = v___x_1942_;
v___y_1914_ = v___y_1857_;
v___y_1915_ = v___y_1858_;
goto v___jp_1911_;
}
else
{
lean_object* v___x_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; 
v___x_1954_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1955_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1956_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1947_, v_opts_1952_, v___x_1955_);
lean_dec_ref(v_opts_1952_);
lean_dec(v___x_1947_);
if (v___x_1956_ == 0)
{
v___y_1912_ = v___x_1941_;
v___y_1913_ = v___x_1942_;
v___y_1914_ = v___y_1857_;
v___y_1915_ = v___y_1858_;
goto v___jp_1911_;
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5);
v___x_1958_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1954_, v___x_1957_, v___y_1857_, v___y_1858_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_dec_ref_known(v___x_1958_, 1);
v___y_1912_ = v___x_1941_;
v___y_1913_ = v___x_1942_;
v___y_1914_ = v___y_1857_;
v___y_1915_ = v___y_1858_;
goto v___jp_1911_;
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
lean_dec_ref(v___x_1942_);
lean_dec(v___x_1941_);
lean_del_object(v___x_1909_);
lean_dec(v_snd_1907_);
lean_dec(v_fst_1906_);
lean_dec_ref_known(v___x_1900_, 2);
lean_del_object(v___x_1869_);
lean_dec(v_snd_1867_);
lean_dec(v_fst_1866_);
lean_dec(v_cmd_1850_);
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
}
}
}
v___jp_1967_:
{
if (v_onUnsolved_1851_ == 0)
{
if (v___y_1852_ == 0)
{
lean_del_object(v___x_1909_);
lean_dec(v_snd_1907_);
lean_dec(v_fst_1906_);
lean_dec_ref_known(v___x_1900_, 2);
goto v___jp_1885_;
}
else
{
if (v___y_1968_ == 0)
{
lean_del_object(v___x_1909_);
lean_dec(v_snd_1907_);
lean_dec(v_fst_1906_);
lean_dec_ref_known(v___x_1900_, 2);
goto v___jp_1885_;
}
else
{
lean_del_object(v___x_1864_);
goto v___jp_1940_;
}
}
}
else
{
lean_del_object(v___x_1864_);
goto v___jp_1940_;
}
}
}
}
else
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v_scopes_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v_opts_1977_; uint8_t v_hasTrace_1978_; 
lean_dec(v___x_1904_);
lean_dec_ref_known(v___x_1900_, 2);
lean_del_object(v___x_1864_);
v___x_1971_ = l_Lean_inheritedTraceOptions;
v___x_1972_ = lean_st_ref_get(v___x_1971_);
v___x_1973_ = lean_st_ref_get(v___y_1858_);
v_scopes_1974_ = lean_ctor_get(v___x_1973_, 2);
lean_inc(v_scopes_1974_);
lean_dec(v___x_1973_);
v___x_1975_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1976_ = l_List_head_x21___redArg(v___x_1975_, v_scopes_1974_);
lean_dec(v_scopes_1974_);
v_opts_1977_ = lean_ctor_get(v___x_1976_, 1);
lean_inc_ref(v_opts_1977_);
lean_dec(v___x_1976_);
v_hasTrace_1978_ = lean_ctor_get_uint8(v_opts_1977_, sizeof(void*)*1);
if (v_hasTrace_1978_ == 0)
{
lean_dec_ref(v_opts_1977_);
lean_dec(v___x_1972_);
lean_dec(v___x_1899_);
lean_dec(v___x_1898_);
lean_del_object(v___x_1896_);
goto v___jp_1889_;
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; uint8_t v___x_1981_; 
v___x_1979_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1980_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1981_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1972_, v_opts_1977_, v___x_1980_);
lean_dec_ref(v_opts_1977_);
lean_dec(v___x_1972_);
if (v___x_1981_ == 0)
{
lean_dec(v___x_1899_);
lean_dec(v___x_1898_);
lean_del_object(v___x_1896_);
goto v___jp_1889_;
}
else
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1985_; 
v___x_1982_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7);
v___x_1983_ = l_Nat_reprFast(v___x_1898_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set_tag(v___x_1896_, 3);
lean_ctor_set(v___x_1896_, 0, v___x_1983_);
v___x_1985_ = v___x_1896_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_1983_);
v___x_1985_ = v_reuseFailAlloc_2005_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1986_ = l_Lean_MessageData_ofFormat(v___x_1985_);
v___x_1987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1982_);
lean_ctor_set(v___x_1987_, 1, v___x_1986_);
v___x_1988_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9);
v___x_1989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1987_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
v___x_1990_ = l_Nat_reprFast(v___x_1899_);
v___x_1991_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
v___x_1992_ = l_Lean_MessageData_ofFormat(v___x_1991_);
v___x_1993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1989_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___x_1994_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11);
v___x_1995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1993_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
v___x_1996_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1979_, v___x_1995_, v___y_1857_, v___y_1858_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_dec_ref_known(v___x_1996_, 1);
goto v___jp_1889_;
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
lean_del_object(v___x_1869_);
lean_dec(v_snd_1867_);
lean_dec(v_fst_1866_);
lean_dec(v_cmd_1850_);
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1996_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1996_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
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
lean_object* v___x_2007_; 
lean_dec(v_endPos_1873_);
lean_del_object(v___x_1864_);
v___x_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2007_, 0, v_fst_1866_);
lean_ctor_set(v___x_2007_, 1, v_snd_1867_);
v_a_1878_ = v___x_2007_;
goto v___jp_1877_;
}
}
}
else
{
lean_object* v___x_2008_; 
lean_dec(v_endPos_1873_);
lean_del_object(v___x_1864_);
v___x_2008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2008_, 0, v_fst_1866_);
lean_ctor_set(v___x_2008_, 1, v_snd_1867_);
v_a_1878_ = v___x_2008_;
goto v___jp_1877_;
}
v___jp_1877_:
{
lean_object* v___x_1880_; 
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 1, v_a_1878_);
lean_ctor_set(v___x_1869_, 0, v___x_1876_);
v___x_1880_ = v___x_1869_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1876_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v_a_1878_);
v___x_1880_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
size_t v___x_1881_; size_t v___x_1882_; lean_object* v___x_1883_; 
v___x_1881_ = ((size_t)1ULL);
v___x_1882_ = lean_usize_add(v_i_1855_, v___x_1881_);
v___x_1883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10_spec__12(v___x_1848_, v_val_1849_, v_cmd_1850_, v_onUnsolved_1851_, v___y_1852_, v_as_1853_, v_sz_1854_, v___x_1882_, v___x_1880_, v___y_1857_, v___y_1858_);
return v___x_1883_;
}
}
v___jp_1885_:
{
lean_object* v___x_1887_; 
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 1, v_snd_1867_);
lean_ctor_set(v___x_1864_, 0, v_fst_1866_);
v___x_1887_ = v___x_1864_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_fst_1866_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_snd_1867_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
v_a_1878_ = v___x_1887_;
goto v___jp_1877_;
}
}
v___jp_1889_:
{
lean_object* v___x_1890_; 
v___x_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1890_, 0, v_fst_1866_);
lean_ctor_set(v___x_1890_, 1, v_snd_1867_);
v_a_1878_ = v___x_1890_;
goto v___jp_1877_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10___boxed(lean_object* v___x_2012_, lean_object* v_val_2013_, lean_object* v_cmd_2014_, lean_object* v_onUnsolved_2015_, lean_object* v___y_2016_, lean_object* v_as_2017_, lean_object* v_sz_2018_, lean_object* v_i_2019_, lean_object* v_b_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
uint8_t v_onUnsolved_boxed_2024_; uint8_t v___y_15967__boxed_2025_; size_t v_sz_boxed_2026_; size_t v_i_boxed_2027_; lean_object* v_res_2028_; 
v_onUnsolved_boxed_2024_ = lean_unbox(v_onUnsolved_2015_);
v___y_15967__boxed_2025_ = lean_unbox(v___y_2016_);
v_sz_boxed_2026_ = lean_unbox_usize(v_sz_2018_);
lean_dec(v_sz_2018_);
v_i_boxed_2027_ = lean_unbox_usize(v_i_2019_);
lean_dec(v_i_2019_);
v_res_2028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10(v___x_2012_, v_val_2013_, v_cmd_2014_, v_onUnsolved_boxed_2024_, v___y_15967__boxed_2025_, v_as_2017_, v_sz_boxed_2026_, v_i_boxed_2027_, v_b_2020_, v___y_2021_, v___y_2022_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec_ref(v_as_2017_);
lean_dec_ref(v_val_2013_);
lean_dec_ref(v___x_2012_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(lean_object* v_init_2029_, lean_object* v___x_2030_, lean_object* v_val_2031_, lean_object* v_cmd_2032_, uint8_t v_onUnsolved_2033_, uint8_t v___y_2034_, lean_object* v_n_2035_, lean_object* v_b_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
if (lean_obj_tag(v_n_2035_) == 0)
{
lean_object* v_cs_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; size_t v_sz_2043_; size_t v___x_2044_; lean_object* v___x_2045_; 
v_cs_2040_ = lean_ctor_get(v_n_2035_, 0);
v___x_2041_ = lean_box(0);
v___x_2042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2041_);
lean_ctor_set(v___x_2042_, 1, v_b_2036_);
v_sz_2043_ = lean_array_size(v_cs_2040_);
v___x_2044_ = ((size_t)0ULL);
v___x_2045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__9(v_init_2029_, v___x_2030_, v_val_2031_, v_cmd_2032_, v_onUnsolved_2033_, v___y_2034_, v_cs_2040_, v_sz_2043_, v___x_2044_, v___x_2042_, v___y_2037_, v___y_2038_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2060_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2048_ = v___x_2045_;
v_isShared_2049_ = v_isSharedCheck_2060_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2045_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2060_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v_fst_2050_; 
v_fst_2050_ = lean_ctor_get(v_a_2046_, 0);
if (lean_obj_tag(v_fst_2050_) == 0)
{
lean_object* v_snd_2051_; lean_object* v___x_2052_; lean_object* v___x_2054_; 
v_snd_2051_ = lean_ctor_get(v_a_2046_, 1);
lean_inc(v_snd_2051_);
lean_dec(v_a_2046_);
v___x_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2052_, 0, v_snd_2051_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 0, v___x_2052_);
v___x_2054_ = v___x_2048_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
else
{
lean_object* v_val_2056_; lean_object* v___x_2058_; 
lean_inc_ref(v_fst_2050_);
lean_dec(v_a_2046_);
v_val_2056_ = lean_ctor_get(v_fst_2050_, 0);
lean_inc(v_val_2056_);
lean_dec_ref_known(v_fst_2050_, 1);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 0, v_val_2056_);
v___x_2058_ = v___x_2048_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_val_2056_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
v_a_2061_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2045_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2045_);
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
else
{
lean_object* v_vs_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; size_t v_sz_2072_; size_t v___x_2073_; lean_object* v___x_2074_; 
v_vs_2069_ = lean_ctor_get(v_n_2035_, 0);
v___x_2070_ = lean_box(0);
v___x_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
lean_ctor_set(v___x_2071_, 1, v_b_2036_);
v_sz_2072_ = lean_array_size(v_vs_2069_);
v___x_2073_ = ((size_t)0ULL);
v___x_2074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10(v___x_2030_, v_val_2031_, v_cmd_2032_, v_onUnsolved_2033_, v___y_2034_, v_vs_2069_, v_sz_2072_, v___x_2073_, v___x_2071_, v___y_2037_, v___y_2038_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2089_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2077_ = v___x_2074_;
v_isShared_2078_ = v_isSharedCheck_2089_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2074_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2089_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v_fst_2079_; 
v_fst_2079_ = lean_ctor_get(v_a_2075_, 0);
if (lean_obj_tag(v_fst_2079_) == 0)
{
lean_object* v_snd_2080_; lean_object* v___x_2081_; lean_object* v___x_2083_; 
v_snd_2080_ = lean_ctor_get(v_a_2075_, 1);
lean_inc(v_snd_2080_);
lean_dec(v_a_2075_);
v___x_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2081_, 0, v_snd_2080_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 0, v___x_2081_);
v___x_2083_ = v___x_2077_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
else
{
lean_object* v_val_2085_; lean_object* v___x_2087_; 
lean_inc_ref(v_fst_2079_);
lean_dec(v_a_2075_);
v_val_2085_ = lean_ctor_get(v_fst_2079_, 0);
lean_inc(v_val_2085_);
lean_dec_ref_known(v_fst_2079_, 1);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 0, v_val_2085_);
v___x_2087_ = v___x_2077_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_val_2085_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
v_a_2090_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2074_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2074_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__9(lean_object* v_init_2098_, lean_object* v___x_2099_, lean_object* v_val_2100_, lean_object* v_cmd_2101_, uint8_t v_onUnsolved_2102_, uint8_t v___y_2103_, lean_object* v_as_2104_, size_t v_sz_2105_, size_t v_i_2106_, lean_object* v_b_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
uint8_t v___x_2111_; 
v___x_2111_ = lean_usize_dec_lt(v_i_2106_, v_sz_2105_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; 
lean_dec(v_cmd_2101_);
v___x_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2112_, 0, v_b_2107_);
return v___x_2112_;
}
else
{
lean_object* v_snd_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2147_; 
v_snd_2113_ = lean_ctor_get(v_b_2107_, 1);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_b_2107_);
if (v_isSharedCheck_2147_ == 0)
{
lean_object* v_unused_2148_; 
v_unused_2148_ = lean_ctor_get(v_b_2107_, 0);
lean_dec(v_unused_2148_);
v___x_2115_ = v_b_2107_;
v_isShared_2116_ = v_isSharedCheck_2147_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_snd_2113_);
lean_dec(v_b_2107_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2147_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v_a_2117_; lean_object* v___x_2118_; 
v_a_2117_ = lean_array_uget_borrowed(v_as_2104_, v_i_2106_);
lean_inc(v_snd_2113_);
lean_inc(v_cmd_2101_);
v___x_2118_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(v_init_2098_, v___x_2099_, v_val_2100_, v_cmd_2101_, v_onUnsolved_2102_, v___y_2103_, v_a_2117_, v_snd_2113_, v___y_2108_, v___y_2109_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2138_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2121_ = v___x_2118_;
v_isShared_2122_ = v_isSharedCheck_2138_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2138_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
if (lean_obj_tag(v_a_2119_) == 0)
{
lean_object* v___x_2123_; lean_object* v___x_2125_; 
lean_dec(v_cmd_2101_);
v___x_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2123_, 0, v_a_2119_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v___x_2123_);
v___x_2125_ = v___x_2115_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2123_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_snd_2113_);
v___x_2125_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
lean_object* v___x_2127_; 
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2125_);
v___x_2127_ = v___x_2121_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2125_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2131_; lean_object* v___x_2133_; 
lean_del_object(v___x_2121_);
lean_dec(v_snd_2113_);
v_a_2130_ = lean_ctor_get(v_a_2119_, 0);
lean_inc(v_a_2130_);
lean_dec_ref_known(v_a_2119_, 1);
v___x_2131_ = lean_box(0);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 1, v_a_2130_);
lean_ctor_set(v___x_2115_, 0, v___x_2131_);
v___x_2133_ = v___x_2115_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2131_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v_a_2130_);
v___x_2133_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
size_t v___x_2134_; size_t v___x_2135_; 
v___x_2134_ = ((size_t)1ULL);
v___x_2135_ = lean_usize_add(v_i_2106_, v___x_2134_);
v_i_2106_ = v___x_2135_;
v_b_2107_ = v___x_2133_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
lean_del_object(v___x_2115_);
lean_dec(v_snd_2113_);
lean_dec(v_cmd_2101_);
v_a_2139_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2141_ = v___x_2118_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2118_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__9___boxed(lean_object* v_init_2149_, lean_object* v___x_2150_, lean_object* v_val_2151_, lean_object* v_cmd_2152_, lean_object* v_onUnsolved_2153_, lean_object* v___y_2154_, lean_object* v_as_2155_, lean_object* v_sz_2156_, lean_object* v_i_2157_, lean_object* v_b_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
uint8_t v_onUnsolved_boxed_2162_; uint8_t v___y_16268__boxed_2163_; size_t v_sz_boxed_2164_; size_t v_i_boxed_2165_; lean_object* v_res_2166_; 
v_onUnsolved_boxed_2162_ = lean_unbox(v_onUnsolved_2153_);
v___y_16268__boxed_2163_ = lean_unbox(v___y_2154_);
v_sz_boxed_2164_ = lean_unbox_usize(v_sz_2156_);
lean_dec(v_sz_2156_);
v_i_boxed_2165_ = lean_unbox_usize(v_i_2157_);
lean_dec(v_i_2157_);
v_res_2166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__9(v_init_2149_, v___x_2150_, v_val_2151_, v_cmd_2152_, v_onUnsolved_boxed_2162_, v___y_16268__boxed_2163_, v_as_2155_, v_sz_boxed_2164_, v_i_boxed_2165_, v_b_2158_, v___y_2159_, v___y_2160_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec_ref(v_as_2155_);
lean_dec_ref(v_val_2151_);
lean_dec_ref(v___x_2150_);
lean_dec_ref(v_init_2149_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___boxed(lean_object* v_init_2167_, lean_object* v___x_2168_, lean_object* v_val_2169_, lean_object* v_cmd_2170_, lean_object* v_onUnsolved_2171_, lean_object* v___y_2172_, lean_object* v_n_2173_, lean_object* v_b_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
uint8_t v_onUnsolved_boxed_2178_; uint8_t v___y_16290__boxed_2179_; lean_object* v_res_2180_; 
v_onUnsolved_boxed_2178_ = lean_unbox(v_onUnsolved_2171_);
v___y_16290__boxed_2179_ = lean_unbox(v___y_2172_);
v_res_2180_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(v_init_2167_, v___x_2168_, v_val_2169_, v_cmd_2170_, v_onUnsolved_boxed_2178_, v___y_16290__boxed_2179_, v_n_2173_, v_b_2174_, v___y_2175_, v___y_2176_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec_ref(v_n_2173_);
lean_dec_ref(v_val_2169_);
lean_dec_ref(v___x_2168_);
lean_dec_ref(v_init_2167_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(lean_object* v___x_2181_, lean_object* v_val_2182_, lean_object* v_cmd_2183_, uint8_t v_onUnsolved_2184_, uint8_t v___y_2185_, lean_object* v_t_2186_, lean_object* v_init_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v_root_2191_; lean_object* v_tail_2192_; lean_object* v___x_2193_; 
v_root_2191_ = lean_ctor_get(v_t_2186_, 0);
v_tail_2192_ = lean_ctor_get(v_t_2186_, 1);
lean_inc(v_cmd_2183_);
lean_inc_ref(v_init_2187_);
v___x_2193_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(v_init_2187_, v___x_2181_, v_val_2182_, v_cmd_2183_, v_onUnsolved_2184_, v___y_2185_, v_root_2191_, v_init_2187_, v___y_2188_, v___y_2189_);
lean_dec_ref(v_init_2187_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2230_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2196_ = v___x_2193_;
v_isShared_2197_ = v_isSharedCheck_2230_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2193_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2230_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
if (lean_obj_tag(v_a_2194_) == 0)
{
lean_object* v_a_2198_; lean_object* v___x_2200_; 
lean_dec(v_cmd_2183_);
v_a_2198_ = lean_ctor_get(v_a_2194_, 0);
lean_inc(v_a_2198_);
lean_dec_ref_known(v_a_2194_, 1);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 0, v_a_2198_);
v___x_2200_ = v___x_2196_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_a_2198_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; size_t v_sz_2205_; size_t v___x_2206_; lean_object* v___x_2207_; 
lean_del_object(v___x_2196_);
v_a_2202_ = lean_ctor_get(v_a_2194_, 0);
lean_inc(v_a_2202_);
lean_dec_ref_known(v_a_2194_, 1);
v___x_2203_ = lean_box(0);
v___x_2204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
lean_ctor_set(v___x_2204_, 1, v_a_2202_);
v_sz_2205_ = lean_array_size(v_tail_2192_);
v___x_2206_ = ((size_t)0ULL);
v___x_2207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8(v___x_2181_, v_val_2182_, v_cmd_2183_, v_onUnsolved_2184_, v___y_2185_, v_tail_2192_, v_sz_2205_, v___x_2206_, v___x_2204_, v___y_2188_, v___y_2189_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2221_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2210_ = v___x_2207_;
v_isShared_2211_ = v_isSharedCheck_2221_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2207_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2221_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v_fst_2212_; 
v_fst_2212_ = lean_ctor_get(v_a_2208_, 0);
if (lean_obj_tag(v_fst_2212_) == 0)
{
lean_object* v_snd_2213_; lean_object* v___x_2215_; 
v_snd_2213_ = lean_ctor_get(v_a_2208_, 1);
lean_inc(v_snd_2213_);
lean_dec(v_a_2208_);
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 0, v_snd_2213_);
v___x_2215_ = v___x_2210_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_snd_2213_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
else
{
lean_object* v_val_2217_; lean_object* v___x_2219_; 
lean_inc_ref(v_fst_2212_);
lean_dec(v_a_2208_);
v_val_2217_ = lean_ctor_get(v_fst_2212_, 0);
lean_inc(v_val_2217_);
lean_dec_ref_known(v_fst_2212_, 1);
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 0, v_val_2217_);
v___x_2219_ = v___x_2210_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_val_2217_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
v_a_2222_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2207_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2207_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_dec(v_cmd_2183_);
v_a_2231_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2193_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2193_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___boxed(lean_object* v___x_2239_, lean_object* v_val_2240_, lean_object* v_cmd_2241_, lean_object* v_onUnsolved_2242_, lean_object* v___y_2243_, lean_object* v_t_2244_, lean_object* v_init_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
uint8_t v_onUnsolved_boxed_2249_; uint8_t v___y_16481__boxed_2250_; lean_object* v_res_2251_; 
v_onUnsolved_boxed_2249_ = lean_unbox(v_onUnsolved_2242_);
v___y_16481__boxed_2250_ = lean_unbox(v___y_2243_);
v_res_2251_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_2239_, v_val_2240_, v_cmd_2241_, v_onUnsolved_boxed_2249_, v___y_16481__boxed_2250_, v_t_2244_, v_init_2245_, v___y_2246_, v___y_2247_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec_ref(v_t_2244_);
lean_dec_ref(v_val_2240_);
lean_dec_ref(v___x_2239_);
return v_res_2251_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0(void){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2252_ = lean_box(0);
v___x_2253_ = lean_unsigned_to_nat(16u);
v___x_2254_ = lean_mk_array(v___x_2253_, v___x_2252_);
return v___x_2254_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1(void){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2255_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0);
v___x_2256_ = lean_unsigned_to_nat(0u);
v___x_2257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
lean_ctor_set(v___x_2257_, 1, v___x_2255_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(lean_object* v_cmd_2261_, lean_object* v_opts_2262_, lean_object* v_tree_2263_, lean_object* v_msgs_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_){
_start:
{
lean_object* v___y_2269_; lean_object* v___y_2270_; uint8_t v___y_2271_; lean_object* v___y_2272_; uint8_t v___y_2273_; uint8_t v___y_2274_; uint8_t v___y_2300_; uint8_t v___y_2301_; lean_object* v_acc_2302_; lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v___f_2306_; uint8_t v___y_2308_; lean_object* v___x_2315_; uint8_t v___x_2316_; 
v___f_2306_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__2));
v___x_2315_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_2316_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2262_, v___x_2315_);
if (v___x_2316_ == 0)
{
lean_object* v___x_2317_; uint8_t v___x_2318_; 
v___x_2317_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_2318_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2262_, v___x_2317_);
v___y_2308_ = v___x_2318_;
goto v___jp_2307_;
}
else
{
v___y_2308_ = v___x_2316_;
goto v___jp_2307_;
}
v___jp_2268_:
{
lean_object* v___x_2275_; 
v___x_2275_ = l_Lean_Syntax_getRange_x3f(v_cmd_2261_, v___y_2274_);
if (lean_obj_tag(v___x_2275_) == 1)
{
lean_object* v_val_2276_; lean_object* v_fileMap_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v_val_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_val_2276_);
lean_dec_ref_known(v___x_2275_, 1);
v_fileMap_2277_ = lean_ctor_get(v___y_2269_, 1);
v___x_2278_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1);
v___x_2279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2279_, 0, v___y_2270_);
lean_ctor_set(v___x_2279_, 1, v___x_2278_);
v___x_2280_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v_fileMap_2277_, v_val_2276_, v_cmd_2261_, v___y_2271_, v___y_2273_, v_msgs_2264_, v___x_2279_, v___y_2269_, v___y_2272_);
lean_dec(v_val_2276_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2289_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2283_ = v___x_2280_;
v_isShared_2284_ = v_isSharedCheck_2289_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2280_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2289_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v_fst_2285_; lean_object* v___x_2287_; 
v_fst_2285_ = lean_ctor_get(v_a_2281_, 0);
lean_inc(v_fst_2285_);
lean_dec(v_a_2281_);
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 0, v_fst_2285_);
v___x_2287_ = v___x_2283_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_fst_2285_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
v_a_2290_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2280_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2280_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
else
{
lean_object* v___x_2298_; 
lean_dec(v___x_2275_);
lean_dec(v_cmd_2261_);
v___x_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2298_, 0, v___y_2270_);
return v___x_2298_;
}
}
v___jp_2299_:
{
if (v___y_2300_ == 0)
{
if (v___y_2301_ == 0)
{
lean_object* v___x_2305_; 
lean_dec(v_cmd_2261_);
v___x_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2305_, 0, v_acc_2302_);
return v___x_2305_;
}
else
{
v___y_2269_ = v___y_2303_;
v___y_2270_ = v_acc_2302_;
v___y_2271_ = v___y_2300_;
v___y_2272_ = v___y_2304_;
v___y_2273_ = v___y_2301_;
v___y_2274_ = v___y_2301_;
goto v___jp_2268_;
}
}
else
{
v___y_2269_ = v___y_2303_;
v___y_2270_ = v_acc_2302_;
v___y_2271_ = v___y_2300_;
v___y_2272_ = v___y_2304_;
v___y_2273_ = v___y_2301_;
v___y_2274_ = v___y_2300_;
goto v___jp_2268_;
}
}
v___jp_2307_:
{
lean_object* v___x_2309_; uint8_t v_onUnsolved_2310_; lean_object* v___x_2311_; uint8_t v_onSorry_2312_; lean_object* v_acc_2313_; 
v___x_2309_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
v_onUnsolved_2310_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2262_, v___x_2309_);
v___x_2311_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v_onSorry_2312_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2262_, v___x_2311_);
v_acc_2313_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__3));
if (v_onSorry_2312_ == 0)
{
lean_dec_ref(v_tree_2263_);
v___y_2300_ = v_onUnsolved_2310_;
v___y_2301_ = v___y_2308_;
v_acc_2302_ = v_acc_2313_;
v___y_2303_ = v_a_2265_;
v___y_2304_ = v_a_2266_;
goto v___jp_2299_;
}
else
{
lean_object* v_acc_2314_; 
v_acc_2314_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_2306_, v_acc_2313_, v_tree_2263_);
v___y_2300_ = v_onUnsolved_2310_;
v___y_2301_ = v___y_2308_;
v_acc_2302_ = v_acc_2314_;
v___y_2303_ = v_a_2265_;
v___y_2304_ = v_a_2266_;
goto v___jp_2299_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___boxed(lean_object* v_cmd_2319_, lean_object* v_opts_2320_, lean_object* v_tree_2321_, lean_object* v_msgs_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_cmd_2319_, v_opts_2320_, v_tree_2321_, v_msgs_2322_, v_a_2323_, v_a_2324_);
lean_dec(v_a_2324_);
lean_dec_ref(v_a_2323_);
lean_dec_ref(v_msgs_2322_);
lean_dec_ref(v_opts_2320_);
return v_res_2326_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(lean_object* v_00_u03b2_2327_, lean_object* v_m_2328_, lean_object* v_a_2329_){
_start:
{
uint8_t v___x_2330_; 
v___x_2330_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(v_m_2328_, v_a_2329_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___boxed(lean_object* v_00_u03b2_2331_, lean_object* v_m_2332_, lean_object* v_a_2333_){
_start:
{
uint8_t v_res_2334_; lean_object* v_r_2335_; 
v_res_2334_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_00_u03b2_2331_, v_m_2332_, v_a_2333_);
lean_dec_ref(v_a_2333_);
lean_dec_ref(v_m_2332_);
v_r_2335_ = lean_box(v_res_2334_);
return v_r_2335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1(lean_object* v_00_u03b2_2336_, lean_object* v_m_2337_, lean_object* v_a_2338_, lean_object* v_b_2339_){
_start:
{
lean_object* v___x_2340_; 
v___x_2340_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_m_2337_, v_a_2338_, v_b_2339_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2(lean_object* v___x_2341_, lean_object* v_fst_2342_, lean_object* v_snd_2343_, lean_object* v___x_2344_, lean_object* v_as_2345_, size_t v_sz_2346_, size_t v_i_2347_, lean_object* v_b_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v___x_2352_; 
v___x_2352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_2341_, v_fst_2342_, v_snd_2343_, v___x_2344_, v_as_2345_, v_sz_2346_, v_i_2347_, v_b_2348_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___boxed(lean_object* v___x_2353_, lean_object* v_fst_2354_, lean_object* v_snd_2355_, lean_object* v___x_2356_, lean_object* v_as_2357_, lean_object* v_sz_2358_, lean_object* v_i_2359_, lean_object* v_b_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
size_t v_sz_boxed_2364_; size_t v_i_boxed_2365_; lean_object* v_res_2366_; 
v_sz_boxed_2364_ = lean_unbox_usize(v_sz_2358_);
lean_dec(v_sz_2358_);
v_i_boxed_2365_ = lean_unbox_usize(v_i_2359_);
lean_dec(v_i_2359_);
v_res_2366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2(v___x_2353_, v_fst_2354_, v_snd_2355_, v___x_2356_, v_as_2357_, v_sz_boxed_2364_, v_i_boxed_2365_, v_b_2360_, v___y_2361_, v___y_2362_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec_ref(v_as_2357_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5(lean_object* v_msgData_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(v_msgData_2367_, v___y_2369_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___boxed(lean_object* v_msgData_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5(v_msgData_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
return v_res_2376_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0(lean_object* v_00_u03b2_2377_, lean_object* v_a_2378_, lean_object* v_x_2379_){
_start:
{
uint8_t v___x_2380_; 
v___x_2380_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(v_a_2378_, v_x_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2381_, lean_object* v_a_2382_, lean_object* v_x_2383_){
_start:
{
uint8_t v_res_2384_; lean_object* v_r_2385_; 
v_res_2384_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0(v_00_u03b2_2381_, v_a_2382_, v_x_2383_);
lean_dec(v_x_2383_);
lean_dec_ref(v_a_2382_);
v_r_2385_ = lean_box(v_res_2384_);
return v_r_2385_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2(lean_object* v_00_u03b2_2386_, lean_object* v_data_2387_){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2___redArg(v_data_2387_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2389_, lean_object* v_i_2390_, lean_object* v_source_2391_, lean_object* v_target_2392_){
_start:
{
lean_object* v___x_2393_; 
v___x_2393_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3___redArg(v_i_2390_, v_source_2391_, v_target_2392_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3_spec__8(lean_object* v_00_u03b2_2394_, lean_object* v_x_2395_, lean_object* v_x_2396_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3_spec__8___redArg(v_x_2395_, v_x_2396_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(lean_object* v_x_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v___x_2406_; 
lean_inc(v___y_2400_);
lean_inc_ref(v___y_2399_);
v___x_2406_ = lean_apply_7(v_x_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, lean_box(0));
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed(lean_object* v_x_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(v_x_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(lean_object* v_mvarId_2416_, lean_object* v_x_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v___f_2425_; lean_object* v___x_2426_; 
lean_inc(v___y_2419_);
lean_inc_ref(v___y_2418_);
v___f_2425_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2425_, 0, v_x_2417_);
lean_closure_set(v___f_2425_, 1, v___y_2418_);
lean_closure_set(v___f_2425_, 2, v___y_2419_);
v___x_2426_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2416_, v___f_2425_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
if (lean_obj_tag(v___x_2426_) == 0)
{
return v___x_2426_;
}
else
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___x_2426_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2426_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2427_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___boxed(lean_object* v_mvarId_2435_, lean_object* v_x_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2435_, v_x_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(lean_object* v_00_u03b1_2445_, lean_object* v_mvarId_2446_, lean_object* v_x_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v___x_2455_; 
v___x_2455_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2446_, v_x_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed(lean_object* v_00_u03b1_2456_, lean_object* v_mvarId_2457_, lean_object* v_x_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(v_00_u03b1_2456_, v_mvarId_2457_, v_x_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(lean_object* v_____r_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2481_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___boxed(lean_object* v_____r_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(v_____r_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(lean_object* v_____r_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2500_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1___boxed(lean_object* v_____r_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(v_____r_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
return v_res_2508_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(uint8_t v___x_2509_, lean_object* v_x_2510_){
_start:
{
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2___boxed(lean_object* v___x_2511_, lean_object* v_x_2512_){
_start:
{
uint8_t v___x_11848__boxed_2513_; uint8_t v_res_2514_; lean_object* v_r_2515_; 
v___x_11848__boxed_2513_ = lean_unbox(v___x_2511_);
v_res_2514_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(v___x_11848__boxed_2513_, v_x_2512_);
lean_dec(v_x_2512_);
v_r_2515_ = lean_box(v_res_2514_);
return v_r_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(lean_object* v_msgData_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v___x_2522_; lean_object* v_env_2523_; lean_object* v___x_2524_; lean_object* v_mctx_2525_; lean_object* v_lctx_2526_; lean_object* v_options_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2522_ = lean_st_ref_get(v___y_2520_);
v_env_2523_ = lean_ctor_get(v___x_2522_, 0);
lean_inc_ref(v_env_2523_);
lean_dec(v___x_2522_);
v___x_2524_ = lean_st_ref_get(v___y_2518_);
v_mctx_2525_ = lean_ctor_get(v___x_2524_, 0);
lean_inc_ref(v_mctx_2525_);
lean_dec(v___x_2524_);
v_lctx_2526_ = lean_ctor_get(v___y_2517_, 2);
v_options_2527_ = lean_ctor_get(v___y_2519_, 2);
lean_inc_ref(v_options_2527_);
lean_inc_ref(v_lctx_2526_);
v___x_2528_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2528_, 0, v_env_2523_);
lean_ctor_set(v___x_2528_, 1, v_mctx_2525_);
lean_ctor_set(v___x_2528_, 2, v_lctx_2526_);
lean_ctor_set(v___x_2528_, 3, v_options_2527_);
v___x_2529_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2528_);
lean_ctor_set(v___x_2529_, 1, v_msgData_2516_);
v___x_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2529_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2___boxed(lean_object* v_msgData_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msgData_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(lean_object* v_cls_2538_, lean_object* v_msg_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
lean_object* v_ref_2545_; lean_object* v___x_2546_; lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2591_; 
v_ref_2545_ = lean_ctor_get(v___y_2542_, 5);
v___x_2546_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2549_ = v___x_2546_;
v_isShared_2550_ = v_isSharedCheck_2591_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2546_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2591_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2551_; lean_object* v_traceState_2552_; lean_object* v_env_2553_; lean_object* v_nextMacroScope_2554_; lean_object* v_ngen_2555_; lean_object* v_auxDeclNGen_2556_; lean_object* v_cache_2557_; lean_object* v_messages_2558_; lean_object* v_infoState_2559_; lean_object* v_snapshotTasks_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2590_; 
v___x_2551_ = lean_st_ref_take(v___y_2543_);
v_traceState_2552_ = lean_ctor_get(v___x_2551_, 4);
v_env_2553_ = lean_ctor_get(v___x_2551_, 0);
v_nextMacroScope_2554_ = lean_ctor_get(v___x_2551_, 1);
v_ngen_2555_ = lean_ctor_get(v___x_2551_, 2);
v_auxDeclNGen_2556_ = lean_ctor_get(v___x_2551_, 3);
v_cache_2557_ = lean_ctor_get(v___x_2551_, 5);
v_messages_2558_ = lean_ctor_get(v___x_2551_, 6);
v_infoState_2559_ = lean_ctor_get(v___x_2551_, 7);
v_snapshotTasks_2560_ = lean_ctor_get(v___x_2551_, 8);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2562_ = v___x_2551_;
v_isShared_2563_ = v_isSharedCheck_2590_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_snapshotTasks_2560_);
lean_inc(v_infoState_2559_);
lean_inc(v_messages_2558_);
lean_inc(v_cache_2557_);
lean_inc(v_traceState_2552_);
lean_inc(v_auxDeclNGen_2556_);
lean_inc(v_ngen_2555_);
lean_inc(v_nextMacroScope_2554_);
lean_inc(v_env_2553_);
lean_dec(v___x_2551_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2590_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
uint64_t v_tid_2564_; lean_object* v_traces_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2589_; 
v_tid_2564_ = lean_ctor_get_uint64(v_traceState_2552_, sizeof(void*)*1);
v_traces_2565_ = lean_ctor_get(v_traceState_2552_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v_traceState_2552_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2567_ = v_traceState_2552_;
v_isShared_2568_ = v_isSharedCheck_2589_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_traces_2565_);
lean_dec(v_traceState_2552_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2589_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; double v___x_2570_; uint8_t v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2579_; 
v___x_2569_ = lean_box(0);
v___x_2570_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0);
v___x_2571_ = 0;
v___x_2572_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2573_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2573_, 0, v_cls_2538_);
lean_ctor_set(v___x_2573_, 1, v___x_2569_);
lean_ctor_set(v___x_2573_, 2, v___x_2572_);
lean_ctor_set_float(v___x_2573_, sizeof(void*)*3, v___x_2570_);
lean_ctor_set_float(v___x_2573_, sizeof(void*)*3 + 8, v___x_2570_);
lean_ctor_set_uint8(v___x_2573_, sizeof(void*)*3 + 16, v___x_2571_);
v___x_2574_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__1));
v___x_2575_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2573_);
lean_ctor_set(v___x_2575_, 1, v_a_2547_);
lean_ctor_set(v___x_2575_, 2, v___x_2574_);
lean_inc(v_ref_2545_);
v___x_2576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2576_, 0, v_ref_2545_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
v___x_2577_ = l_Lean_PersistentArray_push___redArg(v_traces_2565_, v___x_2576_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v___x_2577_);
v___x_2579_ = v___x_2567_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2577_);
lean_ctor_set_uint64(v_reuseFailAlloc_2588_, sizeof(void*)*1, v_tid_2564_);
v___x_2579_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2581_; 
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 4, v___x_2579_);
v___x_2581_ = v___x_2562_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_env_2553_);
lean_ctor_set(v_reuseFailAlloc_2587_, 1, v_nextMacroScope_2554_);
lean_ctor_set(v_reuseFailAlloc_2587_, 2, v_ngen_2555_);
lean_ctor_set(v_reuseFailAlloc_2587_, 3, v_auxDeclNGen_2556_);
lean_ctor_set(v_reuseFailAlloc_2587_, 4, v___x_2579_);
lean_ctor_set(v_reuseFailAlloc_2587_, 5, v_cache_2557_);
lean_ctor_set(v_reuseFailAlloc_2587_, 6, v_messages_2558_);
lean_ctor_set(v_reuseFailAlloc_2587_, 7, v_infoState_2559_);
lean_ctor_set(v_reuseFailAlloc_2587_, 8, v_snapshotTasks_2560_);
v___x_2581_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2585_; 
v___x_2582_ = lean_st_ref_set(v___y_2543_, v___x_2581_);
v___x_2583_ = lean_box(0);
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 0, v___x_2583_);
v___x_2585_ = v___x_2549_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2583_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg___boxed(lean_object* v_cls_2592_, lean_object* v_msg_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_2592_, v_msg_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
return v_res_2599_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2601_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__0));
v___x_2602_ = l_Lean_stringToMessageData(v___x_2601_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(lean_object* v___x_2603_, lean_object* v___x_2604_, lean_object* v___x_2605_, lean_object* v___f_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v___x_2614_; lean_object* v_a_2616_; lean_object* v___y_2620_; lean_object* v___x_2634_; 
v___x_2614_ = lean_st_mk_ref(v___x_2603_);
v___x_2634_ = l_Lean_Elab_Tactic_saveState___redArg(v___x_2614_, v___y_2608_, v___y_2610_, v___y_2612_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_a_2635_; lean_object* v___x_2636_; 
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
lean_inc(v_a_2635_);
lean_dec_ref_known(v___x_2634_, 1);
v___x_2636_ = l_Lean_Elab_Tactic_Try_collectTryCoreSuggestions(v___x_2604_, v___x_2605_, v___x_2614_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; 
lean_dec(v_a_2635_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___f_2606_);
lean_dec_ref(v___x_2605_);
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_a_2637_);
lean_dec_ref_known(v___x_2636_, 1);
v_a_2616_ = v_a_2637_;
goto v___jp_2615_;
}
else
{
lean_object* v_a_2638_; uint8_t v___y_2640_; uint8_t v___x_2683_; 
v_a_2638_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_a_2638_);
v___x_2683_ = l_Lean_Exception_isInterrupt(v_a_2638_);
if (v___x_2683_ == 0)
{
uint8_t v___x_2684_; 
lean_inc(v_a_2638_);
v___x_2684_ = l_Lean_Exception_isRuntime(v_a_2638_);
v___y_2640_ = v___x_2684_;
goto v___jp_2639_;
}
else
{
v___y_2640_ = v___x_2683_;
goto v___jp_2639_;
}
v___jp_2639_:
{
if (v___y_2640_ == 0)
{
lean_object* v___x_2641_; 
lean_dec_ref_known(v___x_2636_, 1);
v___x_2641_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2635_, v___y_2640_, v___x_2614_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2673_; 
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2673_ == 0)
{
lean_object* v_unused_2674_; 
v_unused_2674_ = lean_ctor_get(v___x_2641_, 0);
lean_dec(v_unused_2674_);
v___x_2643_ = v___x_2641_;
v_isShared_2644_ = v_isSharedCheck_2673_;
goto v_resetjp_2642_;
}
else
{
lean_dec(v___x_2641_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2673_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
uint8_t v___x_2645_; 
v___x_2645_ = l_Lean_Exception_isInterrupt(v_a_2638_);
if (v___x_2645_ == 0)
{
uint8_t v___x_2646_; 
lean_inc(v_a_2638_);
v___x_2646_ = l_Lean_Exception_isMaxRecDepth(v_a_2638_);
if (v___x_2646_ == 0)
{
lean_object* v_options_2647_; uint8_t v_hasTrace_2648_; 
lean_del_object(v___x_2643_);
v_options_2647_ = lean_ctor_get(v___y_2611_, 2);
v_hasTrace_2648_ = lean_ctor_get_uint8(v_options_2647_, sizeof(void*)*1);
if (v_hasTrace_2648_ == 0)
{
lean_dec(v_a_2638_);
goto v___jp_2631_;
}
else
{
lean_object* v_inheritedTraceOptions_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; uint8_t v___x_2652_; 
v_inheritedTraceOptions_2649_ = lean_ctor_get(v___y_2611_, 13);
v___x_2650_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2651_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_2652_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2649_, v_options_2647_, v___x_2651_);
if (v___x_2652_ == 0)
{
lean_dec(v_a_2638_);
goto v___jp_2631_;
}
else
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2653_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_2654_ = l_Lean_Exception_toMessageData(v_a_2638_);
v___x_2655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2653_);
lean_ctor_set(v___x_2655_, 1, v___x_2654_);
v___x_2656_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v___x_2650_, v___x_2655_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2658_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___x_2656_, 1);
lean_inc(v___x_2614_);
v___x_2658_ = lean_apply_10(v___f_2606_, v_a_2657_, v___x_2605_, v___x_2614_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, lean_box(0));
v___y_2620_ = v___x_2658_;
goto v___jp_2619_;
}
else
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
lean_dec(v___x_2614_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___f_2606_);
lean_dec_ref(v___x_2605_);
v_a_2659_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2661_ = v___x_2656_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2656_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2659_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
}
}
}
else
{
lean_object* v___x_2668_; 
lean_dec(v___x_2614_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___f_2606_);
lean_dec_ref(v___x_2605_);
if (v_isShared_2644_ == 0)
{
lean_ctor_set_tag(v___x_2643_, 1);
lean_ctor_set(v___x_2643_, 0, v_a_2638_);
v___x_2668_ = v___x_2643_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_a_2638_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
else
{
lean_object* v___x_2671_; 
lean_dec(v___x_2614_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___f_2606_);
lean_dec_ref(v___x_2605_);
if (v_isShared_2644_ == 0)
{
lean_ctor_set_tag(v___x_2643_, 1);
lean_ctor_set(v___x_2643_, 0, v_a_2638_);
v___x_2671_ = v___x_2643_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_a_2638_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_dec(v_a_2638_);
lean_dec(v___x_2614_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___f_2606_);
lean_dec_ref(v___x_2605_);
v_a_2675_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2641_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2641_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
else
{
lean_dec(v_a_2638_);
lean_dec(v_a_2635_);
lean_dec(v___x_2614_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___f_2606_);
lean_dec_ref(v___x_2605_);
return v___x_2636_;
}
}
}
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
lean_dec(v___x_2614_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___f_2606_);
lean_dec_ref(v___x_2605_);
lean_dec_ref(v___x_2604_);
v_a_2685_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2634_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2634_);
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
v___jp_2615_:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2617_ = lean_st_ref_get(v___x_2614_);
lean_dec(v___x_2614_);
lean_dec(v___x_2617_);
v___x_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2618_, 0, v_a_2616_);
return v___x_2618_;
}
v___jp_2619_:
{
if (lean_obj_tag(v___y_2620_) == 0)
{
lean_object* v_a_2621_; lean_object* v_a_2622_; 
v_a_2621_ = lean_ctor_get(v___y_2620_, 0);
lean_inc(v_a_2621_);
lean_dec_ref_known(v___y_2620_, 1);
v_a_2622_ = lean_ctor_get(v_a_2621_, 0);
lean_inc(v_a_2622_);
lean_dec(v_a_2621_);
v_a_2616_ = v_a_2622_;
goto v___jp_2615_;
}
else
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
lean_dec(v___x_2614_);
v_a_2623_ = lean_ctor_get(v___y_2620_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___y_2620_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___y_2620_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___y_2620_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2623_);
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
v___jp_2631_:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2632_ = lean_box(0);
lean_inc(v___x_2614_);
v___x_2633_ = lean_apply_10(v___f_2606_, v___x_2632_, v___x_2605_, v___x_2614_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, lean_box(0));
v___y_2620_ = v___x_2633_;
goto v___jp_2619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed(lean_object* v___x_2693_, lean_object* v___x_2694_, lean_object* v___x_2695_, lean_object* v___f_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(v___x_2693_, v___x_2694_, v___x_2695_, v___f_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(lean_object* v___x_2705_, uint8_t v___x_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2705_, v___x_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed(lean_object* v___x_2715_, lean_object* v___x_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
uint8_t v___x_12177__boxed_2724_; lean_object* v_res_2725_; 
v___x_12177__boxed_2724_ = lean_unbox(v___x_2716_);
v_res_2725_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(v___x_2715_, v___x_12177__boxed_2724_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(lean_object* v_cls_2726_, lean_object* v_msg_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v_ref_2733_; lean_object* v___x_2734_; lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2779_; 
v_ref_2733_ = lean_ctor_get(v___y_2730_, 5);
v___x_2734_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2737_ = v___x_2734_;
v_isShared_2738_ = v_isSharedCheck_2779_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2734_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2779_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2739_; lean_object* v_traceState_2740_; lean_object* v_env_2741_; lean_object* v_nextMacroScope_2742_; lean_object* v_ngen_2743_; lean_object* v_auxDeclNGen_2744_; lean_object* v_cache_2745_; lean_object* v_messages_2746_; lean_object* v_infoState_2747_; lean_object* v_snapshotTasks_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2778_; 
v___x_2739_ = lean_st_ref_take(v___y_2731_);
v_traceState_2740_ = lean_ctor_get(v___x_2739_, 4);
v_env_2741_ = lean_ctor_get(v___x_2739_, 0);
v_nextMacroScope_2742_ = lean_ctor_get(v___x_2739_, 1);
v_ngen_2743_ = lean_ctor_get(v___x_2739_, 2);
v_auxDeclNGen_2744_ = lean_ctor_get(v___x_2739_, 3);
v_cache_2745_ = lean_ctor_get(v___x_2739_, 5);
v_messages_2746_ = lean_ctor_get(v___x_2739_, 6);
v_infoState_2747_ = lean_ctor_get(v___x_2739_, 7);
v_snapshotTasks_2748_ = lean_ctor_get(v___x_2739_, 8);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2750_ = v___x_2739_;
v_isShared_2751_ = v_isSharedCheck_2778_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_snapshotTasks_2748_);
lean_inc(v_infoState_2747_);
lean_inc(v_messages_2746_);
lean_inc(v_cache_2745_);
lean_inc(v_traceState_2740_);
lean_inc(v_auxDeclNGen_2744_);
lean_inc(v_ngen_2743_);
lean_inc(v_nextMacroScope_2742_);
lean_inc(v_env_2741_);
lean_dec(v___x_2739_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2778_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
uint64_t v_tid_2752_; lean_object* v_traces_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2777_; 
v_tid_2752_ = lean_ctor_get_uint64(v_traceState_2740_, sizeof(void*)*1);
v_traces_2753_ = lean_ctor_get(v_traceState_2740_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v_traceState_2740_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2755_ = v_traceState_2740_;
v_isShared_2756_ = v_isSharedCheck_2777_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_traces_2753_);
lean_dec(v_traceState_2740_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2777_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2757_; double v___x_2758_; uint8_t v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2767_; 
v___x_2757_ = lean_box(0);
v___x_2758_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0);
v___x_2759_ = 0;
v___x_2760_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2761_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2761_, 0, v_cls_2726_);
lean_ctor_set(v___x_2761_, 1, v___x_2757_);
lean_ctor_set(v___x_2761_, 2, v___x_2760_);
lean_ctor_set_float(v___x_2761_, sizeof(void*)*3, v___x_2758_);
lean_ctor_set_float(v___x_2761_, sizeof(void*)*3 + 8, v___x_2758_);
lean_ctor_set_uint8(v___x_2761_, sizeof(void*)*3 + 16, v___x_2759_);
v___x_2762_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__1));
v___x_2763_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2761_);
lean_ctor_set(v___x_2763_, 1, v_a_2735_);
lean_ctor_set(v___x_2763_, 2, v___x_2762_);
lean_inc(v_ref_2733_);
v___x_2764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2764_, 0, v_ref_2733_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
v___x_2765_ = l_Lean_PersistentArray_push___redArg(v_traces_2753_, v___x_2764_);
if (v_isShared_2756_ == 0)
{
lean_ctor_set(v___x_2755_, 0, v___x_2765_);
v___x_2767_ = v___x_2755_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2765_);
lean_ctor_set_uint64(v_reuseFailAlloc_2776_, sizeof(void*)*1, v_tid_2752_);
v___x_2767_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
lean_object* v___x_2769_; 
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 4, v___x_2767_);
v___x_2769_ = v___x_2750_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_env_2741_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v_nextMacroScope_2742_);
lean_ctor_set(v_reuseFailAlloc_2775_, 2, v_ngen_2743_);
lean_ctor_set(v_reuseFailAlloc_2775_, 3, v_auxDeclNGen_2744_);
lean_ctor_set(v_reuseFailAlloc_2775_, 4, v___x_2767_);
lean_ctor_set(v_reuseFailAlloc_2775_, 5, v_cache_2745_);
lean_ctor_set(v_reuseFailAlloc_2775_, 6, v_messages_2746_);
lean_ctor_set(v_reuseFailAlloc_2775_, 7, v_infoState_2747_);
lean_ctor_set(v_reuseFailAlloc_2775_, 8, v_snapshotTasks_2748_);
v___x_2769_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2773_; 
v___x_2770_ = lean_st_ref_set(v___y_2731_, v___x_2769_);
v___x_2771_ = lean_box(0);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 0, v___x_2771_);
v___x_2773_ = v___x_2737_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2771_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3___boxed(lean_object* v_cls_2780_, lean_object* v_msg_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v_cls_2780_, v_msg_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
return v_res_2787_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__0));
v___x_2790_ = l_Lean_stringToMessageData(v___x_2789_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(lean_object* v_term_2791_, lean_object* v___x_2792_, lean_object* v___x_2793_, lean_object* v___f_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v___y_2801_; lean_object* v___x_2819_; 
v___x_2819_ = l_Lean_Elab_Term_TermElabM_run___redArg(v_term_2791_, v___x_2792_, v___x_2793_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2828_; 
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec_ref(v___f_2794_);
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2822_ = v___x_2819_;
v_isShared_2823_ = v_isSharedCheck_2828_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2819_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2828_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v_fst_2824_; lean_object* v___x_2826_; 
v_fst_2824_ = lean_ctor_get(v_a_2820_, 0);
lean_inc(v_fst_2824_);
lean_dec(v_a_2820_);
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 0, v_fst_2824_);
v___x_2826_ = v___x_2822_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_fst_2824_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
else
{
lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2871_; 
v_a_2829_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2831_ = v___x_2819_;
v_isShared_2832_ = v_isSharedCheck_2871_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2819_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2871_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
uint8_t v___y_2837_; uint8_t v___x_2869_; 
v___x_2869_ = l_Lean_Exception_isInterrupt(v_a_2829_);
if (v___x_2869_ == 0)
{
uint8_t v___x_2870_; 
lean_inc(v_a_2829_);
v___x_2870_ = l_Lean_Exception_isRuntime(v_a_2829_);
v___y_2837_ = v___x_2870_;
goto v___jp_2836_;
}
else
{
v___y_2837_ = v___x_2869_;
goto v___jp_2836_;
}
v___jp_2833_:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = lean_box(0);
v___x_2835_ = lean_apply_6(v___f_2794_, v___x_2834_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, lean_box(0));
v___y_2801_ = v___x_2835_;
goto v___jp_2800_;
}
v___jp_2836_:
{
if (v___y_2837_ == 0)
{
uint8_t v___x_2838_; 
v___x_2838_ = l_Lean_Exception_isInterrupt(v_a_2829_);
if (v___x_2838_ == 0)
{
uint8_t v___x_2839_; 
lean_inc(v_a_2829_);
v___x_2839_ = l_Lean_Exception_isMaxRecDepth(v_a_2829_);
if (v___x_2839_ == 0)
{
lean_object* v_options_2840_; uint8_t v_hasTrace_2841_; 
lean_del_object(v___x_2831_);
v_options_2840_ = lean_ctor_get(v___y_2797_, 2);
v_hasTrace_2841_ = lean_ctor_get_uint8(v_options_2840_, sizeof(void*)*1);
if (v_hasTrace_2841_ == 0)
{
lean_dec(v_a_2829_);
goto v___jp_2833_;
}
else
{
lean_object* v_inheritedTraceOptions_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; uint8_t v___x_2845_; 
v_inheritedTraceOptions_2842_ = lean_ctor_get(v___y_2797_, 13);
v___x_2843_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2844_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_2845_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2842_, v_options_2840_, v___x_2844_);
if (v___x_2845_ == 0)
{
lean_dec(v_a_2829_);
goto v___jp_2833_;
}
else
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2846_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1);
v___x_2847_ = l_Lean_Exception_toMessageData(v_a_2829_);
v___x_2848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2846_);
lean_ctor_set(v___x_2848_, 1, v___x_2847_);
v___x_2849_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_2843_, v___x_2848_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2851_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref_known(v___x_2849_, 1);
v___x_2851_ = lean_apply_6(v___f_2794_, v_a_2850_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, lean_box(0));
v___y_2801_ = v___x_2851_;
goto v___jp_2800_;
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec_ref(v___f_2794_);
v_a_2852_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2854_ = v___x_2849_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2849_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
}
}
else
{
lean_object* v___x_2861_; 
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec_ref(v___f_2794_);
if (v_isShared_2832_ == 0)
{
v___x_2861_ = v___x_2831_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2829_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
else
{
lean_object* v___x_2864_; 
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec_ref(v___f_2794_);
if (v_isShared_2832_ == 0)
{
v___x_2864_ = v___x_2831_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_a_2829_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
else
{
lean_object* v___x_2867_; 
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec_ref(v___f_2794_);
if (v_isShared_2832_ == 0)
{
v___x_2867_ = v___x_2831_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2829_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
}
v___jp_2800_:
{
if (lean_obj_tag(v___y_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2810_; 
v_a_2802_ = lean_ctor_get(v___y_2801_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___y_2801_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2804_ = v___y_2801_;
v_isShared_2805_ = v_isSharedCheck_2810_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___y_2801_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2810_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v_a_2806_; lean_object* v___x_2808_; 
v_a_2806_ = lean_ctor_get(v_a_2802_, 0);
lean_inc(v_a_2806_);
lean_dec(v_a_2802_);
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 0, v_a_2806_);
v___x_2808_ = v___x_2804_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_a_2806_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
else
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2818_; 
v_a_2811_ = lean_ctor_get(v___y_2801_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___y_2801_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2813_ = v___y_2801_;
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___y_2801_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2816_; 
if (v_isShared_2814_ == 0)
{
v___x_2816_ = v___x_2813_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___boxed(lean_object* v_term_2872_, lean_object* v___x_2873_, lean_object* v___x_2874_, lean_object* v___f_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(v_term_2872_, v___x_2873_, v___x_2874_, v___f_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_2882_, lean_object* v_vals_2883_, lean_object* v_i_2884_, lean_object* v_k_2885_){
_start:
{
lean_object* v___x_2886_; uint8_t v___x_2887_; 
v___x_2886_ = lean_array_get_size(v_keys_2882_);
v___x_2887_ = lean_nat_dec_lt(v_i_2884_, v___x_2886_);
if (v___x_2887_ == 0)
{
lean_object* v___x_2888_; 
lean_dec(v_i_2884_);
v___x_2888_ = lean_box(0);
return v___x_2888_;
}
else
{
lean_object* v_k_x27_2889_; uint8_t v___x_2890_; 
v_k_x27_2889_ = lean_array_fget_borrowed(v_keys_2882_, v_i_2884_);
v___x_2890_ = l_Lean_instBEqMVarId_beq(v_k_2885_, v_k_x27_2889_);
if (v___x_2890_ == 0)
{
lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2891_ = lean_unsigned_to_nat(1u);
v___x_2892_ = lean_nat_add(v_i_2884_, v___x_2891_);
lean_dec(v_i_2884_);
v_i_2884_ = v___x_2892_;
goto _start;
}
else
{
lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2894_ = lean_array_fget_borrowed(v_vals_2883_, v_i_2884_);
lean_dec(v_i_2884_);
lean_inc(v___x_2894_);
v___x_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2894_);
return v___x_2895_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_2896_, lean_object* v_vals_2897_, lean_object* v_i_2898_, lean_object* v_k_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_keys_2896_, v_vals_2897_, v_i_2898_, v_k_2899_);
lean_dec(v_k_2899_);
lean_dec_ref(v_vals_2897_);
lean_dec_ref(v_keys_2896_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(lean_object* v_x_2901_, size_t v_x_2902_, lean_object* v_x_2903_){
_start:
{
if (lean_obj_tag(v_x_2901_) == 0)
{
lean_object* v_es_2904_; lean_object* v___x_2905_; size_t v___x_2906_; size_t v___x_2907_; lean_object* v_j_2908_; lean_object* v___x_2909_; 
v_es_2904_ = lean_ctor_get(v_x_2901_, 0);
v___x_2905_ = lean_box(2);
v___x_2906_ = ((size_t)31ULL);
v___x_2907_ = lean_usize_land(v_x_2902_, v___x_2906_);
v_j_2908_ = lean_usize_to_nat(v___x_2907_);
v___x_2909_ = lean_array_get_borrowed(v___x_2905_, v_es_2904_, v_j_2908_);
lean_dec(v_j_2908_);
switch(lean_obj_tag(v___x_2909_))
{
case 0:
{
lean_object* v_key_2910_; lean_object* v_val_2911_; uint8_t v___x_2912_; 
v_key_2910_ = lean_ctor_get(v___x_2909_, 0);
v_val_2911_ = lean_ctor_get(v___x_2909_, 1);
v___x_2912_ = l_Lean_instBEqMVarId_beq(v_x_2903_, v_key_2910_);
if (v___x_2912_ == 0)
{
lean_object* v___x_2913_; 
v___x_2913_ = lean_box(0);
return v___x_2913_;
}
else
{
lean_object* v___x_2914_; 
lean_inc(v_val_2911_);
v___x_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2914_, 0, v_val_2911_);
return v___x_2914_;
}
}
case 1:
{
lean_object* v_node_2915_; size_t v___x_2916_; size_t v___x_2917_; 
v_node_2915_ = lean_ctor_get(v___x_2909_, 0);
v___x_2916_ = ((size_t)5ULL);
v___x_2917_ = lean_usize_shift_right(v_x_2902_, v___x_2916_);
v_x_2901_ = v_node_2915_;
v_x_2902_ = v___x_2917_;
goto _start;
}
default: 
{
lean_object* v___x_2919_; 
v___x_2919_ = lean_box(0);
return v___x_2919_;
}
}
}
else
{
lean_object* v_ks_2920_; lean_object* v_vs_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; 
v_ks_2920_ = lean_ctor_get(v_x_2901_, 0);
v_vs_2921_ = lean_ctor_get(v_x_2901_, 1);
v___x_2922_ = lean_unsigned_to_nat(0u);
v___x_2923_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_ks_2920_, v_vs_2921_, v___x_2922_, v_x_2903_);
return v___x_2923_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg___boxed(lean_object* v_x_2924_, lean_object* v_x_2925_, lean_object* v_x_2926_){
_start:
{
size_t v_x_12496__boxed_2927_; lean_object* v_res_2928_; 
v_x_12496__boxed_2927_ = lean_unbox_usize(v_x_2925_);
lean_dec(v_x_2925_);
v_res_2928_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_2924_, v_x_12496__boxed_2927_, v_x_2926_);
lean_dec(v_x_2926_);
lean_dec_ref(v_x_2924_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(lean_object* v_x_2929_, lean_object* v_x_2930_){
_start:
{
uint64_t v___x_2931_; size_t v___x_2932_; lean_object* v___x_2933_; 
v___x_2931_ = l_Lean_instHashableMVarId_hash(v_x_2930_);
v___x_2932_ = lean_uint64_to_usize(v___x_2931_);
v___x_2933_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_2929_, v___x_2932_, v_x_2930_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg___boxed(lean_object* v_x_2934_, lean_object* v_x_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_x_2934_, v_x_2935_);
lean_dec(v_x_2935_);
lean_dec_ref(v_x_2934_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(lean_object* v_c_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_){
_start:
{
lean_object* v_mctx_2966_; lean_object* v_env_2967_; lean_object* v_opts_2968_; lean_object* v_namingCtx_2969_; lean_object* v_goal_2970_; lean_object* v_decls_2971_; lean_object* v___x_2972_; 
v_mctx_2966_ = lean_ctor_get(v_c_2962_, 3);
lean_inc_ref(v_mctx_2966_);
v_env_2967_ = lean_ctor_get(v_c_2962_, 2);
lean_inc_ref(v_env_2967_);
v_opts_2968_ = lean_ctor_get(v_c_2962_, 4);
lean_inc_ref(v_opts_2968_);
v_namingCtx_2969_ = lean_ctor_get(v_c_2962_, 5);
lean_inc_ref(v_namingCtx_2969_);
v_goal_2970_ = lean_ctor_get(v_c_2962_, 6);
lean_inc(v_goal_2970_);
lean_dec_ref(v_c_2962_);
v_decls_2971_ = lean_ctor_get(v_mctx_2966_, 5);
v___x_2972_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_decls_2971_, v_goal_2970_);
if (lean_obj_tag(v___x_2972_) == 1)
{
lean_object* v_val_2973_; lean_object* v_lctx_2974_; lean_object* v___f_2975_; lean_object* v___f_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___f_2981_; lean_object* v___x_2982_; uint8_t v___x_2983_; lean_object* v___x_2984_; lean_object* v_term_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___f_2988_; lean_object* v___x_2989_; 
v_val_2973_ = lean_ctor_get(v___x_2972_, 0);
lean_inc(v_val_2973_);
lean_dec_ref_known(v___x_2972_, 1);
v_lctx_2974_ = lean_ctor_get(v_val_2973_, 1);
lean_inc_ref(v_lctx_2974_);
lean_dec(v_val_2973_);
v___f_2975_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__0));
v___f_2976_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__1));
v___x_2977_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__3));
v___x_2978_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__4));
v___x_2979_ = lean_box(0);
lean_inc(v_goal_2970_);
v___x_2980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2980_, 0, v_goal_2970_);
lean_ctor_set(v___x_2980_, 1, v___x_2979_);
v___f_2981_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed), 11, 4);
lean_closure_set(v___f_2981_, 0, v___x_2980_);
lean_closure_set(v___f_2981_, 1, v___x_2977_);
lean_closure_set(v___f_2981_, 2, v___x_2978_);
lean_closure_set(v___f_2981_, 3, v___f_2975_);
v___x_2982_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed), 10, 3);
lean_closure_set(v___x_2982_, 0, lean_box(0));
lean_closure_set(v___x_2982_, 1, v_goal_2970_);
lean_closure_set(v___x_2982_, 2, v___f_2981_);
v___x_2983_ = 1;
v___x_2984_ = lean_box(v___x_2983_);
v_term_2985_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed), 9, 2);
lean_closure_set(v_term_2985_, 0, v___x_2982_);
lean_closure_set(v_term_2985_, 1, v___x_2984_);
v___x_2986_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__6));
v___x_2987_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__7));
v___f_2988_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___boxed), 9, 4);
lean_closure_set(v___f_2988_, 0, v_term_2985_);
lean_closure_set(v___f_2988_, 1, v___x_2986_);
lean_closure_set(v___f_2988_, 2, v___x_2987_);
lean_closure_set(v___f_2988_, 3, v___f_2976_);
v___x_2989_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_2967_, v_mctx_2966_, v_lctx_2974_, v_opts_2968_, v_namingCtx_2969_, v___f_2988_, v_a_2963_, v_a_2964_);
lean_dec_ref(v_namingCtx_2969_);
return v___x_2989_;
}
else
{
lean_object* v___x_2990_; lean_object* v___x_2991_; 
lean_dec(v___x_2972_);
lean_dec(v_goal_2970_);
lean_dec_ref(v_namingCtx_2969_);
lean_dec_ref(v_opts_2968_);
lean_dec_ref(v_env_2967_);
lean_dec_ref(v_mctx_2966_);
v___x_2990_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__0));
v___x_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2990_);
return v___x_2991_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___boxed(lean_object* v_c_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(v_c_2992_, v_a_2993_, v_a_2994_);
lean_dec(v_a_2994_);
lean_dec_ref(v_a_2993_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0(lean_object* v_00_u03b2_2997_, lean_object* v_x_2998_, lean_object* v_x_2999_){
_start:
{
lean_object* v___x_3000_; 
v___x_3000_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_x_2998_, v_x_2999_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___boxed(lean_object* v_00_u03b2_3001_, lean_object* v_x_3002_, lean_object* v_x_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0(v_00_u03b2_3001_, v_x_3002_, v_x_3003_);
lean_dec(v_x_3003_);
lean_dec_ref(v_x_3002_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(lean_object* v_cls_3005_, lean_object* v_msg_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
lean_object* v___x_3016_; 
v___x_3016_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_3005_, v_msg_3006_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___boxed(lean_object* v_cls_3017_, lean_object* v_msg_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(v_cls_3017_, v_msg_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(lean_object* v_00_u03b2_3029_, lean_object* v_x_3030_, size_t v_x_3031_, lean_object* v_x_3032_){
_start:
{
lean_object* v___x_3033_; 
v___x_3033_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_3030_, v_x_3031_, v_x_3032_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3034_, lean_object* v_x_3035_, lean_object* v_x_3036_, lean_object* v_x_3037_){
_start:
{
size_t v_x_12753__boxed_3038_; lean_object* v_res_3039_; 
v_x_12753__boxed_3038_ = lean_unbox_usize(v_x_3036_);
lean_dec(v_x_3036_);
v_res_3039_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(v_00_u03b2_3034_, v_x_3035_, v_x_12753__boxed_3038_, v_x_3037_);
lean_dec(v_x_3037_);
lean_dec_ref(v_x_3035_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3040_, lean_object* v_keys_3041_, lean_object* v_vals_3042_, lean_object* v_heq_3043_, lean_object* v_i_3044_, lean_object* v_k_3045_){
_start:
{
lean_object* v___x_3046_; 
v___x_3046_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_keys_3041_, v_vals_3042_, v_i_3044_, v_k_3045_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3047_, lean_object* v_keys_3048_, lean_object* v_vals_3049_, lean_object* v_heq_3050_, lean_object* v_i_3051_, lean_object* v_k_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2(v_00_u03b2_3047_, v_keys_3048_, v_vals_3049_, v_heq_3050_, v_i_3051_, v_k_3052_);
lean_dec(v_k_3052_);
lean_dec_ref(v_vals_3049_);
lean_dec_ref(v_keys_3048_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(uint8_t v___x_3056_, lean_object* v___x_3057_, lean_object* v_ref_3058_, lean_object* v_a_3059_, lean_object* v___x_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
if (v___x_3056_ == 0)
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; uint8_t v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3057_);
v___x_3065_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__0));
v___x_3066_ = lean_box(0);
v___x_3067_ = 4;
v___x_3068_ = l_Lean_MessageData_nil;
v___x_3069_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_3058_, v_a_3059_, v___x_3064_, v___x_3065_, v___x_3066_, v___x_3067_, v___x_3068_, v___y_3061_, v___y_3062_);
return v___x_3069_;
}
else
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; uint8_t v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3070_ = l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default;
v___x_3071_ = lean_array_get(v___x_3070_, v_a_3059_, v___x_3060_);
lean_dec_ref(v_a_3059_);
v___x_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3057_);
v___x_3073_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__1));
v___x_3074_ = lean_box(0);
v___x_3075_ = 4;
v___x_3076_ = l_Lean_MessageData_nil;
v___x_3077_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_3058_, v___x_3071_, v___x_3072_, v___x_3073_, v___x_3074_, v___x_3075_, v___x_3076_, v___y_3061_, v___y_3062_);
return v___x_3077_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed(lean_object* v___x_3078_, lean_object* v___x_3079_, lean_object* v_ref_3080_, lean_object* v_a_3081_, lean_object* v___x_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
uint8_t v___x_3935__boxed_3086_; lean_object* v_res_3087_; 
v___x_3935__boxed_3086_ = lean_unbox(v___x_3078_);
v_res_3087_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(v___x_3935__boxed_3086_, v___x_3079_, v_ref_3080_, v_a_3081_, v___x_3082_, v___y_3083_, v___y_3084_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___x_3082_);
return v_res_3087_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(uint8_t v___y_3088_, uint8_t v_suppressElabErrors_3089_, lean_object* v_x_3090_){
_start:
{
if (lean_obj_tag(v_x_3090_) == 1)
{
lean_object* v_pre_3091_; 
v_pre_3091_ = lean_ctor_get(v_x_3090_, 0);
if (lean_obj_tag(v_pre_3091_) == 0)
{
lean_object* v_str_3092_; lean_object* v___x_3093_; uint8_t v___x_3094_; 
v_str_3092_ = lean_ctor_get(v_x_3090_, 1);
v___x_3093_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__1));
v___x_3094_ = lean_string_dec_eq(v_str_3092_, v___x_3093_);
if (v___x_3094_ == 0)
{
return v___y_3088_;
}
else
{
return v_suppressElabErrors_3089_;
}
}
else
{
return v___y_3088_;
}
}
else
{
return v___y_3088_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed(lean_object* v___y_3095_, lean_object* v_suppressElabErrors_3096_, lean_object* v_x_3097_){
_start:
{
uint8_t v___y_3987__boxed_3098_; uint8_t v_suppressElabErrors_boxed_3099_; uint8_t v_res_3100_; lean_object* v_r_3101_; 
v___y_3987__boxed_3098_ = lean_unbox(v___y_3095_);
v_suppressElabErrors_boxed_3099_ = lean_unbox(v_suppressElabErrors_3096_);
v_res_3100_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(v___y_3987__boxed_3098_, v_suppressElabErrors_boxed_3099_, v_x_3097_);
lean_dec(v_x_3097_);
v_r_3101_ = lean_box(v_res_3100_);
return v_r_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(lean_object* v_ref_3102_, lean_object* v_msgData_3103_, uint8_t v_severity_3104_, uint8_t v_isSilent_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_){
_start:
{
lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; uint8_t v___y_3114_; lean_object* v___y_3115_; uint8_t v___y_3116_; lean_object* v___y_3117_; uint8_t v___y_3174_; uint8_t v___y_3175_; lean_object* v___y_3176_; uint8_t v___y_3177_; lean_object* v___y_3178_; uint8_t v___y_3202_; lean_object* v___y_3203_; uint8_t v___y_3204_; uint8_t v___y_3205_; lean_object* v___y_3206_; uint8_t v___y_3210_; uint8_t v___y_3211_; uint8_t v___y_3212_; uint8_t v___x_3227_; uint8_t v___y_3229_; uint8_t v___y_3230_; uint8_t v___y_3231_; uint8_t v___y_3233_; uint8_t v___x_3245_; 
v___x_3227_ = 2;
v___x_3245_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3104_, v___x_3227_);
if (v___x_3245_ == 0)
{
v___y_3233_ = v___x_3245_;
goto v___jp_3232_;
}
else
{
uint8_t v___x_3246_; 
lean_inc_ref(v_msgData_3103_);
v___x_3246_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3103_);
v___y_3233_ = v___x_3246_;
goto v___jp_3232_;
}
v___jp_3109_:
{
lean_object* v___x_3118_; 
v___x_3118_ = l_Lean_Elab_Command_getScope___redArg(v___y_3117_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_object* v_a_3119_; lean_object* v___x_3120_; 
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
lean_inc(v_a_3119_);
lean_dec_ref_known(v___x_3118_, 1);
v___x_3120_ = l_Lean_Elab_Command_getScope___redArg(v___y_3117_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3156_; 
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3123_ = v___x_3120_;
v_isShared_3124_ = v_isSharedCheck_3156_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3120_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3156_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3125_; lean_object* v_currNamespace_3126_; lean_object* v_openDecls_3127_; lean_object* v_env_3128_; lean_object* v_messages_3129_; lean_object* v_scopes_3130_; lean_object* v_usedQuotCtxts_3131_; lean_object* v_nextMacroScope_3132_; lean_object* v_maxRecDepth_3133_; lean_object* v_ngen_3134_; lean_object* v_auxDeclNGen_3135_; lean_object* v_infoState_3136_; lean_object* v_traceState_3137_; lean_object* v_snapshotTasks_3138_; lean_object* v_prevLinterStates_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3155_; 
v___x_3125_ = lean_st_ref_take(v___y_3117_);
v_currNamespace_3126_ = lean_ctor_get(v_a_3119_, 2);
lean_inc(v_currNamespace_3126_);
lean_dec(v_a_3119_);
v_openDecls_3127_ = lean_ctor_get(v_a_3121_, 3);
lean_inc(v_openDecls_3127_);
lean_dec(v_a_3121_);
v_env_3128_ = lean_ctor_get(v___x_3125_, 0);
v_messages_3129_ = lean_ctor_get(v___x_3125_, 1);
v_scopes_3130_ = lean_ctor_get(v___x_3125_, 2);
v_usedQuotCtxts_3131_ = lean_ctor_get(v___x_3125_, 3);
v_nextMacroScope_3132_ = lean_ctor_get(v___x_3125_, 4);
v_maxRecDepth_3133_ = lean_ctor_get(v___x_3125_, 5);
v_ngen_3134_ = lean_ctor_get(v___x_3125_, 6);
v_auxDeclNGen_3135_ = lean_ctor_get(v___x_3125_, 7);
v_infoState_3136_ = lean_ctor_get(v___x_3125_, 8);
v_traceState_3137_ = lean_ctor_get(v___x_3125_, 9);
v_snapshotTasks_3138_ = lean_ctor_get(v___x_3125_, 10);
v_prevLinterStates_3139_ = lean_ctor_get(v___x_3125_, 11);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3141_ = v___x_3125_;
v_isShared_3142_ = v_isSharedCheck_3155_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_prevLinterStates_3139_);
lean_inc(v_snapshotTasks_3138_);
lean_inc(v_traceState_3137_);
lean_inc(v_infoState_3136_);
lean_inc(v_auxDeclNGen_3135_);
lean_inc(v_ngen_3134_);
lean_inc(v_maxRecDepth_3133_);
lean_inc(v_nextMacroScope_3132_);
lean_inc(v_usedQuotCtxts_3131_);
lean_inc(v_scopes_3130_);
lean_inc(v_messages_3129_);
lean_inc(v_env_3128_);
lean_dec(v___x_3125_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3155_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3148_; 
v___x_3143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3143_, 0, v_currNamespace_3126_);
lean_ctor_set(v___x_3143_, 1, v_openDecls_3127_);
v___x_3144_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3143_);
lean_ctor_set(v___x_3144_, 1, v___y_3113_);
lean_inc_ref(v___y_3111_);
lean_inc_ref(v___y_3110_);
v___x_3145_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3145_, 0, v___y_3110_);
lean_ctor_set(v___x_3145_, 1, v___y_3112_);
lean_ctor_set(v___x_3145_, 2, v___y_3115_);
lean_ctor_set(v___x_3145_, 3, v___y_3111_);
lean_ctor_set(v___x_3145_, 4, v___x_3144_);
lean_ctor_set_uint8(v___x_3145_, sizeof(void*)*5, v___y_3116_);
lean_ctor_set_uint8(v___x_3145_, sizeof(void*)*5 + 1, v___y_3114_);
lean_ctor_set_uint8(v___x_3145_, sizeof(void*)*5 + 2, v_isSilent_3105_);
v___x_3146_ = l_Lean_MessageLog_add(v___x_3145_, v_messages_3129_);
if (v_isShared_3142_ == 0)
{
lean_ctor_set(v___x_3141_, 1, v___x_3146_);
v___x_3148_ = v___x_3141_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_env_3128_);
lean_ctor_set(v_reuseFailAlloc_3154_, 1, v___x_3146_);
lean_ctor_set(v_reuseFailAlloc_3154_, 2, v_scopes_3130_);
lean_ctor_set(v_reuseFailAlloc_3154_, 3, v_usedQuotCtxts_3131_);
lean_ctor_set(v_reuseFailAlloc_3154_, 4, v_nextMacroScope_3132_);
lean_ctor_set(v_reuseFailAlloc_3154_, 5, v_maxRecDepth_3133_);
lean_ctor_set(v_reuseFailAlloc_3154_, 6, v_ngen_3134_);
lean_ctor_set(v_reuseFailAlloc_3154_, 7, v_auxDeclNGen_3135_);
lean_ctor_set(v_reuseFailAlloc_3154_, 8, v_infoState_3136_);
lean_ctor_set(v_reuseFailAlloc_3154_, 9, v_traceState_3137_);
lean_ctor_set(v_reuseFailAlloc_3154_, 10, v_snapshotTasks_3138_);
lean_ctor_set(v_reuseFailAlloc_3154_, 11, v_prevLinterStates_3139_);
v___x_3148_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3152_; 
v___x_3149_ = lean_st_ref_set(v___y_3117_, v___x_3148_);
v___x_3150_ = lean_box(0);
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 0, v___x_3150_);
v___x_3152_ = v___x_3123_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___x_3150_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
}
}
else
{
lean_object* v_a_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3164_; 
lean_dec(v_a_3119_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3113_);
lean_dec_ref(v___y_3112_);
v_a_3157_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3159_ = v___x_3120_;
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_a_3157_);
lean_dec(v___x_3120_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3162_; 
if (v_isShared_3160_ == 0)
{
v___x_3162_ = v___x_3159_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_a_3157_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
}
}
else
{
lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3172_; 
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3113_);
lean_dec_ref(v___y_3112_);
v_a_3165_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3167_ = v___x_3118_;
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v___x_3118_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3170_; 
if (v_isShared_3168_ == 0)
{
v___x_3170_ = v___x_3167_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_a_3165_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
}
}
v___jp_3173_:
{
lean_object* v_fileName_3179_; lean_object* v_fileMap_3180_; uint8_t v_suppressElabErrors_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v_a_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3200_; 
v_fileName_3179_ = lean_ctor_get(v___y_3106_, 0);
v_fileMap_3180_ = lean_ctor_get(v___y_3106_, 1);
v_suppressElabErrors_3181_ = lean_ctor_get_uint8(v___y_3106_, sizeof(void*)*10);
v___x_3182_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3103_);
v___x_3183_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(v___x_3182_, v___y_3107_);
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3186_ = v___x_3183_;
v_isShared_3187_ = v_isSharedCheck_3200_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_dec(v___x_3183_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3200_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
lean_inc_ref_n(v_fileMap_3180_, 2);
v___x_3188_ = l_Lean_FileMap_toPosition(v_fileMap_3180_, v___y_3176_);
lean_dec(v___y_3176_);
v___x_3189_ = l_Lean_FileMap_toPosition(v_fileMap_3180_, v___y_3178_);
lean_dec(v___y_3178_);
v___x_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3189_);
v___x_3191_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
if (v_suppressElabErrors_3181_ == 0)
{
lean_del_object(v___x_3186_);
v___y_3110_ = v_fileName_3179_;
v___y_3111_ = v___x_3191_;
v___y_3112_ = v___x_3188_;
v___y_3113_ = v_a_3184_;
v___y_3114_ = v___y_3175_;
v___y_3115_ = v___x_3190_;
v___y_3116_ = v___y_3177_;
v___y_3117_ = v___y_3107_;
goto v___jp_3109_;
}
else
{
lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___f_3194_; uint8_t v___x_3195_; 
v___x_3192_ = lean_box(v___y_3174_);
v___x_3193_ = lean_box(v_suppressElabErrors_3181_);
v___f_3194_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3194_, 0, v___x_3192_);
lean_closure_set(v___f_3194_, 1, v___x_3193_);
lean_inc(v_a_3184_);
v___x_3195_ = l_Lean_MessageData_hasTag(v___f_3194_, v_a_3184_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; lean_object* v___x_3198_; 
lean_dec_ref_known(v___x_3190_, 1);
lean_dec_ref(v___x_3188_);
lean_dec(v_a_3184_);
v___x_3196_ = lean_box(0);
if (v_isShared_3187_ == 0)
{
lean_ctor_set(v___x_3186_, 0, v___x_3196_);
v___x_3198_ = v___x_3186_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v___x_3196_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
else
{
lean_del_object(v___x_3186_);
v___y_3110_ = v_fileName_3179_;
v___y_3111_ = v___x_3191_;
v___y_3112_ = v___x_3188_;
v___y_3113_ = v_a_3184_;
v___y_3114_ = v___y_3175_;
v___y_3115_ = v___x_3190_;
v___y_3116_ = v___y_3177_;
v___y_3117_ = v___y_3107_;
goto v___jp_3109_;
}
}
}
}
v___jp_3201_:
{
lean_object* v___x_3207_; 
v___x_3207_ = l_Lean_Syntax_getTailPos_x3f(v___y_3203_, v___y_3205_);
lean_dec(v___y_3203_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_inc(v___y_3206_);
v___y_3174_ = v___y_3202_;
v___y_3175_ = v___y_3204_;
v___y_3176_ = v___y_3206_;
v___y_3177_ = v___y_3205_;
v___y_3178_ = v___y_3206_;
goto v___jp_3173_;
}
else
{
lean_object* v_val_3208_; 
v_val_3208_ = lean_ctor_get(v___x_3207_, 0);
lean_inc(v_val_3208_);
lean_dec_ref_known(v___x_3207_, 1);
v___y_3174_ = v___y_3202_;
v___y_3175_ = v___y_3204_;
v___y_3176_ = v___y_3206_;
v___y_3177_ = v___y_3205_;
v___y_3178_ = v_val_3208_;
goto v___jp_3173_;
}
}
v___jp_3209_:
{
lean_object* v___x_3213_; 
v___x_3213_ = l_Lean_Elab_Command_getRef___redArg(v___y_3106_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v_a_3214_; lean_object* v_ref_3215_; lean_object* v___x_3216_; 
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
lean_inc(v_a_3214_);
lean_dec_ref_known(v___x_3213_, 1);
v_ref_3215_ = l_Lean_replaceRef(v_ref_3102_, v_a_3214_);
lean_dec(v_a_3214_);
v___x_3216_ = l_Lean_Syntax_getPos_x3f(v_ref_3215_, v___y_3211_);
if (lean_obj_tag(v___x_3216_) == 0)
{
lean_object* v___x_3217_; 
v___x_3217_ = lean_unsigned_to_nat(0u);
v___y_3202_ = v___y_3210_;
v___y_3203_ = v_ref_3215_;
v___y_3204_ = v___y_3212_;
v___y_3205_ = v___y_3211_;
v___y_3206_ = v___x_3217_;
goto v___jp_3201_;
}
else
{
lean_object* v_val_3218_; 
v_val_3218_ = lean_ctor_get(v___x_3216_, 0);
lean_inc(v_val_3218_);
lean_dec_ref_known(v___x_3216_, 1);
v___y_3202_ = v___y_3210_;
v___y_3203_ = v_ref_3215_;
v___y_3204_ = v___y_3212_;
v___y_3205_ = v___y_3211_;
v___y_3206_ = v_val_3218_;
goto v___jp_3201_;
}
}
else
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
lean_dec_ref(v_msgData_3103_);
v_a_3219_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3221_ = v___x_3213_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3213_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3219_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
v___jp_3228_:
{
if (v___y_3231_ == 0)
{
v___y_3210_ = v___y_3229_;
v___y_3211_ = v___y_3230_;
v___y_3212_ = v_severity_3104_;
goto v___jp_3209_;
}
else
{
v___y_3210_ = v___y_3229_;
v___y_3211_ = v___y_3230_;
v___y_3212_ = v___x_3227_;
goto v___jp_3209_;
}
}
v___jp_3232_:
{
if (v___y_3233_ == 0)
{
lean_object* v___x_3234_; lean_object* v_scopes_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v_opts_3238_; uint8_t v___x_3239_; uint8_t v___x_3240_; 
v___x_3234_ = lean_st_ref_get(v___y_3107_);
v_scopes_3235_ = lean_ctor_get(v___x_3234_, 2);
lean_inc(v_scopes_3235_);
lean_dec(v___x_3234_);
v___x_3236_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3237_ = l_List_head_x21___redArg(v___x_3236_, v_scopes_3235_);
lean_dec(v_scopes_3235_);
v_opts_3238_ = lean_ctor_get(v___x_3237_, 1);
lean_inc_ref(v_opts_3238_);
lean_dec(v___x_3237_);
v___x_3239_ = 1;
v___x_3240_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3104_, v___x_3239_);
if (v___x_3240_ == 0)
{
lean_dec_ref(v_opts_3238_);
v___y_3229_ = v___y_3233_;
v___y_3230_ = v___y_3233_;
v___y_3231_ = v___x_3240_;
goto v___jp_3228_;
}
else
{
lean_object* v___x_3241_; uint8_t v___x_3242_; 
v___x_3241_ = l_Lean_warningAsError;
v___x_3242_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_3238_, v___x_3241_);
lean_dec_ref(v_opts_3238_);
v___y_3229_ = v___y_3233_;
v___y_3230_ = v___y_3233_;
v___y_3231_ = v___x_3242_;
goto v___jp_3228_;
}
}
else
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
lean_dec_ref(v_msgData_3103_);
v___x_3243_ = lean_box(0);
v___x_3244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3243_);
return v___x_3244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___boxed(lean_object* v_ref_3247_, lean_object* v_msgData_3248_, lean_object* v_severity_3249_, lean_object* v_isSilent_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
uint8_t v_severity_boxed_3254_; uint8_t v_isSilent_boxed_3255_; lean_object* v_res_3256_; 
v_severity_boxed_3254_ = lean_unbox(v_severity_3249_);
v_isSilent_boxed_3255_ = lean_unbox(v_isSilent_3250_);
v_res_3256_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3247_, v_msgData_3248_, v_severity_boxed_3254_, v_isSilent_boxed_3255_, v___y_3251_, v___y_3252_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v_ref_3247_);
return v_res_3256_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(lean_object* v_ref_3257_, lean_object* v_msgData_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
uint8_t v___x_3262_; uint8_t v___x_3263_; lean_object* v___x_3264_; 
v___x_3262_ = 0;
v___x_3263_ = 0;
v___x_3264_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3257_, v_msgData_3258_, v___x_3262_, v___x_3263_, v___y_3259_, v___y_3260_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0___boxed(lean_object* v_ref_3265_, lean_object* v_msgData_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_){
_start:
{
lean_object* v_res_3270_; 
v_res_3270_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3265_, v_msgData_3266_, v___y_3267_, v___y_3268_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
lean_dec(v_ref_3265_);
return v_res_3270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(lean_object* v___x_3272_, lean_object* v_x_3273_){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3274_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___closed__0));
v___x_3275_ = lean_string_append(v___x_3274_, v___x_3272_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed(lean_object* v___x_3276_, lean_object* v_x_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(v___x_3276_, v_x_3277_);
lean_dec_ref(v_x_3277_);
lean_dec_ref(v___x_3276_);
return v_res_3278_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3280_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__0));
v___x_3281_ = l_Lean_stringToMessageData(v___x_3280_);
return v___x_3281_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3283_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__2));
v___x_3284_ = l_Lean_stringToMessageData(v___x_3283_);
return v___x_3284_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3286_; lean_object* v___x_3287_; 
v___x_3286_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__4));
v___x_3287_ = l_Lean_stringToMessageData(v___x_3286_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(lean_object* v___x_3288_, uint8_t v___x_3289_, lean_object* v___x_3290_, lean_object* v_insertPos_3291_, lean_object* v_cmdLine_3292_, lean_object* v_ref_3293_, size_t v_sz_3294_, size_t v_i_3295_, lean_object* v_bs_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
uint8_t v___x_3300_; 
v___x_3300_ = lean_usize_dec_lt(v_i_3295_, v_sz_3294_);
if (v___x_3300_ == 0)
{
lean_object* v___x_3301_; 
lean_dec_ref(v___x_3290_);
lean_dec_ref(v___x_3288_);
v___x_3301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3301_, 0, v_bs_3296_);
return v___x_3301_;
}
else
{
lean_object* v_v_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v_v_3302_ = lean_array_uget(v_bs_3296_, v_i_3295_);
lean_inc(v_v_3302_);
v___x_3303_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppTactic___boxed), 4, 1);
lean_closure_set(v___x_3303_, 0, v_v_3302_);
v___x_3304_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_3303_, v___y_3297_, v___y_3298_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v_a_3305_; lean_object* v___x_3306_; lean_object* v_bs_x27_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___f_3310_; lean_object* v___x_3311_; 
v_a_3305_ = lean_ctor_get(v___x_3304_, 0);
lean_inc(v_a_3305_);
lean_dec_ref_known(v___x_3304_, 1);
v___x_3306_ = lean_unsigned_to_nat(0u);
v_bs_x27_3307_ = lean_array_uset(v_bs_3296_, v_i_3295_, v___x_3306_);
v___x_3308_ = l_Std_Format_defWidth;
v___x_3309_ = l_Std_Format_pretty(v_a_3305_, v___x_3308_, v___x_3306_, v___x_3306_);
lean_inc_ref(v___x_3309_);
v___f_3310_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3310_, 0, v___x_3309_);
lean_inc_ref(v___x_3288_);
v___x_3311_ = lean_string_append(v___x_3288_, v___x_3309_);
lean_dec_ref(v___x_3309_);
if (v___x_3289_ == 0)
{
goto v___jp_3312_;
}
else
{
lean_object* v___x_3323_; lean_object* v_line_3324_; lean_object* v_column_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3360_; 
lean_inc_ref(v___x_3290_);
v___x_3323_ = l_Lean_FileMap_toPosition(v___x_3290_, v_insertPos_3291_);
v_line_3324_ = lean_ctor_get(v___x_3323_, 0);
v_column_3325_ = lean_ctor_get(v___x_3323_, 1);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3327_ = v___x_3323_;
v_isShared_3328_ = v_isSharedCheck_3360_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_column_3325_);
lean_inc(v_line_3324_);
lean_dec(v___x_3323_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3360_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3337_; 
v___x_3329_ = lean_nat_sub(v_line_3324_, v_cmdLine_3292_);
lean_dec(v_line_3324_);
v___x_3330_ = lean_unsigned_to_nat(1u);
v___x_3331_ = lean_nat_add(v___x_3329_, v___x_3330_);
lean_dec(v___x_3329_);
v___x_3332_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1);
lean_inc_ref(v___x_3311_);
v___x_3333_ = l_String_quote(v___x_3311_);
v___x_3334_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3333_);
v___x_3335_ = l_Lean_MessageData_ofFormat(v___x_3334_);
if (v_isShared_3328_ == 0)
{
lean_ctor_set_tag(v___x_3327_, 7);
lean_ctor_set(v___x_3327_, 1, v___x_3335_);
lean_ctor_set(v___x_3327_, 0, v___x_3332_);
v___x_3337_ = v___x_3327_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v___x_3332_);
lean_ctor_set(v_reuseFailAlloc_3359_, 1, v___x_3335_);
v___x_3337_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3338_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3);
v___x_3339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3337_);
lean_ctor_set(v___x_3339_, 1, v___x_3338_);
v___x_3340_ = l_Nat_reprFast(v___x_3331_);
v___x_3341_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3340_);
v___x_3342_ = l_Lean_MessageData_ofFormat(v___x_3341_);
v___x_3343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3339_);
lean_ctor_set(v___x_3343_, 1, v___x_3342_);
v___x_3344_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5);
v___x_3345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3343_);
lean_ctor_set(v___x_3345_, 1, v___x_3344_);
v___x_3346_ = l_Nat_reprFast(v_column_3325_);
v___x_3347_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3346_);
v___x_3348_ = l_Lean_MessageData_ofFormat(v___x_3347_);
v___x_3349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3345_);
lean_ctor_set(v___x_3349_, 1, v___x_3348_);
v___x_3350_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3293_, v___x_3349_, v___y_3297_, v___y_3298_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_dec_ref_known(v___x_3350_, 1);
goto v___jp_3312_;
}
else
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3358_; 
lean_dec_ref(v___x_3311_);
lean_dec_ref(v___f_3310_);
lean_dec_ref(v_bs_x27_3307_);
lean_dec(v_v_3302_);
lean_dec_ref(v___x_3290_);
lean_dec_ref(v___x_3288_);
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3353_ = v___x_3350_;
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3350_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3356_; 
if (v_isShared_3354_ == 0)
{
v___x_3356_ = v___x_3353_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_a_3351_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
}
}
}
v___jp_3312_:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; size_t v___x_3319_; size_t v___x_3320_; lean_object* v___x_3321_; 
v___x_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3311_);
v___x_3314_ = lean_box(0);
v___x_3315_ = l_Lean_MessageData_ofSyntax(v_v_3302_);
v___x_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3315_);
v___x_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3317_, 0, v___f_3310_);
v___x_3318_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3313_);
lean_ctor_set(v___x_3318_, 1, v___x_3314_);
lean_ctor_set(v___x_3318_, 2, v___x_3314_);
lean_ctor_set(v___x_3318_, 3, v___x_3314_);
lean_ctor_set(v___x_3318_, 4, v___x_3316_);
lean_ctor_set(v___x_3318_, 5, v___x_3317_);
v___x_3319_ = ((size_t)1ULL);
v___x_3320_ = lean_usize_add(v_i_3295_, v___x_3319_);
v___x_3321_ = lean_array_uset(v_bs_x27_3307_, v_i_3295_, v___x_3318_);
v_i_3295_ = v___x_3320_;
v_bs_3296_ = v___x_3321_;
goto _start;
}
}
else
{
lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3368_; 
lean_dec(v_v_3302_);
lean_dec_ref(v_bs_3296_);
lean_dec_ref(v___x_3290_);
lean_dec_ref(v___x_3288_);
v_a_3361_ = lean_ctor_get(v___x_3304_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3363_ = v___x_3304_;
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3304_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3366_; 
if (v_isShared_3364_ == 0)
{
v___x_3366_ = v___x_3363_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3361_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___boxed(lean_object* v___x_3369_, lean_object* v___x_3370_, lean_object* v___x_3371_, lean_object* v_insertPos_3372_, lean_object* v_cmdLine_3373_, lean_object* v_ref_3374_, lean_object* v_sz_3375_, lean_object* v_i_3376_, lean_object* v_bs_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
uint8_t v___x_4299__boxed_3381_; size_t v_sz_boxed_3382_; size_t v_i_boxed_3383_; lean_object* v_res_3384_; 
v___x_4299__boxed_3381_ = lean_unbox(v___x_3370_);
v_sz_boxed_3382_ = lean_unbox_usize(v_sz_3375_);
lean_dec(v_sz_3375_);
v_i_boxed_3383_ = lean_unbox_usize(v_i_3376_);
lean_dec(v_i_3376_);
v_res_3384_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3369_, v___x_4299__boxed_3381_, v___x_3371_, v_insertPos_3372_, v_cmdLine_3373_, v_ref_3374_, v_sz_boxed_3382_, v_i_boxed_3383_, v_bs_3377_, v___y_3378_, v___y_3379_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v_ref_3374_);
lean_dec(v_cmdLine_3373_);
lean_dec(v_insertPos_3372_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(lean_object* v_tacticSeq_3385_, lean_object* v_ref_3386_, lean_object* v_insertPos_3387_, lean_object* v_suggs_3388_, lean_object* v_cmdLine_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_){
_start:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; uint8_t v___x_3395_; 
v___x_3393_ = lean_array_get_size(v_suggs_3388_);
v___x_3394_ = lean_unsigned_to_nat(0u);
v___x_3395_ = lean_nat_dec_eq(v___x_3393_, v___x_3394_);
if (v___x_3395_ == 0)
{
lean_object* v___x_3396_; lean_object* v_fileMap_3397_; lean_object* v_scopes_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v_opts_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; uint8_t v___x_3404_; size_t v_sz_3405_; size_t v___x_3406_; lean_object* v___x_3407_; 
v___x_3396_ = lean_st_ref_get(v_a_3391_);
v_fileMap_3397_ = lean_ctor_get(v_a_3390_, 1);
v_scopes_3398_ = lean_ctor_get(v___x_3396_, 2);
lean_inc(v_scopes_3398_);
lean_dec(v___x_3396_);
v___x_3399_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3400_ = l_List_head_x21___redArg(v___x_3399_, v_scopes_3398_);
lean_dec(v_scopes_3398_);
v_opts_3401_ = lean_ctor_get(v___x_3400_, 1);
lean_inc_ref(v_opts_3401_);
lean_dec(v___x_3400_);
lean_inc_ref_n(v_fileMap_3397_, 2);
v___x_3402_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(v_tacticSeq_3385_, v_fileMap_3397_);
v___x_3403_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_debug_autoTry_showEdits;
v___x_3404_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_3401_, v___x_3403_);
lean_dec_ref(v_opts_3401_);
v_sz_3405_ = lean_array_size(v_suggs_3388_);
v___x_3406_ = ((size_t)0ULL);
v___x_3407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3402_, v___x_3404_, v_fileMap_3397_, v_insertPos_3387_, v_cmdLine_3389_, v_ref_3386_, v_sz_3405_, v___x_3406_, v_suggs_3388_, v_a_3390_, v_a_3391_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; uint8_t v___x_3412_; lean_object* v___x_3413_; lean_object* v___y_3414_; lean_object* v___x_3415_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3408_);
lean_dec_ref_known(v___x_3407_, 1);
v___x_3409_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx(v_insertPos_3387_);
v___x_3410_ = lean_array_get_size(v_a_3408_);
v___x_3411_ = lean_unsigned_to_nat(1u);
v___x_3412_ = lean_nat_dec_eq(v___x_3410_, v___x_3411_);
v___x_3413_ = lean_box(v___x_3412_);
v___y_3414_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed), 8, 5);
lean_closure_set(v___y_3414_, 0, v___x_3413_);
lean_closure_set(v___y_3414_, 1, v___x_3409_);
lean_closure_set(v___y_3414_, 2, v_ref_3386_);
lean_closure_set(v___y_3414_, 3, v_a_3408_);
lean_closure_set(v___y_3414_, 4, v___x_3394_);
v___x_3415_ = l_Lean_Elab_Command_liftCoreM___redArg(v___y_3414_, v_a_3390_, v_a_3391_);
return v___x_3415_;
}
else
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3423_; 
lean_dec(v_insertPos_3387_);
lean_dec(v_ref_3386_);
v_a_3416_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3418_ = v___x_3407_;
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3407_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_a_3416_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
else
{
lean_object* v___x_3424_; lean_object* v___x_3425_; 
lean_dec_ref(v_suggs_3388_);
lean_dec(v_insertPos_3387_);
lean_dec(v_ref_3386_);
v___x_3424_ = lean_box(0);
v___x_3425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3424_);
return v___x_3425_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___boxed(lean_object* v_tacticSeq_3426_, lean_object* v_ref_3427_, lean_object* v_insertPos_3428_, lean_object* v_suggs_3429_, lean_object* v_cmdLine_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_){
_start:
{
lean_object* v_res_3434_; 
v_res_3434_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(v_tacticSeq_3426_, v_ref_3427_, v_insertPos_3428_, v_suggs_3429_, v_cmdLine_3430_, v_a_3431_, v_a_3432_);
lean_dec(v_a_3432_);
lean_dec_ref(v_a_3431_);
lean_dec(v_cmdLine_3430_);
lean_dec(v_tacticSeq_3426_);
return v_res_3434_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(lean_object* v_x_3435_){
_start:
{
uint8_t v___x_3436_; 
v___x_3436_ = 0;
return v___x_3436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0___boxed(lean_object* v_x_3437_){
_start:
{
uint8_t v_res_3438_; lean_object* v_r_3439_; 
v_res_3438_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(v_x_3437_);
lean_dec(v_x_3437_);
v_r_3439_ = lean_box(v_res_3438_);
return v_r_3439_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7(void){
_start:
{
lean_object* v___x_3456_; 
v___x_3456_ = l_Array_mkArray0(lean_box(0));
return v___x_3456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(lean_object* v___f_3460_, lean_object* v_ref_3461_, lean_object* v_goal_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
lean_object* v_fileName_3468_; lean_object* v_fileMap_3469_; lean_object* v_options_3470_; lean_object* v_currRecDepth_3471_; lean_object* v_maxRecDepth_3472_; lean_object* v_ref_3473_; lean_object* v_currNamespace_3474_; lean_object* v_openDecls_3475_; lean_object* v_initHeartbeats_3476_; lean_object* v_maxHeartbeats_3477_; lean_object* v_quotContext_3478_; lean_object* v_currMacroScope_3479_; uint8_t v_diag_3480_; lean_object* v_cancelTk_x3f_3481_; uint8_t v_suppressElabErrors_3482_; lean_object* v_inheritedTraceOptions_3483_; uint8_t v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; uint8_t v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v_ref_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v_fileName_3468_ = lean_ctor_get(v___y_3465_, 0);
v_fileMap_3469_ = lean_ctor_get(v___y_3465_, 1);
v_options_3470_ = lean_ctor_get(v___y_3465_, 2);
v_currRecDepth_3471_ = lean_ctor_get(v___y_3465_, 3);
v_maxRecDepth_3472_ = lean_ctor_get(v___y_3465_, 4);
v_ref_3473_ = lean_ctor_get(v___y_3465_, 5);
v_currNamespace_3474_ = lean_ctor_get(v___y_3465_, 6);
v_openDecls_3475_ = lean_ctor_get(v___y_3465_, 7);
v_initHeartbeats_3476_ = lean_ctor_get(v___y_3465_, 8);
v_maxHeartbeats_3477_ = lean_ctor_get(v___y_3465_, 9);
v_quotContext_3478_ = lean_ctor_get(v___y_3465_, 10);
v_currMacroScope_3479_ = lean_ctor_get(v___y_3465_, 11);
v_diag_3480_ = lean_ctor_get_uint8(v___y_3465_, sizeof(void*)*14);
v_cancelTk_x3f_3481_ = lean_ctor_get(v___y_3465_, 12);
v_suppressElabErrors_3482_ = lean_ctor_get_uint8(v___y_3465_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3483_ = lean_ctor_get(v___y_3465_, 13);
v___x_3484_ = 0;
v___x_3485_ = l_Lean_SourceInfo_fromRef(v_ref_3473_, v___x_3484_);
v___x_3486_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__1));
v___x_3487_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__2));
lean_inc_n(v___x_3485_, 3);
v___x_3488_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3485_);
lean_ctor_set(v___x_3488_, 1, v___x_3487_);
v___x_3489_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__4));
v___x_3490_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__6));
v___x_3491_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7);
v___x_3492_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3485_);
lean_ctor_set(v___x_3492_, 1, v___x_3490_);
lean_ctor_set(v___x_3492_, 2, v___x_3491_);
v___x_3493_ = l_Lean_Syntax_node1(v___x_3485_, v___x_3489_, v___x_3492_);
v___x_3494_ = l_Lean_Syntax_node2(v___x_3485_, v___x_3486_, v___x_3488_, v___x_3493_);
v___x_3495_ = lean_box(0);
v___x_3496_ = lean_box(0);
v___x_3497_ = 1;
v___x_3498_ = lean_box(1);
v___x_3499_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__5));
v___x_3500_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_3500_, 0, v___x_3495_);
lean_ctor_set(v___x_3500_, 1, v___x_3496_);
lean_ctor_set(v___x_3500_, 2, v___x_3495_);
lean_ctor_set(v___x_3500_, 3, v___f_3460_);
lean_ctor_set(v___x_3500_, 4, v___x_3498_);
lean_ctor_set(v___x_3500_, 5, v___x_3498_);
lean_ctor_set(v___x_3500_, 6, v___x_3495_);
lean_ctor_set(v___x_3500_, 7, v___x_3499_);
lean_ctor_set_uint8(v___x_3500_, sizeof(void*)*8, v___x_3497_);
lean_ctor_set_uint8(v___x_3500_, sizeof(void*)*8 + 1, v___x_3497_);
lean_ctor_set_uint8(v___x_3500_, sizeof(void*)*8 + 2, v___x_3497_);
lean_ctor_set_uint8(v___x_3500_, sizeof(void*)*8 + 3, v___x_3497_);
lean_ctor_set_uint8(v___x_3500_, sizeof(void*)*8 + 4, v___x_3484_);
lean_ctor_set_uint8(v___x_3500_, sizeof(void*)*8 + 5, v___x_3484_);
lean_ctor_set_uint8(v___x_3500_, sizeof(void*)*8 + 6, v___x_3484_);
lean_ctor_set_uint8(v___x_3500_, sizeof(void*)*8 + 7, v___x_3484_);
lean_ctor_set_uint8(v___x_3500_, sizeof(void*)*8 + 8, v___x_3497_);
lean_ctor_set_uint8(v___x_3500_, sizeof(void*)*8 + 9, v___x_3484_);
lean_ctor_set_uint8(v___x_3500_, sizeof(void*)*8 + 10, v___x_3497_);
v___x_3501_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__8));
v_ref_3502_ = l_Lean_replaceRef(v_ref_3461_, v_ref_3473_);
lean_inc_ref(v_inheritedTraceOptions_3483_);
lean_inc(v_cancelTk_x3f_3481_);
lean_inc(v_currMacroScope_3479_);
lean_inc(v_quotContext_3478_);
lean_inc(v_maxHeartbeats_3477_);
lean_inc(v_initHeartbeats_3476_);
lean_inc(v_openDecls_3475_);
lean_inc(v_currNamespace_3474_);
lean_inc(v_maxRecDepth_3472_);
lean_inc(v_currRecDepth_3471_);
lean_inc_ref(v_options_3470_);
lean_inc_ref(v_fileMap_3469_);
lean_inc_ref(v_fileName_3468_);
v___x_3503_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3503_, 0, v_fileName_3468_);
lean_ctor_set(v___x_3503_, 1, v_fileMap_3469_);
lean_ctor_set(v___x_3503_, 2, v_options_3470_);
lean_ctor_set(v___x_3503_, 3, v_currRecDepth_3471_);
lean_ctor_set(v___x_3503_, 4, v_maxRecDepth_3472_);
lean_ctor_set(v___x_3503_, 5, v_ref_3502_);
lean_ctor_set(v___x_3503_, 6, v_currNamespace_3474_);
lean_ctor_set(v___x_3503_, 7, v_openDecls_3475_);
lean_ctor_set(v___x_3503_, 8, v_initHeartbeats_3476_);
lean_ctor_set(v___x_3503_, 9, v_maxHeartbeats_3477_);
lean_ctor_set(v___x_3503_, 10, v_quotContext_3478_);
lean_ctor_set(v___x_3503_, 11, v_currMacroScope_3479_);
lean_ctor_set(v___x_3503_, 12, v_cancelTk_x3f_3481_);
lean_ctor_set(v___x_3503_, 13, v_inheritedTraceOptions_3483_);
lean_ctor_set_uint8(v___x_3503_, sizeof(void*)*14, v_diag_3480_);
lean_ctor_set_uint8(v___x_3503_, sizeof(void*)*14 + 1, v_suppressElabErrors_3482_);
v___x_3504_ = l_Lean_Elab_runTactic(v_goal_3462_, v___x_3494_, v___x_3500_, v___x_3501_, v___y_3463_, v___y_3464_, v___x_3503_, v___y_3466_);
lean_dec_ref_known(v___x_3503_, 14);
if (lean_obj_tag(v___x_3504_) == 0)
{
lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3512_; 
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3512_ == 0)
{
lean_object* v_unused_3513_; 
v_unused_3513_ = lean_ctor_get(v___x_3504_, 0);
lean_dec(v_unused_3513_);
v___x_3506_ = v___x_3504_;
v_isShared_3507_ = v_isSharedCheck_3512_;
goto v_resetjp_3505_;
}
else
{
lean_dec(v___x_3504_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3512_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3508_; lean_object* v___x_3510_; 
v___x_3508_ = lean_box(0);
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 0, v___x_3508_);
v___x_3510_ = v___x_3506_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v___x_3508_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
else
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3540_; 
v_a_3514_ = lean_ctor_get(v___x_3504_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3516_ = v___x_3504_;
v_isShared_3517_ = v_isSharedCheck_3540_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3504_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3540_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3523_; uint8_t v___y_3525_; uint8_t v___y_3535_; uint8_t v___x_3538_; 
lean_inc(v_a_3514_);
v___x_3523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3523_, 0, v_a_3514_);
v___x_3538_ = l_Lean_Exception_isInterrupt(v_a_3514_);
if (v___x_3538_ == 0)
{
uint8_t v___x_3539_; 
lean_inc(v_a_3514_);
v___x_3539_ = l_Lean_Exception_isRuntime(v_a_3514_);
v___y_3535_ = v___x_3539_;
goto v___jp_3534_;
}
else
{
v___y_3535_ = v___x_3538_;
goto v___jp_3534_;
}
v___jp_3518_:
{
lean_object* v___x_3519_; lean_object* v___x_3521_; 
v___x_3519_ = lean_box(0);
if (v_isShared_3517_ == 0)
{
lean_ctor_set_tag(v___x_3516_, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3519_);
v___x_3521_ = v___x_3516_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v___x_3519_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
v___jp_3524_:
{
if (v___y_3525_ == 0)
{
uint8_t v_hasTrace_3526_; 
lean_dec_ref_known(v___x_3523_, 1);
v_hasTrace_3526_ = lean_ctor_get_uint8(v_options_3470_, sizeof(void*)*1);
if (v_hasTrace_3526_ == 0)
{
lean_dec(v_a_3514_);
goto v___jp_3518_;
}
else
{
lean_object* v___x_3527_; lean_object* v___x_3528_; uint8_t v___x_3529_; 
v___x_3527_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3528_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_3529_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3483_, v_options_3470_, v___x_3528_);
if (v___x_3529_ == 0)
{
lean_dec(v_a_3514_);
goto v___jp_3518_;
}
else
{
lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
lean_del_object(v___x_3516_);
v___x_3530_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_3531_ = l_Lean_Exception_toMessageData(v_a_3514_);
v___x_3532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3530_);
lean_ctor_set(v___x_3532_, 1, v___x_3531_);
v___x_3533_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_3527_, v___x_3532_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
return v___x_3533_;
}
}
}
else
{
lean_del_object(v___x_3516_);
lean_dec(v_a_3514_);
return v___x_3523_;
}
}
v___jp_3534_:
{
if (v___y_3535_ == 0)
{
uint8_t v___x_3536_; 
v___x_3536_ = l_Lean_Exception_isInterrupt(v_a_3514_);
if (v___x_3536_ == 0)
{
uint8_t v___x_3537_; 
lean_inc(v_a_3514_);
v___x_3537_ = l_Lean_Exception_isMaxRecDepth(v_a_3514_);
v___y_3525_ = v___x_3537_;
goto v___jp_3524_;
}
else
{
v___y_3525_ = v___x_3536_;
goto v___jp_3524_;
}
}
else
{
lean_del_object(v___x_3516_);
lean_dec(v_a_3514_);
return v___x_3523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___boxed(lean_object* v___f_3541_, lean_object* v_ref_3542_, lean_object* v_goal_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v_res_3549_; 
v_res_3549_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(v___f_3541_, v_ref_3542_, v_goal_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_);
lean_dec(v___y_3547_);
lean_dec_ref(v___y_3546_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
lean_dec(v_ref_3542_);
return v_res_3549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(lean_object* v_c_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_){
_start:
{
lean_object* v_mctx_3555_; lean_object* v_ref_3556_; lean_object* v_env_3557_; lean_object* v_opts_3558_; lean_object* v_namingCtx_3559_; lean_object* v_goal_3560_; lean_object* v_decls_3561_; lean_object* v___x_3562_; 
v_mctx_3555_ = lean_ctor_get(v_c_3551_, 3);
lean_inc_ref(v_mctx_3555_);
v_ref_3556_ = lean_ctor_get(v_c_3551_, 1);
lean_inc(v_ref_3556_);
v_env_3557_ = lean_ctor_get(v_c_3551_, 2);
lean_inc_ref(v_env_3557_);
v_opts_3558_ = lean_ctor_get(v_c_3551_, 4);
lean_inc_ref(v_opts_3558_);
v_namingCtx_3559_ = lean_ctor_get(v_c_3551_, 5);
lean_inc_ref(v_namingCtx_3559_);
v_goal_3560_ = lean_ctor_get(v_c_3551_, 6);
lean_inc(v_goal_3560_);
lean_dec_ref(v_c_3551_);
v_decls_3561_ = lean_ctor_get(v_mctx_3555_, 5);
v___x_3562_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_decls_3561_, v_goal_3560_);
if (lean_obj_tag(v___x_3562_) == 1)
{
lean_object* v_val_3563_; lean_object* v_lctx_3564_; lean_object* v___f_3565_; lean_object* v___f_3566_; lean_object* v___x_3567_; 
v_val_3563_ = lean_ctor_get(v___x_3562_, 0);
lean_inc(v_val_3563_);
lean_dec_ref_known(v___x_3562_, 1);
v_lctx_3564_ = lean_ctor_get(v_val_3563_, 1);
lean_inc_ref(v_lctx_3564_);
lean_dec(v_val_3563_);
v___f_3565_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___closed__0));
v___f_3566_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___boxed), 8, 3);
lean_closure_set(v___f_3566_, 0, v___f_3565_);
lean_closure_set(v___f_3566_, 1, v_ref_3556_);
lean_closure_set(v___f_3566_, 2, v_goal_3560_);
v___x_3567_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_3557_, v_mctx_3555_, v_lctx_3564_, v_opts_3558_, v_namingCtx_3559_, v___f_3566_, v_a_3552_, v_a_3553_);
lean_dec_ref(v_namingCtx_3559_);
return v___x_3567_;
}
else
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
lean_dec(v___x_3562_);
lean_dec(v_goal_3560_);
lean_dec_ref(v_namingCtx_3559_);
lean_dec_ref(v_opts_3558_);
lean_dec_ref(v_env_3557_);
lean_dec(v_ref_3556_);
lean_dec_ref(v_mctx_3555_);
v___x_3568_ = lean_box(0);
v___x_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3568_);
return v___x_3569_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___boxed(lean_object* v_c_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(v_c_3570_, v_a_3571_, v_a_3572_);
lean_dec(v_a_3572_);
lean_dec_ref(v_a_3571_);
return v_res_3574_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(lean_object* v___x_3575_, lean_object* v_val_3576_, lean_object* v_as_3577_, size_t v_i_3578_, size_t v_stop_3579_){
_start:
{
uint8_t v___x_3584_; uint8_t v___x_3585_; 
v___x_3584_ = 0;
v___x_3585_ = lean_usize_dec_eq(v_i_3578_, v_stop_3579_);
if (v___x_3585_ == 0)
{
lean_object* v___x_3586_; lean_object* v_pos_3587_; uint8_t v_severity_3588_; lean_object* v_data_3589_; lean_object* v___f_3590_; uint8_t v___x_3591_; lean_object* v___x_3592_; uint8_t v___x_3593_; uint8_t v___y_3595_; 
v___x_3586_ = lean_array_uget_borrowed(v_as_3577_, v_i_3578_);
v_pos_3587_ = lean_ctor_get(v___x_3586_, 1);
v_severity_3588_ = lean_ctor_get_uint8(v___x_3586_, sizeof(void*)*5 + 1);
v_data_3589_ = lean_ctor_get(v___x_3586_, 4);
v___f_3590_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
v___x_3591_ = 1;
lean_inc_ref(v_pos_3587_);
v___x_3592_ = l_Lean_FileMap_ofPosition(v___x_3575_, v_pos_3587_);
v___x_3593_ = l_Lean_Syntax_Range_contains(v_val_3576_, v___x_3592_, v___x_3591_);
lean_dec(v___x_3592_);
if (v_severity_3588_ == 2)
{
v___y_3595_ = v___x_3591_;
goto v___jp_3594_;
}
else
{
v___y_3595_ = v___x_3584_;
goto v___jp_3594_;
}
v___jp_3594_:
{
if (v___x_3593_ == 0)
{
goto v___jp_3580_;
}
else
{
if (v___y_3595_ == 0)
{
goto v___jp_3580_;
}
else
{
uint8_t v___x_3596_; 
lean_inc(v_data_3589_);
v___x_3596_ = l_Lean_MessageData_hasTag(v___f_3590_, v_data_3589_);
if (v___x_3596_ == 0)
{
return v___x_3591_;
}
else
{
if (v___x_3585_ == 0)
{
goto v___jp_3580_;
}
else
{
return v___x_3591_;
}
}
}
}
}
}
else
{
return v___x_3584_;
}
v___jp_3580_:
{
size_t v___x_3581_; size_t v___x_3582_; 
v___x_3581_ = ((size_t)1ULL);
v___x_3582_ = lean_usize_add(v_i_3578_, v___x_3581_);
v_i_3578_ = v___x_3582_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1___boxed(lean_object* v___x_3597_, lean_object* v_val_3598_, lean_object* v_as_3599_, lean_object* v_i_3600_, lean_object* v_stop_3601_){
_start:
{
size_t v_i_boxed_3602_; size_t v_stop_boxed_3603_; uint8_t v_res_3604_; lean_object* v_r_3605_; 
v_i_boxed_3602_ = lean_unbox_usize(v_i_3600_);
lean_dec(v_i_3600_);
v_stop_boxed_3603_ = lean_unbox_usize(v_stop_3601_);
lean_dec(v_stop_3601_);
v_res_3604_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3597_, v_val_3598_, v_as_3599_, v_i_boxed_3602_, v_stop_boxed_3603_);
lean_dec_ref(v_as_3599_);
lean_dec_ref(v_val_3598_);
lean_dec_ref(v___x_3597_);
v_r_3605_ = lean_box(v_res_3604_);
return v_r_3605_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(lean_object* v___x_3606_, lean_object* v_val_3607_, lean_object* v_x_3608_){
_start:
{
if (lean_obj_tag(v_x_3608_) == 0)
{
lean_object* v_cs_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; uint8_t v___x_3612_; 
v_cs_3609_ = lean_ctor_get(v_x_3608_, 0);
v___x_3610_ = lean_unsigned_to_nat(0u);
v___x_3611_ = lean_array_get_size(v_cs_3609_);
v___x_3612_ = lean_nat_dec_lt(v___x_3610_, v___x_3611_);
if (v___x_3612_ == 0)
{
return v___x_3612_;
}
else
{
if (v___x_3612_ == 0)
{
return v___x_3612_;
}
else
{
size_t v___x_3613_; size_t v___x_3614_; uint8_t v___x_3615_; 
v___x_3613_ = ((size_t)0ULL);
v___x_3614_ = lean_usize_of_nat(v___x_3611_);
v___x_3615_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3606_, v_val_3607_, v_cs_3609_, v___x_3613_, v___x_3614_);
return v___x_3615_;
}
}
}
else
{
lean_object* v_vs_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; uint8_t v___x_3619_; 
v_vs_3616_ = lean_ctor_get(v_x_3608_, 0);
v___x_3617_ = lean_unsigned_to_nat(0u);
v___x_3618_ = lean_array_get_size(v_vs_3616_);
v___x_3619_ = lean_nat_dec_lt(v___x_3617_, v___x_3618_);
if (v___x_3619_ == 0)
{
return v___x_3619_;
}
else
{
if (v___x_3619_ == 0)
{
return v___x_3619_;
}
else
{
size_t v___x_3620_; size_t v___x_3621_; uint8_t v___x_3622_; 
v___x_3620_ = ((size_t)0ULL);
v___x_3621_ = lean_usize_of_nat(v___x_3618_);
v___x_3622_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3606_, v_val_3607_, v_vs_3616_, v___x_3620_, v___x_3621_);
return v___x_3622_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(lean_object* v___x_3623_, lean_object* v_val_3624_, lean_object* v_as_3625_, size_t v_i_3626_, size_t v_stop_3627_){
_start:
{
uint8_t v___x_3628_; 
v___x_3628_ = lean_usize_dec_eq(v_i_3626_, v_stop_3627_);
if (v___x_3628_ == 0)
{
lean_object* v___x_3629_; uint8_t v___x_3630_; 
v___x_3629_ = lean_array_uget_borrowed(v_as_3625_, v_i_3626_);
v___x_3630_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3623_, v_val_3624_, v___x_3629_);
if (v___x_3630_ == 0)
{
size_t v___x_3631_; size_t v___x_3632_; 
v___x_3631_ = ((size_t)1ULL);
v___x_3632_ = lean_usize_add(v_i_3626_, v___x_3631_);
v_i_3626_ = v___x_3632_;
goto _start;
}
else
{
return v___x_3630_;
}
}
else
{
uint8_t v___x_3634_; 
v___x_3634_ = 0;
return v___x_3634_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3635_, lean_object* v_val_3636_, lean_object* v_as_3637_, lean_object* v_i_3638_, lean_object* v_stop_3639_){
_start:
{
size_t v_i_boxed_3640_; size_t v_stop_boxed_3641_; uint8_t v_res_3642_; lean_object* v_r_3643_; 
v_i_boxed_3640_ = lean_unbox_usize(v_i_3638_);
lean_dec(v_i_3638_);
v_stop_boxed_3641_ = lean_unbox_usize(v_stop_3639_);
lean_dec(v_stop_3639_);
v_res_3642_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3635_, v_val_3636_, v_as_3637_, v_i_boxed_3640_, v_stop_boxed_3641_);
lean_dec_ref(v_as_3637_);
lean_dec_ref(v_val_3636_);
lean_dec_ref(v___x_3635_);
v_r_3643_ = lean_box(v_res_3642_);
return v_r_3643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0___boxed(lean_object* v___x_3644_, lean_object* v_val_3645_, lean_object* v_x_3646_){
_start:
{
uint8_t v_res_3647_; lean_object* v_r_3648_; 
v_res_3647_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3644_, v_val_3645_, v_x_3646_);
lean_dec_ref(v_x_3646_);
lean_dec_ref(v_val_3645_);
lean_dec_ref(v___x_3644_);
v_r_3648_ = lean_box(v_res_3647_);
return v_r_3648_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(lean_object* v___x_3649_, lean_object* v_val_3650_, lean_object* v_t_3651_){
_start:
{
lean_object* v_root_3652_; lean_object* v_tail_3653_; uint8_t v___x_3654_; 
v_root_3652_ = lean_ctor_get(v_t_3651_, 0);
v_tail_3653_ = lean_ctor_get(v_t_3651_, 1);
v___x_3654_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3649_, v_val_3650_, v_root_3652_);
if (v___x_3654_ == 0)
{
lean_object* v___x_3655_; lean_object* v___x_3656_; uint8_t v___x_3657_; 
v___x_3655_ = lean_unsigned_to_nat(0u);
v___x_3656_ = lean_array_get_size(v_tail_3653_);
v___x_3657_ = lean_nat_dec_lt(v___x_3655_, v___x_3656_);
if (v___x_3657_ == 0)
{
return v___x_3654_;
}
else
{
if (v___x_3657_ == 0)
{
return v___x_3654_;
}
else
{
size_t v___x_3658_; size_t v___x_3659_; uint8_t v___x_3660_; 
v___x_3658_ = ((size_t)0ULL);
v___x_3659_ = lean_usize_of_nat(v___x_3656_);
v___x_3660_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3649_, v_val_3650_, v_tail_3653_, v___x_3658_, v___x_3659_);
return v___x_3660_;
}
}
}
else
{
return v___x_3654_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0___boxed(lean_object* v___x_3661_, lean_object* v_val_3662_, lean_object* v_t_3663_){
_start:
{
uint8_t v_res_3664_; lean_object* v_r_3665_; 
v_res_3664_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v___x_3661_, v_val_3662_, v_t_3663_);
lean_dec_ref(v_t_3663_);
lean_dec_ref(v_val_3662_);
lean_dec_ref(v___x_3661_);
v_r_3665_ = lean_box(v_res_3664_);
return v_r_3665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(lean_object* v_stx_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_){
_start:
{
uint8_t v___x_3670_; lean_object* v___x_3671_; 
v___x_3670_ = 0;
v___x_3671_ = l_Lean_Syntax_getRange_x3f(v_stx_3666_, v___x_3670_);
if (lean_obj_tag(v___x_3671_) == 1)
{
lean_object* v_val_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3685_; 
v_val_3672_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3674_ = v___x_3671_;
v_isShared_3675_ = v_isSharedCheck_3685_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_val_3672_);
lean_dec(v___x_3671_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3685_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3676_; lean_object* v_fileMap_3677_; lean_object* v_messages_3678_; lean_object* v___x_3679_; uint8_t v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3683_; 
v___x_3676_ = lean_st_ref_get(v_a_3668_);
v_fileMap_3677_ = lean_ctor_get(v_a_3667_, 1);
v_messages_3678_ = lean_ctor_get(v___x_3676_, 1);
lean_inc_ref(v_messages_3678_);
lean_dec(v___x_3676_);
v___x_3679_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_3678_);
v___x_3680_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v_fileMap_3677_, v_val_3672_, v___x_3679_);
lean_dec_ref(v___x_3679_);
lean_dec(v_val_3672_);
v___x_3681_ = lean_box(v___x_3680_);
if (v_isShared_3675_ == 0)
{
lean_ctor_set_tag(v___x_3674_, 0);
lean_ctor_set(v___x_3674_, 0, v___x_3681_);
v___x_3683_ = v___x_3674_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v___x_3681_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
else
{
lean_object* v___x_3686_; lean_object* v___x_3687_; 
lean_dec(v___x_3671_);
v___x_3686_ = lean_box(v___x_3670_);
v___x_3687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3686_);
return v___x_3687_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError___boxed(lean_object* v_stx_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_){
_start:
{
lean_object* v_res_3692_; 
v_res_3692_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(v_stx_3688_, v_a_3689_, v_a_3690_);
lean_dec(v_a_3690_);
lean_dec_ref(v_a_3689_);
lean_dec(v_stx_3688_);
return v_res_3692_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(lean_object* v_tree_3693_, lean_object* v_fileMap_3694_, lean_object* v_c_3695_){
_start:
{
lean_object* v___y_3697_; lean_object* v_kind_3701_; lean_object* v_ref_3702_; lean_object* v___y_3704_; 
v_kind_3701_ = lean_ctor_get(v_c_3695_, 0);
lean_inc(v_kind_3701_);
v_ref_3702_ = lean_ctor_get(v_c_3695_, 1);
lean_inc(v_ref_3702_);
lean_dec_ref(v_c_3695_);
if (lean_obj_tag(v_kind_3701_) == 0)
{
lean_object* v_insertPos_3720_; 
lean_dec(v_ref_3702_);
v_insertPos_3720_ = lean_ctor_get(v_kind_3701_, 1);
lean_inc(v_insertPos_3720_);
v___y_3704_ = v_insertPos_3720_;
goto v___jp_3703_;
}
else
{
uint8_t v___x_3721_; lean_object* v___x_3722_; 
v___x_3721_ = 0;
v___x_3722_ = l_Lean_Syntax_getPos_x3f(v_ref_3702_, v___x_3721_);
lean_dec(v_ref_3702_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v___x_3723_; 
v___x_3723_ = lean_unsigned_to_nat(0u);
v___y_3704_ = v___x_3723_;
goto v___jp_3703_;
}
else
{
lean_object* v_val_3724_; 
v_val_3724_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_val_3724_);
lean_dec_ref_known(v___x_3722_, 1);
v___y_3704_ = v_val_3724_;
goto v___jp_3703_;
}
}
v___jp_3696_:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; uint8_t v___x_3700_; 
v___x_3698_ = l_List_lengthTR___redArg(v___y_3697_);
lean_dec(v___y_3697_);
v___x_3699_ = lean_unsigned_to_nat(1u);
v___x_3700_ = lean_nat_dec_eq(v___x_3698_, v___x_3699_);
lean_dec(v___x_3698_);
return v___x_3700_;
}
v___jp_3703_:
{
lean_object* v___x_3705_; 
v___x_3705_ = l_Lean_Elab_InfoTree_goalsAt_x3f(v_fileMap_3694_, v_tree_3693_, v___y_3704_);
if (lean_obj_tag(v___x_3705_) == 1)
{
lean_object* v_tail_3706_; 
v_tail_3706_ = lean_ctor_get(v___x_3705_, 1);
lean_inc(v_tail_3706_);
if (lean_obj_tag(v_tail_3706_) == 0)
{
if (lean_obj_tag(v_kind_3701_) == 0)
{
lean_object* v_head_3707_; lean_object* v_tacticSeq_3708_; uint8_t v___x_3709_; lean_object* v___x_3710_; 
v_head_3707_ = lean_ctor_get(v___x_3705_, 0);
lean_inc(v_head_3707_);
lean_dec_ref_known(v___x_3705_, 2);
v_tacticSeq_3708_ = lean_ctor_get(v_kind_3701_, 0);
lean_inc(v_tacticSeq_3708_);
lean_dec_ref_known(v_kind_3701_, 2);
v___x_3709_ = 0;
v___x_3710_ = l_Lean_Syntax_getPos_x3f(v_tacticSeq_3708_, v___x_3709_);
lean_dec(v_tacticSeq_3708_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v_tacticInfo_3711_; lean_object* v_goalsBefore_3712_; 
v_tacticInfo_3711_ = lean_ctor_get(v_head_3707_, 1);
lean_inc_ref(v_tacticInfo_3711_);
lean_dec(v_head_3707_);
v_goalsBefore_3712_ = lean_ctor_get(v_tacticInfo_3711_, 2);
lean_inc(v_goalsBefore_3712_);
lean_dec_ref(v_tacticInfo_3711_);
v___y_3697_ = v_goalsBefore_3712_;
goto v___jp_3696_;
}
else
{
lean_object* v_tacticInfo_3713_; lean_object* v_goalsAfter_3714_; 
lean_dec_ref_known(v___x_3710_, 1);
v_tacticInfo_3713_ = lean_ctor_get(v_head_3707_, 1);
lean_inc_ref(v_tacticInfo_3713_);
lean_dec(v_head_3707_);
v_goalsAfter_3714_ = lean_ctor_get(v_tacticInfo_3713_, 4);
lean_inc(v_goalsAfter_3714_);
lean_dec_ref(v_tacticInfo_3713_);
v___y_3697_ = v_goalsAfter_3714_;
goto v___jp_3696_;
}
}
else
{
lean_object* v_head_3715_; lean_object* v_tacticInfo_3716_; lean_object* v_goalsBefore_3717_; 
v_head_3715_ = lean_ctor_get(v___x_3705_, 0);
lean_inc(v_head_3715_);
lean_dec_ref_known(v___x_3705_, 2);
v_tacticInfo_3716_ = lean_ctor_get(v_head_3715_, 1);
lean_inc_ref(v_tacticInfo_3716_);
lean_dec(v_head_3715_);
v_goalsBefore_3717_ = lean_ctor_get(v_tacticInfo_3716_, 2);
lean_inc(v_goalsBefore_3717_);
lean_dec_ref(v_tacticInfo_3716_);
v___y_3697_ = v_goalsBefore_3717_;
goto v___jp_3696_;
}
}
else
{
uint8_t v___x_3718_; 
lean_dec_ref_known(v___x_3705_, 2);
lean_dec(v_tail_3706_);
lean_dec(v_kind_3701_);
v___x_3718_ = 0;
return v___x_3718_;
}
}
else
{
uint8_t v___x_3719_; 
lean_dec(v___x_3705_);
lean_dec(v_kind_3701_);
v___x_3719_ = 0;
return v___x_3719_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos___boxed(lean_object* v_tree_3725_, lean_object* v_fileMap_3726_, lean_object* v_c_3727_){
_start:
{
uint8_t v_res_3728_; lean_object* v_r_3729_; 
v_res_3728_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(v_tree_3725_, v_fileMap_3726_, v_c_3727_);
v_r_3729_ = lean_box(v_res_3728_);
return v_r_3729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(lean_object* v___y_3730_){
_start:
{
lean_object* v___x_3732_; lean_object* v_infoState_3733_; lean_object* v_trees_3734_; lean_object* v___x_3735_; 
v___x_3732_ = lean_st_ref_get(v___y_3730_);
v_infoState_3733_ = lean_ctor_get(v___x_3732_, 8);
lean_inc_ref(v_infoState_3733_);
lean_dec(v___x_3732_);
v_trees_3734_ = lean_ctor_get(v_infoState_3733_, 2);
lean_inc_ref(v_trees_3734_);
lean_dec_ref(v_infoState_3733_);
v___x_3735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3735_, 0, v_trees_3734_);
return v___x_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg___boxed(lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
lean_object* v_res_3738_; 
v_res_3738_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_3736_);
lean_dec(v___y_3736_);
return v_res_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
lean_object* v___x_3742_; 
v___x_3742_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_3740_);
return v___x_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___boxed(lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
lean_object* v_res_3746_; 
v_res_3746_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(v___y_3743_, v___y_3744_);
lean_dec(v___y_3744_);
lean_dec_ref(v___y_3743_);
return v_res_3746_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3748_; lean_object* v___x_3749_; 
v___x_3748_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__0));
v___x_3749_ = l_Lean_stringToMessageData(v___x_3748_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(lean_object* v_tree_3750_, lean_object* v___x_3751_, lean_object* v___x_3752_, lean_object* v_as_3753_, size_t v_sz_3754_, size_t v_i_3755_, lean_object* v_b_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_){
_start:
{
lean_object* v_a_3761_; uint8_t v___x_3765_; 
v___x_3765_ = lean_usize_dec_lt(v_i_3755_, v_sz_3754_);
if (v___x_3765_ == 0)
{
lean_object* v___x_3766_; 
lean_dec_ref(v___x_3751_);
lean_dec_ref(v_tree_3750_);
v___x_3766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3766_, 0, v_b_3756_);
return v___x_3766_;
}
else
{
lean_object* v___x_3767_; lean_object* v_a_3768_; uint8_t v___x_3769_; 
v___x_3767_ = lean_box(0);
v_a_3768_ = lean_array_uget_borrowed(v_as_3753_, v_i_3755_);
lean_inc(v_a_3768_);
lean_inc_ref(v___x_3751_);
lean_inc_ref(v_tree_3750_);
v___x_3769_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(v_tree_3750_, v___x_3751_, v_a_3768_);
if (v___x_3769_ == 0)
{
lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v_scopes_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v_opts_3776_; uint8_t v_hasTrace_3777_; 
v___x_3770_ = l_Lean_inheritedTraceOptions;
v___x_3771_ = lean_st_ref_get(v___x_3770_);
v___x_3772_ = lean_st_ref_get(v___y_3758_);
v_scopes_3773_ = lean_ctor_get(v___x_3772_, 2);
lean_inc(v_scopes_3773_);
lean_dec(v___x_3772_);
v___x_3774_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3775_ = l_List_head_x21___redArg(v___x_3774_, v_scopes_3773_);
lean_dec(v_scopes_3773_);
v_opts_3776_ = lean_ctor_get(v___x_3775_, 1);
lean_inc_ref(v_opts_3776_);
lean_dec(v___x_3775_);
v_hasTrace_3777_ = lean_ctor_get_uint8(v_opts_3776_, sizeof(void*)*1);
if (v_hasTrace_3777_ == 0)
{
lean_dec_ref(v_opts_3776_);
lean_dec(v___x_3771_);
v_a_3761_ = v___x_3767_;
goto v___jp_3760_;
}
else
{
lean_object* v___x_3778_; lean_object* v___x_3779_; uint8_t v___x_3780_; 
v___x_3778_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3779_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_3780_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3771_, v_opts_3776_, v___x_3779_);
lean_dec_ref(v_opts_3776_);
lean_dec(v___x_3771_);
if (v___x_3780_ == 0)
{
v_a_3761_ = v___x_3767_;
goto v___jp_3760_;
}
else
{
lean_object* v___x_3781_; lean_object* v___x_3782_; 
v___x_3781_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1);
v___x_3782_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_3778_, v___x_3781_, v___y_3757_, v___y_3758_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_dec_ref_known(v___x_3782_, 1);
v_a_3761_ = v___x_3767_;
goto v___jp_3760_;
}
else
{
lean_dec_ref(v___x_3751_);
lean_dec_ref(v_tree_3750_);
return v___x_3782_;
}
}
}
}
else
{
lean_object* v_kind_3783_; 
v_kind_3783_ = lean_ctor_get(v_a_3768_, 0);
if (lean_obj_tag(v_kind_3783_) == 0)
{
lean_object* v_ref_3784_; lean_object* v_tacticSeq_3785_; lean_object* v_insertPos_3786_; lean_object* v___x_3787_; 
v_ref_3784_ = lean_ctor_get(v_a_3768_, 1);
v_tacticSeq_3785_ = lean_ctor_get(v_kind_3783_, 0);
v_insertPos_3786_ = lean_ctor_get(v_kind_3783_, 1);
lean_inc(v_a_3768_);
v___x_3787_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(v_a_3768_, v___y_3757_, v___y_3758_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_object* v_a_3788_; lean_object* v___x_3789_; 
v_a_3788_ = lean_ctor_get(v___x_3787_, 0);
lean_inc(v_a_3788_);
lean_dec_ref_known(v___x_3787_, 1);
lean_inc(v_insertPos_3786_);
lean_inc(v_ref_3784_);
v___x_3789_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(v_tacticSeq_3785_, v_ref_3784_, v_insertPos_3786_, v_a_3788_, v___x_3752_, v___y_3757_, v___y_3758_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_dec_ref_known(v___x_3789_, 1);
v_a_3761_ = v___x_3767_;
goto v___jp_3760_;
}
else
{
lean_dec_ref(v___x_3751_);
lean_dec_ref(v_tree_3750_);
return v___x_3789_;
}
}
else
{
lean_object* v_a_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3797_; 
lean_dec_ref(v___x_3751_);
lean_dec_ref(v_tree_3750_);
v_a_3790_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3792_ = v___x_3787_;
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_a_3790_);
lean_dec(v___x_3787_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3795_; 
if (v_isShared_3793_ == 0)
{
v___x_3795_ = v___x_3792_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_a_3790_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
}
else
{
lean_object* v___x_3798_; 
lean_inc(v_a_3768_);
v___x_3798_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(v_a_3768_, v___y_3757_, v___y_3758_);
if (lean_obj_tag(v___x_3798_) == 0)
{
lean_dec_ref_known(v___x_3798_, 1);
v_a_3761_ = v___x_3767_;
goto v___jp_3760_;
}
else
{
lean_dec_ref(v___x_3751_);
lean_dec_ref(v_tree_3750_);
return v___x_3798_;
}
}
}
}
v___jp_3760_:
{
size_t v___x_3762_; size_t v___x_3763_; 
v___x_3762_ = ((size_t)1ULL);
v___x_3763_ = lean_usize_add(v_i_3755_, v___x_3762_);
v_i_3755_ = v___x_3763_;
v_b_3756_ = v_a_3761_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___boxed(lean_object* v_tree_3799_, lean_object* v___x_3800_, lean_object* v___x_3801_, lean_object* v_as_3802_, lean_object* v_sz_3803_, lean_object* v_i_3804_, lean_object* v_b_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
size_t v_sz_boxed_3809_; size_t v_i_boxed_3810_; lean_object* v_res_3811_; 
v_sz_boxed_3809_ = lean_unbox_usize(v_sz_3803_);
lean_dec(v_sz_3803_);
v_i_boxed_3810_ = lean_unbox_usize(v_i_3804_);
lean_dec(v_i_3804_);
v_res_3811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_tree_3799_, v___x_3800_, v___x_3801_, v_as_3802_, v_sz_boxed_3809_, v_i_boxed_3810_, v_b_3805_, v___y_3806_, v___y_3807_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec_ref(v_as_3802_);
lean_dec(v___x_3801_);
return v_res_3811_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3816_; lean_object* v___x_3817_; 
v___x_3816_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__1));
v___x_3817_ = l_Lean_stringToMessageData(v___x_3816_);
return v___x_3817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(lean_object* v_stx_3818_, lean_object* v___x_3819_, lean_object* v___x_3820_, lean_object* v___x_3821_, lean_object* v___x_3822_, lean_object* v_as_3823_, size_t v_sz_3824_, size_t v_i_3825_, lean_object* v_b_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
uint8_t v___x_3830_; 
v___x_3830_ = lean_usize_dec_lt(v_i_3825_, v_sz_3824_);
if (v___x_3830_ == 0)
{
lean_object* v___x_3831_; 
lean_dec_ref(v___x_3821_);
lean_dec(v_stx_3818_);
v___x_3831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3831_, 0, v_b_3826_);
return v___x_3831_;
}
else
{
lean_object* v_a_3832_; lean_object* v___x_3833_; 
lean_dec_ref(v_b_3826_);
v_a_3832_ = lean_array_uget_borrowed(v_as_3823_, v_i_3825_);
lean_inc(v_a_3832_);
lean_inc(v_stx_3818_);
v___x_3833_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3818_, v___x_3819_, v_a_3832_, v___x_3820_, v___y_3827_, v___y_3828_);
if (lean_obj_tag(v___x_3833_) == 0)
{
lean_object* v_a_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v_scopes_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v_opts_3841_; uint8_t v_hasTrace_3842_; lean_object* v___x_3843_; lean_object* v___y_3845_; lean_object* v___y_3846_; 
v_a_3834_ = lean_ctor_get(v___x_3833_, 0);
lean_inc(v_a_3834_);
lean_dec_ref_known(v___x_3833_, 1);
v___x_3835_ = l_Lean_inheritedTraceOptions;
v___x_3836_ = lean_st_ref_get(v___x_3835_);
v___x_3837_ = lean_st_ref_get(v___y_3828_);
v_scopes_3838_ = lean_ctor_get(v___x_3837_, 2);
lean_inc(v_scopes_3838_);
lean_dec(v___x_3837_);
v___x_3839_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3840_ = l_List_head_x21___redArg(v___x_3839_, v_scopes_3838_);
lean_dec(v_scopes_3838_);
v_opts_3841_ = lean_ctor_get(v___x_3840_, 1);
lean_inc_ref(v_opts_3841_);
lean_dec(v___x_3840_);
v_hasTrace_3842_ = lean_ctor_get_uint8(v_opts_3841_, sizeof(void*)*1);
v___x_3843_ = lean_box(0);
if (v_hasTrace_3842_ == 0)
{
lean_dec_ref(v_opts_3841_);
lean_dec(v___x_3836_);
v___y_3845_ = v___y_3827_;
v___y_3846_ = v___y_3828_;
goto v___jp_3844_;
}
else
{
lean_object* v___x_3862_; lean_object* v___x_3863_; uint8_t v___x_3864_; 
v___x_3862_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3863_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_3864_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3836_, v_opts_3841_, v___x_3863_);
lean_dec_ref(v_opts_3841_);
lean_dec(v___x_3836_);
if (v___x_3864_ == 0)
{
v___y_3845_ = v___y_3827_;
v___y_3846_ = v___y_3828_;
goto v___jp_3844_;
}
else
{
lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3865_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_3866_ = lean_array_get_size(v_a_3834_);
v___x_3867_ = l_Nat_reprFast(v___x_3866_);
v___x_3868_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3867_);
v___x_3869_ = l_Lean_MessageData_ofFormat(v___x_3868_);
v___x_3870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3865_);
lean_ctor_set(v___x_3870_, 1, v___x_3869_);
v___x_3871_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_3862_, v___x_3870_, v___y_3827_, v___y_3828_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_dec_ref_known(v___x_3871_, 1);
v___y_3845_ = v___y_3827_;
v___y_3846_ = v___y_3828_;
goto v___jp_3844_;
}
else
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3879_; 
lean_dec(v_a_3834_);
lean_dec_ref(v___x_3821_);
lean_dec(v_stx_3818_);
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3874_ = v___x_3871_;
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3871_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3877_; 
if (v_isShared_3875_ == 0)
{
v___x_3877_ = v___x_3874_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_a_3872_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
}
}
}
v___jp_3844_:
{
size_t v_sz_3847_; size_t v___x_3848_; lean_object* v___x_3849_; 
v_sz_3847_ = lean_array_size(v_a_3834_);
v___x_3848_ = ((size_t)0ULL);
lean_inc_ref(v___x_3821_);
lean_inc(v_a_3832_);
v___x_3849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_3832_, v___x_3821_, v___x_3822_, v_a_3834_, v_sz_3847_, v___x_3848_, v___x_3843_, v___y_3845_, v___y_3846_);
lean_dec(v_a_3834_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v___x_3850_; size_t v___x_3851_; size_t v___x_3852_; 
lean_dec_ref_known(v___x_3849_, 1);
v___x_3850_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_3851_ = ((size_t)1ULL);
v___x_3852_ = lean_usize_add(v_i_3825_, v___x_3851_);
v_i_3825_ = v___x_3852_;
v_b_3826_ = v___x_3850_;
goto _start;
}
else
{
lean_object* v_a_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3861_; 
lean_dec_ref(v___x_3821_);
lean_dec(v_stx_3818_);
v_a_3854_ = lean_ctor_get(v___x_3849_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3856_ = v___x_3849_;
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_a_3854_);
lean_dec(v___x_3849_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___x_3859_; 
if (v_isShared_3857_ == 0)
{
v___x_3859_ = v___x_3856_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_a_3854_);
v___x_3859_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
return v___x_3859_;
}
}
}
}
}
else
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
lean_dec_ref(v___x_3821_);
lean_dec(v_stx_3818_);
v_a_3880_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3882_ = v___x_3833_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3833_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3880_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___boxed(lean_object* v_stx_3888_, lean_object* v___x_3889_, lean_object* v___x_3890_, lean_object* v___x_3891_, lean_object* v___x_3892_, lean_object* v_as_3893_, lean_object* v_sz_3894_, lean_object* v_i_3895_, lean_object* v_b_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_){
_start:
{
size_t v_sz_boxed_3900_; size_t v_i_boxed_3901_; lean_object* v_res_3902_; 
v_sz_boxed_3900_ = lean_unbox_usize(v_sz_3894_);
lean_dec(v_sz_3894_);
v_i_boxed_3901_ = lean_unbox_usize(v_i_3895_);
lean_dec(v_i_3895_);
v_res_3902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_3888_, v___x_3889_, v___x_3890_, v___x_3891_, v___x_3892_, v_as_3893_, v_sz_boxed_3900_, v_i_boxed_3901_, v_b_3896_, v___y_3897_, v___y_3898_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec_ref(v_as_3893_);
lean_dec(v___x_3892_);
lean_dec_ref(v___x_3890_);
lean_dec_ref(v___x_3889_);
return v_res_3902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(lean_object* v_stx_3903_, lean_object* v___x_3904_, lean_object* v___x_3905_, lean_object* v___x_3906_, lean_object* v___x_3907_, lean_object* v_as_3908_, size_t v_sz_3909_, size_t v_i_3910_, lean_object* v_b_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_){
_start:
{
uint8_t v___x_3915_; 
v___x_3915_ = lean_usize_dec_lt(v_i_3910_, v_sz_3909_);
if (v___x_3915_ == 0)
{
lean_object* v___x_3916_; 
lean_dec_ref(v___x_3906_);
lean_dec(v_stx_3903_);
v___x_3916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3916_, 0, v_b_3911_);
return v___x_3916_;
}
else
{
lean_object* v_a_3917_; lean_object* v___x_3918_; 
lean_dec_ref(v_b_3911_);
v_a_3917_ = lean_array_uget_borrowed(v_as_3908_, v_i_3910_);
lean_inc(v_a_3917_);
lean_inc(v_stx_3903_);
v___x_3918_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3903_, v___x_3904_, v_a_3917_, v___x_3905_, v___y_3912_, v___y_3913_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v_a_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v_scopes_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v_opts_3926_; uint8_t v_hasTrace_3927_; lean_object* v___x_3928_; lean_object* v___y_3930_; lean_object* v___y_3931_; 
v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
lean_inc(v_a_3919_);
lean_dec_ref_known(v___x_3918_, 1);
v___x_3920_ = l_Lean_inheritedTraceOptions;
v___x_3921_ = lean_st_ref_get(v___x_3920_);
v___x_3922_ = lean_st_ref_get(v___y_3913_);
v_scopes_3923_ = lean_ctor_get(v___x_3922_, 2);
lean_inc(v_scopes_3923_);
lean_dec(v___x_3922_);
v___x_3924_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3925_ = l_List_head_x21___redArg(v___x_3924_, v_scopes_3923_);
lean_dec(v_scopes_3923_);
v_opts_3926_ = lean_ctor_get(v___x_3925_, 1);
lean_inc_ref(v_opts_3926_);
lean_dec(v___x_3925_);
v_hasTrace_3927_ = lean_ctor_get_uint8(v_opts_3926_, sizeof(void*)*1);
v___x_3928_ = lean_box(0);
if (v_hasTrace_3927_ == 0)
{
lean_dec_ref(v_opts_3926_);
lean_dec(v___x_3921_);
v___y_3930_ = v___y_3912_;
v___y_3931_ = v___y_3913_;
goto v___jp_3929_;
}
else
{
lean_object* v___x_3947_; lean_object* v___x_3948_; uint8_t v___x_3949_; 
v___x_3947_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3948_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_3949_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3921_, v_opts_3926_, v___x_3948_);
lean_dec_ref(v_opts_3926_);
lean_dec(v___x_3921_);
if (v___x_3949_ == 0)
{
v___y_3930_ = v___y_3912_;
v___y_3931_ = v___y_3913_;
goto v___jp_3929_;
}
else
{
lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v___x_3950_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_3951_ = lean_array_get_size(v_a_3919_);
v___x_3952_ = l_Nat_reprFast(v___x_3951_);
v___x_3953_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3952_);
v___x_3954_ = l_Lean_MessageData_ofFormat(v___x_3953_);
v___x_3955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3950_);
lean_ctor_set(v___x_3955_, 1, v___x_3954_);
v___x_3956_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_3947_, v___x_3955_, v___y_3912_, v___y_3913_);
if (lean_obj_tag(v___x_3956_) == 0)
{
lean_dec_ref_known(v___x_3956_, 1);
v___y_3930_ = v___y_3912_;
v___y_3931_ = v___y_3913_;
goto v___jp_3929_;
}
else
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3964_; 
lean_dec(v_a_3919_);
lean_dec_ref(v___x_3906_);
lean_dec(v_stx_3903_);
v_a_3957_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3959_ = v___x_3956_;
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3956_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3962_; 
if (v_isShared_3960_ == 0)
{
v___x_3962_ = v___x_3959_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_a_3957_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
}
}
}
v___jp_3929_:
{
size_t v_sz_3932_; size_t v___x_3933_; lean_object* v___x_3934_; 
v_sz_3932_ = lean_array_size(v_a_3919_);
v___x_3933_ = ((size_t)0ULL);
lean_inc_ref(v___x_3906_);
lean_inc(v_a_3917_);
v___x_3934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_3917_, v___x_3906_, v___x_3907_, v_a_3919_, v_sz_3932_, v___x_3933_, v___x_3928_, v___y_3930_, v___y_3931_);
lean_dec(v_a_3919_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v___x_3935_; size_t v___x_3936_; size_t v___x_3937_; lean_object* v___x_3938_; 
lean_dec_ref_known(v___x_3934_, 1);
v___x_3935_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_3936_ = ((size_t)1ULL);
v___x_3937_ = lean_usize_add(v_i_3910_, v___x_3936_);
v___x_3938_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_3903_, v___x_3904_, v___x_3905_, v___x_3906_, v___x_3907_, v_as_3908_, v_sz_3909_, v___x_3937_, v___x_3935_, v___y_3912_, v___y_3913_);
return v___x_3938_;
}
else
{
lean_object* v_a_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3946_; 
lean_dec_ref(v___x_3906_);
lean_dec(v_stx_3903_);
v_a_3939_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_3946_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_3946_ == 0)
{
v___x_3941_ = v___x_3934_;
v_isShared_3942_ = v_isSharedCheck_3946_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_a_3939_);
lean_dec(v___x_3934_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3946_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v___x_3944_; 
if (v_isShared_3942_ == 0)
{
v___x_3944_ = v___x_3941_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v_a_3939_);
v___x_3944_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
return v___x_3944_;
}
}
}
}
}
else
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3972_; 
lean_dec_ref(v___x_3906_);
lean_dec(v_stx_3903_);
v_a_3965_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3967_ = v___x_3918_;
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3918_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3970_; 
if (v_isShared_3968_ == 0)
{
v___x_3970_ = v___x_3967_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3965_);
v___x_3970_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
return v___x_3970_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3___boxed(lean_object* v_stx_3973_, lean_object* v___x_3974_, lean_object* v___x_3975_, lean_object* v___x_3976_, lean_object* v___x_3977_, lean_object* v_as_3978_, lean_object* v_sz_3979_, lean_object* v_i_3980_, lean_object* v_b_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_){
_start:
{
size_t v_sz_boxed_3985_; size_t v_i_boxed_3986_; lean_object* v_res_3987_; 
v_sz_boxed_3985_ = lean_unbox_usize(v_sz_3979_);
lean_dec(v_sz_3979_);
v_i_boxed_3986_ = lean_unbox_usize(v_i_3980_);
lean_dec(v_i_3980_);
v_res_3987_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(v_stx_3973_, v___x_3974_, v___x_3975_, v___x_3976_, v___x_3977_, v_as_3978_, v_sz_boxed_3985_, v_i_boxed_3986_, v_b_3981_, v___y_3982_, v___y_3983_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec_ref(v_as_3978_);
lean_dec(v___x_3977_);
lean_dec_ref(v___x_3975_);
lean_dec_ref(v___x_3974_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(lean_object* v_stx_3991_, lean_object* v___x_3992_, lean_object* v___x_3993_, lean_object* v___x_3994_, lean_object* v___x_3995_, lean_object* v_as_3996_, size_t v_sz_3997_, size_t v_i_3998_, lean_object* v_b_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_){
_start:
{
uint8_t v___x_4003_; 
v___x_4003_ = lean_usize_dec_lt(v_i_3998_, v_sz_3997_);
if (v___x_4003_ == 0)
{
lean_object* v___x_4004_; 
lean_dec_ref(v___x_3994_);
lean_dec(v_stx_3991_);
v___x_4004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4004_, 0, v_b_3999_);
return v___x_4004_;
}
else
{
lean_object* v_a_4005_; lean_object* v___x_4006_; 
lean_dec_ref(v_b_3999_);
v_a_4005_ = lean_array_uget_borrowed(v_as_3996_, v_i_3998_);
lean_inc(v_a_4005_);
lean_inc(v_stx_3991_);
v___x_4006_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3991_, v___x_3992_, v_a_4005_, v___x_3993_, v___y_4000_, v___y_4001_);
if (lean_obj_tag(v___x_4006_) == 0)
{
lean_object* v_a_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v_scopes_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v_opts_4014_; uint8_t v_hasTrace_4015_; lean_object* v___x_4016_; lean_object* v___y_4018_; lean_object* v___y_4019_; 
v_a_4007_ = lean_ctor_get(v___x_4006_, 0);
lean_inc(v_a_4007_);
lean_dec_ref_known(v___x_4006_, 1);
v___x_4008_ = l_Lean_inheritedTraceOptions;
v___x_4009_ = lean_st_ref_get(v___x_4008_);
v___x_4010_ = lean_st_ref_get(v___y_4001_);
v_scopes_4011_ = lean_ctor_get(v___x_4010_, 2);
lean_inc(v_scopes_4011_);
lean_dec(v___x_4010_);
v___x_4012_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4013_ = l_List_head_x21___redArg(v___x_4012_, v_scopes_4011_);
lean_dec(v_scopes_4011_);
v_opts_4014_ = lean_ctor_get(v___x_4013_, 1);
lean_inc_ref(v_opts_4014_);
lean_dec(v___x_4013_);
v_hasTrace_4015_ = lean_ctor_get_uint8(v_opts_4014_, sizeof(void*)*1);
v___x_4016_ = lean_box(0);
if (v_hasTrace_4015_ == 0)
{
lean_dec_ref(v_opts_4014_);
lean_dec(v___x_4009_);
v___y_4018_ = v___y_4000_;
v___y_4019_ = v___y_4001_;
goto v___jp_4017_;
}
else
{
lean_object* v___x_4035_; lean_object* v___x_4036_; uint8_t v___x_4037_; 
v___x_4035_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4036_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_4037_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4009_, v_opts_4014_, v___x_4036_);
lean_dec_ref(v_opts_4014_);
lean_dec(v___x_4009_);
if (v___x_4037_ == 0)
{
v___y_4018_ = v___y_4000_;
v___y_4019_ = v___y_4001_;
goto v___jp_4017_;
}
else
{
lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4038_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_4039_ = lean_array_get_size(v_a_4007_);
v___x_4040_ = l_Nat_reprFast(v___x_4039_);
v___x_4041_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4041_, 0, v___x_4040_);
v___x_4042_ = l_Lean_MessageData_ofFormat(v___x_4041_);
v___x_4043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4038_);
lean_ctor_set(v___x_4043_, 1, v___x_4042_);
v___x_4044_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_4035_, v___x_4043_, v___y_4000_, v___y_4001_);
if (lean_obj_tag(v___x_4044_) == 0)
{
lean_dec_ref_known(v___x_4044_, 1);
v___y_4018_ = v___y_4000_;
v___y_4019_ = v___y_4001_;
goto v___jp_4017_;
}
else
{
lean_object* v_a_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4052_; 
lean_dec(v_a_4007_);
lean_dec_ref(v___x_3994_);
lean_dec(v_stx_3991_);
v_a_4045_ = lean_ctor_get(v___x_4044_, 0);
v_isSharedCheck_4052_ = !lean_is_exclusive(v___x_4044_);
if (v_isSharedCheck_4052_ == 0)
{
v___x_4047_ = v___x_4044_;
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_a_4045_);
lean_dec(v___x_4044_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4050_; 
if (v_isShared_4048_ == 0)
{
v___x_4050_ = v___x_4047_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_a_4045_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
}
}
}
}
}
v___jp_4017_:
{
size_t v_sz_4020_; size_t v___x_4021_; lean_object* v___x_4022_; 
v_sz_4020_ = lean_array_size(v_a_4007_);
v___x_4021_ = ((size_t)0ULL);
lean_inc_ref(v___x_3994_);
lean_inc(v_a_4005_);
v___x_4022_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4005_, v___x_3994_, v___x_3995_, v_a_4007_, v_sz_4020_, v___x_4021_, v___x_4016_, v___y_4018_, v___y_4019_);
lean_dec(v_a_4007_);
if (lean_obj_tag(v___x_4022_) == 0)
{
lean_object* v___x_4023_; size_t v___x_4024_; size_t v___x_4025_; 
lean_dec_ref_known(v___x_4022_, 1);
v___x_4023_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_4024_ = ((size_t)1ULL);
v___x_4025_ = lean_usize_add(v_i_3998_, v___x_4024_);
v_i_3998_ = v___x_4025_;
v_b_3999_ = v___x_4023_;
goto _start;
}
else
{
lean_object* v_a_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4034_; 
lean_dec_ref(v___x_3994_);
lean_dec(v_stx_3991_);
v_a_4027_ = lean_ctor_get(v___x_4022_, 0);
v_isSharedCheck_4034_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4034_ == 0)
{
v___x_4029_ = v___x_4022_;
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
else
{
lean_inc(v_a_4027_);
lean_dec(v___x_4022_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v___x_4032_; 
if (v_isShared_4030_ == 0)
{
v___x_4032_ = v___x_4029_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v_a_4027_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
return v___x_4032_;
}
}
}
}
}
else
{
lean_object* v_a_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4060_; 
lean_dec_ref(v___x_3994_);
lean_dec(v_stx_3991_);
v_a_4053_ = lean_ctor_get(v___x_4006_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4055_ = v___x_4006_;
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_a_4053_);
lean_dec(v___x_4006_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4058_; 
if (v_isShared_4056_ == 0)
{
v___x_4058_ = v___x_4055_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_a_4053_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
return v___x_4058_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_stx_4061_, lean_object* v___x_4062_, lean_object* v___x_4063_, lean_object* v___x_4064_, lean_object* v___x_4065_, lean_object* v_as_4066_, lean_object* v_sz_4067_, lean_object* v_i_4068_, lean_object* v_b_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_){
_start:
{
size_t v_sz_boxed_4073_; size_t v_i_boxed_4074_; lean_object* v_res_4075_; 
v_sz_boxed_4073_ = lean_unbox_usize(v_sz_4067_);
lean_dec(v_sz_4067_);
v_i_boxed_4074_ = lean_unbox_usize(v_i_4068_);
lean_dec(v_i_4068_);
v_res_4075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4061_, v___x_4062_, v___x_4063_, v___x_4064_, v___x_4065_, v_as_4066_, v_sz_boxed_4073_, v_i_boxed_4074_, v_b_4069_, v___y_4070_, v___y_4071_);
lean_dec(v___y_4071_);
lean_dec_ref(v___y_4070_);
lean_dec_ref(v_as_4066_);
lean_dec(v___x_4065_);
lean_dec_ref(v___x_4063_);
lean_dec_ref(v___x_4062_);
return v_res_4075_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(lean_object* v_stx_4076_, lean_object* v___x_4077_, lean_object* v___x_4078_, lean_object* v___x_4079_, lean_object* v___x_4080_, lean_object* v_as_4081_, size_t v_sz_4082_, size_t v_i_4083_, lean_object* v_b_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_){
_start:
{
uint8_t v___x_4088_; 
v___x_4088_ = lean_usize_dec_lt(v_i_4083_, v_sz_4082_);
if (v___x_4088_ == 0)
{
lean_object* v___x_4089_; 
lean_dec_ref(v___x_4079_);
lean_dec(v_stx_4076_);
v___x_4089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4089_, 0, v_b_4084_);
return v___x_4089_;
}
else
{
lean_object* v_a_4090_; lean_object* v___x_4091_; 
lean_dec_ref(v_b_4084_);
v_a_4090_ = lean_array_uget_borrowed(v_as_4081_, v_i_4083_);
lean_inc(v_a_4090_);
lean_inc(v_stx_4076_);
v___x_4091_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_4076_, v___x_4077_, v_a_4090_, v___x_4078_, v___y_4085_, v___y_4086_);
if (lean_obj_tag(v___x_4091_) == 0)
{
lean_object* v_a_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v_scopes_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v_opts_4099_; uint8_t v_hasTrace_4100_; lean_object* v___x_4101_; lean_object* v___y_4103_; lean_object* v___y_4104_; 
v_a_4092_ = lean_ctor_get(v___x_4091_, 0);
lean_inc(v_a_4092_);
lean_dec_ref_known(v___x_4091_, 1);
v___x_4093_ = l_Lean_inheritedTraceOptions;
v___x_4094_ = lean_st_ref_get(v___x_4093_);
v___x_4095_ = lean_st_ref_get(v___y_4086_);
v_scopes_4096_ = lean_ctor_get(v___x_4095_, 2);
lean_inc(v_scopes_4096_);
lean_dec(v___x_4095_);
v___x_4097_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4098_ = l_List_head_x21___redArg(v___x_4097_, v_scopes_4096_);
lean_dec(v_scopes_4096_);
v_opts_4099_ = lean_ctor_get(v___x_4098_, 1);
lean_inc_ref(v_opts_4099_);
lean_dec(v___x_4098_);
v_hasTrace_4100_ = lean_ctor_get_uint8(v_opts_4099_, sizeof(void*)*1);
v___x_4101_ = lean_box(0);
if (v_hasTrace_4100_ == 0)
{
lean_dec_ref(v_opts_4099_);
lean_dec(v___x_4094_);
v___y_4103_ = v___y_4085_;
v___y_4104_ = v___y_4086_;
goto v___jp_4102_;
}
else
{
lean_object* v___x_4120_; lean_object* v___x_4121_; uint8_t v___x_4122_; 
v___x_4120_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4121_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_4122_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4094_, v_opts_4099_, v___x_4121_);
lean_dec_ref(v_opts_4099_);
lean_dec(v___x_4094_);
if (v___x_4122_ == 0)
{
v___y_4103_ = v___y_4085_;
v___y_4104_ = v___y_4086_;
goto v___jp_4102_;
}
else
{
lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; 
v___x_4123_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_4124_ = lean_array_get_size(v_a_4092_);
v___x_4125_ = l_Nat_reprFast(v___x_4124_);
v___x_4126_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4125_);
v___x_4127_ = l_Lean_MessageData_ofFormat(v___x_4126_);
v___x_4128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4128_, 0, v___x_4123_);
lean_ctor_set(v___x_4128_, 1, v___x_4127_);
v___x_4129_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_4120_, v___x_4128_, v___y_4085_, v___y_4086_);
if (lean_obj_tag(v___x_4129_) == 0)
{
lean_dec_ref_known(v___x_4129_, 1);
v___y_4103_ = v___y_4085_;
v___y_4104_ = v___y_4086_;
goto v___jp_4102_;
}
else
{
lean_object* v_a_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4137_; 
lean_dec(v_a_4092_);
lean_dec_ref(v___x_4079_);
lean_dec(v_stx_4076_);
v_a_4130_ = lean_ctor_get(v___x_4129_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4129_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4132_ = v___x_4129_;
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_a_4130_);
lean_dec(v___x_4129_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4135_; 
if (v_isShared_4133_ == 0)
{
v___x_4135_ = v___x_4132_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_a_4130_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
}
}
v___jp_4102_:
{
size_t v_sz_4105_; size_t v___x_4106_; lean_object* v___x_4107_; 
v_sz_4105_ = lean_array_size(v_a_4092_);
v___x_4106_ = ((size_t)0ULL);
lean_inc_ref(v___x_4079_);
lean_inc(v_a_4090_);
v___x_4107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4090_, v___x_4079_, v___x_4080_, v_a_4092_, v_sz_4105_, v___x_4106_, v___x_4101_, v___y_4103_, v___y_4104_);
lean_dec(v_a_4092_);
if (lean_obj_tag(v___x_4107_) == 0)
{
lean_object* v___x_4108_; size_t v___x_4109_; size_t v___x_4110_; lean_object* v___x_4111_; 
lean_dec_ref_known(v___x_4107_, 1);
v___x_4108_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_4109_ = ((size_t)1ULL);
v___x_4110_ = lean_usize_add(v_i_4083_, v___x_4109_);
v___x_4111_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4076_, v___x_4077_, v___x_4078_, v___x_4079_, v___x_4080_, v_as_4081_, v_sz_4082_, v___x_4110_, v___x_4108_, v___y_4085_, v___y_4086_);
return v___x_4111_;
}
else
{
lean_object* v_a_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4119_; 
lean_dec_ref(v___x_4079_);
lean_dec(v_stx_4076_);
v_a_4112_ = lean_ctor_get(v___x_4107_, 0);
v_isSharedCheck_4119_ = !lean_is_exclusive(v___x_4107_);
if (v_isSharedCheck_4119_ == 0)
{
v___x_4114_ = v___x_4107_;
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_a_4112_);
lean_dec(v___x_4107_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v___x_4117_; 
if (v_isShared_4115_ == 0)
{
v___x_4117_ = v___x_4114_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v_a_4112_);
v___x_4117_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
return v___x_4117_;
}
}
}
}
}
else
{
lean_object* v_a_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4145_; 
lean_dec_ref(v___x_4079_);
lean_dec(v_stx_4076_);
v_a_4138_ = lean_ctor_get(v___x_4091_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4091_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4140_ = v___x_4091_;
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_a_4138_);
lean_dec(v___x_4091_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v___x_4143_; 
if (v_isShared_4141_ == 0)
{
v___x_4143_ = v___x_4140_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_a_4138_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4___boxed(lean_object* v_stx_4146_, lean_object* v___x_4147_, lean_object* v___x_4148_, lean_object* v___x_4149_, lean_object* v___x_4150_, lean_object* v_as_4151_, lean_object* v_sz_4152_, lean_object* v_i_4153_, lean_object* v_b_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_){
_start:
{
size_t v_sz_boxed_4158_; size_t v_i_boxed_4159_; lean_object* v_res_4160_; 
v_sz_boxed_4158_ = lean_unbox_usize(v_sz_4152_);
lean_dec(v_sz_4152_);
v_i_boxed_4159_ = lean_unbox_usize(v_i_4153_);
lean_dec(v_i_4153_);
v_res_4160_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(v_stx_4146_, v___x_4147_, v___x_4148_, v___x_4149_, v___x_4150_, v_as_4151_, v_sz_boxed_4158_, v_i_boxed_4159_, v_b_4154_, v___y_4155_, v___y_4156_);
lean_dec(v___y_4156_);
lean_dec_ref(v___y_4155_);
lean_dec_ref(v_as_4151_);
lean_dec(v___x_4150_);
lean_dec_ref(v___x_4148_);
lean_dec_ref(v___x_4147_);
return v_res_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(lean_object* v_init_4161_, lean_object* v_stx_4162_, lean_object* v___x_4163_, lean_object* v___x_4164_, lean_object* v___x_4165_, lean_object* v___x_4166_, lean_object* v_n_4167_, lean_object* v_b_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_){
_start:
{
if (lean_obj_tag(v_n_4167_) == 0)
{
lean_object* v_cs_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; size_t v_sz_4175_; size_t v___x_4176_; lean_object* v___x_4177_; 
v_cs_4172_ = lean_ctor_get(v_n_4167_, 0);
v___x_4173_ = lean_box(0);
v___x_4174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4173_);
lean_ctor_set(v___x_4174_, 1, v_b_4168_);
v_sz_4175_ = lean_array_size(v_cs_4172_);
v___x_4176_ = ((size_t)0ULL);
v___x_4177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(v_init_4161_, v_stx_4162_, v___x_4163_, v___x_4164_, v___x_4165_, v___x_4166_, v_cs_4172_, v_sz_4175_, v___x_4176_, v___x_4174_, v___y_4169_, v___y_4170_);
if (lean_obj_tag(v___x_4177_) == 0)
{
lean_object* v_a_4178_; lean_object* v___x_4180_; uint8_t v_isShared_4181_; uint8_t v_isSharedCheck_4192_; 
v_a_4178_ = lean_ctor_get(v___x_4177_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4177_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4180_ = v___x_4177_;
v_isShared_4181_ = v_isSharedCheck_4192_;
goto v_resetjp_4179_;
}
else
{
lean_inc(v_a_4178_);
lean_dec(v___x_4177_);
v___x_4180_ = lean_box(0);
v_isShared_4181_ = v_isSharedCheck_4192_;
goto v_resetjp_4179_;
}
v_resetjp_4179_:
{
lean_object* v_fst_4182_; 
v_fst_4182_ = lean_ctor_get(v_a_4178_, 0);
if (lean_obj_tag(v_fst_4182_) == 0)
{
lean_object* v_snd_4183_; lean_object* v___x_4184_; lean_object* v___x_4186_; 
v_snd_4183_ = lean_ctor_get(v_a_4178_, 1);
lean_inc(v_snd_4183_);
lean_dec(v_a_4178_);
v___x_4184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4184_, 0, v_snd_4183_);
if (v_isShared_4181_ == 0)
{
lean_ctor_set(v___x_4180_, 0, v___x_4184_);
v___x_4186_ = v___x_4180_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v___x_4184_);
v___x_4186_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
return v___x_4186_;
}
}
else
{
lean_object* v_val_4188_; lean_object* v___x_4190_; 
lean_inc_ref(v_fst_4182_);
lean_dec(v_a_4178_);
v_val_4188_ = lean_ctor_get(v_fst_4182_, 0);
lean_inc(v_val_4188_);
lean_dec_ref_known(v_fst_4182_, 1);
if (v_isShared_4181_ == 0)
{
lean_ctor_set(v___x_4180_, 0, v_val_4188_);
v___x_4190_ = v___x_4180_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v_val_4188_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
return v___x_4190_;
}
}
}
}
else
{
lean_object* v_a_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4200_; 
v_a_4193_ = lean_ctor_get(v___x_4177_, 0);
v_isSharedCheck_4200_ = !lean_is_exclusive(v___x_4177_);
if (v_isSharedCheck_4200_ == 0)
{
v___x_4195_ = v___x_4177_;
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_a_4193_);
lean_dec(v___x_4177_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v___x_4198_; 
if (v_isShared_4196_ == 0)
{
v___x_4198_ = v___x_4195_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v_a_4193_);
v___x_4198_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
return v___x_4198_;
}
}
}
}
else
{
lean_object* v_vs_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; size_t v_sz_4204_; size_t v___x_4205_; lean_object* v___x_4206_; 
v_vs_4201_ = lean_ctor_get(v_n_4167_, 0);
v___x_4202_ = lean_box(0);
v___x_4203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4202_);
lean_ctor_set(v___x_4203_, 1, v_b_4168_);
v_sz_4204_ = lean_array_size(v_vs_4201_);
v___x_4205_ = ((size_t)0ULL);
v___x_4206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(v_stx_4162_, v___x_4163_, v___x_4164_, v___x_4165_, v___x_4166_, v_vs_4201_, v_sz_4204_, v___x_4205_, v___x_4203_, v___y_4169_, v___y_4170_);
if (lean_obj_tag(v___x_4206_) == 0)
{
lean_object* v_a_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4221_; 
v_a_4207_ = lean_ctor_get(v___x_4206_, 0);
v_isSharedCheck_4221_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4221_ == 0)
{
v___x_4209_ = v___x_4206_;
v_isShared_4210_ = v_isSharedCheck_4221_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_a_4207_);
lean_dec(v___x_4206_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4221_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v_fst_4211_; 
v_fst_4211_ = lean_ctor_get(v_a_4207_, 0);
if (lean_obj_tag(v_fst_4211_) == 0)
{
lean_object* v_snd_4212_; lean_object* v___x_4213_; lean_object* v___x_4215_; 
v_snd_4212_ = lean_ctor_get(v_a_4207_, 1);
lean_inc(v_snd_4212_);
lean_dec(v_a_4207_);
v___x_4213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4213_, 0, v_snd_4212_);
if (v_isShared_4210_ == 0)
{
lean_ctor_set(v___x_4209_, 0, v___x_4213_);
v___x_4215_ = v___x_4209_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v___x_4213_);
v___x_4215_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
return v___x_4215_;
}
}
else
{
lean_object* v_val_4217_; lean_object* v___x_4219_; 
lean_inc_ref(v_fst_4211_);
lean_dec(v_a_4207_);
v_val_4217_ = lean_ctor_get(v_fst_4211_, 0);
lean_inc(v_val_4217_);
lean_dec_ref_known(v_fst_4211_, 1);
if (v_isShared_4210_ == 0)
{
lean_ctor_set(v___x_4209_, 0, v_val_4217_);
v___x_4219_ = v___x_4209_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_val_4217_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
}
}
else
{
lean_object* v_a_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4229_; 
v_a_4222_ = lean_ctor_get(v___x_4206_, 0);
v_isSharedCheck_4229_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4229_ == 0)
{
v___x_4224_ = v___x_4206_;
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_a_4222_);
lean_dec(v___x_4206_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v___x_4227_; 
if (v_isShared_4225_ == 0)
{
v___x_4227_ = v___x_4224_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_a_4222_);
v___x_4227_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
return v___x_4227_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(lean_object* v_init_4230_, lean_object* v_stx_4231_, lean_object* v___x_4232_, lean_object* v___x_4233_, lean_object* v___x_4234_, lean_object* v___x_4235_, lean_object* v_as_4236_, size_t v_sz_4237_, size_t v_i_4238_, lean_object* v_b_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_){
_start:
{
uint8_t v___x_4243_; 
v___x_4243_ = lean_usize_dec_lt(v_i_4238_, v_sz_4237_);
if (v___x_4243_ == 0)
{
lean_object* v___x_4244_; 
lean_dec_ref(v___x_4234_);
lean_dec(v_stx_4231_);
v___x_4244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4244_, 0, v_b_4239_);
return v___x_4244_;
}
else
{
lean_object* v_snd_4245_; lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4279_; 
v_snd_4245_ = lean_ctor_get(v_b_4239_, 1);
v_isSharedCheck_4279_ = !lean_is_exclusive(v_b_4239_);
if (v_isSharedCheck_4279_ == 0)
{
lean_object* v_unused_4280_; 
v_unused_4280_ = lean_ctor_get(v_b_4239_, 0);
lean_dec(v_unused_4280_);
v___x_4247_ = v_b_4239_;
v_isShared_4248_ = v_isSharedCheck_4279_;
goto v_resetjp_4246_;
}
else
{
lean_inc(v_snd_4245_);
lean_dec(v_b_4239_);
v___x_4247_ = lean_box(0);
v_isShared_4248_ = v_isSharedCheck_4279_;
goto v_resetjp_4246_;
}
v_resetjp_4246_:
{
lean_object* v_a_4249_; lean_object* v___x_4250_; 
v_a_4249_ = lean_array_uget_borrowed(v_as_4236_, v_i_4238_);
lean_inc(v_snd_4245_);
lean_inc_ref(v___x_4234_);
lean_inc(v_stx_4231_);
v___x_4250_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4230_, v_stx_4231_, v___x_4232_, v___x_4233_, v___x_4234_, v___x_4235_, v_a_4249_, v_snd_4245_, v___y_4240_, v___y_4241_);
if (lean_obj_tag(v___x_4250_) == 0)
{
lean_object* v_a_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4270_; 
v_a_4251_ = lean_ctor_get(v___x_4250_, 0);
v_isSharedCheck_4270_ = !lean_is_exclusive(v___x_4250_);
if (v_isSharedCheck_4270_ == 0)
{
v___x_4253_ = v___x_4250_;
v_isShared_4254_ = v_isSharedCheck_4270_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_a_4251_);
lean_dec(v___x_4250_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4270_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
if (lean_obj_tag(v_a_4251_) == 0)
{
lean_object* v___x_4255_; lean_object* v___x_4257_; 
lean_dec_ref(v___x_4234_);
lean_dec(v_stx_4231_);
v___x_4255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4255_, 0, v_a_4251_);
if (v_isShared_4248_ == 0)
{
lean_ctor_set(v___x_4247_, 0, v___x_4255_);
v___x_4257_ = v___x_4247_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v___x_4255_);
lean_ctor_set(v_reuseFailAlloc_4261_, 1, v_snd_4245_);
v___x_4257_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
lean_object* v___x_4259_; 
if (v_isShared_4254_ == 0)
{
lean_ctor_set(v___x_4253_, 0, v___x_4257_);
v___x_4259_ = v___x_4253_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4260_; 
v_reuseFailAlloc_4260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4260_, 0, v___x_4257_);
v___x_4259_ = v_reuseFailAlloc_4260_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
return v___x_4259_;
}
}
}
else
{
lean_object* v_a_4262_; lean_object* v___x_4263_; lean_object* v___x_4265_; 
lean_del_object(v___x_4253_);
lean_dec(v_snd_4245_);
v_a_4262_ = lean_ctor_get(v_a_4251_, 0);
lean_inc(v_a_4262_);
lean_dec_ref_known(v_a_4251_, 1);
v___x_4263_ = lean_box(0);
if (v_isShared_4248_ == 0)
{
lean_ctor_set(v___x_4247_, 1, v_a_4262_);
lean_ctor_set(v___x_4247_, 0, v___x_4263_);
v___x_4265_ = v___x_4247_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v___x_4263_);
lean_ctor_set(v_reuseFailAlloc_4269_, 1, v_a_4262_);
v___x_4265_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
size_t v___x_4266_; size_t v___x_4267_; 
v___x_4266_ = ((size_t)1ULL);
v___x_4267_ = lean_usize_add(v_i_4238_, v___x_4266_);
v_i_4238_ = v___x_4267_;
v_b_4239_ = v___x_4265_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4278_; 
lean_del_object(v___x_4247_);
lean_dec(v_snd_4245_);
lean_dec_ref(v___x_4234_);
lean_dec(v_stx_4231_);
v_a_4271_ = lean_ctor_get(v___x_4250_, 0);
v_isSharedCheck_4278_ = !lean_is_exclusive(v___x_4250_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4273_ = v___x_4250_;
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_a_4271_);
lean_dec(v___x_4250_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v___x_4276_; 
if (v_isShared_4274_ == 0)
{
v___x_4276_ = v___x_4273_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_a_4271_);
v___x_4276_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
return v___x_4276_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3___boxed(lean_object* v_init_4281_, lean_object* v_stx_4282_, lean_object* v___x_4283_, lean_object* v___x_4284_, lean_object* v___x_4285_, lean_object* v___x_4286_, lean_object* v_as_4287_, lean_object* v_sz_4288_, lean_object* v_i_4289_, lean_object* v_b_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_){
_start:
{
size_t v_sz_boxed_4294_; size_t v_i_boxed_4295_; lean_object* v_res_4296_; 
v_sz_boxed_4294_ = lean_unbox_usize(v_sz_4288_);
lean_dec(v_sz_4288_);
v_i_boxed_4295_ = lean_unbox_usize(v_i_4289_);
lean_dec(v_i_4289_);
v_res_4296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(v_init_4281_, v_stx_4282_, v___x_4283_, v___x_4284_, v___x_4285_, v___x_4286_, v_as_4287_, v_sz_boxed_4294_, v_i_boxed_4295_, v_b_4290_, v___y_4291_, v___y_4292_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec_ref(v_as_4287_);
lean_dec(v___x_4286_);
lean_dec_ref(v___x_4284_);
lean_dec_ref(v___x_4283_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2___boxed(lean_object* v_init_4297_, lean_object* v_stx_4298_, lean_object* v___x_4299_, lean_object* v___x_4300_, lean_object* v___x_4301_, lean_object* v___x_4302_, lean_object* v_n_4303_, lean_object* v_b_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_){
_start:
{
lean_object* v_res_4308_; 
v_res_4308_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4297_, v_stx_4298_, v___x_4299_, v___x_4300_, v___x_4301_, v___x_4302_, v_n_4303_, v_b_4304_, v___y_4305_, v___y_4306_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec_ref(v_n_4303_);
lean_dec(v___x_4302_);
lean_dec_ref(v___x_4300_);
lean_dec_ref(v___x_4299_);
return v_res_4308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(lean_object* v___x_4309_, lean_object* v___x_4310_, lean_object* v_stx_4311_, lean_object* v___x_4312_, lean_object* v___x_4313_, lean_object* v_t_4314_, lean_object* v_init_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_){
_start:
{
lean_object* v_root_4319_; lean_object* v_tail_4320_; lean_object* v___x_4321_; 
v_root_4319_ = lean_ctor_get(v_t_4314_, 0);
v_tail_4320_ = lean_ctor_get(v_t_4314_, 1);
lean_inc_ref(v___x_4309_);
lean_inc(v_stx_4311_);
v___x_4321_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4315_, v_stx_4311_, v___x_4312_, v___x_4313_, v___x_4309_, v___x_4310_, v_root_4319_, v_init_4315_, v___y_4316_, v___y_4317_);
if (lean_obj_tag(v___x_4321_) == 0)
{
lean_object* v_a_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4358_; 
v_a_4322_ = lean_ctor_get(v___x_4321_, 0);
v_isSharedCheck_4358_ = !lean_is_exclusive(v___x_4321_);
if (v_isSharedCheck_4358_ == 0)
{
v___x_4324_ = v___x_4321_;
v_isShared_4325_ = v_isSharedCheck_4358_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_a_4322_);
lean_dec(v___x_4321_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4358_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
if (lean_obj_tag(v_a_4322_) == 0)
{
lean_object* v_a_4326_; lean_object* v___x_4328_; 
lean_dec(v_stx_4311_);
lean_dec_ref(v___x_4309_);
v_a_4326_ = lean_ctor_get(v_a_4322_, 0);
lean_inc(v_a_4326_);
lean_dec_ref_known(v_a_4322_, 1);
if (v_isShared_4325_ == 0)
{
lean_ctor_set(v___x_4324_, 0, v_a_4326_);
v___x_4328_ = v___x_4324_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_a_4326_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
return v___x_4328_;
}
}
else
{
lean_object* v_a_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; size_t v_sz_4333_; size_t v___x_4334_; lean_object* v___x_4335_; 
lean_del_object(v___x_4324_);
v_a_4330_ = lean_ctor_get(v_a_4322_, 0);
lean_inc(v_a_4330_);
lean_dec_ref_known(v_a_4322_, 1);
v___x_4331_ = lean_box(0);
v___x_4332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4332_, 0, v___x_4331_);
lean_ctor_set(v___x_4332_, 1, v_a_4330_);
v_sz_4333_ = lean_array_size(v_tail_4320_);
v___x_4334_ = ((size_t)0ULL);
v___x_4335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(v_stx_4311_, v___x_4312_, v___x_4313_, v___x_4309_, v___x_4310_, v_tail_4320_, v_sz_4333_, v___x_4334_, v___x_4332_, v___y_4316_, v___y_4317_);
if (lean_obj_tag(v___x_4335_) == 0)
{
lean_object* v_a_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4349_; 
v_a_4336_ = lean_ctor_get(v___x_4335_, 0);
v_isSharedCheck_4349_ = !lean_is_exclusive(v___x_4335_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4338_ = v___x_4335_;
v_isShared_4339_ = v_isSharedCheck_4349_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_a_4336_);
lean_dec(v___x_4335_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4349_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v_fst_4340_; 
v_fst_4340_ = lean_ctor_get(v_a_4336_, 0);
if (lean_obj_tag(v_fst_4340_) == 0)
{
lean_object* v_snd_4341_; lean_object* v___x_4343_; 
v_snd_4341_ = lean_ctor_get(v_a_4336_, 1);
lean_inc(v_snd_4341_);
lean_dec(v_a_4336_);
if (v_isShared_4339_ == 0)
{
lean_ctor_set(v___x_4338_, 0, v_snd_4341_);
v___x_4343_ = v___x_4338_;
goto v_reusejp_4342_;
}
else
{
lean_object* v_reuseFailAlloc_4344_; 
v_reuseFailAlloc_4344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4344_, 0, v_snd_4341_);
v___x_4343_ = v_reuseFailAlloc_4344_;
goto v_reusejp_4342_;
}
v_reusejp_4342_:
{
return v___x_4343_;
}
}
else
{
lean_object* v_val_4345_; lean_object* v___x_4347_; 
lean_inc_ref(v_fst_4340_);
lean_dec(v_a_4336_);
v_val_4345_ = lean_ctor_get(v_fst_4340_, 0);
lean_inc(v_val_4345_);
lean_dec_ref_known(v_fst_4340_, 1);
if (v_isShared_4339_ == 0)
{
lean_ctor_set(v___x_4338_, 0, v_val_4345_);
v___x_4347_ = v___x_4338_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v_val_4345_);
v___x_4347_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
return v___x_4347_;
}
}
}
}
else
{
lean_object* v_a_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4357_; 
v_a_4350_ = lean_ctor_get(v___x_4335_, 0);
v_isSharedCheck_4357_ = !lean_is_exclusive(v___x_4335_);
if (v_isSharedCheck_4357_ == 0)
{
v___x_4352_ = v___x_4335_;
v_isShared_4353_ = v_isSharedCheck_4357_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_a_4350_);
lean_dec(v___x_4335_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4357_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v___x_4355_; 
if (v_isShared_4353_ == 0)
{
v___x_4355_ = v___x_4352_;
goto v_reusejp_4354_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v_a_4350_);
v___x_4355_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4354_;
}
v_reusejp_4354_:
{
return v___x_4355_;
}
}
}
}
}
}
else
{
lean_object* v_a_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4366_; 
lean_dec(v_stx_4311_);
lean_dec_ref(v___x_4309_);
v_a_4359_ = lean_ctor_get(v___x_4321_, 0);
v_isSharedCheck_4366_ = !lean_is_exclusive(v___x_4321_);
if (v_isSharedCheck_4366_ == 0)
{
v___x_4361_ = v___x_4321_;
v_isShared_4362_ = v_isSharedCheck_4366_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_a_4359_);
lean_dec(v___x_4321_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4366_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v___x_4364_; 
if (v_isShared_4362_ == 0)
{
v___x_4364_ = v___x_4361_;
goto v_reusejp_4363_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_a_4359_);
v___x_4364_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4363_;
}
v_reusejp_4363_:
{
return v___x_4364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2___boxed(lean_object* v___x_4367_, lean_object* v___x_4368_, lean_object* v_stx_4369_, lean_object* v___x_4370_, lean_object* v___x_4371_, lean_object* v_t_4372_, lean_object* v_init_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_){
_start:
{
lean_object* v_res_4377_; 
v_res_4377_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___x_4367_, v___x_4368_, v_stx_4369_, v___x_4370_, v___x_4371_, v_t_4372_, v_init_4373_, v___y_4374_, v___y_4375_);
lean_dec(v___y_4375_);
lean_dec_ref(v___y_4374_);
lean_dec_ref(v_t_4372_);
lean_dec_ref(v___x_4371_);
lean_dec_ref(v___x_4370_);
lean_dec(v___x_4368_);
return v_res_4377_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; 
v___x_4379_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__0));
v___x_4380_ = l_Lean_stringToMessageData(v___x_4379_);
return v___x_4380_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4384_; lean_object* v___x_4385_; 
v___x_4384_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__4));
v___x_4385_ = l_Lean_stringToMessageData(v___x_4384_);
return v___x_4385_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4387_; lean_object* v___x_4388_; 
v___x_4387_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__6));
v___x_4388_ = l_Lean_stringToMessageData(v___x_4387_);
return v___x_4388_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9(void){
_start:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; 
v___x_4390_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__8));
v___x_4391_ = l_Lean_stringToMessageData(v___x_4390_);
return v___x_4391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(lean_object* v_stx_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_){
_start:
{
lean_object* v___x_4399_; lean_object* v_scopes_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v_opts_4403_; lean_object* v___y_4405_; lean_object* v___y_4406_; lean_object* v___y_4407_; lean_object* v___y_4408_; uint8_t v___y_4427_; lean_object* v___y_4428_; lean_object* v___y_4429_; uint8_t v___y_4435_; lean_object* v___y_4436_; lean_object* v___y_4437_; lean_object* v___y_4438_; uint8_t v___y_4444_; lean_object* v___y_4445_; uint8_t v___y_4446_; lean_object* v___y_4447_; lean_object* v___y_4448_; lean_object* v___y_4457_; uint8_t v___y_4458_; lean_object* v___y_4459_; uint8_t v___y_4460_; uint8_t v___y_4461_; lean_object* v___y_4462_; uint8_t v___y_4471_; uint8_t v___y_4472_; uint8_t v___y_4473_; uint8_t v___y_4507_; lean_object* v___x_4514_; uint8_t v___x_4515_; 
v___x_4399_ = lean_st_ref_get(v___y_4394_);
v_scopes_4400_ = lean_ctor_get(v___x_4399_, 2);
lean_inc(v_scopes_4400_);
lean_dec(v___x_4399_);
v___x_4401_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4402_ = l_List_head_x21___redArg(v___x_4401_, v_scopes_4400_);
lean_dec(v_scopes_4400_);
v_opts_4403_ = lean_ctor_get(v___x_4402_, 1);
lean_inc_ref(v_opts_4403_);
lean_dec(v___x_4402_);
v___x_4514_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_4515_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4403_, v___x_4514_);
if (v___x_4515_ == 0)
{
lean_object* v___x_4516_; uint8_t v___x_4517_; 
v___x_4516_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_4517_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4403_, v___x_4516_);
v___y_4507_ = v___x_4517_;
goto v___jp_4506_;
}
else
{
v___y_4507_ = v___x_4515_;
goto v___jp_4506_;
}
v___jp_4396_:
{
lean_object* v___x_4397_; lean_object* v___x_4398_; 
v___x_4397_ = lean_box(0);
v___x_4398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4398_, 0, v___x_4397_);
return v___x_4398_;
}
v___jp_4404_:
{
lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v_a_4411_; lean_object* v___x_4412_; lean_object* v_line_4413_; lean_object* v_messages_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; 
v___x_4409_ = lean_st_ref_get(v___y_4405_);
v___x_4410_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_4405_);
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
lean_inc(v_a_4411_);
lean_dec_ref(v___x_4410_);
lean_inc_ref_n(v___y_4406_, 2);
v___x_4412_ = l_Lean_FileMap_toPosition(v___y_4406_, v___y_4408_);
lean_dec(v___y_4408_);
v_line_4413_ = lean_ctor_get(v___x_4412_, 0);
lean_inc(v_line_4413_);
lean_dec_ref(v___x_4412_);
v_messages_4414_ = lean_ctor_get(v___x_4409_, 1);
lean_inc_ref(v_messages_4414_);
lean_dec(v___x_4409_);
v___x_4415_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_4414_);
v___x_4416_ = lean_box(0);
v___x_4417_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___y_4406_, v_line_4413_, v_stx_4392_, v_opts_4403_, v___x_4415_, v_a_4411_, v___x_4416_, v___y_4407_, v___y_4405_);
lean_dec(v_a_4411_);
lean_dec_ref(v___x_4415_);
lean_dec_ref(v_opts_4403_);
lean_dec(v_line_4413_);
if (lean_obj_tag(v___x_4417_) == 0)
{
lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4424_; 
v_isSharedCheck_4424_ = !lean_is_exclusive(v___x_4417_);
if (v_isSharedCheck_4424_ == 0)
{
lean_object* v_unused_4425_; 
v_unused_4425_ = lean_ctor_get(v___x_4417_, 0);
lean_dec(v_unused_4425_);
v___x_4419_ = v___x_4417_;
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
else
{
lean_dec(v___x_4417_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
lean_object* v___x_4422_; 
if (v_isShared_4420_ == 0)
{
lean_ctor_set(v___x_4419_, 0, v___x_4416_);
v___x_4422_ = v___x_4419_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v___x_4416_);
v___x_4422_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
return v___x_4422_;
}
}
}
else
{
return v___x_4417_;
}
}
v___jp_4426_:
{
lean_object* v_fileMap_4430_; lean_object* v___x_4431_; 
v_fileMap_4430_ = lean_ctor_get(v___y_4428_, 1);
v___x_4431_ = l_Lean_Syntax_getPos_x3f(v_stx_4392_, v___y_4427_);
if (lean_obj_tag(v___x_4431_) == 0)
{
lean_object* v___x_4432_; 
v___x_4432_ = lean_unsigned_to_nat(0u);
v___y_4405_ = v___y_4429_;
v___y_4406_ = v_fileMap_4430_;
v___y_4407_ = v___y_4428_;
v___y_4408_ = v___x_4432_;
goto v___jp_4404_;
}
else
{
lean_object* v_val_4433_; 
v_val_4433_ = lean_ctor_get(v___x_4431_, 0);
lean_inc(v_val_4433_);
lean_dec_ref_known(v___x_4431_, 1);
v___y_4405_ = v___y_4429_;
v___y_4406_ = v_fileMap_4430_;
v___y_4407_ = v___y_4428_;
v___y_4408_ = v_val_4433_;
goto v___jp_4404_;
}
}
v___jp_4434_:
{
lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; 
lean_inc_ref(v___y_4438_);
v___x_4439_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4439_, 0, v___y_4438_);
v___x_4440_ = l_Lean_MessageData_ofFormat(v___x_4439_);
v___x_4441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4441_, 0, v___y_4437_);
lean_ctor_set(v___x_4441_, 1, v___x_4440_);
lean_inc(v___y_4436_);
v___x_4442_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___y_4436_, v___x_4441_, v___y_4393_, v___y_4394_);
if (lean_obj_tag(v___x_4442_) == 0)
{
lean_dec_ref_known(v___x_4442_, 1);
v___y_4427_ = v___y_4435_;
v___y_4428_ = v___y_4393_;
v___y_4429_ = v___y_4394_;
goto v___jp_4426_;
}
else
{
lean_dec_ref(v_opts_4403_);
lean_dec(v_stx_4392_);
return v___x_4442_;
}
}
v___jp_4443_:
{
lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; 
lean_inc_ref(v___y_4448_);
v___x_4449_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4449_, 0, v___y_4448_);
v___x_4450_ = l_Lean_MessageData_ofFormat(v___x_4449_);
v___x_4451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4451_, 0, v___y_4447_);
lean_ctor_set(v___x_4451_, 1, v___x_4450_);
v___x_4452_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1);
v___x_4453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4453_, 0, v___x_4451_);
lean_ctor_set(v___x_4453_, 1, v___x_4452_);
if (v___y_4446_ == 0)
{
lean_object* v___x_4454_; 
v___x_4454_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4435_ = v___y_4444_;
v___y_4436_ = v___y_4445_;
v___y_4437_ = v___x_4453_;
v___y_4438_ = v___x_4454_;
goto v___jp_4434_;
}
else
{
lean_object* v___x_4455_; 
v___x_4455_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4435_ = v___y_4444_;
v___y_4436_ = v___y_4445_;
v___y_4437_ = v___x_4453_;
v___y_4438_ = v___x_4455_;
goto v___jp_4434_;
}
}
v___jp_4456_:
{
lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; 
lean_inc_ref(v___y_4462_);
v___x_4463_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4463_, 0, v___y_4462_);
v___x_4464_ = l_Lean_MessageData_ofFormat(v___x_4463_);
lean_inc_ref(v___y_4457_);
v___x_4465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4465_, 0, v___y_4457_);
lean_ctor_set(v___x_4465_, 1, v___x_4464_);
v___x_4466_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5);
v___x_4467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4467_, 0, v___x_4465_);
lean_ctor_set(v___x_4467_, 1, v___x_4466_);
if (v___y_4461_ == 0)
{
lean_object* v___x_4468_; 
v___x_4468_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4444_ = v___y_4458_;
v___y_4445_ = v___y_4459_;
v___y_4446_ = v___y_4460_;
v___y_4447_ = v___x_4467_;
v___y_4448_ = v___x_4468_;
goto v___jp_4443_;
}
else
{
lean_object* v___x_4469_; 
v___x_4469_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4444_ = v___y_4458_;
v___y_4445_ = v___y_4459_;
v___y_4446_ = v___y_4460_;
v___y_4447_ = v___x_4467_;
v___y_4448_ = v___x_4469_;
goto v___jp_4443_;
}
}
v___jp_4470_:
{
lean_object* v___x_4474_; lean_object* v_a_4475_; uint8_t v___x_4476_; 
v___x_4474_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(v_stx_4392_, v___y_4393_, v___y_4394_);
v_a_4475_ = lean_ctor_get(v___x_4474_, 0);
lean_inc(v_a_4475_);
lean_dec_ref(v___x_4474_);
v___x_4476_ = lean_unbox(v_a_4475_);
if (v___x_4476_ == 0)
{
lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v_scopes_4480_; lean_object* v___x_4481_; lean_object* v_opts_4482_; uint8_t v_hasTrace_4483_; 
v___x_4477_ = l_Lean_inheritedTraceOptions;
v___x_4478_ = lean_st_ref_get(v___x_4477_);
v___x_4479_ = lean_st_ref_get(v___y_4394_);
v_scopes_4480_ = lean_ctor_get(v___x_4479_, 2);
lean_inc(v_scopes_4480_);
lean_dec(v___x_4479_);
v___x_4481_ = l_List_head_x21___redArg(v___x_4401_, v_scopes_4480_);
lean_dec(v_scopes_4480_);
v_opts_4482_ = lean_ctor_get(v___x_4481_, 1);
lean_inc_ref(v_opts_4482_);
lean_dec(v___x_4481_);
v_hasTrace_4483_ = lean_ctor_get_uint8(v_opts_4482_, sizeof(void*)*1);
if (v_hasTrace_4483_ == 0)
{
uint8_t v___x_4484_; 
lean_dec_ref(v_opts_4482_);
lean_dec(v___x_4478_);
v___x_4484_ = lean_unbox(v_a_4475_);
lean_dec(v_a_4475_);
v___y_4427_ = v___x_4484_;
v___y_4428_ = v___y_4393_;
v___y_4429_ = v___y_4394_;
goto v___jp_4426_;
}
else
{
lean_object* v___x_4485_; lean_object* v___x_4486_; uint8_t v___x_4487_; 
v___x_4485_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4486_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_4487_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4478_, v_opts_4482_, v___x_4486_);
lean_dec_ref(v_opts_4482_);
lean_dec(v___x_4478_);
if (v___x_4487_ == 0)
{
uint8_t v___x_4488_; 
v___x_4488_ = lean_unbox(v_a_4475_);
lean_dec(v_a_4475_);
v___y_4427_ = v___x_4488_;
v___y_4428_ = v___y_4393_;
v___y_4429_ = v___y_4394_;
goto v___jp_4426_;
}
else
{
lean_object* v___x_4489_; 
v___x_4489_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7);
if (v___y_4472_ == 0)
{
lean_object* v___x_4490_; uint8_t v___x_4491_; 
v___x_4490_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___x_4491_ = lean_unbox(v_a_4475_);
lean_dec(v_a_4475_);
v___y_4457_ = v___x_4489_;
v___y_4458_ = v___x_4491_;
v___y_4459_ = v___x_4485_;
v___y_4460_ = v___y_4471_;
v___y_4461_ = v___y_4473_;
v___y_4462_ = v___x_4490_;
goto v___jp_4456_;
}
else
{
lean_object* v___x_4492_; uint8_t v___x_4493_; 
v___x_4492_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___x_4493_ = lean_unbox(v_a_4475_);
lean_dec(v_a_4475_);
v___y_4457_ = v___x_4489_;
v___y_4458_ = v___x_4493_;
v___y_4459_ = v___x_4485_;
v___y_4460_ = v___y_4471_;
v___y_4461_ = v___y_4473_;
v___y_4462_ = v___x_4492_;
goto v___jp_4456_;
}
}
}
}
else
{
lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v_scopes_4497_; lean_object* v___x_4498_; lean_object* v_opts_4499_; uint8_t v_hasTrace_4500_; 
lean_dec(v_a_4475_);
lean_dec_ref(v_opts_4403_);
lean_dec(v_stx_4392_);
v___x_4494_ = l_Lean_inheritedTraceOptions;
v___x_4495_ = lean_st_ref_get(v___x_4494_);
v___x_4496_ = lean_st_ref_get(v___y_4394_);
v_scopes_4497_ = lean_ctor_get(v___x_4496_, 2);
lean_inc(v_scopes_4497_);
lean_dec(v___x_4496_);
v___x_4498_ = l_List_head_x21___redArg(v___x_4401_, v_scopes_4497_);
lean_dec(v_scopes_4497_);
v_opts_4499_ = lean_ctor_get(v___x_4498_, 1);
lean_inc_ref(v_opts_4499_);
lean_dec(v___x_4498_);
v_hasTrace_4500_ = lean_ctor_get_uint8(v_opts_4499_, sizeof(void*)*1);
if (v_hasTrace_4500_ == 0)
{
lean_dec_ref(v_opts_4499_);
lean_dec(v___x_4495_);
goto v___jp_4396_;
}
else
{
lean_object* v___x_4501_; lean_object* v___x_4502_; uint8_t v___x_4503_; 
v___x_4501_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4502_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_4503_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4495_, v_opts_4499_, v___x_4502_);
lean_dec_ref(v_opts_4499_);
lean_dec(v___x_4495_);
if (v___x_4503_ == 0)
{
goto v___jp_4396_;
}
else
{
lean_object* v___x_4504_; lean_object* v___x_4505_; 
v___x_4504_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9);
v___x_4505_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_4501_, v___x_4504_, v___y_4393_, v___y_4394_);
if (lean_obj_tag(v___x_4505_) == 0)
{
lean_dec_ref_known(v___x_4505_, 1);
goto v___jp_4396_;
}
else
{
return v___x_4505_;
}
}
}
}
}
v___jp_4506_:
{
lean_object* v___x_4508_; uint8_t v___x_4509_; lean_object* v___x_4510_; uint8_t v___x_4511_; 
v___x_4508_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
v___x_4509_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4403_, v___x_4508_);
v___x_4510_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v___x_4511_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4403_, v___x_4510_);
if (v___y_4507_ == 0)
{
if (v___x_4509_ == 0)
{
if (v___x_4511_ == 0)
{
lean_object* v___x_4512_; lean_object* v___x_4513_; 
lean_dec_ref(v_opts_4403_);
lean_dec(v_stx_4392_);
v___x_4512_ = lean_box(0);
v___x_4513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4513_, 0, v___x_4512_);
return v___x_4513_;
}
else
{
v___y_4471_ = v___x_4511_;
v___y_4472_ = v___y_4507_;
v___y_4473_ = v___x_4509_;
goto v___jp_4470_;
}
}
else
{
v___y_4471_ = v___x_4511_;
v___y_4472_ = v___y_4507_;
v___y_4473_ = v___x_4509_;
goto v___jp_4470_;
}
}
else
{
v___y_4471_ = v___x_4511_;
v___y_4472_ = v___y_4507_;
v___y_4473_ = v___x_4509_;
goto v___jp_4470_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___boxed(lean_object* v_stx_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_){
_start:
{
lean_object* v_res_4522_; 
v_res_4522_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(v_stx_4518_, v___y_4519_, v___y_4520_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
return v_res_4522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4535_; lean_object* v___x_4536_; 
v___x_4535_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook));
v___x_4536_ = l_Lean_Elab_Command_addLinter(v___x_4535_);
return v___x_4536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2____boxed(lean_object* v_a_4537_){
_start:
{
lean_object* v_res_4538_; 
v_res_4538_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_();
return v_res_4538_;
}
}
lean_object* runtime_initialize_Init_Try(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_InfoUtils(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Try(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Meta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_BuiltinTerm(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_AutoTry(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
