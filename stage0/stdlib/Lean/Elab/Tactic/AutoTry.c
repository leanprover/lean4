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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
extern lean_object* l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default;
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_337_; uint8_t v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v_fileName_364_; lean_object* v_fileMap_365_; lean_object* v_ref_366_; lean_object* v_cancelTk_x3f_367_; lean_object* v_a_369_; lean_object* v_a_376_; lean_object* v_currNamespace_378_; lean_object* v_openDecls_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v_env_386_; lean_object* v___x_387_; lean_object* v___y_389_; uint8_t v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; uint8_t v___y_492_; uint8_t v___y_493_; lean_object* v___x_513_; uint8_t v___x_514_; lean_object* v___y_516_; lean_object* v___y_517_; uint8_t v___y_555_; uint8_t v___x_575_; 
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
v___x_382_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19);
v___x_383_ = lean_box(0);
lean_inc(v_cancelTk_x3f_367_);
lean_inc(v_openDecls_379_);
lean_inc(v_currNamespace_378_);
lean_inc_ref(v_fileMap_365_);
lean_inc_ref(v_fileName_364_);
v___x_384_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_384_, 0, v_fileName_364_);
lean_ctor_set(v___x_384_, 1, v_fileMap_365_);
lean_ctor_set(v___x_384_, 2, v___x_380_);
lean_ctor_set(v___x_384_, 3, v___x_381_);
lean_ctor_set(v___x_384_, 4, v_currNamespace_378_);
lean_ctor_set(v___x_384_, 5, v_openDecls_379_);
lean_ctor_set(v___x_384_, 6, v___x_351_);
lean_ctor_set(v___x_384_, 7, v___x_382_);
lean_ctor_set(v___x_384_, 8, v___x_355_);
lean_ctor_set(v___x_384_, 9, v___x_352_);
lean_ctor_set(v___x_384_, 10, v_cancelTk_x3f_367_);
lean_ctor_set(v___x_384_, 11, v___x_362_);
v___x_385_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_385_, 0, v___x_384_);
lean_ctor_set(v___x_385_, 1, v___x_342_);
lean_ctor_set(v___x_385_, 2, v___x_383_);
lean_ctor_set_uint8(v___x_385_, sizeof(void*)*3, v___x_338_);
lean_ctor_set_uint8(v___x_385_, sizeof(void*)*3 + 1, v___x_338_);
v_env_386_ = lean_ctor_get(v___x_363_, 0);
lean_inc_ref(v_env_386_);
lean_dec(v___x_363_);
v___x_387_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_387_, 0, v_mctx_329_);
lean_ctor_set(v___x_387_, 1, v___x_346_);
lean_ctor_set(v___x_387_, 2, v___x_337_);
lean_ctor_set(v___x_387_, 3, v___x_347_);
lean_ctor_set(v___x_387_, 4, v___x_348_);
v___x_513_ = l_Lean_diagnostics;
v___x_514_ = lean_uint8_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23);
v___x_575_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_386_);
lean_dec_ref(v_env_386_);
if (v___x_514_ == 0)
{
if (v___x_575_ == 0)
{
lean_inc(v___x_360_);
v___y_516_ = v___x_385_;
v___y_517_ = v___x_360_;
goto v___jp_515_;
}
else
{
v___y_555_ = v___x_514_;
goto v___jp_554_;
}
}
else
{
v___y_555_ = v___x_575_;
goto v___jp_554_;
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
v___jp_388_:
{
lean_object* v___x_393_; lean_object* v_toCold_394_; lean_object* v_currRecDepth_395_; lean_object* v_ref_396_; uint8_t v_suppressElabErrors_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_487_; 
v___x_393_ = lean_st_mk_ref(v___x_387_);
v_toCold_394_ = lean_ctor_get(v___y_391_, 0);
v_currRecDepth_395_ = lean_ctor_get(v___y_391_, 1);
v_ref_396_ = lean_ctor_get(v___y_391_, 2);
v_suppressElabErrors_397_ = lean_ctor_get_uint8(v___y_391_, sizeof(void*)*3 + 1);
v_isSharedCheck_487_ = !lean_is_exclusive(v___y_391_);
if (v_isSharedCheck_487_ == 0)
{
v___x_399_ = v___y_391_;
v_isShared_400_ = v_isSharedCheck_487_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_ref_396_);
lean_inc(v_currRecDepth_395_);
lean_inc(v_toCold_394_);
lean_dec(v___y_391_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_487_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v_fileName_401_; lean_object* v_fileMap_402_; lean_object* v_currNamespace_403_; lean_object* v_openDecls_404_; lean_object* v_initHeartbeats_405_; lean_object* v_maxHeartbeats_406_; lean_object* v_quotContext_407_; lean_object* v_currMacroScope_408_; lean_object* v_cancelTk_x3f_409_; lean_object* v_inheritedTraceOptions_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_484_; 
v_fileName_401_ = lean_ctor_get(v_toCold_394_, 0);
v_fileMap_402_ = lean_ctor_get(v_toCold_394_, 1);
v_currNamespace_403_ = lean_ctor_get(v_toCold_394_, 4);
v_openDecls_404_ = lean_ctor_get(v_toCold_394_, 5);
v_initHeartbeats_405_ = lean_ctor_get(v_toCold_394_, 6);
v_maxHeartbeats_406_ = lean_ctor_get(v_toCold_394_, 7);
v_quotContext_407_ = lean_ctor_get(v_toCold_394_, 8);
v_currMacroScope_408_ = lean_ctor_get(v_toCold_394_, 9);
v_cancelTk_x3f_409_ = lean_ctor_get(v_toCold_394_, 10);
v_inheritedTraceOptions_410_ = lean_ctor_get(v_toCold_394_, 11);
v_isSharedCheck_484_ = !lean_is_exclusive(v_toCold_394_);
if (v_isSharedCheck_484_ == 0)
{
lean_object* v_unused_485_; lean_object* v_unused_486_; 
v_unused_485_ = lean_ctor_get(v_toCold_394_, 3);
lean_dec(v_unused_485_);
v_unused_486_ = lean_ctor_get(v_toCold_394_, 2);
lean_dec(v_unused_486_);
v___x_412_ = v_toCold_394_;
v_isShared_413_ = v_isSharedCheck_484_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_inheritedTraceOptions_410_);
lean_inc(v_cancelTk_x3f_409_);
lean_inc(v_currMacroScope_408_);
lean_inc(v_quotContext_407_);
lean_inc(v_maxHeartbeats_406_);
lean_inc(v_initHeartbeats_405_);
lean_inc(v_openDecls_404_);
lean_inc(v_currNamespace_403_);
lean_inc(v_fileMap_402_);
lean_inc(v_fileName_401_);
lean_dec(v_toCold_394_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_484_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_414_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__1(v_opts_331_, v___y_389_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 3, v___x_414_);
lean_ctor_set(v___x_412_, 2, v_opts_331_);
v___x_416_ = v___x_412_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_fileName_401_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v_fileMap_402_);
lean_ctor_set(v_reuseFailAlloc_483_, 2, v_opts_331_);
lean_ctor_set(v_reuseFailAlloc_483_, 3, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_483_, 4, v_currNamespace_403_);
lean_ctor_set(v_reuseFailAlloc_483_, 5, v_openDecls_404_);
lean_ctor_set(v_reuseFailAlloc_483_, 6, v_initHeartbeats_405_);
lean_ctor_set(v_reuseFailAlloc_483_, 7, v_maxHeartbeats_406_);
lean_ctor_set(v_reuseFailAlloc_483_, 8, v_quotContext_407_);
lean_ctor_set(v_reuseFailAlloc_483_, 9, v_currMacroScope_408_);
lean_ctor_set(v_reuseFailAlloc_483_, 10, v_cancelTk_x3f_409_);
lean_ctor_set(v_reuseFailAlloc_483_, 11, v_inheritedTraceOptions_410_);
v___x_416_ = v_reuseFailAlloc_483_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_418_; 
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_416_);
v___x_418_ = v___x_399_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_416_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v_currRecDepth_395_);
lean_ctor_set(v_reuseFailAlloc_482_, 2, v_ref_396_);
lean_ctor_set_uint8(v_reuseFailAlloc_482_, sizeof(void*)*3 + 1, v_suppressElabErrors_397_);
v___x_418_ = v_reuseFailAlloc_482_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_419_; 
lean_ctor_set_uint8(v___x_418_, sizeof(void*)*3, v___y_390_);
lean_inc(v___x_393_);
v___x_419_ = lean_apply_5(v_x_333_, v___x_345_, v___x_393_, v___x_418_, v___y_392_, lean_box(0));
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_466_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_466_ == 0)
{
v___x_422_ = v___x_419_;
v_isShared_423_ = v_isSharedCheck_466_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_466_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v_traceState_427_; lean_object* v_traceState_428_; lean_object* v_env_429_; lean_object* v_messages_430_; lean_object* v_scopes_431_; lean_object* v_usedQuotCtxts_432_; lean_object* v_nextMacroScope_433_; lean_object* v_maxRecDepth_434_; lean_object* v_ngen_435_; lean_object* v_auxDeclNGen_436_; lean_object* v_infoState_437_; lean_object* v_snapshotTasks_438_; lean_object* v_prevLinterStates_439_; lean_object* v_codeQualityEntryTasks_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_464_; 
v___x_424_ = lean_st_ref_get(v___x_393_);
lean_dec(v___x_393_);
lean_dec(v___x_424_);
v___x_425_ = lean_st_ref_get(v___x_360_);
lean_dec(v___x_360_);
v___x_426_ = lean_st_ref_take(v_a_335_);
v_traceState_427_ = lean_ctor_get(v___x_426_, 9);
lean_inc_ref(v_traceState_427_);
v_traceState_428_ = lean_ctor_get(v___x_425_, 4);
lean_inc_ref(v_traceState_428_);
v_env_429_ = lean_ctor_get(v___x_426_, 0);
v_messages_430_ = lean_ctor_get(v___x_426_, 1);
v_scopes_431_ = lean_ctor_get(v___x_426_, 2);
v_usedQuotCtxts_432_ = lean_ctor_get(v___x_426_, 3);
v_nextMacroScope_433_ = lean_ctor_get(v___x_426_, 4);
v_maxRecDepth_434_ = lean_ctor_get(v___x_426_, 5);
v_ngen_435_ = lean_ctor_get(v___x_426_, 6);
v_auxDeclNGen_436_ = lean_ctor_get(v___x_426_, 7);
v_infoState_437_ = lean_ctor_get(v___x_426_, 8);
v_snapshotTasks_438_ = lean_ctor_get(v___x_426_, 10);
v_prevLinterStates_439_ = lean_ctor_get(v___x_426_, 11);
v_codeQualityEntryTasks_440_ = lean_ctor_get(v___x_426_, 12);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; 
v_unused_465_ = lean_ctor_get(v___x_426_, 9);
lean_dec(v_unused_465_);
v___x_442_ = v___x_426_;
v_isShared_443_ = v_isSharedCheck_464_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_codeQualityEntryTasks_440_);
lean_inc(v_prevLinterStates_439_);
lean_inc(v_snapshotTasks_438_);
lean_inc(v_infoState_437_);
lean_inc(v_auxDeclNGen_436_);
lean_inc(v_ngen_435_);
lean_inc(v_maxRecDepth_434_);
lean_inc(v_nextMacroScope_433_);
lean_inc(v_usedQuotCtxts_432_);
lean_inc(v_scopes_431_);
lean_inc(v_messages_430_);
lean_inc(v_env_429_);
lean_dec(v___x_426_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_464_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v_messages_444_; uint64_t v_tid_445_; lean_object* v_traces_446_; lean_object* v_traces_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_463_; 
v_messages_444_ = lean_ctor_get(v___x_425_, 6);
lean_inc_ref(v_messages_444_);
lean_dec(v___x_425_);
v_tid_445_ = lean_ctor_get_uint64(v_traceState_427_, sizeof(void*)*1);
v_traces_446_ = lean_ctor_get(v_traceState_427_, 0);
lean_inc_ref(v_traces_446_);
lean_dec_ref(v_traceState_427_);
v_traces_447_ = lean_ctor_get(v_traceState_428_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v_traceState_428_);
if (v_isSharedCheck_463_ == 0)
{
v___x_449_ = v_traceState_428_;
v_isShared_450_ = v_isSharedCheck_463_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_traces_447_);
lean_dec(v_traceState_428_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_463_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_454_; 
v___x_451_ = l_Lean_MessageLog_append(v_messages_430_, v_messages_444_);
v___x_452_ = l_Lean_PersistentArray_append___redArg(v_traces_446_, v_traces_447_);
lean_dec_ref(v_traces_447_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_452_);
v___x_454_ = v___x_449_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_452_);
v___x_454_ = v_reuseFailAlloc_462_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v___x_456_; 
lean_ctor_set_uint64(v___x_454_, sizeof(void*)*1, v_tid_445_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 9, v___x_454_);
lean_ctor_set(v___x_442_, 1, v___x_451_);
v___x_456_ = v___x_442_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_env_429_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v___x_451_);
lean_ctor_set(v_reuseFailAlloc_461_, 2, v_scopes_431_);
lean_ctor_set(v_reuseFailAlloc_461_, 3, v_usedQuotCtxts_432_);
lean_ctor_set(v_reuseFailAlloc_461_, 4, v_nextMacroScope_433_);
lean_ctor_set(v_reuseFailAlloc_461_, 5, v_maxRecDepth_434_);
lean_ctor_set(v_reuseFailAlloc_461_, 6, v_ngen_435_);
lean_ctor_set(v_reuseFailAlloc_461_, 7, v_auxDeclNGen_436_);
lean_ctor_set(v_reuseFailAlloc_461_, 8, v_infoState_437_);
lean_ctor_set(v_reuseFailAlloc_461_, 9, v___x_454_);
lean_ctor_set(v_reuseFailAlloc_461_, 10, v_snapshotTasks_438_);
lean_ctor_set(v_reuseFailAlloc_461_, 11, v_prevLinterStates_439_);
lean_ctor_set(v_reuseFailAlloc_461_, 12, v_codeQualityEntryTasks_440_);
v___x_456_ = v_reuseFailAlloc_461_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_457_; lean_object* v___x_459_; 
v___x_457_ = lean_st_ref_put(v_a_335_, v___x_456_);
if (v_isShared_423_ == 0)
{
v___x_459_ = v___x_422_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_420_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_467_; 
lean_dec(v___x_393_);
lean_dec(v___x_360_);
v_a_467_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_a_467_);
lean_dec_ref_known(v___x_419_, 1);
if (lean_obj_tag(v_a_467_) == 0)
{
lean_object* v_msg_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v_msg_468_ = lean_ctor_get(v_a_467_, 1);
lean_inc_ref(v_msg_468_);
lean_dec_ref_known(v_a_467_, 2);
v___x_469_ = l_Lean_MessageData_toString(v_msg_468_);
v___x_470_ = lean_mk_io_user_error(v___x_469_);
v_a_369_ = v___x_470_;
goto v___jp_368_;
}
else
{
lean_object* v_id_471_; lean_object* v___x_472_; 
v_id_471_ = lean_ctor_get(v_a_467_, 0);
lean_inc(v_id_471_);
lean_dec_ref_known(v_a_467_, 2);
v___x_472_ = l_Lean_InternalExceptionId_getName(v_id_471_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
lean_dec(v_id_471_);
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
lean_dec_ref_known(v___x_472_, 1);
v___x_474_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20));
v___x_475_ = l_Lean_Name_toString(v_a_473_, v___x_340_);
v___x_476_ = lean_string_append(v___x_474_, v___x_475_);
lean_dec_ref(v___x_475_);
v_a_376_ = v___x_476_;
goto v___jp_375_;
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec_ref_known(v___x_472_, 1);
v___x_477_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21));
v___x_478_ = l_Nat_reprFast(v_id_471_);
v___x_479_ = lean_string_append(v___x_477_, v___x_478_);
lean_dec_ref(v___x_478_);
v___x_480_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__22));
v___x_481_ = lean_string_append(v___x_479_, v___x_480_);
v_a_376_ = v___x_481_;
goto v___jp_375_;
}
}
}
}
}
}
}
}
v___jp_488_:
{
if (v___y_493_ == 0)
{
lean_object* v___x_494_; lean_object* v_env_495_; lean_object* v_nextMacroScope_496_; lean_object* v_ngen_497_; lean_object* v_auxDeclNGen_498_; lean_object* v_traceState_499_; lean_object* v_messages_500_; lean_object* v_infoState_501_; lean_object* v_snapshotTasks_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_511_; 
v___x_494_ = lean_st_ref_take(v___y_491_);
v_env_495_ = lean_ctor_get(v___x_494_, 0);
v_nextMacroScope_496_ = lean_ctor_get(v___x_494_, 1);
v_ngen_497_ = lean_ctor_get(v___x_494_, 2);
v_auxDeclNGen_498_ = lean_ctor_get(v___x_494_, 3);
v_traceState_499_ = lean_ctor_get(v___x_494_, 4);
v_messages_500_ = lean_ctor_get(v___x_494_, 6);
v_infoState_501_ = lean_ctor_get(v___x_494_, 7);
v_snapshotTasks_502_ = lean_ctor_get(v___x_494_, 8);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_511_ == 0)
{
lean_object* v_unused_512_; 
v_unused_512_ = lean_ctor_get(v___x_494_, 5);
lean_dec(v_unused_512_);
v___x_504_ = v___x_494_;
v_isShared_505_ = v_isSharedCheck_511_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_snapshotTasks_502_);
lean_inc(v_infoState_501_);
lean_inc(v_messages_500_);
lean_inc(v_traceState_499_);
lean_inc(v_auxDeclNGen_498_);
lean_inc(v_ngen_497_);
lean_inc(v_nextMacroScope_496_);
lean_inc(v_env_495_);
lean_dec(v___x_494_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_511_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_506_; lean_object* v___x_508_; 
v___x_506_ = l_Lean_Kernel_enableDiag(v_env_495_, v___y_492_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 5, v___x_349_);
lean_ctor_set(v___x_504_, 0, v___x_506_);
v___x_508_ = v___x_504_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_506_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_nextMacroScope_496_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v_ngen_497_);
lean_ctor_set(v_reuseFailAlloc_510_, 3, v_auxDeclNGen_498_);
lean_ctor_set(v_reuseFailAlloc_510_, 4, v_traceState_499_);
lean_ctor_set(v_reuseFailAlloc_510_, 5, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_510_, 6, v_messages_500_);
lean_ctor_set(v_reuseFailAlloc_510_, 7, v_infoState_501_);
lean_ctor_set(v_reuseFailAlloc_510_, 8, v_snapshotTasks_502_);
v___x_508_ = v_reuseFailAlloc_510_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_509_; 
v___x_509_ = lean_st_ref_put(v___y_491_, v___x_508_);
v___y_389_ = v___y_489_;
v___y_390_ = v___y_492_;
v___y_391_ = v___y_490_;
v___y_392_ = v___y_491_;
goto v___jp_388_;
}
}
}
else
{
v___y_389_ = v___y_489_;
v___y_390_ = v___y_492_;
v___y_391_ = v___y_490_;
v___y_392_ = v___y_491_;
goto v___jp_388_;
}
}
v___jp_515_:
{
lean_object* v___x_518_; lean_object* v_toCold_519_; lean_object* v_currRecDepth_520_; lean_object* v_ref_521_; uint8_t v_suppressElabErrors_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_553_; 
v___x_518_ = lean_st_ref_get(v___y_517_);
v_toCold_519_ = lean_ctor_get(v___y_516_, 0);
v_currRecDepth_520_ = lean_ctor_get(v___y_516_, 1);
v_ref_521_ = lean_ctor_get(v___y_516_, 2);
v_suppressElabErrors_522_ = lean_ctor_get_uint8(v___y_516_, sizeof(void*)*3 + 1);
v_isSharedCheck_553_ = !lean_is_exclusive(v___y_516_);
if (v_isSharedCheck_553_ == 0)
{
v___x_524_ = v___y_516_;
v_isShared_525_ = v_isSharedCheck_553_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_ref_521_);
lean_inc(v_currRecDepth_520_);
lean_inc(v_toCold_519_);
lean_dec(v___y_516_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_553_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v_fileName_526_; lean_object* v_fileMap_527_; lean_object* v_currNamespace_528_; lean_object* v_openDecls_529_; lean_object* v_initHeartbeats_530_; lean_object* v_maxHeartbeats_531_; lean_object* v_quotContext_532_; lean_object* v_currMacroScope_533_; lean_object* v_cancelTk_x3f_534_; lean_object* v_inheritedTraceOptions_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_550_; 
v_fileName_526_ = lean_ctor_get(v_toCold_519_, 0);
v_fileMap_527_ = lean_ctor_get(v_toCold_519_, 1);
v_currNamespace_528_ = lean_ctor_get(v_toCold_519_, 4);
v_openDecls_529_ = lean_ctor_get(v_toCold_519_, 5);
v_initHeartbeats_530_ = lean_ctor_get(v_toCold_519_, 6);
v_maxHeartbeats_531_ = lean_ctor_get(v_toCold_519_, 7);
v_quotContext_532_ = lean_ctor_get(v_toCold_519_, 8);
v_currMacroScope_533_ = lean_ctor_get(v_toCold_519_, 9);
v_cancelTk_x3f_534_ = lean_ctor_get(v_toCold_519_, 10);
v_inheritedTraceOptions_535_ = lean_ctor_get(v_toCold_519_, 11);
v_isSharedCheck_550_ = !lean_is_exclusive(v_toCold_519_);
if (v_isSharedCheck_550_ == 0)
{
lean_object* v_unused_551_; lean_object* v_unused_552_; 
v_unused_551_ = lean_ctor_get(v_toCold_519_, 3);
lean_dec(v_unused_551_);
v_unused_552_ = lean_ctor_get(v_toCold_519_, 2);
lean_dec(v_unused_552_);
v___x_537_ = v_toCold_519_;
v_isShared_538_ = v_isSharedCheck_550_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_inheritedTraceOptions_535_);
lean_inc(v_cancelTk_x3f_534_);
lean_inc(v_currMacroScope_533_);
lean_inc(v_quotContext_532_);
lean_inc(v_maxHeartbeats_531_);
lean_inc(v_initHeartbeats_530_);
lean_inc(v_openDecls_529_);
lean_inc(v_currNamespace_528_);
lean_inc(v_fileMap_527_);
lean_inc(v_fileName_526_);
lean_dec(v_toCold_519_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_550_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v_env_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
v_env_539_ = lean_ctor_get(v___x_518_, 0);
lean_inc_ref(v_env_539_);
lean_dec(v___x_518_);
v___x_540_ = l_Lean_maxRecDepth;
v___x_541_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 3, v___x_541_);
lean_ctor_set(v___x_537_, 2, v___x_380_);
v___x_543_ = v___x_537_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_fileName_526_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_fileMap_527_);
lean_ctor_set(v_reuseFailAlloc_549_, 2, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_549_, 3, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_549_, 4, v_currNamespace_528_);
lean_ctor_set(v_reuseFailAlloc_549_, 5, v_openDecls_529_);
lean_ctor_set(v_reuseFailAlloc_549_, 6, v_initHeartbeats_530_);
lean_ctor_set(v_reuseFailAlloc_549_, 7, v_maxHeartbeats_531_);
lean_ctor_set(v_reuseFailAlloc_549_, 8, v_quotContext_532_);
lean_ctor_set(v_reuseFailAlloc_549_, 9, v_currMacroScope_533_);
lean_ctor_set(v_reuseFailAlloc_549_, 10, v_cancelTk_x3f_534_);
lean_ctor_set(v_reuseFailAlloc_549_, 11, v_inheritedTraceOptions_535_);
v___x_543_ = v_reuseFailAlloc_549_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_545_; 
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v___x_543_);
v___x_545_ = v___x_524_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_currRecDepth_520_);
lean_ctor_set(v_reuseFailAlloc_548_, 2, v_ref_521_);
lean_ctor_set_uint8(v_reuseFailAlloc_548_, sizeof(void*)*3 + 1, v_suppressElabErrors_522_);
v___x_545_ = v_reuseFailAlloc_548_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
uint8_t v___x_546_; uint8_t v___x_547_; 
lean_ctor_set_uint8(v___x_545_, sizeof(void*)*3, v___x_514_);
v___x_546_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_331_, v___x_513_);
v___x_547_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_539_);
lean_dec_ref(v_env_539_);
if (v___x_546_ == 0)
{
if (v___x_547_ == 0)
{
v___y_389_ = v___x_540_;
v___y_390_ = v___x_546_;
v___y_391_ = v___x_545_;
v___y_392_ = v___y_517_;
goto v___jp_388_;
}
else
{
v___y_489_ = v___x_540_;
v___y_490_ = v___x_545_;
v___y_491_ = v___y_517_;
v___y_492_ = v___x_546_;
v___y_493_ = v___x_546_;
goto v___jp_488_;
}
}
else
{
v___y_489_ = v___x_540_;
v___y_490_ = v___x_545_;
v___y_491_ = v___y_517_;
v___y_492_ = v___x_546_;
v___y_493_ = v___x_547_;
goto v___jp_488_;
}
}
}
}
}
}
v___jp_554_:
{
if (v___y_555_ == 0)
{
lean_object* v___x_556_; lean_object* v_env_557_; lean_object* v_nextMacroScope_558_; lean_object* v_ngen_559_; lean_object* v_auxDeclNGen_560_; lean_object* v_traceState_561_; lean_object* v_messages_562_; lean_object* v_infoState_563_; lean_object* v_snapshotTasks_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_573_; 
v___x_556_ = lean_st_ref_take(v___x_360_);
v_env_557_ = lean_ctor_get(v___x_556_, 0);
v_nextMacroScope_558_ = lean_ctor_get(v___x_556_, 1);
v_ngen_559_ = lean_ctor_get(v___x_556_, 2);
v_auxDeclNGen_560_ = lean_ctor_get(v___x_556_, 3);
v_traceState_561_ = lean_ctor_get(v___x_556_, 4);
v_messages_562_ = lean_ctor_get(v___x_556_, 6);
v_infoState_563_ = lean_ctor_get(v___x_556_, 7);
v_snapshotTasks_564_ = lean_ctor_get(v___x_556_, 8);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; 
v_unused_574_ = lean_ctor_get(v___x_556_, 5);
lean_dec(v_unused_574_);
v___x_566_ = v___x_556_;
v_isShared_567_ = v_isSharedCheck_573_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_snapshotTasks_564_);
lean_inc(v_infoState_563_);
lean_inc(v_messages_562_);
lean_inc(v_traceState_561_);
lean_inc(v_auxDeclNGen_560_);
lean_inc(v_ngen_559_);
lean_inc(v_nextMacroScope_558_);
lean_inc(v_env_557_);
lean_dec(v___x_556_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_573_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_568_ = l_Lean_Kernel_enableDiag(v_env_557_, v___x_514_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 5, v___x_349_);
lean_ctor_set(v___x_566_, 0, v___x_568_);
v___x_570_ = v___x_566_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_nextMacroScope_558_);
lean_ctor_set(v_reuseFailAlloc_572_, 2, v_ngen_559_);
lean_ctor_set(v_reuseFailAlloc_572_, 3, v_auxDeclNGen_560_);
lean_ctor_set(v_reuseFailAlloc_572_, 4, v_traceState_561_);
lean_ctor_set(v_reuseFailAlloc_572_, 5, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_572_, 6, v_messages_562_);
lean_ctor_set(v_reuseFailAlloc_572_, 7, v_infoState_563_);
lean_ctor_set(v_reuseFailAlloc_572_, 8, v_snapshotTasks_564_);
v___x_570_ = v_reuseFailAlloc_572_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_571_; 
v___x_571_ = lean_st_ref_put(v___x_360_, v___x_570_);
lean_inc(v___x_360_);
v___y_516_ = v___x_385_;
v___y_517_ = v___x_360_;
goto v___jp_515_;
}
}
}
else
{
lean_inc(v___x_360_);
v___y_516_ = v___x_385_;
v___y_517_ = v___x_360_;
goto v___jp_515_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___boxed(lean_object* v_env_576_, lean_object* v_mctx_577_, lean_object* v_lctx_578_, lean_object* v_opts_579_, lean_object* v_namingCtx_580_, lean_object* v_x_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_576_, v_mctx_577_, v_lctx_578_, v_opts_579_, v_namingCtx_580_, v_x_581_, v_a_582_, v_a_583_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
lean_dec_ref(v_namingCtx_580_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope(lean_object* v_00_u03b1_586_, lean_object* v_env_587_, lean_object* v_mctx_588_, lean_object* v_lctx_589_, lean_object* v_opts_590_, lean_object* v_namingCtx_591_, lean_object* v_x_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_587_, v_mctx_588_, v_lctx_589_, v_opts_590_, v_namingCtx_591_, v_x_592_, v_a_593_, v_a_594_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___boxed(lean_object* v_00_u03b1_597_, lean_object* v_env_598_, lean_object* v_mctx_599_, lean_object* v_lctx_600_, lean_object* v_opts_601_, lean_object* v_namingCtx_602_, lean_object* v_x_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope(v_00_u03b1_597_, v_env_598_, v_mctx_599_, v_lctx_600_, v_opts_601_, v_namingCtx_602_, v_x_603_, v_a_604_, v_a_605_);
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
lean_dec_ref(v_namingCtx_602_);
return v_res_607_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(lean_object* v_stx_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_Syntax_getKind(v_stx_611_);
if (lean_obj_tag(v___x_612_) == 1)
{
lean_object* v_pre_613_; 
v_pre_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_pre_613_);
if (lean_obj_tag(v_pre_613_) == 1)
{
lean_object* v_pre_614_; 
v_pre_614_ = lean_ctor_get(v_pre_613_, 0);
lean_inc(v_pre_614_);
if (lean_obj_tag(v_pre_614_) == 1)
{
lean_object* v_pre_615_; 
v_pre_615_ = lean_ctor_get(v_pre_614_, 0);
lean_inc(v_pre_615_);
if (lean_obj_tag(v_pre_615_) == 1)
{
lean_object* v_pre_616_; 
v_pre_616_ = lean_ctor_get(v_pre_615_, 0);
if (lean_obj_tag(v_pre_616_) == 0)
{
lean_object* v_str_617_; lean_object* v_str_618_; lean_object* v_str_619_; lean_object* v_str_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v_str_617_ = lean_ctor_get(v___x_612_, 1);
lean_inc_ref(v_str_617_);
lean_dec_ref_known(v___x_612_, 2);
v_str_618_ = lean_ctor_get(v_pre_613_, 1);
lean_inc_ref(v_str_618_);
lean_dec_ref_known(v_pre_613_, 2);
v_str_619_ = lean_ctor_get(v_pre_614_, 1);
lean_inc_ref(v_str_619_);
lean_dec_ref_known(v_pre_614_, 2);
v_str_620_ = lean_ctor_get(v_pre_615_, 1);
lean_inc_ref(v_str_620_);
lean_dec_ref_known(v_pre_615_, 2);
v___x_621_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_622_ = lean_string_dec_eq(v_str_620_, v___x_621_);
lean_dec_ref(v_str_620_);
if (v___x_622_ == 0)
{
lean_dec_ref(v_str_619_);
lean_dec_ref(v_str_618_);
lean_dec_ref(v_str_617_);
return v___x_622_;
}
else
{
lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_623_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0));
v___x_624_ = lean_string_dec_eq(v_str_619_, v___x_623_);
lean_dec_ref(v_str_619_);
if (v___x_624_ == 0)
{
lean_dec_ref(v_str_618_);
lean_dec_ref(v_str_617_);
return v___x_624_;
}
else
{
lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_625_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_626_ = lean_string_dec_eq(v_str_618_, v___x_625_);
lean_dec_ref(v_str_618_);
if (v___x_626_ == 0)
{
lean_dec_ref(v_str_617_);
return v___x_626_;
}
else
{
lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_627_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__1));
v___x_628_ = lean_string_dec_eq(v_str_617_, v___x_627_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_629_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__2));
v___x_630_ = lean_string_dec_eq(v_str_617_, v___x_629_);
lean_dec_ref(v_str_617_);
return v___x_630_;
}
else
{
lean_dec_ref(v_str_617_);
return v___x_628_;
}
}
}
}
}
else
{
uint8_t v___x_631_; 
lean_dec_ref_known(v_pre_615_, 2);
lean_dec_ref_known(v_pre_614_, 2);
lean_dec_ref_known(v_pre_613_, 2);
lean_dec_ref_known(v___x_612_, 2);
v___x_631_ = 0;
return v___x_631_;
}
}
else
{
uint8_t v___x_632_; 
lean_dec_ref_known(v_pre_614_, 2);
lean_dec(v_pre_615_);
lean_dec_ref_known(v_pre_613_, 2);
lean_dec_ref_known(v___x_612_, 2);
v___x_632_ = 0;
return v___x_632_;
}
}
else
{
uint8_t v___x_633_; 
lean_dec(v_pre_614_);
lean_dec_ref_known(v_pre_613_, 2);
lean_dec_ref_known(v___x_612_, 2);
v___x_633_ = 0;
return v___x_633_;
}
}
else
{
uint8_t v___x_634_; 
lean_dec(v_pre_613_);
lean_dec_ref_known(v___x_612_, 2);
v___x_634_ = 0;
return v___x_634_;
}
}
else
{
uint8_t v___x_635_; 
lean_dec(v___x_612_);
v___x_635_ = 0;
return v___x_635_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___boxed(lean_object* v_stx_636_){
_start:
{
uint8_t v_res_637_; lean_object* v_r_638_; 
v_res_637_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(v_stx_636_);
v_r_638_ = lean_box(v_res_637_);
return v_r_638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx(lean_object* v_x_639_){
_start:
{
if (lean_obj_tag(v_x_639_) == 0)
{
lean_object* v___x_640_; 
v___x_640_ = lean_unsigned_to_nat(0u);
return v___x_640_;
}
else
{
lean_object* v___x_641_; 
v___x_641_ = lean_unsigned_to_nat(1u);
return v___x_641_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx___boxed(lean_object* v_x_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx(v_x_642_);
lean_dec(v_x_642_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(lean_object* v_t_644_, lean_object* v_k_645_){
_start:
{
if (lean_obj_tag(v_t_644_) == 0)
{
lean_object* v_tacticSeq_646_; lean_object* v_insertPos_647_; lean_object* v___x_648_; 
v_tacticSeq_646_ = lean_ctor_get(v_t_644_, 0);
lean_inc(v_tacticSeq_646_);
v_insertPos_647_ = lean_ctor_get(v_t_644_, 1);
lean_inc(v_insertPos_647_);
lean_dec_ref_known(v_t_644_, 2);
v___x_648_ = lean_apply_2(v_k_645_, v_tacticSeq_646_, v_insertPos_647_);
return v___x_648_;
}
else
{
return v_k_645_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim(lean_object* v_motive_649_, lean_object* v_ctorIdx_650_, lean_object* v_t_651_, lean_object* v_h_652_, lean_object* v_k_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_651_, v_k_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___boxed(lean_object* v_motive_655_, lean_object* v_ctorIdx_656_, lean_object* v_t_657_, lean_object* v_h_658_, lean_object* v_k_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim(v_motive_655_, v_ctorIdx_656_, v_t_657_, v_h_658_, v_k_659_);
lean_dec(v_ctorIdx_656_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_unsolvedGoal_elim___redArg(lean_object* v_t_661_, lean_object* v_unsolvedGoal_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_661_, v_unsolvedGoal_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_unsolvedGoal_elim(lean_object* v_motive_664_, lean_object* v_t_665_, lean_object* v_h_666_, lean_object* v_unsolvedGoal_667_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_665_, v_unsolvedGoal_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_sorryTactic_elim___redArg(lean_object* v_t_669_, lean_object* v_sorryTactic_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_669_, v_sorryTactic_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_sorryTactic_elim(lean_object* v_motive_672_, lean_object* v_t_673_, lean_object* v_h_674_, lean_object* v_sorryTactic_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_673_, v_sorryTactic_675_);
return v___x_676_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed__const__1(void){
_start:
{
uint32_t v___x_680_; lean_object* v___x_681_; 
v___x_680_ = 32;
v___x_681_ = lean_box_uint32(v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(lean_object* v_tacticSeq_682_, lean_object* v_fileMap_683_){
_start:
{
uint8_t v___x_684_; lean_object* v___x_685_; 
v___x_684_ = 0;
v___x_685_ = l_Lean_Syntax_getPos_x3f(v_tacticSeq_682_, v___x_684_);
if (lean_obj_tag(v___x_685_) == 1)
{
lean_object* v_val_686_; lean_object* v___x_687_; 
v_val_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_val_686_);
lean_dec_ref_known(v___x_685_, 1);
v___x_687_ = l_Lean_Syntax_getTailPos_x3f(v_tacticSeq_682_, v___x_684_);
if (lean_obj_tag(v___x_687_) == 1)
{
lean_object* v_val_688_; lean_object* v_startPos_689_; lean_object* v_line_690_; lean_object* v_column_691_; lean_object* v_endPos_692_; lean_object* v_line_693_; uint8_t v___x_694_; 
v_val_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_val_688_);
lean_dec_ref_known(v___x_687_, 1);
lean_inc_ref(v_fileMap_683_);
v_startPos_689_ = l_Lean_FileMap_toPosition(v_fileMap_683_, v_val_686_);
lean_dec(v_val_686_);
v_line_690_ = lean_ctor_get(v_startPos_689_, 0);
lean_inc(v_line_690_);
v_column_691_ = lean_ctor_get(v_startPos_689_, 1);
lean_inc(v_column_691_);
lean_dec_ref(v_startPos_689_);
v_endPos_692_ = l_Lean_FileMap_toPosition(v_fileMap_683_, v_val_688_);
lean_dec(v_val_688_);
v_line_693_ = lean_ctor_get(v_endPos_692_, 0);
lean_inc(v_line_693_);
lean_dec_ref(v_endPos_692_);
v___x_694_ = lean_nat_dec_eq(v_line_690_, v_line_693_);
lean_dec(v_line_693_);
lean_dec(v_line_690_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_695_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__0));
v___x_696_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed__const__1;
v___x_697_ = l_List_replicateTR___redArg(v_column_691_, v___x_696_);
v___x_698_ = lean_string_mk(v___x_697_);
v___x_699_ = lean_string_append(v___x_695_, v___x_698_);
lean_dec_ref(v___x_698_);
return v___x_699_;
}
else
{
lean_object* v___x_700_; 
lean_dec(v_column_691_);
v___x_700_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__1));
return v___x_700_;
}
}
else
{
lean_object* v___x_701_; 
lean_dec(v___x_687_);
lean_dec(v_val_686_);
lean_dec_ref(v_fileMap_683_);
v___x_701_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__2));
return v___x_701_;
}
}
else
{
lean_object* v___x_702_; 
lean_dec(v___x_685_);
lean_dec_ref(v_fileMap_683_);
v___x_702_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__2));
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed(lean_object* v_tacticSeq_703_, lean_object* v_fileMap_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(v_tacticSeq_703_, v_fileMap_704_);
lean_dec(v_tacticSeq_703_);
return v_res_705_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_708_ = lean_string_utf8_byte_size(v___x_707_);
return v___x_708_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2(void){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_709_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1);
v___x_710_ = lean_unsigned_to_nat(0u);
v___x_711_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_712_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
lean_ctor_set(v___x_712_, 1, v___x_710_);
lean_ctor_set(v___x_712_, 2, v___x_709_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx(lean_object* v_p_713_){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_714_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_715_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2);
lean_inc(v_p_713_);
v___x_716_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
lean_ctor_set(v___x_716_, 1, v_p_713_);
lean_ctor_set(v___x_716_, 2, v___x_715_);
lean_ctor_set(v___x_716_, 3, v_p_713_);
v___x_717_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
lean_ctor_set(v___x_717_, 1, v___x_714_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(lean_object* v_range_718_){
_start:
{
lean_object* v_start_719_; lean_object* v_stop_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_730_; 
v_start_719_ = lean_ctor_get(v_range_718_, 0);
v_stop_720_ = lean_ctor_get(v_range_718_, 1);
v_isSharedCheck_730_ = !lean_is_exclusive(v_range_718_);
if (v_isSharedCheck_730_ == 0)
{
v___x_722_ = v_range_718_;
v_isShared_723_ = v_isSharedCheck_730_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_stop_720_);
lean_inc(v_start_719_);
lean_dec(v_range_718_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_730_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_724_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_725_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2);
v___x_726_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
lean_ctor_set(v___x_726_, 1, v_start_719_);
lean_ctor_set(v___x_726_, 2, v___x_725_);
lean_ctor_set(v___x_726_, 3, v_stop_720_);
if (v_isShared_723_ == 0)
{
lean_ctor_set_tag(v___x_722_, 2);
lean_ctor_set(v___x_722_, 1, v___x_724_);
lean_ctor_set(v___x_722_, 0, v___x_726_);
v___x_728_ = v___x_722_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v___x_724_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(lean_object* v_mc_x3f_731_, lean_object* v_nc_x3f_732_, lean_object* v_msg_733_, lean_object* v_acc_734_){
_start:
{
switch(lean_obj_tag(v_msg_733_))
{
case 3:
{
lean_object* v_a_735_; lean_object* v_a_736_; lean_object* v___x_737_; 
lean_dec(v_mc_x3f_731_);
v_a_735_ = lean_ctor_get(v_msg_733_, 0);
v_a_736_ = lean_ctor_get(v_msg_733_, 1);
lean_inc_ref(v_a_735_);
v___x_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_737_, 0, v_a_735_);
v_mc_x3f_731_ = v___x_737_;
v_msg_733_ = v_a_736_;
goto _start;
}
case 4:
{
lean_object* v_a_739_; lean_object* v_a_740_; lean_object* v___x_741_; 
lean_dec(v_nc_x3f_732_);
v_a_739_ = lean_ctor_get(v_msg_733_, 0);
v_a_740_ = lean_ctor_get(v_msg_733_, 1);
lean_inc_ref(v_a_739_);
v___x_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_741_, 0, v_a_739_);
v_nc_x3f_732_ = v___x_741_;
v_msg_733_ = v_a_740_;
goto _start;
}
case 5:
{
lean_object* v_a_743_; 
v_a_743_ = lean_ctor_get(v_msg_733_, 1);
v_msg_733_ = v_a_743_;
goto _start;
}
case 6:
{
lean_object* v_a_745_; 
v_a_745_ = lean_ctor_get(v_msg_733_, 0);
v_msg_733_ = v_a_745_;
goto _start;
}
case 8:
{
lean_object* v_a_747_; 
v_a_747_ = lean_ctor_get(v_msg_733_, 1);
v_msg_733_ = v_a_747_;
goto _start;
}
case 7:
{
lean_object* v_a_749_; lean_object* v_a_750_; lean_object* v___x_751_; 
v_a_749_ = lean_ctor_get(v_msg_733_, 0);
v_a_750_ = lean_ctor_get(v_msg_733_, 1);
lean_inc(v_nc_x3f_732_);
lean_inc(v_mc_x3f_731_);
v___x_751_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_731_, v_nc_x3f_732_, v_a_749_, v_acc_734_);
v_msg_733_ = v_a_750_;
v_acc_734_ = v___x_751_;
goto _start;
}
case 2:
{
lean_object* v_a_753_; 
v_a_753_ = lean_ctor_get(v_msg_733_, 1);
v_msg_733_ = v_a_753_;
goto _start;
}
case 9:
{
lean_object* v_msg_755_; lean_object* v_children_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v_msg_755_ = lean_ctor_get(v_msg_733_, 1);
v_children_756_ = lean_ctor_get(v_msg_733_, 2);
lean_inc(v_nc_x3f_732_);
lean_inc(v_mc_x3f_731_);
v___x_757_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_731_, v_nc_x3f_732_, v_msg_755_, v_acc_734_);
v___x_758_ = lean_unsigned_to_nat(0u);
v___x_759_ = lean_array_get_size(v_children_756_);
v___x_760_ = lean_nat_dec_lt(v___x_758_, v___x_759_);
if (v___x_760_ == 0)
{
lean_dec(v_nc_x3f_732_);
lean_dec(v_mc_x3f_731_);
return v___x_757_;
}
else
{
uint8_t v___x_761_; 
v___x_761_ = lean_nat_dec_le(v___x_759_, v___x_759_);
if (v___x_761_ == 0)
{
if (v___x_760_ == 0)
{
lean_dec(v_nc_x3f_732_);
lean_dec(v_mc_x3f_731_);
return v___x_757_;
}
else
{
size_t v___x_762_; size_t v___x_763_; lean_object* v___x_764_; 
v___x_762_ = ((size_t)0ULL);
v___x_763_ = lean_usize_of_nat(v___x_759_);
v___x_764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_731_, v_nc_x3f_732_, v_children_756_, v___x_762_, v___x_763_, v___x_757_);
return v___x_764_;
}
}
else
{
size_t v___x_765_; size_t v___x_766_; lean_object* v___x_767_; 
v___x_765_ = ((size_t)0ULL);
v___x_766_ = lean_usize_of_nat(v___x_759_);
v___x_767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_731_, v_nc_x3f_732_, v_children_756_, v___x_765_, v___x_766_, v___x_757_);
return v___x_767_;
}
}
}
case 1:
{
if (lean_obj_tag(v_mc_x3f_731_) == 1)
{
if (lean_obj_tag(v_nc_x3f_732_) == 1)
{
lean_object* v_a_768_; lean_object* v_val_769_; lean_object* v_val_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v_a_768_ = lean_ctor_get(v_msg_733_, 0);
v_val_769_ = lean_ctor_get(v_mc_x3f_731_, 0);
lean_inc(v_val_769_);
lean_dec_ref_known(v_mc_x3f_731_, 1);
v_val_770_ = lean_ctor_get(v_nc_x3f_732_, 0);
lean_inc(v_val_770_);
lean_dec_ref_known(v_nc_x3f_732_, 1);
lean_inc(v_a_768_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v_val_770_);
lean_ctor_set(v___x_771_, 1, v_a_768_);
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v_val_769_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = lean_array_push(v_acc_734_, v___x_772_);
return v___x_773_;
}
else
{
lean_dec_ref_known(v_mc_x3f_731_, 1);
lean_dec(v_nc_x3f_732_);
return v_acc_734_;
}
}
else
{
lean_dec(v_nc_x3f_732_);
lean_dec(v_mc_x3f_731_);
return v_acc_734_;
}
}
default: 
{
lean_dec(v_nc_x3f_732_);
lean_dec(v_mc_x3f_731_);
return v_acc_734_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(lean_object* v_mc_x3f_774_, lean_object* v_nc_x3f_775_, lean_object* v_as_776_, size_t v_i_777_, size_t v_stop_778_, lean_object* v_b_779_){
_start:
{
uint8_t v___x_780_; 
v___x_780_ = lean_usize_dec_eq(v_i_777_, v_stop_778_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; lean_object* v___x_782_; size_t v___x_783_; size_t v___x_784_; 
v___x_781_ = lean_array_uget_borrowed(v_as_776_, v_i_777_);
lean_inc(v_nc_x3f_775_);
lean_inc(v_mc_x3f_774_);
v___x_782_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_774_, v_nc_x3f_775_, v___x_781_, v_b_779_);
v___x_783_ = ((size_t)1ULL);
v___x_784_ = lean_usize_add(v_i_777_, v___x_783_);
v_i_777_ = v___x_784_;
v_b_779_ = v___x_782_;
goto _start;
}
else
{
lean_dec(v_nc_x3f_775_);
lean_dec(v_mc_x3f_774_);
return v_b_779_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0___boxed(lean_object* v_mc_x3f_786_, lean_object* v_nc_x3f_787_, lean_object* v_as_788_, lean_object* v_i_789_, lean_object* v_stop_790_, lean_object* v_b_791_){
_start:
{
size_t v_i_boxed_792_; size_t v_stop_boxed_793_; lean_object* v_res_794_; 
v_i_boxed_792_ = lean_unbox_usize(v_i_789_);
lean_dec(v_i_789_);
v_stop_boxed_793_ = lean_unbox_usize(v_stop_790_);
lean_dec(v_stop_790_);
v_res_794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_786_, v_nc_x3f_787_, v_as_788_, v_i_boxed_792_, v_stop_boxed_793_, v_b_791_);
lean_dec_ref(v_as_788_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go___boxed(lean_object* v_mc_x3f_795_, lean_object* v_nc_x3f_796_, lean_object* v_msg_797_, lean_object* v_acc_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_795_, v_nc_x3f_796_, v_msg_797_, v_acc_798_);
lean_dec_ref(v_msg_797_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(lean_object* v_msg_802_){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_803_ = lean_box(0);
v___x_804_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___closed__0));
v___x_805_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v___x_803_, v___x_803_, v_msg_802_, v___x_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___boxed(lean_object* v_msg_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_msg_806_);
lean_dec_ref(v_msg_806_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f(lean_object* v_range_810_, lean_object* v_stx_811_){
_start:
{
lean_object* v___x_812_; 
lean_inc(v_stx_811_);
v___x_812_ = l_Lean_Syntax_getKind(v_stx_811_);
if (lean_obj_tag(v___x_812_) == 1)
{
lean_object* v_pre_813_; 
v_pre_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_pre_813_);
if (lean_obj_tag(v_pre_813_) == 1)
{
lean_object* v_pre_814_; 
v_pre_814_ = lean_ctor_get(v_pre_813_, 0);
lean_inc(v_pre_814_);
if (lean_obj_tag(v_pre_814_) == 1)
{
lean_object* v_pre_815_; 
v_pre_815_ = lean_ctor_get(v_pre_814_, 0);
lean_inc(v_pre_815_);
if (lean_obj_tag(v_pre_815_) == 1)
{
lean_object* v_pre_816_; 
v_pre_816_ = lean_ctor_get(v_pre_815_, 0);
if (lean_obj_tag(v_pre_816_) == 0)
{
lean_object* v_str_817_; lean_object* v_str_818_; lean_object* v_str_819_; lean_object* v_str_820_; lean_object* v___x_821_; uint8_t v___x_822_; 
v_str_817_ = lean_ctor_get(v___x_812_, 1);
lean_inc_ref(v_str_817_);
lean_dec_ref_known(v___x_812_, 2);
v_str_818_ = lean_ctor_get(v_pre_813_, 1);
lean_inc_ref(v_str_818_);
lean_dec_ref_known(v_pre_813_, 2);
v_str_819_ = lean_ctor_get(v_pre_814_, 1);
lean_inc_ref(v_str_819_);
lean_dec_ref_known(v_pre_814_, 2);
v_str_820_ = lean_ctor_get(v_pre_815_, 1);
lean_inc_ref(v_str_820_);
lean_dec_ref_known(v_pre_815_, 2);
v___x_821_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_822_ = lean_string_dec_eq(v_str_820_, v___x_821_);
lean_dec_ref(v_str_820_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; 
lean_dec_ref(v_str_819_);
lean_dec_ref(v_str_818_);
lean_dec_ref(v_str_817_);
lean_dec(v_stx_811_);
lean_dec_ref(v_range_810_);
v___x_823_ = lean_box(0);
return v___x_823_;
}
else
{
lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_824_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0));
v___x_825_ = lean_string_dec_eq(v_str_819_, v___x_824_);
lean_dec_ref(v_str_819_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; 
lean_dec_ref(v_str_818_);
lean_dec_ref(v_str_817_);
lean_dec(v_stx_811_);
lean_dec_ref(v_range_810_);
v___x_826_ = lean_box(0);
return v___x_826_;
}
else
{
lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_827_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_828_ = lean_string_dec_eq(v_str_818_, v___x_827_);
lean_dec_ref(v_str_818_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; 
lean_dec_ref(v_str_817_);
lean_dec(v_stx_811_);
lean_dec_ref(v_range_810_);
v___x_829_ = lean_box(0);
return v___x_829_;
}
else
{
lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_830_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__0));
v___x_831_ = lean_string_dec_eq(v_str_817_, v___x_830_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_832_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__1));
v___x_833_ = lean_string_dec_eq(v_str_817_, v___x_832_);
lean_dec_ref(v_str_817_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; 
lean_dec(v_stx_811_);
lean_dec_ref(v_range_810_);
v___x_834_ = lean_box(0);
return v___x_834_;
}
else
{
lean_object* v___x_835_; lean_object* v_body_836_; lean_object* v___y_838_; lean_object* v___x_841_; 
v___x_835_ = lean_unsigned_to_nat(1u);
v_body_836_ = l_Lean_Syntax_getArg(v_stx_811_, v___x_835_);
v___x_841_ = l_Lean_Syntax_getTailPos_x3f(v_body_836_, v___x_831_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_842_ = lean_unsigned_to_nat(2u);
v___x_843_ = l_Lean_Syntax_getArg(v_stx_811_, v___x_842_);
lean_dec(v_stx_811_);
v___x_844_ = l_Lean_Syntax_getPos_x3f(v___x_843_, v___x_831_);
lean_dec(v___x_843_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_stop_845_; 
v_stop_845_ = lean_ctor_get(v_range_810_, 1);
lean_inc(v_stop_845_);
lean_dec_ref(v_range_810_);
v___y_838_ = v_stop_845_;
goto v___jp_837_;
}
else
{
lean_object* v_val_846_; 
lean_dec_ref(v_range_810_);
v_val_846_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_val_846_);
lean_dec_ref_known(v___x_844_, 1);
v___y_838_ = v_val_846_;
goto v___jp_837_;
}
}
else
{
lean_object* v_val_847_; 
lean_dec(v_stx_811_);
lean_dec_ref(v_range_810_);
v_val_847_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_val_847_);
lean_dec_ref_known(v___x_841_, 1);
v___y_838_ = v_val_847_;
goto v___jp_837_;
}
v___jp_837_:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_839_, 0, v_body_836_);
lean_ctor_set(v___x_839_, 1, v___y_838_);
v___x_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
return v___x_840_;
}
}
}
else
{
lean_object* v___x_848_; lean_object* v_body_849_; lean_object* v___y_851_; uint8_t v___x_854_; lean_object* v___x_855_; 
lean_dec_ref(v_str_817_);
v___x_848_ = lean_unsigned_to_nat(0u);
v_body_849_ = l_Lean_Syntax_getArg(v_stx_811_, v___x_848_);
lean_dec(v_stx_811_);
v___x_854_ = 0;
v___x_855_ = l_Lean_Syntax_getTailPos_x3f(v_body_849_, v___x_854_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_stop_856_; 
v_stop_856_ = lean_ctor_get(v_range_810_, 1);
lean_inc(v_stop_856_);
lean_dec_ref(v_range_810_);
v___y_851_ = v_stop_856_;
goto v___jp_850_;
}
else
{
lean_object* v_val_857_; 
lean_dec_ref(v_range_810_);
v_val_857_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_val_857_);
lean_dec_ref_known(v___x_855_, 1);
v___y_851_ = v_val_857_;
goto v___jp_850_;
}
v___jp_850_:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_852_, 0, v_body_849_);
lean_ctor_set(v___x_852_, 1, v___y_851_);
v___x_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
return v___x_853_;
}
}
}
}
}
}
else
{
lean_object* v___x_858_; 
lean_dec_ref_known(v_pre_815_, 2);
lean_dec_ref_known(v_pre_814_, 2);
lean_dec_ref_known(v_pre_813_, 2);
lean_dec_ref_known(v___x_812_, 2);
lean_dec(v_stx_811_);
lean_dec_ref(v_range_810_);
v___x_858_ = lean_box(0);
return v___x_858_;
}
}
else
{
lean_object* v___x_859_; 
lean_dec(v_pre_815_);
lean_dec_ref_known(v_pre_814_, 2);
lean_dec_ref_known(v_pre_813_, 2);
lean_dec_ref_known(v___x_812_, 2);
lean_dec(v_stx_811_);
lean_dec_ref(v_range_810_);
v___x_859_ = lean_box(0);
return v___x_859_;
}
}
else
{
lean_object* v___x_860_; 
lean_dec(v_pre_814_);
lean_dec_ref_known(v_pre_813_, 2);
lean_dec_ref_known(v___x_812_, 2);
lean_dec(v_stx_811_);
lean_dec_ref(v_range_810_);
v___x_860_ = lean_box(0);
return v___x_860_;
}
}
else
{
lean_object* v___x_861_; 
lean_dec(v_pre_813_);
lean_dec_ref_known(v___x_812_, 2);
lean_dec(v_stx_811_);
lean_dec_ref(v_range_810_);
v___x_861_ = lean_box(0);
return v___x_861_;
}
}
else
{
lean_object* v___x_862_; 
lean_dec(v___x_812_);
lean_dec(v_stx_811_);
lean_dec_ref(v_range_810_);
v___x_862_ = lean_box(0);
return v___x_862_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(lean_object* v_range_866_, lean_object* v_stx_867_){
_start:
{
lean_object* v___x_868_; 
lean_inc(v_stx_867_);
lean_inc_ref(v_range_866_);
v___x_868_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f(v_range_866_, v_stx_867_);
if (lean_obj_tag(v___x_868_) == 1)
{
lean_dec(v_stx_867_);
lean_dec_ref(v_range_866_);
return v___x_868_;
}
else
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; size_t v_sz_872_; size_t v___x_873_; lean_object* v___x_874_; lean_object* v_fst_875_; 
lean_dec(v___x_868_);
v___x_869_ = l_Lean_Syntax_getArgs(v_stx_867_);
lean_dec(v_stx_867_);
v___x_870_ = lean_box(0);
v___x_871_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v_sz_872_ = lean_array_size(v___x_869_);
v___x_873_ = ((size_t)0ULL);
v___x_874_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(v_range_866_, v___x_869_, v_sz_872_, v___x_873_, v___x_871_);
lean_dec_ref(v___x_869_);
v_fst_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_fst_875_);
lean_dec_ref(v___x_874_);
if (lean_obj_tag(v_fst_875_) == 0)
{
return v___x_870_;
}
else
{
lean_object* v_val_876_; 
v_val_876_ = lean_ctor_get(v_fst_875_, 0);
lean_inc(v_val_876_);
lean_dec_ref_known(v_fst_875_, 1);
return v_val_876_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(lean_object* v_range_877_, lean_object* v_as_878_, size_t v_sz_879_, size_t v_i_880_, lean_object* v_b_881_){
_start:
{
uint8_t v___x_882_; 
v___x_882_ = lean_usize_dec_lt(v_i_880_, v_sz_879_);
if (v___x_882_ == 0)
{
lean_dec_ref(v_range_877_);
lean_inc_ref(v_b_881_);
return v_b_881_;
}
else
{
lean_object* v___x_883_; lean_object* v_a_884_; lean_object* v___x_885_; 
v___x_883_ = lean_box(0);
v_a_884_ = lean_array_uget_borrowed(v_as_878_, v_i_880_);
lean_inc(v_a_884_);
lean_inc_ref(v_range_877_);
v___x_885_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(v_range_877_, v_a_884_);
if (lean_obj_tag(v___x_885_) == 1)
{
lean_object* v___x_886_; lean_object* v___x_887_; 
lean_dec_ref(v_range_877_);
v___x_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
v___x_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
lean_ctor_set(v___x_887_, 1, v___x_883_);
return v___x_887_;
}
else
{
lean_object* v___x_888_; size_t v___x_889_; size_t v___x_890_; 
lean_dec(v___x_885_);
v___x_888_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v___x_889_ = ((size_t)1ULL);
v___x_890_ = lean_usize_add(v_i_880_, v___x_889_);
v_i_880_ = v___x_890_;
v_b_881_ = v___x_888_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___boxed(lean_object* v_range_892_, lean_object* v_as_893_, lean_object* v_sz_894_, lean_object* v_i_895_, lean_object* v_b_896_){
_start:
{
size_t v_sz_boxed_897_; size_t v_i_boxed_898_; lean_object* v_res_899_; 
v_sz_boxed_897_ = lean_unbox_usize(v_sz_894_);
lean_dec(v_sz_894_);
v_i_boxed_898_ = lean_unbox_usize(v_i_895_);
lean_dec(v_i_895_);
v_res_899_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(v_range_892_, v_as_893_, v_sz_boxed_897_, v_i_boxed_898_, v_b_896_);
lean_dec_ref(v_b_896_);
lean_dec_ref(v_as_893_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(lean_object* v_range_900_, lean_object* v_stx_901_){
_start:
{
uint8_t v___x_902_; lean_object* v___x_903_; 
v___x_902_ = 0;
v___x_903_ = l_Lean_Syntax_getRange_x3f(v_stx_901_, v___x_902_);
if (lean_obj_tag(v___x_903_) == 1)
{
lean_object* v_val_904_; uint8_t v___x_905_; 
v_val_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_val_904_);
lean_dec_ref_known(v___x_903_, 1);
v___x_905_ = l_Lean_Syntax_Range_includes(v_val_904_, v_range_900_, v___x_902_, v___x_902_);
lean_dec(v_val_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; 
lean_dec(v_stx_901_);
lean_dec_ref(v_range_900_);
v___x_906_ = lean_box(0);
return v___x_906_;
}
else
{
lean_object* v___x_907_; lean_object* v___x_908_; size_t v_sz_909_; size_t v___x_910_; lean_object* v___x_911_; lean_object* v_fst_912_; 
v___x_907_ = l_Lean_Syntax_getArgs(v_stx_901_);
v___x_908_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v_sz_909_ = lean_array_size(v___x_907_);
v___x_910_ = ((size_t)0ULL);
lean_inc_ref(v_range_900_);
v___x_911_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(v_range_900_, v___x_907_, v_sz_909_, v___x_910_, v___x_908_);
lean_dec_ref(v___x_907_);
v_fst_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_fst_912_);
lean_dec_ref(v___x_911_);
if (lean_obj_tag(v_fst_912_) == 0)
{
lean_object* v___x_913_; 
v___x_913_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(v_range_900_, v_stx_901_);
return v___x_913_;
}
else
{
lean_object* v_val_914_; 
lean_dec(v_stx_901_);
lean_dec_ref(v_range_900_);
v_val_914_ = lean_ctor_get(v_fst_912_, 0);
lean_inc(v_val_914_);
lean_dec_ref_known(v_fst_912_, 1);
return v_val_914_;
}
}
}
else
{
lean_object* v___x_915_; 
lean_dec(v___x_903_);
lean_dec(v_stx_901_);
lean_dec_ref(v_range_900_);
v___x_915_ = lean_box(0);
return v___x_915_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(lean_object* v_range_916_, lean_object* v_as_917_, size_t v_sz_918_, size_t v_i_919_, lean_object* v_b_920_){
_start:
{
uint8_t v___x_921_; 
v___x_921_ = lean_usize_dec_lt(v_i_919_, v_sz_918_);
if (v___x_921_ == 0)
{
lean_dec_ref(v_range_916_);
lean_inc_ref(v_b_920_);
return v_b_920_;
}
else
{
lean_object* v___x_922_; lean_object* v_a_923_; lean_object* v___x_924_; 
v___x_922_ = lean_box(0);
v_a_923_ = lean_array_uget_borrowed(v_as_917_, v_i_919_);
lean_inc(v_a_923_);
lean_inc_ref(v_range_916_);
v___x_924_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v_range_916_, v_a_923_);
if (lean_obj_tag(v___x_924_) == 1)
{
lean_object* v___x_925_; lean_object* v___x_926_; 
lean_dec_ref(v_range_916_);
v___x_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
lean_ctor_set(v___x_926_, 1, v___x_922_);
return v___x_926_;
}
else
{
lean_object* v___x_927_; size_t v___x_928_; size_t v___x_929_; 
lean_dec(v___x_924_);
v___x_927_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v___x_928_ = ((size_t)1ULL);
v___x_929_ = lean_usize_add(v_i_919_, v___x_928_);
v_i_919_ = v___x_929_;
v_b_920_ = v___x_927_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0___boxed(lean_object* v_range_931_, lean_object* v_as_932_, lean_object* v_sz_933_, lean_object* v_i_934_, lean_object* v_b_935_){
_start:
{
size_t v_sz_boxed_936_; size_t v_i_boxed_937_; lean_object* v_res_938_; 
v_sz_boxed_936_ = lean_unbox_usize(v_sz_933_);
lean_dec(v_sz_933_);
v_i_boxed_937_ = lean_unbox_usize(v_i_934_);
lean_dec(v_i_934_);
v_res_938_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(v_range_931_, v_as_932_, v_sz_boxed_936_, v_i_boxed_937_, v_b_935_);
lean_dec_ref(v_b_935_);
lean_dec_ref(v_as_932_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody(lean_object* v_cmd_939_, lean_object* v_range_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v_range_940_, v_cmd_939_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0(lean_object* v_ctx_942_, lean_object* v_info_943_, lean_object* v_acc_944_){
_start:
{
if (lean_obj_tag(v_info_943_) == 0)
{
lean_object* v_i_945_; lean_object* v_toElabInfo_946_; lean_object* v_mctxBefore_947_; lean_object* v_goalsBefore_948_; lean_object* v_stx_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_967_; 
v_i_945_ = lean_ctor_get(v_info_943_, 0);
lean_inc_ref(v_i_945_);
lean_dec_ref_known(v_info_943_, 1);
v_toElabInfo_946_ = lean_ctor_get(v_i_945_, 0);
lean_inc_ref(v_toElabInfo_946_);
v_mctxBefore_947_ = lean_ctor_get(v_i_945_, 1);
lean_inc_ref(v_mctxBefore_947_);
v_goalsBefore_948_ = lean_ctor_get(v_i_945_, 2);
lean_inc(v_goalsBefore_948_);
lean_dec_ref(v_i_945_);
v_stx_949_ = lean_ctor_get(v_toElabInfo_946_, 1);
v_isSharedCheck_967_ = !lean_is_exclusive(v_toElabInfo_946_);
if (v_isSharedCheck_967_ == 0)
{
lean_object* v_unused_968_; 
v_unused_968_ = lean_ctor_get(v_toElabInfo_946_, 0);
lean_dec(v_unused_968_);
v___x_951_ = v_toElabInfo_946_;
v_isShared_952_ = v_isSharedCheck_967_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_stx_949_);
lean_dec(v_toElabInfo_946_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_967_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
uint8_t v___x_953_; 
lean_inc(v_stx_949_);
v___x_953_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(v_stx_949_);
if (v___x_953_ == 0)
{
lean_del_object(v___x_951_);
lean_dec(v_stx_949_);
lean_dec(v_goalsBefore_948_);
lean_dec_ref(v_mctxBefore_947_);
return v_acc_944_;
}
else
{
lean_object* v___x_954_; 
v___x_954_ = l_List_head_x3f___redArg(v_goalsBefore_948_);
lean_dec(v_goalsBefore_948_);
if (lean_obj_tag(v___x_954_) == 1)
{
lean_object* v_toCommandContextInfo_955_; lean_object* v_val_956_; lean_object* v_env_957_; lean_object* v_options_958_; lean_object* v_currNamespace_959_; lean_object* v_openDecls_960_; lean_object* v_namingCtx_962_; 
v_toCommandContextInfo_955_ = lean_ctor_get(v_ctx_942_, 0);
v_val_956_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_val_956_);
lean_dec_ref_known(v___x_954_, 1);
v_env_957_ = lean_ctor_get(v_toCommandContextInfo_955_, 0);
v_options_958_ = lean_ctor_get(v_toCommandContextInfo_955_, 4);
v_currNamespace_959_ = lean_ctor_get(v_toCommandContextInfo_955_, 5);
v_openDecls_960_ = lean_ctor_get(v_toCommandContextInfo_955_, 6);
lean_inc(v_openDecls_960_);
lean_inc(v_currNamespace_959_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 1, v_openDecls_960_);
lean_ctor_set(v___x_951_, 0, v_currNamespace_959_);
v_namingCtx_962_ = v___x_951_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_currNamespace_959_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_openDecls_960_);
v_namingCtx_962_ = v_reuseFailAlloc_966_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_963_ = lean_box(1);
lean_inc_ref(v_options_958_);
lean_inc_ref(v_env_957_);
v___x_964_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v_stx_949_);
lean_ctor_set(v___x_964_, 2, v_env_957_);
lean_ctor_set(v___x_964_, 3, v_mctxBefore_947_);
lean_ctor_set(v___x_964_, 4, v_options_958_);
lean_ctor_set(v___x_964_, 5, v_namingCtx_962_);
lean_ctor_set(v___x_964_, 6, v_val_956_);
v___x_965_ = lean_array_push(v_acc_944_, v___x_964_);
return v___x_965_;
}
}
else
{
lean_dec(v___x_954_);
lean_del_object(v___x_951_);
lean_dec(v_stx_949_);
lean_dec_ref(v_mctxBefore_947_);
return v_acc_944_;
}
}
}
}
else
{
lean_dec_ref(v_info_943_);
return v_acc_944_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0___boxed(lean_object* v_ctx_969_, lean_object* v_info_970_, lean_object* v_acc_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0(v_ctx_969_, v_info_970_, v_acc_971_);
lean_dec_ref(v_ctx_969_);
return v_res_972_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_973_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__0);
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
return v___x_975_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_976_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1);
v___x_977_ = lean_unsigned_to_nat(0u);
v___x_978_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
lean_ctor_set(v___x_978_, 2, v___x_977_);
lean_ctor_set(v___x_978_, 3, v___x_977_);
lean_ctor_set(v___x_978_, 4, v___x_976_);
lean_ctor_set(v___x_978_, 5, v___x_976_);
lean_ctor_set(v___x_978_, 6, v___x_976_);
lean_ctor_set(v___x_978_, 7, v___x_976_);
lean_ctor_set(v___x_978_, 8, v___x_976_);
lean_ctor_set(v___x_978_, 9, v___x_976_);
lean_ctor_set(v___x_978_, 10, v___x_976_);
return v___x_978_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_979_ = lean_unsigned_to_nat(32u);
v___x_980_ = lean_mk_empty_array_with_capacity(v___x_979_);
v___x_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
return v___x_981_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_982_ = ((size_t)5ULL);
v___x_983_ = lean_unsigned_to_nat(0u);
v___x_984_ = lean_unsigned_to_nat(32u);
v___x_985_ = lean_mk_empty_array_with_capacity(v___x_984_);
v___x_986_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__3);
v___x_987_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_987_, 0, v___x_986_);
lean_ctor_set(v___x_987_, 1, v___x_985_);
lean_ctor_set(v___x_987_, 2, v___x_983_);
lean_ctor_set(v___x_987_, 3, v___x_983_);
lean_ctor_set_usize(v___x_987_, 4, v___x_982_);
return v___x_987_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_988_ = lean_box(1);
v___x_989_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__4);
v___x_990_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1);
v___x_991_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
lean_ctor_set(v___x_991_, 1, v___x_989_);
lean_ctor_set(v___x_991_, 2, v___x_988_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(lean_object* v_msgData_992_, lean_object* v___y_993_){
_start:
{
lean_object* v___x_995_; lean_object* v_env_996_; lean_object* v___x_997_; lean_object* v_scopes_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v_opts_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_995_ = lean_st_ref_get(v___y_993_);
v_env_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc_ref(v_env_996_);
lean_dec(v___x_995_);
v___x_997_ = lean_st_ref_get(v___y_993_);
v_scopes_998_ = lean_ctor_get(v___x_997_, 2);
lean_inc(v_scopes_998_);
lean_dec(v___x_997_);
v___x_999_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1000_ = l_List_head_x21___redArg(v___x_999_, v_scopes_998_);
lean_dec(v_scopes_998_);
v_opts_1001_ = lean_ctor_get(v___x_1000_, 1);
lean_inc_ref(v_opts_1001_);
lean_dec(v___x_1000_);
v___x_1002_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__2);
v___x_1003_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__5);
v___x_1004_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1004_, 0, v_env_996_);
lean_ctor_set(v___x_1004_, 1, v___x_1002_);
lean_ctor_set(v___x_1004_, 2, v___x_1003_);
lean_ctor_set(v___x_1004_, 3, v_opts_1001_);
v___x_1005_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set(v___x_1005_, 1, v_msgData_992_);
v___x_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___boxed(lean_object* v_msgData_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(v_msgData_1007_, v___y_1008_);
lean_dec(v___y_1008_);
return v_res_1010_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1011_; double v___x_1012_; 
v___x_1011_ = lean_unsigned_to_nat(0u);
v___x_1012_ = lean_float_of_nat(v___x_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(lean_object* v_cls_1015_, lean_object* v_msg_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Lean_Elab_Command_getRef___redArg(v___y_1017_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1022_; lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1071_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref_known(v___x_1020_, 1);
v___x_1022_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(v_msg_1016_, v___y_1018_);
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1071_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1071_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1027_; lean_object* v_traceState_1028_; lean_object* v_env_1029_; lean_object* v_messages_1030_; lean_object* v_scopes_1031_; lean_object* v_usedQuotCtxts_1032_; lean_object* v_nextMacroScope_1033_; lean_object* v_maxRecDepth_1034_; lean_object* v_ngen_1035_; lean_object* v_auxDeclNGen_1036_; lean_object* v_infoState_1037_; lean_object* v_snapshotTasks_1038_; lean_object* v_prevLinterStates_1039_; lean_object* v_codeQualityEntryTasks_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1070_; 
v___x_1027_ = lean_st_ref_take(v___y_1018_);
v_traceState_1028_ = lean_ctor_get(v___x_1027_, 9);
v_env_1029_ = lean_ctor_get(v___x_1027_, 0);
v_messages_1030_ = lean_ctor_get(v___x_1027_, 1);
v_scopes_1031_ = lean_ctor_get(v___x_1027_, 2);
v_usedQuotCtxts_1032_ = lean_ctor_get(v___x_1027_, 3);
v_nextMacroScope_1033_ = lean_ctor_get(v___x_1027_, 4);
v_maxRecDepth_1034_ = lean_ctor_get(v___x_1027_, 5);
v_ngen_1035_ = lean_ctor_get(v___x_1027_, 6);
v_auxDeclNGen_1036_ = lean_ctor_get(v___x_1027_, 7);
v_infoState_1037_ = lean_ctor_get(v___x_1027_, 8);
v_snapshotTasks_1038_ = lean_ctor_get(v___x_1027_, 10);
v_prevLinterStates_1039_ = lean_ctor_get(v___x_1027_, 11);
v_codeQualityEntryTasks_1040_ = lean_ctor_get(v___x_1027_, 12);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1042_ = v___x_1027_;
v_isShared_1043_ = v_isSharedCheck_1070_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1040_);
lean_inc(v_prevLinterStates_1039_);
lean_inc(v_snapshotTasks_1038_);
lean_inc(v_traceState_1028_);
lean_inc(v_infoState_1037_);
lean_inc(v_auxDeclNGen_1036_);
lean_inc(v_ngen_1035_);
lean_inc(v_maxRecDepth_1034_);
lean_inc(v_nextMacroScope_1033_);
lean_inc(v_usedQuotCtxts_1032_);
lean_inc(v_scopes_1031_);
lean_inc(v_messages_1030_);
lean_inc(v_env_1029_);
lean_dec(v___x_1027_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1070_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
uint64_t v_tid_1044_; lean_object* v_traces_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1069_; 
v_tid_1044_ = lean_ctor_get_uint64(v_traceState_1028_, sizeof(void*)*1);
v_traces_1045_ = lean_ctor_get(v_traceState_1028_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_traceState_1028_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1047_ = v_traceState_1028_;
v_isShared_1048_ = v_isSharedCheck_1069_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_traces_1045_);
lean_dec(v_traceState_1028_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1069_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; double v___x_1050_; uint8_t v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1049_ = lean_box(0);
v___x_1050_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0);
v___x_1051_ = 0;
v___x_1052_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_1053_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1053_, 0, v_cls_1015_);
lean_ctor_set(v___x_1053_, 1, v___x_1049_);
lean_ctor_set(v___x_1053_, 2, v___x_1052_);
lean_ctor_set_float(v___x_1053_, sizeof(void*)*3, v___x_1050_);
lean_ctor_set_float(v___x_1053_, sizeof(void*)*3 + 8, v___x_1050_);
lean_ctor_set_uint8(v___x_1053_, sizeof(void*)*3 + 16, v___x_1051_);
v___x_1054_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__1));
v___x_1055_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1053_);
lean_ctor_set(v___x_1055_, 1, v_a_1023_);
lean_ctor_set(v___x_1055_, 2, v___x_1054_);
v___x_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1056_, 0, v_a_1021_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = l_Lean_PersistentArray_push___redArg(v_traces_1045_, v___x_1056_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 0, v___x_1057_);
v___x_1059_ = v___x_1047_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1057_);
lean_ctor_set_uint64(v_reuseFailAlloc_1068_, sizeof(void*)*1, v_tid_1044_);
v___x_1059_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1061_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 9, v___x_1059_);
v___x_1061_ = v___x_1042_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_env_1029_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_messages_1030_);
lean_ctor_set(v_reuseFailAlloc_1067_, 2, v_scopes_1031_);
lean_ctor_set(v_reuseFailAlloc_1067_, 3, v_usedQuotCtxts_1032_);
lean_ctor_set(v_reuseFailAlloc_1067_, 4, v_nextMacroScope_1033_);
lean_ctor_set(v_reuseFailAlloc_1067_, 5, v_maxRecDepth_1034_);
lean_ctor_set(v_reuseFailAlloc_1067_, 6, v_ngen_1035_);
lean_ctor_set(v_reuseFailAlloc_1067_, 7, v_auxDeclNGen_1036_);
lean_ctor_set(v_reuseFailAlloc_1067_, 8, v_infoState_1037_);
lean_ctor_set(v_reuseFailAlloc_1067_, 9, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1067_, 10, v_snapshotTasks_1038_);
lean_ctor_set(v_reuseFailAlloc_1067_, 11, v_prevLinterStates_1039_);
lean_ctor_set(v_reuseFailAlloc_1067_, 12, v_codeQualityEntryTasks_1040_);
v___x_1061_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1065_; 
v___x_1062_ = lean_st_ref_put(v___y_1018_, v___x_1061_);
v___x_1063_ = lean_box(0);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1063_);
v___x_1065_ = v___x_1025_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1063_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
lean_dec_ref(v_msg_1016_);
lean_dec(v_cls_1015_);
v_a_1072_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1020_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1020_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___boxed(lean_object* v_cls_1080_, lean_object* v_msg_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v_cls_1080_, v_msg_1081_, v___y_1082_, v___y_1083_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
return v_res_1085_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0(lean_object* v_x_1090_){
_start:
{
lean_object* v___x_1091_; uint8_t v___x_1092_; 
v___x_1091_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0___closed__1));
v___x_1092_ = lean_name_eq(v_x_1090_, v___x_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0___boxed(lean_object* v_x_1093_){
_start:
{
uint8_t v_res_1094_; lean_object* v_r_1095_; 
v_res_1094_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0(v_x_1093_);
lean_dec(v_x_1093_);
v_r_1095_ = lean_box(v_res_1094_);
return v_r_1095_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(lean_object* v_a_1096_, lean_object* v_x_1097_){
_start:
{
if (lean_obj_tag(v_x_1097_) == 0)
{
uint8_t v___x_1098_; 
v___x_1098_ = 0;
return v___x_1098_;
}
else
{
lean_object* v_key_1099_; lean_object* v_tail_1100_; uint8_t v___y_1102_; lean_object* v_fst_1104_; lean_object* v_snd_1105_; lean_object* v_fst_1106_; lean_object* v_snd_1107_; uint8_t v___x_1108_; 
v_key_1099_ = lean_ctor_get(v_x_1097_, 0);
v_tail_1100_ = lean_ctor_get(v_x_1097_, 2);
v_fst_1104_ = lean_ctor_get(v_key_1099_, 0);
v_snd_1105_ = lean_ctor_get(v_key_1099_, 1);
v_fst_1106_ = lean_ctor_get(v_a_1096_, 0);
v_snd_1107_ = lean_ctor_get(v_a_1096_, 1);
v___x_1108_ = l_Lean_Syntax_instBEqRange_beq(v_fst_1104_, v_fst_1106_);
if (v___x_1108_ == 0)
{
v___y_1102_ = v___x_1108_;
goto v___jp_1101_;
}
else
{
uint8_t v___x_1109_; 
v___x_1109_ = l_Lean_instBEqMVarId_beq(v_snd_1105_, v_snd_1107_);
v___y_1102_ = v___x_1109_;
goto v___jp_1101_;
}
v___jp_1101_:
{
if (v___y_1102_ == 0)
{
v_x_1097_ = v_tail_1100_;
goto _start;
}
else
{
return v___y_1102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg___boxed(lean_object* v_a_1110_, lean_object* v_x_1111_){
_start:
{
uint8_t v_res_1112_; lean_object* v_r_1113_; 
v_res_1112_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(v_a_1110_, v_x_1111_);
lean_dec(v_x_1111_);
lean_dec_ref(v_a_1110_);
v_r_1113_ = lean_box(v_res_1112_);
return v_r_1113_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(lean_object* v_m_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v_buckets_1116_; lean_object* v_fst_1117_; lean_object* v_snd_1118_; lean_object* v___x_1119_; uint64_t v___x_1120_; uint64_t v___x_1121_; uint64_t v___x_1122_; uint64_t v___x_1123_; uint64_t v___x_1124_; uint64_t v_fold_1125_; uint64_t v___x_1126_; uint64_t v___x_1127_; uint64_t v___x_1128_; size_t v___x_1129_; size_t v___x_1130_; size_t v___x_1131_; size_t v___x_1132_; size_t v___x_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
v_buckets_1116_ = lean_ctor_get(v_m_1114_, 1);
v_fst_1117_ = lean_ctor_get(v_a_1115_, 0);
v_snd_1118_ = lean_ctor_get(v_a_1115_, 1);
v___x_1119_ = lean_array_get_size(v_buckets_1116_);
v___x_1120_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1117_);
v___x_1121_ = l_Lean_instHashableMVarId_hash(v_snd_1118_);
v___x_1122_ = lean_uint64_mix_hash(v___x_1120_, v___x_1121_);
v___x_1123_ = 32ULL;
v___x_1124_ = lean_uint64_shift_right(v___x_1122_, v___x_1123_);
v_fold_1125_ = lean_uint64_xor(v___x_1122_, v___x_1124_);
v___x_1126_ = 16ULL;
v___x_1127_ = lean_uint64_shift_right(v_fold_1125_, v___x_1126_);
v___x_1128_ = lean_uint64_xor(v_fold_1125_, v___x_1127_);
v___x_1129_ = lean_uint64_to_usize(v___x_1128_);
v___x_1130_ = lean_usize_of_nat(v___x_1119_);
v___x_1131_ = ((size_t)1ULL);
v___x_1132_ = lean_usize_sub(v___x_1130_, v___x_1131_);
v___x_1133_ = lean_usize_land(v___x_1129_, v___x_1132_);
v___x_1134_ = lean_array_uget_borrowed(v_buckets_1116_, v___x_1133_);
v___x_1135_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(v_a_1115_, v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg___boxed(lean_object* v_m_1136_, lean_object* v_a_1137_){
_start:
{
uint8_t v_res_1138_; lean_object* v_r_1139_; 
v_res_1138_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(v_m_1136_, v_a_1137_);
lean_dec_ref(v_a_1137_);
lean_dec_ref(v_m_1136_);
v_r_1139_ = lean_box(v_res_1138_);
return v_r_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3_spec__8___redArg(lean_object* v_x_1140_, lean_object* v_x_1141_){
_start:
{
if (lean_obj_tag(v_x_1141_) == 0)
{
return v_x_1140_;
}
else
{
lean_object* v_key_1142_; lean_object* v_value_1143_; lean_object* v_tail_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1171_; 
v_key_1142_ = lean_ctor_get(v_x_1141_, 0);
v_value_1143_ = lean_ctor_get(v_x_1141_, 1);
v_tail_1144_ = lean_ctor_get(v_x_1141_, 2);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_x_1141_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1146_ = v_x_1141_;
v_isShared_1147_ = v_isSharedCheck_1171_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_tail_1144_);
lean_inc(v_value_1143_);
lean_inc(v_key_1142_);
lean_dec(v_x_1141_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1171_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v_fst_1148_; lean_object* v_snd_1149_; lean_object* v___x_1150_; uint64_t v___x_1151_; uint64_t v___x_1152_; uint64_t v___x_1153_; uint64_t v___x_1154_; uint64_t v___x_1155_; uint64_t v_fold_1156_; uint64_t v___x_1157_; uint64_t v___x_1158_; uint64_t v___x_1159_; size_t v___x_1160_; size_t v___x_1161_; size_t v___x_1162_; size_t v___x_1163_; size_t v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1167_; 
v_fst_1148_ = lean_ctor_get(v_key_1142_, 0);
v_snd_1149_ = lean_ctor_get(v_key_1142_, 1);
v___x_1150_ = lean_array_get_size(v_x_1140_);
v___x_1151_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1148_);
v___x_1152_ = l_Lean_instHashableMVarId_hash(v_snd_1149_);
v___x_1153_ = lean_uint64_mix_hash(v___x_1151_, v___x_1152_);
v___x_1154_ = 32ULL;
v___x_1155_ = lean_uint64_shift_right(v___x_1153_, v___x_1154_);
v_fold_1156_ = lean_uint64_xor(v___x_1153_, v___x_1155_);
v___x_1157_ = 16ULL;
v___x_1158_ = lean_uint64_shift_right(v_fold_1156_, v___x_1157_);
v___x_1159_ = lean_uint64_xor(v_fold_1156_, v___x_1158_);
v___x_1160_ = lean_uint64_to_usize(v___x_1159_);
v___x_1161_ = lean_usize_of_nat(v___x_1150_);
v___x_1162_ = ((size_t)1ULL);
v___x_1163_ = lean_usize_sub(v___x_1161_, v___x_1162_);
v___x_1164_ = lean_usize_land(v___x_1160_, v___x_1163_);
v___x_1165_ = lean_array_uget_borrowed(v_x_1140_, v___x_1164_);
lean_inc(v___x_1165_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 2, v___x_1165_);
v___x_1167_ = v___x_1146_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_key_1142_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_value_1143_);
lean_ctor_set(v_reuseFailAlloc_1170_, 2, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_array_uset(v_x_1140_, v___x_1164_, v___x_1167_);
v_x_1140_ = v___x_1168_;
v_x_1141_ = v_tail_1144_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3___redArg(lean_object* v_i_1172_, lean_object* v_source_1173_, lean_object* v_target_1174_){
_start:
{
lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = lean_array_get_size(v_source_1173_);
v___x_1176_ = lean_nat_dec_lt(v_i_1172_, v___x_1175_);
if (v___x_1176_ == 0)
{
lean_dec_ref(v_source_1173_);
lean_dec(v_i_1172_);
return v_target_1174_;
}
else
{
lean_object* v_es_1177_; lean_object* v___x_1178_; lean_object* v_source_1179_; lean_object* v_target_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v_es_1177_ = lean_array_fget(v_source_1173_, v_i_1172_);
v___x_1178_ = lean_box(0);
v_source_1179_ = lean_array_fset(v_source_1173_, v_i_1172_, v___x_1178_);
v_target_1180_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3_spec__8___redArg(v_target_1174_, v_es_1177_);
v___x_1181_ = lean_unsigned_to_nat(1u);
v___x_1182_ = lean_nat_add(v_i_1172_, v___x_1181_);
lean_dec(v_i_1172_);
v_i_1172_ = v___x_1182_;
v_source_1173_ = v_source_1179_;
v_target_1174_ = v_target_1180_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2___redArg(lean_object* v_data_1184_){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v_nbuckets_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1185_ = lean_array_get_size(v_data_1184_);
v___x_1186_ = lean_unsigned_to_nat(2u);
v_nbuckets_1187_ = lean_nat_mul(v___x_1185_, v___x_1186_);
v___x_1188_ = lean_unsigned_to_nat(0u);
v___x_1189_ = lean_box(0);
v___x_1190_ = lean_mk_array(v_nbuckets_1187_, v___x_1189_);
v___x_1191_ = lean_array_propagate_mark(v_data_1184_, v___x_1190_);
v___x_1192_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3___redArg(v___x_1188_, v_data_1184_, v___x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(lean_object* v_m_1193_, lean_object* v_a_1194_, lean_object* v_b_1195_){
_start:
{
lean_object* v_size_1196_; lean_object* v_buckets_1197_; lean_object* v_fst_1198_; lean_object* v_snd_1199_; lean_object* v___x_1200_; uint64_t v___x_1201_; uint64_t v___x_1202_; uint64_t v___x_1203_; uint64_t v___x_1204_; uint64_t v___x_1205_; uint64_t v_fold_1206_; uint64_t v___x_1207_; uint64_t v___x_1208_; uint64_t v___x_1209_; size_t v___x_1210_; size_t v___x_1211_; size_t v___x_1212_; size_t v___x_1213_; size_t v___x_1214_; lean_object* v_bkt_1215_; uint8_t v___x_1216_; 
v_size_1196_ = lean_ctor_get(v_m_1193_, 0);
v_buckets_1197_ = lean_ctor_get(v_m_1193_, 1);
v_fst_1198_ = lean_ctor_get(v_a_1194_, 0);
v_snd_1199_ = lean_ctor_get(v_a_1194_, 1);
v___x_1200_ = lean_array_get_size(v_buckets_1197_);
v___x_1201_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1198_);
v___x_1202_ = l_Lean_instHashableMVarId_hash(v_snd_1199_);
v___x_1203_ = lean_uint64_mix_hash(v___x_1201_, v___x_1202_);
v___x_1204_ = 32ULL;
v___x_1205_ = lean_uint64_shift_right(v___x_1203_, v___x_1204_);
v_fold_1206_ = lean_uint64_xor(v___x_1203_, v___x_1205_);
v___x_1207_ = 16ULL;
v___x_1208_ = lean_uint64_shift_right(v_fold_1206_, v___x_1207_);
v___x_1209_ = lean_uint64_xor(v_fold_1206_, v___x_1208_);
v___x_1210_ = lean_uint64_to_usize(v___x_1209_);
v___x_1211_ = lean_usize_of_nat(v___x_1200_);
v___x_1212_ = ((size_t)1ULL);
v___x_1213_ = lean_usize_sub(v___x_1211_, v___x_1212_);
v___x_1214_ = lean_usize_land(v___x_1210_, v___x_1213_);
v_bkt_1215_ = lean_array_uget_borrowed(v_buckets_1197_, v___x_1214_);
v___x_1216_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(v_a_1194_, v_bkt_1215_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1237_; 
lean_inc_ref(v_buckets_1197_);
lean_inc(v_size_1196_);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_m_1193_);
if (v_isSharedCheck_1237_ == 0)
{
lean_object* v_unused_1238_; lean_object* v_unused_1239_; 
v_unused_1238_ = lean_ctor_get(v_m_1193_, 1);
lean_dec(v_unused_1238_);
v_unused_1239_ = lean_ctor_get(v_m_1193_, 0);
lean_dec(v_unused_1239_);
v___x_1218_ = v_m_1193_;
v_isShared_1219_ = v_isSharedCheck_1237_;
goto v_resetjp_1217_;
}
else
{
lean_dec(v_m_1193_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1237_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1220_; lean_object* v_size_x27_1221_; lean_object* v___x_1222_; lean_object* v_buckets_x27_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1220_ = lean_unsigned_to_nat(1u);
v_size_x27_1221_ = lean_nat_add(v_size_1196_, v___x_1220_);
lean_dec(v_size_1196_);
lean_inc(v_bkt_1215_);
v___x_1222_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1222_, 0, v_a_1194_);
lean_ctor_set(v___x_1222_, 1, v_b_1195_);
lean_ctor_set(v___x_1222_, 2, v_bkt_1215_);
v_buckets_x27_1223_ = lean_array_uset(v_buckets_1197_, v___x_1214_, v___x_1222_);
v___x_1224_ = lean_unsigned_to_nat(4u);
v___x_1225_ = lean_nat_mul(v_size_x27_1221_, v___x_1224_);
v___x_1226_ = lean_unsigned_to_nat(3u);
v___x_1227_ = lean_nat_div(v___x_1225_, v___x_1226_);
lean_dec(v___x_1225_);
v___x_1228_ = lean_array_get_size(v_buckets_x27_1223_);
v___x_1229_ = lean_nat_dec_le(v___x_1227_, v___x_1228_);
lean_dec(v___x_1227_);
if (v___x_1229_ == 0)
{
lean_object* v_val_1230_; lean_object* v___x_1232_; 
v_val_1230_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2___redArg(v_buckets_x27_1223_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 1, v_val_1230_);
lean_ctor_set(v___x_1218_, 0, v_size_x27_1221_);
v___x_1232_ = v___x_1218_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_size_x27_1221_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_val_1230_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
else
{
lean_object* v___x_1235_; 
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 1, v_buckets_x27_1223_);
lean_ctor_set(v___x_1218_, 0, v_size_x27_1221_);
v___x_1235_ = v___x_1218_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_size_x27_1221_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v_buckets_x27_1223_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
else
{
lean_dec(v_b_1195_);
lean_dec_ref(v_a_1194_);
return v_m_1193_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(lean_object* v___x_1240_, lean_object* v_fst_1241_, lean_object* v_snd_1242_, lean_object* v___x_1243_, lean_object* v_as_1244_, size_t v_sz_1245_, size_t v_i_1246_, lean_object* v_b_1247_){
_start:
{
lean_object* v_a_1250_; uint8_t v___x_1254_; 
v___x_1254_ = lean_usize_dec_lt(v_i_1246_, v_sz_1245_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; 
lean_dec(v___x_1243_);
lean_dec(v_snd_1242_);
lean_dec(v_fst_1241_);
lean_dec_ref(v___x_1240_);
v___x_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1255_, 0, v_b_1247_);
return v___x_1255_;
}
else
{
lean_object* v_a_1256_; lean_object* v_snd_1257_; lean_object* v_fst_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1294_; 
v_a_1256_ = lean_array_uget(v_as_1244_, v_i_1246_);
v_snd_1257_ = lean_ctor_get(v_a_1256_, 1);
v_fst_1258_ = lean_ctor_get(v_a_1256_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_a_1256_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1260_ = v_a_1256_;
v_isShared_1261_ = v_isSharedCheck_1294_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_snd_1257_);
lean_inc(v_fst_1258_);
lean_dec(v_a_1256_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1294_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v_fst_1262_; lean_object* v_snd_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1293_; 
v_fst_1262_ = lean_ctor_get(v_snd_1257_, 0);
v_snd_1263_ = lean_ctor_get(v_snd_1257_, 1);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_snd_1257_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1265_ = v_snd_1257_;
v_isShared_1266_ = v_isSharedCheck_1293_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_snd_1263_);
lean_inc(v_fst_1262_);
lean_dec(v_snd_1257_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1293_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v_fst_1267_; lean_object* v_snd_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1292_; 
v_fst_1267_ = lean_ctor_get(v_b_1247_, 0);
v_snd_1268_ = lean_ctor_get(v_b_1247_, 1);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_b_1247_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1270_ = v_b_1247_;
v_isShared_1271_ = v_isSharedCheck_1292_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_snd_1268_);
lean_inc(v_fst_1267_);
lean_dec(v_b_1247_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1292_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
lean_inc(v_snd_1263_);
lean_inc_ref(v___x_1240_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 1, v_snd_1263_);
lean_ctor_set(v___x_1270_, 0, v___x_1240_);
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1240_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_snd_1263_);
v___x_1273_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
uint8_t v___x_1274_; 
v___x_1274_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(v_snd_1268_, v___x_1273_);
if (v___x_1274_ == 0)
{
lean_object* v_env_1275_; lean_object* v_mctx_1276_; lean_object* v_opts_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1281_; 
v_env_1275_ = lean_ctor_get(v_fst_1258_, 0);
lean_inc_ref(v_env_1275_);
v_mctx_1276_ = lean_ctor_get(v_fst_1258_, 1);
lean_inc_ref(v_mctx_1276_);
v_opts_1277_ = lean_ctor_get(v_fst_1258_, 3);
lean_inc_ref(v_opts_1277_);
lean_dec(v_fst_1258_);
v___x_1278_ = lean_box(0);
v___x_1279_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_snd_1268_, v___x_1273_, v___x_1278_);
lean_inc(v_snd_1242_);
lean_inc(v_fst_1241_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 1, v_snd_1242_);
lean_ctor_set(v___x_1260_, 0, v_fst_1241_);
v___x_1281_ = v___x_1260_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_fst_1241_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_snd_1242_);
v___x_1281_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1285_; 
lean_inc(v___x_1243_);
v___x_1282_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
lean_ctor_set(v___x_1282_, 1, v___x_1243_);
lean_ctor_set(v___x_1282_, 2, v_env_1275_);
lean_ctor_set(v___x_1282_, 3, v_mctx_1276_);
lean_ctor_set(v___x_1282_, 4, v_opts_1277_);
lean_ctor_set(v___x_1282_, 5, v_fst_1262_);
lean_ctor_set(v___x_1282_, 6, v_snd_1263_);
v___x_1283_ = lean_array_push(v_fst_1267_, v___x_1282_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 1, v___x_1279_);
lean_ctor_set(v___x_1265_, 0, v___x_1283_);
v___x_1285_ = v___x_1265_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1283_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v___x_1279_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
v_a_1250_ = v___x_1285_;
goto v___jp_1249_;
}
}
}
else
{
lean_object* v___x_1289_; 
lean_dec_ref(v___x_1273_);
lean_dec(v_snd_1263_);
lean_dec(v_fst_1262_);
lean_del_object(v___x_1260_);
lean_dec(v_fst_1258_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 1, v_snd_1268_);
lean_ctor_set(v___x_1265_, 0, v_fst_1267_);
v___x_1289_ = v___x_1265_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_fst_1267_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_snd_1268_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
v_a_1250_ = v___x_1289_;
goto v___jp_1249_;
}
}
}
}
}
}
}
v___jp_1249_:
{
size_t v___x_1251_; size_t v___x_1252_; 
v___x_1251_ = ((size_t)1ULL);
v___x_1252_ = lean_usize_add(v_i_1246_, v___x_1251_);
v_i_1246_ = v___x_1252_;
v_b_1247_ = v_a_1250_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg___boxed(lean_object* v___x_1295_, lean_object* v_fst_1296_, lean_object* v_snd_1297_, lean_object* v___x_1298_, lean_object* v_as_1299_, lean_object* v_sz_1300_, lean_object* v_i_1301_, lean_object* v_b_1302_, lean_object* v___y_1303_){
_start:
{
size_t v_sz_boxed_1304_; size_t v_i_boxed_1305_; lean_object* v_res_1306_; 
v_sz_boxed_1304_ = lean_unbox_usize(v_sz_1300_);
lean_dec(v_sz_1300_);
v_i_boxed_1305_ = lean_unbox_usize(v_i_1301_);
lean_dec(v_i_1301_);
v_res_1306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1295_, v_fst_1296_, v_snd_1297_, v___x_1298_, v_as_1299_, v_sz_boxed_1304_, v_i_boxed_1305_, v_b_1302_);
lean_dec_ref(v_as_1299_);
return v_res_1306_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1312_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__2));
v___x_1313_ = l_Lean_Name_append(v___x_1312_, v___x_1311_);
return v___x_1313_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__4));
v___x_1316_ = l_Lean_stringToMessageData(v___x_1315_);
return v___x_1316_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__6));
v___x_1319_ = l_Lean_stringToMessageData(v___x_1318_);
return v___x_1319_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9(void){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__8));
v___x_1322_ = l_Lean_stringToMessageData(v___x_1321_);
return v___x_1322_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11(void){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__10));
v___x_1325_ = l_Lean_stringToMessageData(v___x_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12(lean_object* v___x_1326_, lean_object* v_val_1327_, lean_object* v_cmd_1328_, uint8_t v_onUnsolved_1329_, uint8_t v___y_1330_, lean_object* v_as_1331_, size_t v_sz_1332_, size_t v_i_1333_, lean_object* v_b_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
uint8_t v___x_1338_; 
v___x_1338_ = lean_usize_dec_lt(v_i_1333_, v_sz_1332_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; 
lean_dec(v_cmd_1328_);
v___x_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1339_, 0, v_b_1334_);
return v___x_1339_;
}
else
{
lean_object* v_snd_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1488_; 
v_snd_1340_ = lean_ctor_get(v_b_1334_, 1);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_b_1334_);
if (v_isSharedCheck_1488_ == 0)
{
lean_object* v_unused_1489_; 
v_unused_1489_ = lean_ctor_get(v_b_1334_, 0);
lean_dec(v_unused_1489_);
v___x_1342_ = v_b_1334_;
v_isShared_1343_ = v_isSharedCheck_1488_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_snd_1340_);
lean_dec(v_b_1334_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1488_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v_fst_1344_; lean_object* v_snd_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1487_; 
v_fst_1344_ = lean_ctor_get(v_snd_1340_, 0);
v_snd_1345_ = lean_ctor_get(v_snd_1340_, 1);
v_isSharedCheck_1487_ = !lean_is_exclusive(v_snd_1340_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1347_ = v_snd_1340_;
v_isShared_1348_ = v_isSharedCheck_1487_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_snd_1345_);
lean_inc(v_fst_1344_);
lean_dec(v_snd_1340_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1487_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v_a_1349_; lean_object* v_pos_1350_; lean_object* v_endPos_1351_; uint8_t v_severity_1352_; lean_object* v_data_1353_; lean_object* v___x_1354_; lean_object* v_a_1356_; 
v_a_1349_ = lean_array_uget_borrowed(v_as_1331_, v_i_1333_);
v_pos_1350_ = lean_ctor_get(v_a_1349_, 1);
v_endPos_1351_ = lean_ctor_get(v_a_1349_, 2);
lean_inc(v_endPos_1351_);
v_severity_1352_ = lean_ctor_get_uint8(v_a_1349_, sizeof(void*)*5 + 1);
v_data_1353_ = lean_ctor_get(v_a_1349_, 4);
v___x_1354_ = lean_box(0);
if (v_severity_1352_ == 2)
{
lean_object* v___f_1369_; uint8_t v___x_1370_; 
v___f_1369_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
lean_inc(v_data_1353_);
v___x_1370_ = l_Lean_MessageData_hasTag(v___f_1369_, v_data_1353_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; 
lean_dec(v_endPos_1351_);
lean_del_object(v___x_1342_);
v___x_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1371_, 0, v_fst_1344_);
lean_ctor_set(v___x_1371_, 1, v_snd_1345_);
v_a_1356_ = v___x_1371_;
goto v___jp_1355_;
}
else
{
if (lean_obj_tag(v_endPos_1351_) == 1)
{
lean_object* v_val_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1484_; 
v_val_1372_ = lean_ctor_get(v_endPos_1351_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v_endPos_1351_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1374_ = v_endPos_1351_;
v_isShared_1375_ = v_isSharedCheck_1484_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_val_1372_);
lean_dec(v_endPos_1351_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1484_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; uint8_t v___x_1380_; 
lean_inc_ref(v_pos_1350_);
v___x_1376_ = l_Lean_FileMap_ofPosition(v___x_1326_, v_pos_1350_);
v___x_1377_ = l_Lean_FileMap_ofPosition(v___x_1326_, v_val_1372_);
lean_inc(v___x_1377_);
lean_inc(v___x_1376_);
v___x_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1376_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
v___x_1379_ = 0;
v___x_1380_ = l_Lean_Syntax_Range_includes(v_val_1327_, v___x_1378_, v___x_1379_, v___x_1379_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; 
lean_dec_ref_known(v___x_1378_, 2);
lean_dec(v___x_1377_);
lean_dec(v___x_1376_);
lean_del_object(v___x_1374_);
lean_del_object(v___x_1342_);
v___x_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1381_, 0, v_fst_1344_);
lean_ctor_set(v___x_1381_, 1, v_snd_1345_);
v_a_1356_ = v___x_1381_;
goto v___jp_1355_;
}
else
{
lean_object* v___x_1382_; 
lean_inc(v_cmd_1328_);
lean_inc_ref(v___x_1378_);
v___x_1382_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1378_, v_cmd_1328_);
if (lean_obj_tag(v___x_1382_) == 1)
{
lean_object* v_val_1383_; lean_object* v_fst_1384_; lean_object* v_snd_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1448_; 
lean_dec(v___x_1377_);
lean_dec(v___x_1376_);
lean_del_object(v___x_1374_);
v_val_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_val_1383_);
lean_dec_ref_known(v___x_1382_, 1);
v_fst_1384_ = lean_ctor_get(v_val_1383_, 0);
v_snd_1385_ = lean_ctor_get(v_val_1383_, 1);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_val_1383_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1387_ = v_val_1383_;
v_isShared_1388_ = v_isSharedCheck_1448_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_snd_1385_);
lean_inc(v_fst_1384_);
lean_dec(v_val_1383_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1448_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; uint8_t v___y_1446_; lean_object* v___x_1447_; 
v___x_1447_ = l_Lean_Syntax_getPos_x3f(v_fst_1384_, v___x_1379_);
if (lean_obj_tag(v___x_1447_) == 0)
{
v___y_1446_ = v___x_1380_;
goto v___jp_1445_;
}
else
{
lean_dec_ref_known(v___x_1447_, 1);
v___y_1446_ = v___x_1379_;
goto v___jp_1445_;
}
v___jp_1389_:
{
lean_object* v___x_1395_; 
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 1, v_snd_1345_);
lean_ctor_set(v___x_1387_, 0, v_fst_1344_);
v___x_1395_ = v___x_1387_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_fst_1344_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_snd_1345_);
v___x_1395_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
size_t v_sz_1396_; size_t v___x_1397_; lean_object* v___x_1398_; 
v_sz_1396_ = lean_array_size(v___y_1391_);
v___x_1397_ = ((size_t)0ULL);
v___x_1398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1378_, v_fst_1384_, v_snd_1385_, v___y_1390_, v___y_1391_, v_sz_1396_, v___x_1397_, v___x_1395_);
lean_dec_ref(v___y_1391_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v_fst_1400_; lean_object* v_snd_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_a_1399_);
lean_dec_ref_known(v___x_1398_, 1);
v_fst_1400_ = lean_ctor_get(v_a_1399_, 0);
v_snd_1401_ = lean_ctor_get(v_a_1399_, 1);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_a_1399_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v_a_1399_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_snd_1401_);
lean_inc(v_fst_1400_);
lean_dec(v_a_1399_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_fst_1400_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_snd_1401_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
v_a_1356_ = v___x_1406_;
goto v___jp_1355_;
}
}
}
else
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
lean_del_object(v___x_1347_);
lean_dec(v_cmd_1328_);
v_a_1409_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1398_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1398_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
v___jp_1418_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; uint8_t v___x_1423_; 
lean_inc_ref(v___x_1378_);
v___x_1419_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1378_);
v___x_1420_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1353_);
v___x_1421_ = lean_array_get_size(v___x_1420_);
v___x_1422_ = lean_unsigned_to_nat(0u);
v___x_1423_ = lean_nat_dec_eq(v___x_1421_, v___x_1422_);
if (v___x_1423_ == 0)
{
v___y_1390_ = v___x_1419_;
v___y_1391_ = v___x_1420_;
v___y_1392_ = v___y_1335_;
v___y_1393_ = v___y_1336_;
goto v___jp_1389_;
}
else
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v_scopes_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v_opts_1430_; uint8_t v_hasTrace_1431_; 
v___x_1424_ = l_Lean_inheritedTraceOptions;
v___x_1425_ = lean_st_ref_get(v___x_1424_);
v___x_1426_ = lean_st_ref_get(v___y_1336_);
v_scopes_1427_ = lean_ctor_get(v___x_1426_, 2);
lean_inc(v_scopes_1427_);
lean_dec(v___x_1426_);
v___x_1428_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1429_ = l_List_head_x21___redArg(v___x_1428_, v_scopes_1427_);
lean_dec(v_scopes_1427_);
v_opts_1430_ = lean_ctor_get(v___x_1429_, 1);
lean_inc_ref(v_opts_1430_);
lean_dec(v___x_1429_);
v_hasTrace_1431_ = lean_ctor_get_uint8(v_opts_1430_, sizeof(void*)*1);
if (v_hasTrace_1431_ == 0)
{
lean_dec_ref(v_opts_1430_);
lean_dec(v___x_1425_);
v___y_1390_ = v___x_1419_;
v___y_1391_ = v___x_1420_;
v___y_1392_ = v___y_1335_;
v___y_1393_ = v___y_1336_;
goto v___jp_1389_;
}
else
{
lean_object* v___x_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v___x_1432_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1433_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1434_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1425_, v_opts_1430_, v___x_1433_);
lean_dec_ref(v_opts_1430_);
lean_dec(v___x_1425_);
if (v___x_1434_ == 0)
{
v___y_1390_ = v___x_1419_;
v___y_1391_ = v___x_1420_;
v___y_1392_ = v___y_1335_;
v___y_1393_ = v___y_1336_;
goto v___jp_1389_;
}
else
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1435_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5);
v___x_1436_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1432_, v___x_1435_, v___y_1335_, v___y_1336_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_dec_ref_known(v___x_1436_, 1);
v___y_1390_ = v___x_1419_;
v___y_1391_ = v___x_1420_;
v___y_1392_ = v___y_1335_;
v___y_1393_ = v___y_1336_;
goto v___jp_1389_;
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec_ref(v___x_1420_);
lean_dec(v___x_1419_);
lean_del_object(v___x_1387_);
lean_dec(v_snd_1385_);
lean_dec(v_fst_1384_);
lean_dec_ref_known(v___x_1378_, 2);
lean_del_object(v___x_1347_);
lean_dec(v_snd_1345_);
lean_dec(v_fst_1344_);
lean_dec(v_cmd_1328_);
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
}
}
}
v___jp_1445_:
{
if (v_onUnsolved_1329_ == 0)
{
if (v___y_1330_ == 0)
{
lean_del_object(v___x_1387_);
lean_dec(v_snd_1385_);
lean_dec(v_fst_1384_);
lean_dec_ref_known(v___x_1378_, 2);
goto v___jp_1363_;
}
else
{
if (v___y_1446_ == 0)
{
lean_del_object(v___x_1387_);
lean_dec(v_snd_1385_);
lean_dec(v_fst_1384_);
lean_dec_ref_known(v___x_1378_, 2);
goto v___jp_1363_;
}
else
{
lean_del_object(v___x_1342_);
goto v___jp_1418_;
}
}
}
else
{
lean_del_object(v___x_1342_);
goto v___jp_1418_;
}
}
}
}
else
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v_scopes_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v_opts_1455_; uint8_t v_hasTrace_1456_; 
lean_dec(v___x_1382_);
lean_dec_ref_known(v___x_1378_, 2);
lean_del_object(v___x_1342_);
v___x_1449_ = l_Lean_inheritedTraceOptions;
v___x_1450_ = lean_st_ref_get(v___x_1449_);
v___x_1451_ = lean_st_ref_get(v___y_1336_);
v_scopes_1452_ = lean_ctor_get(v___x_1451_, 2);
lean_inc(v_scopes_1452_);
lean_dec(v___x_1451_);
v___x_1453_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1454_ = l_List_head_x21___redArg(v___x_1453_, v_scopes_1452_);
lean_dec(v_scopes_1452_);
v_opts_1455_ = lean_ctor_get(v___x_1454_, 1);
lean_inc_ref(v_opts_1455_);
lean_dec(v___x_1454_);
v_hasTrace_1456_ = lean_ctor_get_uint8(v_opts_1455_, sizeof(void*)*1);
if (v_hasTrace_1456_ == 0)
{
lean_dec_ref(v_opts_1455_);
lean_dec(v___x_1450_);
lean_dec(v___x_1377_);
lean_dec(v___x_1376_);
lean_del_object(v___x_1374_);
goto v___jp_1367_;
}
else
{
lean_object* v___x_1457_; lean_object* v___x_1458_; uint8_t v___x_1459_; 
v___x_1457_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1458_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1459_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1450_, v_opts_1455_, v___x_1458_);
lean_dec_ref(v_opts_1455_);
lean_dec(v___x_1450_);
if (v___x_1459_ == 0)
{
lean_dec(v___x_1377_);
lean_dec(v___x_1376_);
lean_del_object(v___x_1374_);
goto v___jp_1367_;
}
else
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1463_; 
v___x_1460_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7);
v___x_1461_ = l_Nat_reprFast(v___x_1376_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set_tag(v___x_1374_, 3);
lean_ctor_set(v___x_1374_, 0, v___x_1461_);
v___x_1463_ = v___x_1374_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1461_);
v___x_1463_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1464_ = l_Lean_MessageData_ofFormat(v___x_1463_);
v___x_1465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1460_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
v___x_1466_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9);
v___x_1467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1465_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v___x_1468_ = l_Nat_reprFast(v___x_1377_);
v___x_1469_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
v___x_1470_ = l_Lean_MessageData_ofFormat(v___x_1469_);
v___x_1471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1467_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11);
v___x_1473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1471_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
v___x_1474_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1457_, v___x_1473_, v___y_1335_, v___y_1336_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_dec_ref_known(v___x_1474_, 1);
goto v___jp_1367_;
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
lean_del_object(v___x_1347_);
lean_dec(v_snd_1345_);
lean_dec(v_fst_1344_);
lean_dec(v_cmd_1328_);
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1474_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1474_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
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
lean_object* v___x_1485_; 
lean_dec(v_endPos_1351_);
lean_del_object(v___x_1342_);
v___x_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1485_, 0, v_fst_1344_);
lean_ctor_set(v___x_1485_, 1, v_snd_1345_);
v_a_1356_ = v___x_1485_;
goto v___jp_1355_;
}
}
}
else
{
lean_object* v___x_1486_; 
lean_dec(v_endPos_1351_);
lean_del_object(v___x_1342_);
v___x_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1486_, 0, v_fst_1344_);
lean_ctor_set(v___x_1486_, 1, v_snd_1345_);
v_a_1356_ = v___x_1486_;
goto v___jp_1355_;
}
v___jp_1355_:
{
lean_object* v___x_1358_; 
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 1, v_a_1356_);
lean_ctor_set(v___x_1347_, 0, v___x_1354_);
v___x_1358_ = v___x_1347_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1354_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_a_1356_);
v___x_1358_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
size_t v___x_1359_; size_t v___x_1360_; 
v___x_1359_ = ((size_t)1ULL);
v___x_1360_ = lean_usize_add(v_i_1333_, v___x_1359_);
v_i_1333_ = v___x_1360_;
v_b_1334_ = v___x_1358_;
goto _start;
}
}
v___jp_1363_:
{
lean_object* v___x_1365_; 
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 1, v_snd_1345_);
lean_ctor_set(v___x_1342_, 0, v_fst_1344_);
v___x_1365_ = v___x_1342_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_fst_1344_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_snd_1345_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
v_a_1356_ = v___x_1365_;
goto v___jp_1355_;
}
}
v___jp_1367_:
{
lean_object* v___x_1368_; 
v___x_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1368_, 0, v_fst_1344_);
lean_ctor_set(v___x_1368_, 1, v_snd_1345_);
v_a_1356_ = v___x_1368_;
goto v___jp_1355_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___boxed(lean_object* v___x_1490_, lean_object* v_val_1491_, lean_object* v_cmd_1492_, lean_object* v_onUnsolved_1493_, lean_object* v___y_1494_, lean_object* v_as_1495_, lean_object* v_sz_1496_, lean_object* v_i_1497_, lean_object* v_b_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
uint8_t v_onUnsolved_boxed_1502_; uint8_t v___y_11928__boxed_1503_; size_t v_sz_boxed_1504_; size_t v_i_boxed_1505_; lean_object* v_res_1506_; 
v_onUnsolved_boxed_1502_ = lean_unbox(v_onUnsolved_1493_);
v___y_11928__boxed_1503_ = lean_unbox(v___y_1494_);
v_sz_boxed_1504_ = lean_unbox_usize(v_sz_1496_);
lean_dec(v_sz_1496_);
v_i_boxed_1505_ = lean_unbox_usize(v_i_1497_);
lean_dec(v_i_1497_);
v_res_1506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12(v___x_1490_, v_val_1491_, v_cmd_1492_, v_onUnsolved_boxed_1502_, v___y_11928__boxed_1503_, v_as_1495_, v_sz_boxed_1504_, v_i_boxed_1505_, v_b_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec_ref(v_as_1495_);
lean_dec_ref(v_val_1491_);
lean_dec_ref(v___x_1490_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8(lean_object* v___x_1507_, lean_object* v_val_1508_, lean_object* v_cmd_1509_, uint8_t v_onUnsolved_1510_, uint8_t v___y_1511_, lean_object* v_as_1512_, size_t v_sz_1513_, size_t v_i_1514_, lean_object* v_b_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
uint8_t v___x_1519_; 
v___x_1519_ = lean_usize_dec_lt(v_i_1514_, v_sz_1513_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; 
lean_dec(v_cmd_1509_);
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v_b_1515_);
return v___x_1520_;
}
else
{
lean_object* v_snd_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1669_; 
v_snd_1521_ = lean_ctor_get(v_b_1515_, 1);
v_isSharedCheck_1669_ = !lean_is_exclusive(v_b_1515_);
if (v_isSharedCheck_1669_ == 0)
{
lean_object* v_unused_1670_; 
v_unused_1670_ = lean_ctor_get(v_b_1515_, 0);
lean_dec(v_unused_1670_);
v___x_1523_ = v_b_1515_;
v_isShared_1524_ = v_isSharedCheck_1669_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_snd_1521_);
lean_dec(v_b_1515_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1669_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v_fst_1525_; lean_object* v_snd_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1668_; 
v_fst_1525_ = lean_ctor_get(v_snd_1521_, 0);
v_snd_1526_ = lean_ctor_get(v_snd_1521_, 1);
v_isSharedCheck_1668_ = !lean_is_exclusive(v_snd_1521_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1528_ = v_snd_1521_;
v_isShared_1529_ = v_isSharedCheck_1668_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_snd_1526_);
lean_inc(v_fst_1525_);
lean_dec(v_snd_1521_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1668_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v_a_1530_; lean_object* v_pos_1531_; lean_object* v_endPos_1532_; uint8_t v_severity_1533_; lean_object* v_data_1534_; lean_object* v___x_1535_; lean_object* v_a_1537_; 
v_a_1530_ = lean_array_uget_borrowed(v_as_1512_, v_i_1514_);
v_pos_1531_ = lean_ctor_get(v_a_1530_, 1);
v_endPos_1532_ = lean_ctor_get(v_a_1530_, 2);
lean_inc(v_endPos_1532_);
v_severity_1533_ = lean_ctor_get_uint8(v_a_1530_, sizeof(void*)*5 + 1);
v_data_1534_ = lean_ctor_get(v_a_1530_, 4);
v___x_1535_ = lean_box(0);
if (v_severity_1533_ == 2)
{
lean_object* v___f_1550_; uint8_t v___x_1551_; 
v___f_1550_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
lean_inc(v_data_1534_);
v___x_1551_ = l_Lean_MessageData_hasTag(v___f_1550_, v_data_1534_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; 
lean_dec(v_endPos_1532_);
lean_del_object(v___x_1523_);
v___x_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1552_, 0, v_fst_1525_);
lean_ctor_set(v___x_1552_, 1, v_snd_1526_);
v_a_1537_ = v___x_1552_;
goto v___jp_1536_;
}
else
{
if (lean_obj_tag(v_endPos_1532_) == 1)
{
lean_object* v_val_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1665_; 
v_val_1553_ = lean_ctor_get(v_endPos_1532_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_endPos_1532_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1555_ = v_endPos_1532_;
v_isShared_1556_ = v_isSharedCheck_1665_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_val_1553_);
lean_dec(v_endPos_1532_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1665_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; uint8_t v___x_1560_; uint8_t v___x_1561_; 
lean_inc_ref(v_pos_1531_);
v___x_1557_ = l_Lean_FileMap_ofPosition(v___x_1507_, v_pos_1531_);
v___x_1558_ = l_Lean_FileMap_ofPosition(v___x_1507_, v_val_1553_);
lean_inc(v___x_1558_);
lean_inc(v___x_1557_);
v___x_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = 0;
v___x_1561_ = l_Lean_Syntax_Range_includes(v_val_1508_, v___x_1559_, v___x_1560_, v___x_1560_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; 
lean_dec_ref_known(v___x_1559_, 2);
lean_dec(v___x_1558_);
lean_dec(v___x_1557_);
lean_del_object(v___x_1555_);
lean_del_object(v___x_1523_);
v___x_1562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1562_, 0, v_fst_1525_);
lean_ctor_set(v___x_1562_, 1, v_snd_1526_);
v_a_1537_ = v___x_1562_;
goto v___jp_1536_;
}
else
{
lean_object* v___x_1563_; 
lean_inc(v_cmd_1509_);
lean_inc_ref(v___x_1559_);
v___x_1563_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1559_, v_cmd_1509_);
if (lean_obj_tag(v___x_1563_) == 1)
{
lean_object* v_val_1564_; lean_object* v_fst_1565_; lean_object* v_snd_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1629_; 
lean_dec(v___x_1558_);
lean_dec(v___x_1557_);
lean_del_object(v___x_1555_);
v_val_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_val_1564_);
lean_dec_ref_known(v___x_1563_, 1);
v_fst_1565_ = lean_ctor_get(v_val_1564_, 0);
v_snd_1566_ = lean_ctor_get(v_val_1564_, 1);
v_isSharedCheck_1629_ = !lean_is_exclusive(v_val_1564_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1568_ = v_val_1564_;
v_isShared_1569_ = v_isSharedCheck_1629_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_snd_1566_);
lean_inc(v_fst_1565_);
lean_dec(v_val_1564_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1629_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; uint8_t v___y_1627_; lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_Syntax_getPos_x3f(v_fst_1565_, v___x_1560_);
if (lean_obj_tag(v___x_1628_) == 0)
{
v___y_1627_ = v___x_1561_;
goto v___jp_1626_;
}
else
{
lean_dec_ref_known(v___x_1628_, 1);
v___y_1627_ = v___x_1560_;
goto v___jp_1626_;
}
v___jp_1570_:
{
lean_object* v___x_1576_; 
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 1, v_snd_1526_);
lean_ctor_set(v___x_1568_, 0, v_fst_1525_);
v___x_1576_ = v___x_1568_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_fst_1525_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v_snd_1526_);
v___x_1576_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
size_t v_sz_1577_; size_t v___x_1578_; lean_object* v___x_1579_; 
v_sz_1577_ = lean_array_size(v___y_1571_);
v___x_1578_ = ((size_t)0ULL);
v___x_1579_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1559_, v_fst_1565_, v_snd_1566_, v___y_1572_, v___y_1571_, v_sz_1577_, v___x_1578_, v___x_1576_);
lean_dec_ref(v___y_1571_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v_fst_1581_; lean_object* v_snd_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 1);
v_fst_1581_ = lean_ctor_get(v_a_1580_, 0);
v_snd_1582_ = lean_ctor_get(v_a_1580_, 1);
v_isSharedCheck_1589_ = !lean_is_exclusive(v_a_1580_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v_a_1580_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_snd_1582_);
lean_inc(v_fst_1581_);
lean_dec(v_a_1580_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_fst_1581_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_snd_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
v_a_1537_ = v___x_1587_;
goto v___jp_1536_;
}
}
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_del_object(v___x_1528_);
lean_dec(v_cmd_1509_);
v_a_1590_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1579_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1579_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
}
v___jp_1599_:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; uint8_t v___x_1604_; 
lean_inc_ref(v___x_1559_);
v___x_1600_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1559_);
v___x_1601_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1534_);
v___x_1602_ = lean_array_get_size(v___x_1601_);
v___x_1603_ = lean_unsigned_to_nat(0u);
v___x_1604_ = lean_nat_dec_eq(v___x_1602_, v___x_1603_);
if (v___x_1604_ == 0)
{
v___y_1571_ = v___x_1601_;
v___y_1572_ = v___x_1600_;
v___y_1573_ = v___y_1516_;
v___y_1574_ = v___y_1517_;
goto v___jp_1570_;
}
else
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v_scopes_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v_opts_1611_; uint8_t v_hasTrace_1612_; 
v___x_1605_ = l_Lean_inheritedTraceOptions;
v___x_1606_ = lean_st_ref_get(v___x_1605_);
v___x_1607_ = lean_st_ref_get(v___y_1517_);
v_scopes_1608_ = lean_ctor_get(v___x_1607_, 2);
lean_inc(v_scopes_1608_);
lean_dec(v___x_1607_);
v___x_1609_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1610_ = l_List_head_x21___redArg(v___x_1609_, v_scopes_1608_);
lean_dec(v_scopes_1608_);
v_opts_1611_ = lean_ctor_get(v___x_1610_, 1);
lean_inc_ref(v_opts_1611_);
lean_dec(v___x_1610_);
v_hasTrace_1612_ = lean_ctor_get_uint8(v_opts_1611_, sizeof(void*)*1);
if (v_hasTrace_1612_ == 0)
{
lean_dec_ref(v_opts_1611_);
lean_dec(v___x_1606_);
v___y_1571_ = v___x_1601_;
v___y_1572_ = v___x_1600_;
v___y_1573_ = v___y_1516_;
v___y_1574_ = v___y_1517_;
goto v___jp_1570_;
}
else
{
lean_object* v___x_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
v___x_1613_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1614_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1615_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1606_, v_opts_1611_, v___x_1614_);
lean_dec_ref(v_opts_1611_);
lean_dec(v___x_1606_);
if (v___x_1615_ == 0)
{
v___y_1571_ = v___x_1601_;
v___y_1572_ = v___x_1600_;
v___y_1573_ = v___y_1516_;
v___y_1574_ = v___y_1517_;
goto v___jp_1570_;
}
else
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5);
v___x_1617_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1613_, v___x_1616_, v___y_1516_, v___y_1517_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_dec_ref_known(v___x_1617_, 1);
v___y_1571_ = v___x_1601_;
v___y_1572_ = v___x_1600_;
v___y_1573_ = v___y_1516_;
v___y_1574_ = v___y_1517_;
goto v___jp_1570_;
}
else
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
lean_dec_ref(v___x_1601_);
lean_dec(v___x_1600_);
lean_del_object(v___x_1568_);
lean_dec(v_snd_1566_);
lean_dec(v_fst_1565_);
lean_dec_ref_known(v___x_1559_, 2);
lean_del_object(v___x_1528_);
lean_dec(v_snd_1526_);
lean_dec(v_fst_1525_);
lean_dec(v_cmd_1509_);
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1617_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1617_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
}
}
}
v___jp_1626_:
{
if (v_onUnsolved_1510_ == 0)
{
if (v___y_1511_ == 0)
{
lean_del_object(v___x_1568_);
lean_dec(v_snd_1566_);
lean_dec(v_fst_1565_);
lean_dec_ref_known(v___x_1559_, 2);
goto v___jp_1544_;
}
else
{
if (v___y_1627_ == 0)
{
lean_del_object(v___x_1568_);
lean_dec(v_snd_1566_);
lean_dec(v_fst_1565_);
lean_dec_ref_known(v___x_1559_, 2);
goto v___jp_1544_;
}
else
{
lean_del_object(v___x_1523_);
goto v___jp_1599_;
}
}
}
else
{
lean_del_object(v___x_1523_);
goto v___jp_1599_;
}
}
}
}
else
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v_scopes_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v_opts_1636_; uint8_t v_hasTrace_1637_; 
lean_dec(v___x_1563_);
lean_dec_ref_known(v___x_1559_, 2);
lean_del_object(v___x_1523_);
v___x_1630_ = l_Lean_inheritedTraceOptions;
v___x_1631_ = lean_st_ref_get(v___x_1630_);
v___x_1632_ = lean_st_ref_get(v___y_1517_);
v_scopes_1633_ = lean_ctor_get(v___x_1632_, 2);
lean_inc(v_scopes_1633_);
lean_dec(v___x_1632_);
v___x_1634_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1635_ = l_List_head_x21___redArg(v___x_1634_, v_scopes_1633_);
lean_dec(v_scopes_1633_);
v_opts_1636_ = lean_ctor_get(v___x_1635_, 1);
lean_inc_ref(v_opts_1636_);
lean_dec(v___x_1635_);
v_hasTrace_1637_ = lean_ctor_get_uint8(v_opts_1636_, sizeof(void*)*1);
if (v_hasTrace_1637_ == 0)
{
lean_dec_ref(v_opts_1636_);
lean_dec(v___x_1631_);
lean_dec(v___x_1558_);
lean_dec(v___x_1557_);
lean_del_object(v___x_1555_);
goto v___jp_1548_;
}
else
{
lean_object* v___x_1638_; lean_object* v___x_1639_; uint8_t v___x_1640_; 
v___x_1638_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1639_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1640_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1631_, v_opts_1636_, v___x_1639_);
lean_dec_ref(v_opts_1636_);
lean_dec(v___x_1631_);
if (v___x_1640_ == 0)
{
lean_dec(v___x_1558_);
lean_dec(v___x_1557_);
lean_del_object(v___x_1555_);
goto v___jp_1548_;
}
else
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1644_; 
v___x_1641_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7);
v___x_1642_ = l_Nat_reprFast(v___x_1557_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set_tag(v___x_1555_, 3);
lean_ctor_set(v___x_1555_, 0, v___x_1642_);
v___x_1644_ = v___x_1555_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1645_ = l_Lean_MessageData_ofFormat(v___x_1644_);
v___x_1646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1641_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
v___x_1647_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9);
v___x_1648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1646_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v___x_1649_ = l_Nat_reprFast(v___x_1558_);
v___x_1650_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1649_);
v___x_1651_ = l_Lean_MessageData_ofFormat(v___x_1650_);
v___x_1652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1648_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
v___x_1653_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11);
v___x_1654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1652_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1638_, v___x_1654_, v___y_1516_, v___y_1517_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_dec_ref_known(v___x_1655_, 1);
goto v___jp_1548_;
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_del_object(v___x_1528_);
lean_dec(v_snd_1526_);
lean_dec(v_fst_1525_);
lean_dec(v_cmd_1509_);
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1655_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1655_);
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
}
}
}
}
else
{
lean_object* v___x_1666_; 
lean_dec(v_endPos_1532_);
lean_del_object(v___x_1523_);
v___x_1666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1666_, 0, v_fst_1525_);
lean_ctor_set(v___x_1666_, 1, v_snd_1526_);
v_a_1537_ = v___x_1666_;
goto v___jp_1536_;
}
}
}
else
{
lean_object* v___x_1667_; 
lean_dec(v_endPos_1532_);
lean_del_object(v___x_1523_);
v___x_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1667_, 0, v_fst_1525_);
lean_ctor_set(v___x_1667_, 1, v_snd_1526_);
v_a_1537_ = v___x_1667_;
goto v___jp_1536_;
}
v___jp_1536_:
{
lean_object* v___x_1539_; 
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 1, v_a_1537_);
lean_ctor_set(v___x_1528_, 0, v___x_1535_);
v___x_1539_ = v___x_1528_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1535_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_a_1537_);
v___x_1539_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
size_t v___x_1540_; size_t v___x_1541_; lean_object* v___x_1542_; 
v___x_1540_ = ((size_t)1ULL);
v___x_1541_ = lean_usize_add(v_i_1514_, v___x_1540_);
v___x_1542_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12(v___x_1507_, v_val_1508_, v_cmd_1509_, v_onUnsolved_1510_, v___y_1511_, v_as_1512_, v_sz_1513_, v___x_1541_, v___x_1539_, v___y_1516_, v___y_1517_);
return v___x_1542_;
}
}
v___jp_1544_:
{
lean_object* v___x_1546_; 
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 1, v_snd_1526_);
lean_ctor_set(v___x_1523_, 0, v_fst_1525_);
v___x_1546_ = v___x_1523_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_fst_1525_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_snd_1526_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
v_a_1537_ = v___x_1546_;
goto v___jp_1536_;
}
}
v___jp_1548_:
{
lean_object* v___x_1549_; 
v___x_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1549_, 0, v_fst_1525_);
lean_ctor_set(v___x_1549_, 1, v_snd_1526_);
v_a_1537_ = v___x_1549_;
goto v___jp_1536_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___boxed(lean_object* v___x_1671_, lean_object* v_val_1672_, lean_object* v_cmd_1673_, lean_object* v_onUnsolved_1674_, lean_object* v___y_1675_, lean_object* v_as_1676_, lean_object* v_sz_1677_, lean_object* v_i_1678_, lean_object* v_b_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
uint8_t v_onUnsolved_boxed_1683_; uint8_t v___y_12269__boxed_1684_; size_t v_sz_boxed_1685_; size_t v_i_boxed_1686_; lean_object* v_res_1687_; 
v_onUnsolved_boxed_1683_ = lean_unbox(v_onUnsolved_1674_);
v___y_12269__boxed_1684_ = lean_unbox(v___y_1675_);
v_sz_boxed_1685_ = lean_unbox_usize(v_sz_1677_);
lean_dec(v_sz_1677_);
v_i_boxed_1686_ = lean_unbox_usize(v_i_1678_);
lean_dec(v_i_1678_);
v_res_1687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8(v___x_1671_, v_val_1672_, v_cmd_1673_, v_onUnsolved_boxed_1683_, v___y_12269__boxed_1684_, v_as_1676_, v_sz_boxed_1685_, v_i_boxed_1686_, v_b_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec_ref(v_as_1676_);
lean_dec_ref(v_val_1672_);
lean_dec_ref(v___x_1671_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10_spec__12(lean_object* v___x_1688_, lean_object* v_val_1689_, lean_object* v_cmd_1690_, uint8_t v_onUnsolved_1691_, uint8_t v___y_1692_, lean_object* v_as_1693_, size_t v_sz_1694_, size_t v_i_1695_, lean_object* v_b_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
uint8_t v___x_1700_; 
v___x_1700_ = lean_usize_dec_lt(v_i_1695_, v_sz_1694_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; 
lean_dec(v_cmd_1690_);
v___x_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1701_, 0, v_b_1696_);
return v___x_1701_;
}
else
{
lean_object* v_snd_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1850_; 
v_snd_1702_ = lean_ctor_get(v_b_1696_, 1);
v_isSharedCheck_1850_ = !lean_is_exclusive(v_b_1696_);
if (v_isSharedCheck_1850_ == 0)
{
lean_object* v_unused_1851_; 
v_unused_1851_ = lean_ctor_get(v_b_1696_, 0);
lean_dec(v_unused_1851_);
v___x_1704_ = v_b_1696_;
v_isShared_1705_ = v_isSharedCheck_1850_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_snd_1702_);
lean_dec(v_b_1696_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1850_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v_fst_1706_; lean_object* v_snd_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1849_; 
v_fst_1706_ = lean_ctor_get(v_snd_1702_, 0);
v_snd_1707_ = lean_ctor_get(v_snd_1702_, 1);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_snd_1702_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1709_ = v_snd_1702_;
v_isShared_1710_ = v_isSharedCheck_1849_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_snd_1707_);
lean_inc(v_fst_1706_);
lean_dec(v_snd_1702_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1849_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v_a_1711_; lean_object* v_pos_1712_; lean_object* v_endPos_1713_; uint8_t v_severity_1714_; lean_object* v_data_1715_; lean_object* v___x_1716_; lean_object* v_a_1718_; 
v_a_1711_ = lean_array_uget_borrowed(v_as_1693_, v_i_1695_);
v_pos_1712_ = lean_ctor_get(v_a_1711_, 1);
v_endPos_1713_ = lean_ctor_get(v_a_1711_, 2);
lean_inc(v_endPos_1713_);
v_severity_1714_ = lean_ctor_get_uint8(v_a_1711_, sizeof(void*)*5 + 1);
v_data_1715_ = lean_ctor_get(v_a_1711_, 4);
v___x_1716_ = lean_box(0);
if (v_severity_1714_ == 2)
{
lean_object* v___f_1731_; uint8_t v___x_1732_; 
v___f_1731_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
lean_inc(v_data_1715_);
v___x_1732_ = l_Lean_MessageData_hasTag(v___f_1731_, v_data_1715_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1733_; 
lean_dec(v_endPos_1713_);
lean_del_object(v___x_1704_);
v___x_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1733_, 0, v_fst_1706_);
lean_ctor_set(v___x_1733_, 1, v_snd_1707_);
v_a_1718_ = v___x_1733_;
goto v___jp_1717_;
}
else
{
if (lean_obj_tag(v_endPos_1713_) == 1)
{
lean_object* v_val_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1846_; 
v_val_1734_ = lean_ctor_get(v_endPos_1713_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v_endPos_1713_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1736_ = v_endPos_1713_;
v_isShared_1737_ = v_isSharedCheck_1846_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_val_1734_);
lean_dec(v_endPos_1713_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1846_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; uint8_t v___x_1741_; uint8_t v___x_1742_; 
lean_inc_ref(v_pos_1712_);
v___x_1738_ = l_Lean_FileMap_ofPosition(v___x_1688_, v_pos_1712_);
v___x_1739_ = l_Lean_FileMap_ofPosition(v___x_1688_, v_val_1734_);
lean_inc(v___x_1739_);
lean_inc(v___x_1738_);
v___x_1740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1738_);
lean_ctor_set(v___x_1740_, 1, v___x_1739_);
v___x_1741_ = 0;
v___x_1742_ = l_Lean_Syntax_Range_includes(v_val_1689_, v___x_1740_, v___x_1741_, v___x_1741_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1743_; 
lean_dec_ref_known(v___x_1740_, 2);
lean_dec(v___x_1739_);
lean_dec(v___x_1738_);
lean_del_object(v___x_1736_);
lean_del_object(v___x_1704_);
v___x_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1743_, 0, v_fst_1706_);
lean_ctor_set(v___x_1743_, 1, v_snd_1707_);
v_a_1718_ = v___x_1743_;
goto v___jp_1717_;
}
else
{
lean_object* v___x_1744_; 
lean_inc(v_cmd_1690_);
lean_inc_ref(v___x_1740_);
v___x_1744_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1740_, v_cmd_1690_);
if (lean_obj_tag(v___x_1744_) == 1)
{
lean_object* v_val_1745_; lean_object* v_fst_1746_; lean_object* v_snd_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1810_; 
lean_dec(v___x_1739_);
lean_dec(v___x_1738_);
lean_del_object(v___x_1736_);
v_val_1745_ = lean_ctor_get(v___x_1744_, 0);
lean_inc(v_val_1745_);
lean_dec_ref_known(v___x_1744_, 1);
v_fst_1746_ = lean_ctor_get(v_val_1745_, 0);
v_snd_1747_ = lean_ctor_get(v_val_1745_, 1);
v_isSharedCheck_1810_ = !lean_is_exclusive(v_val_1745_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1749_ = v_val_1745_;
v_isShared_1750_ = v_isSharedCheck_1810_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_snd_1747_);
lean_inc(v_fst_1746_);
lean_dec(v_val_1745_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1810_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; uint8_t v___y_1808_; lean_object* v___x_1809_; 
v___x_1809_ = l_Lean_Syntax_getPos_x3f(v_fst_1746_, v___x_1741_);
if (lean_obj_tag(v___x_1809_) == 0)
{
v___y_1808_ = v___x_1742_;
goto v___jp_1807_;
}
else
{
lean_dec_ref_known(v___x_1809_, 1);
v___y_1808_ = v___x_1741_;
goto v___jp_1807_;
}
v___jp_1751_:
{
lean_object* v___x_1757_; 
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 1, v_snd_1707_);
lean_ctor_set(v___x_1749_, 0, v_fst_1706_);
v___x_1757_ = v___x_1749_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_fst_1706_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_snd_1707_);
v___x_1757_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
size_t v_sz_1758_; size_t v___x_1759_; lean_object* v___x_1760_; 
v_sz_1758_ = lean_array_size(v___y_1752_);
v___x_1759_ = ((size_t)0ULL);
v___x_1760_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1740_, v_fst_1746_, v_snd_1747_, v___y_1753_, v___y_1752_, v_sz_1758_, v___x_1759_, v___x_1757_);
lean_dec_ref(v___y_1752_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; lean_object* v_fst_1762_; lean_object* v_snd_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_a_1761_);
lean_dec_ref_known(v___x_1760_, 1);
v_fst_1762_ = lean_ctor_get(v_a_1761_, 0);
v_snd_1763_ = lean_ctor_get(v_a_1761_, 1);
v_isSharedCheck_1770_ = !lean_is_exclusive(v_a_1761_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v_a_1761_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_snd_1763_);
lean_inc(v_fst_1762_);
lean_dec(v_a_1761_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_fst_1762_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_snd_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
v_a_1718_ = v___x_1768_;
goto v___jp_1717_;
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_del_object(v___x_1709_);
lean_dec(v_cmd_1690_);
v_a_1771_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1760_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1760_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
}
v___jp_1780_:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
lean_inc_ref(v___x_1740_);
v___x_1781_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1740_);
v___x_1782_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1715_);
v___x_1783_ = lean_array_get_size(v___x_1782_);
v___x_1784_ = lean_unsigned_to_nat(0u);
v___x_1785_ = lean_nat_dec_eq(v___x_1783_, v___x_1784_);
if (v___x_1785_ == 0)
{
v___y_1752_ = v___x_1782_;
v___y_1753_ = v___x_1781_;
v___y_1754_ = v___y_1697_;
v___y_1755_ = v___y_1698_;
goto v___jp_1751_;
}
else
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v_scopes_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v_opts_1792_; uint8_t v_hasTrace_1793_; 
v___x_1786_ = l_Lean_inheritedTraceOptions;
v___x_1787_ = lean_st_ref_get(v___x_1786_);
v___x_1788_ = lean_st_ref_get(v___y_1698_);
v_scopes_1789_ = lean_ctor_get(v___x_1788_, 2);
lean_inc(v_scopes_1789_);
lean_dec(v___x_1788_);
v___x_1790_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1791_ = l_List_head_x21___redArg(v___x_1790_, v_scopes_1789_);
lean_dec(v_scopes_1789_);
v_opts_1792_ = lean_ctor_get(v___x_1791_, 1);
lean_inc_ref(v_opts_1792_);
lean_dec(v___x_1791_);
v_hasTrace_1793_ = lean_ctor_get_uint8(v_opts_1792_, sizeof(void*)*1);
if (v_hasTrace_1793_ == 0)
{
lean_dec_ref(v_opts_1792_);
lean_dec(v___x_1787_);
v___y_1752_ = v___x_1782_;
v___y_1753_ = v___x_1781_;
v___y_1754_ = v___y_1697_;
v___y_1755_ = v___y_1698_;
goto v___jp_1751_;
}
else
{
lean_object* v___x_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1794_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1795_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1796_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1787_, v_opts_1792_, v___x_1795_);
lean_dec_ref(v_opts_1792_);
lean_dec(v___x_1787_);
if (v___x_1796_ == 0)
{
v___y_1752_ = v___x_1782_;
v___y_1753_ = v___x_1781_;
v___y_1754_ = v___y_1697_;
v___y_1755_ = v___y_1698_;
goto v___jp_1751_;
}
else
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5);
v___x_1798_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1794_, v___x_1797_, v___y_1697_, v___y_1698_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_dec_ref_known(v___x_1798_, 1);
v___y_1752_ = v___x_1782_;
v___y_1753_ = v___x_1781_;
v___y_1754_ = v___y_1697_;
v___y_1755_ = v___y_1698_;
goto v___jp_1751_;
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
lean_dec_ref(v___x_1782_);
lean_dec(v___x_1781_);
lean_del_object(v___x_1749_);
lean_dec(v_snd_1747_);
lean_dec(v_fst_1746_);
lean_dec_ref_known(v___x_1740_, 2);
lean_del_object(v___x_1709_);
lean_dec(v_snd_1707_);
lean_dec(v_fst_1706_);
lean_dec(v_cmd_1690_);
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1798_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1798_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
}
}
}
v___jp_1807_:
{
if (v_onUnsolved_1691_ == 0)
{
if (v___y_1692_ == 0)
{
lean_del_object(v___x_1749_);
lean_dec(v_snd_1747_);
lean_dec(v_fst_1746_);
lean_dec_ref_known(v___x_1740_, 2);
goto v___jp_1725_;
}
else
{
if (v___y_1808_ == 0)
{
lean_del_object(v___x_1749_);
lean_dec(v_snd_1747_);
lean_dec(v_fst_1746_);
lean_dec_ref_known(v___x_1740_, 2);
goto v___jp_1725_;
}
else
{
lean_del_object(v___x_1704_);
goto v___jp_1780_;
}
}
}
else
{
lean_del_object(v___x_1704_);
goto v___jp_1780_;
}
}
}
}
else
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v_scopes_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v_opts_1817_; uint8_t v_hasTrace_1818_; 
lean_dec(v___x_1744_);
lean_dec_ref_known(v___x_1740_, 2);
lean_del_object(v___x_1704_);
v___x_1811_ = l_Lean_inheritedTraceOptions;
v___x_1812_ = lean_st_ref_get(v___x_1811_);
v___x_1813_ = lean_st_ref_get(v___y_1698_);
v_scopes_1814_ = lean_ctor_get(v___x_1813_, 2);
lean_inc(v_scopes_1814_);
lean_dec(v___x_1813_);
v___x_1815_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1816_ = l_List_head_x21___redArg(v___x_1815_, v_scopes_1814_);
lean_dec(v_scopes_1814_);
v_opts_1817_ = lean_ctor_get(v___x_1816_, 1);
lean_inc_ref(v_opts_1817_);
lean_dec(v___x_1816_);
v_hasTrace_1818_ = lean_ctor_get_uint8(v_opts_1817_, sizeof(void*)*1);
if (v_hasTrace_1818_ == 0)
{
lean_dec_ref(v_opts_1817_);
lean_dec(v___x_1812_);
lean_dec(v___x_1739_);
lean_dec(v___x_1738_);
lean_del_object(v___x_1736_);
goto v___jp_1729_;
}
else
{
lean_object* v___x_1819_; lean_object* v___x_1820_; uint8_t v___x_1821_; 
v___x_1819_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1820_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1821_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1812_, v_opts_1817_, v___x_1820_);
lean_dec_ref(v_opts_1817_);
lean_dec(v___x_1812_);
if (v___x_1821_ == 0)
{
lean_dec(v___x_1739_);
lean_dec(v___x_1738_);
lean_del_object(v___x_1736_);
goto v___jp_1729_;
}
else
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1825_; 
v___x_1822_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7);
v___x_1823_ = l_Nat_reprFast(v___x_1738_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set_tag(v___x_1736_, 3);
lean_ctor_set(v___x_1736_, 0, v___x_1823_);
v___x_1825_ = v___x_1736_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1826_ = l_Lean_MessageData_ofFormat(v___x_1825_);
v___x_1827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1822_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
v___x_1828_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9);
v___x_1829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1827_);
lean_ctor_set(v___x_1829_, 1, v___x_1828_);
v___x_1830_ = l_Nat_reprFast(v___x_1739_);
v___x_1831_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
v___x_1832_ = l_Lean_MessageData_ofFormat(v___x_1831_);
v___x_1833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1829_);
lean_ctor_set(v___x_1833_, 1, v___x_1832_);
v___x_1834_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11);
v___x_1835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1833_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___x_1836_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1819_, v___x_1835_, v___y_1697_, v___y_1698_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_dec_ref_known(v___x_1836_, 1);
goto v___jp_1729_;
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1844_; 
lean_del_object(v___x_1709_);
lean_dec(v_snd_1707_);
lean_dec(v_fst_1706_);
lean_dec(v_cmd_1690_);
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1837_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
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
lean_object* v___x_1847_; 
lean_dec(v_endPos_1713_);
lean_del_object(v___x_1704_);
v___x_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1847_, 0, v_fst_1706_);
lean_ctor_set(v___x_1847_, 1, v_snd_1707_);
v_a_1718_ = v___x_1847_;
goto v___jp_1717_;
}
}
}
else
{
lean_object* v___x_1848_; 
lean_dec(v_endPos_1713_);
lean_del_object(v___x_1704_);
v___x_1848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1848_, 0, v_fst_1706_);
lean_ctor_set(v___x_1848_, 1, v_snd_1707_);
v_a_1718_ = v___x_1848_;
goto v___jp_1717_;
}
v___jp_1717_:
{
lean_object* v___x_1720_; 
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 1, v_a_1718_);
lean_ctor_set(v___x_1709_, 0, v___x_1716_);
v___x_1720_ = v___x_1709_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1716_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v_a_1718_);
v___x_1720_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
size_t v___x_1721_; size_t v___x_1722_; 
v___x_1721_ = ((size_t)1ULL);
v___x_1722_ = lean_usize_add(v_i_1695_, v___x_1721_);
v_i_1695_ = v___x_1722_;
v_b_1696_ = v___x_1720_;
goto _start;
}
}
v___jp_1725_:
{
lean_object* v___x_1727_; 
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 1, v_snd_1707_);
lean_ctor_set(v___x_1704_, 0, v_fst_1706_);
v___x_1727_ = v___x_1704_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_fst_1706_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_snd_1707_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
v_a_1718_ = v___x_1727_;
goto v___jp_1717_;
}
}
v___jp_1729_:
{
lean_object* v___x_1730_; 
v___x_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1730_, 0, v_fst_1706_);
lean_ctor_set(v___x_1730_, 1, v_snd_1707_);
v_a_1718_ = v___x_1730_;
goto v___jp_1717_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10_spec__12___boxed(lean_object* v___x_1852_, lean_object* v_val_1853_, lean_object* v_cmd_1854_, lean_object* v_onUnsolved_1855_, lean_object* v___y_1856_, lean_object* v_as_1857_, lean_object* v_sz_1858_, lean_object* v_i_1859_, lean_object* v_b_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
uint8_t v_onUnsolved_boxed_1864_; uint8_t v___y_12601__boxed_1865_; size_t v_sz_boxed_1866_; size_t v_i_boxed_1867_; lean_object* v_res_1868_; 
v_onUnsolved_boxed_1864_ = lean_unbox(v_onUnsolved_1855_);
v___y_12601__boxed_1865_ = lean_unbox(v___y_1856_);
v_sz_boxed_1866_ = lean_unbox_usize(v_sz_1858_);
lean_dec(v_sz_1858_);
v_i_boxed_1867_ = lean_unbox_usize(v_i_1859_);
lean_dec(v_i_1859_);
v_res_1868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10_spec__12(v___x_1852_, v_val_1853_, v_cmd_1854_, v_onUnsolved_boxed_1864_, v___y_12601__boxed_1865_, v_as_1857_, v_sz_boxed_1866_, v_i_boxed_1867_, v_b_1860_, v___y_1861_, v___y_1862_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec_ref(v_as_1857_);
lean_dec_ref(v_val_1853_);
lean_dec_ref(v___x_1852_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10(lean_object* v___x_1869_, lean_object* v_val_1870_, lean_object* v_cmd_1871_, uint8_t v_onUnsolved_1872_, uint8_t v___y_1873_, lean_object* v_as_1874_, size_t v_sz_1875_, size_t v_i_1876_, lean_object* v_b_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
uint8_t v___x_1881_; 
v___x_1881_ = lean_usize_dec_lt(v_i_1876_, v_sz_1875_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1882_; 
lean_dec(v_cmd_1871_);
v___x_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1882_, 0, v_b_1877_);
return v___x_1882_;
}
else
{
lean_object* v_snd_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_2031_; 
v_snd_1883_ = lean_ctor_get(v_b_1877_, 1);
v_isSharedCheck_2031_ = !lean_is_exclusive(v_b_1877_);
if (v_isSharedCheck_2031_ == 0)
{
lean_object* v_unused_2032_; 
v_unused_2032_ = lean_ctor_get(v_b_1877_, 0);
lean_dec(v_unused_2032_);
v___x_1885_ = v_b_1877_;
v_isShared_1886_ = v_isSharedCheck_2031_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_snd_1883_);
lean_dec(v_b_1877_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_2031_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v_fst_1887_; lean_object* v_snd_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_2030_; 
v_fst_1887_ = lean_ctor_get(v_snd_1883_, 0);
v_snd_1888_ = lean_ctor_get(v_snd_1883_, 1);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_snd_1883_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_1890_ = v_snd_1883_;
v_isShared_1891_ = v_isSharedCheck_2030_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_snd_1888_);
lean_inc(v_fst_1887_);
lean_dec(v_snd_1883_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_2030_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v_a_1892_; lean_object* v_pos_1893_; lean_object* v_endPos_1894_; uint8_t v_severity_1895_; lean_object* v_data_1896_; lean_object* v___x_1897_; lean_object* v_a_1899_; 
v_a_1892_ = lean_array_uget_borrowed(v_as_1874_, v_i_1876_);
v_pos_1893_ = lean_ctor_get(v_a_1892_, 1);
v_endPos_1894_ = lean_ctor_get(v_a_1892_, 2);
lean_inc(v_endPos_1894_);
v_severity_1895_ = lean_ctor_get_uint8(v_a_1892_, sizeof(void*)*5 + 1);
v_data_1896_ = lean_ctor_get(v_a_1892_, 4);
v___x_1897_ = lean_box(0);
if (v_severity_1895_ == 2)
{
lean_object* v___f_1912_; uint8_t v___x_1913_; 
v___f_1912_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
lean_inc(v_data_1896_);
v___x_1913_ = l_Lean_MessageData_hasTag(v___f_1912_, v_data_1896_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; 
lean_dec(v_endPos_1894_);
lean_del_object(v___x_1885_);
v___x_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1914_, 0, v_fst_1887_);
lean_ctor_set(v___x_1914_, 1, v_snd_1888_);
v_a_1899_ = v___x_1914_;
goto v___jp_1898_;
}
else
{
if (lean_obj_tag(v_endPos_1894_) == 1)
{
lean_object* v_val_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_2027_; 
v_val_1915_ = lean_ctor_get(v_endPos_1894_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v_endPos_1894_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_1917_ = v_endPos_1894_;
v_isShared_1918_ = v_isSharedCheck_2027_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_val_1915_);
lean_dec(v_endPos_1894_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_2027_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; uint8_t v___x_1923_; 
lean_inc_ref(v_pos_1893_);
v___x_1919_ = l_Lean_FileMap_ofPosition(v___x_1869_, v_pos_1893_);
v___x_1920_ = l_Lean_FileMap_ofPosition(v___x_1869_, v_val_1915_);
lean_inc(v___x_1920_);
lean_inc(v___x_1919_);
v___x_1921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1919_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = 0;
v___x_1923_ = l_Lean_Syntax_Range_includes(v_val_1870_, v___x_1921_, v___x_1922_, v___x_1922_);
if (v___x_1923_ == 0)
{
lean_object* v___x_1924_; 
lean_dec_ref_known(v___x_1921_, 2);
lean_dec(v___x_1920_);
lean_dec(v___x_1919_);
lean_del_object(v___x_1917_);
lean_del_object(v___x_1885_);
v___x_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1924_, 0, v_fst_1887_);
lean_ctor_set(v___x_1924_, 1, v_snd_1888_);
v_a_1899_ = v___x_1924_;
goto v___jp_1898_;
}
else
{
lean_object* v___x_1925_; 
lean_inc(v_cmd_1871_);
lean_inc_ref(v___x_1921_);
v___x_1925_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1921_, v_cmd_1871_);
if (lean_obj_tag(v___x_1925_) == 1)
{
lean_object* v_val_1926_; lean_object* v_fst_1927_; lean_object* v_snd_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1991_; 
lean_dec(v___x_1920_);
lean_dec(v___x_1919_);
lean_del_object(v___x_1917_);
v_val_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_val_1926_);
lean_dec_ref_known(v___x_1925_, 1);
v_fst_1927_ = lean_ctor_get(v_val_1926_, 0);
v_snd_1928_ = lean_ctor_get(v_val_1926_, 1);
v_isSharedCheck_1991_ = !lean_is_exclusive(v_val_1926_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1930_ = v_val_1926_;
v_isShared_1931_ = v_isSharedCheck_1991_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_snd_1928_);
lean_inc(v_fst_1927_);
lean_dec(v_val_1926_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1991_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; uint8_t v___y_1989_; lean_object* v___x_1990_; 
v___x_1990_ = l_Lean_Syntax_getPos_x3f(v_fst_1927_, v___x_1922_);
if (lean_obj_tag(v___x_1990_) == 0)
{
v___y_1989_ = v___x_1923_;
goto v___jp_1988_;
}
else
{
lean_dec_ref_known(v___x_1990_, 1);
v___y_1989_ = v___x_1922_;
goto v___jp_1988_;
}
v___jp_1932_:
{
lean_object* v___x_1938_; 
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 1, v_snd_1888_);
lean_ctor_set(v___x_1930_, 0, v_fst_1887_);
v___x_1938_ = v___x_1930_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_fst_1887_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v_snd_1888_);
v___x_1938_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
size_t v_sz_1939_; size_t v___x_1940_; lean_object* v___x_1941_; 
v_sz_1939_ = lean_array_size(v___y_1933_);
v___x_1940_ = ((size_t)0ULL);
v___x_1941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1921_, v_fst_1927_, v_snd_1928_, v___y_1934_, v___y_1933_, v_sz_1939_, v___x_1940_, v___x_1938_);
lean_dec_ref(v___y_1933_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; lean_object* v_fst_1943_; lean_object* v_snd_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1942_);
lean_dec_ref_known(v___x_1941_, 1);
v_fst_1943_ = lean_ctor_get(v_a_1942_, 0);
v_snd_1944_ = lean_ctor_get(v_a_1942_, 1);
v_isSharedCheck_1951_ = !lean_is_exclusive(v_a_1942_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v_a_1942_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_snd_1944_);
lean_inc(v_fst_1943_);
lean_dec(v_a_1942_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_fst_1943_);
lean_ctor_set(v_reuseFailAlloc_1950_, 1, v_snd_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
v_a_1899_ = v___x_1949_;
goto v___jp_1898_;
}
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_del_object(v___x_1890_);
lean_dec(v_cmd_1871_);
v_a_1952_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1941_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1941_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
v___jp_1961_:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; uint8_t v___x_1966_; 
lean_inc_ref(v___x_1921_);
v___x_1962_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1921_);
v___x_1963_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1896_);
v___x_1964_ = lean_array_get_size(v___x_1963_);
v___x_1965_ = lean_unsigned_to_nat(0u);
v___x_1966_ = lean_nat_dec_eq(v___x_1964_, v___x_1965_);
if (v___x_1966_ == 0)
{
v___y_1933_ = v___x_1963_;
v___y_1934_ = v___x_1962_;
v___y_1935_ = v___y_1878_;
v___y_1936_ = v___y_1879_;
goto v___jp_1932_;
}
else
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v_scopes_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v_opts_1973_; uint8_t v_hasTrace_1974_; 
v___x_1967_ = l_Lean_inheritedTraceOptions;
v___x_1968_ = lean_st_ref_get(v___x_1967_);
v___x_1969_ = lean_st_ref_get(v___y_1879_);
v_scopes_1970_ = lean_ctor_get(v___x_1969_, 2);
lean_inc(v_scopes_1970_);
lean_dec(v___x_1969_);
v___x_1971_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1972_ = l_List_head_x21___redArg(v___x_1971_, v_scopes_1970_);
lean_dec(v_scopes_1970_);
v_opts_1973_ = lean_ctor_get(v___x_1972_, 1);
lean_inc_ref(v_opts_1973_);
lean_dec(v___x_1972_);
v_hasTrace_1974_ = lean_ctor_get_uint8(v_opts_1973_, sizeof(void*)*1);
if (v_hasTrace_1974_ == 0)
{
lean_dec_ref(v_opts_1973_);
lean_dec(v___x_1968_);
v___y_1933_ = v___x_1963_;
v___y_1934_ = v___x_1962_;
v___y_1935_ = v___y_1878_;
v___y_1936_ = v___y_1879_;
goto v___jp_1932_;
}
else
{
lean_object* v___x_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; 
v___x_1975_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1976_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1977_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1968_, v_opts_1973_, v___x_1976_);
lean_dec_ref(v_opts_1973_);
lean_dec(v___x_1968_);
if (v___x_1977_ == 0)
{
v___y_1933_ = v___x_1963_;
v___y_1934_ = v___x_1962_;
v___y_1935_ = v___y_1878_;
v___y_1936_ = v___y_1879_;
goto v___jp_1932_;
}
else
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5);
v___x_1979_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1975_, v___x_1978_, v___y_1878_, v___y_1879_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_dec_ref_known(v___x_1979_, 1);
v___y_1933_ = v___x_1963_;
v___y_1934_ = v___x_1962_;
v___y_1935_ = v___y_1878_;
v___y_1936_ = v___y_1879_;
goto v___jp_1932_;
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec_ref(v___x_1963_);
lean_dec(v___x_1962_);
lean_del_object(v___x_1930_);
lean_dec(v_snd_1928_);
lean_dec(v_fst_1927_);
lean_dec_ref_known(v___x_1921_, 2);
lean_del_object(v___x_1890_);
lean_dec(v_snd_1888_);
lean_dec(v_fst_1887_);
lean_dec(v_cmd_1871_);
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
}
}
}
v___jp_1988_:
{
if (v_onUnsolved_1872_ == 0)
{
if (v___y_1873_ == 0)
{
lean_del_object(v___x_1930_);
lean_dec(v_snd_1928_);
lean_dec(v_fst_1927_);
lean_dec_ref_known(v___x_1921_, 2);
goto v___jp_1906_;
}
else
{
if (v___y_1989_ == 0)
{
lean_del_object(v___x_1930_);
lean_dec(v_snd_1928_);
lean_dec(v_fst_1927_);
lean_dec_ref_known(v___x_1921_, 2);
goto v___jp_1906_;
}
else
{
lean_del_object(v___x_1885_);
goto v___jp_1961_;
}
}
}
else
{
lean_del_object(v___x_1885_);
goto v___jp_1961_;
}
}
}
}
else
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v_scopes_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v_opts_1998_; uint8_t v_hasTrace_1999_; 
lean_dec(v___x_1925_);
lean_dec_ref_known(v___x_1921_, 2);
lean_del_object(v___x_1885_);
v___x_1992_ = l_Lean_inheritedTraceOptions;
v___x_1993_ = lean_st_ref_get(v___x_1992_);
v___x_1994_ = lean_st_ref_get(v___y_1879_);
v_scopes_1995_ = lean_ctor_get(v___x_1994_, 2);
lean_inc(v_scopes_1995_);
lean_dec(v___x_1994_);
v___x_1996_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1997_ = l_List_head_x21___redArg(v___x_1996_, v_scopes_1995_);
lean_dec(v_scopes_1995_);
v_opts_1998_ = lean_ctor_get(v___x_1997_, 1);
lean_inc_ref(v_opts_1998_);
lean_dec(v___x_1997_);
v_hasTrace_1999_ = lean_ctor_get_uint8(v_opts_1998_, sizeof(void*)*1);
if (v_hasTrace_1999_ == 0)
{
lean_dec_ref(v_opts_1998_);
lean_dec(v___x_1993_);
lean_dec(v___x_1920_);
lean_dec(v___x_1919_);
lean_del_object(v___x_1917_);
goto v___jp_1910_;
}
else
{
lean_object* v___x_2000_; lean_object* v___x_2001_; uint8_t v___x_2002_; 
v___x_2000_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2001_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_2002_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1993_, v_opts_1998_, v___x_2001_);
lean_dec_ref(v_opts_1998_);
lean_dec(v___x_1993_);
if (v___x_2002_ == 0)
{
lean_dec(v___x_1920_);
lean_dec(v___x_1919_);
lean_del_object(v___x_1917_);
goto v___jp_1910_;
}
else
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2006_; 
v___x_2003_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7);
v___x_2004_ = l_Nat_reprFast(v___x_1919_);
if (v_isShared_1918_ == 0)
{
lean_ctor_set_tag(v___x_1917_, 3);
lean_ctor_set(v___x_1917_, 0, v___x_2004_);
v___x_2006_ = v___x_1917_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2007_ = l_Lean_MessageData_ofFormat(v___x_2006_);
v___x_2008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2003_);
lean_ctor_set(v___x_2008_, 1, v___x_2007_);
v___x_2009_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9);
v___x_2010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2008_);
lean_ctor_set(v___x_2010_, 1, v___x_2009_);
v___x_2011_ = l_Nat_reprFast(v___x_1920_);
v___x_2012_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2011_);
v___x_2013_ = l_Lean_MessageData_ofFormat(v___x_2012_);
v___x_2014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2010_);
lean_ctor_set(v___x_2014_, 1, v___x_2013_);
v___x_2015_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11);
v___x_2016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2014_);
lean_ctor_set(v___x_2016_, 1, v___x_2015_);
v___x_2017_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_2000_, v___x_2016_, v___y_1878_, v___y_1879_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_dec_ref_known(v___x_2017_, 1);
goto v___jp_1910_;
}
else
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
lean_del_object(v___x_1890_);
lean_dec(v_snd_1888_);
lean_dec(v_fst_1887_);
lean_dec(v_cmd_1871_);
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_2017_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_2017_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
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
lean_object* v___x_2028_; 
lean_dec(v_endPos_1894_);
lean_del_object(v___x_1885_);
v___x_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2028_, 0, v_fst_1887_);
lean_ctor_set(v___x_2028_, 1, v_snd_1888_);
v_a_1899_ = v___x_2028_;
goto v___jp_1898_;
}
}
}
else
{
lean_object* v___x_2029_; 
lean_dec(v_endPos_1894_);
lean_del_object(v___x_1885_);
v___x_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2029_, 0, v_fst_1887_);
lean_ctor_set(v___x_2029_, 1, v_snd_1888_);
v_a_1899_ = v___x_2029_;
goto v___jp_1898_;
}
v___jp_1898_:
{
lean_object* v___x_1901_; 
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 1, v_a_1899_);
lean_ctor_set(v___x_1890_, 0, v___x_1897_);
v___x_1901_ = v___x_1890_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v___x_1897_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v_a_1899_);
v___x_1901_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
size_t v___x_1902_; size_t v___x_1903_; lean_object* v___x_1904_; 
v___x_1902_ = ((size_t)1ULL);
v___x_1903_ = lean_usize_add(v_i_1876_, v___x_1902_);
v___x_1904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10_spec__12(v___x_1869_, v_val_1870_, v_cmd_1871_, v_onUnsolved_1872_, v___y_1873_, v_as_1874_, v_sz_1875_, v___x_1903_, v___x_1901_, v___y_1878_, v___y_1879_);
return v___x_1904_;
}
}
v___jp_1906_:
{
lean_object* v___x_1908_; 
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 1, v_snd_1888_);
lean_ctor_set(v___x_1885_, 0, v_fst_1887_);
v___x_1908_ = v___x_1885_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_fst_1887_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v_snd_1888_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
v_a_1899_ = v___x_1908_;
goto v___jp_1898_;
}
}
v___jp_1910_:
{
lean_object* v___x_1911_; 
v___x_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1911_, 0, v_fst_1887_);
lean_ctor_set(v___x_1911_, 1, v_snd_1888_);
v_a_1899_ = v___x_1911_;
goto v___jp_1898_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10___boxed(lean_object* v___x_2033_, lean_object* v_val_2034_, lean_object* v_cmd_2035_, lean_object* v_onUnsolved_2036_, lean_object* v___y_2037_, lean_object* v_as_2038_, lean_object* v_sz_2039_, lean_object* v_i_2040_, lean_object* v_b_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
uint8_t v_onUnsolved_boxed_2045_; uint8_t v___y_12933__boxed_2046_; size_t v_sz_boxed_2047_; size_t v_i_boxed_2048_; lean_object* v_res_2049_; 
v_onUnsolved_boxed_2045_ = lean_unbox(v_onUnsolved_2036_);
v___y_12933__boxed_2046_ = lean_unbox(v___y_2037_);
v_sz_boxed_2047_ = lean_unbox_usize(v_sz_2039_);
lean_dec(v_sz_2039_);
v_i_boxed_2048_ = lean_unbox_usize(v_i_2040_);
lean_dec(v_i_2040_);
v_res_2049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10(v___x_2033_, v_val_2034_, v_cmd_2035_, v_onUnsolved_boxed_2045_, v___y_12933__boxed_2046_, v_as_2038_, v_sz_boxed_2047_, v_i_boxed_2048_, v_b_2041_, v___y_2042_, v___y_2043_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec_ref(v_as_2038_);
lean_dec_ref(v_val_2034_);
lean_dec_ref(v___x_2033_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(lean_object* v_init_2050_, lean_object* v___x_2051_, lean_object* v_val_2052_, lean_object* v_cmd_2053_, uint8_t v_onUnsolved_2054_, uint8_t v___y_2055_, lean_object* v_n_2056_, lean_object* v_b_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
if (lean_obj_tag(v_n_2056_) == 0)
{
lean_object* v_cs_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; size_t v_sz_2064_; size_t v___x_2065_; lean_object* v___x_2066_; 
v_cs_2061_ = lean_ctor_get(v_n_2056_, 0);
v___x_2062_ = lean_box(0);
v___x_2063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
lean_ctor_set(v___x_2063_, 1, v_b_2057_);
v_sz_2064_ = lean_array_size(v_cs_2061_);
v___x_2065_ = ((size_t)0ULL);
v___x_2066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__9(v_init_2050_, v___x_2051_, v_val_2052_, v_cmd_2053_, v_onUnsolved_2054_, v___y_2055_, v_cs_2061_, v_sz_2064_, v___x_2065_, v___x_2063_, v___y_2058_, v___y_2059_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2081_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2069_ = v___x_2066_;
v_isShared_2070_ = v_isSharedCheck_2081_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2081_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v_fst_2071_; 
v_fst_2071_ = lean_ctor_get(v_a_2067_, 0);
if (lean_obj_tag(v_fst_2071_) == 0)
{
lean_object* v_snd_2072_; lean_object* v___x_2073_; lean_object* v___x_2075_; 
v_snd_2072_ = lean_ctor_get(v_a_2067_, 1);
lean_inc(v_snd_2072_);
lean_dec(v_a_2067_);
v___x_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2073_, 0, v_snd_2072_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2073_);
v___x_2075_ = v___x_2069_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2073_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
else
{
lean_object* v_val_2077_; lean_object* v___x_2079_; 
lean_inc_ref(v_fst_2071_);
lean_dec(v_a_2067_);
v_val_2077_ = lean_ctor_get(v_fst_2071_, 0);
lean_inc(v_val_2077_);
lean_dec_ref_known(v_fst_2071_, 1);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v_val_2077_);
v___x_2079_ = v___x_2069_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_val_2077_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
v_a_2082_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2066_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2066_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
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
lean_object* v_vs_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; size_t v_sz_2093_; size_t v___x_2094_; lean_object* v___x_2095_; 
v_vs_2090_ = lean_ctor_get(v_n_2056_, 0);
v___x_2091_ = lean_box(0);
v___x_2092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
lean_ctor_set(v___x_2092_, 1, v_b_2057_);
v_sz_2093_ = lean_array_size(v_vs_2090_);
v___x_2094_ = ((size_t)0ULL);
v___x_2095_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10(v___x_2051_, v_val_2052_, v_cmd_2053_, v_onUnsolved_2054_, v___y_2055_, v_vs_2090_, v_sz_2093_, v___x_2094_, v___x_2092_, v___y_2058_, v___y_2059_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2110_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2098_ = v___x_2095_;
v_isShared_2099_ = v_isSharedCheck_2110_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2095_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2110_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v_fst_2100_; 
v_fst_2100_ = lean_ctor_get(v_a_2096_, 0);
if (lean_obj_tag(v_fst_2100_) == 0)
{
lean_object* v_snd_2101_; lean_object* v___x_2102_; lean_object* v___x_2104_; 
v_snd_2101_ = lean_ctor_get(v_a_2096_, 1);
lean_inc(v_snd_2101_);
lean_dec(v_a_2096_);
v___x_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2102_, 0, v_snd_2101_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 0, v___x_2102_);
v___x_2104_ = v___x_2098_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2102_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
else
{
lean_object* v_val_2106_; lean_object* v___x_2108_; 
lean_inc_ref(v_fst_2100_);
lean_dec(v_a_2096_);
v_val_2106_ = lean_ctor_get(v_fst_2100_, 0);
lean_inc(v_val_2106_);
lean_dec_ref_known(v_fst_2100_, 1);
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 0, v_val_2106_);
v___x_2108_ = v___x_2098_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_val_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
v_a_2111_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2095_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2095_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__9(lean_object* v_init_2119_, lean_object* v___x_2120_, lean_object* v_val_2121_, lean_object* v_cmd_2122_, uint8_t v_onUnsolved_2123_, uint8_t v___y_2124_, lean_object* v_as_2125_, size_t v_sz_2126_, size_t v_i_2127_, lean_object* v_b_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
uint8_t v___x_2132_; 
v___x_2132_ = lean_usize_dec_lt(v_i_2127_, v_sz_2126_);
if (v___x_2132_ == 0)
{
lean_object* v___x_2133_; 
lean_dec(v_cmd_2122_);
v___x_2133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2133_, 0, v_b_2128_);
return v___x_2133_;
}
else
{
lean_object* v_snd_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2168_; 
v_snd_2134_ = lean_ctor_get(v_b_2128_, 1);
v_isSharedCheck_2168_ = !lean_is_exclusive(v_b_2128_);
if (v_isSharedCheck_2168_ == 0)
{
lean_object* v_unused_2169_; 
v_unused_2169_ = lean_ctor_get(v_b_2128_, 0);
lean_dec(v_unused_2169_);
v___x_2136_ = v_b_2128_;
v_isShared_2137_ = v_isSharedCheck_2168_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_snd_2134_);
lean_dec(v_b_2128_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2168_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v_a_2138_; lean_object* v___x_2139_; 
v_a_2138_ = lean_array_uget_borrowed(v_as_2125_, v_i_2127_);
lean_inc(v_snd_2134_);
lean_inc(v_cmd_2122_);
v___x_2139_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(v_init_2119_, v___x_2120_, v_val_2121_, v_cmd_2122_, v_onUnsolved_2123_, v___y_2124_, v_a_2138_, v_snd_2134_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2159_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2142_ = v___x_2139_;
v_isShared_2143_ = v_isSharedCheck_2159_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2139_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2159_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
if (lean_obj_tag(v_a_2140_) == 0)
{
lean_object* v___x_2144_; lean_object* v___x_2146_; 
lean_dec(v_cmd_2122_);
v___x_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2144_, 0, v_a_2140_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 0, v___x_2144_);
v___x_2146_ = v___x_2136_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2144_);
lean_ctor_set(v_reuseFailAlloc_2150_, 1, v_snd_2134_);
v___x_2146_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
lean_object* v___x_2148_; 
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 0, v___x_2146_);
v___x_2148_ = v___x_2142_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2146_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2152_; lean_object* v___x_2154_; 
lean_del_object(v___x_2142_);
lean_dec(v_snd_2134_);
v_a_2151_ = lean_ctor_get(v_a_2140_, 0);
lean_inc(v_a_2151_);
lean_dec_ref_known(v_a_2140_, 1);
v___x_2152_ = lean_box(0);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 1, v_a_2151_);
lean_ctor_set(v___x_2136_, 0, v___x_2152_);
v___x_2154_ = v___x_2136_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v_a_2151_);
v___x_2154_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
size_t v___x_2155_; size_t v___x_2156_; 
v___x_2155_ = ((size_t)1ULL);
v___x_2156_ = lean_usize_add(v_i_2127_, v___x_2155_);
v_i_2127_ = v___x_2156_;
v_b_2128_ = v___x_2154_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_del_object(v___x_2136_);
lean_dec(v_snd_2134_);
lean_dec(v_cmd_2122_);
v_a_2160_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2139_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2139_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__9___boxed(lean_object* v_init_2170_, lean_object* v___x_2171_, lean_object* v_val_2172_, lean_object* v_cmd_2173_, lean_object* v_onUnsolved_2174_, lean_object* v___y_2175_, lean_object* v_as_2176_, lean_object* v_sz_2177_, lean_object* v_i_2178_, lean_object* v_b_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
uint8_t v_onUnsolved_boxed_2183_; uint8_t v___y_13234__boxed_2184_; size_t v_sz_boxed_2185_; size_t v_i_boxed_2186_; lean_object* v_res_2187_; 
v_onUnsolved_boxed_2183_ = lean_unbox(v_onUnsolved_2174_);
v___y_13234__boxed_2184_ = lean_unbox(v___y_2175_);
v_sz_boxed_2185_ = lean_unbox_usize(v_sz_2177_);
lean_dec(v_sz_2177_);
v_i_boxed_2186_ = lean_unbox_usize(v_i_2178_);
lean_dec(v_i_2178_);
v_res_2187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__9(v_init_2170_, v___x_2171_, v_val_2172_, v_cmd_2173_, v_onUnsolved_boxed_2183_, v___y_13234__boxed_2184_, v_as_2176_, v_sz_boxed_2185_, v_i_boxed_2186_, v_b_2179_, v___y_2180_, v___y_2181_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec_ref(v_as_2176_);
lean_dec_ref(v_val_2172_);
lean_dec_ref(v___x_2171_);
lean_dec_ref(v_init_2170_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___boxed(lean_object* v_init_2188_, lean_object* v___x_2189_, lean_object* v_val_2190_, lean_object* v_cmd_2191_, lean_object* v_onUnsolved_2192_, lean_object* v___y_2193_, lean_object* v_n_2194_, lean_object* v_b_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
uint8_t v_onUnsolved_boxed_2199_; uint8_t v___y_13256__boxed_2200_; lean_object* v_res_2201_; 
v_onUnsolved_boxed_2199_ = lean_unbox(v_onUnsolved_2192_);
v___y_13256__boxed_2200_ = lean_unbox(v___y_2193_);
v_res_2201_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(v_init_2188_, v___x_2189_, v_val_2190_, v_cmd_2191_, v_onUnsolved_boxed_2199_, v___y_13256__boxed_2200_, v_n_2194_, v_b_2195_, v___y_2196_, v___y_2197_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec_ref(v_n_2194_);
lean_dec_ref(v_val_2190_);
lean_dec_ref(v___x_2189_);
lean_dec_ref(v_init_2188_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(lean_object* v___x_2202_, lean_object* v_val_2203_, lean_object* v_cmd_2204_, uint8_t v_onUnsolved_2205_, uint8_t v___y_2206_, lean_object* v_t_2207_, lean_object* v_init_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_root_2212_; lean_object* v_tail_2213_; lean_object* v___x_2214_; 
v_root_2212_ = lean_ctor_get(v_t_2207_, 0);
v_tail_2213_ = lean_ctor_get(v_t_2207_, 1);
lean_inc(v_cmd_2204_);
lean_inc_ref(v_init_2208_);
v___x_2214_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(v_init_2208_, v___x_2202_, v_val_2203_, v_cmd_2204_, v_onUnsolved_2205_, v___y_2206_, v_root_2212_, v_init_2208_, v___y_2209_, v___y_2210_);
lean_dec_ref(v_init_2208_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2251_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2217_ = v___x_2214_;
v_isShared_2218_ = v_isSharedCheck_2251_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2214_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2251_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
if (lean_obj_tag(v_a_2215_) == 0)
{
lean_object* v_a_2219_; lean_object* v___x_2221_; 
lean_dec(v_cmd_2204_);
v_a_2219_ = lean_ctor_get(v_a_2215_, 0);
lean_inc(v_a_2219_);
lean_dec_ref_known(v_a_2215_, 1);
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 0, v_a_2219_);
v___x_2221_ = v___x_2217_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2219_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; size_t v_sz_2226_; size_t v___x_2227_; lean_object* v___x_2228_; 
lean_del_object(v___x_2217_);
v_a_2223_ = lean_ctor_get(v_a_2215_, 0);
lean_inc(v_a_2223_);
lean_dec_ref_known(v_a_2215_, 1);
v___x_2224_ = lean_box(0);
v___x_2225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2224_);
lean_ctor_set(v___x_2225_, 1, v_a_2223_);
v_sz_2226_ = lean_array_size(v_tail_2213_);
v___x_2227_ = ((size_t)0ULL);
v___x_2228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8(v___x_2202_, v_val_2203_, v_cmd_2204_, v_onUnsolved_2205_, v___y_2206_, v_tail_2213_, v_sz_2226_, v___x_2227_, v___x_2225_, v___y_2209_, v___y_2210_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2242_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2231_ = v___x_2228_;
v_isShared_2232_ = v_isSharedCheck_2242_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2242_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v_fst_2233_; 
v_fst_2233_ = lean_ctor_get(v_a_2229_, 0);
if (lean_obj_tag(v_fst_2233_) == 0)
{
lean_object* v_snd_2234_; lean_object* v___x_2236_; 
v_snd_2234_ = lean_ctor_get(v_a_2229_, 1);
lean_inc(v_snd_2234_);
lean_dec(v_a_2229_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 0, v_snd_2234_);
v___x_2236_ = v___x_2231_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_snd_2234_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
else
{
lean_object* v_val_2238_; lean_object* v___x_2240_; 
lean_inc_ref(v_fst_2233_);
lean_dec(v_a_2229_);
v_val_2238_ = lean_ctor_get(v_fst_2233_, 0);
lean_inc(v_val_2238_);
lean_dec_ref_known(v_fst_2233_, 1);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 0, v_val_2238_);
v___x_2240_ = v___x_2231_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_val_2238_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
v_a_2243_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2228_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2228_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
}
}
else
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2259_; 
lean_dec(v_cmd_2204_);
v_a_2252_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2254_ = v___x_2214_;
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2214_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2257_; 
if (v_isShared_2255_ == 0)
{
v___x_2257_ = v___x_2254_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2252_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___boxed(lean_object* v___x_2260_, lean_object* v_val_2261_, lean_object* v_cmd_2262_, lean_object* v_onUnsolved_2263_, lean_object* v___y_2264_, lean_object* v_t_2265_, lean_object* v_init_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
uint8_t v_onUnsolved_boxed_2270_; uint8_t v___y_13447__boxed_2271_; lean_object* v_res_2272_; 
v_onUnsolved_boxed_2270_ = lean_unbox(v_onUnsolved_2263_);
v___y_13447__boxed_2271_ = lean_unbox(v___y_2264_);
v_res_2272_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_2260_, v_val_2261_, v_cmd_2262_, v_onUnsolved_boxed_2270_, v___y_13447__boxed_2271_, v_t_2265_, v_init_2266_, v___y_2267_, v___y_2268_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec_ref(v_t_2265_);
lean_dec_ref(v_val_2261_);
lean_dec_ref(v___x_2260_);
return v_res_2272_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0(void){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2273_ = lean_box(0);
v___x_2274_ = lean_unsigned_to_nat(16u);
v___x_2275_ = lean_mk_array(v___x_2274_, v___x_2273_);
return v___x_2275_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1(void){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2276_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0);
v___x_2277_ = lean_unsigned_to_nat(0u);
v___x_2278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
lean_ctor_set(v___x_2278_, 1, v___x_2276_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(lean_object* v_cmd_2282_, lean_object* v_opts_2283_, lean_object* v_tree_2284_, lean_object* v_msgs_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_){
_start:
{
uint8_t v___y_2290_; lean_object* v___y_2291_; uint8_t v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; uint8_t v___y_2295_; uint8_t v___y_2321_; uint8_t v___y_2322_; lean_object* v_acc_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___f_2327_; uint8_t v___y_2329_; lean_object* v___x_2336_; uint8_t v___x_2337_; 
v___f_2327_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__2));
v___x_2336_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_2337_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2283_, v___x_2336_);
if (v___x_2337_ == 0)
{
lean_object* v___x_2338_; uint8_t v___x_2339_; 
v___x_2338_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_2339_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2283_, v___x_2338_);
v___y_2329_ = v___x_2339_;
goto v___jp_2328_;
}
else
{
v___y_2329_ = v___x_2337_;
goto v___jp_2328_;
}
v___jp_2289_:
{
lean_object* v___x_2296_; 
v___x_2296_ = l_Lean_Syntax_getRange_x3f(v_cmd_2282_, v___y_2295_);
if (lean_obj_tag(v___x_2296_) == 1)
{
lean_object* v_val_2297_; lean_object* v_fileMap_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v_val_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_val_2297_);
lean_dec_ref_known(v___x_2296_, 1);
v_fileMap_2298_ = lean_ctor_get(v___y_2294_, 1);
v___x_2299_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1);
v___x_2300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___y_2291_);
lean_ctor_set(v___x_2300_, 1, v___x_2299_);
v___x_2301_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v_fileMap_2298_, v_val_2297_, v_cmd_2282_, v___y_2292_, v___y_2290_, v_msgs_2285_, v___x_2300_, v___y_2294_, v___y_2293_);
lean_dec(v_val_2297_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2310_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2304_ = v___x_2301_;
v_isShared_2305_ = v_isSharedCheck_2310_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2301_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2310_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v_fst_2306_; lean_object* v___x_2308_; 
v_fst_2306_ = lean_ctor_get(v_a_2302_, 0);
lean_inc(v_fst_2306_);
lean_dec(v_a_2302_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v_fst_2306_);
v___x_2308_ = v___x_2304_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_fst_2306_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
v_a_2311_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2301_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2301_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
else
{
lean_object* v___x_2319_; 
lean_dec(v___x_2296_);
lean_dec(v_cmd_2282_);
v___x_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2319_, 0, v___y_2291_);
return v___x_2319_;
}
}
v___jp_2320_:
{
if (v___y_2322_ == 0)
{
if (v___y_2321_ == 0)
{
lean_object* v___x_2326_; 
lean_dec(v_cmd_2282_);
v___x_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2326_, 0, v_acc_2323_);
return v___x_2326_;
}
else
{
v___y_2290_ = v___y_2321_;
v___y_2291_ = v_acc_2323_;
v___y_2292_ = v___y_2322_;
v___y_2293_ = v___y_2325_;
v___y_2294_ = v___y_2324_;
v___y_2295_ = v___y_2321_;
goto v___jp_2289_;
}
}
else
{
v___y_2290_ = v___y_2321_;
v___y_2291_ = v_acc_2323_;
v___y_2292_ = v___y_2322_;
v___y_2293_ = v___y_2325_;
v___y_2294_ = v___y_2324_;
v___y_2295_ = v___y_2322_;
goto v___jp_2289_;
}
}
v___jp_2328_:
{
lean_object* v___x_2330_; uint8_t v_onUnsolved_2331_; lean_object* v___x_2332_; uint8_t v_onSorry_2333_; lean_object* v_acc_2334_; 
v___x_2330_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
v_onUnsolved_2331_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2283_, v___x_2330_);
v___x_2332_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v_onSorry_2333_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2283_, v___x_2332_);
v_acc_2334_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__3));
if (v_onSorry_2333_ == 0)
{
lean_dec_ref(v_tree_2284_);
v___y_2321_ = v___y_2329_;
v___y_2322_ = v_onUnsolved_2331_;
v_acc_2323_ = v_acc_2334_;
v___y_2324_ = v_a_2286_;
v___y_2325_ = v_a_2287_;
goto v___jp_2320_;
}
else
{
lean_object* v_acc_2335_; 
v_acc_2335_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_2327_, v_acc_2334_, v_tree_2284_);
v___y_2321_ = v___y_2329_;
v___y_2322_ = v_onUnsolved_2331_;
v_acc_2323_ = v_acc_2335_;
v___y_2324_ = v_a_2286_;
v___y_2325_ = v_a_2287_;
goto v___jp_2320_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___boxed(lean_object* v_cmd_2340_, lean_object* v_opts_2341_, lean_object* v_tree_2342_, lean_object* v_msgs_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_cmd_2340_, v_opts_2341_, v_tree_2342_, v_msgs_2343_, v_a_2344_, v_a_2345_);
lean_dec(v_a_2345_);
lean_dec_ref(v_a_2344_);
lean_dec_ref(v_msgs_2343_);
lean_dec_ref(v_opts_2341_);
return v_res_2347_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(lean_object* v_00_u03b2_2348_, lean_object* v_m_2349_, lean_object* v_a_2350_){
_start:
{
uint8_t v___x_2351_; 
v___x_2351_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(v_m_2349_, v_a_2350_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___boxed(lean_object* v_00_u03b2_2352_, lean_object* v_m_2353_, lean_object* v_a_2354_){
_start:
{
uint8_t v_res_2355_; lean_object* v_r_2356_; 
v_res_2355_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_00_u03b2_2352_, v_m_2353_, v_a_2354_);
lean_dec_ref(v_a_2354_);
lean_dec_ref(v_m_2353_);
v_r_2356_ = lean_box(v_res_2355_);
return v_r_2356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1(lean_object* v_00_u03b2_2357_, lean_object* v_m_2358_, lean_object* v_a_2359_, lean_object* v_b_2360_){
_start:
{
lean_object* v___x_2361_; 
v___x_2361_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_m_2358_, v_a_2359_, v_b_2360_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2(lean_object* v___x_2362_, lean_object* v_fst_2363_, lean_object* v_snd_2364_, lean_object* v___x_2365_, lean_object* v_as_2366_, size_t v_sz_2367_, size_t v_i_2368_, lean_object* v_b_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v___x_2373_; 
v___x_2373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_2362_, v_fst_2363_, v_snd_2364_, v___x_2365_, v_as_2366_, v_sz_2367_, v_i_2368_, v_b_2369_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___boxed(lean_object* v___x_2374_, lean_object* v_fst_2375_, lean_object* v_snd_2376_, lean_object* v___x_2377_, lean_object* v_as_2378_, lean_object* v_sz_2379_, lean_object* v_i_2380_, lean_object* v_b_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
size_t v_sz_boxed_2385_; size_t v_i_boxed_2386_; lean_object* v_res_2387_; 
v_sz_boxed_2385_ = lean_unbox_usize(v_sz_2379_);
lean_dec(v_sz_2379_);
v_i_boxed_2386_ = lean_unbox_usize(v_i_2380_);
lean_dec(v_i_2380_);
v_res_2387_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2(v___x_2374_, v_fst_2375_, v_snd_2376_, v___x_2377_, v_as_2378_, v_sz_boxed_2385_, v_i_boxed_2386_, v_b_2381_, v___y_2382_, v___y_2383_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec_ref(v_as_2378_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5(lean_object* v_msgData_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v___x_2392_; 
v___x_2392_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(v_msgData_2388_, v___y_2390_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___boxed(lean_object* v_msgData_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5(v_msgData_2393_, v___y_2394_, v___y_2395_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
return v_res_2397_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0(lean_object* v_00_u03b2_2398_, lean_object* v_a_2399_, lean_object* v_x_2400_){
_start:
{
uint8_t v___x_2401_; 
v___x_2401_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(v_a_2399_, v_x_2400_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2402_, lean_object* v_a_2403_, lean_object* v_x_2404_){
_start:
{
uint8_t v_res_2405_; lean_object* v_r_2406_; 
v_res_2405_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0(v_00_u03b2_2402_, v_a_2403_, v_x_2404_);
lean_dec(v_x_2404_);
lean_dec_ref(v_a_2403_);
v_r_2406_ = lean_box(v_res_2405_);
return v_r_2406_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2(lean_object* v_00_u03b2_2407_, lean_object* v_data_2408_){
_start:
{
lean_object* v___x_2409_; 
v___x_2409_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2___redArg(v_data_2408_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2410_, lean_object* v_i_2411_, lean_object* v_source_2412_, lean_object* v_target_2413_){
_start:
{
lean_object* v___x_2414_; 
v___x_2414_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3___redArg(v_i_2411_, v_source_2412_, v_target_2413_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3_spec__8(lean_object* v_00_u03b2_2415_, lean_object* v_x_2416_, lean_object* v_x_2417_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3_spec__8___redArg(v_x_2416_, v_x_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(lean_object* v_x_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v___x_2427_; 
lean_inc(v___y_2421_);
lean_inc_ref(v___y_2420_);
v___x_2427_ = lean_apply_7(v_x_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, lean_box(0));
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed(lean_object* v_x_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(v_x_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(lean_object* v_mvarId_2437_, lean_object* v_x_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v___f_2446_; lean_object* v___x_2447_; 
lean_inc(v___y_2440_);
lean_inc_ref(v___y_2439_);
v___f_2446_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2446_, 0, v_x_2438_);
lean_closure_set(v___f_2446_, 1, v___y_2439_);
lean_closure_set(v___f_2446_, 2, v___y_2440_);
v___x_2447_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2437_, v___f_2446_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
if (lean_obj_tag(v___x_2447_) == 0)
{
return v___x_2447_;
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v___x_2447_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2447_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___boxed(lean_object* v_mvarId_2456_, lean_object* v_x_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2456_, v_x_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(lean_object* v_00_u03b1_2466_, lean_object* v_mvarId_2467_, lean_object* v_x_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v___x_2476_; 
v___x_2476_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2467_, v_x_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed(lean_object* v_00_u03b1_2477_, lean_object* v_mvarId_2478_, lean_object* v_x_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(v_00_u03b1_2477_, v_mvarId_2478_, v_x_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(lean_object* v_____r_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2502_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___boxed(lean_object* v_____r_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(v_____r_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(lean_object* v_____r_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1___boxed(lean_object* v_____r_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(v_____r_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
return v_res_2529_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(uint8_t v___x_2530_, lean_object* v_x_2531_){
_start:
{
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2___boxed(lean_object* v___x_2532_, lean_object* v_x_2533_){
_start:
{
uint8_t v___x_10973__boxed_2534_; uint8_t v_res_2535_; lean_object* v_r_2536_; 
v___x_10973__boxed_2534_ = lean_unbox(v___x_2532_);
v_res_2535_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(v___x_10973__boxed_2534_, v_x_2533_);
lean_dec(v_x_2533_);
v_r_2536_ = lean_box(v_res_2535_);
return v_r_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(lean_object* v_msgData_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
lean_object* v___x_2543_; lean_object* v_env_2544_; lean_object* v___x_2545_; lean_object* v_toCold_2546_; lean_object* v_mctx_2547_; lean_object* v_lctx_2548_; lean_object* v_options_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2543_ = lean_st_ref_get(v___y_2541_);
v_env_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc_ref(v_env_2544_);
lean_dec(v___x_2543_);
v___x_2545_ = lean_st_ref_get(v___y_2539_);
v_toCold_2546_ = lean_ctor_get(v___y_2540_, 0);
v_mctx_2547_ = lean_ctor_get(v___x_2545_, 0);
lean_inc_ref(v_mctx_2547_);
lean_dec(v___x_2545_);
v_lctx_2548_ = lean_ctor_get(v___y_2538_, 2);
v_options_2549_ = lean_ctor_get(v_toCold_2546_, 2);
lean_inc_ref(v_options_2549_);
lean_inc_ref(v_lctx_2548_);
v___x_2550_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2550_, 0, v_env_2544_);
lean_ctor_set(v___x_2550_, 1, v_mctx_2547_);
lean_ctor_set(v___x_2550_, 2, v_lctx_2548_);
lean_ctor_set(v___x_2550_, 3, v_options_2549_);
v___x_2551_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2550_);
lean_ctor_set(v___x_2551_, 1, v_msgData_2537_);
v___x_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2551_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2___boxed(lean_object* v_msgData_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msgData_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(lean_object* v_cls_2560_, lean_object* v_msg_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v_ref_2567_; lean_object* v___x_2568_; lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2613_; 
v_ref_2567_ = lean_ctor_get(v___y_2564_, 2);
v___x_2568_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2571_ = v___x_2568_;
v_isShared_2572_ = v_isSharedCheck_2613_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2568_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2613_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2573_; lean_object* v_traceState_2574_; lean_object* v_env_2575_; lean_object* v_nextMacroScope_2576_; lean_object* v_ngen_2577_; lean_object* v_auxDeclNGen_2578_; lean_object* v_cache_2579_; lean_object* v_messages_2580_; lean_object* v_infoState_2581_; lean_object* v_snapshotTasks_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2612_; 
v___x_2573_ = lean_st_ref_take(v___y_2565_);
v_traceState_2574_ = lean_ctor_get(v___x_2573_, 4);
v_env_2575_ = lean_ctor_get(v___x_2573_, 0);
v_nextMacroScope_2576_ = lean_ctor_get(v___x_2573_, 1);
v_ngen_2577_ = lean_ctor_get(v___x_2573_, 2);
v_auxDeclNGen_2578_ = lean_ctor_get(v___x_2573_, 3);
v_cache_2579_ = lean_ctor_get(v___x_2573_, 5);
v_messages_2580_ = lean_ctor_get(v___x_2573_, 6);
v_infoState_2581_ = lean_ctor_get(v___x_2573_, 7);
v_snapshotTasks_2582_ = lean_ctor_get(v___x_2573_, 8);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2584_ = v___x_2573_;
v_isShared_2585_ = v_isSharedCheck_2612_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_snapshotTasks_2582_);
lean_inc(v_infoState_2581_);
lean_inc(v_messages_2580_);
lean_inc(v_cache_2579_);
lean_inc(v_traceState_2574_);
lean_inc(v_auxDeclNGen_2578_);
lean_inc(v_ngen_2577_);
lean_inc(v_nextMacroScope_2576_);
lean_inc(v_env_2575_);
lean_dec(v___x_2573_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2612_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
uint64_t v_tid_2586_; lean_object* v_traces_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2611_; 
v_tid_2586_ = lean_ctor_get_uint64(v_traceState_2574_, sizeof(void*)*1);
v_traces_2587_ = lean_ctor_get(v_traceState_2574_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v_traceState_2574_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2589_ = v_traceState_2574_;
v_isShared_2590_ = v_isSharedCheck_2611_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_traces_2587_);
lean_dec(v_traceState_2574_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2611_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2591_; double v___x_2592_; uint8_t v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2601_; 
v___x_2591_ = lean_box(0);
v___x_2592_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0);
v___x_2593_ = 0;
v___x_2594_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2595_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2595_, 0, v_cls_2560_);
lean_ctor_set(v___x_2595_, 1, v___x_2591_);
lean_ctor_set(v___x_2595_, 2, v___x_2594_);
lean_ctor_set_float(v___x_2595_, sizeof(void*)*3, v___x_2592_);
lean_ctor_set_float(v___x_2595_, sizeof(void*)*3 + 8, v___x_2592_);
lean_ctor_set_uint8(v___x_2595_, sizeof(void*)*3 + 16, v___x_2593_);
v___x_2596_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__1));
v___x_2597_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2595_);
lean_ctor_set(v___x_2597_, 1, v_a_2569_);
lean_ctor_set(v___x_2597_, 2, v___x_2596_);
lean_inc(v_ref_2567_);
v___x_2598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2598_, 0, v_ref_2567_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
v___x_2599_ = l_Lean_PersistentArray_push___redArg(v_traces_2587_, v___x_2598_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v___x_2599_);
v___x_2601_ = v___x_2589_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2599_);
lean_ctor_set_uint64(v_reuseFailAlloc_2610_, sizeof(void*)*1, v_tid_2586_);
v___x_2601_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
lean_object* v___x_2603_; 
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 4, v___x_2601_);
v___x_2603_ = v___x_2584_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_env_2575_);
lean_ctor_set(v_reuseFailAlloc_2609_, 1, v_nextMacroScope_2576_);
lean_ctor_set(v_reuseFailAlloc_2609_, 2, v_ngen_2577_);
lean_ctor_set(v_reuseFailAlloc_2609_, 3, v_auxDeclNGen_2578_);
lean_ctor_set(v_reuseFailAlloc_2609_, 4, v___x_2601_);
lean_ctor_set(v_reuseFailAlloc_2609_, 5, v_cache_2579_);
lean_ctor_set(v_reuseFailAlloc_2609_, 6, v_messages_2580_);
lean_ctor_set(v_reuseFailAlloc_2609_, 7, v_infoState_2581_);
lean_ctor_set(v_reuseFailAlloc_2609_, 8, v_snapshotTasks_2582_);
v___x_2603_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2607_; 
v___x_2604_ = lean_st_ref_put(v___y_2565_, v___x_2603_);
v___x_2605_ = lean_box(0);
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 0, v___x_2605_);
v___x_2607_ = v___x_2571_;
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg___boxed(lean_object* v_cls_2614_, lean_object* v_msg_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_2614_, v_msg_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
return v_res_2621_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2623_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__0));
v___x_2624_ = l_Lean_stringToMessageData(v___x_2623_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(lean_object* v___x_2625_, lean_object* v___x_2626_, lean_object* v___x_2627_, lean_object* v___f_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v___x_2636_; lean_object* v_a_2638_; lean_object* v___y_2642_; lean_object* v___x_2656_; 
v___x_2636_ = lean_st_mk_ref(v___x_2625_);
v___x_2656_ = l_Lean_Elab_Tactic_saveState___redArg(v___x_2636_, v___y_2630_, v___y_2632_, v___y_2634_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2658_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___x_2656_, 1);
v___x_2658_ = l_Lean_Elab_Tactic_Try_collectTryCoreSuggestions(v___x_2626_, v___x_2627_, v___x_2636_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; 
lean_dec(v_a_2657_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec_ref(v___f_2628_);
lean_dec_ref(v___x_2627_);
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2659_);
lean_dec_ref_known(v___x_2658_, 1);
v_a_2638_ = v_a_2659_;
goto v___jp_2637_;
}
else
{
lean_object* v_a_2660_; uint8_t v___y_2662_; uint8_t v___x_2706_; 
v_a_2660_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2660_);
v___x_2706_ = l_Lean_Exception_isInterrupt(v_a_2660_);
if (v___x_2706_ == 0)
{
uint8_t v___x_2707_; 
lean_inc(v_a_2660_);
v___x_2707_ = l_Lean_Exception_isRuntime(v_a_2660_);
v___y_2662_ = v___x_2707_;
goto v___jp_2661_;
}
else
{
v___y_2662_ = v___x_2706_;
goto v___jp_2661_;
}
v___jp_2661_:
{
if (v___y_2662_ == 0)
{
lean_object* v___x_2663_; 
lean_dec_ref_known(v___x_2658_, 1);
v___x_2663_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2657_, v___y_2662_, v___x_2636_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2696_; 
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2696_ == 0)
{
lean_object* v_unused_2697_; 
v_unused_2697_ = lean_ctor_get(v___x_2663_, 0);
lean_dec(v_unused_2697_);
v___x_2665_ = v___x_2663_;
v_isShared_2666_ = v_isSharedCheck_2696_;
goto v_resetjp_2664_;
}
else
{
lean_dec(v___x_2663_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2696_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
uint8_t v___x_2667_; 
v___x_2667_ = l_Lean_Exception_isInterrupt(v_a_2660_);
if (v___x_2667_ == 0)
{
uint8_t v___x_2668_; 
lean_inc(v_a_2660_);
v___x_2668_ = l_Lean_Exception_isMaxRecDepth(v_a_2660_);
if (v___x_2668_ == 0)
{
lean_object* v_toCold_2669_; lean_object* v_options_2670_; uint8_t v_hasTrace_2671_; 
lean_del_object(v___x_2665_);
v_toCold_2669_ = lean_ctor_get(v___y_2633_, 0);
v_options_2670_ = lean_ctor_get(v_toCold_2669_, 2);
v_hasTrace_2671_ = lean_ctor_get_uint8(v_options_2670_, sizeof(void*)*1);
if (v_hasTrace_2671_ == 0)
{
lean_dec(v_a_2660_);
goto v___jp_2653_;
}
else
{
lean_object* v_inheritedTraceOptions_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; 
v_inheritedTraceOptions_2672_ = lean_ctor_get(v_toCold_2669_, 11);
v___x_2673_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2674_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_2675_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2672_, v_options_2670_, v___x_2674_);
if (v___x_2675_ == 0)
{
lean_dec(v_a_2660_);
goto v___jp_2653_;
}
else
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2676_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_2677_ = l_Lean_Exception_toMessageData(v_a_2660_);
v___x_2678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2676_);
lean_ctor_set(v___x_2678_, 1, v___x_2677_);
v___x_2679_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v___x_2673_, v___x_2678_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; lean_object* v___x_2681_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v___x_2679_, 1);
lean_inc(v___x_2636_);
v___x_2681_ = lean_apply_10(v___f_2628_, v_a_2680_, v___x_2627_, v___x_2636_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, lean_box(0));
v___y_2642_ = v___x_2681_;
goto v___jp_2641_;
}
else
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
lean_dec(v___x_2636_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec_ref(v___f_2628_);
lean_dec_ref(v___x_2627_);
v_a_2682_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2684_ = v___x_2679_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2679_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2685_ == 0)
{
v___x_2687_ = v___x_2684_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_a_2682_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
}
}
}
else
{
lean_object* v___x_2691_; 
lean_dec(v___x_2636_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec_ref(v___f_2628_);
lean_dec_ref(v___x_2627_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set_tag(v___x_2665_, 1);
lean_ctor_set(v___x_2665_, 0, v_a_2660_);
v___x_2691_ = v___x_2665_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2660_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
else
{
lean_object* v___x_2694_; 
lean_dec(v___x_2636_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec_ref(v___f_2628_);
lean_dec_ref(v___x_2627_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set_tag(v___x_2665_, 1);
lean_ctor_set(v___x_2665_, 0, v_a_2660_);
v___x_2694_ = v___x_2665_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2660_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
else
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
lean_dec(v_a_2660_);
lean_dec(v___x_2636_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec_ref(v___f_2628_);
lean_dec_ref(v___x_2627_);
v_a_2698_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2663_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2663_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
if (v_isShared_2701_ == 0)
{
v___x_2703_ = v___x_2700_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
else
{
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_dec(v___x_2636_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec_ref(v___f_2628_);
lean_dec_ref(v___x_2627_);
return v___x_2658_;
}
}
}
}
else
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2715_; 
lean_dec(v___x_2636_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec_ref(v___f_2628_);
lean_dec_ref(v___x_2627_);
lean_dec_ref(v___x_2626_);
v_a_2708_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2710_ = v___x_2656_;
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2656_);
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
v___jp_2637_:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2639_ = lean_st_ref_get(v___x_2636_);
lean_dec(v___x_2636_);
lean_dec(v___x_2639_);
v___x_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2640_, 0, v_a_2638_);
return v___x_2640_;
}
v___jp_2641_:
{
if (lean_obj_tag(v___y_2642_) == 0)
{
lean_object* v_a_2643_; lean_object* v_a_2644_; 
v_a_2643_ = lean_ctor_get(v___y_2642_, 0);
lean_inc(v_a_2643_);
lean_dec_ref_known(v___y_2642_, 1);
v_a_2644_ = lean_ctor_get(v_a_2643_, 0);
lean_inc(v_a_2644_);
lean_dec(v_a_2643_);
v_a_2638_ = v_a_2644_;
goto v___jp_2637_;
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
lean_dec(v___x_2636_);
v_a_2645_ = lean_ctor_get(v___y_2642_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___y_2642_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___y_2642_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___y_2642_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2645_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
v___jp_2653_:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = lean_box(0);
lean_inc(v___x_2636_);
v___x_2655_ = lean_apply_10(v___f_2628_, v___x_2654_, v___x_2627_, v___x_2636_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, lean_box(0));
v___y_2642_ = v___x_2655_;
goto v___jp_2641_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed(lean_object* v___x_2716_, lean_object* v___x_2717_, lean_object* v___x_2718_, lean_object* v___f_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(v___x_2716_, v___x_2717_, v___x_2718_, v___f_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(lean_object* v___x_2728_, uint8_t v___x_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v___x_2737_; 
v___x_2737_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2728_, v___x_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed(lean_object* v___x_2738_, lean_object* v___x_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
uint8_t v___x_11302__boxed_2747_; lean_object* v_res_2748_; 
v___x_11302__boxed_2747_ = lean_unbox(v___x_2739_);
v_res_2748_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(v___x_2738_, v___x_11302__boxed_2747_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(lean_object* v_cls_2749_, lean_object* v_msg_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v_ref_2756_; lean_object* v___x_2757_; lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2802_; 
v_ref_2756_ = lean_ctor_get(v___y_2753_, 2);
v___x_2757_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_);
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2760_ = v___x_2757_;
v_isShared_2761_ = v_isSharedCheck_2802_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2757_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2802_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2762_; lean_object* v_traceState_2763_; lean_object* v_env_2764_; lean_object* v_nextMacroScope_2765_; lean_object* v_ngen_2766_; lean_object* v_auxDeclNGen_2767_; lean_object* v_cache_2768_; lean_object* v_messages_2769_; lean_object* v_infoState_2770_; lean_object* v_snapshotTasks_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2801_; 
v___x_2762_ = lean_st_ref_take(v___y_2754_);
v_traceState_2763_ = lean_ctor_get(v___x_2762_, 4);
v_env_2764_ = lean_ctor_get(v___x_2762_, 0);
v_nextMacroScope_2765_ = lean_ctor_get(v___x_2762_, 1);
v_ngen_2766_ = lean_ctor_get(v___x_2762_, 2);
v_auxDeclNGen_2767_ = lean_ctor_get(v___x_2762_, 3);
v_cache_2768_ = lean_ctor_get(v___x_2762_, 5);
v_messages_2769_ = lean_ctor_get(v___x_2762_, 6);
v_infoState_2770_ = lean_ctor_get(v___x_2762_, 7);
v_snapshotTasks_2771_ = lean_ctor_get(v___x_2762_, 8);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2773_ = v___x_2762_;
v_isShared_2774_ = v_isSharedCheck_2801_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_snapshotTasks_2771_);
lean_inc(v_infoState_2770_);
lean_inc(v_messages_2769_);
lean_inc(v_cache_2768_);
lean_inc(v_traceState_2763_);
lean_inc(v_auxDeclNGen_2767_);
lean_inc(v_ngen_2766_);
lean_inc(v_nextMacroScope_2765_);
lean_inc(v_env_2764_);
lean_dec(v___x_2762_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2801_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
uint64_t v_tid_2775_; lean_object* v_traces_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2800_; 
v_tid_2775_ = lean_ctor_get_uint64(v_traceState_2763_, sizeof(void*)*1);
v_traces_2776_ = lean_ctor_get(v_traceState_2763_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v_traceState_2763_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2778_ = v_traceState_2763_;
v_isShared_2779_ = v_isSharedCheck_2800_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_traces_2776_);
lean_dec(v_traceState_2763_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2800_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2780_; double v___x_2781_; uint8_t v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2790_; 
v___x_2780_ = lean_box(0);
v___x_2781_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0);
v___x_2782_ = 0;
v___x_2783_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2784_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2784_, 0, v_cls_2749_);
lean_ctor_set(v___x_2784_, 1, v___x_2780_);
lean_ctor_set(v___x_2784_, 2, v___x_2783_);
lean_ctor_set_float(v___x_2784_, sizeof(void*)*3, v___x_2781_);
lean_ctor_set_float(v___x_2784_, sizeof(void*)*3 + 8, v___x_2781_);
lean_ctor_set_uint8(v___x_2784_, sizeof(void*)*3 + 16, v___x_2782_);
v___x_2785_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__1));
v___x_2786_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2784_);
lean_ctor_set(v___x_2786_, 1, v_a_2758_);
lean_ctor_set(v___x_2786_, 2, v___x_2785_);
lean_inc(v_ref_2756_);
v___x_2787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2787_, 0, v_ref_2756_);
lean_ctor_set(v___x_2787_, 1, v___x_2786_);
v___x_2788_ = l_Lean_PersistentArray_push___redArg(v_traces_2776_, v___x_2787_);
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 0, v___x_2788_);
v___x_2790_ = v___x_2778_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2788_);
lean_ctor_set_uint64(v_reuseFailAlloc_2799_, sizeof(void*)*1, v_tid_2775_);
v___x_2790_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
lean_object* v___x_2792_; 
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 4, v___x_2790_);
v___x_2792_ = v___x_2773_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_env_2764_);
lean_ctor_set(v_reuseFailAlloc_2798_, 1, v_nextMacroScope_2765_);
lean_ctor_set(v_reuseFailAlloc_2798_, 2, v_ngen_2766_);
lean_ctor_set(v_reuseFailAlloc_2798_, 3, v_auxDeclNGen_2767_);
lean_ctor_set(v_reuseFailAlloc_2798_, 4, v___x_2790_);
lean_ctor_set(v_reuseFailAlloc_2798_, 5, v_cache_2768_);
lean_ctor_set(v_reuseFailAlloc_2798_, 6, v_messages_2769_);
lean_ctor_set(v_reuseFailAlloc_2798_, 7, v_infoState_2770_);
lean_ctor_set(v_reuseFailAlloc_2798_, 8, v_snapshotTasks_2771_);
v___x_2792_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2796_; 
v___x_2793_ = lean_st_ref_put(v___y_2754_, v___x_2792_);
v___x_2794_ = lean_box(0);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v___x_2794_);
v___x_2796_ = v___x_2760_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2794_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3___boxed(lean_object* v_cls_2803_, lean_object* v_msg_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v_cls_2803_, v_msg_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
return v_res_2810_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2812_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__0));
v___x_2813_ = l_Lean_stringToMessageData(v___x_2812_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(lean_object* v_term_2814_, lean_object* v___x_2815_, lean_object* v___x_2816_, lean_object* v___f_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v___y_2824_; lean_object* v___x_2842_; 
v___x_2842_ = l_Lean_Elab_Term_TermElabM_run___redArg(v_term_2814_, v___x_2815_, v___x_2816_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2851_; 
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec_ref(v___f_2817_);
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2845_ = v___x_2842_;
v_isShared_2846_ = v_isSharedCheck_2851_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2842_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2851_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v_fst_2847_; lean_object* v___x_2849_; 
v_fst_2847_ = lean_ctor_get(v_a_2843_, 0);
lean_inc(v_fst_2847_);
lean_dec(v_a_2843_);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 0, v_fst_2847_);
v___x_2849_ = v___x_2845_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_fst_2847_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2895_; 
v_a_2852_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2854_ = v___x_2842_;
v_isShared_2855_ = v_isSharedCheck_2895_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2842_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2895_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
uint8_t v___y_2860_; uint8_t v___x_2893_; 
v___x_2893_ = l_Lean_Exception_isInterrupt(v_a_2852_);
if (v___x_2893_ == 0)
{
uint8_t v___x_2894_; 
lean_inc(v_a_2852_);
v___x_2894_ = l_Lean_Exception_isRuntime(v_a_2852_);
v___y_2860_ = v___x_2894_;
goto v___jp_2859_;
}
else
{
v___y_2860_ = v___x_2893_;
goto v___jp_2859_;
}
v___jp_2856_:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2857_ = lean_box(0);
v___x_2858_ = lean_apply_6(v___f_2817_, v___x_2857_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, lean_box(0));
v___y_2824_ = v___x_2858_;
goto v___jp_2823_;
}
v___jp_2859_:
{
if (v___y_2860_ == 0)
{
uint8_t v___x_2861_; 
v___x_2861_ = l_Lean_Exception_isInterrupt(v_a_2852_);
if (v___x_2861_ == 0)
{
uint8_t v___x_2862_; 
lean_inc(v_a_2852_);
v___x_2862_ = l_Lean_Exception_isMaxRecDepth(v_a_2852_);
if (v___x_2862_ == 0)
{
lean_object* v_toCold_2863_; lean_object* v_options_2864_; uint8_t v_hasTrace_2865_; 
lean_del_object(v___x_2854_);
v_toCold_2863_ = lean_ctor_get(v___y_2820_, 0);
v_options_2864_ = lean_ctor_get(v_toCold_2863_, 2);
v_hasTrace_2865_ = lean_ctor_get_uint8(v_options_2864_, sizeof(void*)*1);
if (v_hasTrace_2865_ == 0)
{
lean_dec(v_a_2852_);
goto v___jp_2856_;
}
else
{
lean_object* v_inheritedTraceOptions_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; uint8_t v___x_2869_; 
v_inheritedTraceOptions_2866_ = lean_ctor_get(v_toCold_2863_, 11);
v___x_2867_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2868_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_2869_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2866_, v_options_2864_, v___x_2868_);
if (v___x_2869_ == 0)
{
lean_dec(v_a_2852_);
goto v___jp_2856_;
}
else
{
lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2870_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1);
v___x_2871_ = l_Lean_Exception_toMessageData(v_a_2852_);
v___x_2872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2870_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
v___x_2873_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_2867_, v___x_2872_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v___x_2875_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2873_, 1);
v___x_2875_ = lean_apply_6(v___f_2817_, v_a_2874_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, lean_box(0));
v___y_2824_ = v___x_2875_;
goto v___jp_2823_;
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec_ref(v___f_2817_);
v_a_2876_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2873_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2873_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2876_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
}
}
else
{
lean_object* v___x_2885_; 
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec_ref(v___f_2817_);
if (v_isShared_2855_ == 0)
{
v___x_2885_ = v___x_2854_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2852_);
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
lean_object* v___x_2888_; 
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec_ref(v___f_2817_);
if (v_isShared_2855_ == 0)
{
v___x_2888_ = v___x_2854_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2852_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
else
{
lean_object* v___x_2891_; 
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec_ref(v___f_2817_);
if (v_isShared_2855_ == 0)
{
v___x_2891_ = v___x_2854_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2852_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
}
v___jp_2823_:
{
if (lean_obj_tag(v___y_2824_) == 0)
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2833_; 
v_a_2825_ = lean_ctor_get(v___y_2824_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___y_2824_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2827_ = v___y_2824_;
v_isShared_2828_ = v_isSharedCheck_2833_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___y_2824_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2833_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v_a_2829_; lean_object* v___x_2831_; 
v_a_2829_ = lean_ctor_get(v_a_2825_, 0);
lean_inc(v_a_2829_);
lean_dec(v_a_2825_);
if (v_isShared_2828_ == 0)
{
lean_ctor_set(v___x_2827_, 0, v_a_2829_);
v___x_2831_ = v___x_2827_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2829_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
v_a_2834_ = lean_ctor_get(v___y_2824_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___y_2824_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___y_2824_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___y_2824_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___boxed(lean_object* v_term_2896_, lean_object* v___x_2897_, lean_object* v___x_2898_, lean_object* v___f_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(v_term_2896_, v___x_2897_, v___x_2898_, v___f_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_2906_, lean_object* v_vals_2907_, lean_object* v_i_2908_, lean_object* v_k_2909_){
_start:
{
lean_object* v___x_2910_; uint8_t v___x_2911_; 
v___x_2910_ = lean_array_get_size(v_keys_2906_);
v___x_2911_ = lean_nat_dec_lt(v_i_2908_, v___x_2910_);
if (v___x_2911_ == 0)
{
lean_object* v___x_2912_; 
lean_dec(v_i_2908_);
v___x_2912_ = lean_box(0);
return v___x_2912_;
}
else
{
lean_object* v_k_x27_2913_; uint8_t v___x_2914_; 
v_k_x27_2913_ = lean_array_fget_borrowed(v_keys_2906_, v_i_2908_);
v___x_2914_ = l_Lean_instBEqMVarId_beq(v_k_2909_, v_k_x27_2913_);
if (v___x_2914_ == 0)
{
lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2915_ = lean_unsigned_to_nat(1u);
v___x_2916_ = lean_nat_add(v_i_2908_, v___x_2915_);
lean_dec(v_i_2908_);
v_i_2908_ = v___x_2916_;
goto _start;
}
else
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2918_ = lean_array_fget_borrowed(v_vals_2907_, v_i_2908_);
lean_dec(v_i_2908_);
lean_inc(v___x_2918_);
v___x_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
return v___x_2919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_2920_, lean_object* v_vals_2921_, lean_object* v_i_2922_, lean_object* v_k_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_keys_2920_, v_vals_2921_, v_i_2922_, v_k_2923_);
lean_dec(v_k_2923_);
lean_dec_ref(v_vals_2921_);
lean_dec_ref(v_keys_2920_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(lean_object* v_x_2925_, size_t v_x_2926_, lean_object* v_x_2927_){
_start:
{
if (lean_obj_tag(v_x_2925_) == 0)
{
lean_object* v_es_2928_; lean_object* v___x_2929_; size_t v___x_2930_; size_t v___x_2931_; lean_object* v_j_2932_; lean_object* v___x_2933_; 
v_es_2928_ = lean_ctor_get(v_x_2925_, 0);
v___x_2929_ = lean_box(2);
v___x_2930_ = ((size_t)31ULL);
v___x_2931_ = lean_usize_land(v_x_2926_, v___x_2930_);
v_j_2932_ = lean_usize_to_nat(v___x_2931_);
v___x_2933_ = lean_array_get_borrowed(v___x_2929_, v_es_2928_, v_j_2932_);
lean_dec(v_j_2932_);
switch(lean_obj_tag(v___x_2933_))
{
case 0:
{
lean_object* v_key_2934_; lean_object* v_val_2935_; uint8_t v___x_2936_; 
v_key_2934_ = lean_ctor_get(v___x_2933_, 0);
v_val_2935_ = lean_ctor_get(v___x_2933_, 1);
v___x_2936_ = l_Lean_instBEqMVarId_beq(v_x_2927_, v_key_2934_);
if (v___x_2936_ == 0)
{
lean_object* v___x_2937_; 
v___x_2937_ = lean_box(0);
return v___x_2937_;
}
else
{
lean_object* v___x_2938_; 
lean_inc(v_val_2935_);
v___x_2938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2938_, 0, v_val_2935_);
return v___x_2938_;
}
}
case 1:
{
lean_object* v_node_2939_; size_t v___x_2940_; size_t v___x_2941_; 
v_node_2939_ = lean_ctor_get(v___x_2933_, 0);
v___x_2940_ = ((size_t)5ULL);
v___x_2941_ = lean_usize_shift_right(v_x_2926_, v___x_2940_);
v_x_2925_ = v_node_2939_;
v_x_2926_ = v___x_2941_;
goto _start;
}
default: 
{
lean_object* v___x_2943_; 
v___x_2943_ = lean_box(0);
return v___x_2943_;
}
}
}
else
{
lean_object* v_ks_2944_; lean_object* v_vs_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v_ks_2944_ = lean_ctor_get(v_x_2925_, 0);
v_vs_2945_ = lean_ctor_get(v_x_2925_, 1);
v___x_2946_ = lean_unsigned_to_nat(0u);
v___x_2947_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_ks_2944_, v_vs_2945_, v___x_2946_, v_x_2927_);
return v___x_2947_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg___boxed(lean_object* v_x_2948_, lean_object* v_x_2949_, lean_object* v_x_2950_){
_start:
{
size_t v_x_11621__boxed_2951_; lean_object* v_res_2952_; 
v_x_11621__boxed_2951_ = lean_unbox_usize(v_x_2949_);
lean_dec(v_x_2949_);
v_res_2952_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_2948_, v_x_11621__boxed_2951_, v_x_2950_);
lean_dec(v_x_2950_);
lean_dec_ref(v_x_2948_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(lean_object* v_x_2953_, lean_object* v_x_2954_){
_start:
{
uint64_t v___x_2955_; size_t v___x_2956_; lean_object* v___x_2957_; 
v___x_2955_ = l_Lean_instHashableMVarId_hash(v_x_2954_);
v___x_2956_ = lean_uint64_to_usize(v___x_2955_);
v___x_2957_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_2953_, v___x_2956_, v_x_2954_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg___boxed(lean_object* v_x_2958_, lean_object* v_x_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_x_2958_, v_x_2959_);
lean_dec(v_x_2959_);
lean_dec_ref(v_x_2958_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(lean_object* v_c_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_){
_start:
{
lean_object* v_mctx_2990_; lean_object* v_env_2991_; lean_object* v_opts_2992_; lean_object* v_namingCtx_2993_; lean_object* v_goal_2994_; lean_object* v_decls_2995_; lean_object* v___x_2996_; 
v_mctx_2990_ = lean_ctor_get(v_c_2986_, 3);
lean_inc_ref(v_mctx_2990_);
v_env_2991_ = lean_ctor_get(v_c_2986_, 2);
lean_inc_ref(v_env_2991_);
v_opts_2992_ = lean_ctor_get(v_c_2986_, 4);
lean_inc_ref(v_opts_2992_);
v_namingCtx_2993_ = lean_ctor_get(v_c_2986_, 5);
lean_inc_ref(v_namingCtx_2993_);
v_goal_2994_ = lean_ctor_get(v_c_2986_, 6);
lean_inc(v_goal_2994_);
lean_dec_ref(v_c_2986_);
v_decls_2995_ = lean_ctor_get(v_mctx_2990_, 5);
v___x_2996_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_decls_2995_, v_goal_2994_);
if (lean_obj_tag(v___x_2996_) == 1)
{
lean_object* v_val_2997_; lean_object* v_lctx_2998_; lean_object* v___f_2999_; lean_object* v___f_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___f_3005_; lean_object* v___x_3006_; uint8_t v___x_3007_; lean_object* v___x_3008_; lean_object* v_term_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___f_3012_; lean_object* v___x_3013_; 
v_val_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_val_2997_);
lean_dec_ref_known(v___x_2996_, 1);
v_lctx_2998_ = lean_ctor_get(v_val_2997_, 1);
lean_inc_ref(v_lctx_2998_);
lean_dec(v_val_2997_);
v___f_2999_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__0));
v___f_3000_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__1));
v___x_3001_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__3));
v___x_3002_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__4));
v___x_3003_ = lean_box(0);
lean_inc(v_goal_2994_);
v___x_3004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3004_, 0, v_goal_2994_);
lean_ctor_set(v___x_3004_, 1, v___x_3003_);
v___f_3005_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed), 11, 4);
lean_closure_set(v___f_3005_, 0, v___x_3004_);
lean_closure_set(v___f_3005_, 1, v___x_3001_);
lean_closure_set(v___f_3005_, 2, v___x_3002_);
lean_closure_set(v___f_3005_, 3, v___f_2999_);
v___x_3006_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed), 10, 3);
lean_closure_set(v___x_3006_, 0, lean_box(0));
lean_closure_set(v___x_3006_, 1, v_goal_2994_);
lean_closure_set(v___x_3006_, 2, v___f_3005_);
v___x_3007_ = 1;
v___x_3008_ = lean_box(v___x_3007_);
v_term_3009_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed), 9, 2);
lean_closure_set(v_term_3009_, 0, v___x_3006_);
lean_closure_set(v_term_3009_, 1, v___x_3008_);
v___x_3010_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__6));
v___x_3011_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__7));
v___f_3012_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___boxed), 9, 4);
lean_closure_set(v___f_3012_, 0, v_term_3009_);
lean_closure_set(v___f_3012_, 1, v___x_3010_);
lean_closure_set(v___f_3012_, 2, v___x_3011_);
lean_closure_set(v___f_3012_, 3, v___f_3000_);
v___x_3013_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_2991_, v_mctx_2990_, v_lctx_2998_, v_opts_2992_, v_namingCtx_2993_, v___f_3012_, v_a_2987_, v_a_2988_);
lean_dec_ref(v_namingCtx_2993_);
return v___x_3013_;
}
else
{
lean_object* v___x_3014_; lean_object* v___x_3015_; 
lean_dec(v___x_2996_);
lean_dec(v_goal_2994_);
lean_dec_ref(v_namingCtx_2993_);
lean_dec_ref(v_opts_2992_);
lean_dec_ref(v_env_2991_);
lean_dec_ref(v_mctx_2990_);
v___x_3014_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__0));
v___x_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3014_);
return v___x_3015_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___boxed(lean_object* v_c_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(v_c_3016_, v_a_3017_, v_a_3018_);
lean_dec(v_a_3018_);
lean_dec_ref(v_a_3017_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0(lean_object* v_00_u03b2_3021_, lean_object* v_x_3022_, lean_object* v_x_3023_){
_start:
{
lean_object* v___x_3024_; 
v___x_3024_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_x_3022_, v_x_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___boxed(lean_object* v_00_u03b2_3025_, lean_object* v_x_3026_, lean_object* v_x_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0(v_00_u03b2_3025_, v_x_3026_, v_x_3027_);
lean_dec(v_x_3027_);
lean_dec_ref(v_x_3026_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(lean_object* v_cls_3029_, lean_object* v_msg_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_){
_start:
{
lean_object* v___x_3040_; 
v___x_3040_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_3029_, v_msg_3030_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___boxed(lean_object* v_cls_3041_, lean_object* v_msg_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(v_cls_3041_, v_msg_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3045_);
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(lean_object* v_00_u03b2_3053_, lean_object* v_x_3054_, size_t v_x_3055_, lean_object* v_x_3056_){
_start:
{
lean_object* v___x_3057_; 
v___x_3057_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_3054_, v_x_3055_, v_x_3056_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3058_, lean_object* v_x_3059_, lean_object* v_x_3060_, lean_object* v_x_3061_){
_start:
{
size_t v_x_11878__boxed_3062_; lean_object* v_res_3063_; 
v_x_11878__boxed_3062_ = lean_unbox_usize(v_x_3060_);
lean_dec(v_x_3060_);
v_res_3063_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(v_00_u03b2_3058_, v_x_3059_, v_x_11878__boxed_3062_, v_x_3061_);
lean_dec(v_x_3061_);
lean_dec_ref(v_x_3059_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3064_, lean_object* v_keys_3065_, lean_object* v_vals_3066_, lean_object* v_heq_3067_, lean_object* v_i_3068_, lean_object* v_k_3069_){
_start:
{
lean_object* v___x_3070_; 
v___x_3070_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_keys_3065_, v_vals_3066_, v_i_3068_, v_k_3069_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3071_, lean_object* v_keys_3072_, lean_object* v_vals_3073_, lean_object* v_heq_3074_, lean_object* v_i_3075_, lean_object* v_k_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2(v_00_u03b2_3071_, v_keys_3072_, v_vals_3073_, v_heq_3074_, v_i_3075_, v_k_3076_);
lean_dec(v_k_3076_);
lean_dec_ref(v_vals_3073_);
lean_dec_ref(v_keys_3072_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(uint8_t v___x_3080_, lean_object* v___x_3081_, lean_object* v_ref_3082_, lean_object* v_a_3083_, lean_object* v___x_3084_, lean_object* v___x_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
if (v___x_3080_ == 0)
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; uint8_t v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3081_);
v___x_3090_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__0));
v___x_3091_ = lean_box(0);
v___x_3092_ = 4;
v___x_3093_ = l_Lean_MessageData_nil;
v___x_3094_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_3082_, v_a_3083_, v___x_3089_, v___x_3090_, v___x_3091_, v___x_3092_, v___x_3093_, v___y_3086_, v___y_3087_);
return v___x_3094_;
}
else
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; uint8_t v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3095_ = lean_array_get(v___x_3084_, v_a_3083_, v___x_3085_);
lean_dec_ref(v_a_3083_);
v___x_3096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3081_);
v___x_3097_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__1));
v___x_3098_ = lean_box(0);
v___x_3099_ = 4;
v___x_3100_ = l_Lean_MessageData_nil;
v___x_3101_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_3082_, v___x_3095_, v___x_3096_, v___x_3097_, v___x_3098_, v___x_3099_, v___x_3100_, v___y_3086_, v___y_3087_);
return v___x_3101_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed(lean_object* v___x_3102_, lean_object* v___x_3103_, lean_object* v_ref_3104_, lean_object* v_a_3105_, lean_object* v___x_3106_, lean_object* v___x_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
uint8_t v___x_3485__boxed_3111_; lean_object* v_res_3112_; 
v___x_3485__boxed_3111_ = lean_unbox(v___x_3102_);
v_res_3112_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(v___x_3485__boxed_3111_, v___x_3103_, v_ref_3104_, v_a_3105_, v___x_3106_, v___x_3107_, v___y_3108_, v___y_3109_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v___x_3107_);
lean_dec_ref(v___x_3106_);
return v_res_3112_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_3113_, uint8_t v___y_3114_, lean_object* v_x_3115_){
_start:
{
if (lean_obj_tag(v_x_3115_) == 1)
{
lean_object* v_pre_3116_; 
v_pre_3116_ = lean_ctor_get(v_x_3115_, 0);
if (lean_obj_tag(v_pre_3116_) == 0)
{
lean_object* v_str_3117_; lean_object* v___x_3118_; uint8_t v___x_3119_; 
v_str_3117_ = lean_ctor_get(v_x_3115_, 1);
v___x_3118_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__1));
v___x_3119_ = lean_string_dec_eq(v_str_3117_, v___x_3118_);
if (v___x_3119_ == 0)
{
return v___x_3119_;
}
else
{
return v_suppressElabErrors_3113_;
}
}
else
{
return v___y_3114_;
}
}
else
{
return v___y_3114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_3120_, lean_object* v___y_3121_, lean_object* v_x_3122_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3123_; uint8_t v___y_3538__boxed_3124_; uint8_t v_res_3125_; lean_object* v_r_3126_; 
v_suppressElabErrors_boxed_3123_ = lean_unbox(v_suppressElabErrors_3120_);
v___y_3538__boxed_3124_ = lean_unbox(v___y_3121_);
v_res_3125_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_3123_, v___y_3538__boxed_3124_, v_x_3122_);
lean_dec(v_x_3122_);
v_r_3126_ = lean_box(v_res_3125_);
return v_r_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(lean_object* v_ref_3127_, lean_object* v_msgData_3128_, uint8_t v_severity_3129_, uint8_t v_isSilent_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_){
_start:
{
lean_object* v___y_3135_; uint8_t v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; uint8_t v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; uint8_t v___y_3200_; uint8_t v___y_3201_; lean_object* v___y_3202_; uint8_t v___y_3203_; lean_object* v___y_3204_; uint8_t v___y_3228_; uint8_t v___y_3229_; lean_object* v___y_3230_; uint8_t v___y_3231_; lean_object* v___y_3232_; uint8_t v___y_3236_; uint8_t v___y_3237_; uint8_t v___y_3238_; uint8_t v___x_3253_; uint8_t v___y_3255_; uint8_t v___y_3256_; uint8_t v___y_3257_; uint8_t v___y_3259_; uint8_t v___x_3271_; 
v___x_3253_ = 2;
v___x_3271_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3129_, v___x_3253_);
if (v___x_3271_ == 0)
{
v___y_3259_ = v___x_3271_;
goto v___jp_3258_;
}
else
{
uint8_t v___x_3272_; 
lean_inc_ref(v_msgData_3128_);
v___x_3272_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3128_);
v___y_3259_ = v___x_3272_;
goto v___jp_3258_;
}
v___jp_3134_:
{
lean_object* v___x_3143_; 
v___x_3143_ = l_Lean_Elab_Command_getScope___redArg(v___y_3142_);
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_object* v_a_3144_; lean_object* v___x_3145_; 
v_a_3144_ = lean_ctor_get(v___x_3143_, 0);
lean_inc(v_a_3144_);
lean_dec_ref_known(v___x_3143_, 1);
v___x_3145_ = l_Lean_Elab_Command_getScope___redArg(v___y_3142_);
if (lean_obj_tag(v___x_3145_) == 0)
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3182_; 
v_a_3146_ = lean_ctor_get(v___x_3145_, 0);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3148_ = v___x_3145_;
v_isShared_3149_ = v_isSharedCheck_3182_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3145_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3182_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3150_; lean_object* v_currNamespace_3151_; lean_object* v_openDecls_3152_; lean_object* v_env_3153_; lean_object* v_messages_3154_; lean_object* v_scopes_3155_; lean_object* v_usedQuotCtxts_3156_; lean_object* v_nextMacroScope_3157_; lean_object* v_maxRecDepth_3158_; lean_object* v_ngen_3159_; lean_object* v_auxDeclNGen_3160_; lean_object* v_infoState_3161_; lean_object* v_traceState_3162_; lean_object* v_snapshotTasks_3163_; lean_object* v_prevLinterStates_3164_; lean_object* v_codeQualityEntryTasks_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3181_; 
v___x_3150_ = lean_st_ref_take(v___y_3142_);
v_currNamespace_3151_ = lean_ctor_get(v_a_3144_, 2);
lean_inc(v_currNamespace_3151_);
lean_dec(v_a_3144_);
v_openDecls_3152_ = lean_ctor_get(v_a_3146_, 3);
lean_inc(v_openDecls_3152_);
lean_dec(v_a_3146_);
v_env_3153_ = lean_ctor_get(v___x_3150_, 0);
v_messages_3154_ = lean_ctor_get(v___x_3150_, 1);
v_scopes_3155_ = lean_ctor_get(v___x_3150_, 2);
v_usedQuotCtxts_3156_ = lean_ctor_get(v___x_3150_, 3);
v_nextMacroScope_3157_ = lean_ctor_get(v___x_3150_, 4);
v_maxRecDepth_3158_ = lean_ctor_get(v___x_3150_, 5);
v_ngen_3159_ = lean_ctor_get(v___x_3150_, 6);
v_auxDeclNGen_3160_ = lean_ctor_get(v___x_3150_, 7);
v_infoState_3161_ = lean_ctor_get(v___x_3150_, 8);
v_traceState_3162_ = lean_ctor_get(v___x_3150_, 9);
v_snapshotTasks_3163_ = lean_ctor_get(v___x_3150_, 10);
v_prevLinterStates_3164_ = lean_ctor_get(v___x_3150_, 11);
v_codeQualityEntryTasks_3165_ = lean_ctor_get(v___x_3150_, 12);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3167_ = v___x_3150_;
v_isShared_3168_ = v_isSharedCheck_3181_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3165_);
lean_inc(v_prevLinterStates_3164_);
lean_inc(v_snapshotTasks_3163_);
lean_inc(v_traceState_3162_);
lean_inc(v_infoState_3161_);
lean_inc(v_auxDeclNGen_3160_);
lean_inc(v_ngen_3159_);
lean_inc(v_maxRecDepth_3158_);
lean_inc(v_nextMacroScope_3157_);
lean_inc(v_usedQuotCtxts_3156_);
lean_inc(v_scopes_3155_);
lean_inc(v_messages_3154_);
lean_inc(v_env_3153_);
lean_dec(v___x_3150_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3181_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3174_; 
v___x_3169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3169_, 0, v_currNamespace_3151_);
lean_ctor_set(v___x_3169_, 1, v_openDecls_3152_);
v___x_3170_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3169_);
lean_ctor_set(v___x_3170_, 1, v___y_3141_);
lean_inc_ref(v___y_3138_);
lean_inc_ref(v___y_3137_);
v___x_3171_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3171_, 0, v___y_3137_);
lean_ctor_set(v___x_3171_, 1, v___y_3140_);
lean_ctor_set(v___x_3171_, 2, v___y_3135_);
lean_ctor_set(v___x_3171_, 3, v___y_3138_);
lean_ctor_set(v___x_3171_, 4, v___x_3170_);
lean_ctor_set_uint8(v___x_3171_, sizeof(void*)*5, v___y_3136_);
lean_ctor_set_uint8(v___x_3171_, sizeof(void*)*5 + 1, v___y_3139_);
lean_ctor_set_uint8(v___x_3171_, sizeof(void*)*5 + 2, v_isSilent_3130_);
v___x_3172_ = l_Lean_MessageLog_add(v___x_3171_, v_messages_3154_);
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 1, v___x_3172_);
v___x_3174_ = v___x_3167_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_env_3153_);
lean_ctor_set(v_reuseFailAlloc_3180_, 1, v___x_3172_);
lean_ctor_set(v_reuseFailAlloc_3180_, 2, v_scopes_3155_);
lean_ctor_set(v_reuseFailAlloc_3180_, 3, v_usedQuotCtxts_3156_);
lean_ctor_set(v_reuseFailAlloc_3180_, 4, v_nextMacroScope_3157_);
lean_ctor_set(v_reuseFailAlloc_3180_, 5, v_maxRecDepth_3158_);
lean_ctor_set(v_reuseFailAlloc_3180_, 6, v_ngen_3159_);
lean_ctor_set(v_reuseFailAlloc_3180_, 7, v_auxDeclNGen_3160_);
lean_ctor_set(v_reuseFailAlloc_3180_, 8, v_infoState_3161_);
lean_ctor_set(v_reuseFailAlloc_3180_, 9, v_traceState_3162_);
lean_ctor_set(v_reuseFailAlloc_3180_, 10, v_snapshotTasks_3163_);
lean_ctor_set(v_reuseFailAlloc_3180_, 11, v_prevLinterStates_3164_);
lean_ctor_set(v_reuseFailAlloc_3180_, 12, v_codeQualityEntryTasks_3165_);
v___x_3174_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3178_; 
v___x_3175_ = lean_st_ref_put(v___y_3142_, v___x_3174_);
v___x_3176_ = lean_box(0);
if (v_isShared_3149_ == 0)
{
lean_ctor_set(v___x_3148_, 0, v___x_3176_);
v___x_3178_ = v___x_3148_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v___x_3176_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
}
else
{
lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3190_; 
lean_dec(v_a_3144_);
lean_dec_ref(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec(v___y_3135_);
v_a_3183_ = lean_ctor_get(v___x_3145_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3185_ = v___x_3145_;
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3145_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3188_; 
if (v_isShared_3186_ == 0)
{
v___x_3188_ = v___x_3185_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3183_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
}
}
else
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3198_; 
lean_dec_ref(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec(v___y_3135_);
v_a_3191_ = lean_ctor_get(v___x_3143_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3193_ = v___x_3143_;
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3143_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3196_; 
if (v_isShared_3194_ == 0)
{
v___x_3196_ = v___x_3193_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_a_3191_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
}
v___jp_3199_:
{
lean_object* v_fileName_3205_; lean_object* v_fileMap_3206_; uint8_t v_suppressElabErrors_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3226_; 
v_fileName_3205_ = lean_ctor_get(v___y_3131_, 0);
v_fileMap_3206_ = lean_ctor_get(v___y_3131_, 1);
v_suppressElabErrors_3207_ = lean_ctor_get_uint8(v___y_3131_, sizeof(void*)*10);
v___x_3208_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3128_);
v___x_3209_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(v___x_3208_, v___y_3132_);
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3212_ = v___x_3209_;
v_isShared_3213_ = v_isSharedCheck_3226_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___x_3209_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3226_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
lean_inc_ref_n(v_fileMap_3206_, 2);
v___x_3214_ = l_Lean_FileMap_toPosition(v_fileMap_3206_, v___y_3202_);
lean_dec(v___y_3202_);
v___x_3215_ = l_Lean_FileMap_toPosition(v_fileMap_3206_, v___y_3204_);
lean_dec(v___y_3204_);
v___x_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3215_);
v___x_3217_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
if (v_suppressElabErrors_3207_ == 0)
{
lean_del_object(v___x_3212_);
v___y_3135_ = v___x_3216_;
v___y_3136_ = v___y_3201_;
v___y_3137_ = v_fileName_3205_;
v___y_3138_ = v___x_3217_;
v___y_3139_ = v___y_3203_;
v___y_3140_ = v___x_3214_;
v___y_3141_ = v_a_3210_;
v___y_3142_ = v___y_3132_;
goto v___jp_3134_;
}
else
{
lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___f_3220_; uint8_t v___x_3221_; 
v___x_3218_ = lean_box(v_suppressElabErrors_3207_);
v___x_3219_ = lean_box(v___y_3200_);
v___f_3220_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3220_, 0, v___x_3218_);
lean_closure_set(v___f_3220_, 1, v___x_3219_);
lean_inc(v_a_3210_);
v___x_3221_ = l_Lean_MessageData_hasTag(v___f_3220_, v_a_3210_);
if (v___x_3221_ == 0)
{
lean_object* v___x_3222_; lean_object* v___x_3224_; 
lean_dec_ref_known(v___x_3216_, 1);
lean_dec_ref(v___x_3214_);
lean_dec(v_a_3210_);
v___x_3222_ = lean_box(0);
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 0, v___x_3222_);
v___x_3224_ = v___x_3212_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3222_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
else
{
lean_del_object(v___x_3212_);
v___y_3135_ = v___x_3216_;
v___y_3136_ = v___y_3201_;
v___y_3137_ = v_fileName_3205_;
v___y_3138_ = v___x_3217_;
v___y_3139_ = v___y_3203_;
v___y_3140_ = v___x_3214_;
v___y_3141_ = v_a_3210_;
v___y_3142_ = v___y_3132_;
goto v___jp_3134_;
}
}
}
}
v___jp_3227_:
{
lean_object* v___x_3233_; 
v___x_3233_ = l_Lean_Syntax_getTailPos_x3f(v___y_3230_, v___y_3229_);
lean_dec(v___y_3230_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_inc(v___y_3232_);
v___y_3200_ = v___y_3228_;
v___y_3201_ = v___y_3229_;
v___y_3202_ = v___y_3232_;
v___y_3203_ = v___y_3231_;
v___y_3204_ = v___y_3232_;
goto v___jp_3199_;
}
else
{
lean_object* v_val_3234_; 
v_val_3234_ = lean_ctor_get(v___x_3233_, 0);
lean_inc(v_val_3234_);
lean_dec_ref_known(v___x_3233_, 1);
v___y_3200_ = v___y_3228_;
v___y_3201_ = v___y_3229_;
v___y_3202_ = v___y_3232_;
v___y_3203_ = v___y_3231_;
v___y_3204_ = v_val_3234_;
goto v___jp_3199_;
}
}
v___jp_3235_:
{
lean_object* v___x_3239_; 
v___x_3239_ = l_Lean_Elab_Command_getRef___redArg(v___y_3131_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; lean_object* v_ref_3241_; lean_object* v___x_3242_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
lean_inc(v_a_3240_);
lean_dec_ref_known(v___x_3239_, 1);
v_ref_3241_ = l_Lean_replaceRef(v_ref_3127_, v_a_3240_);
lean_dec(v_a_3240_);
v___x_3242_ = l_Lean_Syntax_getPos_x3f(v_ref_3241_, v___y_3237_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v___x_3243_; 
v___x_3243_ = lean_unsigned_to_nat(0u);
v___y_3228_ = v___y_3236_;
v___y_3229_ = v___y_3237_;
v___y_3230_ = v_ref_3241_;
v___y_3231_ = v___y_3238_;
v___y_3232_ = v___x_3243_;
goto v___jp_3227_;
}
else
{
lean_object* v_val_3244_; 
v_val_3244_ = lean_ctor_get(v___x_3242_, 0);
lean_inc(v_val_3244_);
lean_dec_ref_known(v___x_3242_, 1);
v___y_3228_ = v___y_3236_;
v___y_3229_ = v___y_3237_;
v___y_3230_ = v_ref_3241_;
v___y_3231_ = v___y_3238_;
v___y_3232_ = v_val_3244_;
goto v___jp_3227_;
}
}
else
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
lean_dec_ref(v_msgData_3128_);
v_a_3245_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3247_ = v___x_3239_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3239_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3250_; 
if (v_isShared_3248_ == 0)
{
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3245_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
v___jp_3254_:
{
if (v___y_3257_ == 0)
{
v___y_3236_ = v___y_3255_;
v___y_3237_ = v___y_3256_;
v___y_3238_ = v_severity_3129_;
goto v___jp_3235_;
}
else
{
v___y_3236_ = v___y_3255_;
v___y_3237_ = v___y_3256_;
v___y_3238_ = v___x_3253_;
goto v___jp_3235_;
}
}
v___jp_3258_:
{
if (v___y_3259_ == 0)
{
lean_object* v___x_3260_; lean_object* v_scopes_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v_opts_3264_; uint8_t v___x_3265_; uint8_t v___x_3266_; 
v___x_3260_ = lean_st_ref_get(v___y_3132_);
v_scopes_3261_ = lean_ctor_get(v___x_3260_, 2);
lean_inc(v_scopes_3261_);
lean_dec(v___x_3260_);
v___x_3262_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3263_ = l_List_head_x21___redArg(v___x_3262_, v_scopes_3261_);
lean_dec(v_scopes_3261_);
v_opts_3264_ = lean_ctor_get(v___x_3263_, 1);
lean_inc_ref(v_opts_3264_);
lean_dec(v___x_3263_);
v___x_3265_ = 1;
v___x_3266_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3129_, v___x_3265_);
if (v___x_3266_ == 0)
{
lean_dec_ref(v_opts_3264_);
v___y_3255_ = v___y_3259_;
v___y_3256_ = v___y_3259_;
v___y_3257_ = v___x_3266_;
goto v___jp_3254_;
}
else
{
lean_object* v___x_3267_; uint8_t v___x_3268_; 
v___x_3267_ = l_Lean_warningAsError;
v___x_3268_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_3264_, v___x_3267_);
lean_dec_ref(v_opts_3264_);
v___y_3255_ = v___y_3259_;
v___y_3256_ = v___y_3259_;
v___y_3257_ = v___x_3268_;
goto v___jp_3254_;
}
}
else
{
lean_object* v___x_3269_; lean_object* v___x_3270_; 
lean_dec_ref(v_msgData_3128_);
v___x_3269_ = lean_box(0);
v___x_3270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3269_);
return v___x_3270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___boxed(lean_object* v_ref_3273_, lean_object* v_msgData_3274_, lean_object* v_severity_3275_, lean_object* v_isSilent_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
uint8_t v_severity_boxed_3280_; uint8_t v_isSilent_boxed_3281_; lean_object* v_res_3282_; 
v_severity_boxed_3280_ = lean_unbox(v_severity_3275_);
v_isSilent_boxed_3281_ = lean_unbox(v_isSilent_3276_);
v_res_3282_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3273_, v_msgData_3274_, v_severity_boxed_3280_, v_isSilent_boxed_3281_, v___y_3277_, v___y_3278_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v_ref_3273_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(lean_object* v_ref_3283_, lean_object* v_msgData_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
uint8_t v___x_3288_; uint8_t v___x_3289_; lean_object* v___x_3290_; 
v___x_3288_ = 0;
v___x_3289_ = 0;
v___x_3290_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3283_, v_msgData_3284_, v___x_3288_, v___x_3289_, v___y_3285_, v___y_3286_);
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0___boxed(lean_object* v_ref_3291_, lean_object* v_msgData_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3291_, v_msgData_3292_, v___y_3293_, v___y_3294_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec(v_ref_3291_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(lean_object* v___x_3298_, lean_object* v_x_3299_){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3300_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___closed__0));
v___x_3301_ = lean_string_append(v___x_3300_, v___x_3298_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed(lean_object* v___x_3302_, lean_object* v_x_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(v___x_3302_, v_x_3303_);
lean_dec_ref(v_x_3303_);
lean_dec_ref(v___x_3302_);
return v_res_3304_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3306_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__0));
v___x_3307_ = l_Lean_stringToMessageData(v___x_3306_);
return v___x_3307_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3309_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__2));
v___x_3310_ = l_Lean_stringToMessageData(v___x_3309_);
return v___x_3310_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3312_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__4));
v___x_3313_ = l_Lean_stringToMessageData(v___x_3312_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(lean_object* v___x_3314_, uint8_t v___x_3315_, lean_object* v___x_3316_, lean_object* v_insertPos_3317_, lean_object* v_cmdLine_3318_, lean_object* v_ref_3319_, size_t v_sz_3320_, size_t v_i_3321_, lean_object* v_bs_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
uint8_t v___x_3326_; 
v___x_3326_ = lean_usize_dec_lt(v_i_3321_, v_sz_3320_);
if (v___x_3326_ == 0)
{
lean_object* v___x_3327_; 
lean_dec_ref(v___x_3316_);
lean_dec_ref(v___x_3314_);
v___x_3327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3327_, 0, v_bs_3322_);
return v___x_3327_;
}
else
{
lean_object* v_v_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v_v_3328_ = lean_array_uget(v_bs_3322_, v_i_3321_);
lean_inc(v_v_3328_);
v___x_3329_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppTactic___boxed), 4, 1);
lean_closure_set(v___x_3329_, 0, v_v_3328_);
v___x_3330_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_3329_, v___y_3323_, v___y_3324_);
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_object* v_a_3331_; lean_object* v___x_3332_; lean_object* v_bs_x27_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___f_3336_; lean_object* v___x_3337_; 
v_a_3331_ = lean_ctor_get(v___x_3330_, 0);
lean_inc(v_a_3331_);
lean_dec_ref_known(v___x_3330_, 1);
v___x_3332_ = lean_unsigned_to_nat(0u);
v_bs_x27_3333_ = lean_array_uset(v_bs_3322_, v_i_3321_, v___x_3332_);
v___x_3334_ = l_Std_Format_defWidth;
v___x_3335_ = l_Std_Format_pretty(v_a_3331_, v___x_3334_, v___x_3332_, v___x_3332_);
lean_inc_ref(v___x_3335_);
v___f_3336_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3336_, 0, v___x_3335_);
lean_inc_ref(v___x_3314_);
v___x_3337_ = lean_string_append(v___x_3314_, v___x_3335_);
lean_dec_ref(v___x_3335_);
if (v___x_3315_ == 0)
{
goto v___jp_3338_;
}
else
{
lean_object* v___x_3349_; lean_object* v_line_3350_; lean_object* v_column_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3386_; 
lean_inc_ref(v___x_3316_);
v___x_3349_ = l_Lean_FileMap_toPosition(v___x_3316_, v_insertPos_3317_);
v_line_3350_ = lean_ctor_get(v___x_3349_, 0);
v_column_3351_ = lean_ctor_get(v___x_3349_, 1);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3353_ = v___x_3349_;
v_isShared_3354_ = v_isSharedCheck_3386_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_column_3351_);
lean_inc(v_line_3350_);
lean_dec(v___x_3349_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3386_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3363_; 
v___x_3355_ = lean_nat_sub(v_line_3350_, v_cmdLine_3318_);
lean_dec(v_line_3350_);
v___x_3356_ = lean_unsigned_to_nat(1u);
v___x_3357_ = lean_nat_add(v___x_3355_, v___x_3356_);
lean_dec(v___x_3355_);
v___x_3358_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1);
lean_inc_ref(v___x_3337_);
v___x_3359_ = l_String_quote(v___x_3337_);
v___x_3360_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3359_);
v___x_3361_ = l_Lean_MessageData_ofFormat(v___x_3360_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set_tag(v___x_3353_, 7);
lean_ctor_set(v___x_3353_, 1, v___x_3361_);
lean_ctor_set(v___x_3353_, 0, v___x_3358_);
v___x_3363_ = v___x_3353_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3358_);
lean_ctor_set(v_reuseFailAlloc_3385_, 1, v___x_3361_);
v___x_3363_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3364_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3);
v___x_3365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3363_);
lean_ctor_set(v___x_3365_, 1, v___x_3364_);
v___x_3366_ = l_Nat_reprFast(v___x_3357_);
v___x_3367_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3366_);
v___x_3368_ = l_Lean_MessageData_ofFormat(v___x_3367_);
v___x_3369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3365_);
lean_ctor_set(v___x_3369_, 1, v___x_3368_);
v___x_3370_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5);
v___x_3371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3369_);
lean_ctor_set(v___x_3371_, 1, v___x_3370_);
v___x_3372_ = l_Nat_reprFast(v_column_3351_);
v___x_3373_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3372_);
v___x_3374_ = l_Lean_MessageData_ofFormat(v___x_3373_);
v___x_3375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3371_);
lean_ctor_set(v___x_3375_, 1, v___x_3374_);
v___x_3376_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3319_, v___x_3375_, v___y_3323_, v___y_3324_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_dec_ref_known(v___x_3376_, 1);
goto v___jp_3338_;
}
else
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
lean_dec_ref(v___x_3337_);
lean_dec_ref(v___f_3336_);
lean_dec_ref(v_bs_x27_3333_);
lean_dec(v_v_3328_);
lean_dec_ref(v___x_3316_);
lean_dec_ref(v___x_3314_);
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v___x_3376_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3376_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
}
}
v___jp_3338_:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; size_t v___x_3345_; size_t v___x_3346_; lean_object* v___x_3347_; 
v___x_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3337_);
v___x_3340_ = lean_box(0);
v___x_3341_ = l_Lean_MessageData_ofSyntax(v_v_3328_);
v___x_3342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3341_);
v___x_3343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3343_, 0, v___f_3336_);
v___x_3344_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3339_);
lean_ctor_set(v___x_3344_, 1, v___x_3340_);
lean_ctor_set(v___x_3344_, 2, v___x_3340_);
lean_ctor_set(v___x_3344_, 3, v___x_3340_);
lean_ctor_set(v___x_3344_, 4, v___x_3342_);
lean_ctor_set(v___x_3344_, 5, v___x_3343_);
v___x_3345_ = ((size_t)1ULL);
v___x_3346_ = lean_usize_add(v_i_3321_, v___x_3345_);
v___x_3347_ = lean_array_uset(v_bs_x27_3333_, v_i_3321_, v___x_3344_);
v_i_3321_ = v___x_3346_;
v_bs_3322_ = v___x_3347_;
goto _start;
}
}
else
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
lean_dec(v_v_3328_);
lean_dec_ref(v_bs_3322_);
lean_dec_ref(v___x_3316_);
lean_dec_ref(v___x_3314_);
v_a_3387_ = lean_ctor_get(v___x_3330_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3330_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v___x_3330_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3330_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3387_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___boxed(lean_object* v___x_3395_, lean_object* v___x_3396_, lean_object* v___x_3397_, lean_object* v_insertPos_3398_, lean_object* v_cmdLine_3399_, lean_object* v_ref_3400_, lean_object* v_sz_3401_, lean_object* v_i_3402_, lean_object* v_bs_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
uint8_t v___x_3850__boxed_3407_; size_t v_sz_boxed_3408_; size_t v_i_boxed_3409_; lean_object* v_res_3410_; 
v___x_3850__boxed_3407_ = lean_unbox(v___x_3396_);
v_sz_boxed_3408_ = lean_unbox_usize(v_sz_3401_);
lean_dec(v_sz_3401_);
v_i_boxed_3409_ = lean_unbox_usize(v_i_3402_);
lean_dec(v_i_3402_);
v_res_3410_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3395_, v___x_3850__boxed_3407_, v___x_3397_, v_insertPos_3398_, v_cmdLine_3399_, v_ref_3400_, v_sz_boxed_3408_, v_i_boxed_3409_, v_bs_3403_, v___y_3404_, v___y_3405_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec(v_ref_3400_);
lean_dec(v_cmdLine_3399_);
lean_dec(v_insertPos_3398_);
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(lean_object* v_tacticSeq_3411_, lean_object* v_ref_3412_, lean_object* v_insertPos_3413_, lean_object* v_suggs_3414_, lean_object* v_cmdLine_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_){
_start:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; uint8_t v___x_3421_; 
v___x_3419_ = lean_array_get_size(v_suggs_3414_);
v___x_3420_ = lean_unsigned_to_nat(0u);
v___x_3421_ = lean_nat_dec_eq(v___x_3419_, v___x_3420_);
if (v___x_3421_ == 0)
{
lean_object* v___x_3422_; lean_object* v_fileMap_3423_; lean_object* v_scopes_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v_opts_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; uint8_t v___x_3430_; size_t v_sz_3431_; size_t v___x_3432_; lean_object* v___x_3433_; 
v___x_3422_ = lean_st_ref_get(v_a_3417_);
v_fileMap_3423_ = lean_ctor_get(v_a_3416_, 1);
v_scopes_3424_ = lean_ctor_get(v___x_3422_, 2);
lean_inc(v_scopes_3424_);
lean_dec(v___x_3422_);
v___x_3425_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3426_ = l_List_head_x21___redArg(v___x_3425_, v_scopes_3424_);
lean_dec(v_scopes_3424_);
v_opts_3427_ = lean_ctor_get(v___x_3426_, 1);
lean_inc_ref(v_opts_3427_);
lean_dec(v___x_3426_);
lean_inc_ref_n(v_fileMap_3423_, 2);
v___x_3428_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(v_tacticSeq_3411_, v_fileMap_3423_);
v___x_3429_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_debug_autoTry_showEdits;
v___x_3430_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_3427_, v___x_3429_);
lean_dec_ref(v_opts_3427_);
v_sz_3431_ = lean_array_size(v_suggs_3414_);
v___x_3432_ = ((size_t)0ULL);
v___x_3433_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3428_, v___x_3430_, v_fileMap_3423_, v_insertPos_3413_, v_cmdLine_3415_, v_ref_3412_, v_sz_3431_, v___x_3432_, v_suggs_3414_, v_a_3416_, v_a_3417_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v_a_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; uint8_t v___x_3439_; lean_object* v___x_3440_; lean_object* v___y_3441_; lean_object* v___x_3442_; 
v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
lean_inc(v_a_3434_);
lean_dec_ref_known(v___x_3433_, 1);
v___x_3435_ = l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default;
v___x_3436_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx(v_insertPos_3413_);
v___x_3437_ = lean_array_get_size(v_a_3434_);
v___x_3438_ = lean_unsigned_to_nat(1u);
v___x_3439_ = lean_nat_dec_eq(v___x_3437_, v___x_3438_);
v___x_3440_ = lean_box(v___x_3439_);
v___y_3441_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed), 9, 6);
lean_closure_set(v___y_3441_, 0, v___x_3440_);
lean_closure_set(v___y_3441_, 1, v___x_3436_);
lean_closure_set(v___y_3441_, 2, v_ref_3412_);
lean_closure_set(v___y_3441_, 3, v_a_3434_);
lean_closure_set(v___y_3441_, 4, v___x_3435_);
lean_closure_set(v___y_3441_, 5, v___x_3420_);
v___x_3442_ = l_Lean_Elab_Command_liftCoreM___redArg(v___y_3441_, v_a_3416_, v_a_3417_);
return v___x_3442_;
}
else
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3450_; 
lean_dec(v_insertPos_3413_);
lean_dec(v_ref_3412_);
v_a_3443_ = lean_ctor_get(v___x_3433_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3445_ = v___x_3433_;
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___x_3433_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3448_; 
if (v_isShared_3446_ == 0)
{
v___x_3448_ = v___x_3445_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_a_3443_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
}
else
{
lean_object* v___x_3451_; lean_object* v___x_3452_; 
lean_dec_ref(v_suggs_3414_);
lean_dec(v_insertPos_3413_);
lean_dec(v_ref_3412_);
v___x_3451_ = lean_box(0);
v___x_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3451_);
return v___x_3452_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___boxed(lean_object* v_tacticSeq_3453_, lean_object* v_ref_3454_, lean_object* v_insertPos_3455_, lean_object* v_suggs_3456_, lean_object* v_cmdLine_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(v_tacticSeq_3453_, v_ref_3454_, v_insertPos_3455_, v_suggs_3456_, v_cmdLine_3457_, v_a_3458_, v_a_3459_);
lean_dec(v_a_3459_);
lean_dec_ref(v_a_3458_);
lean_dec(v_cmdLine_3457_);
lean_dec(v_tacticSeq_3453_);
return v_res_3461_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(lean_object* v_x_3462_){
_start:
{
uint8_t v___x_3463_; 
v___x_3463_ = 0;
return v___x_3463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0___boxed(lean_object* v_x_3464_){
_start:
{
uint8_t v_res_3465_; lean_object* v_r_3466_; 
v_res_3465_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(v_x_3464_);
lean_dec(v_x_3464_);
v_r_3466_ = lean_box(v_res_3465_);
return v_r_3466_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7(void){
_start:
{
lean_object* v___x_3483_; 
v___x_3483_ = l_Array_mkArray0(lean_box(0));
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(lean_object* v___f_3487_, lean_object* v_ref_3488_, lean_object* v_goal_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_){
_start:
{
lean_object* v_toCold_3495_; lean_object* v_currRecDepth_3496_; lean_object* v_ref_3497_; uint8_t v_diag_3498_; uint8_t v_suppressElabErrors_3499_; uint8_t v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; uint8_t v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v_ref_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v_toCold_3495_ = lean_ctor_get(v___y_3492_, 0);
v_currRecDepth_3496_ = lean_ctor_get(v___y_3492_, 1);
v_ref_3497_ = lean_ctor_get(v___y_3492_, 2);
v_diag_3498_ = lean_ctor_get_uint8(v___y_3492_, sizeof(void*)*3);
v_suppressElabErrors_3499_ = lean_ctor_get_uint8(v___y_3492_, sizeof(void*)*3 + 1);
v___x_3500_ = 0;
v___x_3501_ = l_Lean_SourceInfo_fromRef(v_ref_3497_, v___x_3500_);
v___x_3502_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__1));
v___x_3503_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__2));
lean_inc_n(v___x_3501_, 3);
v___x_3504_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3501_);
lean_ctor_set(v___x_3504_, 1, v___x_3503_);
v___x_3505_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__4));
v___x_3506_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__6));
v___x_3507_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7);
v___x_3508_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3508_, 0, v___x_3501_);
lean_ctor_set(v___x_3508_, 1, v___x_3506_);
lean_ctor_set(v___x_3508_, 2, v___x_3507_);
v___x_3509_ = l_Lean_Syntax_node1(v___x_3501_, v___x_3505_, v___x_3508_);
v___x_3510_ = l_Lean_Syntax_node2(v___x_3501_, v___x_3502_, v___x_3504_, v___x_3509_);
v___x_3511_ = lean_box(0);
v___x_3512_ = lean_box(0);
v___x_3513_ = 1;
v___x_3514_ = lean_box(1);
v___x_3515_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__5));
v___x_3516_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_3516_, 0, v___x_3511_);
lean_ctor_set(v___x_3516_, 1, v___x_3512_);
lean_ctor_set(v___x_3516_, 2, v___x_3511_);
lean_ctor_set(v___x_3516_, 3, v___f_3487_);
lean_ctor_set(v___x_3516_, 4, v___x_3514_);
lean_ctor_set(v___x_3516_, 5, v___x_3514_);
lean_ctor_set(v___x_3516_, 6, v___x_3511_);
lean_ctor_set(v___x_3516_, 7, v___x_3515_);
lean_ctor_set_uint8(v___x_3516_, sizeof(void*)*8, v___x_3513_);
lean_ctor_set_uint8(v___x_3516_, sizeof(void*)*8 + 1, v___x_3513_);
lean_ctor_set_uint8(v___x_3516_, sizeof(void*)*8 + 2, v___x_3513_);
lean_ctor_set_uint8(v___x_3516_, sizeof(void*)*8 + 3, v___x_3513_);
lean_ctor_set_uint8(v___x_3516_, sizeof(void*)*8 + 4, v___x_3500_);
lean_ctor_set_uint8(v___x_3516_, sizeof(void*)*8 + 5, v___x_3500_);
lean_ctor_set_uint8(v___x_3516_, sizeof(void*)*8 + 6, v___x_3500_);
lean_ctor_set_uint8(v___x_3516_, sizeof(void*)*8 + 7, v___x_3500_);
lean_ctor_set_uint8(v___x_3516_, sizeof(void*)*8 + 8, v___x_3513_);
lean_ctor_set_uint8(v___x_3516_, sizeof(void*)*8 + 9, v___x_3500_);
lean_ctor_set_uint8(v___x_3516_, sizeof(void*)*8 + 10, v___x_3513_);
v___x_3517_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__8));
v_ref_3518_ = l_Lean_replaceRef(v_ref_3488_, v_ref_3497_);
lean_inc(v_currRecDepth_3496_);
lean_inc_ref(v_toCold_3495_);
v___x_3519_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3519_, 0, v_toCold_3495_);
lean_ctor_set(v___x_3519_, 1, v_currRecDepth_3496_);
lean_ctor_set(v___x_3519_, 2, v_ref_3518_);
lean_ctor_set_uint8(v___x_3519_, sizeof(void*)*3, v_diag_3498_);
lean_ctor_set_uint8(v___x_3519_, sizeof(void*)*3 + 1, v_suppressElabErrors_3499_);
v___x_3520_ = l_Lean_Elab_runTactic(v_goal_3489_, v___x_3510_, v___x_3516_, v___x_3517_, v___y_3490_, v___y_3491_, v___x_3519_, v___y_3493_);
lean_dec_ref_known(v___x_3519_, 3);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3528_; 
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3528_ == 0)
{
lean_object* v_unused_3529_; 
v_unused_3529_ = lean_ctor_get(v___x_3520_, 0);
lean_dec(v_unused_3529_);
v___x_3522_ = v___x_3520_;
v_isShared_3523_ = v_isSharedCheck_3528_;
goto v_resetjp_3521_;
}
else
{
lean_dec(v___x_3520_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3528_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3524_; lean_object* v___x_3526_; 
v___x_3524_ = lean_box(0);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v___x_3524_);
v___x_3526_ = v___x_3522_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3524_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
else
{
lean_object* v_a_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3558_; 
v_a_3530_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3532_ = v___x_3520_;
v_isShared_3533_ = v_isSharedCheck_3558_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_a_3530_);
lean_dec(v___x_3520_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3558_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___x_3539_; uint8_t v___y_3541_; uint8_t v___y_3553_; uint8_t v___x_3556_; 
lean_inc(v_a_3530_);
v___x_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3539_, 0, v_a_3530_);
v___x_3556_ = l_Lean_Exception_isInterrupt(v_a_3530_);
if (v___x_3556_ == 0)
{
uint8_t v___x_3557_; 
lean_inc(v_a_3530_);
v___x_3557_ = l_Lean_Exception_isRuntime(v_a_3530_);
v___y_3553_ = v___x_3557_;
goto v___jp_3552_;
}
else
{
v___y_3553_ = v___x_3556_;
goto v___jp_3552_;
}
v___jp_3534_:
{
lean_object* v___x_3535_; lean_object* v___x_3537_; 
v___x_3535_ = lean_box(0);
if (v_isShared_3533_ == 0)
{
lean_ctor_set_tag(v___x_3532_, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3535_);
v___x_3537_ = v___x_3532_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3535_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
v___jp_3540_:
{
if (v___y_3541_ == 0)
{
lean_object* v_options_3542_; uint8_t v_hasTrace_3543_; 
lean_dec_ref_known(v___x_3539_, 1);
v_options_3542_ = lean_ctor_get(v_toCold_3495_, 2);
v_hasTrace_3543_ = lean_ctor_get_uint8(v_options_3542_, sizeof(void*)*1);
if (v_hasTrace_3543_ == 0)
{
lean_dec(v_a_3530_);
goto v___jp_3534_;
}
else
{
lean_object* v_inheritedTraceOptions_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; uint8_t v___x_3547_; 
v_inheritedTraceOptions_3544_ = lean_ctor_get(v_toCold_3495_, 11);
v___x_3545_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3546_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_3547_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3544_, v_options_3542_, v___x_3546_);
if (v___x_3547_ == 0)
{
lean_dec(v_a_3530_);
goto v___jp_3534_;
}
else
{
lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
lean_del_object(v___x_3532_);
v___x_3548_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_3549_ = l_Lean_Exception_toMessageData(v_a_3530_);
v___x_3550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3548_);
lean_ctor_set(v___x_3550_, 1, v___x_3549_);
v___x_3551_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_3545_, v___x_3550_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
return v___x_3551_;
}
}
}
else
{
lean_del_object(v___x_3532_);
lean_dec(v_a_3530_);
return v___x_3539_;
}
}
v___jp_3552_:
{
if (v___y_3553_ == 0)
{
uint8_t v___x_3554_; 
v___x_3554_ = l_Lean_Exception_isInterrupt(v_a_3530_);
if (v___x_3554_ == 0)
{
uint8_t v___x_3555_; 
lean_inc(v_a_3530_);
v___x_3555_ = l_Lean_Exception_isMaxRecDepth(v_a_3530_);
v___y_3541_ = v___x_3555_;
goto v___jp_3540_;
}
else
{
v___y_3541_ = v___x_3554_;
goto v___jp_3540_;
}
}
else
{
lean_del_object(v___x_3532_);
lean_dec(v_a_3530_);
return v___x_3539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___boxed(lean_object* v___f_3559_, lean_object* v_ref_3560_, lean_object* v_goal_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(v___f_3559_, v_ref_3560_, v_goal_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
lean_dec(v_ref_3560_);
return v_res_3567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(lean_object* v_c_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_){
_start:
{
lean_object* v_mctx_3573_; lean_object* v_ref_3574_; lean_object* v_env_3575_; lean_object* v_opts_3576_; lean_object* v_namingCtx_3577_; lean_object* v_goal_3578_; lean_object* v_decls_3579_; lean_object* v___x_3580_; 
v_mctx_3573_ = lean_ctor_get(v_c_3569_, 3);
lean_inc_ref(v_mctx_3573_);
v_ref_3574_ = lean_ctor_get(v_c_3569_, 1);
lean_inc(v_ref_3574_);
v_env_3575_ = lean_ctor_get(v_c_3569_, 2);
lean_inc_ref(v_env_3575_);
v_opts_3576_ = lean_ctor_get(v_c_3569_, 4);
lean_inc_ref(v_opts_3576_);
v_namingCtx_3577_ = lean_ctor_get(v_c_3569_, 5);
lean_inc_ref(v_namingCtx_3577_);
v_goal_3578_ = lean_ctor_get(v_c_3569_, 6);
lean_inc(v_goal_3578_);
lean_dec_ref(v_c_3569_);
v_decls_3579_ = lean_ctor_get(v_mctx_3573_, 5);
v___x_3580_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_decls_3579_, v_goal_3578_);
if (lean_obj_tag(v___x_3580_) == 1)
{
lean_object* v_val_3581_; lean_object* v_lctx_3582_; lean_object* v___f_3583_; lean_object* v___f_3584_; lean_object* v___x_3585_; 
v_val_3581_ = lean_ctor_get(v___x_3580_, 0);
lean_inc(v_val_3581_);
lean_dec_ref_known(v___x_3580_, 1);
v_lctx_3582_ = lean_ctor_get(v_val_3581_, 1);
lean_inc_ref(v_lctx_3582_);
lean_dec(v_val_3581_);
v___f_3583_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___closed__0));
v___f_3584_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___boxed), 8, 3);
lean_closure_set(v___f_3584_, 0, v___f_3583_);
lean_closure_set(v___f_3584_, 1, v_ref_3574_);
lean_closure_set(v___f_3584_, 2, v_goal_3578_);
v___x_3585_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_3575_, v_mctx_3573_, v_lctx_3582_, v_opts_3576_, v_namingCtx_3577_, v___f_3584_, v_a_3570_, v_a_3571_);
lean_dec_ref(v_namingCtx_3577_);
return v___x_3585_;
}
else
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
lean_dec(v___x_3580_);
lean_dec(v_goal_3578_);
lean_dec_ref(v_namingCtx_3577_);
lean_dec_ref(v_opts_3576_);
lean_dec_ref(v_env_3575_);
lean_dec(v_ref_3574_);
lean_dec_ref(v_mctx_3573_);
v___x_3586_ = lean_box(0);
v___x_3587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3586_);
return v___x_3587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___boxed(lean_object* v_c_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_){
_start:
{
lean_object* v_res_3592_; 
v_res_3592_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(v_c_3588_, v_a_3589_, v_a_3590_);
lean_dec(v_a_3590_);
lean_dec_ref(v_a_3589_);
return v_res_3592_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(lean_object* v___x_3593_, lean_object* v_val_3594_, lean_object* v_as_3595_, size_t v_i_3596_, size_t v_stop_3597_){
_start:
{
uint8_t v___x_3602_; uint8_t v___x_3603_; 
v___x_3602_ = 0;
v___x_3603_ = lean_usize_dec_eq(v_i_3596_, v_stop_3597_);
if (v___x_3603_ == 0)
{
lean_object* v___x_3604_; lean_object* v_pos_3605_; uint8_t v_severity_3606_; lean_object* v_data_3607_; lean_object* v___f_3608_; uint8_t v___x_3609_; lean_object* v___x_3610_; uint8_t v___x_3611_; uint8_t v___y_3613_; 
v___x_3604_ = lean_array_uget_borrowed(v_as_3595_, v_i_3596_);
v_pos_3605_ = lean_ctor_get(v___x_3604_, 1);
v_severity_3606_ = lean_ctor_get_uint8(v___x_3604_, sizeof(void*)*5 + 1);
v_data_3607_ = lean_ctor_get(v___x_3604_, 4);
v___f_3608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
v___x_3609_ = 1;
lean_inc_ref(v_pos_3605_);
v___x_3610_ = l_Lean_FileMap_ofPosition(v___x_3593_, v_pos_3605_);
v___x_3611_ = l_Lean_Syntax_Range_contains(v_val_3594_, v___x_3610_, v___x_3609_);
lean_dec(v___x_3610_);
if (v_severity_3606_ == 2)
{
v___y_3613_ = v___x_3609_;
goto v___jp_3612_;
}
else
{
v___y_3613_ = v___x_3602_;
goto v___jp_3612_;
}
v___jp_3612_:
{
if (v___x_3611_ == 0)
{
goto v___jp_3598_;
}
else
{
if (v___y_3613_ == 0)
{
goto v___jp_3598_;
}
else
{
uint8_t v___x_3614_; 
lean_inc(v_data_3607_);
v___x_3614_ = l_Lean_MessageData_hasTag(v___f_3608_, v_data_3607_);
if (v___x_3614_ == 0)
{
return v___x_3609_;
}
else
{
goto v___jp_3598_;
}
}
}
}
}
else
{
return v___x_3602_;
}
v___jp_3598_:
{
size_t v___x_3599_; size_t v___x_3600_; 
v___x_3599_ = ((size_t)1ULL);
v___x_3600_ = lean_usize_add(v_i_3596_, v___x_3599_);
v_i_3596_ = v___x_3600_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1___boxed(lean_object* v___x_3615_, lean_object* v_val_3616_, lean_object* v_as_3617_, lean_object* v_i_3618_, lean_object* v_stop_3619_){
_start:
{
size_t v_i_boxed_3620_; size_t v_stop_boxed_3621_; uint8_t v_res_3622_; lean_object* v_r_3623_; 
v_i_boxed_3620_ = lean_unbox_usize(v_i_3618_);
lean_dec(v_i_3618_);
v_stop_boxed_3621_ = lean_unbox_usize(v_stop_3619_);
lean_dec(v_stop_3619_);
v_res_3622_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3615_, v_val_3616_, v_as_3617_, v_i_boxed_3620_, v_stop_boxed_3621_);
lean_dec_ref(v_as_3617_);
lean_dec_ref(v_val_3616_);
lean_dec_ref(v___x_3615_);
v_r_3623_ = lean_box(v_res_3622_);
return v_r_3623_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(lean_object* v___x_3624_, lean_object* v_val_3625_, lean_object* v_x_3626_){
_start:
{
if (lean_obj_tag(v_x_3626_) == 0)
{
lean_object* v_cs_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; uint8_t v___x_3630_; 
v_cs_3627_ = lean_ctor_get(v_x_3626_, 0);
v___x_3628_ = lean_unsigned_to_nat(0u);
v___x_3629_ = lean_array_get_size(v_cs_3627_);
v___x_3630_ = lean_nat_dec_lt(v___x_3628_, v___x_3629_);
if (v___x_3630_ == 0)
{
return v___x_3630_;
}
else
{
if (v___x_3630_ == 0)
{
return v___x_3630_;
}
else
{
size_t v___x_3631_; size_t v___x_3632_; uint8_t v___x_3633_; 
v___x_3631_ = ((size_t)0ULL);
v___x_3632_ = lean_usize_of_nat(v___x_3629_);
v___x_3633_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3624_, v_val_3625_, v_cs_3627_, v___x_3631_, v___x_3632_);
return v___x_3633_;
}
}
}
else
{
lean_object* v_vs_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; uint8_t v___x_3637_; 
v_vs_3634_ = lean_ctor_get(v_x_3626_, 0);
v___x_3635_ = lean_unsigned_to_nat(0u);
v___x_3636_ = lean_array_get_size(v_vs_3634_);
v___x_3637_ = lean_nat_dec_lt(v___x_3635_, v___x_3636_);
if (v___x_3637_ == 0)
{
return v___x_3637_;
}
else
{
if (v___x_3637_ == 0)
{
return v___x_3637_;
}
else
{
size_t v___x_3638_; size_t v___x_3639_; uint8_t v___x_3640_; 
v___x_3638_ = ((size_t)0ULL);
v___x_3639_ = lean_usize_of_nat(v___x_3636_);
v___x_3640_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3624_, v_val_3625_, v_vs_3634_, v___x_3638_, v___x_3639_);
return v___x_3640_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(lean_object* v___x_3641_, lean_object* v_val_3642_, lean_object* v_as_3643_, size_t v_i_3644_, size_t v_stop_3645_){
_start:
{
uint8_t v___x_3646_; 
v___x_3646_ = lean_usize_dec_eq(v_i_3644_, v_stop_3645_);
if (v___x_3646_ == 0)
{
lean_object* v___x_3647_; uint8_t v___x_3648_; 
v___x_3647_ = lean_array_uget_borrowed(v_as_3643_, v_i_3644_);
v___x_3648_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3641_, v_val_3642_, v___x_3647_);
if (v___x_3648_ == 0)
{
size_t v___x_3649_; size_t v___x_3650_; 
v___x_3649_ = ((size_t)1ULL);
v___x_3650_ = lean_usize_add(v_i_3644_, v___x_3649_);
v_i_3644_ = v___x_3650_;
goto _start;
}
else
{
return v___x_3648_;
}
}
else
{
uint8_t v___x_3652_; 
v___x_3652_ = 0;
return v___x_3652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3653_, lean_object* v_val_3654_, lean_object* v_as_3655_, lean_object* v_i_3656_, lean_object* v_stop_3657_){
_start:
{
size_t v_i_boxed_3658_; size_t v_stop_boxed_3659_; uint8_t v_res_3660_; lean_object* v_r_3661_; 
v_i_boxed_3658_ = lean_unbox_usize(v_i_3656_);
lean_dec(v_i_3656_);
v_stop_boxed_3659_ = lean_unbox_usize(v_stop_3657_);
lean_dec(v_stop_3657_);
v_res_3660_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3653_, v_val_3654_, v_as_3655_, v_i_boxed_3658_, v_stop_boxed_3659_);
lean_dec_ref(v_as_3655_);
lean_dec_ref(v_val_3654_);
lean_dec_ref(v___x_3653_);
v_r_3661_ = lean_box(v_res_3660_);
return v_r_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0___boxed(lean_object* v___x_3662_, lean_object* v_val_3663_, lean_object* v_x_3664_){
_start:
{
uint8_t v_res_3665_; lean_object* v_r_3666_; 
v_res_3665_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3662_, v_val_3663_, v_x_3664_);
lean_dec_ref(v_x_3664_);
lean_dec_ref(v_val_3663_);
lean_dec_ref(v___x_3662_);
v_r_3666_ = lean_box(v_res_3665_);
return v_r_3666_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(lean_object* v___x_3667_, lean_object* v_val_3668_, lean_object* v_t_3669_){
_start:
{
lean_object* v_root_3670_; lean_object* v_tail_3671_; uint8_t v___x_3672_; 
v_root_3670_ = lean_ctor_get(v_t_3669_, 0);
v_tail_3671_ = lean_ctor_get(v_t_3669_, 1);
v___x_3672_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3667_, v_val_3668_, v_root_3670_);
if (v___x_3672_ == 0)
{
lean_object* v___x_3673_; lean_object* v___x_3674_; uint8_t v___x_3675_; 
v___x_3673_ = lean_unsigned_to_nat(0u);
v___x_3674_ = lean_array_get_size(v_tail_3671_);
v___x_3675_ = lean_nat_dec_lt(v___x_3673_, v___x_3674_);
if (v___x_3675_ == 0)
{
return v___x_3675_;
}
else
{
if (v___x_3675_ == 0)
{
return v___x_3675_;
}
else
{
size_t v___x_3676_; size_t v___x_3677_; uint8_t v___x_3678_; 
v___x_3676_ = ((size_t)0ULL);
v___x_3677_ = lean_usize_of_nat(v___x_3674_);
v___x_3678_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3667_, v_val_3668_, v_tail_3671_, v___x_3676_, v___x_3677_);
return v___x_3678_;
}
}
}
else
{
return v___x_3672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0___boxed(lean_object* v___x_3679_, lean_object* v_val_3680_, lean_object* v_t_3681_){
_start:
{
uint8_t v_res_3682_; lean_object* v_r_3683_; 
v_res_3682_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v___x_3679_, v_val_3680_, v_t_3681_);
lean_dec_ref(v_t_3681_);
lean_dec_ref(v_val_3680_);
lean_dec_ref(v___x_3679_);
v_r_3683_ = lean_box(v_res_3682_);
return v_r_3683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(lean_object* v_stx_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_){
_start:
{
uint8_t v___x_3688_; lean_object* v___x_3689_; 
v___x_3688_ = 0;
v___x_3689_ = l_Lean_Syntax_getRange_x3f(v_stx_3684_, v___x_3688_);
if (lean_obj_tag(v___x_3689_) == 1)
{
lean_object* v_val_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3703_; 
v_val_3690_ = lean_ctor_get(v___x_3689_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3689_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3692_ = v___x_3689_;
v_isShared_3693_ = v_isSharedCheck_3703_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_val_3690_);
lean_dec(v___x_3689_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3703_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3694_; lean_object* v_fileMap_3695_; lean_object* v_messages_3696_; lean_object* v___x_3697_; uint8_t v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3701_; 
v___x_3694_ = lean_st_ref_get(v_a_3686_);
v_fileMap_3695_ = lean_ctor_get(v_a_3685_, 1);
v_messages_3696_ = lean_ctor_get(v___x_3694_, 1);
lean_inc_ref(v_messages_3696_);
lean_dec(v___x_3694_);
v___x_3697_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_3696_);
v___x_3698_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v_fileMap_3695_, v_val_3690_, v___x_3697_);
lean_dec_ref(v___x_3697_);
lean_dec(v_val_3690_);
v___x_3699_ = lean_box(v___x_3698_);
if (v_isShared_3693_ == 0)
{
lean_ctor_set_tag(v___x_3692_, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3699_);
v___x_3701_ = v___x_3692_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v___x_3699_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
else
{
lean_object* v___x_3704_; lean_object* v___x_3705_; 
lean_dec(v___x_3689_);
v___x_3704_ = lean_box(v___x_3688_);
v___x_3705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3704_);
return v___x_3705_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError___boxed(lean_object* v_stx_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(v_stx_3706_, v_a_3707_, v_a_3708_);
lean_dec(v_a_3708_);
lean_dec_ref(v_a_3707_);
lean_dec(v_stx_3706_);
return v_res_3710_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(lean_object* v_tree_3711_, lean_object* v_fileMap_3712_, lean_object* v_c_3713_){
_start:
{
lean_object* v___y_3715_; lean_object* v_kind_3719_; lean_object* v_ref_3720_; lean_object* v___y_3722_; 
v_kind_3719_ = lean_ctor_get(v_c_3713_, 0);
lean_inc(v_kind_3719_);
v_ref_3720_ = lean_ctor_get(v_c_3713_, 1);
lean_inc(v_ref_3720_);
lean_dec_ref(v_c_3713_);
if (lean_obj_tag(v_kind_3719_) == 0)
{
lean_object* v_insertPos_3738_; 
lean_dec(v_ref_3720_);
v_insertPos_3738_ = lean_ctor_get(v_kind_3719_, 1);
lean_inc(v_insertPos_3738_);
v___y_3722_ = v_insertPos_3738_;
goto v___jp_3721_;
}
else
{
uint8_t v___x_3739_; lean_object* v___x_3740_; 
v___x_3739_ = 0;
v___x_3740_ = l_Lean_Syntax_getPos_x3f(v_ref_3720_, v___x_3739_);
lean_dec(v_ref_3720_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v___x_3741_; 
v___x_3741_ = lean_unsigned_to_nat(0u);
v___y_3722_ = v___x_3741_;
goto v___jp_3721_;
}
else
{
lean_object* v_val_3742_; 
v_val_3742_ = lean_ctor_get(v___x_3740_, 0);
lean_inc(v_val_3742_);
lean_dec_ref_known(v___x_3740_, 1);
v___y_3722_ = v_val_3742_;
goto v___jp_3721_;
}
}
v___jp_3714_:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; uint8_t v___x_3718_; 
v___x_3716_ = l_List_lengthTR___redArg(v___y_3715_);
lean_dec(v___y_3715_);
v___x_3717_ = lean_unsigned_to_nat(1u);
v___x_3718_ = lean_nat_dec_eq(v___x_3716_, v___x_3717_);
lean_dec(v___x_3716_);
return v___x_3718_;
}
v___jp_3721_:
{
lean_object* v___x_3723_; 
v___x_3723_ = l_Lean_Elab_InfoTree_goalsAt_x3f(v_fileMap_3712_, v_tree_3711_, v___y_3722_);
if (lean_obj_tag(v___x_3723_) == 1)
{
lean_object* v_tail_3724_; 
v_tail_3724_ = lean_ctor_get(v___x_3723_, 1);
lean_inc(v_tail_3724_);
if (lean_obj_tag(v_tail_3724_) == 0)
{
if (lean_obj_tag(v_kind_3719_) == 0)
{
lean_object* v_head_3725_; lean_object* v_tacticSeq_3726_; uint8_t v___x_3727_; lean_object* v___x_3728_; 
v_head_3725_ = lean_ctor_get(v___x_3723_, 0);
lean_inc(v_head_3725_);
lean_dec_ref_known(v___x_3723_, 2);
v_tacticSeq_3726_ = lean_ctor_get(v_kind_3719_, 0);
lean_inc(v_tacticSeq_3726_);
lean_dec_ref_known(v_kind_3719_, 2);
v___x_3727_ = 0;
v___x_3728_ = l_Lean_Syntax_getPos_x3f(v_tacticSeq_3726_, v___x_3727_);
lean_dec(v_tacticSeq_3726_);
if (lean_obj_tag(v___x_3728_) == 0)
{
lean_object* v_tacticInfo_3729_; lean_object* v_goalsBefore_3730_; 
v_tacticInfo_3729_ = lean_ctor_get(v_head_3725_, 1);
lean_inc_ref(v_tacticInfo_3729_);
lean_dec(v_head_3725_);
v_goalsBefore_3730_ = lean_ctor_get(v_tacticInfo_3729_, 2);
lean_inc(v_goalsBefore_3730_);
lean_dec_ref(v_tacticInfo_3729_);
v___y_3715_ = v_goalsBefore_3730_;
goto v___jp_3714_;
}
else
{
lean_object* v_tacticInfo_3731_; lean_object* v_goalsAfter_3732_; 
lean_dec_ref_known(v___x_3728_, 1);
v_tacticInfo_3731_ = lean_ctor_get(v_head_3725_, 1);
lean_inc_ref(v_tacticInfo_3731_);
lean_dec(v_head_3725_);
v_goalsAfter_3732_ = lean_ctor_get(v_tacticInfo_3731_, 4);
lean_inc(v_goalsAfter_3732_);
lean_dec_ref(v_tacticInfo_3731_);
v___y_3715_ = v_goalsAfter_3732_;
goto v___jp_3714_;
}
}
else
{
lean_object* v_head_3733_; lean_object* v_tacticInfo_3734_; lean_object* v_goalsBefore_3735_; 
v_head_3733_ = lean_ctor_get(v___x_3723_, 0);
lean_inc(v_head_3733_);
lean_dec_ref_known(v___x_3723_, 2);
v_tacticInfo_3734_ = lean_ctor_get(v_head_3733_, 1);
lean_inc_ref(v_tacticInfo_3734_);
lean_dec(v_head_3733_);
v_goalsBefore_3735_ = lean_ctor_get(v_tacticInfo_3734_, 2);
lean_inc(v_goalsBefore_3735_);
lean_dec_ref(v_tacticInfo_3734_);
v___y_3715_ = v_goalsBefore_3735_;
goto v___jp_3714_;
}
}
else
{
uint8_t v___x_3736_; 
lean_dec(v_tail_3724_);
lean_dec_ref_known(v___x_3723_, 2);
lean_dec(v_kind_3719_);
v___x_3736_ = 0;
return v___x_3736_;
}
}
else
{
uint8_t v___x_3737_; 
lean_dec(v___x_3723_);
lean_dec(v_kind_3719_);
v___x_3737_ = 0;
return v___x_3737_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos___boxed(lean_object* v_tree_3743_, lean_object* v_fileMap_3744_, lean_object* v_c_3745_){
_start:
{
uint8_t v_res_3746_; lean_object* v_r_3747_; 
v_res_3746_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(v_tree_3743_, v_fileMap_3744_, v_c_3745_);
v_r_3747_ = lean_box(v_res_3746_);
return v_r_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(lean_object* v___y_3748_){
_start:
{
lean_object* v___x_3750_; lean_object* v_infoState_3751_; lean_object* v_trees_3752_; lean_object* v___x_3753_; 
v___x_3750_ = lean_st_ref_get(v___y_3748_);
v_infoState_3751_ = lean_ctor_get(v___x_3750_, 8);
lean_inc_ref(v_infoState_3751_);
lean_dec(v___x_3750_);
v_trees_3752_ = lean_ctor_get(v_infoState_3751_, 2);
lean_inc_ref(v_trees_3752_);
lean_dec_ref(v_infoState_3751_);
v___x_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3753_, 0, v_trees_3752_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg___boxed(lean_object* v___y_3754_, lean_object* v___y_3755_){
_start:
{
lean_object* v_res_3756_; 
v_res_3756_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_3754_);
lean_dec(v___y_3754_);
return v_res_3756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(lean_object* v___y_3757_, lean_object* v___y_3758_){
_start:
{
lean_object* v___x_3760_; 
v___x_3760_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_3758_);
return v___x_3760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___boxed(lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_){
_start:
{
lean_object* v_res_3764_; 
v_res_3764_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(v___y_3761_, v___y_3762_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
return v_res_3764_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3766_; lean_object* v___x_3767_; 
v___x_3766_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__0));
v___x_3767_ = l_Lean_stringToMessageData(v___x_3766_);
return v___x_3767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(lean_object* v_tree_3768_, lean_object* v___x_3769_, lean_object* v___x_3770_, lean_object* v_as_3771_, size_t v_sz_3772_, size_t v_i_3773_, lean_object* v_b_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_){
_start:
{
lean_object* v_a_3779_; uint8_t v___x_3783_; 
v___x_3783_ = lean_usize_dec_lt(v_i_3773_, v_sz_3772_);
if (v___x_3783_ == 0)
{
lean_object* v___x_3784_; 
lean_dec_ref(v___x_3769_);
lean_dec_ref(v_tree_3768_);
v___x_3784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3784_, 0, v_b_3774_);
return v___x_3784_;
}
else
{
lean_object* v___x_3785_; lean_object* v_a_3786_; uint8_t v___x_3787_; 
v___x_3785_ = lean_box(0);
v_a_3786_ = lean_array_uget_borrowed(v_as_3771_, v_i_3773_);
lean_inc(v_a_3786_);
lean_inc_ref(v___x_3769_);
lean_inc_ref(v_tree_3768_);
v___x_3787_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(v_tree_3768_, v___x_3769_, v_a_3786_);
if (v___x_3787_ == 0)
{
lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v_scopes_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v_opts_3794_; uint8_t v_hasTrace_3795_; 
v___x_3788_ = l_Lean_inheritedTraceOptions;
v___x_3789_ = lean_st_ref_get(v___x_3788_);
v___x_3790_ = lean_st_ref_get(v___y_3776_);
v_scopes_3791_ = lean_ctor_get(v___x_3790_, 2);
lean_inc(v_scopes_3791_);
lean_dec(v___x_3790_);
v___x_3792_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3793_ = l_List_head_x21___redArg(v___x_3792_, v_scopes_3791_);
lean_dec(v_scopes_3791_);
v_opts_3794_ = lean_ctor_get(v___x_3793_, 1);
lean_inc_ref(v_opts_3794_);
lean_dec(v___x_3793_);
v_hasTrace_3795_ = lean_ctor_get_uint8(v_opts_3794_, sizeof(void*)*1);
if (v_hasTrace_3795_ == 0)
{
lean_dec_ref(v_opts_3794_);
lean_dec(v___x_3789_);
v_a_3779_ = v___x_3785_;
goto v___jp_3778_;
}
else
{
lean_object* v___x_3796_; lean_object* v___x_3797_; uint8_t v___x_3798_; 
v___x_3796_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3797_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_3798_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3789_, v_opts_3794_, v___x_3797_);
lean_dec_ref(v_opts_3794_);
lean_dec(v___x_3789_);
if (v___x_3798_ == 0)
{
v_a_3779_ = v___x_3785_;
goto v___jp_3778_;
}
else
{
lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3799_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1);
v___x_3800_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_3796_, v___x_3799_, v___y_3775_, v___y_3776_);
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_dec_ref_known(v___x_3800_, 1);
v_a_3779_ = v___x_3785_;
goto v___jp_3778_;
}
else
{
lean_dec_ref(v___x_3769_);
lean_dec_ref(v_tree_3768_);
return v___x_3800_;
}
}
}
}
else
{
lean_object* v_kind_3801_; 
v_kind_3801_ = lean_ctor_get(v_a_3786_, 0);
if (lean_obj_tag(v_kind_3801_) == 0)
{
lean_object* v_ref_3802_; lean_object* v_tacticSeq_3803_; lean_object* v_insertPos_3804_; lean_object* v___x_3805_; 
v_ref_3802_ = lean_ctor_get(v_a_3786_, 1);
v_tacticSeq_3803_ = lean_ctor_get(v_kind_3801_, 0);
v_insertPos_3804_ = lean_ctor_get(v_kind_3801_, 1);
lean_inc(v_a_3786_);
v___x_3805_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(v_a_3786_, v___y_3775_, v___y_3776_);
if (lean_obj_tag(v___x_3805_) == 0)
{
lean_object* v_a_3806_; lean_object* v___x_3807_; 
v_a_3806_ = lean_ctor_get(v___x_3805_, 0);
lean_inc(v_a_3806_);
lean_dec_ref_known(v___x_3805_, 1);
lean_inc(v_insertPos_3804_);
lean_inc(v_ref_3802_);
v___x_3807_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(v_tacticSeq_3803_, v_ref_3802_, v_insertPos_3804_, v_a_3806_, v___x_3770_, v___y_3775_, v___y_3776_);
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_dec_ref_known(v___x_3807_, 1);
v_a_3779_ = v___x_3785_;
goto v___jp_3778_;
}
else
{
lean_dec_ref(v___x_3769_);
lean_dec_ref(v_tree_3768_);
return v___x_3807_;
}
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
lean_dec_ref(v___x_3769_);
lean_dec_ref(v_tree_3768_);
v_a_3808_ = lean_ctor_get(v___x_3805_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3805_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3805_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
else
{
lean_object* v___x_3816_; 
lean_inc(v_a_3786_);
v___x_3816_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(v_a_3786_, v___y_3775_, v___y_3776_);
if (lean_obj_tag(v___x_3816_) == 0)
{
lean_dec_ref_known(v___x_3816_, 1);
v_a_3779_ = v___x_3785_;
goto v___jp_3778_;
}
else
{
lean_dec_ref(v___x_3769_);
lean_dec_ref(v_tree_3768_);
return v___x_3816_;
}
}
}
}
v___jp_3778_:
{
size_t v___x_3780_; size_t v___x_3781_; 
v___x_3780_ = ((size_t)1ULL);
v___x_3781_ = lean_usize_add(v_i_3773_, v___x_3780_);
v_i_3773_ = v___x_3781_;
v_b_3774_ = v_a_3779_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___boxed(lean_object* v_tree_3817_, lean_object* v___x_3818_, lean_object* v___x_3819_, lean_object* v_as_3820_, lean_object* v_sz_3821_, lean_object* v_i_3822_, lean_object* v_b_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_){
_start:
{
size_t v_sz_boxed_3827_; size_t v_i_boxed_3828_; lean_object* v_res_3829_; 
v_sz_boxed_3827_ = lean_unbox_usize(v_sz_3821_);
lean_dec(v_sz_3821_);
v_i_boxed_3828_ = lean_unbox_usize(v_i_3822_);
lean_dec(v_i_3822_);
v_res_3829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_tree_3817_, v___x_3818_, v___x_3819_, v_as_3820_, v_sz_boxed_3827_, v_i_boxed_3828_, v_b_3823_, v___y_3824_, v___y_3825_);
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
lean_dec_ref(v_as_3820_);
lean_dec(v___x_3819_);
return v_res_3829_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; 
v___x_3834_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__1));
v___x_3835_ = l_Lean_stringToMessageData(v___x_3834_);
return v___x_3835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(lean_object* v_stx_3836_, lean_object* v___x_3837_, lean_object* v___x_3838_, lean_object* v___x_3839_, lean_object* v___x_3840_, lean_object* v_as_3841_, size_t v_sz_3842_, size_t v_i_3843_, lean_object* v_b_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_){
_start:
{
uint8_t v___x_3848_; 
v___x_3848_ = lean_usize_dec_lt(v_i_3843_, v_sz_3842_);
if (v___x_3848_ == 0)
{
lean_object* v___x_3849_; 
lean_dec_ref(v___x_3839_);
lean_dec(v_stx_3836_);
v___x_3849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3849_, 0, v_b_3844_);
return v___x_3849_;
}
else
{
lean_object* v_a_3850_; lean_object* v___x_3851_; 
lean_dec_ref(v_b_3844_);
v_a_3850_ = lean_array_uget_borrowed(v_as_3841_, v_i_3843_);
lean_inc(v_a_3850_);
lean_inc(v_stx_3836_);
v___x_3851_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3836_, v___x_3837_, v_a_3850_, v___x_3838_, v___y_3845_, v___y_3846_);
if (lean_obj_tag(v___x_3851_) == 0)
{
lean_object* v_a_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v_scopes_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v_opts_3859_; uint8_t v_hasTrace_3860_; lean_object* v___x_3861_; lean_object* v___y_3863_; lean_object* v___y_3864_; 
v_a_3852_ = lean_ctor_get(v___x_3851_, 0);
lean_inc(v_a_3852_);
lean_dec_ref_known(v___x_3851_, 1);
v___x_3853_ = l_Lean_inheritedTraceOptions;
v___x_3854_ = lean_st_ref_get(v___x_3853_);
v___x_3855_ = lean_st_ref_get(v___y_3846_);
v_scopes_3856_ = lean_ctor_get(v___x_3855_, 2);
lean_inc(v_scopes_3856_);
lean_dec(v___x_3855_);
v___x_3857_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3858_ = l_List_head_x21___redArg(v___x_3857_, v_scopes_3856_);
lean_dec(v_scopes_3856_);
v_opts_3859_ = lean_ctor_get(v___x_3858_, 1);
lean_inc_ref(v_opts_3859_);
lean_dec(v___x_3858_);
v_hasTrace_3860_ = lean_ctor_get_uint8(v_opts_3859_, sizeof(void*)*1);
v___x_3861_ = lean_box(0);
if (v_hasTrace_3860_ == 0)
{
lean_dec_ref(v_opts_3859_);
lean_dec(v___x_3854_);
v___y_3863_ = v___y_3845_;
v___y_3864_ = v___y_3846_;
goto v___jp_3862_;
}
else
{
lean_object* v___x_3880_; lean_object* v___x_3881_; uint8_t v___x_3882_; 
v___x_3880_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3881_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_3882_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3854_, v_opts_3859_, v___x_3881_);
lean_dec_ref(v_opts_3859_);
lean_dec(v___x_3854_);
if (v___x_3882_ == 0)
{
v___y_3863_ = v___y_3845_;
v___y_3864_ = v___y_3846_;
goto v___jp_3862_;
}
else
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; 
v___x_3883_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_3884_ = lean_array_get_size(v_a_3852_);
v___x_3885_ = l_Nat_reprFast(v___x_3884_);
v___x_3886_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3885_);
v___x_3887_ = l_Lean_MessageData_ofFormat(v___x_3886_);
v___x_3888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3883_);
lean_ctor_set(v___x_3888_, 1, v___x_3887_);
v___x_3889_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_3880_, v___x_3888_, v___y_3845_, v___y_3846_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_dec_ref_known(v___x_3889_, 1);
v___y_3863_ = v___y_3845_;
v___y_3864_ = v___y_3846_;
goto v___jp_3862_;
}
else
{
lean_object* v_a_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3897_; 
lean_dec(v_a_3852_);
lean_dec_ref(v___x_3839_);
lean_dec(v_stx_3836_);
v_a_3890_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_3897_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3892_ = v___x_3889_;
v_isShared_3893_ = v_isSharedCheck_3897_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_a_3890_);
lean_dec(v___x_3889_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3897_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
lean_object* v___x_3895_; 
if (v_isShared_3893_ == 0)
{
v___x_3895_ = v___x_3892_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v_a_3890_);
v___x_3895_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
return v___x_3895_;
}
}
}
}
}
v___jp_3862_:
{
size_t v_sz_3865_; size_t v___x_3866_; lean_object* v___x_3867_; 
v_sz_3865_ = lean_array_size(v_a_3852_);
v___x_3866_ = ((size_t)0ULL);
lean_inc_ref(v___x_3839_);
lean_inc(v_a_3850_);
v___x_3867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_3850_, v___x_3839_, v___x_3840_, v_a_3852_, v_sz_3865_, v___x_3866_, v___x_3861_, v___y_3863_, v___y_3864_);
lean_dec(v_a_3852_);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v___x_3868_; size_t v___x_3869_; size_t v___x_3870_; 
lean_dec_ref_known(v___x_3867_, 1);
v___x_3868_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_3869_ = ((size_t)1ULL);
v___x_3870_ = lean_usize_add(v_i_3843_, v___x_3869_);
v_i_3843_ = v___x_3870_;
v_b_3844_ = v___x_3868_;
goto _start;
}
else
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3879_; 
lean_dec_ref(v___x_3839_);
lean_dec(v_stx_3836_);
v_a_3872_ = lean_ctor_get(v___x_3867_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3874_ = v___x_3867_;
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3867_);
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
else
{
lean_object* v_a_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3905_; 
lean_dec_ref(v___x_3839_);
lean_dec(v_stx_3836_);
v_a_3898_ = lean_ctor_get(v___x_3851_, 0);
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3900_ = v___x_3851_;
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_a_3898_);
lean_dec(v___x_3851_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3903_; 
if (v_isShared_3901_ == 0)
{
v___x_3903_ = v___x_3900_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_a_3898_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
return v___x_3903_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___boxed(lean_object* v_stx_3906_, lean_object* v___x_3907_, lean_object* v___x_3908_, lean_object* v___x_3909_, lean_object* v___x_3910_, lean_object* v_as_3911_, lean_object* v_sz_3912_, lean_object* v_i_3913_, lean_object* v_b_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_){
_start:
{
size_t v_sz_boxed_3918_; size_t v_i_boxed_3919_; lean_object* v_res_3920_; 
v_sz_boxed_3918_ = lean_unbox_usize(v_sz_3912_);
lean_dec(v_sz_3912_);
v_i_boxed_3919_ = lean_unbox_usize(v_i_3913_);
lean_dec(v_i_3913_);
v_res_3920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_3906_, v___x_3907_, v___x_3908_, v___x_3909_, v___x_3910_, v_as_3911_, v_sz_boxed_3918_, v_i_boxed_3919_, v_b_3914_, v___y_3915_, v___y_3916_);
lean_dec(v___y_3916_);
lean_dec_ref(v___y_3915_);
lean_dec_ref(v_as_3911_);
lean_dec(v___x_3910_);
lean_dec_ref(v___x_3908_);
lean_dec_ref(v___x_3907_);
return v_res_3920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(lean_object* v_stx_3921_, lean_object* v___x_3922_, lean_object* v___x_3923_, lean_object* v___x_3924_, lean_object* v___x_3925_, lean_object* v_as_3926_, size_t v_sz_3927_, size_t v_i_3928_, lean_object* v_b_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_){
_start:
{
uint8_t v___x_3933_; 
v___x_3933_ = lean_usize_dec_lt(v_i_3928_, v_sz_3927_);
if (v___x_3933_ == 0)
{
lean_object* v___x_3934_; 
lean_dec_ref(v___x_3924_);
lean_dec(v_stx_3921_);
v___x_3934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3934_, 0, v_b_3929_);
return v___x_3934_;
}
else
{
lean_object* v_a_3935_; lean_object* v___x_3936_; 
lean_dec_ref(v_b_3929_);
v_a_3935_ = lean_array_uget_borrowed(v_as_3926_, v_i_3928_);
lean_inc(v_a_3935_);
lean_inc(v_stx_3921_);
v___x_3936_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3921_, v___x_3922_, v_a_3935_, v___x_3923_, v___y_3930_, v___y_3931_);
if (lean_obj_tag(v___x_3936_) == 0)
{
lean_object* v_a_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v_scopes_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v_opts_3944_; uint8_t v_hasTrace_3945_; lean_object* v___x_3946_; lean_object* v___y_3948_; lean_object* v___y_3949_; 
v_a_3937_ = lean_ctor_get(v___x_3936_, 0);
lean_inc(v_a_3937_);
lean_dec_ref_known(v___x_3936_, 1);
v___x_3938_ = l_Lean_inheritedTraceOptions;
v___x_3939_ = lean_st_ref_get(v___x_3938_);
v___x_3940_ = lean_st_ref_get(v___y_3931_);
v_scopes_3941_ = lean_ctor_get(v___x_3940_, 2);
lean_inc(v_scopes_3941_);
lean_dec(v___x_3940_);
v___x_3942_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3943_ = l_List_head_x21___redArg(v___x_3942_, v_scopes_3941_);
lean_dec(v_scopes_3941_);
v_opts_3944_ = lean_ctor_get(v___x_3943_, 1);
lean_inc_ref(v_opts_3944_);
lean_dec(v___x_3943_);
v_hasTrace_3945_ = lean_ctor_get_uint8(v_opts_3944_, sizeof(void*)*1);
v___x_3946_ = lean_box(0);
if (v_hasTrace_3945_ == 0)
{
lean_dec_ref(v_opts_3944_);
lean_dec(v___x_3939_);
v___y_3948_ = v___y_3930_;
v___y_3949_ = v___y_3931_;
goto v___jp_3947_;
}
else
{
lean_object* v___x_3965_; lean_object* v___x_3966_; uint8_t v___x_3967_; 
v___x_3965_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3966_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_3967_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3939_, v_opts_3944_, v___x_3966_);
lean_dec_ref(v_opts_3944_);
lean_dec(v___x_3939_);
if (v___x_3967_ == 0)
{
v___y_3948_ = v___y_3930_;
v___y_3949_ = v___y_3931_;
goto v___jp_3947_;
}
else
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3968_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_3969_ = lean_array_get_size(v_a_3937_);
v___x_3970_ = l_Nat_reprFast(v___x_3969_);
v___x_3971_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3970_);
v___x_3972_ = l_Lean_MessageData_ofFormat(v___x_3971_);
v___x_3973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3968_);
lean_ctor_set(v___x_3973_, 1, v___x_3972_);
v___x_3974_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_3965_, v___x_3973_, v___y_3930_, v___y_3931_);
if (lean_obj_tag(v___x_3974_) == 0)
{
lean_dec_ref_known(v___x_3974_, 1);
v___y_3948_ = v___y_3930_;
v___y_3949_ = v___y_3931_;
goto v___jp_3947_;
}
else
{
lean_object* v_a_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3982_; 
lean_dec(v_a_3937_);
lean_dec_ref(v___x_3924_);
lean_dec(v_stx_3921_);
v_a_3975_ = lean_ctor_get(v___x_3974_, 0);
v_isSharedCheck_3982_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3977_ = v___x_3974_;
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_a_3975_);
lean_dec(v___x_3974_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3980_; 
if (v_isShared_3978_ == 0)
{
v___x_3980_ = v___x_3977_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v_a_3975_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
}
}
}
v___jp_3947_:
{
size_t v_sz_3950_; size_t v___x_3951_; lean_object* v___x_3952_; 
v_sz_3950_ = lean_array_size(v_a_3937_);
v___x_3951_ = ((size_t)0ULL);
lean_inc_ref(v___x_3924_);
lean_inc(v_a_3935_);
v___x_3952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_3935_, v___x_3924_, v___x_3925_, v_a_3937_, v_sz_3950_, v___x_3951_, v___x_3946_, v___y_3948_, v___y_3949_);
lean_dec(v_a_3937_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_object* v___x_3953_; size_t v___x_3954_; size_t v___x_3955_; lean_object* v___x_3956_; 
lean_dec_ref_known(v___x_3952_, 1);
v___x_3953_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_3954_ = ((size_t)1ULL);
v___x_3955_ = lean_usize_add(v_i_3928_, v___x_3954_);
v___x_3956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_3921_, v___x_3922_, v___x_3923_, v___x_3924_, v___x_3925_, v_as_3926_, v_sz_3927_, v___x_3955_, v___x_3953_, v___y_3930_, v___y_3931_);
return v___x_3956_;
}
else
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3964_; 
lean_dec_ref(v___x_3924_);
lean_dec(v_stx_3921_);
v_a_3957_ = lean_ctor_get(v___x_3952_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3952_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3959_ = v___x_3952_;
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3952_);
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
else
{
lean_object* v_a_3983_; lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_3990_; 
lean_dec_ref(v___x_3924_);
lean_dec(v_stx_3921_);
v_a_3983_ = lean_ctor_get(v___x_3936_, 0);
v_isSharedCheck_3990_ = !lean_is_exclusive(v___x_3936_);
if (v_isSharedCheck_3990_ == 0)
{
v___x_3985_ = v___x_3936_;
v_isShared_3986_ = v_isSharedCheck_3990_;
goto v_resetjp_3984_;
}
else
{
lean_inc(v_a_3983_);
lean_dec(v___x_3936_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_3990_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
lean_object* v___x_3988_; 
if (v_isShared_3986_ == 0)
{
v___x_3988_ = v___x_3985_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_3989_; 
v_reuseFailAlloc_3989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3989_, 0, v_a_3983_);
v___x_3988_ = v_reuseFailAlloc_3989_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
return v___x_3988_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3___boxed(lean_object* v_stx_3991_, lean_object* v___x_3992_, lean_object* v___x_3993_, lean_object* v___x_3994_, lean_object* v___x_3995_, lean_object* v_as_3996_, lean_object* v_sz_3997_, lean_object* v_i_3998_, lean_object* v_b_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_){
_start:
{
size_t v_sz_boxed_4003_; size_t v_i_boxed_4004_; lean_object* v_res_4005_; 
v_sz_boxed_4003_ = lean_unbox_usize(v_sz_3997_);
lean_dec(v_sz_3997_);
v_i_boxed_4004_ = lean_unbox_usize(v_i_3998_);
lean_dec(v_i_3998_);
v_res_4005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(v_stx_3991_, v___x_3992_, v___x_3993_, v___x_3994_, v___x_3995_, v_as_3996_, v_sz_boxed_4003_, v_i_boxed_4004_, v_b_3999_, v___y_4000_, v___y_4001_);
lean_dec(v___y_4001_);
lean_dec_ref(v___y_4000_);
lean_dec_ref(v_as_3996_);
lean_dec(v___x_3995_);
lean_dec_ref(v___x_3993_);
lean_dec_ref(v___x_3992_);
return v_res_4005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(lean_object* v_stx_4009_, lean_object* v___x_4010_, lean_object* v___x_4011_, lean_object* v___x_4012_, lean_object* v___x_4013_, lean_object* v_as_4014_, size_t v_sz_4015_, size_t v_i_4016_, lean_object* v_b_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_){
_start:
{
uint8_t v___x_4021_; 
v___x_4021_ = lean_usize_dec_lt(v_i_4016_, v_sz_4015_);
if (v___x_4021_ == 0)
{
lean_object* v___x_4022_; 
lean_dec_ref(v___x_4012_);
lean_dec(v_stx_4009_);
v___x_4022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4022_, 0, v_b_4017_);
return v___x_4022_;
}
else
{
lean_object* v_a_4023_; lean_object* v___x_4024_; 
lean_dec_ref(v_b_4017_);
v_a_4023_ = lean_array_uget_borrowed(v_as_4014_, v_i_4016_);
lean_inc(v_a_4023_);
lean_inc(v_stx_4009_);
v___x_4024_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_4009_, v___x_4010_, v_a_4023_, v___x_4011_, v___y_4018_, v___y_4019_);
if (lean_obj_tag(v___x_4024_) == 0)
{
lean_object* v_a_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v_scopes_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v_opts_4032_; uint8_t v_hasTrace_4033_; lean_object* v___x_4034_; lean_object* v___y_4036_; lean_object* v___y_4037_; 
v_a_4025_ = lean_ctor_get(v___x_4024_, 0);
lean_inc(v_a_4025_);
lean_dec_ref_known(v___x_4024_, 1);
v___x_4026_ = l_Lean_inheritedTraceOptions;
v___x_4027_ = lean_st_ref_get(v___x_4026_);
v___x_4028_ = lean_st_ref_get(v___y_4019_);
v_scopes_4029_ = lean_ctor_get(v___x_4028_, 2);
lean_inc(v_scopes_4029_);
lean_dec(v___x_4028_);
v___x_4030_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4031_ = l_List_head_x21___redArg(v___x_4030_, v_scopes_4029_);
lean_dec(v_scopes_4029_);
v_opts_4032_ = lean_ctor_get(v___x_4031_, 1);
lean_inc_ref(v_opts_4032_);
lean_dec(v___x_4031_);
v_hasTrace_4033_ = lean_ctor_get_uint8(v_opts_4032_, sizeof(void*)*1);
v___x_4034_ = lean_box(0);
if (v_hasTrace_4033_ == 0)
{
lean_dec_ref(v_opts_4032_);
lean_dec(v___x_4027_);
v___y_4036_ = v___y_4018_;
v___y_4037_ = v___y_4019_;
goto v___jp_4035_;
}
else
{
lean_object* v___x_4053_; lean_object* v___x_4054_; uint8_t v___x_4055_; 
v___x_4053_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4054_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_4055_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4027_, v_opts_4032_, v___x_4054_);
lean_dec_ref(v_opts_4032_);
lean_dec(v___x_4027_);
if (v___x_4055_ == 0)
{
v___y_4036_ = v___y_4018_;
v___y_4037_ = v___y_4019_;
goto v___jp_4035_;
}
else
{
lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___x_4056_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_4057_ = lean_array_get_size(v_a_4025_);
v___x_4058_ = l_Nat_reprFast(v___x_4057_);
v___x_4059_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4058_);
v___x_4060_ = l_Lean_MessageData_ofFormat(v___x_4059_);
v___x_4061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4061_, 0, v___x_4056_);
lean_ctor_set(v___x_4061_, 1, v___x_4060_);
v___x_4062_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_4053_, v___x_4061_, v___y_4018_, v___y_4019_);
if (lean_obj_tag(v___x_4062_) == 0)
{
lean_dec_ref_known(v___x_4062_, 1);
v___y_4036_ = v___y_4018_;
v___y_4037_ = v___y_4019_;
goto v___jp_4035_;
}
else
{
lean_object* v_a_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4070_; 
lean_dec(v_a_4025_);
lean_dec_ref(v___x_4012_);
lean_dec(v_stx_4009_);
v_a_4063_ = lean_ctor_get(v___x_4062_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4062_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4065_ = v___x_4062_;
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_a_4063_);
lean_dec(v___x_4062_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4068_; 
if (v_isShared_4066_ == 0)
{
v___x_4068_ = v___x_4065_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_a_4063_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
return v___x_4068_;
}
}
}
}
}
v___jp_4035_:
{
size_t v_sz_4038_; size_t v___x_4039_; lean_object* v___x_4040_; 
v_sz_4038_ = lean_array_size(v_a_4025_);
v___x_4039_ = ((size_t)0ULL);
lean_inc_ref(v___x_4012_);
lean_inc(v_a_4023_);
v___x_4040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4023_, v___x_4012_, v___x_4013_, v_a_4025_, v_sz_4038_, v___x_4039_, v___x_4034_, v___y_4036_, v___y_4037_);
lean_dec(v_a_4025_);
if (lean_obj_tag(v___x_4040_) == 0)
{
lean_object* v___x_4041_; size_t v___x_4042_; size_t v___x_4043_; 
lean_dec_ref_known(v___x_4040_, 1);
v___x_4041_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_4042_ = ((size_t)1ULL);
v___x_4043_ = lean_usize_add(v_i_4016_, v___x_4042_);
v_i_4016_ = v___x_4043_;
v_b_4017_ = v___x_4041_;
goto _start;
}
else
{
lean_object* v_a_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4052_; 
lean_dec_ref(v___x_4012_);
lean_dec(v_stx_4009_);
v_a_4045_ = lean_ctor_get(v___x_4040_, 0);
v_isSharedCheck_4052_ = !lean_is_exclusive(v___x_4040_);
if (v_isSharedCheck_4052_ == 0)
{
v___x_4047_ = v___x_4040_;
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_a_4045_);
lean_dec(v___x_4040_);
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
else
{
lean_object* v_a_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4078_; 
lean_dec_ref(v___x_4012_);
lean_dec(v_stx_4009_);
v_a_4071_ = lean_ctor_get(v___x_4024_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4073_ = v___x_4024_;
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_a_4071_);
lean_dec(v___x_4024_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4076_; 
if (v_isShared_4074_ == 0)
{
v___x_4076_ = v___x_4073_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_a_4071_);
v___x_4076_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
return v___x_4076_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_stx_4079_, lean_object* v___x_4080_, lean_object* v___x_4081_, lean_object* v___x_4082_, lean_object* v___x_4083_, lean_object* v_as_4084_, lean_object* v_sz_4085_, lean_object* v_i_4086_, lean_object* v_b_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_){
_start:
{
size_t v_sz_boxed_4091_; size_t v_i_boxed_4092_; lean_object* v_res_4093_; 
v_sz_boxed_4091_ = lean_unbox_usize(v_sz_4085_);
lean_dec(v_sz_4085_);
v_i_boxed_4092_ = lean_unbox_usize(v_i_4086_);
lean_dec(v_i_4086_);
v_res_4093_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4079_, v___x_4080_, v___x_4081_, v___x_4082_, v___x_4083_, v_as_4084_, v_sz_boxed_4091_, v_i_boxed_4092_, v_b_4087_, v___y_4088_, v___y_4089_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
lean_dec_ref(v_as_4084_);
lean_dec(v___x_4083_);
lean_dec_ref(v___x_4081_);
lean_dec_ref(v___x_4080_);
return v_res_4093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(lean_object* v_stx_4094_, lean_object* v___x_4095_, lean_object* v___x_4096_, lean_object* v___x_4097_, lean_object* v___x_4098_, lean_object* v_as_4099_, size_t v_sz_4100_, size_t v_i_4101_, lean_object* v_b_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_){
_start:
{
uint8_t v___x_4106_; 
v___x_4106_ = lean_usize_dec_lt(v_i_4101_, v_sz_4100_);
if (v___x_4106_ == 0)
{
lean_object* v___x_4107_; 
lean_dec_ref(v___x_4097_);
lean_dec(v_stx_4094_);
v___x_4107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4107_, 0, v_b_4102_);
return v___x_4107_;
}
else
{
lean_object* v_a_4108_; lean_object* v___x_4109_; 
lean_dec_ref(v_b_4102_);
v_a_4108_ = lean_array_uget_borrowed(v_as_4099_, v_i_4101_);
lean_inc(v_a_4108_);
lean_inc(v_stx_4094_);
v___x_4109_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_4094_, v___x_4095_, v_a_4108_, v___x_4096_, v___y_4103_, v___y_4104_);
if (lean_obj_tag(v___x_4109_) == 0)
{
lean_object* v_a_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v_scopes_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v_opts_4117_; uint8_t v_hasTrace_4118_; lean_object* v___x_4119_; lean_object* v___y_4121_; lean_object* v___y_4122_; 
v_a_4110_ = lean_ctor_get(v___x_4109_, 0);
lean_inc(v_a_4110_);
lean_dec_ref_known(v___x_4109_, 1);
v___x_4111_ = l_Lean_inheritedTraceOptions;
v___x_4112_ = lean_st_ref_get(v___x_4111_);
v___x_4113_ = lean_st_ref_get(v___y_4104_);
v_scopes_4114_ = lean_ctor_get(v___x_4113_, 2);
lean_inc(v_scopes_4114_);
lean_dec(v___x_4113_);
v___x_4115_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4116_ = l_List_head_x21___redArg(v___x_4115_, v_scopes_4114_);
lean_dec(v_scopes_4114_);
v_opts_4117_ = lean_ctor_get(v___x_4116_, 1);
lean_inc_ref(v_opts_4117_);
lean_dec(v___x_4116_);
v_hasTrace_4118_ = lean_ctor_get_uint8(v_opts_4117_, sizeof(void*)*1);
v___x_4119_ = lean_box(0);
if (v_hasTrace_4118_ == 0)
{
lean_dec_ref(v_opts_4117_);
lean_dec(v___x_4112_);
v___y_4121_ = v___y_4103_;
v___y_4122_ = v___y_4104_;
goto v___jp_4120_;
}
else
{
lean_object* v___x_4138_; lean_object* v___x_4139_; uint8_t v___x_4140_; 
v___x_4138_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4139_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_4140_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4112_, v_opts_4117_, v___x_4139_);
lean_dec_ref(v_opts_4117_);
lean_dec(v___x_4112_);
if (v___x_4140_ == 0)
{
v___y_4121_ = v___y_4103_;
v___y_4122_ = v___y_4104_;
goto v___jp_4120_;
}
else
{
lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4141_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_4142_ = lean_array_get_size(v_a_4110_);
v___x_4143_ = l_Nat_reprFast(v___x_4142_);
v___x_4144_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4143_);
v___x_4145_ = l_Lean_MessageData_ofFormat(v___x_4144_);
v___x_4146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4141_);
lean_ctor_set(v___x_4146_, 1, v___x_4145_);
v___x_4147_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_4138_, v___x_4146_, v___y_4103_, v___y_4104_);
if (lean_obj_tag(v___x_4147_) == 0)
{
lean_dec_ref_known(v___x_4147_, 1);
v___y_4121_ = v___y_4103_;
v___y_4122_ = v___y_4104_;
goto v___jp_4120_;
}
else
{
lean_object* v_a_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4155_; 
lean_dec(v_a_4110_);
lean_dec_ref(v___x_4097_);
lean_dec(v_stx_4094_);
v_a_4148_ = lean_ctor_get(v___x_4147_, 0);
v_isSharedCheck_4155_ = !lean_is_exclusive(v___x_4147_);
if (v_isSharedCheck_4155_ == 0)
{
v___x_4150_ = v___x_4147_;
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_a_4148_);
lean_dec(v___x_4147_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v___x_4153_; 
if (v_isShared_4151_ == 0)
{
v___x_4153_ = v___x_4150_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_a_4148_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
return v___x_4153_;
}
}
}
}
}
v___jp_4120_:
{
size_t v_sz_4123_; size_t v___x_4124_; lean_object* v___x_4125_; 
v_sz_4123_ = lean_array_size(v_a_4110_);
v___x_4124_ = ((size_t)0ULL);
lean_inc_ref(v___x_4097_);
lean_inc(v_a_4108_);
v___x_4125_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4108_, v___x_4097_, v___x_4098_, v_a_4110_, v_sz_4123_, v___x_4124_, v___x_4119_, v___y_4121_, v___y_4122_);
lean_dec(v_a_4110_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_object* v___x_4126_; size_t v___x_4127_; size_t v___x_4128_; lean_object* v___x_4129_; 
lean_dec_ref_known(v___x_4125_, 1);
v___x_4126_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_4127_ = ((size_t)1ULL);
v___x_4128_ = lean_usize_add(v_i_4101_, v___x_4127_);
v___x_4129_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4094_, v___x_4095_, v___x_4096_, v___x_4097_, v___x_4098_, v_as_4099_, v_sz_4100_, v___x_4128_, v___x_4126_, v___y_4103_, v___y_4104_);
return v___x_4129_;
}
else
{
lean_object* v_a_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4137_; 
lean_dec_ref(v___x_4097_);
lean_dec(v_stx_4094_);
v_a_4130_ = lean_ctor_get(v___x_4125_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4132_ = v___x_4125_;
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_a_4130_);
lean_dec(v___x_4125_);
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
else
{
lean_object* v_a_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4163_; 
lean_dec_ref(v___x_4097_);
lean_dec(v_stx_4094_);
v_a_4156_ = lean_ctor_get(v___x_4109_, 0);
v_isSharedCheck_4163_ = !lean_is_exclusive(v___x_4109_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4158_ = v___x_4109_;
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_a_4156_);
lean_dec(v___x_4109_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___x_4161_; 
if (v_isShared_4159_ == 0)
{
v___x_4161_ = v___x_4158_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v_a_4156_);
v___x_4161_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
return v___x_4161_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4___boxed(lean_object* v_stx_4164_, lean_object* v___x_4165_, lean_object* v___x_4166_, lean_object* v___x_4167_, lean_object* v___x_4168_, lean_object* v_as_4169_, lean_object* v_sz_4170_, lean_object* v_i_4171_, lean_object* v_b_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_){
_start:
{
size_t v_sz_boxed_4176_; size_t v_i_boxed_4177_; lean_object* v_res_4178_; 
v_sz_boxed_4176_ = lean_unbox_usize(v_sz_4170_);
lean_dec(v_sz_4170_);
v_i_boxed_4177_ = lean_unbox_usize(v_i_4171_);
lean_dec(v_i_4171_);
v_res_4178_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(v_stx_4164_, v___x_4165_, v___x_4166_, v___x_4167_, v___x_4168_, v_as_4169_, v_sz_boxed_4176_, v_i_boxed_4177_, v_b_4172_, v___y_4173_, v___y_4174_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec_ref(v_as_4169_);
lean_dec(v___x_4168_);
lean_dec_ref(v___x_4166_);
lean_dec_ref(v___x_4165_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(lean_object* v_init_4179_, lean_object* v_stx_4180_, lean_object* v___x_4181_, lean_object* v___x_4182_, lean_object* v___x_4183_, lean_object* v___x_4184_, lean_object* v_n_4185_, lean_object* v_b_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_){
_start:
{
if (lean_obj_tag(v_n_4185_) == 0)
{
lean_object* v_cs_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; size_t v_sz_4193_; size_t v___x_4194_; lean_object* v___x_4195_; 
v_cs_4190_ = lean_ctor_get(v_n_4185_, 0);
v___x_4191_ = lean_box(0);
v___x_4192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4191_);
lean_ctor_set(v___x_4192_, 1, v_b_4186_);
v_sz_4193_ = lean_array_size(v_cs_4190_);
v___x_4194_ = ((size_t)0ULL);
v___x_4195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(v_init_4179_, v_stx_4180_, v___x_4181_, v___x_4182_, v___x_4183_, v___x_4184_, v_cs_4190_, v_sz_4193_, v___x_4194_, v___x_4192_, v___y_4187_, v___y_4188_);
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_object* v_a_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4210_; 
v_a_4196_ = lean_ctor_get(v___x_4195_, 0);
v_isSharedCheck_4210_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4198_ = v___x_4195_;
v_isShared_4199_ = v_isSharedCheck_4210_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_a_4196_);
lean_dec(v___x_4195_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4210_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
lean_object* v_fst_4200_; 
v_fst_4200_ = lean_ctor_get(v_a_4196_, 0);
if (lean_obj_tag(v_fst_4200_) == 0)
{
lean_object* v_snd_4201_; lean_object* v___x_4202_; lean_object* v___x_4204_; 
v_snd_4201_ = lean_ctor_get(v_a_4196_, 1);
lean_inc(v_snd_4201_);
lean_dec(v_a_4196_);
v___x_4202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4202_, 0, v_snd_4201_);
if (v_isShared_4199_ == 0)
{
lean_ctor_set(v___x_4198_, 0, v___x_4202_);
v___x_4204_ = v___x_4198_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v___x_4202_);
v___x_4204_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
return v___x_4204_;
}
}
else
{
lean_object* v_val_4206_; lean_object* v___x_4208_; 
lean_inc_ref(v_fst_4200_);
lean_dec(v_a_4196_);
v_val_4206_ = lean_ctor_get(v_fst_4200_, 0);
lean_inc(v_val_4206_);
lean_dec_ref_known(v_fst_4200_, 1);
if (v_isShared_4199_ == 0)
{
lean_ctor_set(v___x_4198_, 0, v_val_4206_);
v___x_4208_ = v___x_4198_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_val_4206_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
return v___x_4208_;
}
}
}
}
else
{
lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4218_; 
v_a_4211_ = lean_ctor_get(v___x_4195_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4213_ = v___x_4195_;
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v___x_4195_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4216_; 
if (v_isShared_4214_ == 0)
{
v___x_4216_ = v___x_4213_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_a_4211_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
}
}
else
{
lean_object* v_vs_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; size_t v_sz_4222_; size_t v___x_4223_; lean_object* v___x_4224_; 
v_vs_4219_ = lean_ctor_get(v_n_4185_, 0);
v___x_4220_ = lean_box(0);
v___x_4221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4221_, 0, v___x_4220_);
lean_ctor_set(v___x_4221_, 1, v_b_4186_);
v_sz_4222_ = lean_array_size(v_vs_4219_);
v___x_4223_ = ((size_t)0ULL);
v___x_4224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(v_stx_4180_, v___x_4181_, v___x_4182_, v___x_4183_, v___x_4184_, v_vs_4219_, v_sz_4222_, v___x_4223_, v___x_4221_, v___y_4187_, v___y_4188_);
if (lean_obj_tag(v___x_4224_) == 0)
{
lean_object* v_a_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4239_; 
v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
v_isSharedCheck_4239_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4227_ = v___x_4224_;
v_isShared_4228_ = v_isSharedCheck_4239_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_a_4225_);
lean_dec(v___x_4224_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4239_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v_fst_4229_; 
v_fst_4229_ = lean_ctor_get(v_a_4225_, 0);
if (lean_obj_tag(v_fst_4229_) == 0)
{
lean_object* v_snd_4230_; lean_object* v___x_4231_; lean_object* v___x_4233_; 
v_snd_4230_ = lean_ctor_get(v_a_4225_, 1);
lean_inc(v_snd_4230_);
lean_dec(v_a_4225_);
v___x_4231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4231_, 0, v_snd_4230_);
if (v_isShared_4228_ == 0)
{
lean_ctor_set(v___x_4227_, 0, v___x_4231_);
v___x_4233_ = v___x_4227_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v___x_4231_);
v___x_4233_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
return v___x_4233_;
}
}
else
{
lean_object* v_val_4235_; lean_object* v___x_4237_; 
lean_inc_ref(v_fst_4229_);
lean_dec(v_a_4225_);
v_val_4235_ = lean_ctor_get(v_fst_4229_, 0);
lean_inc(v_val_4235_);
lean_dec_ref_known(v_fst_4229_, 1);
if (v_isShared_4228_ == 0)
{
lean_ctor_set(v___x_4227_, 0, v_val_4235_);
v___x_4237_ = v___x_4227_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v_val_4235_);
v___x_4237_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
return v___x_4237_;
}
}
}
}
else
{
lean_object* v_a_4240_; lean_object* v___x_4242_; uint8_t v_isShared_4243_; uint8_t v_isSharedCheck_4247_; 
v_a_4240_ = lean_ctor_get(v___x_4224_, 0);
v_isSharedCheck_4247_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4247_ == 0)
{
v___x_4242_ = v___x_4224_;
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
else
{
lean_inc(v_a_4240_);
lean_dec(v___x_4224_);
v___x_4242_ = lean_box(0);
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
v_resetjp_4241_:
{
lean_object* v___x_4245_; 
if (v_isShared_4243_ == 0)
{
v___x_4245_ = v___x_4242_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v_a_4240_);
v___x_4245_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
return v___x_4245_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(lean_object* v_init_4248_, lean_object* v_stx_4249_, lean_object* v___x_4250_, lean_object* v___x_4251_, lean_object* v___x_4252_, lean_object* v___x_4253_, lean_object* v_as_4254_, size_t v_sz_4255_, size_t v_i_4256_, lean_object* v_b_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
uint8_t v___x_4261_; 
v___x_4261_ = lean_usize_dec_lt(v_i_4256_, v_sz_4255_);
if (v___x_4261_ == 0)
{
lean_object* v___x_4262_; 
lean_dec_ref(v___x_4252_);
lean_dec(v_stx_4249_);
v___x_4262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4262_, 0, v_b_4257_);
return v___x_4262_;
}
else
{
lean_object* v_snd_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4297_; 
v_snd_4263_ = lean_ctor_get(v_b_4257_, 1);
v_isSharedCheck_4297_ = !lean_is_exclusive(v_b_4257_);
if (v_isSharedCheck_4297_ == 0)
{
lean_object* v_unused_4298_; 
v_unused_4298_ = lean_ctor_get(v_b_4257_, 0);
lean_dec(v_unused_4298_);
v___x_4265_ = v_b_4257_;
v_isShared_4266_ = v_isSharedCheck_4297_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_snd_4263_);
lean_dec(v_b_4257_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4297_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
lean_object* v_a_4267_; lean_object* v___x_4268_; 
v_a_4267_ = lean_array_uget_borrowed(v_as_4254_, v_i_4256_);
lean_inc(v_snd_4263_);
lean_inc_ref(v___x_4252_);
lean_inc(v_stx_4249_);
v___x_4268_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4248_, v_stx_4249_, v___x_4250_, v___x_4251_, v___x_4252_, v___x_4253_, v_a_4267_, v_snd_4263_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4268_) == 0)
{
lean_object* v_a_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4288_; 
v_a_4269_ = lean_ctor_get(v___x_4268_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4268_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4271_ = v___x_4268_;
v_isShared_4272_ = v_isSharedCheck_4288_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_a_4269_);
lean_dec(v___x_4268_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4288_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
if (lean_obj_tag(v_a_4269_) == 0)
{
lean_object* v___x_4273_; lean_object* v___x_4275_; 
lean_dec_ref(v___x_4252_);
lean_dec(v_stx_4249_);
v___x_4273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4273_, 0, v_a_4269_);
if (v_isShared_4266_ == 0)
{
lean_ctor_set(v___x_4265_, 0, v___x_4273_);
v___x_4275_ = v___x_4265_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v___x_4273_);
lean_ctor_set(v_reuseFailAlloc_4279_, 1, v_snd_4263_);
v___x_4275_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
lean_object* v___x_4277_; 
if (v_isShared_4272_ == 0)
{
lean_ctor_set(v___x_4271_, 0, v___x_4275_);
v___x_4277_ = v___x_4271_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v___x_4275_);
v___x_4277_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
return v___x_4277_;
}
}
}
else
{
lean_object* v_a_4280_; lean_object* v___x_4281_; lean_object* v___x_4283_; 
lean_del_object(v___x_4271_);
lean_dec(v_snd_4263_);
v_a_4280_ = lean_ctor_get(v_a_4269_, 0);
lean_inc(v_a_4280_);
lean_dec_ref_known(v_a_4269_, 1);
v___x_4281_ = lean_box(0);
if (v_isShared_4266_ == 0)
{
lean_ctor_set(v___x_4265_, 1, v_a_4280_);
lean_ctor_set(v___x_4265_, 0, v___x_4281_);
v___x_4283_ = v___x_4265_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v___x_4281_);
lean_ctor_set(v_reuseFailAlloc_4287_, 1, v_a_4280_);
v___x_4283_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
size_t v___x_4284_; size_t v___x_4285_; 
v___x_4284_ = ((size_t)1ULL);
v___x_4285_ = lean_usize_add(v_i_4256_, v___x_4284_);
v_i_4256_ = v___x_4285_;
v_b_4257_ = v___x_4283_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4296_; 
lean_del_object(v___x_4265_);
lean_dec(v_snd_4263_);
lean_dec_ref(v___x_4252_);
lean_dec(v_stx_4249_);
v_a_4289_ = lean_ctor_get(v___x_4268_, 0);
v_isSharedCheck_4296_ = !lean_is_exclusive(v___x_4268_);
if (v_isSharedCheck_4296_ == 0)
{
v___x_4291_ = v___x_4268_;
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_a_4289_);
lean_dec(v___x_4268_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v___x_4294_; 
if (v_isShared_4292_ == 0)
{
v___x_4294_ = v___x_4291_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_a_4289_);
v___x_4294_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
return v___x_4294_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3___boxed(lean_object* v_init_4299_, lean_object* v_stx_4300_, lean_object* v___x_4301_, lean_object* v___x_4302_, lean_object* v___x_4303_, lean_object* v___x_4304_, lean_object* v_as_4305_, lean_object* v_sz_4306_, lean_object* v_i_4307_, lean_object* v_b_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_){
_start:
{
size_t v_sz_boxed_4312_; size_t v_i_boxed_4313_; lean_object* v_res_4314_; 
v_sz_boxed_4312_ = lean_unbox_usize(v_sz_4306_);
lean_dec(v_sz_4306_);
v_i_boxed_4313_ = lean_unbox_usize(v_i_4307_);
lean_dec(v_i_4307_);
v_res_4314_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(v_init_4299_, v_stx_4300_, v___x_4301_, v___x_4302_, v___x_4303_, v___x_4304_, v_as_4305_, v_sz_boxed_4312_, v_i_boxed_4313_, v_b_4308_, v___y_4309_, v___y_4310_);
lean_dec(v___y_4310_);
lean_dec_ref(v___y_4309_);
lean_dec_ref(v_as_4305_);
lean_dec(v___x_4304_);
lean_dec_ref(v___x_4302_);
lean_dec_ref(v___x_4301_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2___boxed(lean_object* v_init_4315_, lean_object* v_stx_4316_, lean_object* v___x_4317_, lean_object* v___x_4318_, lean_object* v___x_4319_, lean_object* v___x_4320_, lean_object* v_n_4321_, lean_object* v_b_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_){
_start:
{
lean_object* v_res_4326_; 
v_res_4326_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4315_, v_stx_4316_, v___x_4317_, v___x_4318_, v___x_4319_, v___x_4320_, v_n_4321_, v_b_4322_, v___y_4323_, v___y_4324_);
lean_dec(v___y_4324_);
lean_dec_ref(v___y_4323_);
lean_dec_ref(v_n_4321_);
lean_dec(v___x_4320_);
lean_dec_ref(v___x_4318_);
lean_dec_ref(v___x_4317_);
return v_res_4326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(lean_object* v___x_4327_, lean_object* v___x_4328_, lean_object* v_stx_4329_, lean_object* v___x_4330_, lean_object* v___x_4331_, lean_object* v_t_4332_, lean_object* v_init_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_){
_start:
{
lean_object* v_root_4337_; lean_object* v_tail_4338_; lean_object* v___x_4339_; 
v_root_4337_ = lean_ctor_get(v_t_4332_, 0);
v_tail_4338_ = lean_ctor_get(v_t_4332_, 1);
lean_inc_ref(v___x_4327_);
lean_inc(v_stx_4329_);
v___x_4339_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4333_, v_stx_4329_, v___x_4330_, v___x_4331_, v___x_4327_, v___x_4328_, v_root_4337_, v_init_4333_, v___y_4334_, v___y_4335_);
if (lean_obj_tag(v___x_4339_) == 0)
{
lean_object* v_a_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4376_; 
v_a_4340_ = lean_ctor_get(v___x_4339_, 0);
v_isSharedCheck_4376_ = !lean_is_exclusive(v___x_4339_);
if (v_isSharedCheck_4376_ == 0)
{
v___x_4342_ = v___x_4339_;
v_isShared_4343_ = v_isSharedCheck_4376_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_a_4340_);
lean_dec(v___x_4339_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4376_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
if (lean_obj_tag(v_a_4340_) == 0)
{
lean_object* v_a_4344_; lean_object* v___x_4346_; 
lean_dec(v_stx_4329_);
lean_dec_ref(v___x_4327_);
v_a_4344_ = lean_ctor_get(v_a_4340_, 0);
lean_inc(v_a_4344_);
lean_dec_ref_known(v_a_4340_, 1);
if (v_isShared_4343_ == 0)
{
lean_ctor_set(v___x_4342_, 0, v_a_4344_);
v___x_4346_ = v___x_4342_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4347_; 
v_reuseFailAlloc_4347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4347_, 0, v_a_4344_);
v___x_4346_ = v_reuseFailAlloc_4347_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
return v___x_4346_;
}
}
else
{
lean_object* v_a_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; size_t v_sz_4351_; size_t v___x_4352_; lean_object* v___x_4353_; 
lean_del_object(v___x_4342_);
v_a_4348_ = lean_ctor_get(v_a_4340_, 0);
lean_inc(v_a_4348_);
lean_dec_ref_known(v_a_4340_, 1);
v___x_4349_ = lean_box(0);
v___x_4350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4350_, 0, v___x_4349_);
lean_ctor_set(v___x_4350_, 1, v_a_4348_);
v_sz_4351_ = lean_array_size(v_tail_4338_);
v___x_4352_ = ((size_t)0ULL);
v___x_4353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(v_stx_4329_, v___x_4330_, v___x_4331_, v___x_4327_, v___x_4328_, v_tail_4338_, v_sz_4351_, v___x_4352_, v___x_4350_, v___y_4334_, v___y_4335_);
if (lean_obj_tag(v___x_4353_) == 0)
{
lean_object* v_a_4354_; lean_object* v___x_4356_; uint8_t v_isShared_4357_; uint8_t v_isSharedCheck_4367_; 
v_a_4354_ = lean_ctor_get(v___x_4353_, 0);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4353_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4356_ = v___x_4353_;
v_isShared_4357_ = v_isSharedCheck_4367_;
goto v_resetjp_4355_;
}
else
{
lean_inc(v_a_4354_);
lean_dec(v___x_4353_);
v___x_4356_ = lean_box(0);
v_isShared_4357_ = v_isSharedCheck_4367_;
goto v_resetjp_4355_;
}
v_resetjp_4355_:
{
lean_object* v_fst_4358_; 
v_fst_4358_ = lean_ctor_get(v_a_4354_, 0);
if (lean_obj_tag(v_fst_4358_) == 0)
{
lean_object* v_snd_4359_; lean_object* v___x_4361_; 
v_snd_4359_ = lean_ctor_get(v_a_4354_, 1);
lean_inc(v_snd_4359_);
lean_dec(v_a_4354_);
if (v_isShared_4357_ == 0)
{
lean_ctor_set(v___x_4356_, 0, v_snd_4359_);
v___x_4361_ = v___x_4356_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v_snd_4359_);
v___x_4361_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
return v___x_4361_;
}
}
else
{
lean_object* v_val_4363_; lean_object* v___x_4365_; 
lean_inc_ref(v_fst_4358_);
lean_dec(v_a_4354_);
v_val_4363_ = lean_ctor_get(v_fst_4358_, 0);
lean_inc(v_val_4363_);
lean_dec_ref_known(v_fst_4358_, 1);
if (v_isShared_4357_ == 0)
{
lean_ctor_set(v___x_4356_, 0, v_val_4363_);
v___x_4365_ = v___x_4356_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_val_4363_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
return v___x_4365_;
}
}
}
}
else
{
lean_object* v_a_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4375_; 
v_a_4368_ = lean_ctor_get(v___x_4353_, 0);
v_isSharedCheck_4375_ = !lean_is_exclusive(v___x_4353_);
if (v_isSharedCheck_4375_ == 0)
{
v___x_4370_ = v___x_4353_;
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_a_4368_);
lean_dec(v___x_4353_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
lean_object* v___x_4373_; 
if (v_isShared_4371_ == 0)
{
v___x_4373_ = v___x_4370_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v_a_4368_);
v___x_4373_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
return v___x_4373_;
}
}
}
}
}
}
else
{
lean_object* v_a_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4384_; 
lean_dec(v_stx_4329_);
lean_dec_ref(v___x_4327_);
v_a_4377_ = lean_ctor_get(v___x_4339_, 0);
v_isSharedCheck_4384_ = !lean_is_exclusive(v___x_4339_);
if (v_isSharedCheck_4384_ == 0)
{
v___x_4379_ = v___x_4339_;
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
else
{
lean_inc(v_a_4377_);
lean_dec(v___x_4339_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v___x_4382_; 
if (v_isShared_4380_ == 0)
{
v___x_4382_ = v___x_4379_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_a_4377_);
v___x_4382_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
return v___x_4382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2___boxed(lean_object* v___x_4385_, lean_object* v___x_4386_, lean_object* v_stx_4387_, lean_object* v___x_4388_, lean_object* v___x_4389_, lean_object* v_t_4390_, lean_object* v_init_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_){
_start:
{
lean_object* v_res_4395_; 
v_res_4395_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___x_4385_, v___x_4386_, v_stx_4387_, v___x_4388_, v___x_4389_, v_t_4390_, v_init_4391_, v___y_4392_, v___y_4393_);
lean_dec(v___y_4393_);
lean_dec_ref(v___y_4392_);
lean_dec_ref(v_t_4390_);
lean_dec_ref(v___x_4389_);
lean_dec_ref(v___x_4388_);
lean_dec(v___x_4386_);
return v_res_4395_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4397_; lean_object* v___x_4398_; 
v___x_4397_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__0));
v___x_4398_ = l_Lean_stringToMessageData(v___x_4397_);
return v___x_4398_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4402_; lean_object* v___x_4403_; 
v___x_4402_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__4));
v___x_4403_ = l_Lean_stringToMessageData(v___x_4402_);
return v___x_4403_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4405_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__6));
v___x_4406_ = l_Lean_stringToMessageData(v___x_4405_);
return v___x_4406_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9(void){
_start:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; 
v___x_4408_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__8));
v___x_4409_ = l_Lean_stringToMessageData(v___x_4408_);
return v___x_4409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(lean_object* v_stx_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_){
_start:
{
lean_object* v___x_4417_; lean_object* v_scopes_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v_opts_4421_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; uint8_t v___y_4445_; lean_object* v___y_4446_; lean_object* v___y_4447_; lean_object* v___y_4453_; uint8_t v___y_4454_; lean_object* v___y_4455_; lean_object* v___y_4456_; lean_object* v___y_4462_; lean_object* v___y_4463_; uint8_t v___y_4464_; uint8_t v___y_4465_; lean_object* v___y_4466_; uint8_t v___y_4475_; lean_object* v___y_4476_; uint8_t v___y_4477_; uint8_t v___y_4478_; lean_object* v___y_4479_; lean_object* v___y_4480_; uint8_t v___y_4489_; uint8_t v___y_4490_; uint8_t v___y_4491_; uint8_t v___y_4525_; lean_object* v___x_4532_; uint8_t v___x_4533_; 
v___x_4417_ = lean_st_ref_get(v___y_4412_);
v_scopes_4418_ = lean_ctor_get(v___x_4417_, 2);
lean_inc(v_scopes_4418_);
lean_dec(v___x_4417_);
v___x_4419_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4420_ = l_List_head_x21___redArg(v___x_4419_, v_scopes_4418_);
lean_dec(v_scopes_4418_);
v_opts_4421_ = lean_ctor_get(v___x_4420_, 1);
lean_inc_ref(v_opts_4421_);
lean_dec(v___x_4420_);
v___x_4532_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_4533_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4421_, v___x_4532_);
if (v___x_4533_ == 0)
{
lean_object* v___x_4534_; uint8_t v___x_4535_; 
v___x_4534_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_4535_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4421_, v___x_4534_);
v___y_4525_ = v___x_4535_;
goto v___jp_4524_;
}
else
{
v___y_4525_ = v___x_4533_;
goto v___jp_4524_;
}
v___jp_4414_:
{
lean_object* v___x_4415_; lean_object* v___x_4416_; 
v___x_4415_ = lean_box(0);
v___x_4416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4416_, 0, v___x_4415_);
return v___x_4416_;
}
v___jp_4422_:
{
lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v_a_4429_; lean_object* v___x_4430_; lean_object* v_line_4431_; lean_object* v_messages_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
v___x_4427_ = lean_st_ref_get(v___y_4423_);
v___x_4428_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_4423_);
v_a_4429_ = lean_ctor_get(v___x_4428_, 0);
lean_inc(v_a_4429_);
lean_dec_ref(v___x_4428_);
lean_inc_ref_n(v___y_4424_, 2);
v___x_4430_ = l_Lean_FileMap_toPosition(v___y_4424_, v___y_4426_);
lean_dec(v___y_4426_);
v_line_4431_ = lean_ctor_get(v___x_4430_, 0);
lean_inc(v_line_4431_);
lean_dec_ref(v___x_4430_);
v_messages_4432_ = lean_ctor_get(v___x_4427_, 1);
lean_inc_ref(v_messages_4432_);
lean_dec(v___x_4427_);
v___x_4433_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_4432_);
v___x_4434_ = lean_box(0);
v___x_4435_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___y_4424_, v_line_4431_, v_stx_4410_, v_opts_4421_, v___x_4433_, v_a_4429_, v___x_4434_, v___y_4425_, v___y_4423_);
lean_dec(v_a_4429_);
lean_dec_ref(v___x_4433_);
lean_dec_ref(v_opts_4421_);
lean_dec(v_line_4431_);
if (lean_obj_tag(v___x_4435_) == 0)
{
lean_object* v___x_4437_; uint8_t v_isShared_4438_; uint8_t v_isSharedCheck_4442_; 
v_isSharedCheck_4442_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4442_ == 0)
{
lean_object* v_unused_4443_; 
v_unused_4443_ = lean_ctor_get(v___x_4435_, 0);
lean_dec(v_unused_4443_);
v___x_4437_ = v___x_4435_;
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
else
{
lean_dec(v___x_4435_);
v___x_4437_ = lean_box(0);
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
v_resetjp_4436_:
{
lean_object* v___x_4440_; 
if (v_isShared_4438_ == 0)
{
lean_ctor_set(v___x_4437_, 0, v___x_4434_);
v___x_4440_ = v___x_4437_;
goto v_reusejp_4439_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v___x_4434_);
v___x_4440_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4439_;
}
v_reusejp_4439_:
{
return v___x_4440_;
}
}
}
else
{
return v___x_4435_;
}
}
v___jp_4444_:
{
lean_object* v_fileMap_4448_; lean_object* v___x_4449_; 
v_fileMap_4448_ = lean_ctor_get(v___y_4446_, 1);
v___x_4449_ = l_Lean_Syntax_getPos_x3f(v_stx_4410_, v___y_4445_);
if (lean_obj_tag(v___x_4449_) == 0)
{
lean_object* v___x_4450_; 
v___x_4450_ = lean_unsigned_to_nat(0u);
v___y_4423_ = v___y_4447_;
v___y_4424_ = v_fileMap_4448_;
v___y_4425_ = v___y_4446_;
v___y_4426_ = v___x_4450_;
goto v___jp_4422_;
}
else
{
lean_object* v_val_4451_; 
v_val_4451_ = lean_ctor_get(v___x_4449_, 0);
lean_inc(v_val_4451_);
lean_dec_ref_known(v___x_4449_, 1);
v___y_4423_ = v___y_4447_;
v___y_4424_ = v_fileMap_4448_;
v___y_4425_ = v___y_4446_;
v___y_4426_ = v_val_4451_;
goto v___jp_4422_;
}
}
v___jp_4452_:
{
lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; 
lean_inc_ref(v___y_4456_);
v___x_4457_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4457_, 0, v___y_4456_);
v___x_4458_ = l_Lean_MessageData_ofFormat(v___x_4457_);
v___x_4459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4459_, 0, v___y_4455_);
lean_ctor_set(v___x_4459_, 1, v___x_4458_);
lean_inc(v___y_4453_);
v___x_4460_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___y_4453_, v___x_4459_, v___y_4411_, v___y_4412_);
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_dec_ref_known(v___x_4460_, 1);
v___y_4445_ = v___y_4454_;
v___y_4446_ = v___y_4411_;
v___y_4447_ = v___y_4412_;
goto v___jp_4444_;
}
else
{
lean_dec_ref(v_opts_4421_);
lean_dec(v_stx_4410_);
return v___x_4460_;
}
}
v___jp_4461_:
{
lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; 
lean_inc_ref(v___y_4466_);
v___x_4467_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4467_, 0, v___y_4466_);
v___x_4468_ = l_Lean_MessageData_ofFormat(v___x_4467_);
v___x_4469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4469_, 0, v___y_4462_);
lean_ctor_set(v___x_4469_, 1, v___x_4468_);
v___x_4470_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1);
v___x_4471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4471_, 0, v___x_4469_);
lean_ctor_set(v___x_4471_, 1, v___x_4470_);
if (v___y_4465_ == 0)
{
lean_object* v___x_4472_; 
v___x_4472_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4453_ = v___y_4463_;
v___y_4454_ = v___y_4464_;
v___y_4455_ = v___x_4471_;
v___y_4456_ = v___x_4472_;
goto v___jp_4452_;
}
else
{
lean_object* v___x_4473_; 
v___x_4473_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4453_ = v___y_4463_;
v___y_4454_ = v___y_4464_;
v___y_4455_ = v___x_4471_;
v___y_4456_ = v___x_4473_;
goto v___jp_4452_;
}
}
v___jp_4474_:
{
lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; 
lean_inc_ref(v___y_4480_);
v___x_4481_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4481_, 0, v___y_4480_);
v___x_4482_ = l_Lean_MessageData_ofFormat(v___x_4481_);
lean_inc_ref(v___y_4479_);
v___x_4483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4483_, 0, v___y_4479_);
lean_ctor_set(v___x_4483_, 1, v___x_4482_);
v___x_4484_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5);
v___x_4485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4485_, 0, v___x_4483_);
lean_ctor_set(v___x_4485_, 1, v___x_4484_);
if (v___y_4475_ == 0)
{
lean_object* v___x_4486_; 
v___x_4486_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4462_ = v___x_4485_;
v___y_4463_ = v___y_4476_;
v___y_4464_ = v___y_4477_;
v___y_4465_ = v___y_4478_;
v___y_4466_ = v___x_4486_;
goto v___jp_4461_;
}
else
{
lean_object* v___x_4487_; 
v___x_4487_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4462_ = v___x_4485_;
v___y_4463_ = v___y_4476_;
v___y_4464_ = v___y_4477_;
v___y_4465_ = v___y_4478_;
v___y_4466_ = v___x_4487_;
goto v___jp_4461_;
}
}
v___jp_4488_:
{
lean_object* v___x_4492_; lean_object* v_a_4493_; uint8_t v___x_4494_; 
v___x_4492_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(v_stx_4410_, v___y_4411_, v___y_4412_);
v_a_4493_ = lean_ctor_get(v___x_4492_, 0);
lean_inc(v_a_4493_);
lean_dec_ref(v___x_4492_);
v___x_4494_ = lean_unbox(v_a_4493_);
if (v___x_4494_ == 0)
{
lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v_scopes_4498_; lean_object* v___x_4499_; lean_object* v_opts_4500_; uint8_t v_hasTrace_4501_; 
v___x_4495_ = l_Lean_inheritedTraceOptions;
v___x_4496_ = lean_st_ref_get(v___x_4495_);
v___x_4497_ = lean_st_ref_get(v___y_4412_);
v_scopes_4498_ = lean_ctor_get(v___x_4497_, 2);
lean_inc(v_scopes_4498_);
lean_dec(v___x_4497_);
v___x_4499_ = l_List_head_x21___redArg(v___x_4419_, v_scopes_4498_);
lean_dec(v_scopes_4498_);
v_opts_4500_ = lean_ctor_get(v___x_4499_, 1);
lean_inc_ref(v_opts_4500_);
lean_dec(v___x_4499_);
v_hasTrace_4501_ = lean_ctor_get_uint8(v_opts_4500_, sizeof(void*)*1);
if (v_hasTrace_4501_ == 0)
{
uint8_t v___x_4502_; 
lean_dec_ref(v_opts_4500_);
lean_dec(v___x_4496_);
v___x_4502_ = lean_unbox(v_a_4493_);
lean_dec(v_a_4493_);
v___y_4445_ = v___x_4502_;
v___y_4446_ = v___y_4411_;
v___y_4447_ = v___y_4412_;
goto v___jp_4444_;
}
else
{
lean_object* v___x_4503_; lean_object* v___x_4504_; uint8_t v___x_4505_; 
v___x_4503_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4504_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_4505_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4496_, v_opts_4500_, v___x_4504_);
lean_dec_ref(v_opts_4500_);
lean_dec(v___x_4496_);
if (v___x_4505_ == 0)
{
uint8_t v___x_4506_; 
v___x_4506_ = lean_unbox(v_a_4493_);
lean_dec(v_a_4493_);
v___y_4445_ = v___x_4506_;
v___y_4446_ = v___y_4411_;
v___y_4447_ = v___y_4412_;
goto v___jp_4444_;
}
else
{
lean_object* v___x_4507_; 
v___x_4507_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7);
if (v___y_4490_ == 0)
{
lean_object* v___x_4508_; uint8_t v___x_4509_; 
v___x_4508_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___x_4509_ = lean_unbox(v_a_4493_);
lean_dec(v_a_4493_);
v___y_4475_ = v___y_4489_;
v___y_4476_ = v___x_4503_;
v___y_4477_ = v___x_4509_;
v___y_4478_ = v___y_4491_;
v___y_4479_ = v___x_4507_;
v___y_4480_ = v___x_4508_;
goto v___jp_4474_;
}
else
{
lean_object* v___x_4510_; uint8_t v___x_4511_; 
v___x_4510_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___x_4511_ = lean_unbox(v_a_4493_);
lean_dec(v_a_4493_);
v___y_4475_ = v___y_4489_;
v___y_4476_ = v___x_4503_;
v___y_4477_ = v___x_4511_;
v___y_4478_ = v___y_4491_;
v___y_4479_ = v___x_4507_;
v___y_4480_ = v___x_4510_;
goto v___jp_4474_;
}
}
}
}
else
{
lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v_scopes_4515_; lean_object* v___x_4516_; lean_object* v_opts_4517_; uint8_t v_hasTrace_4518_; 
lean_dec(v_a_4493_);
lean_dec_ref(v_opts_4421_);
lean_dec(v_stx_4410_);
v___x_4512_ = l_Lean_inheritedTraceOptions;
v___x_4513_ = lean_st_ref_get(v___x_4512_);
v___x_4514_ = lean_st_ref_get(v___y_4412_);
v_scopes_4515_ = lean_ctor_get(v___x_4514_, 2);
lean_inc(v_scopes_4515_);
lean_dec(v___x_4514_);
v___x_4516_ = l_List_head_x21___redArg(v___x_4419_, v_scopes_4515_);
lean_dec(v_scopes_4515_);
v_opts_4517_ = lean_ctor_get(v___x_4516_, 1);
lean_inc_ref(v_opts_4517_);
lean_dec(v___x_4516_);
v_hasTrace_4518_ = lean_ctor_get_uint8(v_opts_4517_, sizeof(void*)*1);
if (v_hasTrace_4518_ == 0)
{
lean_dec_ref(v_opts_4517_);
lean_dec(v___x_4513_);
goto v___jp_4414_;
}
else
{
lean_object* v___x_4519_; lean_object* v___x_4520_; uint8_t v___x_4521_; 
v___x_4519_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4520_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_4521_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4513_, v_opts_4517_, v___x_4520_);
lean_dec_ref(v_opts_4517_);
lean_dec(v___x_4513_);
if (v___x_4521_ == 0)
{
goto v___jp_4414_;
}
else
{
lean_object* v___x_4522_; lean_object* v___x_4523_; 
v___x_4522_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9);
v___x_4523_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_4519_, v___x_4522_, v___y_4411_, v___y_4412_);
if (lean_obj_tag(v___x_4523_) == 0)
{
lean_dec_ref_known(v___x_4523_, 1);
goto v___jp_4414_;
}
else
{
return v___x_4523_;
}
}
}
}
}
v___jp_4524_:
{
lean_object* v___x_4526_; uint8_t v___x_4527_; lean_object* v___x_4528_; uint8_t v___x_4529_; 
v___x_4526_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
v___x_4527_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4421_, v___x_4526_);
v___x_4528_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v___x_4529_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4421_, v___x_4528_);
if (v___y_4525_ == 0)
{
if (v___x_4527_ == 0)
{
if (v___x_4529_ == 0)
{
lean_object* v___x_4530_; lean_object* v___x_4531_; 
lean_dec_ref(v_opts_4421_);
lean_dec(v_stx_4410_);
v___x_4530_ = lean_box(0);
v___x_4531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4531_, 0, v___x_4530_);
return v___x_4531_;
}
else
{
v___y_4489_ = v___x_4527_;
v___y_4490_ = v___y_4525_;
v___y_4491_ = v___x_4529_;
goto v___jp_4488_;
}
}
else
{
v___y_4489_ = v___x_4527_;
v___y_4490_ = v___y_4525_;
v___y_4491_ = v___x_4529_;
goto v___jp_4488_;
}
}
else
{
v___y_4489_ = v___x_4527_;
v___y_4490_ = v___y_4525_;
v___y_4491_ = v___x_4529_;
goto v___jp_4488_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___boxed(lean_object* v_stx_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_){
_start:
{
lean_object* v_res_4540_; 
v_res_4540_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(v_stx_4536_, v___y_4537_, v___y_4538_);
lean_dec(v___y_4538_);
lean_dec_ref(v___y_4537_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4553_; lean_object* v___x_4554_; 
v___x_4553_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook));
v___x_4554_ = l_Lean_Elab_Command_addLinter(v___x_4553_);
return v___x_4554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2____boxed(lean_object* v_a_4555_){
_start:
{
lean_object* v_res_4556_; 
v_res_4556_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_();
return v_res_4556_;
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
