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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_append(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
extern lean_object* l_Lean_inheritedTraceOptions;
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
extern lean_object* l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default;
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0___redArg();
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
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__13_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__15_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__16;
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
v___x_276_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
v___x_292_ = l_Lean_Options_empty;
v___x_293_ = l_Lean_Core_getMaxHeartbeats(v___x_292_);
return v___x_293_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_294_ = lean_unsigned_to_nat(1u);
v___x_295_ = l_Lean_firstFrontendMacroScope;
v___x_296_ = lean_nat_add(v___x_295_, v___x_294_);
return v___x_296_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__16(void){
_start:
{
lean_object* v___x_307_; uint64_t v___x_308_; lean_object* v___x_309_; 
v___x_307_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8);
v___x_308_ = 0ULL;
v___x_309_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_309_, 0, v___x_307_);
lean_ctor_set_uint64(v___x_309_, sizeof(void*)*1, v___x_308_);
return v___x_309_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5);
v___x_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
return v___x_311_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_312_ = l_Lean_NameSet_empty;
v___x_313_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8);
v___x_314_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
lean_ctor_set(v___x_314_, 2, v___x_312_);
return v___x_314_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; lean_object* v___x_318_; 
v___x_315_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8);
v___x_316_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5);
v___x_317_ = 1;
v___x_318_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_318_, 0, v___x_316_);
lean_ctor_set(v___x_318_, 1, v___x_316_);
lean_ctor_set(v___x_318_, 2, v___x_315_);
lean_ctor_set_uint8(v___x_318_, sizeof(void*)*3, v___x_317_);
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
lean_object* v___x_337_; uint8_t v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v_fileName_349_; lean_object* v_fileMap_350_; lean_object* v_ref_351_; lean_object* v_cancelTk_x3f_352_; lean_object* v_a_354_; lean_object* v_a_361_; lean_object* v_currNamespace_363_; lean_object* v_openDecls_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___y_382_; uint8_t v___y_383_; lean_object* v_fileName_384_; lean_object* v_fileMap_385_; lean_object* v_currNamespace_386_; lean_object* v_openDecls_387_; lean_object* v_initHeartbeats_388_; lean_object* v_maxHeartbeats_389_; lean_object* v_quotContext_390_; lean_object* v_currMacroScope_391_; lean_object* v_cancelTk_x3f_392_; lean_object* v_inheritedTraceOptions_393_; lean_object* v_currRecDepth_394_; lean_object* v_ref_395_; uint8_t v_suppressElabErrors_396_; lean_object* v___y_397_; lean_object* v___y_466_; uint8_t v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___y_485_; lean_object* v___y_486_; uint8_t v___y_487_; lean_object* v___y_488_; uint8_t v___y_489_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; lean_object* v___y_514_; lean_object* v___x_523_; uint8_t v___y_525_; lean_object* v_env_545_; uint8_t v___x_546_; 
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
v_fileName_349_ = lean_ctor_get(v_a_334_, 0);
v_fileMap_350_ = lean_ctor_get(v_a_334_, 1);
v_ref_351_ = lean_ctor_get(v_a_334_, 7);
v_cancelTk_x3f_352_ = lean_ctor_get(v_a_334_, 9);
v_currNamespace_363_ = lean_ctor_get(v_namingCtx_332_, 0);
lean_inc(v_currNamespace_363_);
v_openDecls_364_ = lean_ctor_get(v_namingCtx_332_, 1);
lean_inc(v_openDecls_364_);
lean_dec_ref(v_namingCtx_332_);
v___x_365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_365_, 0, v_mctx_329_);
lean_ctor_set(v___x_365_, 1, v___x_346_);
lean_ctor_set(v___x_365_, 2, v___x_337_);
lean_ctor_set(v___x_365_, 3, v___x_347_);
lean_ctor_set(v___x_365_, 4, v___x_348_);
v___x_366_ = l_Lean_Options_empty;
v___x_367_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10);
v___x_368_ = lean_box(0);
v___x_369_ = l_Lean_firstFrontendMacroScope;
v___x_370_ = lean_box(0);
v___x_371_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11);
v___x_372_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__14));
v___x_373_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__15));
v___x_374_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__16, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__16_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__16);
v___x_375_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17);
v___x_376_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18);
v___x_377_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19);
v___x_378_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_378_, 0, v___x_339_);
lean_ctor_set(v___x_378_, 1, v___x_371_);
lean_ctor_set(v___x_378_, 2, v___x_372_);
lean_ctor_set(v___x_378_, 3, v___x_373_);
lean_ctor_set(v___x_378_, 4, v___x_374_);
lean_ctor_set(v___x_378_, 5, v___x_375_);
lean_ctor_set(v___x_378_, 6, v___x_376_);
lean_ctor_set(v___x_378_, 7, v___x_377_);
lean_ctor_set(v___x_378_, 8, v___x_343_);
v___x_379_ = lean_io_get_num_heartbeats();
v___x_380_ = lean_st_mk_ref(v___x_378_);
v___x_509_ = l_Lean_inheritedTraceOptions;
v___x_510_ = lean_st_ref_get(v___x_509_);
v___x_511_ = l_Lean_diagnostics;
v___x_512_ = lean_uint8_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23);
v___x_523_ = lean_st_ref_get(v___x_380_);
v_env_545_ = lean_ctor_get(v___x_523_, 0);
lean_inc_ref(v_env_545_);
lean_dec(v___x_523_);
v___x_546_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_545_);
lean_dec_ref(v_env_545_);
if (v___x_512_ == 0)
{
if (v___x_546_ == 0)
{
lean_inc(v___x_380_);
v___y_514_ = v___x_380_;
goto v___jp_513_;
}
else
{
v___y_525_ = v___x_512_;
goto v___jp_524_;
}
}
else
{
v___y_525_ = v___x_546_;
goto v___jp_524_;
}
v___jp_353_:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_355_ = lean_io_error_to_string(v_a_354_);
v___x_356_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
v___x_357_ = l_Lean_MessageData_ofFormat(v___x_356_);
lean_inc(v_ref_351_);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v_ref_351_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
v___x_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
return v___x_359_;
}
v___jp_360_:
{
lean_object* v___x_362_; 
v___x_362_ = lean_mk_io_user_error(v_a_361_);
v_a_354_ = v___x_362_;
goto v___jp_353_;
}
v___jp_381_:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_398_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__1(v_opts_331_, v___y_382_);
v___x_399_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_399_, 0, v_fileName_384_);
lean_ctor_set(v___x_399_, 1, v_fileMap_385_);
lean_ctor_set(v___x_399_, 2, v_opts_331_);
lean_ctor_set(v___x_399_, 3, v___x_398_);
lean_ctor_set(v___x_399_, 4, v_currNamespace_386_);
lean_ctor_set(v___x_399_, 5, v_openDecls_387_);
lean_ctor_set(v___x_399_, 6, v_initHeartbeats_388_);
lean_ctor_set(v___x_399_, 7, v_maxHeartbeats_389_);
lean_ctor_set(v___x_399_, 8, v_quotContext_390_);
lean_ctor_set(v___x_399_, 9, v_currMacroScope_391_);
lean_ctor_set(v___x_399_, 10, v_cancelTk_x3f_392_);
lean_ctor_set(v___x_399_, 11, v_inheritedTraceOptions_393_);
v___x_400_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_400_, 0, v___x_399_);
lean_ctor_set(v___x_400_, 1, v_currRecDepth_394_);
lean_ctor_set(v___x_400_, 2, v_ref_395_);
lean_ctor_set_uint8(v___x_400_, sizeof(void*)*3, v___y_383_);
lean_ctor_set_uint8(v___x_400_, sizeof(void*)*3 + 1, v_suppressElabErrors_396_);
v___x_401_ = lean_st_mk_ref(v___x_365_);
lean_inc(v___x_401_);
v___x_402_ = lean_apply_5(v_x_333_, v___x_345_, v___x_401_, v___x_400_, v___y_397_, lean_box(0));
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_449_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_449_ == 0)
{
v___x_405_ = v___x_402_;
v_isShared_406_ = v_isSharedCheck_449_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_402_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_449_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v_traceState_410_; lean_object* v_traceState_411_; lean_object* v_env_412_; lean_object* v_messages_413_; lean_object* v_scopes_414_; lean_object* v_usedQuotCtxts_415_; lean_object* v_nextMacroScope_416_; lean_object* v_maxRecDepth_417_; lean_object* v_ngen_418_; lean_object* v_auxDeclNGen_419_; lean_object* v_infoState_420_; lean_object* v_snapshotTasks_421_; lean_object* v_prevLinterStates_422_; lean_object* v_codeQualityEntryTasks_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_447_; 
v___x_407_ = lean_st_ref_get(v___x_401_);
lean_dec(v___x_401_);
lean_dec(v___x_407_);
v___x_408_ = lean_st_ref_get(v___x_380_);
lean_dec(v___x_380_);
v___x_409_ = lean_st_ref_take(v_a_335_);
v_traceState_410_ = lean_ctor_get(v___x_409_, 9);
lean_inc_ref(v_traceState_410_);
v_traceState_411_ = lean_ctor_get(v___x_408_, 4);
lean_inc_ref(v_traceState_411_);
v_env_412_ = lean_ctor_get(v___x_409_, 0);
v_messages_413_ = lean_ctor_get(v___x_409_, 1);
v_scopes_414_ = lean_ctor_get(v___x_409_, 2);
v_usedQuotCtxts_415_ = lean_ctor_get(v___x_409_, 3);
v_nextMacroScope_416_ = lean_ctor_get(v___x_409_, 4);
v_maxRecDepth_417_ = lean_ctor_get(v___x_409_, 5);
v_ngen_418_ = lean_ctor_get(v___x_409_, 6);
v_auxDeclNGen_419_ = lean_ctor_get(v___x_409_, 7);
v_infoState_420_ = lean_ctor_get(v___x_409_, 8);
v_snapshotTasks_421_ = lean_ctor_get(v___x_409_, 10);
v_prevLinterStates_422_ = lean_ctor_get(v___x_409_, 11);
v_codeQualityEntryTasks_423_ = lean_ctor_get(v___x_409_, 12);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; 
v_unused_448_ = lean_ctor_get(v___x_409_, 9);
lean_dec(v_unused_448_);
v___x_425_ = v___x_409_;
v_isShared_426_ = v_isSharedCheck_447_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_codeQualityEntryTasks_423_);
lean_inc(v_prevLinterStates_422_);
lean_inc(v_snapshotTasks_421_);
lean_inc(v_infoState_420_);
lean_inc(v_auxDeclNGen_419_);
lean_inc(v_ngen_418_);
lean_inc(v_maxRecDepth_417_);
lean_inc(v_nextMacroScope_416_);
lean_inc(v_usedQuotCtxts_415_);
lean_inc(v_scopes_414_);
lean_inc(v_messages_413_);
lean_inc(v_env_412_);
lean_dec(v___x_409_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_447_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v_messages_427_; uint64_t v_tid_428_; lean_object* v_traces_429_; lean_object* v_traces_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_446_; 
v_messages_427_ = lean_ctor_get(v___x_408_, 6);
lean_inc_ref(v_messages_427_);
lean_dec(v___x_408_);
v_tid_428_ = lean_ctor_get_uint64(v_traceState_410_, sizeof(void*)*1);
v_traces_429_ = lean_ctor_get(v_traceState_410_, 0);
lean_inc_ref(v_traces_429_);
lean_dec_ref(v_traceState_410_);
v_traces_430_ = lean_ctor_get(v_traceState_411_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v_traceState_411_);
if (v_isSharedCheck_446_ == 0)
{
v___x_432_ = v_traceState_411_;
v_isShared_433_ = v_isSharedCheck_446_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_traces_430_);
lean_dec(v_traceState_411_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_446_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_434_ = l_Lean_MessageLog_append(v_messages_413_, v_messages_427_);
v___x_435_ = l_Lean_PersistentArray_append___redArg(v_traces_429_, v_traces_430_);
lean_dec_ref(v_traces_430_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___x_435_);
v___x_437_ = v___x_432_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_435_);
v___x_437_ = v_reuseFailAlloc_445_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_439_; 
lean_ctor_set_uint64(v___x_437_, sizeof(void*)*1, v_tid_428_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 9, v___x_437_);
lean_ctor_set(v___x_425_, 1, v___x_434_);
v___x_439_ = v___x_425_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_env_412_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_444_, 2, v_scopes_414_);
lean_ctor_set(v_reuseFailAlloc_444_, 3, v_usedQuotCtxts_415_);
lean_ctor_set(v_reuseFailAlloc_444_, 4, v_nextMacroScope_416_);
lean_ctor_set(v_reuseFailAlloc_444_, 5, v_maxRecDepth_417_);
lean_ctor_set(v_reuseFailAlloc_444_, 6, v_ngen_418_);
lean_ctor_set(v_reuseFailAlloc_444_, 7, v_auxDeclNGen_419_);
lean_ctor_set(v_reuseFailAlloc_444_, 8, v_infoState_420_);
lean_ctor_set(v_reuseFailAlloc_444_, 9, v___x_437_);
lean_ctor_set(v_reuseFailAlloc_444_, 10, v_snapshotTasks_421_);
lean_ctor_set(v_reuseFailAlloc_444_, 11, v_prevLinterStates_422_);
lean_ctor_set(v_reuseFailAlloc_444_, 12, v_codeQualityEntryTasks_423_);
v___x_439_ = v_reuseFailAlloc_444_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_440_ = lean_st_ref_put(v_a_335_, v___x_439_);
if (v_isShared_406_ == 0)
{
v___x_442_ = v___x_405_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_403_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_450_; 
lean_dec(v___x_401_);
lean_dec(v___x_380_);
v_a_450_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_450_);
lean_dec_ref_known(v___x_402_, 1);
if (lean_obj_tag(v_a_450_) == 0)
{
lean_object* v_msg_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v_msg_451_ = lean_ctor_get(v_a_450_, 1);
lean_inc_ref(v_msg_451_);
lean_dec_ref_known(v_a_450_, 2);
v___x_452_ = l_Lean_MessageData_toString(v_msg_451_);
v___x_453_ = lean_mk_io_user_error(v___x_452_);
v_a_354_ = v___x_453_;
goto v___jp_353_;
}
else
{
lean_object* v_id_454_; lean_object* v___x_455_; 
v_id_454_ = lean_ctor_get(v_a_450_, 0);
lean_inc(v_id_454_);
lean_dec_ref_known(v_a_450_, 2);
v___x_455_ = l_Lean_InternalExceptionId_getName(v_id_454_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
lean_dec(v_id_454_);
v_a_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_a_456_);
lean_dec_ref_known(v___x_455_, 1);
v___x_457_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20));
v___x_458_ = l_Lean_Name_toString(v_a_456_, v___x_340_);
v___x_459_ = lean_string_append(v___x_457_, v___x_458_);
lean_dec_ref(v___x_458_);
v_a_361_ = v___x_459_;
goto v___jp_360_;
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
lean_dec_ref_known(v___x_455_, 1);
v___x_460_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21));
v___x_461_ = l_Nat_reprFast(v_id_454_);
v___x_462_ = lean_string_append(v___x_460_, v___x_461_);
lean_dec_ref(v___x_461_);
v___x_463_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__22));
v___x_464_ = lean_string_append(v___x_462_, v___x_463_);
v_a_361_ = v___x_464_;
goto v___jp_360_;
}
}
}
}
v___jp_465_:
{
lean_object* v_toCold_470_; lean_object* v_currRecDepth_471_; lean_object* v_ref_472_; uint8_t v_suppressElabErrors_473_; lean_object* v_fileName_474_; lean_object* v_fileMap_475_; lean_object* v_currNamespace_476_; lean_object* v_openDecls_477_; lean_object* v_initHeartbeats_478_; lean_object* v_maxHeartbeats_479_; lean_object* v_quotContext_480_; lean_object* v_currMacroScope_481_; lean_object* v_cancelTk_x3f_482_; lean_object* v_inheritedTraceOptions_483_; 
v_toCold_470_ = lean_ctor_get(v___y_468_, 0);
lean_inc_ref(v_toCold_470_);
v_currRecDepth_471_ = lean_ctor_get(v___y_468_, 1);
lean_inc(v_currRecDepth_471_);
v_ref_472_ = lean_ctor_get(v___y_468_, 2);
lean_inc(v_ref_472_);
v_suppressElabErrors_473_ = lean_ctor_get_uint8(v___y_468_, sizeof(void*)*3 + 1);
lean_dec_ref(v___y_468_);
v_fileName_474_ = lean_ctor_get(v_toCold_470_, 0);
lean_inc_ref(v_fileName_474_);
v_fileMap_475_ = lean_ctor_get(v_toCold_470_, 1);
lean_inc_ref(v_fileMap_475_);
v_currNamespace_476_ = lean_ctor_get(v_toCold_470_, 4);
lean_inc(v_currNamespace_476_);
v_openDecls_477_ = lean_ctor_get(v_toCold_470_, 5);
lean_inc(v_openDecls_477_);
v_initHeartbeats_478_ = lean_ctor_get(v_toCold_470_, 6);
lean_inc(v_initHeartbeats_478_);
v_maxHeartbeats_479_ = lean_ctor_get(v_toCold_470_, 7);
lean_inc(v_maxHeartbeats_479_);
v_quotContext_480_ = lean_ctor_get(v_toCold_470_, 8);
lean_inc(v_quotContext_480_);
v_currMacroScope_481_ = lean_ctor_get(v_toCold_470_, 9);
lean_inc(v_currMacroScope_481_);
v_cancelTk_x3f_482_ = lean_ctor_get(v_toCold_470_, 10);
lean_inc(v_cancelTk_x3f_482_);
v_inheritedTraceOptions_483_ = lean_ctor_get(v_toCold_470_, 11);
lean_inc_ref(v_inheritedTraceOptions_483_);
lean_dec_ref(v_toCold_470_);
v___y_382_ = v___y_466_;
v___y_383_ = v___y_467_;
v_fileName_384_ = v_fileName_474_;
v_fileMap_385_ = v_fileMap_475_;
v_currNamespace_386_ = v_currNamespace_476_;
v_openDecls_387_ = v_openDecls_477_;
v_initHeartbeats_388_ = v_initHeartbeats_478_;
v_maxHeartbeats_389_ = v_maxHeartbeats_479_;
v_quotContext_390_ = v_quotContext_480_;
v_currMacroScope_391_ = v_currMacroScope_481_;
v_cancelTk_x3f_392_ = v_cancelTk_x3f_482_;
v_inheritedTraceOptions_393_ = v_inheritedTraceOptions_483_;
v_currRecDepth_394_ = v_currRecDepth_471_;
v_ref_395_ = v_ref_472_;
v_suppressElabErrors_396_ = v_suppressElabErrors_473_;
v___y_397_ = v___y_469_;
goto v___jp_381_;
}
v___jp_484_:
{
if (v___y_489_ == 0)
{
lean_object* v___x_490_; lean_object* v_env_491_; lean_object* v_nextMacroScope_492_; lean_object* v_ngen_493_; lean_object* v_auxDeclNGen_494_; lean_object* v_traceState_495_; lean_object* v_messages_496_; lean_object* v_infoState_497_; lean_object* v_snapshotTasks_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_507_; 
v___x_490_ = lean_st_ref_take(v___y_486_);
v_env_491_ = lean_ctor_get(v___x_490_, 0);
v_nextMacroScope_492_ = lean_ctor_get(v___x_490_, 1);
v_ngen_493_ = lean_ctor_get(v___x_490_, 2);
v_auxDeclNGen_494_ = lean_ctor_get(v___x_490_, 3);
v_traceState_495_ = lean_ctor_get(v___x_490_, 4);
v_messages_496_ = lean_ctor_get(v___x_490_, 6);
v_infoState_497_ = lean_ctor_get(v___x_490_, 7);
v_snapshotTasks_498_ = lean_ctor_get(v___x_490_, 8);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_507_ == 0)
{
lean_object* v_unused_508_; 
v_unused_508_ = lean_ctor_get(v___x_490_, 5);
lean_dec(v_unused_508_);
v___x_500_ = v___x_490_;
v_isShared_501_ = v_isSharedCheck_507_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_snapshotTasks_498_);
lean_inc(v_infoState_497_);
lean_inc(v_messages_496_);
lean_inc(v_traceState_495_);
lean_inc(v_auxDeclNGen_494_);
lean_inc(v_ngen_493_);
lean_inc(v_nextMacroScope_492_);
lean_inc(v_env_491_);
lean_dec(v___x_490_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_507_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_502_ = l_Lean_Kernel_enableDiag(v_env_491_, v___y_487_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 5, v___x_375_);
lean_ctor_set(v___x_500_, 0, v___x_502_);
v___x_504_ = v___x_500_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_nextMacroScope_492_);
lean_ctor_set(v_reuseFailAlloc_506_, 2, v_ngen_493_);
lean_ctor_set(v_reuseFailAlloc_506_, 3, v_auxDeclNGen_494_);
lean_ctor_set(v_reuseFailAlloc_506_, 4, v_traceState_495_);
lean_ctor_set(v_reuseFailAlloc_506_, 5, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_506_, 6, v_messages_496_);
lean_ctor_set(v_reuseFailAlloc_506_, 7, v_infoState_497_);
lean_ctor_set(v_reuseFailAlloc_506_, 8, v_snapshotTasks_498_);
v___x_504_ = v_reuseFailAlloc_506_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_505_; 
v___x_505_ = lean_st_ref_put(v___y_486_, v___x_504_);
v___y_466_ = v___y_485_;
v___y_467_ = v___y_487_;
v___y_468_ = v___y_488_;
v___y_469_ = v___y_486_;
goto v___jp_465_;
}
}
}
else
{
v___y_466_ = v___y_485_;
v___y_467_ = v___y_487_;
v___y_468_ = v___y_488_;
v___y_469_ = v___y_486_;
goto v___jp_465_;
}
}
v___jp_513_:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; lean_object* v___x_520_; lean_object* v_env_521_; uint8_t v___x_522_; 
v___x_515_ = l_Lean_maxRecDepth;
v___x_516_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24);
lean_inc(v___x_510_);
lean_inc(v_cancelTk_x3f_352_);
lean_inc(v___x_379_);
lean_inc(v_openDecls_364_);
lean_inc(v_currNamespace_363_);
lean_inc_ref(v_fileMap_350_);
lean_inc_ref(v_fileName_349_);
v___x_517_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_517_, 0, v_fileName_349_);
lean_ctor_set(v___x_517_, 1, v_fileMap_350_);
lean_ctor_set(v___x_517_, 2, v___x_366_);
lean_ctor_set(v___x_517_, 3, v___x_516_);
lean_ctor_set(v___x_517_, 4, v_currNamespace_363_);
lean_ctor_set(v___x_517_, 5, v_openDecls_364_);
lean_ctor_set(v___x_517_, 6, v___x_379_);
lean_ctor_set(v___x_517_, 7, v___x_367_);
lean_ctor_set(v___x_517_, 8, v___x_368_);
lean_ctor_set(v___x_517_, 9, v___x_369_);
lean_ctor_set(v___x_517_, 10, v_cancelTk_x3f_352_);
lean_ctor_set(v___x_517_, 11, v___x_510_);
v___x_518_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_518_, 0, v___x_517_);
lean_ctor_set(v___x_518_, 1, v___x_342_);
lean_ctor_set(v___x_518_, 2, v___x_370_);
lean_ctor_set_uint8(v___x_518_, sizeof(void*)*3, v___x_512_);
lean_ctor_set_uint8(v___x_518_, sizeof(void*)*3 + 1, v___x_338_);
v___x_519_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_331_, v___x_511_);
v___x_520_ = lean_st_ref_get(v___y_514_);
v_env_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc_ref(v_env_521_);
lean_dec(v___x_520_);
v___x_522_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_521_);
lean_dec_ref(v_env_521_);
if (v___x_519_ == 0)
{
if (v___x_522_ == 0)
{
lean_dec_ref_known(v___x_518_, 3);
lean_inc(v_cancelTk_x3f_352_);
lean_inc_ref(v_fileMap_350_);
lean_inc_ref(v_fileName_349_);
v___y_382_ = v___x_515_;
v___y_383_ = v___x_519_;
v_fileName_384_ = v_fileName_349_;
v_fileMap_385_ = v_fileMap_350_;
v_currNamespace_386_ = v_currNamespace_363_;
v_openDecls_387_ = v_openDecls_364_;
v_initHeartbeats_388_ = v___x_379_;
v_maxHeartbeats_389_ = v___x_367_;
v_quotContext_390_ = v___x_368_;
v_currMacroScope_391_ = v___x_369_;
v_cancelTk_x3f_392_ = v_cancelTk_x3f_352_;
v_inheritedTraceOptions_393_ = v___x_510_;
v_currRecDepth_394_ = v___x_342_;
v_ref_395_ = v___x_370_;
v_suppressElabErrors_396_ = v___x_338_;
v___y_397_ = v___y_514_;
goto v___jp_381_;
}
else
{
lean_dec(v___x_510_);
lean_dec(v___x_379_);
lean_dec(v_openDecls_364_);
lean_dec(v_currNamespace_363_);
v___y_485_ = v___x_515_;
v___y_486_ = v___y_514_;
v___y_487_ = v___x_519_;
v___y_488_ = v___x_518_;
v___y_489_ = v___x_519_;
goto v___jp_484_;
}
}
else
{
lean_dec(v___x_510_);
lean_dec(v___x_379_);
lean_dec(v_openDecls_364_);
lean_dec(v_currNamespace_363_);
v___y_485_ = v___x_515_;
v___y_486_ = v___y_514_;
v___y_487_ = v___x_519_;
v___y_488_ = v___x_518_;
v___y_489_ = v___x_522_;
goto v___jp_484_;
}
}
v___jp_524_:
{
if (v___y_525_ == 0)
{
lean_object* v___x_526_; lean_object* v_env_527_; lean_object* v_nextMacroScope_528_; lean_object* v_ngen_529_; lean_object* v_auxDeclNGen_530_; lean_object* v_traceState_531_; lean_object* v_messages_532_; lean_object* v_infoState_533_; lean_object* v_snapshotTasks_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_543_; 
v___x_526_ = lean_st_ref_take(v___x_380_);
v_env_527_ = lean_ctor_get(v___x_526_, 0);
v_nextMacroScope_528_ = lean_ctor_get(v___x_526_, 1);
v_ngen_529_ = lean_ctor_get(v___x_526_, 2);
v_auxDeclNGen_530_ = lean_ctor_get(v___x_526_, 3);
v_traceState_531_ = lean_ctor_get(v___x_526_, 4);
v_messages_532_ = lean_ctor_get(v___x_526_, 6);
v_infoState_533_ = lean_ctor_get(v___x_526_, 7);
v_snapshotTasks_534_ = lean_ctor_get(v___x_526_, 8);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_543_ == 0)
{
lean_object* v_unused_544_; 
v_unused_544_ = lean_ctor_get(v___x_526_, 5);
lean_dec(v_unused_544_);
v___x_536_ = v___x_526_;
v_isShared_537_ = v_isSharedCheck_543_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_snapshotTasks_534_);
lean_inc(v_infoState_533_);
lean_inc(v_messages_532_);
lean_inc(v_traceState_531_);
lean_inc(v_auxDeclNGen_530_);
lean_inc(v_ngen_529_);
lean_inc(v_nextMacroScope_528_);
lean_inc(v_env_527_);
lean_dec(v___x_526_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_543_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_538_ = l_Lean_Kernel_enableDiag(v_env_527_, v___x_512_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 5, v___x_375_);
lean_ctor_set(v___x_536_, 0, v___x_538_);
v___x_540_ = v___x_536_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_nextMacroScope_528_);
lean_ctor_set(v_reuseFailAlloc_542_, 2, v_ngen_529_);
lean_ctor_set(v_reuseFailAlloc_542_, 3, v_auxDeclNGen_530_);
lean_ctor_set(v_reuseFailAlloc_542_, 4, v_traceState_531_);
lean_ctor_set(v_reuseFailAlloc_542_, 5, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_542_, 6, v_messages_532_);
lean_ctor_set(v_reuseFailAlloc_542_, 7, v_infoState_533_);
lean_ctor_set(v_reuseFailAlloc_542_, 8, v_snapshotTasks_534_);
v___x_540_ = v_reuseFailAlloc_542_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_541_; 
v___x_541_ = lean_st_ref_put(v___x_380_, v___x_540_);
lean_inc(v___x_380_);
v___y_514_ = v___x_380_;
goto v___jp_513_;
}
}
}
else
{
lean_inc(v___x_380_);
v___y_514_ = v___x_380_;
goto v___jp_513_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___boxed(lean_object* v_env_547_, lean_object* v_mctx_548_, lean_object* v_lctx_549_, lean_object* v_opts_550_, lean_object* v_namingCtx_551_, lean_object* v_x_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_547_, v_mctx_548_, v_lctx_549_, v_opts_550_, v_namingCtx_551_, v_x_552_, v_a_553_, v_a_554_);
lean_dec(v_a_554_);
lean_dec_ref(v_a_553_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope(lean_object* v_00_u03b1_557_, lean_object* v_env_558_, lean_object* v_mctx_559_, lean_object* v_lctx_560_, lean_object* v_opts_561_, lean_object* v_namingCtx_562_, lean_object* v_x_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_558_, v_mctx_559_, v_lctx_560_, v_opts_561_, v_namingCtx_562_, v_x_563_, v_a_564_, v_a_565_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___boxed(lean_object* v_00_u03b1_568_, lean_object* v_env_569_, lean_object* v_mctx_570_, lean_object* v_lctx_571_, lean_object* v_opts_572_, lean_object* v_namingCtx_573_, lean_object* v_x_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope(v_00_u03b1_568_, v_env_569_, v_mctx_570_, v_lctx_571_, v_opts_572_, v_namingCtx_573_, v_x_574_, v_a_575_, v_a_576_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
return v_res_578_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(lean_object* v_stx_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_Syntax_getKind(v_stx_582_);
if (lean_obj_tag(v___x_583_) == 1)
{
lean_object* v_pre_584_; 
v_pre_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_pre_584_);
if (lean_obj_tag(v_pre_584_) == 1)
{
lean_object* v_pre_585_; 
v_pre_585_ = lean_ctor_get(v_pre_584_, 0);
lean_inc(v_pre_585_);
if (lean_obj_tag(v_pre_585_) == 1)
{
lean_object* v_pre_586_; 
v_pre_586_ = lean_ctor_get(v_pre_585_, 0);
lean_inc(v_pre_586_);
if (lean_obj_tag(v_pre_586_) == 1)
{
lean_object* v_pre_587_; 
v_pre_587_ = lean_ctor_get(v_pre_586_, 0);
if (lean_obj_tag(v_pre_587_) == 0)
{
lean_object* v_str_588_; lean_object* v_str_589_; lean_object* v_str_590_; lean_object* v_str_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v_str_588_ = lean_ctor_get(v___x_583_, 1);
lean_inc_ref(v_str_588_);
lean_dec_ref_known(v___x_583_, 2);
v_str_589_ = lean_ctor_get(v_pre_584_, 1);
lean_inc_ref(v_str_589_);
lean_dec_ref_known(v_pre_584_, 2);
v_str_590_ = lean_ctor_get(v_pre_585_, 1);
lean_inc_ref(v_str_590_);
lean_dec_ref_known(v_pre_585_, 2);
v_str_591_ = lean_ctor_get(v_pre_586_, 1);
lean_inc_ref(v_str_591_);
lean_dec_ref_known(v_pre_586_, 2);
v___x_592_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_593_ = lean_string_dec_eq(v_str_591_, v___x_592_);
lean_dec_ref(v_str_591_);
if (v___x_593_ == 0)
{
lean_dec_ref(v_str_590_);
lean_dec_ref(v_str_589_);
lean_dec_ref(v_str_588_);
return v___x_593_;
}
else
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0));
v___x_595_ = lean_string_dec_eq(v_str_590_, v___x_594_);
lean_dec_ref(v_str_590_);
if (v___x_595_ == 0)
{
lean_dec_ref(v_str_589_);
lean_dec_ref(v_str_588_);
return v___x_595_;
}
else
{
lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_596_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_597_ = lean_string_dec_eq(v_str_589_, v___x_596_);
lean_dec_ref(v_str_589_);
if (v___x_597_ == 0)
{
lean_dec_ref(v_str_588_);
return v___x_597_;
}
else
{
lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_598_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__1));
v___x_599_ = lean_string_dec_eq(v_str_588_, v___x_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_600_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__2));
v___x_601_ = lean_string_dec_eq(v_str_588_, v___x_600_);
lean_dec_ref(v_str_588_);
return v___x_601_;
}
else
{
lean_dec_ref(v_str_588_);
return v___x_599_;
}
}
}
}
}
else
{
uint8_t v___x_602_; 
lean_dec_ref_known(v_pre_586_, 2);
lean_dec_ref_known(v_pre_585_, 2);
lean_dec_ref_known(v_pre_584_, 2);
lean_dec_ref_known(v___x_583_, 2);
v___x_602_ = 0;
return v___x_602_;
}
}
else
{
uint8_t v___x_603_; 
lean_dec_ref_known(v_pre_585_, 2);
lean_dec(v_pre_586_);
lean_dec_ref_known(v_pre_584_, 2);
lean_dec_ref_known(v___x_583_, 2);
v___x_603_ = 0;
return v___x_603_;
}
}
else
{
uint8_t v___x_604_; 
lean_dec(v_pre_585_);
lean_dec_ref_known(v_pre_584_, 2);
lean_dec_ref_known(v___x_583_, 2);
v___x_604_ = 0;
return v___x_604_;
}
}
else
{
uint8_t v___x_605_; 
lean_dec(v_pre_584_);
lean_dec_ref_known(v___x_583_, 2);
v___x_605_ = 0;
return v___x_605_;
}
}
else
{
uint8_t v___x_606_; 
lean_dec(v___x_583_);
v___x_606_ = 0;
return v___x_606_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___boxed(lean_object* v_stx_607_){
_start:
{
uint8_t v_res_608_; lean_object* v_r_609_; 
v_res_608_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(v_stx_607_);
v_r_609_ = lean_box(v_res_608_);
return v_r_609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx(lean_object* v_x_610_){
_start:
{
if (lean_obj_tag(v_x_610_) == 0)
{
lean_object* v___x_611_; 
v___x_611_ = lean_unsigned_to_nat(0u);
return v___x_611_;
}
else
{
lean_object* v___x_612_; 
v___x_612_ = lean_unsigned_to_nat(1u);
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx___boxed(lean_object* v_x_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx(v_x_613_);
lean_dec(v_x_613_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(lean_object* v_t_615_, lean_object* v_k_616_){
_start:
{
if (lean_obj_tag(v_t_615_) == 0)
{
lean_object* v_tacticSeq_617_; lean_object* v_insertPos_618_; lean_object* v___x_619_; 
v_tacticSeq_617_ = lean_ctor_get(v_t_615_, 0);
lean_inc(v_tacticSeq_617_);
v_insertPos_618_ = lean_ctor_get(v_t_615_, 1);
lean_inc(v_insertPos_618_);
lean_dec_ref_known(v_t_615_, 2);
v___x_619_ = lean_apply_2(v_k_616_, v_tacticSeq_617_, v_insertPos_618_);
return v___x_619_;
}
else
{
return v_k_616_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim(lean_object* v_motive_620_, lean_object* v_ctorIdx_621_, lean_object* v_t_622_, lean_object* v_h_623_, lean_object* v_k_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_622_, v_k_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___boxed(lean_object* v_motive_626_, lean_object* v_ctorIdx_627_, lean_object* v_t_628_, lean_object* v_h_629_, lean_object* v_k_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim(v_motive_626_, v_ctorIdx_627_, v_t_628_, v_h_629_, v_k_630_);
lean_dec(v_ctorIdx_627_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_unsolvedGoal_elim___redArg(lean_object* v_t_632_, lean_object* v_unsolvedGoal_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_632_, v_unsolvedGoal_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_unsolvedGoal_elim(lean_object* v_motive_635_, lean_object* v_t_636_, lean_object* v_h_637_, lean_object* v_unsolvedGoal_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_636_, v_unsolvedGoal_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_sorryTactic_elim___redArg(lean_object* v_t_640_, lean_object* v_sorryTactic_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_640_, v_sorryTactic_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_sorryTactic_elim(lean_object* v_motive_643_, lean_object* v_t_644_, lean_object* v_h_645_, lean_object* v_sorryTactic_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_644_, v_sorryTactic_646_);
return v___x_647_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed__const__1(void){
_start:
{
uint32_t v___x_651_; lean_object* v___x_652_; 
v___x_651_ = 32;
v___x_652_ = lean_box_uint32(v___x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(lean_object* v_tacticSeq_653_, lean_object* v_fileMap_654_){
_start:
{
uint8_t v___x_655_; lean_object* v___x_656_; 
v___x_655_ = 0;
v___x_656_ = l_Lean_Syntax_getPos_x3f(v_tacticSeq_653_, v___x_655_);
if (lean_obj_tag(v___x_656_) == 1)
{
lean_object* v_val_657_; lean_object* v___x_658_; 
v_val_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_val_657_);
lean_dec_ref_known(v___x_656_, 1);
v___x_658_ = l_Lean_Syntax_getTailPos_x3f(v_tacticSeq_653_, v___x_655_);
if (lean_obj_tag(v___x_658_) == 1)
{
lean_object* v_val_659_; lean_object* v_startPos_660_; lean_object* v_line_661_; lean_object* v_column_662_; lean_object* v_endPos_663_; lean_object* v_line_664_; uint8_t v___x_665_; 
v_val_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_val_659_);
lean_dec_ref_known(v___x_658_, 1);
lean_inc_ref(v_fileMap_654_);
v_startPos_660_ = l_Lean_FileMap_toPosition(v_fileMap_654_, v_val_657_);
lean_dec(v_val_657_);
v_line_661_ = lean_ctor_get(v_startPos_660_, 0);
lean_inc(v_line_661_);
v_column_662_ = lean_ctor_get(v_startPos_660_, 1);
lean_inc(v_column_662_);
lean_dec_ref(v_startPos_660_);
v_endPos_663_ = l_Lean_FileMap_toPosition(v_fileMap_654_, v_val_659_);
lean_dec(v_val_659_);
v_line_664_ = lean_ctor_get(v_endPos_663_, 0);
lean_inc(v_line_664_);
lean_dec_ref(v_endPos_663_);
v___x_665_ = lean_nat_dec_eq(v_line_661_, v_line_664_);
lean_dec(v_line_664_);
lean_dec(v_line_661_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_666_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__0));
v___x_667_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed__const__1;
v___x_668_ = l_List_replicateTR___redArg(v_column_662_, v___x_667_);
v___x_669_ = lean_string_mk(v___x_668_);
v___x_670_ = lean_string_append(v___x_666_, v___x_669_);
lean_dec_ref(v___x_669_);
return v___x_670_;
}
else
{
lean_object* v___x_671_; 
lean_dec(v_column_662_);
v___x_671_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__1));
return v___x_671_;
}
}
else
{
lean_object* v___x_672_; 
lean_dec(v___x_658_);
lean_dec(v_val_657_);
lean_dec_ref(v_fileMap_654_);
v___x_672_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__2));
return v___x_672_;
}
}
else
{
lean_object* v___x_673_; 
lean_dec(v___x_656_);
lean_dec_ref(v_fileMap_654_);
v___x_673_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__2));
return v___x_673_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed(lean_object* v_tacticSeq_674_, lean_object* v_fileMap_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(v_tacticSeq_674_, v_fileMap_675_);
lean_dec(v_tacticSeq_674_);
return v_res_676_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_679_ = lean_string_utf8_byte_size(v___x_678_);
return v___x_679_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_680_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1);
v___x_681_ = lean_unsigned_to_nat(0u);
v___x_682_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_683_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
lean_ctor_set(v___x_683_, 1, v___x_681_);
lean_ctor_set(v___x_683_, 2, v___x_680_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx(lean_object* v_p_684_){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_685_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_686_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2);
lean_inc(v_p_684_);
v___x_687_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
lean_ctor_set(v___x_687_, 1, v_p_684_);
lean_ctor_set(v___x_687_, 2, v___x_686_);
lean_ctor_set(v___x_687_, 3, v_p_684_);
v___x_688_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
lean_ctor_set(v___x_688_, 1, v___x_685_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(lean_object* v_range_689_){
_start:
{
lean_object* v_start_690_; lean_object* v_stop_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_701_; 
v_start_690_ = lean_ctor_get(v_range_689_, 0);
v_stop_691_ = lean_ctor_get(v_range_689_, 1);
v_isSharedCheck_701_ = !lean_is_exclusive(v_range_689_);
if (v_isSharedCheck_701_ == 0)
{
v___x_693_ = v_range_689_;
v_isShared_694_ = v_isSharedCheck_701_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_stop_691_);
lean_inc(v_start_690_);
lean_dec(v_range_689_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_701_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_695_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_696_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2);
v___x_697_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
lean_ctor_set(v___x_697_, 1, v_start_690_);
lean_ctor_set(v___x_697_, 2, v___x_696_);
lean_ctor_set(v___x_697_, 3, v_stop_691_);
if (v_isShared_694_ == 0)
{
lean_ctor_set_tag(v___x_693_, 2);
lean_ctor_set(v___x_693_, 1, v___x_695_);
lean_ctor_set(v___x_693_, 0, v___x_697_);
v___x_699_ = v___x_693_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v___x_695_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(lean_object* v_mc_x3f_702_, lean_object* v_nc_x3f_703_, lean_object* v_msg_704_, lean_object* v_acc_705_){
_start:
{
switch(lean_obj_tag(v_msg_704_))
{
case 3:
{
lean_object* v_a_706_; lean_object* v_a_707_; lean_object* v___x_708_; 
lean_dec(v_mc_x3f_702_);
v_a_706_ = lean_ctor_get(v_msg_704_, 0);
v_a_707_ = lean_ctor_get(v_msg_704_, 1);
lean_inc_ref(v_a_706_);
v___x_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_708_, 0, v_a_706_);
v_mc_x3f_702_ = v___x_708_;
v_msg_704_ = v_a_707_;
goto _start;
}
case 4:
{
lean_object* v_a_710_; lean_object* v_a_711_; lean_object* v___x_712_; 
lean_dec(v_nc_x3f_703_);
v_a_710_ = lean_ctor_get(v_msg_704_, 0);
v_a_711_ = lean_ctor_get(v_msg_704_, 1);
lean_inc_ref(v_a_710_);
v___x_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_712_, 0, v_a_710_);
v_nc_x3f_703_ = v___x_712_;
v_msg_704_ = v_a_711_;
goto _start;
}
case 5:
{
lean_object* v_a_714_; 
v_a_714_ = lean_ctor_get(v_msg_704_, 1);
v_msg_704_ = v_a_714_;
goto _start;
}
case 6:
{
lean_object* v_a_716_; 
v_a_716_ = lean_ctor_get(v_msg_704_, 0);
v_msg_704_ = v_a_716_;
goto _start;
}
case 8:
{
lean_object* v_a_718_; 
v_a_718_ = lean_ctor_get(v_msg_704_, 1);
v_msg_704_ = v_a_718_;
goto _start;
}
case 7:
{
lean_object* v_a_720_; lean_object* v_a_721_; lean_object* v___x_722_; 
v_a_720_ = lean_ctor_get(v_msg_704_, 0);
v_a_721_ = lean_ctor_get(v_msg_704_, 1);
lean_inc(v_nc_x3f_703_);
lean_inc(v_mc_x3f_702_);
v___x_722_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_702_, v_nc_x3f_703_, v_a_720_, v_acc_705_);
v_msg_704_ = v_a_721_;
v_acc_705_ = v___x_722_;
goto _start;
}
case 2:
{
lean_object* v_a_724_; 
v_a_724_ = lean_ctor_get(v_msg_704_, 1);
v_msg_704_ = v_a_724_;
goto _start;
}
case 9:
{
lean_object* v_msg_726_; lean_object* v_children_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; 
v_msg_726_ = lean_ctor_get(v_msg_704_, 1);
v_children_727_ = lean_ctor_get(v_msg_704_, 2);
lean_inc(v_nc_x3f_703_);
lean_inc(v_mc_x3f_702_);
v___x_728_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_702_, v_nc_x3f_703_, v_msg_726_, v_acc_705_);
v___x_729_ = lean_unsigned_to_nat(0u);
v___x_730_ = lean_array_get_size(v_children_727_);
v___x_731_ = lean_nat_dec_lt(v___x_729_, v___x_730_);
if (v___x_731_ == 0)
{
lean_dec(v_nc_x3f_703_);
lean_dec(v_mc_x3f_702_);
return v___x_728_;
}
else
{
uint8_t v___x_732_; 
v___x_732_ = lean_nat_dec_le(v___x_730_, v___x_730_);
if (v___x_732_ == 0)
{
if (v___x_731_ == 0)
{
lean_dec(v_nc_x3f_703_);
lean_dec(v_mc_x3f_702_);
return v___x_728_;
}
else
{
size_t v___x_733_; size_t v___x_734_; lean_object* v___x_735_; 
v___x_733_ = ((size_t)0ULL);
v___x_734_ = lean_usize_of_nat(v___x_730_);
v___x_735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_702_, v_nc_x3f_703_, v_children_727_, v___x_733_, v___x_734_, v___x_728_);
return v___x_735_;
}
}
else
{
size_t v___x_736_; size_t v___x_737_; lean_object* v___x_738_; 
v___x_736_ = ((size_t)0ULL);
v___x_737_ = lean_usize_of_nat(v___x_730_);
v___x_738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_702_, v_nc_x3f_703_, v_children_727_, v___x_736_, v___x_737_, v___x_728_);
return v___x_738_;
}
}
}
case 1:
{
if (lean_obj_tag(v_mc_x3f_702_) == 1)
{
if (lean_obj_tag(v_nc_x3f_703_) == 1)
{
lean_object* v_a_739_; lean_object* v_val_740_; lean_object* v_val_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v_a_739_ = lean_ctor_get(v_msg_704_, 0);
v_val_740_ = lean_ctor_get(v_mc_x3f_702_, 0);
lean_inc(v_val_740_);
lean_dec_ref_known(v_mc_x3f_702_, 1);
v_val_741_ = lean_ctor_get(v_nc_x3f_703_, 0);
lean_inc(v_val_741_);
lean_dec_ref_known(v_nc_x3f_703_, 1);
lean_inc(v_a_739_);
v___x_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_742_, 0, v_val_741_);
lean_ctor_set(v___x_742_, 1, v_a_739_);
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v_val_740_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = lean_array_push(v_acc_705_, v___x_743_);
return v___x_744_;
}
else
{
lean_dec_ref_known(v_mc_x3f_702_, 1);
lean_dec(v_nc_x3f_703_);
return v_acc_705_;
}
}
else
{
lean_dec(v_nc_x3f_703_);
lean_dec(v_mc_x3f_702_);
return v_acc_705_;
}
}
default: 
{
lean_dec(v_nc_x3f_703_);
lean_dec(v_mc_x3f_702_);
return v_acc_705_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(lean_object* v_mc_x3f_745_, lean_object* v_nc_x3f_746_, lean_object* v_as_747_, size_t v_i_748_, size_t v_stop_749_, lean_object* v_b_750_){
_start:
{
uint8_t v___x_751_; 
v___x_751_ = lean_usize_dec_eq(v_i_748_, v_stop_749_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; size_t v___x_754_; size_t v___x_755_; 
v___x_752_ = lean_array_uget_borrowed(v_as_747_, v_i_748_);
lean_inc(v_nc_x3f_746_);
lean_inc(v_mc_x3f_745_);
v___x_753_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_745_, v_nc_x3f_746_, v___x_752_, v_b_750_);
v___x_754_ = ((size_t)1ULL);
v___x_755_ = lean_usize_add(v_i_748_, v___x_754_);
v_i_748_ = v___x_755_;
v_b_750_ = v___x_753_;
goto _start;
}
else
{
lean_dec(v_nc_x3f_746_);
lean_dec(v_mc_x3f_745_);
return v_b_750_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0___boxed(lean_object* v_mc_x3f_757_, lean_object* v_nc_x3f_758_, lean_object* v_as_759_, lean_object* v_i_760_, lean_object* v_stop_761_, lean_object* v_b_762_){
_start:
{
size_t v_i_boxed_763_; size_t v_stop_boxed_764_; lean_object* v_res_765_; 
v_i_boxed_763_ = lean_unbox_usize(v_i_760_);
lean_dec(v_i_760_);
v_stop_boxed_764_ = lean_unbox_usize(v_stop_761_);
lean_dec(v_stop_761_);
v_res_765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_757_, v_nc_x3f_758_, v_as_759_, v_i_boxed_763_, v_stop_boxed_764_, v_b_762_);
lean_dec_ref(v_as_759_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go___boxed(lean_object* v_mc_x3f_766_, lean_object* v_nc_x3f_767_, lean_object* v_msg_768_, lean_object* v_acc_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_766_, v_nc_x3f_767_, v_msg_768_, v_acc_769_);
lean_dec_ref(v_msg_768_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(lean_object* v_msg_773_){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_774_ = lean_box(0);
v___x_775_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___closed__0));
v___x_776_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v___x_774_, v___x_774_, v_msg_773_, v___x_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___boxed(lean_object* v_msg_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_msg_777_);
lean_dec_ref(v_msg_777_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f(lean_object* v_range_781_, lean_object* v_stx_782_){
_start:
{
lean_object* v___x_783_; 
lean_inc(v_stx_782_);
v___x_783_ = l_Lean_Syntax_getKind(v_stx_782_);
if (lean_obj_tag(v___x_783_) == 1)
{
lean_object* v_pre_784_; 
v_pre_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_pre_784_);
if (lean_obj_tag(v_pre_784_) == 1)
{
lean_object* v_pre_785_; 
v_pre_785_ = lean_ctor_get(v_pre_784_, 0);
lean_inc(v_pre_785_);
if (lean_obj_tag(v_pre_785_) == 1)
{
lean_object* v_pre_786_; 
v_pre_786_ = lean_ctor_get(v_pre_785_, 0);
lean_inc(v_pre_786_);
if (lean_obj_tag(v_pre_786_) == 1)
{
lean_object* v_pre_787_; 
v_pre_787_ = lean_ctor_get(v_pre_786_, 0);
if (lean_obj_tag(v_pre_787_) == 0)
{
lean_object* v_str_788_; lean_object* v_str_789_; lean_object* v_str_790_; lean_object* v_str_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v_str_788_ = lean_ctor_get(v___x_783_, 1);
lean_inc_ref(v_str_788_);
lean_dec_ref_known(v___x_783_, 2);
v_str_789_ = lean_ctor_get(v_pre_784_, 1);
lean_inc_ref(v_str_789_);
lean_dec_ref_known(v_pre_784_, 2);
v_str_790_ = lean_ctor_get(v_pre_785_, 1);
lean_inc_ref(v_str_790_);
lean_dec_ref_known(v_pre_785_, 2);
v_str_791_ = lean_ctor_get(v_pre_786_, 1);
lean_inc_ref(v_str_791_);
lean_dec_ref_known(v_pre_786_, 2);
v___x_792_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_793_ = lean_string_dec_eq(v_str_791_, v___x_792_);
lean_dec_ref(v_str_791_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; 
lean_dec_ref(v_str_790_);
lean_dec_ref(v_str_789_);
lean_dec_ref(v_str_788_);
lean_dec(v_stx_782_);
lean_dec_ref(v_range_781_);
v___x_794_ = lean_box(0);
return v___x_794_;
}
else
{
lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_795_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0));
v___x_796_ = lean_string_dec_eq(v_str_790_, v___x_795_);
lean_dec_ref(v_str_790_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; 
lean_dec_ref(v_str_789_);
lean_dec_ref(v_str_788_);
lean_dec(v_stx_782_);
lean_dec_ref(v_range_781_);
v___x_797_ = lean_box(0);
return v___x_797_;
}
else
{
lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_798_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_799_ = lean_string_dec_eq(v_str_789_, v___x_798_);
lean_dec_ref(v_str_789_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; 
lean_dec_ref(v_str_788_);
lean_dec(v_stx_782_);
lean_dec_ref(v_range_781_);
v___x_800_ = lean_box(0);
return v___x_800_;
}
else
{
lean_object* v___x_801_; uint8_t v___x_802_; 
v___x_801_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__0));
v___x_802_ = lean_string_dec_eq(v_str_788_, v___x_801_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_803_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__1));
v___x_804_ = lean_string_dec_eq(v_str_788_, v___x_803_);
lean_dec_ref(v_str_788_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; 
lean_dec(v_stx_782_);
lean_dec_ref(v_range_781_);
v___x_805_ = lean_box(0);
return v___x_805_;
}
else
{
lean_object* v___x_806_; lean_object* v_body_807_; lean_object* v___y_809_; lean_object* v___x_812_; 
v___x_806_ = lean_unsigned_to_nat(1u);
v_body_807_ = l_Lean_Syntax_getArg(v_stx_782_, v___x_806_);
v___x_812_ = l_Lean_Syntax_getTailPos_x3f(v_body_807_, v___x_802_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_813_ = lean_unsigned_to_nat(2u);
v___x_814_ = l_Lean_Syntax_getArg(v_stx_782_, v___x_813_);
lean_dec(v_stx_782_);
v___x_815_ = l_Lean_Syntax_getPos_x3f(v___x_814_, v___x_802_);
lean_dec(v___x_814_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_stop_816_; 
v_stop_816_ = lean_ctor_get(v_range_781_, 1);
lean_inc(v_stop_816_);
lean_dec_ref(v_range_781_);
v___y_809_ = v_stop_816_;
goto v___jp_808_;
}
else
{
lean_object* v_val_817_; 
lean_dec_ref(v_range_781_);
v_val_817_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_val_817_);
lean_dec_ref_known(v___x_815_, 1);
v___y_809_ = v_val_817_;
goto v___jp_808_;
}
}
else
{
lean_object* v_val_818_; 
lean_dec(v_stx_782_);
lean_dec_ref(v_range_781_);
v_val_818_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_val_818_);
lean_dec_ref_known(v___x_812_, 1);
v___y_809_ = v_val_818_;
goto v___jp_808_;
}
v___jp_808_:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_810_, 0, v_body_807_);
lean_ctor_set(v___x_810_, 1, v___y_809_);
v___x_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
return v___x_811_;
}
}
}
else
{
lean_object* v___x_819_; lean_object* v_body_820_; lean_object* v___y_822_; uint8_t v___x_825_; lean_object* v___x_826_; 
lean_dec_ref(v_str_788_);
v___x_819_ = lean_unsigned_to_nat(0u);
v_body_820_ = l_Lean_Syntax_getArg(v_stx_782_, v___x_819_);
lean_dec(v_stx_782_);
v___x_825_ = 0;
v___x_826_ = l_Lean_Syntax_getTailPos_x3f(v_body_820_, v___x_825_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_stop_827_; 
v_stop_827_ = lean_ctor_get(v_range_781_, 1);
lean_inc(v_stop_827_);
lean_dec_ref(v_range_781_);
v___y_822_ = v_stop_827_;
goto v___jp_821_;
}
else
{
lean_object* v_val_828_; 
lean_dec_ref(v_range_781_);
v_val_828_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_val_828_);
lean_dec_ref_known(v___x_826_, 1);
v___y_822_ = v_val_828_;
goto v___jp_821_;
}
v___jp_821_:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_823_, 0, v_body_820_);
lean_ctor_set(v___x_823_, 1, v___y_822_);
v___x_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
return v___x_824_;
}
}
}
}
}
}
else
{
lean_object* v___x_829_; 
lean_dec_ref_known(v_pre_786_, 2);
lean_dec_ref_known(v_pre_785_, 2);
lean_dec_ref_known(v_pre_784_, 2);
lean_dec_ref_known(v___x_783_, 2);
lean_dec(v_stx_782_);
lean_dec_ref(v_range_781_);
v___x_829_ = lean_box(0);
return v___x_829_;
}
}
else
{
lean_object* v___x_830_; 
lean_dec(v_pre_786_);
lean_dec_ref_known(v_pre_785_, 2);
lean_dec_ref_known(v_pre_784_, 2);
lean_dec_ref_known(v___x_783_, 2);
lean_dec(v_stx_782_);
lean_dec_ref(v_range_781_);
v___x_830_ = lean_box(0);
return v___x_830_;
}
}
else
{
lean_object* v___x_831_; 
lean_dec(v_pre_785_);
lean_dec_ref_known(v_pre_784_, 2);
lean_dec_ref_known(v___x_783_, 2);
lean_dec(v_stx_782_);
lean_dec_ref(v_range_781_);
v___x_831_ = lean_box(0);
return v___x_831_;
}
}
else
{
lean_object* v___x_832_; 
lean_dec(v_pre_784_);
lean_dec_ref_known(v___x_783_, 2);
lean_dec(v_stx_782_);
lean_dec_ref(v_range_781_);
v___x_832_ = lean_box(0);
return v___x_832_;
}
}
else
{
lean_object* v___x_833_; 
lean_dec(v___x_783_);
lean_dec(v_stx_782_);
lean_dec_ref(v_range_781_);
v___x_833_ = lean_box(0);
return v___x_833_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(lean_object* v_range_837_, lean_object* v_stx_838_){
_start:
{
lean_object* v___x_839_; 
lean_inc(v_stx_838_);
lean_inc_ref(v_range_837_);
v___x_839_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f(v_range_837_, v_stx_838_);
if (lean_obj_tag(v___x_839_) == 1)
{
lean_dec(v_stx_838_);
lean_dec_ref(v_range_837_);
return v___x_839_;
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; size_t v_sz_843_; size_t v___x_844_; lean_object* v___x_845_; lean_object* v_fst_846_; 
lean_dec(v___x_839_);
v___x_840_ = l_Lean_Syntax_getArgs(v_stx_838_);
lean_dec(v_stx_838_);
v___x_841_ = lean_box(0);
v___x_842_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v_sz_843_ = lean_array_size(v___x_840_);
v___x_844_ = ((size_t)0ULL);
v___x_845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(v_range_837_, v___x_840_, v_sz_843_, v___x_844_, v___x_842_);
lean_dec_ref(v___x_840_);
v_fst_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_fst_846_);
lean_dec_ref(v___x_845_);
if (lean_obj_tag(v_fst_846_) == 0)
{
return v___x_841_;
}
else
{
lean_object* v_val_847_; 
v_val_847_ = lean_ctor_get(v_fst_846_, 0);
lean_inc(v_val_847_);
lean_dec_ref_known(v_fst_846_, 1);
return v_val_847_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(lean_object* v_range_848_, lean_object* v_as_849_, size_t v_sz_850_, size_t v_i_851_, lean_object* v_b_852_){
_start:
{
uint8_t v___x_853_; 
v___x_853_ = lean_usize_dec_lt(v_i_851_, v_sz_850_);
if (v___x_853_ == 0)
{
lean_dec_ref(v_range_848_);
lean_inc_ref(v_b_852_);
return v_b_852_;
}
else
{
lean_object* v___x_854_; lean_object* v_a_855_; lean_object* v___x_856_; 
v___x_854_ = lean_box(0);
v_a_855_ = lean_array_uget_borrowed(v_as_849_, v_i_851_);
lean_inc(v_a_855_);
lean_inc_ref(v_range_848_);
v___x_856_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(v_range_848_, v_a_855_);
if (lean_obj_tag(v___x_856_) == 1)
{
lean_object* v___x_857_; lean_object* v___x_858_; 
lean_dec_ref(v_range_848_);
v___x_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set(v___x_858_, 1, v___x_854_);
return v___x_858_;
}
else
{
lean_object* v___x_859_; size_t v___x_860_; size_t v___x_861_; 
lean_dec(v___x_856_);
v___x_859_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v___x_860_ = ((size_t)1ULL);
v___x_861_ = lean_usize_add(v_i_851_, v___x_860_);
v_i_851_ = v___x_861_;
v_b_852_ = v___x_859_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___boxed(lean_object* v_range_863_, lean_object* v_as_864_, lean_object* v_sz_865_, lean_object* v_i_866_, lean_object* v_b_867_){
_start:
{
size_t v_sz_boxed_868_; size_t v_i_boxed_869_; lean_object* v_res_870_; 
v_sz_boxed_868_ = lean_unbox_usize(v_sz_865_);
lean_dec(v_sz_865_);
v_i_boxed_869_ = lean_unbox_usize(v_i_866_);
lean_dec(v_i_866_);
v_res_870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(v_range_863_, v_as_864_, v_sz_boxed_868_, v_i_boxed_869_, v_b_867_);
lean_dec_ref(v_b_867_);
lean_dec_ref(v_as_864_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(lean_object* v_range_871_, lean_object* v_stx_872_){
_start:
{
uint8_t v___x_873_; lean_object* v___x_874_; 
v___x_873_ = 0;
v___x_874_ = l_Lean_Syntax_getRange_x3f(v_stx_872_, v___x_873_);
if (lean_obj_tag(v___x_874_) == 1)
{
lean_object* v_val_875_; uint8_t v___x_876_; 
v_val_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_val_875_);
lean_dec_ref_known(v___x_874_, 1);
v___x_876_ = l_Lean_Syntax_Range_includes(v_val_875_, v_range_871_, v___x_873_, v___x_873_);
lean_dec(v_val_875_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; 
lean_dec(v_stx_872_);
lean_dec_ref(v_range_871_);
v___x_877_ = lean_box(0);
return v___x_877_;
}
else
{
lean_object* v___x_878_; lean_object* v___x_879_; size_t v_sz_880_; size_t v___x_881_; lean_object* v___x_882_; lean_object* v_fst_883_; 
v___x_878_ = l_Lean_Syntax_getArgs(v_stx_872_);
v___x_879_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v_sz_880_ = lean_array_size(v___x_878_);
v___x_881_ = ((size_t)0ULL);
lean_inc_ref(v_range_871_);
v___x_882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(v_range_871_, v___x_878_, v_sz_880_, v___x_881_, v___x_879_);
lean_dec_ref(v___x_878_);
v_fst_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_fst_883_);
lean_dec_ref(v___x_882_);
if (lean_obj_tag(v_fst_883_) == 0)
{
lean_object* v___x_884_; 
v___x_884_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(v_range_871_, v_stx_872_);
return v___x_884_;
}
else
{
lean_object* v_val_885_; 
lean_dec(v_stx_872_);
lean_dec_ref(v_range_871_);
v_val_885_ = lean_ctor_get(v_fst_883_, 0);
lean_inc(v_val_885_);
lean_dec_ref_known(v_fst_883_, 1);
return v_val_885_;
}
}
}
else
{
lean_object* v___x_886_; 
lean_dec(v___x_874_);
lean_dec(v_stx_872_);
lean_dec_ref(v_range_871_);
v___x_886_ = lean_box(0);
return v___x_886_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(lean_object* v_range_887_, lean_object* v_as_888_, size_t v_sz_889_, size_t v_i_890_, lean_object* v_b_891_){
_start:
{
uint8_t v___x_892_; 
v___x_892_ = lean_usize_dec_lt(v_i_890_, v_sz_889_);
if (v___x_892_ == 0)
{
lean_dec_ref(v_range_887_);
lean_inc_ref(v_b_891_);
return v_b_891_;
}
else
{
lean_object* v___x_893_; lean_object* v_a_894_; lean_object* v___x_895_; 
v___x_893_ = lean_box(0);
v_a_894_ = lean_array_uget_borrowed(v_as_888_, v_i_890_);
lean_inc(v_a_894_);
lean_inc_ref(v_range_887_);
v___x_895_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v_range_887_, v_a_894_);
if (lean_obj_tag(v___x_895_) == 1)
{
lean_object* v___x_896_; lean_object* v___x_897_; 
lean_dec_ref(v_range_887_);
v___x_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
v___x_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
lean_ctor_set(v___x_897_, 1, v___x_893_);
return v___x_897_;
}
else
{
lean_object* v___x_898_; size_t v___x_899_; size_t v___x_900_; 
lean_dec(v___x_895_);
v___x_898_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v___x_899_ = ((size_t)1ULL);
v___x_900_ = lean_usize_add(v_i_890_, v___x_899_);
v_i_890_ = v___x_900_;
v_b_891_ = v___x_898_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0___boxed(lean_object* v_range_902_, lean_object* v_as_903_, lean_object* v_sz_904_, lean_object* v_i_905_, lean_object* v_b_906_){
_start:
{
size_t v_sz_boxed_907_; size_t v_i_boxed_908_; lean_object* v_res_909_; 
v_sz_boxed_907_ = lean_unbox_usize(v_sz_904_);
lean_dec(v_sz_904_);
v_i_boxed_908_ = lean_unbox_usize(v_i_905_);
lean_dec(v_i_905_);
v_res_909_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(v_range_902_, v_as_903_, v_sz_boxed_907_, v_i_boxed_908_, v_b_906_);
lean_dec_ref(v_b_906_);
lean_dec_ref(v_as_903_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody(lean_object* v_cmd_910_, lean_object* v_range_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v_range_911_, v_cmd_910_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0(lean_object* v_ctx_913_, lean_object* v_info_914_, lean_object* v_acc_915_){
_start:
{
if (lean_obj_tag(v_info_914_) == 0)
{
lean_object* v_i_916_; lean_object* v_toElabInfo_917_; lean_object* v_mctxBefore_918_; lean_object* v_goalsBefore_919_; lean_object* v_stx_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_938_; 
v_i_916_ = lean_ctor_get(v_info_914_, 0);
lean_inc_ref(v_i_916_);
lean_dec_ref_known(v_info_914_, 1);
v_toElabInfo_917_ = lean_ctor_get(v_i_916_, 0);
lean_inc_ref(v_toElabInfo_917_);
v_mctxBefore_918_ = lean_ctor_get(v_i_916_, 1);
lean_inc_ref(v_mctxBefore_918_);
v_goalsBefore_919_ = lean_ctor_get(v_i_916_, 2);
lean_inc(v_goalsBefore_919_);
lean_dec_ref(v_i_916_);
v_stx_920_ = lean_ctor_get(v_toElabInfo_917_, 1);
v_isSharedCheck_938_ = !lean_is_exclusive(v_toElabInfo_917_);
if (v_isSharedCheck_938_ == 0)
{
lean_object* v_unused_939_; 
v_unused_939_ = lean_ctor_get(v_toElabInfo_917_, 0);
lean_dec(v_unused_939_);
v___x_922_ = v_toElabInfo_917_;
v_isShared_923_ = v_isSharedCheck_938_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_stx_920_);
lean_dec(v_toElabInfo_917_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_938_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
uint8_t v___x_924_; 
lean_inc(v_stx_920_);
v___x_924_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(v_stx_920_);
if (v___x_924_ == 0)
{
lean_del_object(v___x_922_);
lean_dec(v_stx_920_);
lean_dec(v_goalsBefore_919_);
lean_dec_ref(v_mctxBefore_918_);
return v_acc_915_;
}
else
{
lean_object* v___x_925_; 
v___x_925_ = l_List_head_x3f___redArg(v_goalsBefore_919_);
lean_dec(v_goalsBefore_919_);
if (lean_obj_tag(v___x_925_) == 1)
{
lean_object* v_toCommandContextInfo_926_; lean_object* v_val_927_; lean_object* v_env_928_; lean_object* v_options_929_; lean_object* v_currNamespace_930_; lean_object* v_openDecls_931_; lean_object* v_namingCtx_933_; 
v_toCommandContextInfo_926_ = lean_ctor_get(v_ctx_913_, 0);
v_val_927_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_val_927_);
lean_dec_ref_known(v___x_925_, 1);
v_env_928_ = lean_ctor_get(v_toCommandContextInfo_926_, 0);
v_options_929_ = lean_ctor_get(v_toCommandContextInfo_926_, 4);
v_currNamespace_930_ = lean_ctor_get(v_toCommandContextInfo_926_, 5);
v_openDecls_931_ = lean_ctor_get(v_toCommandContextInfo_926_, 6);
lean_inc(v_openDecls_931_);
lean_inc(v_currNamespace_930_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 1, v_openDecls_931_);
lean_ctor_set(v___x_922_, 0, v_currNamespace_930_);
v_namingCtx_933_ = v___x_922_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_currNamespace_930_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v_openDecls_931_);
v_namingCtx_933_ = v_reuseFailAlloc_937_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_934_ = lean_box(1);
lean_inc_ref(v_options_929_);
lean_inc_ref(v_env_928_);
v___x_935_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set(v___x_935_, 1, v_stx_920_);
lean_ctor_set(v___x_935_, 2, v_env_928_);
lean_ctor_set(v___x_935_, 3, v_mctxBefore_918_);
lean_ctor_set(v___x_935_, 4, v_options_929_);
lean_ctor_set(v___x_935_, 5, v_namingCtx_933_);
lean_ctor_set(v___x_935_, 6, v_val_927_);
v___x_936_ = lean_array_push(v_acc_915_, v___x_935_);
return v___x_936_;
}
}
else
{
lean_dec(v___x_925_);
lean_del_object(v___x_922_);
lean_dec(v_stx_920_);
lean_dec_ref(v_mctxBefore_918_);
return v_acc_915_;
}
}
}
}
else
{
lean_dec_ref(v_info_914_);
return v_acc_915_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0___boxed(lean_object* v_ctx_940_, lean_object* v_info_941_, lean_object* v_acc_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0(v_ctx_940_, v_info_941_, v_acc_942_);
lean_dec_ref(v_ctx_940_);
return v_res_943_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4);
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
return v___x_945_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_946_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__0);
v___x_947_ = lean_unsigned_to_nat(0u);
v___x_948_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
lean_ctor_set(v___x_948_, 2, v___x_947_);
lean_ctor_set(v___x_948_, 3, v___x_947_);
lean_ctor_set(v___x_948_, 4, v___x_946_);
lean_ctor_set(v___x_948_, 5, v___x_946_);
lean_ctor_set(v___x_948_, 6, v___x_946_);
lean_ctor_set(v___x_948_, 7, v___x_946_);
lean_ctor_set(v___x_948_, 8, v___x_946_);
lean_ctor_set(v___x_948_, 9, v___x_946_);
lean_ctor_set(v___x_948_, 10, v___x_946_);
return v___x_948_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_949_ = lean_unsigned_to_nat(32u);
v___x_950_ = lean_mk_empty_array_with_capacity(v___x_949_);
v___x_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
return v___x_951_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__3(void){
_start:
{
size_t v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_952_ = ((size_t)5ULL);
v___x_953_ = lean_unsigned_to_nat(0u);
v___x_954_ = lean_unsigned_to_nat(32u);
v___x_955_ = lean_mk_empty_array_with_capacity(v___x_954_);
v___x_956_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__2);
v___x_957_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set(v___x_957_, 1, v___x_955_);
lean_ctor_set(v___x_957_, 2, v___x_953_);
lean_ctor_set(v___x_957_, 3, v___x_953_);
lean_ctor_set_usize(v___x_957_, 4, v___x_952_);
return v___x_957_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__4(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_958_ = lean_box(1);
v___x_959_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__3);
v___x_960_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__0);
v___x_961_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set(v___x_961_, 1, v___x_959_);
lean_ctor_set(v___x_961_, 2, v___x_958_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(lean_object* v_msgData_962_, lean_object* v___y_963_){
_start:
{
lean_object* v___x_965_; lean_object* v_env_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v_scopes_969_; lean_object* v___x_970_; lean_object* v_opts_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_965_ = lean_st_ref_get(v___y_963_);
v_env_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc_ref(v_env_966_);
lean_dec(v___x_965_);
v___x_967_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_968_ = lean_st_ref_get(v___y_963_);
v_scopes_969_ = lean_ctor_get(v___x_968_, 2);
lean_inc(v_scopes_969_);
lean_dec(v___x_968_);
v___x_970_ = l_List_head_x21___redArg(v___x_967_, v_scopes_969_);
lean_dec(v_scopes_969_);
v_opts_971_ = lean_ctor_get(v___x_970_, 1);
lean_inc_ref(v_opts_971_);
lean_dec(v___x_970_);
v___x_972_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1);
v___x_973_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__4);
v___x_974_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_974_, 0, v_env_966_);
lean_ctor_set(v___x_974_, 1, v___x_972_);
lean_ctor_set(v___x_974_, 2, v___x_973_);
lean_ctor_set(v___x_974_, 3, v_opts_971_);
v___x_975_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set(v___x_975_, 1, v_msgData_962_);
v___x_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___boxed(lean_object* v_msgData_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(v_msgData_977_, v___y_978_);
lean_dec(v___y_978_);
return v_res_980_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0(void){
_start:
{
lean_object* v___x_981_; double v___x_982_; 
v___x_981_ = lean_unsigned_to_nat(0u);
v___x_982_ = lean_float_of_nat(v___x_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(lean_object* v_cls_985_, lean_object* v_msg_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_Lean_Elab_Command_getRef___redArg(v___y_987_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v___x_992_; lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1041_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref_known(v___x_990_, 1);
v___x_992_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(v_msg_986_, v___y_988_);
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1041_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1041_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; lean_object* v_traceState_998_; lean_object* v_env_999_; lean_object* v_messages_1000_; lean_object* v_scopes_1001_; lean_object* v_usedQuotCtxts_1002_; lean_object* v_nextMacroScope_1003_; lean_object* v_maxRecDepth_1004_; lean_object* v_ngen_1005_; lean_object* v_auxDeclNGen_1006_; lean_object* v_infoState_1007_; lean_object* v_snapshotTasks_1008_; lean_object* v_prevLinterStates_1009_; lean_object* v_codeQualityEntryTasks_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1040_; 
v___x_997_ = lean_st_ref_take(v___y_988_);
v_traceState_998_ = lean_ctor_get(v___x_997_, 9);
v_env_999_ = lean_ctor_get(v___x_997_, 0);
v_messages_1000_ = lean_ctor_get(v___x_997_, 1);
v_scopes_1001_ = lean_ctor_get(v___x_997_, 2);
v_usedQuotCtxts_1002_ = lean_ctor_get(v___x_997_, 3);
v_nextMacroScope_1003_ = lean_ctor_get(v___x_997_, 4);
v_maxRecDepth_1004_ = lean_ctor_get(v___x_997_, 5);
v_ngen_1005_ = lean_ctor_get(v___x_997_, 6);
v_auxDeclNGen_1006_ = lean_ctor_get(v___x_997_, 7);
v_infoState_1007_ = lean_ctor_get(v___x_997_, 8);
v_snapshotTasks_1008_ = lean_ctor_get(v___x_997_, 10);
v_prevLinterStates_1009_ = lean_ctor_get(v___x_997_, 11);
v_codeQualityEntryTasks_1010_ = lean_ctor_get(v___x_997_, 12);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1012_ = v___x_997_;
v_isShared_1013_ = v_isSharedCheck_1040_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1010_);
lean_inc(v_prevLinterStates_1009_);
lean_inc(v_snapshotTasks_1008_);
lean_inc(v_traceState_998_);
lean_inc(v_infoState_1007_);
lean_inc(v_auxDeclNGen_1006_);
lean_inc(v_ngen_1005_);
lean_inc(v_maxRecDepth_1004_);
lean_inc(v_nextMacroScope_1003_);
lean_inc(v_usedQuotCtxts_1002_);
lean_inc(v_scopes_1001_);
lean_inc(v_messages_1000_);
lean_inc(v_env_999_);
lean_dec(v___x_997_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1040_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
uint64_t v_tid_1014_; lean_object* v_traces_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1039_; 
v_tid_1014_ = lean_ctor_get_uint64(v_traceState_998_, sizeof(void*)*1);
v_traces_1015_ = lean_ctor_get(v_traceState_998_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_traceState_998_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1017_ = v_traceState_998_;
v_isShared_1018_ = v_isSharedCheck_1039_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_traces_1015_);
lean_dec(v_traceState_998_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1039_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; double v___x_1021_; uint8_t v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1019_ = lean_box(0);
v___x_1020_ = lean_box(0);
v___x_1021_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0);
v___x_1022_ = 0;
v___x_1023_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_1024_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1024_, 0, v_cls_985_);
lean_ctor_set(v___x_1024_, 1, v___x_1020_);
lean_ctor_set(v___x_1024_, 2, v___x_1023_);
lean_ctor_set_float(v___x_1024_, sizeof(void*)*3, v___x_1021_);
lean_ctor_set_float(v___x_1024_, sizeof(void*)*3 + 8, v___x_1021_);
lean_ctor_set_uint8(v___x_1024_, sizeof(void*)*3 + 16, v___x_1022_);
v___x_1025_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__1));
v___x_1026_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set(v___x_1026_, 1, v_a_993_);
lean_ctor_set(v___x_1026_, 2, v___x_1025_);
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v_a_991_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = l_Lean_PersistentArray_push___redArg(v_traces_1015_, v___x_1027_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 0, v___x_1028_);
v___x_1030_ = v___x_1017_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1028_);
lean_ctor_set_uint64(v_reuseFailAlloc_1038_, sizeof(void*)*1, v_tid_1014_);
v___x_1030_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1032_; 
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 9, v___x_1030_);
v___x_1032_ = v___x_1012_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_env_999_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_messages_1000_);
lean_ctor_set(v_reuseFailAlloc_1037_, 2, v_scopes_1001_);
lean_ctor_set(v_reuseFailAlloc_1037_, 3, v_usedQuotCtxts_1002_);
lean_ctor_set(v_reuseFailAlloc_1037_, 4, v_nextMacroScope_1003_);
lean_ctor_set(v_reuseFailAlloc_1037_, 5, v_maxRecDepth_1004_);
lean_ctor_set(v_reuseFailAlloc_1037_, 6, v_ngen_1005_);
lean_ctor_set(v_reuseFailAlloc_1037_, 7, v_auxDeclNGen_1006_);
lean_ctor_set(v_reuseFailAlloc_1037_, 8, v_infoState_1007_);
lean_ctor_set(v_reuseFailAlloc_1037_, 9, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1037_, 10, v_snapshotTasks_1008_);
lean_ctor_set(v_reuseFailAlloc_1037_, 11, v_prevLinterStates_1009_);
lean_ctor_set(v_reuseFailAlloc_1037_, 12, v_codeQualityEntryTasks_1010_);
v___x_1032_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
lean_object* v___x_1033_; lean_object* v___x_1035_; 
v___x_1033_ = lean_st_ref_put(v___y_988_, v___x_1032_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_1019_);
v___x_1035_ = v___x_995_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1019_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec_ref(v_msg_986_);
lean_dec(v_cls_985_);
v_a_1042_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_990_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_990_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___boxed(lean_object* v_cls_1050_, lean_object* v_msg_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v_cls_1050_, v_msg_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
return v_res_1055_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0(lean_object* v_x_1060_){
_start:
{
lean_object* v___x_1061_; uint8_t v___x_1062_; 
v___x_1061_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0___closed__1));
v___x_1062_ = lean_name_eq(v_x_1060_, v___x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0___boxed(lean_object* v_x_1063_){
_start:
{
uint8_t v_res_1064_; lean_object* v_r_1065_; 
v_res_1064_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0(v_x_1063_);
lean_dec(v_x_1063_);
v_r_1065_ = lean_box(v_res_1064_);
return v_r_1065_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(lean_object* v_a_1066_, lean_object* v_x_1067_){
_start:
{
if (lean_obj_tag(v_x_1067_) == 0)
{
uint8_t v___x_1068_; 
v___x_1068_ = 0;
return v___x_1068_;
}
else
{
lean_object* v_key_1069_; lean_object* v_tail_1070_; uint8_t v___y_1072_; lean_object* v_fst_1074_; lean_object* v_snd_1075_; lean_object* v_fst_1076_; lean_object* v_snd_1077_; uint8_t v___x_1078_; 
v_key_1069_ = lean_ctor_get(v_x_1067_, 0);
v_tail_1070_ = lean_ctor_get(v_x_1067_, 2);
v_fst_1074_ = lean_ctor_get(v_key_1069_, 0);
v_snd_1075_ = lean_ctor_get(v_key_1069_, 1);
v_fst_1076_ = lean_ctor_get(v_a_1066_, 0);
v_snd_1077_ = lean_ctor_get(v_a_1066_, 1);
v___x_1078_ = l_Lean_Syntax_instBEqRange_beq(v_fst_1074_, v_fst_1076_);
if (v___x_1078_ == 0)
{
v___y_1072_ = v___x_1078_;
goto v___jp_1071_;
}
else
{
uint8_t v___x_1079_; 
v___x_1079_ = l_Lean_instBEqMVarId_beq(v_snd_1075_, v_snd_1077_);
v___y_1072_ = v___x_1079_;
goto v___jp_1071_;
}
v___jp_1071_:
{
if (v___y_1072_ == 0)
{
v_x_1067_ = v_tail_1070_;
goto _start;
}
else
{
return v___y_1072_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg___boxed(lean_object* v_a_1080_, lean_object* v_x_1081_){
_start:
{
uint8_t v_res_1082_; lean_object* v_r_1083_; 
v_res_1082_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(v_a_1080_, v_x_1081_);
lean_dec(v_x_1081_);
lean_dec_ref(v_a_1080_);
v_r_1083_ = lean_box(v_res_1082_);
return v_r_1083_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(lean_object* v_m_1084_, lean_object* v_a_1085_){
_start:
{
lean_object* v_buckets_1086_; lean_object* v_fst_1087_; lean_object* v_snd_1088_; lean_object* v___x_1089_; uint64_t v___x_1090_; uint64_t v___x_1091_; uint64_t v___x_1092_; uint64_t v___x_1093_; uint64_t v___x_1094_; uint64_t v_fold_1095_; uint64_t v___x_1096_; uint64_t v___x_1097_; uint64_t v___x_1098_; size_t v___x_1099_; size_t v___x_1100_; size_t v___x_1101_; size_t v___x_1102_; size_t v___x_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v_buckets_1086_ = lean_ctor_get(v_m_1084_, 1);
v_fst_1087_ = lean_ctor_get(v_a_1085_, 0);
v_snd_1088_ = lean_ctor_get(v_a_1085_, 1);
v___x_1089_ = lean_array_get_size(v_buckets_1086_);
v___x_1090_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1087_);
v___x_1091_ = l_Lean_instHashableMVarId_hash(v_snd_1088_);
v___x_1092_ = lean_uint64_mix_hash(v___x_1090_, v___x_1091_);
v___x_1093_ = 32ULL;
v___x_1094_ = lean_uint64_shift_right(v___x_1092_, v___x_1093_);
v_fold_1095_ = lean_uint64_xor(v___x_1092_, v___x_1094_);
v___x_1096_ = 16ULL;
v___x_1097_ = lean_uint64_shift_right(v_fold_1095_, v___x_1096_);
v___x_1098_ = lean_uint64_xor(v_fold_1095_, v___x_1097_);
v___x_1099_ = lean_uint64_to_usize(v___x_1098_);
v___x_1100_ = lean_usize_of_nat(v___x_1089_);
v___x_1101_ = ((size_t)1ULL);
v___x_1102_ = lean_usize_sub(v___x_1100_, v___x_1101_);
v___x_1103_ = lean_usize_land(v___x_1099_, v___x_1102_);
v___x_1104_ = lean_array_uget_borrowed(v_buckets_1086_, v___x_1103_);
v___x_1105_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(v_a_1085_, v___x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg___boxed(lean_object* v_m_1106_, lean_object* v_a_1107_){
_start:
{
uint8_t v_res_1108_; lean_object* v_r_1109_; 
v_res_1108_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(v_m_1106_, v_a_1107_);
lean_dec_ref(v_a_1107_);
lean_dec_ref(v_m_1106_);
v_r_1109_ = lean_box(v_res_1108_);
return v_r_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3_spec__8___redArg(lean_object* v_x_1110_, lean_object* v_x_1111_){
_start:
{
if (lean_obj_tag(v_x_1111_) == 0)
{
return v_x_1110_;
}
else
{
lean_object* v_key_1112_; lean_object* v_value_1113_; lean_object* v_tail_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1141_; 
v_key_1112_ = lean_ctor_get(v_x_1111_, 0);
v_value_1113_ = lean_ctor_get(v_x_1111_, 1);
v_tail_1114_ = lean_ctor_get(v_x_1111_, 2);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_x_1111_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1116_ = v_x_1111_;
v_isShared_1117_ = v_isSharedCheck_1141_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_tail_1114_);
lean_inc(v_value_1113_);
lean_inc(v_key_1112_);
lean_dec(v_x_1111_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1141_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v_fst_1118_; lean_object* v_snd_1119_; lean_object* v___x_1120_; uint64_t v___x_1121_; uint64_t v___x_1122_; uint64_t v___x_1123_; uint64_t v___x_1124_; uint64_t v___x_1125_; uint64_t v_fold_1126_; uint64_t v___x_1127_; uint64_t v___x_1128_; uint64_t v___x_1129_; size_t v___x_1130_; size_t v___x_1131_; size_t v___x_1132_; size_t v___x_1133_; size_t v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1137_; 
v_fst_1118_ = lean_ctor_get(v_key_1112_, 0);
v_snd_1119_ = lean_ctor_get(v_key_1112_, 1);
v___x_1120_ = lean_array_get_size(v_x_1110_);
v___x_1121_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1118_);
v___x_1122_ = l_Lean_instHashableMVarId_hash(v_snd_1119_);
v___x_1123_ = lean_uint64_mix_hash(v___x_1121_, v___x_1122_);
v___x_1124_ = 32ULL;
v___x_1125_ = lean_uint64_shift_right(v___x_1123_, v___x_1124_);
v_fold_1126_ = lean_uint64_xor(v___x_1123_, v___x_1125_);
v___x_1127_ = 16ULL;
v___x_1128_ = lean_uint64_shift_right(v_fold_1126_, v___x_1127_);
v___x_1129_ = lean_uint64_xor(v_fold_1126_, v___x_1128_);
v___x_1130_ = lean_uint64_to_usize(v___x_1129_);
v___x_1131_ = lean_usize_of_nat(v___x_1120_);
v___x_1132_ = ((size_t)1ULL);
v___x_1133_ = lean_usize_sub(v___x_1131_, v___x_1132_);
v___x_1134_ = lean_usize_land(v___x_1130_, v___x_1133_);
v___x_1135_ = lean_array_uget_borrowed(v_x_1110_, v___x_1134_);
lean_inc(v___x_1135_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 2, v___x_1135_);
v___x_1137_ = v___x_1116_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_key_1112_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_value_1113_);
lean_ctor_set(v_reuseFailAlloc_1140_, 2, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_array_uset(v_x_1110_, v___x_1134_, v___x_1137_);
v_x_1110_ = v___x_1138_;
v_x_1111_ = v_tail_1114_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3___redArg(lean_object* v_i_1142_, lean_object* v_source_1143_, lean_object* v_target_1144_){
_start:
{
lean_object* v___x_1145_; uint8_t v___x_1146_; 
v___x_1145_ = lean_array_get_size(v_source_1143_);
v___x_1146_ = lean_nat_dec_lt(v_i_1142_, v___x_1145_);
if (v___x_1146_ == 0)
{
lean_dec_ref(v_source_1143_);
lean_dec(v_i_1142_);
return v_target_1144_;
}
else
{
lean_object* v_es_1147_; lean_object* v___x_1148_; lean_object* v_source_1149_; lean_object* v_target_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v_es_1147_ = lean_array_fget(v_source_1143_, v_i_1142_);
v___x_1148_ = lean_box(0);
v_source_1149_ = lean_array_fset(v_source_1143_, v_i_1142_, v___x_1148_);
v_target_1150_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3_spec__8___redArg(v_target_1144_, v_es_1147_);
v___x_1151_ = lean_unsigned_to_nat(1u);
v___x_1152_ = lean_nat_add(v_i_1142_, v___x_1151_);
lean_dec(v_i_1142_);
v_i_1142_ = v___x_1152_;
v_source_1143_ = v_source_1149_;
v_target_1144_ = v_target_1150_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2___redArg(lean_object* v_data_1154_){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v_nbuckets_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1155_ = lean_array_get_size(v_data_1154_);
v___x_1156_ = lean_unsigned_to_nat(2u);
v_nbuckets_1157_ = lean_nat_mul(v___x_1155_, v___x_1156_);
v___x_1158_ = lean_unsigned_to_nat(0u);
v___x_1159_ = lean_box(0);
v___x_1160_ = lean_mk_array(v_nbuckets_1157_, v___x_1159_);
v___x_1161_ = lean_array_propagate_mark(v_data_1154_, v___x_1160_);
v___x_1162_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3___redArg(v___x_1158_, v_data_1154_, v___x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(lean_object* v_m_1163_, lean_object* v_a_1164_, lean_object* v_b_1165_){
_start:
{
lean_object* v_size_1166_; lean_object* v_buckets_1167_; lean_object* v_fst_1168_; lean_object* v_snd_1169_; lean_object* v___x_1170_; uint64_t v___x_1171_; uint64_t v___x_1172_; uint64_t v___x_1173_; uint64_t v___x_1174_; uint64_t v___x_1175_; uint64_t v_fold_1176_; uint64_t v___x_1177_; uint64_t v___x_1178_; uint64_t v___x_1179_; size_t v___x_1180_; size_t v___x_1181_; size_t v___x_1182_; size_t v___x_1183_; size_t v___x_1184_; lean_object* v_bkt_1185_; uint8_t v___x_1186_; 
v_size_1166_ = lean_ctor_get(v_m_1163_, 0);
v_buckets_1167_ = lean_ctor_get(v_m_1163_, 1);
v_fst_1168_ = lean_ctor_get(v_a_1164_, 0);
v_snd_1169_ = lean_ctor_get(v_a_1164_, 1);
v___x_1170_ = lean_array_get_size(v_buckets_1167_);
v___x_1171_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1168_);
v___x_1172_ = l_Lean_instHashableMVarId_hash(v_snd_1169_);
v___x_1173_ = lean_uint64_mix_hash(v___x_1171_, v___x_1172_);
v___x_1174_ = 32ULL;
v___x_1175_ = lean_uint64_shift_right(v___x_1173_, v___x_1174_);
v_fold_1176_ = lean_uint64_xor(v___x_1173_, v___x_1175_);
v___x_1177_ = 16ULL;
v___x_1178_ = lean_uint64_shift_right(v_fold_1176_, v___x_1177_);
v___x_1179_ = lean_uint64_xor(v_fold_1176_, v___x_1178_);
v___x_1180_ = lean_uint64_to_usize(v___x_1179_);
v___x_1181_ = lean_usize_of_nat(v___x_1170_);
v___x_1182_ = ((size_t)1ULL);
v___x_1183_ = lean_usize_sub(v___x_1181_, v___x_1182_);
v___x_1184_ = lean_usize_land(v___x_1180_, v___x_1183_);
v_bkt_1185_ = lean_array_uget_borrowed(v_buckets_1167_, v___x_1184_);
v___x_1186_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(v_a_1164_, v_bkt_1185_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1207_; 
lean_inc_ref(v_buckets_1167_);
lean_inc(v_size_1166_);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_m_1163_);
if (v_isSharedCheck_1207_ == 0)
{
lean_object* v_unused_1208_; lean_object* v_unused_1209_; 
v_unused_1208_ = lean_ctor_get(v_m_1163_, 1);
lean_dec(v_unused_1208_);
v_unused_1209_ = lean_ctor_get(v_m_1163_, 0);
lean_dec(v_unused_1209_);
v___x_1188_ = v_m_1163_;
v_isShared_1189_ = v_isSharedCheck_1207_;
goto v_resetjp_1187_;
}
else
{
lean_dec(v_m_1163_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1207_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v_size_x27_1191_; lean_object* v___x_1192_; lean_object* v_buckets_x27_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; 
v___x_1190_ = lean_unsigned_to_nat(1u);
v_size_x27_1191_ = lean_nat_add(v_size_1166_, v___x_1190_);
lean_dec(v_size_1166_);
lean_inc(v_bkt_1185_);
v___x_1192_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1192_, 0, v_a_1164_);
lean_ctor_set(v___x_1192_, 1, v_b_1165_);
lean_ctor_set(v___x_1192_, 2, v_bkt_1185_);
v_buckets_x27_1193_ = lean_array_uset(v_buckets_1167_, v___x_1184_, v___x_1192_);
v___x_1194_ = lean_unsigned_to_nat(4u);
v___x_1195_ = lean_nat_mul(v_size_x27_1191_, v___x_1194_);
v___x_1196_ = lean_unsigned_to_nat(3u);
v___x_1197_ = lean_nat_div(v___x_1195_, v___x_1196_);
lean_dec(v___x_1195_);
v___x_1198_ = lean_array_get_size(v_buckets_x27_1193_);
v___x_1199_ = lean_nat_dec_le(v___x_1197_, v___x_1198_);
lean_dec(v___x_1197_);
if (v___x_1199_ == 0)
{
lean_object* v_val_1200_; lean_object* v___x_1202_; 
v_val_1200_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2___redArg(v_buckets_x27_1193_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 1, v_val_1200_);
lean_ctor_set(v___x_1188_, 0, v_size_x27_1191_);
v___x_1202_ = v___x_1188_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_size_x27_1191_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_val_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
else
{
lean_object* v___x_1205_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 1, v_buckets_x27_1193_);
lean_ctor_set(v___x_1188_, 0, v_size_x27_1191_);
v___x_1205_ = v___x_1188_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_size_x27_1191_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_buckets_x27_1193_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
else
{
lean_dec(v_b_1165_);
lean_dec_ref(v_a_1164_);
return v_m_1163_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(lean_object* v___x_1210_, lean_object* v_fst_1211_, lean_object* v_snd_1212_, lean_object* v___x_1213_, lean_object* v_as_1214_, size_t v_sz_1215_, size_t v_i_1216_, lean_object* v_b_1217_){
_start:
{
lean_object* v_a_1220_; uint8_t v___x_1224_; 
v___x_1224_ = lean_usize_dec_lt(v_i_1216_, v_sz_1215_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; 
lean_dec(v___x_1213_);
lean_dec(v_snd_1212_);
lean_dec(v_fst_1211_);
lean_dec_ref(v___x_1210_);
v___x_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1225_, 0, v_b_1217_);
return v___x_1225_;
}
else
{
lean_object* v_a_1226_; lean_object* v_snd_1227_; lean_object* v_fst_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1264_; 
v_a_1226_ = lean_array_uget(v_as_1214_, v_i_1216_);
v_snd_1227_ = lean_ctor_get(v_a_1226_, 1);
v_fst_1228_ = lean_ctor_get(v_a_1226_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_a_1226_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1230_ = v_a_1226_;
v_isShared_1231_ = v_isSharedCheck_1264_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_snd_1227_);
lean_inc(v_fst_1228_);
lean_dec(v_a_1226_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1264_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v_fst_1232_; lean_object* v_snd_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1263_; 
v_fst_1232_ = lean_ctor_get(v_snd_1227_, 0);
v_snd_1233_ = lean_ctor_get(v_snd_1227_, 1);
v_isSharedCheck_1263_ = !lean_is_exclusive(v_snd_1227_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1235_ = v_snd_1227_;
v_isShared_1236_ = v_isSharedCheck_1263_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_snd_1233_);
lean_inc(v_fst_1232_);
lean_dec(v_snd_1227_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1263_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v_fst_1237_; lean_object* v_snd_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1262_; 
v_fst_1237_ = lean_ctor_get(v_b_1217_, 0);
v_snd_1238_ = lean_ctor_get(v_b_1217_, 1);
v_isSharedCheck_1262_ = !lean_is_exclusive(v_b_1217_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1240_ = v_b_1217_;
v_isShared_1241_ = v_isSharedCheck_1262_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_snd_1238_);
lean_inc(v_fst_1237_);
lean_dec(v_b_1217_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1262_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
lean_inc(v_snd_1233_);
lean_inc_ref(v___x_1210_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 1, v_snd_1233_);
lean_ctor_set(v___x_1240_, 0, v___x_1210_);
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_snd_1233_);
v___x_1243_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
uint8_t v___x_1244_; 
v___x_1244_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(v_snd_1238_, v___x_1243_);
if (v___x_1244_ == 0)
{
lean_object* v_env_1245_; lean_object* v_mctx_1246_; lean_object* v_opts_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1251_; 
v_env_1245_ = lean_ctor_get(v_fst_1228_, 0);
lean_inc_ref(v_env_1245_);
v_mctx_1246_ = lean_ctor_get(v_fst_1228_, 1);
lean_inc_ref(v_mctx_1246_);
v_opts_1247_ = lean_ctor_get(v_fst_1228_, 3);
lean_inc_ref(v_opts_1247_);
lean_dec(v_fst_1228_);
v___x_1248_ = lean_box(0);
v___x_1249_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_snd_1238_, v___x_1243_, v___x_1248_);
lean_inc(v_snd_1212_);
lean_inc(v_fst_1211_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 1, v_snd_1212_);
lean_ctor_set(v___x_1230_, 0, v_fst_1211_);
v___x_1251_ = v___x_1230_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_fst_1211_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_snd_1212_);
v___x_1251_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1255_; 
lean_inc(v___x_1213_);
v___x_1252_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
lean_ctor_set(v___x_1252_, 1, v___x_1213_);
lean_ctor_set(v___x_1252_, 2, v_env_1245_);
lean_ctor_set(v___x_1252_, 3, v_mctx_1246_);
lean_ctor_set(v___x_1252_, 4, v_opts_1247_);
lean_ctor_set(v___x_1252_, 5, v_fst_1232_);
lean_ctor_set(v___x_1252_, 6, v_snd_1233_);
v___x_1253_ = lean_array_push(v_fst_1237_, v___x_1252_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 1, v___x_1249_);
lean_ctor_set(v___x_1235_, 0, v___x_1253_);
v___x_1255_ = v___x_1235_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1253_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v___x_1249_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
v_a_1220_ = v___x_1255_;
goto v___jp_1219_;
}
}
}
else
{
lean_object* v___x_1259_; 
lean_dec_ref(v___x_1243_);
lean_dec(v_snd_1233_);
lean_dec(v_fst_1232_);
lean_del_object(v___x_1230_);
lean_dec(v_fst_1228_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 1, v_snd_1238_);
lean_ctor_set(v___x_1235_, 0, v_fst_1237_);
v___x_1259_ = v___x_1235_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_fst_1237_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_snd_1238_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
v_a_1220_ = v___x_1259_;
goto v___jp_1219_;
}
}
}
}
}
}
}
v___jp_1219_:
{
size_t v___x_1221_; size_t v___x_1222_; 
v___x_1221_ = ((size_t)1ULL);
v___x_1222_ = lean_usize_add(v_i_1216_, v___x_1221_);
v_i_1216_ = v___x_1222_;
v_b_1217_ = v_a_1220_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg___boxed(lean_object* v___x_1265_, lean_object* v_fst_1266_, lean_object* v_snd_1267_, lean_object* v___x_1268_, lean_object* v_as_1269_, lean_object* v_sz_1270_, lean_object* v_i_1271_, lean_object* v_b_1272_, lean_object* v___y_1273_){
_start:
{
size_t v_sz_boxed_1274_; size_t v_i_boxed_1275_; lean_object* v_res_1276_; 
v_sz_boxed_1274_ = lean_unbox_usize(v_sz_1270_);
lean_dec(v_sz_1270_);
v_i_boxed_1275_ = lean_unbox_usize(v_i_1271_);
lean_dec(v_i_1271_);
v_res_1276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1265_, v_fst_1266_, v_snd_1267_, v___x_1268_, v_as_1269_, v_sz_boxed_1274_, v_i_boxed_1275_, v_b_1272_);
lean_dec_ref(v_as_1269_);
return v_res_1276_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3(void){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1281_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1282_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__2));
v___x_1283_ = l_Lean_Name_append(v___x_1282_, v___x_1281_);
return v___x_1283_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__4));
v___x_1286_ = l_Lean_stringToMessageData(v___x_1285_);
return v___x_1286_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__6));
v___x_1289_ = l_Lean_stringToMessageData(v___x_1288_);
return v___x_1289_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__8));
v___x_1292_ = l_Lean_stringToMessageData(v___x_1291_);
return v___x_1292_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__10));
v___x_1295_ = l_Lean_stringToMessageData(v___x_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12(lean_object* v___x_1296_, lean_object* v_val_1297_, lean_object* v_cmd_1298_, uint8_t v_onUnsolved_1299_, uint8_t v___y_1300_, lean_object* v_as_1301_, size_t v_sz_1302_, size_t v_i_1303_, lean_object* v_b_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
uint8_t v___x_1308_; 
v___x_1308_ = lean_usize_dec_lt(v_i_1303_, v_sz_1302_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; 
lean_dec(v_cmd_1298_);
v___x_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1309_, 0, v_b_1304_);
return v___x_1309_;
}
else
{
lean_object* v_snd_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1458_; 
v_snd_1310_ = lean_ctor_get(v_b_1304_, 1);
v_isSharedCheck_1458_ = !lean_is_exclusive(v_b_1304_);
if (v_isSharedCheck_1458_ == 0)
{
lean_object* v_unused_1459_; 
v_unused_1459_ = lean_ctor_get(v_b_1304_, 0);
lean_dec(v_unused_1459_);
v___x_1312_ = v_b_1304_;
v_isShared_1313_ = v_isSharedCheck_1458_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_snd_1310_);
lean_dec(v_b_1304_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1458_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v_fst_1314_; lean_object* v_snd_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1457_; 
v_fst_1314_ = lean_ctor_get(v_snd_1310_, 0);
v_snd_1315_ = lean_ctor_get(v_snd_1310_, 1);
v_isSharedCheck_1457_ = !lean_is_exclusive(v_snd_1310_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1317_ = v_snd_1310_;
v_isShared_1318_ = v_isSharedCheck_1457_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_snd_1315_);
lean_inc(v_fst_1314_);
lean_dec(v_snd_1310_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1457_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v_a_1319_; lean_object* v_pos_1320_; lean_object* v_endPos_1321_; uint8_t v_severity_1322_; lean_object* v_data_1323_; lean_object* v___x_1324_; lean_object* v_a_1326_; 
v_a_1319_ = lean_array_uget_borrowed(v_as_1301_, v_i_1303_);
v_pos_1320_ = lean_ctor_get(v_a_1319_, 1);
v_endPos_1321_ = lean_ctor_get(v_a_1319_, 2);
lean_inc(v_endPos_1321_);
v_severity_1322_ = lean_ctor_get_uint8(v_a_1319_, sizeof(void*)*5 + 1);
v_data_1323_ = lean_ctor_get(v_a_1319_, 4);
v___x_1324_ = lean_box(0);
if (v_severity_1322_ == 2)
{
lean_object* v___f_1339_; uint8_t v___x_1340_; 
v___f_1339_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
lean_inc(v_data_1323_);
v___x_1340_ = l_Lean_MessageData_hasTag(v___f_1339_, v_data_1323_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; 
lean_dec(v_endPos_1321_);
lean_del_object(v___x_1312_);
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v_fst_1314_);
lean_ctor_set(v___x_1341_, 1, v_snd_1315_);
v_a_1326_ = v___x_1341_;
goto v___jp_1325_;
}
else
{
if (lean_obj_tag(v_endPos_1321_) == 1)
{
lean_object* v_val_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1454_; 
v_val_1342_ = lean_ctor_get(v_endPos_1321_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_endPos_1321_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1344_ = v_endPos_1321_;
v_isShared_1345_ = v_isSharedCheck_1454_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_val_1342_);
lean_dec(v_endPos_1321_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1454_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; uint8_t v___x_1350_; 
lean_inc_ref(v_pos_1320_);
v___x_1346_ = l_Lean_FileMap_ofPosition(v___x_1296_, v_pos_1320_);
v___x_1347_ = l_Lean_FileMap_ofPosition(v___x_1296_, v_val_1342_);
lean_inc(v___x_1347_);
lean_inc(v___x_1346_);
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1346_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
v___x_1349_ = 0;
v___x_1350_ = l_Lean_Syntax_Range_includes(v_val_1297_, v___x_1348_, v___x_1349_, v___x_1349_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; 
lean_dec_ref_known(v___x_1348_, 2);
lean_dec(v___x_1347_);
lean_dec(v___x_1346_);
lean_del_object(v___x_1344_);
lean_del_object(v___x_1312_);
v___x_1351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1351_, 0, v_fst_1314_);
lean_ctor_set(v___x_1351_, 1, v_snd_1315_);
v_a_1326_ = v___x_1351_;
goto v___jp_1325_;
}
else
{
lean_object* v___x_1352_; 
lean_inc(v_cmd_1298_);
lean_inc_ref(v___x_1348_);
v___x_1352_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1348_, v_cmd_1298_);
if (lean_obj_tag(v___x_1352_) == 1)
{
lean_object* v_val_1353_; lean_object* v_fst_1354_; lean_object* v_snd_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1418_; 
lean_dec(v___x_1347_);
lean_dec(v___x_1346_);
lean_del_object(v___x_1344_);
v_val_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_val_1353_);
lean_dec_ref_known(v___x_1352_, 1);
v_fst_1354_ = lean_ctor_get(v_val_1353_, 0);
v_snd_1355_ = lean_ctor_get(v_val_1353_, 1);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_val_1353_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1357_ = v_val_1353_;
v_isShared_1358_ = v_isSharedCheck_1418_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_snd_1355_);
lean_inc(v_fst_1354_);
lean_dec(v_val_1353_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1418_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; uint8_t v___y_1416_; lean_object* v___x_1417_; 
v___x_1417_ = l_Lean_Syntax_getPos_x3f(v_fst_1354_, v___x_1349_);
if (lean_obj_tag(v___x_1417_) == 0)
{
v___y_1416_ = v___x_1350_;
goto v___jp_1415_;
}
else
{
lean_dec_ref_known(v___x_1417_, 1);
v___y_1416_ = v___x_1349_;
goto v___jp_1415_;
}
v___jp_1359_:
{
lean_object* v___x_1365_; 
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 1, v_snd_1315_);
lean_ctor_set(v___x_1357_, 0, v_fst_1314_);
v___x_1365_ = v___x_1357_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_fst_1314_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v_snd_1315_);
v___x_1365_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
size_t v_sz_1366_; size_t v___x_1367_; lean_object* v___x_1368_; 
v_sz_1366_ = lean_array_size(v___y_1361_);
v___x_1367_ = ((size_t)0ULL);
v___x_1368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1348_, v_fst_1354_, v_snd_1355_, v___y_1360_, v___y_1361_, v_sz_1366_, v___x_1367_, v___x_1365_);
lean_dec_ref(v___y_1361_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v_fst_1370_; lean_object* v_snd_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1369_);
lean_dec_ref_known(v___x_1368_, 1);
v_fst_1370_ = lean_ctor_get(v_a_1369_, 0);
v_snd_1371_ = lean_ctor_get(v_a_1369_, 1);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_a_1369_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v_a_1369_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_snd_1371_);
lean_inc(v_fst_1370_);
lean_dec(v_a_1369_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_fst_1370_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_snd_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
v_a_1326_ = v___x_1376_;
goto v___jp_1325_;
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_del_object(v___x_1317_);
lean_dec(v_cmd_1298_);
v_a_1379_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1368_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1368_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
}
v___jp_1388_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; uint8_t v___x_1393_; 
lean_inc_ref(v___x_1348_);
v___x_1389_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1348_);
v___x_1390_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1323_);
v___x_1391_ = lean_array_get_size(v___x_1390_);
v___x_1392_ = lean_unsigned_to_nat(0u);
v___x_1393_ = lean_nat_dec_eq(v___x_1391_, v___x_1392_);
if (v___x_1393_ == 0)
{
v___y_1360_ = v___x_1389_;
v___y_1361_ = v___x_1390_;
v___y_1362_ = v___y_1305_;
v___y_1363_ = v___y_1306_;
goto v___jp_1359_;
}
else
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v_scopes_1399_; lean_object* v___x_1400_; lean_object* v_opts_1401_; uint8_t v_hasTrace_1402_; 
v___x_1394_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1395_ = l_Lean_inheritedTraceOptions;
v___x_1396_ = lean_st_ref_get(v___x_1395_);
v___x_1397_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1398_ = lean_st_ref_get(v___y_1306_);
v_scopes_1399_ = lean_ctor_get(v___x_1398_, 2);
lean_inc(v_scopes_1399_);
lean_dec(v___x_1398_);
v___x_1400_ = l_List_head_x21___redArg(v___x_1397_, v_scopes_1399_);
lean_dec(v_scopes_1399_);
v_opts_1401_ = lean_ctor_get(v___x_1400_, 1);
lean_inc_ref(v_opts_1401_);
lean_dec(v___x_1400_);
v_hasTrace_1402_ = lean_ctor_get_uint8(v_opts_1401_, sizeof(void*)*1);
if (v_hasTrace_1402_ == 0)
{
lean_dec_ref(v_opts_1401_);
lean_dec(v___x_1396_);
v___y_1360_ = v___x_1389_;
v___y_1361_ = v___x_1390_;
v___y_1362_ = v___y_1305_;
v___y_1363_ = v___y_1306_;
goto v___jp_1359_;
}
else
{
lean_object* v___x_1403_; uint8_t v___x_1404_; 
v___x_1403_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1404_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1396_, v_opts_1401_, v___x_1403_);
lean_dec_ref(v_opts_1401_);
lean_dec(v___x_1396_);
if (v___x_1404_ == 0)
{
v___y_1360_ = v___x_1389_;
v___y_1361_ = v___x_1390_;
v___y_1362_ = v___y_1305_;
v___y_1363_ = v___y_1306_;
goto v___jp_1359_;
}
else
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1405_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5);
v___x_1406_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1394_, v___x_1405_, v___y_1305_, v___y_1306_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_dec_ref_known(v___x_1406_, 1);
v___y_1360_ = v___x_1389_;
v___y_1361_ = v___x_1390_;
v___y_1362_ = v___y_1305_;
v___y_1363_ = v___y_1306_;
goto v___jp_1359_;
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_dec_ref(v___x_1390_);
lean_dec(v___x_1389_);
lean_del_object(v___x_1357_);
lean_dec(v_snd_1355_);
lean_dec(v_fst_1354_);
lean_dec_ref_known(v___x_1348_, 2);
lean_del_object(v___x_1317_);
lean_dec(v_snd_1315_);
lean_dec(v_fst_1314_);
lean_dec(v_cmd_1298_);
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
}
}
v___jp_1415_:
{
if (v_onUnsolved_1299_ == 0)
{
if (v___y_1300_ == 0)
{
lean_del_object(v___x_1357_);
lean_dec(v_snd_1355_);
lean_dec(v_fst_1354_);
lean_dec_ref_known(v___x_1348_, 2);
goto v___jp_1333_;
}
else
{
if (v___y_1416_ == 0)
{
lean_del_object(v___x_1357_);
lean_dec(v_snd_1355_);
lean_dec(v_fst_1354_);
lean_dec_ref_known(v___x_1348_, 2);
goto v___jp_1333_;
}
else
{
lean_del_object(v___x_1312_);
goto v___jp_1388_;
}
}
}
else
{
lean_del_object(v___x_1312_);
goto v___jp_1388_;
}
}
}
}
else
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v_scopes_1424_; lean_object* v___x_1425_; lean_object* v_opts_1426_; uint8_t v_hasTrace_1427_; 
lean_dec(v___x_1352_);
lean_dec_ref_known(v___x_1348_, 2);
lean_del_object(v___x_1312_);
v___x_1419_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1420_ = l_Lean_inheritedTraceOptions;
v___x_1421_ = lean_st_ref_get(v___x_1420_);
v___x_1422_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1423_ = lean_st_ref_get(v___y_1306_);
v_scopes_1424_ = lean_ctor_get(v___x_1423_, 2);
lean_inc(v_scopes_1424_);
lean_dec(v___x_1423_);
v___x_1425_ = l_List_head_x21___redArg(v___x_1422_, v_scopes_1424_);
lean_dec(v_scopes_1424_);
v_opts_1426_ = lean_ctor_get(v___x_1425_, 1);
lean_inc_ref(v_opts_1426_);
lean_dec(v___x_1425_);
v_hasTrace_1427_ = lean_ctor_get_uint8(v_opts_1426_, sizeof(void*)*1);
if (v_hasTrace_1427_ == 0)
{
lean_dec_ref(v_opts_1426_);
lean_dec(v___x_1421_);
lean_dec(v___x_1347_);
lean_dec(v___x_1346_);
lean_del_object(v___x_1344_);
goto v___jp_1337_;
}
else
{
lean_object* v___x_1428_; uint8_t v___x_1429_; 
v___x_1428_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1429_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1421_, v_opts_1426_, v___x_1428_);
lean_dec_ref(v_opts_1426_);
lean_dec(v___x_1421_);
if (v___x_1429_ == 0)
{
lean_dec(v___x_1347_);
lean_dec(v___x_1346_);
lean_del_object(v___x_1344_);
goto v___jp_1337_;
}
else
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1433_; 
v___x_1430_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7);
v___x_1431_ = l_Nat_reprFast(v___x_1346_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set_tag(v___x_1344_, 3);
lean_ctor_set(v___x_1344_, 0, v___x_1431_);
v___x_1433_ = v___x_1344_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1434_ = l_Lean_MessageData_ofFormat(v___x_1433_);
v___x_1435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1430_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
v___x_1436_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9);
v___x_1437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1435_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
v___x_1438_ = l_Nat_reprFast(v___x_1347_);
v___x_1439_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
v___x_1440_ = l_Lean_MessageData_ofFormat(v___x_1439_);
v___x_1441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1437_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
v___x_1442_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11);
v___x_1443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1441_);
lean_ctor_set(v___x_1443_, 1, v___x_1442_);
v___x_1444_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1419_, v___x_1443_, v___y_1305_, v___y_1306_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_dec_ref_known(v___x_1444_, 1);
goto v___jp_1337_;
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
lean_del_object(v___x_1317_);
lean_dec(v_snd_1315_);
lean_dec(v_fst_1314_);
lean_dec(v_cmd_1298_);
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1444_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1444_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1445_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
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
lean_object* v___x_1455_; 
lean_dec(v_endPos_1321_);
lean_del_object(v___x_1312_);
v___x_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1455_, 0, v_fst_1314_);
lean_ctor_set(v___x_1455_, 1, v_snd_1315_);
v_a_1326_ = v___x_1455_;
goto v___jp_1325_;
}
}
}
else
{
lean_object* v___x_1456_; 
lean_dec(v_endPos_1321_);
lean_del_object(v___x_1312_);
v___x_1456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1456_, 0, v_fst_1314_);
lean_ctor_set(v___x_1456_, 1, v_snd_1315_);
v_a_1326_ = v___x_1456_;
goto v___jp_1325_;
}
v___jp_1325_:
{
lean_object* v___x_1328_; 
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 1, v_a_1326_);
lean_ctor_set(v___x_1317_, 0, v___x_1324_);
v___x_1328_ = v___x_1317_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1324_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_a_1326_);
v___x_1328_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
size_t v___x_1329_; size_t v___x_1330_; 
v___x_1329_ = ((size_t)1ULL);
v___x_1330_ = lean_usize_add(v_i_1303_, v___x_1329_);
v_i_1303_ = v___x_1330_;
v_b_1304_ = v___x_1328_;
goto _start;
}
}
v___jp_1333_:
{
lean_object* v___x_1335_; 
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 1, v_snd_1315_);
lean_ctor_set(v___x_1312_, 0, v_fst_1314_);
v___x_1335_ = v___x_1312_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_fst_1314_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_snd_1315_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
v_a_1326_ = v___x_1335_;
goto v___jp_1325_;
}
}
v___jp_1337_:
{
lean_object* v___x_1338_; 
v___x_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1338_, 0, v_fst_1314_);
lean_ctor_set(v___x_1338_, 1, v_snd_1315_);
v_a_1326_ = v___x_1338_;
goto v___jp_1325_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___boxed(lean_object* v___x_1460_, lean_object* v_val_1461_, lean_object* v_cmd_1462_, lean_object* v_onUnsolved_1463_, lean_object* v___y_1464_, lean_object* v_as_1465_, lean_object* v_sz_1466_, lean_object* v_i_1467_, lean_object* v_b_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
uint8_t v_onUnsolved_boxed_1472_; uint8_t v___y_11947__boxed_1473_; size_t v_sz_boxed_1474_; size_t v_i_boxed_1475_; lean_object* v_res_1476_; 
v_onUnsolved_boxed_1472_ = lean_unbox(v_onUnsolved_1463_);
v___y_11947__boxed_1473_ = lean_unbox(v___y_1464_);
v_sz_boxed_1474_ = lean_unbox_usize(v_sz_1466_);
lean_dec(v_sz_1466_);
v_i_boxed_1475_ = lean_unbox_usize(v_i_1467_);
lean_dec(v_i_1467_);
v_res_1476_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12(v___x_1460_, v_val_1461_, v_cmd_1462_, v_onUnsolved_boxed_1472_, v___y_11947__boxed_1473_, v_as_1465_, v_sz_boxed_1474_, v_i_boxed_1475_, v_b_1468_, v___y_1469_, v___y_1470_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec_ref(v_as_1465_);
lean_dec_ref(v_val_1461_);
lean_dec_ref(v___x_1460_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8(lean_object* v___x_1477_, lean_object* v_val_1478_, lean_object* v_cmd_1479_, uint8_t v_onUnsolved_1480_, uint8_t v___y_1481_, lean_object* v_as_1482_, size_t v_sz_1483_, size_t v_i_1484_, lean_object* v_b_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
uint8_t v___x_1489_; 
v___x_1489_ = lean_usize_dec_lt(v_i_1484_, v_sz_1483_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; 
lean_dec(v_cmd_1479_);
v___x_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1490_, 0, v_b_1485_);
return v___x_1490_;
}
else
{
lean_object* v_snd_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1639_; 
v_snd_1491_ = lean_ctor_get(v_b_1485_, 1);
v_isSharedCheck_1639_ = !lean_is_exclusive(v_b_1485_);
if (v_isSharedCheck_1639_ == 0)
{
lean_object* v_unused_1640_; 
v_unused_1640_ = lean_ctor_get(v_b_1485_, 0);
lean_dec(v_unused_1640_);
v___x_1493_ = v_b_1485_;
v_isShared_1494_ = v_isSharedCheck_1639_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_snd_1491_);
lean_dec(v_b_1485_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1639_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v_fst_1495_; lean_object* v_snd_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1638_; 
v_fst_1495_ = lean_ctor_get(v_snd_1491_, 0);
v_snd_1496_ = lean_ctor_get(v_snd_1491_, 1);
v_isSharedCheck_1638_ = !lean_is_exclusive(v_snd_1491_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1498_ = v_snd_1491_;
v_isShared_1499_ = v_isSharedCheck_1638_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_snd_1496_);
lean_inc(v_fst_1495_);
lean_dec(v_snd_1491_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1638_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v_a_1500_; lean_object* v_pos_1501_; lean_object* v_endPos_1502_; uint8_t v_severity_1503_; lean_object* v_data_1504_; lean_object* v___x_1505_; lean_object* v_a_1507_; 
v_a_1500_ = lean_array_uget_borrowed(v_as_1482_, v_i_1484_);
v_pos_1501_ = lean_ctor_get(v_a_1500_, 1);
v_endPos_1502_ = lean_ctor_get(v_a_1500_, 2);
lean_inc(v_endPos_1502_);
v_severity_1503_ = lean_ctor_get_uint8(v_a_1500_, sizeof(void*)*5 + 1);
v_data_1504_ = lean_ctor_get(v_a_1500_, 4);
v___x_1505_ = lean_box(0);
if (v_severity_1503_ == 2)
{
lean_object* v___f_1520_; uint8_t v___x_1521_; 
v___f_1520_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
lean_inc(v_data_1504_);
v___x_1521_ = l_Lean_MessageData_hasTag(v___f_1520_, v_data_1504_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; 
lean_dec(v_endPos_1502_);
lean_del_object(v___x_1493_);
v___x_1522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1522_, 0, v_fst_1495_);
lean_ctor_set(v___x_1522_, 1, v_snd_1496_);
v_a_1507_ = v___x_1522_;
goto v___jp_1506_;
}
else
{
if (lean_obj_tag(v_endPos_1502_) == 1)
{
lean_object* v_val_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1635_; 
v_val_1523_ = lean_ctor_get(v_endPos_1502_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v_endPos_1502_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1525_ = v_endPos_1502_;
v_isShared_1526_ = v_isSharedCheck_1635_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_val_1523_);
lean_dec(v_endPos_1502_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1635_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; uint8_t v___x_1531_; 
lean_inc_ref(v_pos_1501_);
v___x_1527_ = l_Lean_FileMap_ofPosition(v___x_1477_, v_pos_1501_);
v___x_1528_ = l_Lean_FileMap_ofPosition(v___x_1477_, v_val_1523_);
lean_inc(v___x_1528_);
lean_inc(v___x_1527_);
v___x_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1527_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
v___x_1530_ = 0;
v___x_1531_ = l_Lean_Syntax_Range_includes(v_val_1478_, v___x_1529_, v___x_1530_, v___x_1530_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; 
lean_dec_ref_known(v___x_1529_, 2);
lean_dec(v___x_1528_);
lean_dec(v___x_1527_);
lean_del_object(v___x_1525_);
lean_del_object(v___x_1493_);
v___x_1532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1532_, 0, v_fst_1495_);
lean_ctor_set(v___x_1532_, 1, v_snd_1496_);
v_a_1507_ = v___x_1532_;
goto v___jp_1506_;
}
else
{
lean_object* v___x_1533_; 
lean_inc(v_cmd_1479_);
lean_inc_ref(v___x_1529_);
v___x_1533_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1529_, v_cmd_1479_);
if (lean_obj_tag(v___x_1533_) == 1)
{
lean_object* v_val_1534_; lean_object* v_fst_1535_; lean_object* v_snd_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1599_; 
lean_dec(v___x_1528_);
lean_dec(v___x_1527_);
lean_del_object(v___x_1525_);
v_val_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_val_1534_);
lean_dec_ref_known(v___x_1533_, 1);
v_fst_1535_ = lean_ctor_get(v_val_1534_, 0);
v_snd_1536_ = lean_ctor_get(v_val_1534_, 1);
v_isSharedCheck_1599_ = !lean_is_exclusive(v_val_1534_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1538_ = v_val_1534_;
v_isShared_1539_ = v_isSharedCheck_1599_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_snd_1536_);
lean_inc(v_fst_1535_);
lean_dec(v_val_1534_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1599_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; uint8_t v___y_1597_; lean_object* v___x_1598_; 
v___x_1598_ = l_Lean_Syntax_getPos_x3f(v_fst_1535_, v___x_1530_);
if (lean_obj_tag(v___x_1598_) == 0)
{
v___y_1597_ = v___x_1531_;
goto v___jp_1596_;
}
else
{
lean_dec_ref_known(v___x_1598_, 1);
v___y_1597_ = v___x_1530_;
goto v___jp_1596_;
}
v___jp_1540_:
{
lean_object* v___x_1546_; 
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 1, v_snd_1496_);
lean_ctor_set(v___x_1538_, 0, v_fst_1495_);
v___x_1546_ = v___x_1538_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_fst_1495_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v_snd_1496_);
v___x_1546_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
size_t v_sz_1547_; size_t v___x_1548_; lean_object* v___x_1549_; 
v_sz_1547_ = lean_array_size(v___y_1541_);
v___x_1548_ = ((size_t)0ULL);
v___x_1549_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1529_, v_fst_1535_, v_snd_1536_, v___y_1542_, v___y_1541_, v_sz_1547_, v___x_1548_, v___x_1546_);
lean_dec_ref(v___y_1541_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v_fst_1551_; lean_object* v_snd_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___x_1549_, 1);
v_fst_1551_ = lean_ctor_get(v_a_1550_, 0);
v_snd_1552_ = lean_ctor_get(v_a_1550_, 1);
v_isSharedCheck_1559_ = !lean_is_exclusive(v_a_1550_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v_a_1550_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_snd_1552_);
lean_inc(v_fst_1551_);
lean_dec(v_a_1550_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_fst_1551_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_snd_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
v_a_1507_ = v___x_1557_;
goto v___jp_1506_;
}
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_del_object(v___x_1498_);
lean_dec(v_cmd_1479_);
v_a_1560_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1549_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1549_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
v___jp_1569_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; uint8_t v___x_1574_; 
lean_inc_ref(v___x_1529_);
v___x_1570_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1529_);
v___x_1571_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1504_);
v___x_1572_ = lean_array_get_size(v___x_1571_);
v___x_1573_ = lean_unsigned_to_nat(0u);
v___x_1574_ = lean_nat_dec_eq(v___x_1572_, v___x_1573_);
if (v___x_1574_ == 0)
{
v___y_1541_ = v___x_1571_;
v___y_1542_ = v___x_1570_;
v___y_1543_ = v___y_1486_;
v___y_1544_ = v___y_1487_;
goto v___jp_1540_;
}
else
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v_scopes_1580_; lean_object* v___x_1581_; lean_object* v_opts_1582_; uint8_t v_hasTrace_1583_; 
v___x_1575_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1576_ = l_Lean_inheritedTraceOptions;
v___x_1577_ = lean_st_ref_get(v___x_1576_);
v___x_1578_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1579_ = lean_st_ref_get(v___y_1487_);
v_scopes_1580_ = lean_ctor_get(v___x_1579_, 2);
lean_inc(v_scopes_1580_);
lean_dec(v___x_1579_);
v___x_1581_ = l_List_head_x21___redArg(v___x_1578_, v_scopes_1580_);
lean_dec(v_scopes_1580_);
v_opts_1582_ = lean_ctor_get(v___x_1581_, 1);
lean_inc_ref(v_opts_1582_);
lean_dec(v___x_1581_);
v_hasTrace_1583_ = lean_ctor_get_uint8(v_opts_1582_, sizeof(void*)*1);
if (v_hasTrace_1583_ == 0)
{
lean_dec_ref(v_opts_1582_);
lean_dec(v___x_1577_);
v___y_1541_ = v___x_1571_;
v___y_1542_ = v___x_1570_;
v___y_1543_ = v___y_1486_;
v___y_1544_ = v___y_1487_;
goto v___jp_1540_;
}
else
{
lean_object* v___x_1584_; uint8_t v___x_1585_; 
v___x_1584_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1585_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1577_, v_opts_1582_, v___x_1584_);
lean_dec_ref(v_opts_1582_);
lean_dec(v___x_1577_);
if (v___x_1585_ == 0)
{
v___y_1541_ = v___x_1571_;
v___y_1542_ = v___x_1570_;
v___y_1543_ = v___y_1486_;
v___y_1544_ = v___y_1487_;
goto v___jp_1540_;
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5);
v___x_1587_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1575_, v___x_1586_, v___y_1486_, v___y_1487_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_dec_ref_known(v___x_1587_, 1);
v___y_1541_ = v___x_1571_;
v___y_1542_ = v___x_1570_;
v___y_1543_ = v___y_1486_;
v___y_1544_ = v___y_1487_;
goto v___jp_1540_;
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
lean_dec_ref(v___x_1571_);
lean_dec(v___x_1570_);
lean_del_object(v___x_1538_);
lean_dec(v_snd_1536_);
lean_dec(v_fst_1535_);
lean_dec_ref_known(v___x_1529_, 2);
lean_del_object(v___x_1498_);
lean_dec(v_snd_1496_);
lean_dec(v_fst_1495_);
lean_dec(v_cmd_1479_);
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1587_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1587_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
}
}
}
v___jp_1596_:
{
if (v_onUnsolved_1480_ == 0)
{
if (v___y_1481_ == 0)
{
lean_del_object(v___x_1538_);
lean_dec(v_snd_1536_);
lean_dec(v_fst_1535_);
lean_dec_ref_known(v___x_1529_, 2);
goto v___jp_1514_;
}
else
{
if (v___y_1597_ == 0)
{
lean_del_object(v___x_1538_);
lean_dec(v_snd_1536_);
lean_dec(v_fst_1535_);
lean_dec_ref_known(v___x_1529_, 2);
goto v___jp_1514_;
}
else
{
lean_del_object(v___x_1493_);
goto v___jp_1569_;
}
}
}
else
{
lean_del_object(v___x_1493_);
goto v___jp_1569_;
}
}
}
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v_scopes_1605_; lean_object* v___x_1606_; lean_object* v_opts_1607_; uint8_t v_hasTrace_1608_; 
lean_dec(v___x_1533_);
lean_dec_ref_known(v___x_1529_, 2);
lean_del_object(v___x_1493_);
v___x_1600_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1601_ = l_Lean_inheritedTraceOptions;
v___x_1602_ = lean_st_ref_get(v___x_1601_);
v___x_1603_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1604_ = lean_st_ref_get(v___y_1487_);
v_scopes_1605_ = lean_ctor_get(v___x_1604_, 2);
lean_inc(v_scopes_1605_);
lean_dec(v___x_1604_);
v___x_1606_ = l_List_head_x21___redArg(v___x_1603_, v_scopes_1605_);
lean_dec(v_scopes_1605_);
v_opts_1607_ = lean_ctor_get(v___x_1606_, 1);
lean_inc_ref(v_opts_1607_);
lean_dec(v___x_1606_);
v_hasTrace_1608_ = lean_ctor_get_uint8(v_opts_1607_, sizeof(void*)*1);
if (v_hasTrace_1608_ == 0)
{
lean_dec_ref(v_opts_1607_);
lean_dec(v___x_1602_);
lean_dec(v___x_1528_);
lean_dec(v___x_1527_);
lean_del_object(v___x_1525_);
goto v___jp_1518_;
}
else
{
lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1609_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1610_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1602_, v_opts_1607_, v___x_1609_);
lean_dec_ref(v_opts_1607_);
lean_dec(v___x_1602_);
if (v___x_1610_ == 0)
{
lean_dec(v___x_1528_);
lean_dec(v___x_1527_);
lean_del_object(v___x_1525_);
goto v___jp_1518_;
}
else
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1614_; 
v___x_1611_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7);
v___x_1612_ = l_Nat_reprFast(v___x_1527_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set_tag(v___x_1525_, 3);
lean_ctor_set(v___x_1525_, 0, v___x_1612_);
v___x_1614_ = v___x_1525_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1612_);
v___x_1614_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1615_ = l_Lean_MessageData_ofFormat(v___x_1614_);
v___x_1616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1611_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9);
v___x_1618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1616_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
v___x_1619_ = l_Nat_reprFast(v___x_1528_);
v___x_1620_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
v___x_1621_ = l_Lean_MessageData_ofFormat(v___x_1620_);
v___x_1622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1618_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11);
v___x_1624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1622_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v___x_1625_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1600_, v___x_1624_, v___y_1486_, v___y_1487_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_dec_ref_known(v___x_1625_, 1);
goto v___jp_1518_;
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
lean_del_object(v___x_1498_);
lean_dec(v_snd_1496_);
lean_dec(v_fst_1495_);
lean_dec(v_cmd_1479_);
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1625_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1625_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
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
lean_object* v___x_1636_; 
lean_dec(v_endPos_1502_);
lean_del_object(v___x_1493_);
v___x_1636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1636_, 0, v_fst_1495_);
lean_ctor_set(v___x_1636_, 1, v_snd_1496_);
v_a_1507_ = v___x_1636_;
goto v___jp_1506_;
}
}
}
else
{
lean_object* v___x_1637_; 
lean_dec(v_endPos_1502_);
lean_del_object(v___x_1493_);
v___x_1637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1637_, 0, v_fst_1495_);
lean_ctor_set(v___x_1637_, 1, v_snd_1496_);
v_a_1507_ = v___x_1637_;
goto v___jp_1506_;
}
v___jp_1506_:
{
lean_object* v___x_1509_; 
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 1, v_a_1507_);
lean_ctor_set(v___x_1498_, 0, v___x_1505_);
v___x_1509_ = v___x_1498_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v_a_1507_);
v___x_1509_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
size_t v___x_1510_; size_t v___x_1511_; lean_object* v___x_1512_; 
v___x_1510_ = ((size_t)1ULL);
v___x_1511_ = lean_usize_add(v_i_1484_, v___x_1510_);
v___x_1512_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12(v___x_1477_, v_val_1478_, v_cmd_1479_, v_onUnsolved_1480_, v___y_1481_, v_as_1482_, v_sz_1483_, v___x_1511_, v___x_1509_, v___y_1486_, v___y_1487_);
return v___x_1512_;
}
}
v___jp_1514_:
{
lean_object* v___x_1516_; 
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 1, v_snd_1496_);
lean_ctor_set(v___x_1493_, 0, v_fst_1495_);
v___x_1516_ = v___x_1493_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_fst_1495_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_snd_1496_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
v_a_1507_ = v___x_1516_;
goto v___jp_1506_;
}
}
v___jp_1518_:
{
lean_object* v___x_1519_; 
v___x_1519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1519_, 0, v_fst_1495_);
lean_ctor_set(v___x_1519_, 1, v_snd_1496_);
v_a_1507_ = v___x_1519_;
goto v___jp_1506_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___boxed(lean_object* v___x_1641_, lean_object* v_val_1642_, lean_object* v_cmd_1643_, lean_object* v_onUnsolved_1644_, lean_object* v___y_1645_, lean_object* v_as_1646_, lean_object* v_sz_1647_, lean_object* v_i_1648_, lean_object* v_b_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
uint8_t v_onUnsolved_boxed_1653_; uint8_t v___y_12288__boxed_1654_; size_t v_sz_boxed_1655_; size_t v_i_boxed_1656_; lean_object* v_res_1657_; 
v_onUnsolved_boxed_1653_ = lean_unbox(v_onUnsolved_1644_);
v___y_12288__boxed_1654_ = lean_unbox(v___y_1645_);
v_sz_boxed_1655_ = lean_unbox_usize(v_sz_1647_);
lean_dec(v_sz_1647_);
v_i_boxed_1656_ = lean_unbox_usize(v_i_1648_);
lean_dec(v_i_1648_);
v_res_1657_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8(v___x_1641_, v_val_1642_, v_cmd_1643_, v_onUnsolved_boxed_1653_, v___y_12288__boxed_1654_, v_as_1646_, v_sz_boxed_1655_, v_i_boxed_1656_, v_b_1649_, v___y_1650_, v___y_1651_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec_ref(v_as_1646_);
lean_dec_ref(v_val_1642_);
lean_dec_ref(v___x_1641_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10_spec__12(lean_object* v___x_1658_, lean_object* v_val_1659_, lean_object* v_cmd_1660_, uint8_t v_onUnsolved_1661_, uint8_t v___y_1662_, lean_object* v_as_1663_, size_t v_sz_1664_, size_t v_i_1665_, lean_object* v_b_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
uint8_t v___x_1670_; 
v___x_1670_ = lean_usize_dec_lt(v_i_1665_, v_sz_1664_);
if (v___x_1670_ == 0)
{
lean_object* v___x_1671_; 
lean_dec(v_cmd_1660_);
v___x_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1671_, 0, v_b_1666_);
return v___x_1671_;
}
else
{
lean_object* v_snd_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1820_; 
v_snd_1672_ = lean_ctor_get(v_b_1666_, 1);
v_isSharedCheck_1820_ = !lean_is_exclusive(v_b_1666_);
if (v_isSharedCheck_1820_ == 0)
{
lean_object* v_unused_1821_; 
v_unused_1821_ = lean_ctor_get(v_b_1666_, 0);
lean_dec(v_unused_1821_);
v___x_1674_ = v_b_1666_;
v_isShared_1675_ = v_isSharedCheck_1820_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_snd_1672_);
lean_dec(v_b_1666_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1820_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v_fst_1676_; lean_object* v_snd_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1819_; 
v_fst_1676_ = lean_ctor_get(v_snd_1672_, 0);
v_snd_1677_ = lean_ctor_get(v_snd_1672_, 1);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_snd_1672_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1679_ = v_snd_1672_;
v_isShared_1680_ = v_isSharedCheck_1819_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_snd_1677_);
lean_inc(v_fst_1676_);
lean_dec(v_snd_1672_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1819_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v_a_1681_; lean_object* v_pos_1682_; lean_object* v_endPos_1683_; uint8_t v_severity_1684_; lean_object* v_data_1685_; lean_object* v___x_1686_; lean_object* v_a_1688_; 
v_a_1681_ = lean_array_uget_borrowed(v_as_1663_, v_i_1665_);
v_pos_1682_ = lean_ctor_get(v_a_1681_, 1);
v_endPos_1683_ = lean_ctor_get(v_a_1681_, 2);
lean_inc(v_endPos_1683_);
v_severity_1684_ = lean_ctor_get_uint8(v_a_1681_, sizeof(void*)*5 + 1);
v_data_1685_ = lean_ctor_get(v_a_1681_, 4);
v___x_1686_ = lean_box(0);
if (v_severity_1684_ == 2)
{
lean_object* v___f_1701_; uint8_t v___x_1702_; 
v___f_1701_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
lean_inc(v_data_1685_);
v___x_1702_ = l_Lean_MessageData_hasTag(v___f_1701_, v_data_1685_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1703_; 
lean_dec(v_endPos_1683_);
lean_del_object(v___x_1674_);
v___x_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1703_, 0, v_fst_1676_);
lean_ctor_set(v___x_1703_, 1, v_snd_1677_);
v_a_1688_ = v___x_1703_;
goto v___jp_1687_;
}
else
{
if (lean_obj_tag(v_endPos_1683_) == 1)
{
lean_object* v_val_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1816_; 
v_val_1704_ = lean_ctor_get(v_endPos_1683_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v_endPos_1683_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1706_ = v_endPos_1683_;
v_isShared_1707_ = v_isSharedCheck_1816_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_val_1704_);
lean_dec(v_endPos_1683_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1816_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; uint8_t v___x_1712_; 
lean_inc_ref(v_pos_1682_);
v___x_1708_ = l_Lean_FileMap_ofPosition(v___x_1658_, v_pos_1682_);
v___x_1709_ = l_Lean_FileMap_ofPosition(v___x_1658_, v_val_1704_);
lean_inc(v___x_1709_);
lean_inc(v___x_1708_);
v___x_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1708_);
lean_ctor_set(v___x_1710_, 1, v___x_1709_);
v___x_1711_ = 0;
v___x_1712_ = l_Lean_Syntax_Range_includes(v_val_1659_, v___x_1710_, v___x_1711_, v___x_1711_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; 
lean_dec_ref_known(v___x_1710_, 2);
lean_dec(v___x_1709_);
lean_dec(v___x_1708_);
lean_del_object(v___x_1706_);
lean_del_object(v___x_1674_);
v___x_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1713_, 0, v_fst_1676_);
lean_ctor_set(v___x_1713_, 1, v_snd_1677_);
v_a_1688_ = v___x_1713_;
goto v___jp_1687_;
}
else
{
lean_object* v___x_1714_; 
lean_inc(v_cmd_1660_);
lean_inc_ref(v___x_1710_);
v___x_1714_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1710_, v_cmd_1660_);
if (lean_obj_tag(v___x_1714_) == 1)
{
lean_object* v_val_1715_; lean_object* v_fst_1716_; lean_object* v_snd_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1780_; 
lean_dec(v___x_1709_);
lean_dec(v___x_1708_);
lean_del_object(v___x_1706_);
v_val_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_val_1715_);
lean_dec_ref_known(v___x_1714_, 1);
v_fst_1716_ = lean_ctor_get(v_val_1715_, 0);
v_snd_1717_ = lean_ctor_get(v_val_1715_, 1);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_val_1715_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1719_ = v_val_1715_;
v_isShared_1720_ = v_isSharedCheck_1780_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_snd_1717_);
lean_inc(v_fst_1716_);
lean_dec(v_val_1715_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1780_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; uint8_t v___y_1778_; lean_object* v___x_1779_; 
v___x_1779_ = l_Lean_Syntax_getPos_x3f(v_fst_1716_, v___x_1711_);
if (lean_obj_tag(v___x_1779_) == 0)
{
v___y_1778_ = v___x_1712_;
goto v___jp_1777_;
}
else
{
lean_dec_ref_known(v___x_1779_, 1);
v___y_1778_ = v___x_1711_;
goto v___jp_1777_;
}
v___jp_1721_:
{
lean_object* v___x_1727_; 
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 1, v_snd_1677_);
lean_ctor_set(v___x_1719_, 0, v_fst_1676_);
v___x_1727_ = v___x_1719_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_fst_1676_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v_snd_1677_);
v___x_1727_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
size_t v_sz_1728_; size_t v___x_1729_; lean_object* v___x_1730_; 
v_sz_1728_ = lean_array_size(v___y_1722_);
v___x_1729_ = ((size_t)0ULL);
v___x_1730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1710_, v_fst_1716_, v_snd_1717_, v___y_1723_, v___y_1722_, v_sz_1728_, v___x_1729_, v___x_1727_);
lean_dec_ref(v___y_1722_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_a_1731_; lean_object* v_fst_1732_; lean_object* v_snd_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_a_1731_);
lean_dec_ref_known(v___x_1730_, 1);
v_fst_1732_ = lean_ctor_get(v_a_1731_, 0);
v_snd_1733_ = lean_ctor_get(v_a_1731_, 1);
v_isSharedCheck_1740_ = !lean_is_exclusive(v_a_1731_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v_a_1731_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_snd_1733_);
lean_inc(v_fst_1732_);
lean_dec(v_a_1731_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_fst_1732_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_snd_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
v_a_1688_ = v___x_1738_;
goto v___jp_1687_;
}
}
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_del_object(v___x_1679_);
lean_dec(v_cmd_1660_);
v_a_1741_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1730_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1730_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1741_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
}
v___jp_1750_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
lean_inc_ref(v___x_1710_);
v___x_1751_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1710_);
v___x_1752_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1685_);
v___x_1753_ = lean_array_get_size(v___x_1752_);
v___x_1754_ = lean_unsigned_to_nat(0u);
v___x_1755_ = lean_nat_dec_eq(v___x_1753_, v___x_1754_);
if (v___x_1755_ == 0)
{
v___y_1722_ = v___x_1752_;
v___y_1723_ = v___x_1751_;
v___y_1724_ = v___y_1667_;
v___y_1725_ = v___y_1668_;
goto v___jp_1721_;
}
else
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v_scopes_1761_; lean_object* v___x_1762_; lean_object* v_opts_1763_; uint8_t v_hasTrace_1764_; 
v___x_1756_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1757_ = l_Lean_inheritedTraceOptions;
v___x_1758_ = lean_st_ref_get(v___x_1757_);
v___x_1759_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1760_ = lean_st_ref_get(v___y_1668_);
v_scopes_1761_ = lean_ctor_get(v___x_1760_, 2);
lean_inc(v_scopes_1761_);
lean_dec(v___x_1760_);
v___x_1762_ = l_List_head_x21___redArg(v___x_1759_, v_scopes_1761_);
lean_dec(v_scopes_1761_);
v_opts_1763_ = lean_ctor_get(v___x_1762_, 1);
lean_inc_ref(v_opts_1763_);
lean_dec(v___x_1762_);
v_hasTrace_1764_ = lean_ctor_get_uint8(v_opts_1763_, sizeof(void*)*1);
if (v_hasTrace_1764_ == 0)
{
lean_dec_ref(v_opts_1763_);
lean_dec(v___x_1758_);
v___y_1722_ = v___x_1752_;
v___y_1723_ = v___x_1751_;
v___y_1724_ = v___y_1667_;
v___y_1725_ = v___y_1668_;
goto v___jp_1721_;
}
else
{
lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1765_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1766_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1758_, v_opts_1763_, v___x_1765_);
lean_dec_ref(v_opts_1763_);
lean_dec(v___x_1758_);
if (v___x_1766_ == 0)
{
v___y_1722_ = v___x_1752_;
v___y_1723_ = v___x_1751_;
v___y_1724_ = v___y_1667_;
v___y_1725_ = v___y_1668_;
goto v___jp_1721_;
}
else
{
lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1767_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5);
v___x_1768_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1756_, v___x_1767_, v___y_1667_, v___y_1668_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_dec_ref_known(v___x_1768_, 1);
v___y_1722_ = v___x_1752_;
v___y_1723_ = v___x_1751_;
v___y_1724_ = v___y_1667_;
v___y_1725_ = v___y_1668_;
goto v___jp_1721_;
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_dec_ref(v___x_1752_);
lean_dec(v___x_1751_);
lean_del_object(v___x_1719_);
lean_dec(v_snd_1717_);
lean_dec(v_fst_1716_);
lean_dec_ref_known(v___x_1710_, 2);
lean_del_object(v___x_1679_);
lean_dec(v_snd_1677_);
lean_dec(v_fst_1676_);
lean_dec(v_cmd_1660_);
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1768_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1768_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
}
}
}
v___jp_1777_:
{
if (v_onUnsolved_1661_ == 0)
{
if (v___y_1662_ == 0)
{
lean_del_object(v___x_1719_);
lean_dec(v_snd_1717_);
lean_dec(v_fst_1716_);
lean_dec_ref_known(v___x_1710_, 2);
goto v___jp_1695_;
}
else
{
if (v___y_1778_ == 0)
{
lean_del_object(v___x_1719_);
lean_dec(v_snd_1717_);
lean_dec(v_fst_1716_);
lean_dec_ref_known(v___x_1710_, 2);
goto v___jp_1695_;
}
else
{
lean_del_object(v___x_1674_);
goto v___jp_1750_;
}
}
}
else
{
lean_del_object(v___x_1674_);
goto v___jp_1750_;
}
}
}
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v_scopes_1786_; lean_object* v___x_1787_; lean_object* v_opts_1788_; uint8_t v_hasTrace_1789_; 
lean_dec(v___x_1714_);
lean_dec_ref_known(v___x_1710_, 2);
lean_del_object(v___x_1674_);
v___x_1781_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1782_ = l_Lean_inheritedTraceOptions;
v___x_1783_ = lean_st_ref_get(v___x_1782_);
v___x_1784_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1785_ = lean_st_ref_get(v___y_1668_);
v_scopes_1786_ = lean_ctor_get(v___x_1785_, 2);
lean_inc(v_scopes_1786_);
lean_dec(v___x_1785_);
v___x_1787_ = l_List_head_x21___redArg(v___x_1784_, v_scopes_1786_);
lean_dec(v_scopes_1786_);
v_opts_1788_ = lean_ctor_get(v___x_1787_, 1);
lean_inc_ref(v_opts_1788_);
lean_dec(v___x_1787_);
v_hasTrace_1789_ = lean_ctor_get_uint8(v_opts_1788_, sizeof(void*)*1);
if (v_hasTrace_1789_ == 0)
{
lean_dec_ref(v_opts_1788_);
lean_dec(v___x_1783_);
lean_dec(v___x_1709_);
lean_dec(v___x_1708_);
lean_del_object(v___x_1706_);
goto v___jp_1699_;
}
else
{
lean_object* v___x_1790_; uint8_t v___x_1791_; 
v___x_1790_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1791_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1783_, v_opts_1788_, v___x_1790_);
lean_dec_ref(v_opts_1788_);
lean_dec(v___x_1783_);
if (v___x_1791_ == 0)
{
lean_dec(v___x_1709_);
lean_dec(v___x_1708_);
lean_del_object(v___x_1706_);
goto v___jp_1699_;
}
else
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1795_; 
v___x_1792_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7);
v___x_1793_ = l_Nat_reprFast(v___x_1708_);
if (v_isShared_1707_ == 0)
{
lean_ctor_set_tag(v___x_1706_, 3);
lean_ctor_set(v___x_1706_, 0, v___x_1793_);
v___x_1795_ = v___x_1706_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1793_);
v___x_1795_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1796_ = l_Lean_MessageData_ofFormat(v___x_1795_);
v___x_1797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1792_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
v___x_1798_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9);
v___x_1799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1797_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
v___x_1800_ = l_Nat_reprFast(v___x_1709_);
v___x_1801_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
v___x_1802_ = l_Lean_MessageData_ofFormat(v___x_1801_);
v___x_1803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1799_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
v___x_1804_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11);
v___x_1805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1803_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
v___x_1806_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1781_, v___x_1805_, v___y_1667_, v___y_1668_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_dec_ref_known(v___x_1806_, 1);
goto v___jp_1699_;
}
else
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1814_; 
lean_del_object(v___x_1679_);
lean_dec(v_snd_1677_);
lean_dec(v_fst_1676_);
lean_dec(v_cmd_1660_);
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1809_ = v___x_1806_;
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1806_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1810_ == 0)
{
v___x_1812_ = v___x_1809_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
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
lean_object* v___x_1817_; 
lean_dec(v_endPos_1683_);
lean_del_object(v___x_1674_);
v___x_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1817_, 0, v_fst_1676_);
lean_ctor_set(v___x_1817_, 1, v_snd_1677_);
v_a_1688_ = v___x_1817_;
goto v___jp_1687_;
}
}
}
else
{
lean_object* v___x_1818_; 
lean_dec(v_endPos_1683_);
lean_del_object(v___x_1674_);
v___x_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1818_, 0, v_fst_1676_);
lean_ctor_set(v___x_1818_, 1, v_snd_1677_);
v_a_1688_ = v___x_1818_;
goto v___jp_1687_;
}
v___jp_1687_:
{
lean_object* v___x_1690_; 
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 1, v_a_1688_);
lean_ctor_set(v___x_1679_, 0, v___x_1686_);
v___x_1690_ = v___x_1679_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1686_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v_a_1688_);
v___x_1690_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
size_t v___x_1691_; size_t v___x_1692_; 
v___x_1691_ = ((size_t)1ULL);
v___x_1692_ = lean_usize_add(v_i_1665_, v___x_1691_);
v_i_1665_ = v___x_1692_;
v_b_1666_ = v___x_1690_;
goto _start;
}
}
v___jp_1695_:
{
lean_object* v___x_1697_; 
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 1, v_snd_1677_);
lean_ctor_set(v___x_1674_, 0, v_fst_1676_);
v___x_1697_ = v___x_1674_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_fst_1676_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_snd_1677_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
v_a_1688_ = v___x_1697_;
goto v___jp_1687_;
}
}
v___jp_1699_:
{
lean_object* v___x_1700_; 
v___x_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1700_, 0, v_fst_1676_);
lean_ctor_set(v___x_1700_, 1, v_snd_1677_);
v_a_1688_ = v___x_1700_;
goto v___jp_1687_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10_spec__12___boxed(lean_object* v___x_1822_, lean_object* v_val_1823_, lean_object* v_cmd_1824_, lean_object* v_onUnsolved_1825_, lean_object* v___y_1826_, lean_object* v_as_1827_, lean_object* v_sz_1828_, lean_object* v_i_1829_, lean_object* v_b_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
uint8_t v_onUnsolved_boxed_1834_; uint8_t v___y_12620__boxed_1835_; size_t v_sz_boxed_1836_; size_t v_i_boxed_1837_; lean_object* v_res_1838_; 
v_onUnsolved_boxed_1834_ = lean_unbox(v_onUnsolved_1825_);
v___y_12620__boxed_1835_ = lean_unbox(v___y_1826_);
v_sz_boxed_1836_ = lean_unbox_usize(v_sz_1828_);
lean_dec(v_sz_1828_);
v_i_boxed_1837_ = lean_unbox_usize(v_i_1829_);
lean_dec(v_i_1829_);
v_res_1838_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10_spec__12(v___x_1822_, v_val_1823_, v_cmd_1824_, v_onUnsolved_boxed_1834_, v___y_12620__boxed_1835_, v_as_1827_, v_sz_boxed_1836_, v_i_boxed_1837_, v_b_1830_, v___y_1831_, v___y_1832_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec_ref(v_as_1827_);
lean_dec_ref(v_val_1823_);
lean_dec_ref(v___x_1822_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10(lean_object* v___x_1839_, lean_object* v_val_1840_, lean_object* v_cmd_1841_, uint8_t v_onUnsolved_1842_, uint8_t v___y_1843_, lean_object* v_as_1844_, size_t v_sz_1845_, size_t v_i_1846_, lean_object* v_b_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
uint8_t v___x_1851_; 
v___x_1851_ = lean_usize_dec_lt(v_i_1846_, v_sz_1845_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; 
lean_dec(v_cmd_1841_);
v___x_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1852_, 0, v_b_1847_);
return v___x_1852_;
}
else
{
lean_object* v_snd_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_2001_; 
v_snd_1853_ = lean_ctor_get(v_b_1847_, 1);
v_isSharedCheck_2001_ = !lean_is_exclusive(v_b_1847_);
if (v_isSharedCheck_2001_ == 0)
{
lean_object* v_unused_2002_; 
v_unused_2002_ = lean_ctor_get(v_b_1847_, 0);
lean_dec(v_unused_2002_);
v___x_1855_ = v_b_1847_;
v_isShared_1856_ = v_isSharedCheck_2001_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_snd_1853_);
lean_dec(v_b_1847_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_2001_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v_fst_1857_; lean_object* v_snd_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_2000_; 
v_fst_1857_ = lean_ctor_get(v_snd_1853_, 0);
v_snd_1858_ = lean_ctor_get(v_snd_1853_, 1);
v_isSharedCheck_2000_ = !lean_is_exclusive(v_snd_1853_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1860_ = v_snd_1853_;
v_isShared_1861_ = v_isSharedCheck_2000_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_snd_1858_);
lean_inc(v_fst_1857_);
lean_dec(v_snd_1853_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_2000_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v_a_1862_; lean_object* v_pos_1863_; lean_object* v_endPos_1864_; uint8_t v_severity_1865_; lean_object* v_data_1866_; lean_object* v___x_1867_; lean_object* v_a_1869_; 
v_a_1862_ = lean_array_uget_borrowed(v_as_1844_, v_i_1846_);
v_pos_1863_ = lean_ctor_get(v_a_1862_, 1);
v_endPos_1864_ = lean_ctor_get(v_a_1862_, 2);
lean_inc(v_endPos_1864_);
v_severity_1865_ = lean_ctor_get_uint8(v_a_1862_, sizeof(void*)*5 + 1);
v_data_1866_ = lean_ctor_get(v_a_1862_, 4);
v___x_1867_ = lean_box(0);
if (v_severity_1865_ == 2)
{
lean_object* v___f_1882_; uint8_t v___x_1883_; 
v___f_1882_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
lean_inc(v_data_1866_);
v___x_1883_ = l_Lean_MessageData_hasTag(v___f_1882_, v_data_1866_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; 
lean_dec(v_endPos_1864_);
lean_del_object(v___x_1855_);
v___x_1884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1884_, 0, v_fst_1857_);
lean_ctor_set(v___x_1884_, 1, v_snd_1858_);
v_a_1869_ = v___x_1884_;
goto v___jp_1868_;
}
else
{
if (lean_obj_tag(v_endPos_1864_) == 1)
{
lean_object* v_val_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1997_; 
v_val_1885_ = lean_ctor_get(v_endPos_1864_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_endPos_1864_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1887_ = v_endPos_1864_;
v_isShared_1888_ = v_isSharedCheck_1997_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_val_1885_);
lean_dec(v_endPos_1864_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1997_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; uint8_t v___x_1892_; uint8_t v___x_1893_; 
lean_inc_ref(v_pos_1863_);
v___x_1889_ = l_Lean_FileMap_ofPosition(v___x_1839_, v_pos_1863_);
v___x_1890_ = l_Lean_FileMap_ofPosition(v___x_1839_, v_val_1885_);
lean_inc(v___x_1890_);
lean_inc(v___x_1889_);
v___x_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1889_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = 0;
v___x_1893_ = l_Lean_Syntax_Range_includes(v_val_1840_, v___x_1891_, v___x_1892_, v___x_1892_);
if (v___x_1893_ == 0)
{
lean_object* v___x_1894_; 
lean_dec_ref_known(v___x_1891_, 2);
lean_dec(v___x_1890_);
lean_dec(v___x_1889_);
lean_del_object(v___x_1887_);
lean_del_object(v___x_1855_);
v___x_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1894_, 0, v_fst_1857_);
lean_ctor_set(v___x_1894_, 1, v_snd_1858_);
v_a_1869_ = v___x_1894_;
goto v___jp_1868_;
}
else
{
lean_object* v___x_1895_; 
lean_inc(v_cmd_1841_);
lean_inc_ref(v___x_1891_);
v___x_1895_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1891_, v_cmd_1841_);
if (lean_obj_tag(v___x_1895_) == 1)
{
lean_object* v_val_1896_; lean_object* v_fst_1897_; lean_object* v_snd_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1961_; 
lean_dec(v___x_1890_);
lean_dec(v___x_1889_);
lean_del_object(v___x_1887_);
v_val_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_val_1896_);
lean_dec_ref_known(v___x_1895_, 1);
v_fst_1897_ = lean_ctor_get(v_val_1896_, 0);
v_snd_1898_ = lean_ctor_get(v_val_1896_, 1);
v_isSharedCheck_1961_ = !lean_is_exclusive(v_val_1896_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1900_ = v_val_1896_;
v_isShared_1901_ = v_isSharedCheck_1961_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_snd_1898_);
lean_inc(v_fst_1897_);
lean_dec(v_val_1896_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1961_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; uint8_t v___y_1959_; lean_object* v___x_1960_; 
v___x_1960_ = l_Lean_Syntax_getPos_x3f(v_fst_1897_, v___x_1892_);
if (lean_obj_tag(v___x_1960_) == 0)
{
v___y_1959_ = v___x_1893_;
goto v___jp_1958_;
}
else
{
lean_dec_ref_known(v___x_1960_, 1);
v___y_1959_ = v___x_1892_;
goto v___jp_1958_;
}
v___jp_1902_:
{
lean_object* v___x_1908_; 
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 1, v_snd_1858_);
lean_ctor_set(v___x_1900_, 0, v_fst_1857_);
v___x_1908_ = v___x_1900_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_fst_1857_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_snd_1858_);
v___x_1908_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
size_t v_sz_1909_; size_t v___x_1910_; lean_object* v___x_1911_; 
v_sz_1909_ = lean_array_size(v___y_1903_);
v___x_1910_ = ((size_t)0ULL);
v___x_1911_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1891_, v_fst_1897_, v_snd_1898_, v___y_1904_, v___y_1903_, v_sz_1909_, v___x_1910_, v___x_1908_);
lean_dec_ref(v___y_1903_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v_fst_1913_; lean_object* v_snd_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref_known(v___x_1911_, 1);
v_fst_1913_ = lean_ctor_get(v_a_1912_, 0);
v_snd_1914_ = lean_ctor_get(v_a_1912_, 1);
v_isSharedCheck_1921_ = !lean_is_exclusive(v_a_1912_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v_a_1912_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_snd_1914_);
lean_inc(v_fst_1913_);
lean_dec(v_a_1912_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_fst_1913_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v_snd_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
v_a_1869_ = v___x_1919_;
goto v___jp_1868_;
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_del_object(v___x_1860_);
lean_dec(v_cmd_1841_);
v_a_1922_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1911_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1911_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
}
v___jp_1931_:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; uint8_t v___x_1936_; 
lean_inc_ref(v___x_1891_);
v___x_1932_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1891_);
v___x_1933_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1866_);
v___x_1934_ = lean_array_get_size(v___x_1933_);
v___x_1935_ = lean_unsigned_to_nat(0u);
v___x_1936_ = lean_nat_dec_eq(v___x_1934_, v___x_1935_);
if (v___x_1936_ == 0)
{
v___y_1903_ = v___x_1933_;
v___y_1904_ = v___x_1932_;
v___y_1905_ = v___y_1848_;
v___y_1906_ = v___y_1849_;
goto v___jp_1902_;
}
else
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v_scopes_1942_; lean_object* v___x_1943_; lean_object* v_opts_1944_; uint8_t v_hasTrace_1945_; 
v___x_1937_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1938_ = l_Lean_inheritedTraceOptions;
v___x_1939_ = lean_st_ref_get(v___x_1938_);
v___x_1940_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1941_ = lean_st_ref_get(v___y_1849_);
v_scopes_1942_ = lean_ctor_get(v___x_1941_, 2);
lean_inc(v_scopes_1942_);
lean_dec(v___x_1941_);
v___x_1943_ = l_List_head_x21___redArg(v___x_1940_, v_scopes_1942_);
lean_dec(v_scopes_1942_);
v_opts_1944_ = lean_ctor_get(v___x_1943_, 1);
lean_inc_ref(v_opts_1944_);
lean_dec(v___x_1943_);
v_hasTrace_1945_ = lean_ctor_get_uint8(v_opts_1944_, sizeof(void*)*1);
if (v_hasTrace_1945_ == 0)
{
lean_dec_ref(v_opts_1944_);
lean_dec(v___x_1939_);
v___y_1903_ = v___x_1933_;
v___y_1904_ = v___x_1932_;
v___y_1905_ = v___y_1848_;
v___y_1906_ = v___y_1849_;
goto v___jp_1902_;
}
else
{
lean_object* v___x_1946_; uint8_t v___x_1947_; 
v___x_1946_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1947_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1939_, v_opts_1944_, v___x_1946_);
lean_dec_ref(v_opts_1944_);
lean_dec(v___x_1939_);
if (v___x_1947_ == 0)
{
v___y_1903_ = v___x_1933_;
v___y_1904_ = v___x_1932_;
v___y_1905_ = v___y_1848_;
v___y_1906_ = v___y_1849_;
goto v___jp_1902_;
}
else
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1948_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5);
v___x_1949_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1937_, v___x_1948_, v___y_1848_, v___y_1849_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_dec_ref_known(v___x_1949_, 1);
v___y_1903_ = v___x_1933_;
v___y_1904_ = v___x_1932_;
v___y_1905_ = v___y_1848_;
v___y_1906_ = v___y_1849_;
goto v___jp_1902_;
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec_ref(v___x_1933_);
lean_dec(v___x_1932_);
lean_del_object(v___x_1900_);
lean_dec(v_snd_1898_);
lean_dec(v_fst_1897_);
lean_dec_ref_known(v___x_1891_, 2);
lean_del_object(v___x_1860_);
lean_dec(v_snd_1858_);
lean_dec(v_fst_1857_);
lean_dec(v_cmd_1841_);
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1949_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1949_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
}
}
}
v___jp_1958_:
{
if (v_onUnsolved_1842_ == 0)
{
if (v___y_1843_ == 0)
{
lean_del_object(v___x_1900_);
lean_dec(v_snd_1898_);
lean_dec(v_fst_1897_);
lean_dec_ref_known(v___x_1891_, 2);
goto v___jp_1876_;
}
else
{
if (v___y_1959_ == 0)
{
lean_del_object(v___x_1900_);
lean_dec(v_snd_1898_);
lean_dec(v_fst_1897_);
lean_dec_ref_known(v___x_1891_, 2);
goto v___jp_1876_;
}
else
{
lean_del_object(v___x_1855_);
goto v___jp_1931_;
}
}
}
else
{
lean_del_object(v___x_1855_);
goto v___jp_1931_;
}
}
}
}
else
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v_scopes_1967_; lean_object* v___x_1968_; lean_object* v_opts_1969_; uint8_t v_hasTrace_1970_; 
lean_dec(v___x_1895_);
lean_dec_ref_known(v___x_1891_, 2);
lean_del_object(v___x_1855_);
v___x_1962_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1963_ = l_Lean_inheritedTraceOptions;
v___x_1964_ = lean_st_ref_get(v___x_1963_);
v___x_1965_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1966_ = lean_st_ref_get(v___y_1849_);
v_scopes_1967_ = lean_ctor_get(v___x_1966_, 2);
lean_inc(v_scopes_1967_);
lean_dec(v___x_1966_);
v___x_1968_ = l_List_head_x21___redArg(v___x_1965_, v_scopes_1967_);
lean_dec(v_scopes_1967_);
v_opts_1969_ = lean_ctor_get(v___x_1968_, 1);
lean_inc_ref(v_opts_1969_);
lean_dec(v___x_1968_);
v_hasTrace_1970_ = lean_ctor_get_uint8(v_opts_1969_, sizeof(void*)*1);
if (v_hasTrace_1970_ == 0)
{
lean_dec_ref(v_opts_1969_);
lean_dec(v___x_1964_);
lean_dec(v___x_1890_);
lean_dec(v___x_1889_);
lean_del_object(v___x_1887_);
goto v___jp_1880_;
}
else
{
lean_object* v___x_1971_; uint8_t v___x_1972_; 
v___x_1971_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1972_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1964_, v_opts_1969_, v___x_1971_);
lean_dec_ref(v_opts_1969_);
lean_dec(v___x_1964_);
if (v___x_1972_ == 0)
{
lean_dec(v___x_1890_);
lean_dec(v___x_1889_);
lean_del_object(v___x_1887_);
goto v___jp_1880_;
}
else
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1976_; 
v___x_1973_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7);
v___x_1974_ = l_Nat_reprFast(v___x_1889_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set_tag(v___x_1887_, 3);
lean_ctor_set(v___x_1887_, 0, v___x_1974_);
v___x_1976_ = v___x_1887_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1974_);
v___x_1976_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1977_ = l_Lean_MessageData_ofFormat(v___x_1976_);
v___x_1978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1973_);
lean_ctor_set(v___x_1978_, 1, v___x_1977_);
v___x_1979_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9);
v___x_1980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1978_);
lean_ctor_set(v___x_1980_, 1, v___x_1979_);
v___x_1981_ = l_Nat_reprFast(v___x_1890_);
v___x_1982_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
v___x_1983_ = l_Lean_MessageData_ofFormat(v___x_1982_);
v___x_1984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1980_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
v___x_1985_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11);
v___x_1986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1984_);
lean_ctor_set(v___x_1986_, 1, v___x_1985_);
v___x_1987_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1962_, v___x_1986_, v___y_1848_, v___y_1849_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_dec_ref_known(v___x_1987_, 1);
goto v___jp_1880_;
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_del_object(v___x_1860_);
lean_dec(v_snd_1858_);
lean_dec(v_fst_1857_);
lean_dec(v_cmd_1841_);
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1987_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1987_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
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
lean_object* v___x_1998_; 
lean_dec(v_endPos_1864_);
lean_del_object(v___x_1855_);
v___x_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1998_, 0, v_fst_1857_);
lean_ctor_set(v___x_1998_, 1, v_snd_1858_);
v_a_1869_ = v___x_1998_;
goto v___jp_1868_;
}
}
}
else
{
lean_object* v___x_1999_; 
lean_dec(v_endPos_1864_);
lean_del_object(v___x_1855_);
v___x_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1999_, 0, v_fst_1857_);
lean_ctor_set(v___x_1999_, 1, v_snd_1858_);
v_a_1869_ = v___x_1999_;
goto v___jp_1868_;
}
v___jp_1868_:
{
lean_object* v___x_1871_; 
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 1, v_a_1869_);
lean_ctor_set(v___x_1860_, 0, v___x_1867_);
v___x_1871_ = v___x_1860_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1867_);
lean_ctor_set(v_reuseFailAlloc_1875_, 1, v_a_1869_);
v___x_1871_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
size_t v___x_1872_; size_t v___x_1873_; lean_object* v___x_1874_; 
v___x_1872_ = ((size_t)1ULL);
v___x_1873_ = lean_usize_add(v_i_1846_, v___x_1872_);
v___x_1874_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10_spec__12(v___x_1839_, v_val_1840_, v_cmd_1841_, v_onUnsolved_1842_, v___y_1843_, v_as_1844_, v_sz_1845_, v___x_1873_, v___x_1871_, v___y_1848_, v___y_1849_);
return v___x_1874_;
}
}
v___jp_1876_:
{
lean_object* v___x_1878_; 
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 1, v_snd_1858_);
lean_ctor_set(v___x_1855_, 0, v_fst_1857_);
v___x_1878_ = v___x_1855_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_fst_1857_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v_snd_1858_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
v_a_1869_ = v___x_1878_;
goto v___jp_1868_;
}
}
v___jp_1880_:
{
lean_object* v___x_1881_; 
v___x_1881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1881_, 0, v_fst_1857_);
lean_ctor_set(v___x_1881_, 1, v_snd_1858_);
v_a_1869_ = v___x_1881_;
goto v___jp_1868_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10___boxed(lean_object* v___x_2003_, lean_object* v_val_2004_, lean_object* v_cmd_2005_, lean_object* v_onUnsolved_2006_, lean_object* v___y_2007_, lean_object* v_as_2008_, lean_object* v_sz_2009_, lean_object* v_i_2010_, lean_object* v_b_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
uint8_t v_onUnsolved_boxed_2015_; uint8_t v___y_12952__boxed_2016_; size_t v_sz_boxed_2017_; size_t v_i_boxed_2018_; lean_object* v_res_2019_; 
v_onUnsolved_boxed_2015_ = lean_unbox(v_onUnsolved_2006_);
v___y_12952__boxed_2016_ = lean_unbox(v___y_2007_);
v_sz_boxed_2017_ = lean_unbox_usize(v_sz_2009_);
lean_dec(v_sz_2009_);
v_i_boxed_2018_ = lean_unbox_usize(v_i_2010_);
lean_dec(v_i_2010_);
v_res_2019_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10(v___x_2003_, v_val_2004_, v_cmd_2005_, v_onUnsolved_boxed_2015_, v___y_12952__boxed_2016_, v_as_2008_, v_sz_boxed_2017_, v_i_boxed_2018_, v_b_2011_, v___y_2012_, v___y_2013_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec_ref(v_as_2008_);
lean_dec_ref(v_val_2004_);
lean_dec_ref(v___x_2003_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(lean_object* v_init_2020_, lean_object* v___x_2021_, lean_object* v_val_2022_, lean_object* v_cmd_2023_, uint8_t v_onUnsolved_2024_, uint8_t v___y_2025_, lean_object* v_n_2026_, lean_object* v_b_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
if (lean_obj_tag(v_n_2026_) == 0)
{
lean_object* v_cs_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; size_t v_sz_2034_; size_t v___x_2035_; lean_object* v___x_2036_; 
v_cs_2031_ = lean_ctor_get(v_n_2026_, 0);
v___x_2032_ = lean_box(0);
v___x_2033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2032_);
lean_ctor_set(v___x_2033_, 1, v_b_2027_);
v_sz_2034_ = lean_array_size(v_cs_2031_);
v___x_2035_ = ((size_t)0ULL);
v___x_2036_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__9(v_init_2020_, v___x_2021_, v_val_2022_, v_cmd_2023_, v_onUnsolved_2024_, v___y_2025_, v_cs_2031_, v_sz_2034_, v___x_2035_, v___x_2033_, v___y_2028_, v___y_2029_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2051_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2039_ = v___x_2036_;
v_isShared_2040_ = v_isSharedCheck_2051_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2036_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2051_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v_fst_2041_; 
v_fst_2041_ = lean_ctor_get(v_a_2037_, 0);
if (lean_obj_tag(v_fst_2041_) == 0)
{
lean_object* v_snd_2042_; lean_object* v___x_2043_; lean_object* v___x_2045_; 
v_snd_2042_ = lean_ctor_get(v_a_2037_, 1);
lean_inc(v_snd_2042_);
lean_dec(v_a_2037_);
v___x_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2043_, 0, v_snd_2042_);
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v___x_2043_);
v___x_2045_ = v___x_2039_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2043_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
else
{
lean_object* v_val_2047_; lean_object* v___x_2049_; 
lean_inc_ref(v_fst_2041_);
lean_dec(v_a_2037_);
v_val_2047_ = lean_ctor_get(v_fst_2041_, 0);
lean_inc(v_val_2047_);
lean_dec_ref_known(v_fst_2041_, 1);
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v_val_2047_);
v___x_2049_ = v___x_2039_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_val_2047_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
v_a_2052_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2036_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2036_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
else
{
lean_object* v_vs_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; size_t v_sz_2063_; size_t v___x_2064_; lean_object* v___x_2065_; 
v_vs_2060_ = lean_ctor_get(v_n_2026_, 0);
v___x_2061_ = lean_box(0);
v___x_2062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
lean_ctor_set(v___x_2062_, 1, v_b_2027_);
v_sz_2063_ = lean_array_size(v_vs_2060_);
v___x_2064_ = ((size_t)0ULL);
v___x_2065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10(v___x_2021_, v_val_2022_, v_cmd_2023_, v_onUnsolved_2024_, v___y_2025_, v_vs_2060_, v_sz_2063_, v___x_2064_, v___x_2062_, v___y_2028_, v___y_2029_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2080_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2068_ = v___x_2065_;
v_isShared_2069_ = v_isSharedCheck_2080_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2065_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2080_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v_fst_2070_; 
v_fst_2070_ = lean_ctor_get(v_a_2066_, 0);
if (lean_obj_tag(v_fst_2070_) == 0)
{
lean_object* v_snd_2071_; lean_object* v___x_2072_; lean_object* v___x_2074_; 
v_snd_2071_ = lean_ctor_get(v_a_2066_, 1);
lean_inc(v_snd_2071_);
lean_dec(v_a_2066_);
v___x_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2072_, 0, v_snd_2071_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 0, v___x_2072_);
v___x_2074_ = v___x_2068_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2072_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
else
{
lean_object* v_val_2076_; lean_object* v___x_2078_; 
lean_inc_ref(v_fst_2070_);
lean_dec(v_a_2066_);
v_val_2076_ = lean_ctor_get(v_fst_2070_, 0);
lean_inc(v_val_2076_);
lean_dec_ref_known(v_fst_2070_, 1);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 0, v_val_2076_);
v___x_2078_ = v___x_2068_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_val_2076_);
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
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
v_a_2081_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2065_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2065_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__9(lean_object* v_init_2089_, lean_object* v___x_2090_, lean_object* v_val_2091_, lean_object* v_cmd_2092_, uint8_t v_onUnsolved_2093_, uint8_t v___y_2094_, lean_object* v_as_2095_, size_t v_sz_2096_, size_t v_i_2097_, lean_object* v_b_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
uint8_t v___x_2102_; 
v___x_2102_ = lean_usize_dec_lt(v_i_2097_, v_sz_2096_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2103_; 
lean_dec(v_cmd_2092_);
v___x_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2103_, 0, v_b_2098_);
return v___x_2103_;
}
else
{
lean_object* v_snd_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2138_; 
v_snd_2104_ = lean_ctor_get(v_b_2098_, 1);
v_isSharedCheck_2138_ = !lean_is_exclusive(v_b_2098_);
if (v_isSharedCheck_2138_ == 0)
{
lean_object* v_unused_2139_; 
v_unused_2139_ = lean_ctor_get(v_b_2098_, 0);
lean_dec(v_unused_2139_);
v___x_2106_ = v_b_2098_;
v_isShared_2107_ = v_isSharedCheck_2138_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_snd_2104_);
lean_dec(v_b_2098_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2138_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2108_; lean_object* v_a_2109_; lean_object* v___x_2110_; 
v___x_2108_ = lean_box(0);
v_a_2109_ = lean_array_uget_borrowed(v_as_2095_, v_i_2097_);
lean_inc(v_snd_2104_);
lean_inc(v_cmd_2092_);
v___x_2110_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(v_init_2089_, v___x_2090_, v_val_2091_, v_cmd_2092_, v_onUnsolved_2093_, v___y_2094_, v_a_2109_, v_snd_2104_, v___y_2099_, v___y_2100_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2129_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2113_ = v___x_2110_;
v_isShared_2114_ = v_isSharedCheck_2129_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2110_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2129_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
if (lean_obj_tag(v_a_2111_) == 0)
{
lean_object* v___x_2115_; lean_object* v___x_2117_; 
lean_dec(v_cmd_2092_);
v___x_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2115_, 0, v_a_2111_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 0, v___x_2115_);
v___x_2117_ = v___x_2106_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2115_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v_snd_2104_);
v___x_2117_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
lean_object* v___x_2119_; 
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v___x_2117_);
v___x_2119_ = v___x_2113_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2117_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; 
lean_del_object(v___x_2113_);
lean_dec(v_snd_2104_);
v_a_2122_ = lean_ctor_get(v_a_2111_, 0);
lean_inc(v_a_2122_);
lean_dec_ref_known(v_a_2111_, 1);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 1, v_a_2122_);
lean_ctor_set(v___x_2106_, 0, v___x_2108_);
v___x_2124_ = v___x_2106_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2108_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v_a_2122_);
v___x_2124_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
size_t v___x_2125_; size_t v___x_2126_; 
v___x_2125_ = ((size_t)1ULL);
v___x_2126_ = lean_usize_add(v_i_2097_, v___x_2125_);
v_i_2097_ = v___x_2126_;
v_b_2098_ = v___x_2124_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_del_object(v___x_2106_);
lean_dec(v_snd_2104_);
lean_dec(v_cmd_2092_);
v_a_2130_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2110_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2110_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__9___boxed(lean_object* v_init_2140_, lean_object* v___x_2141_, lean_object* v_val_2142_, lean_object* v_cmd_2143_, lean_object* v_onUnsolved_2144_, lean_object* v___y_2145_, lean_object* v_as_2146_, lean_object* v_sz_2147_, lean_object* v_i_2148_, lean_object* v_b_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
uint8_t v_onUnsolved_boxed_2153_; uint8_t v___y_13253__boxed_2154_; size_t v_sz_boxed_2155_; size_t v_i_boxed_2156_; lean_object* v_res_2157_; 
v_onUnsolved_boxed_2153_ = lean_unbox(v_onUnsolved_2144_);
v___y_13253__boxed_2154_ = lean_unbox(v___y_2145_);
v_sz_boxed_2155_ = lean_unbox_usize(v_sz_2147_);
lean_dec(v_sz_2147_);
v_i_boxed_2156_ = lean_unbox_usize(v_i_2148_);
lean_dec(v_i_2148_);
v_res_2157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__9(v_init_2140_, v___x_2141_, v_val_2142_, v_cmd_2143_, v_onUnsolved_boxed_2153_, v___y_13253__boxed_2154_, v_as_2146_, v_sz_boxed_2155_, v_i_boxed_2156_, v_b_2149_, v___y_2150_, v___y_2151_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec_ref(v_as_2146_);
lean_dec_ref(v_val_2142_);
lean_dec_ref(v___x_2141_);
lean_dec_ref(v_init_2140_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___boxed(lean_object* v_init_2158_, lean_object* v___x_2159_, lean_object* v_val_2160_, lean_object* v_cmd_2161_, lean_object* v_onUnsolved_2162_, lean_object* v___y_2163_, lean_object* v_n_2164_, lean_object* v_b_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
uint8_t v_onUnsolved_boxed_2169_; uint8_t v___y_13275__boxed_2170_; lean_object* v_res_2171_; 
v_onUnsolved_boxed_2169_ = lean_unbox(v_onUnsolved_2162_);
v___y_13275__boxed_2170_ = lean_unbox(v___y_2163_);
v_res_2171_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(v_init_2158_, v___x_2159_, v_val_2160_, v_cmd_2161_, v_onUnsolved_boxed_2169_, v___y_13275__boxed_2170_, v_n_2164_, v_b_2165_, v___y_2166_, v___y_2167_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec_ref(v_n_2164_);
lean_dec_ref(v_val_2160_);
lean_dec_ref(v___x_2159_);
lean_dec_ref(v_init_2158_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(lean_object* v___x_2172_, lean_object* v_val_2173_, lean_object* v_cmd_2174_, uint8_t v_onUnsolved_2175_, uint8_t v___y_2176_, lean_object* v_t_2177_, lean_object* v_init_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v_root_2182_; lean_object* v_tail_2183_; lean_object* v___x_2184_; 
v_root_2182_ = lean_ctor_get(v_t_2177_, 0);
v_tail_2183_ = lean_ctor_get(v_t_2177_, 1);
lean_inc(v_cmd_2174_);
lean_inc_ref(v_init_2178_);
v___x_2184_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(v_init_2178_, v___x_2172_, v_val_2173_, v_cmd_2174_, v_onUnsolved_2175_, v___y_2176_, v_root_2182_, v_init_2178_, v___y_2179_, v___y_2180_);
lean_dec_ref(v_init_2178_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2221_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2187_ = v___x_2184_;
v_isShared_2188_ = v_isSharedCheck_2221_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2184_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2221_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
if (lean_obj_tag(v_a_2185_) == 0)
{
lean_object* v_a_2189_; lean_object* v___x_2191_; 
lean_dec(v_cmd_2174_);
v_a_2189_ = lean_ctor_get(v_a_2185_, 0);
lean_inc(v_a_2189_);
lean_dec_ref_known(v_a_2185_, 1);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 0, v_a_2189_);
v___x_2191_ = v___x_2187_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2189_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; size_t v_sz_2196_; size_t v___x_2197_; lean_object* v___x_2198_; 
lean_del_object(v___x_2187_);
v_a_2193_ = lean_ctor_get(v_a_2185_, 0);
lean_inc(v_a_2193_);
lean_dec_ref_known(v_a_2185_, 1);
v___x_2194_ = lean_box(0);
v___x_2195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
lean_ctor_set(v___x_2195_, 1, v_a_2193_);
v_sz_2196_ = lean_array_size(v_tail_2183_);
v___x_2197_ = ((size_t)0ULL);
v___x_2198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8(v___x_2172_, v_val_2173_, v_cmd_2174_, v_onUnsolved_2175_, v___y_2176_, v_tail_2183_, v_sz_2196_, v___x_2197_, v___x_2195_, v___y_2179_, v___y_2180_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2212_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2201_ = v___x_2198_;
v_isShared_2202_ = v_isSharedCheck_2212_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2198_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2212_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v_fst_2203_; 
v_fst_2203_ = lean_ctor_get(v_a_2199_, 0);
if (lean_obj_tag(v_fst_2203_) == 0)
{
lean_object* v_snd_2204_; lean_object* v___x_2206_; 
v_snd_2204_ = lean_ctor_get(v_a_2199_, 1);
lean_inc(v_snd_2204_);
lean_dec(v_a_2199_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 0, v_snd_2204_);
v___x_2206_ = v___x_2201_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_snd_2204_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
else
{
lean_object* v_val_2208_; lean_object* v___x_2210_; 
lean_inc_ref(v_fst_2203_);
lean_dec(v_a_2199_);
v_val_2208_ = lean_ctor_get(v_fst_2203_, 0);
lean_inc(v_val_2208_);
lean_dec_ref_known(v_fst_2203_, 1);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 0, v_val_2208_);
v___x_2210_ = v___x_2201_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_val_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
v_a_2213_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2198_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2198_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
}
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_dec(v_cmd_2174_);
v_a_2222_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2184_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2184_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___boxed(lean_object* v___x_2230_, lean_object* v_val_2231_, lean_object* v_cmd_2232_, lean_object* v_onUnsolved_2233_, lean_object* v___y_2234_, lean_object* v_t_2235_, lean_object* v_init_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
uint8_t v_onUnsolved_boxed_2240_; uint8_t v___y_13466__boxed_2241_; lean_object* v_res_2242_; 
v_onUnsolved_boxed_2240_ = lean_unbox(v_onUnsolved_2233_);
v___y_13466__boxed_2241_ = lean_unbox(v___y_2234_);
v_res_2242_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_2230_, v_val_2231_, v_cmd_2232_, v_onUnsolved_boxed_2240_, v___y_13466__boxed_2241_, v_t_2235_, v_init_2236_, v___y_2237_, v___y_2238_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec_ref(v_t_2235_);
lean_dec_ref(v_val_2231_);
lean_dec_ref(v___x_2230_);
return v_res_2242_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0(void){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2243_ = lean_box(0);
v___x_2244_ = lean_unsigned_to_nat(16u);
v___x_2245_ = lean_mk_array(v___x_2244_, v___x_2243_);
return v___x_2245_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1(void){
_start:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2246_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0);
v___x_2247_ = lean_unsigned_to_nat(0u);
v___x_2248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
lean_ctor_set(v___x_2248_, 1, v___x_2246_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(lean_object* v_cmd_2252_, lean_object* v_opts_2253_, lean_object* v_tree_2254_, lean_object* v_msgs_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_){
_start:
{
uint8_t v___y_2260_; lean_object* v___y_2261_; uint8_t v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; uint8_t v___y_2265_; uint8_t v___y_2291_; uint8_t v___y_2292_; lean_object* v_acc_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___f_2297_; uint8_t v___y_2299_; lean_object* v___x_2306_; uint8_t v___x_2307_; 
v___f_2297_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__2));
v___x_2306_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_2307_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2253_, v___x_2306_);
if (v___x_2307_ == 0)
{
lean_object* v___x_2308_; uint8_t v___x_2309_; 
v___x_2308_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_2309_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2253_, v___x_2308_);
v___y_2299_ = v___x_2309_;
goto v___jp_2298_;
}
else
{
v___y_2299_ = v___x_2307_;
goto v___jp_2298_;
}
v___jp_2259_:
{
lean_object* v___x_2266_; 
v___x_2266_ = l_Lean_Syntax_getRange_x3f(v_cmd_2252_, v___y_2265_);
if (lean_obj_tag(v___x_2266_) == 1)
{
lean_object* v_val_2267_; lean_object* v_fileMap_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v_val_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_val_2267_);
lean_dec_ref_known(v___x_2266_, 1);
v_fileMap_2268_ = lean_ctor_get(v___y_2264_, 1);
v___x_2269_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1);
v___x_2270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___y_2261_);
lean_ctor_set(v___x_2270_, 1, v___x_2269_);
v___x_2271_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v_fileMap_2268_, v_val_2267_, v_cmd_2252_, v___y_2262_, v___y_2260_, v_msgs_2255_, v___x_2270_, v___y_2264_, v___y_2263_);
lean_dec(v_val_2267_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2280_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2274_ = v___x_2271_;
v_isShared_2275_ = v_isSharedCheck_2280_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2271_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2280_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v_fst_2276_; lean_object* v___x_2278_; 
v_fst_2276_ = lean_ctor_get(v_a_2272_, 0);
lean_inc(v_fst_2276_);
lean_dec(v_a_2272_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 0, v_fst_2276_);
v___x_2278_ = v___x_2274_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_fst_2276_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
v_a_2281_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2271_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2271_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
else
{
lean_object* v___x_2289_; 
lean_dec(v___x_2266_);
lean_dec(v_cmd_2252_);
v___x_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2289_, 0, v___y_2261_);
return v___x_2289_;
}
}
v___jp_2290_:
{
if (v___y_2292_ == 0)
{
if (v___y_2291_ == 0)
{
lean_object* v___x_2296_; 
lean_dec(v_cmd_2252_);
v___x_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2296_, 0, v_acc_2293_);
return v___x_2296_;
}
else
{
v___y_2260_ = v___y_2291_;
v___y_2261_ = v_acc_2293_;
v___y_2262_ = v___y_2292_;
v___y_2263_ = v___y_2295_;
v___y_2264_ = v___y_2294_;
v___y_2265_ = v___y_2291_;
goto v___jp_2259_;
}
}
else
{
v___y_2260_ = v___y_2291_;
v___y_2261_ = v_acc_2293_;
v___y_2262_ = v___y_2292_;
v___y_2263_ = v___y_2295_;
v___y_2264_ = v___y_2294_;
v___y_2265_ = v___y_2292_;
goto v___jp_2259_;
}
}
v___jp_2298_:
{
lean_object* v___x_2300_; uint8_t v_onUnsolved_2301_; lean_object* v___x_2302_; uint8_t v_onSorry_2303_; lean_object* v_acc_2304_; 
v___x_2300_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
v_onUnsolved_2301_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2253_, v___x_2300_);
v___x_2302_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v_onSorry_2303_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2253_, v___x_2302_);
v_acc_2304_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__3));
if (v_onSorry_2303_ == 0)
{
lean_dec_ref(v_tree_2254_);
v___y_2291_ = v___y_2299_;
v___y_2292_ = v_onUnsolved_2301_;
v_acc_2293_ = v_acc_2304_;
v___y_2294_ = v_a_2256_;
v___y_2295_ = v_a_2257_;
goto v___jp_2290_;
}
else
{
lean_object* v_acc_2305_; 
v_acc_2305_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_2297_, v_acc_2304_, v_tree_2254_);
v___y_2291_ = v___y_2299_;
v___y_2292_ = v_onUnsolved_2301_;
v_acc_2293_ = v_acc_2305_;
v___y_2294_ = v_a_2256_;
v___y_2295_ = v_a_2257_;
goto v___jp_2290_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___boxed(lean_object* v_cmd_2310_, lean_object* v_opts_2311_, lean_object* v_tree_2312_, lean_object* v_msgs_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_cmd_2310_, v_opts_2311_, v_tree_2312_, v_msgs_2313_, v_a_2314_, v_a_2315_);
lean_dec(v_a_2315_);
lean_dec_ref(v_a_2314_);
lean_dec_ref(v_msgs_2313_);
lean_dec_ref(v_opts_2311_);
return v_res_2317_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(lean_object* v_00_u03b2_2318_, lean_object* v_m_2319_, lean_object* v_a_2320_){
_start:
{
uint8_t v___x_2321_; 
v___x_2321_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(v_m_2319_, v_a_2320_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___boxed(lean_object* v_00_u03b2_2322_, lean_object* v_m_2323_, lean_object* v_a_2324_){
_start:
{
uint8_t v_res_2325_; lean_object* v_r_2326_; 
v_res_2325_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_00_u03b2_2322_, v_m_2323_, v_a_2324_);
lean_dec_ref(v_a_2324_);
lean_dec_ref(v_m_2323_);
v_r_2326_ = lean_box(v_res_2325_);
return v_r_2326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1(lean_object* v_00_u03b2_2327_, lean_object* v_m_2328_, lean_object* v_a_2329_, lean_object* v_b_2330_){
_start:
{
lean_object* v___x_2331_; 
v___x_2331_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_m_2328_, v_a_2329_, v_b_2330_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2(lean_object* v___x_2332_, lean_object* v_fst_2333_, lean_object* v_snd_2334_, lean_object* v___x_2335_, lean_object* v_as_2336_, size_t v_sz_2337_, size_t v_i_2338_, lean_object* v_b_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v___x_2343_; 
v___x_2343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_2332_, v_fst_2333_, v_snd_2334_, v___x_2335_, v_as_2336_, v_sz_2337_, v_i_2338_, v_b_2339_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___boxed(lean_object* v___x_2344_, lean_object* v_fst_2345_, lean_object* v_snd_2346_, lean_object* v___x_2347_, lean_object* v_as_2348_, lean_object* v_sz_2349_, lean_object* v_i_2350_, lean_object* v_b_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
size_t v_sz_boxed_2355_; size_t v_i_boxed_2356_; lean_object* v_res_2357_; 
v_sz_boxed_2355_ = lean_unbox_usize(v_sz_2349_);
lean_dec(v_sz_2349_);
v_i_boxed_2356_ = lean_unbox_usize(v_i_2350_);
lean_dec(v_i_2350_);
v_res_2357_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2(v___x_2344_, v_fst_2345_, v_snd_2346_, v___x_2347_, v_as_2348_, v_sz_boxed_2355_, v_i_boxed_2356_, v_b_2351_, v___y_2352_, v___y_2353_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec_ref(v_as_2348_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5(lean_object* v_msgData_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(v_msgData_2358_, v___y_2360_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___boxed(lean_object* v_msgData_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5(v_msgData_2363_, v___y_2364_, v___y_2365_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
return v_res_2367_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0(lean_object* v_00_u03b2_2368_, lean_object* v_a_2369_, lean_object* v_x_2370_){
_start:
{
uint8_t v___x_2371_; 
v___x_2371_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(v_a_2369_, v_x_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2372_, lean_object* v_a_2373_, lean_object* v_x_2374_){
_start:
{
uint8_t v_res_2375_; lean_object* v_r_2376_; 
v_res_2375_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0(v_00_u03b2_2372_, v_a_2373_, v_x_2374_);
lean_dec(v_x_2374_);
lean_dec_ref(v_a_2373_);
v_r_2376_ = lean_box(v_res_2375_);
return v_r_2376_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2(lean_object* v_00_u03b2_2377_, lean_object* v_data_2378_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2___redArg(v_data_2378_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2380_, lean_object* v_i_2381_, lean_object* v_source_2382_, lean_object* v_target_2383_){
_start:
{
lean_object* v___x_2384_; 
v___x_2384_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3___redArg(v_i_2381_, v_source_2382_, v_target_2383_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3_spec__8(lean_object* v_00_u03b2_2385_, lean_object* v_x_2386_, lean_object* v_x_2387_){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3_spec__8___redArg(v_x_2386_, v_x_2387_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(lean_object* v_x_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v___x_2397_; 
lean_inc(v___y_2391_);
lean_inc_ref(v___y_2390_);
v___x_2397_ = lean_apply_7(v_x_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, lean_box(0));
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed(lean_object* v_x_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(v_x_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(lean_object* v_mvarId_2407_, lean_object* v_x_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v___f_2416_; lean_object* v___x_2417_; 
lean_inc(v___y_2410_);
lean_inc_ref(v___y_2409_);
v___f_2416_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2416_, 0, v_x_2408_);
lean_closure_set(v___f_2416_, 1, v___y_2409_);
lean_closure_set(v___f_2416_, 2, v___y_2410_);
v___x_2417_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2407_, v___f_2416_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
if (lean_obj_tag(v___x_2417_) == 0)
{
return v___x_2417_;
}
else
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2425_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2420_ = v___x_2417_;
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2417_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2423_; 
if (v_isShared_2421_ == 0)
{
v___x_2423_ = v___x_2420_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2418_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___boxed(lean_object* v_mvarId_2426_, lean_object* v_x_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2426_, v_x_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(lean_object* v_00_u03b1_2436_, lean_object* v_mvarId_2437_, lean_object* v_x_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2437_, v_x_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed(lean_object* v_00_u03b1_2447_, lean_object* v_mvarId_2448_, lean_object* v_x_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(v_00_u03b1_2447_, v_mvarId_2448_, v_x_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(lean_object* v_____r_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_){
_start:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2472_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2472_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___boxed(lean_object* v_____r_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(v_____r_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(lean_object* v_____r_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2491_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2491_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1___boxed(lean_object* v_____r_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(v_____r_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
return v_res_2499_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(uint8_t v___x_2500_, lean_object* v_x_2501_){
_start:
{
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2___boxed(lean_object* v___x_2502_, lean_object* v_x_2503_){
_start:
{
uint8_t v___x_10980__boxed_2504_; uint8_t v_res_2505_; lean_object* v_r_2506_; 
v___x_10980__boxed_2504_ = lean_unbox(v___x_2502_);
v_res_2505_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(v___x_10980__boxed_2504_, v_x_2503_);
lean_dec(v_x_2503_);
v_r_2506_ = lean_box(v_res_2505_);
return v_r_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(lean_object* v_msgData_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v___x_2513_; lean_object* v_env_2514_; lean_object* v___x_2515_; lean_object* v_toCold_2516_; lean_object* v_mctx_2517_; lean_object* v_lctx_2518_; lean_object* v_options_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2513_ = lean_st_ref_get(v___y_2511_);
v_env_2514_ = lean_ctor_get(v___x_2513_, 0);
lean_inc_ref(v_env_2514_);
lean_dec(v___x_2513_);
v___x_2515_ = lean_st_ref_get(v___y_2509_);
v_toCold_2516_ = lean_ctor_get(v___y_2510_, 0);
v_mctx_2517_ = lean_ctor_get(v___x_2515_, 0);
lean_inc_ref(v_mctx_2517_);
lean_dec(v___x_2515_);
v_lctx_2518_ = lean_ctor_get(v___y_2508_, 2);
v_options_2519_ = lean_ctor_get(v_toCold_2516_, 2);
lean_inc_ref(v_options_2519_);
lean_inc_ref(v_lctx_2518_);
v___x_2520_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2520_, 0, v_env_2514_);
lean_ctor_set(v___x_2520_, 1, v_mctx_2517_);
lean_ctor_set(v___x_2520_, 2, v_lctx_2518_);
lean_ctor_set(v___x_2520_, 3, v_options_2519_);
v___x_2521_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
lean_ctor_set(v___x_2521_, 1, v_msgData_2507_);
v___x_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2___boxed(lean_object* v_msgData_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msgData_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(lean_object* v_cls_2530_, lean_object* v_msg_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v_ref_2537_; lean_object* v___x_2538_; lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2583_; 
v_ref_2537_ = lean_ctor_get(v___y_2534_, 2);
v___x_2538_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2541_ = v___x_2538_;
v_isShared_2542_ = v_isSharedCheck_2583_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2538_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2583_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2543_; lean_object* v_traceState_2544_; lean_object* v_env_2545_; lean_object* v_nextMacroScope_2546_; lean_object* v_ngen_2547_; lean_object* v_auxDeclNGen_2548_; lean_object* v_cache_2549_; lean_object* v_messages_2550_; lean_object* v_infoState_2551_; lean_object* v_snapshotTasks_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2582_; 
v___x_2543_ = lean_st_ref_take(v___y_2535_);
v_traceState_2544_ = lean_ctor_get(v___x_2543_, 4);
v_env_2545_ = lean_ctor_get(v___x_2543_, 0);
v_nextMacroScope_2546_ = lean_ctor_get(v___x_2543_, 1);
v_ngen_2547_ = lean_ctor_get(v___x_2543_, 2);
v_auxDeclNGen_2548_ = lean_ctor_get(v___x_2543_, 3);
v_cache_2549_ = lean_ctor_get(v___x_2543_, 5);
v_messages_2550_ = lean_ctor_get(v___x_2543_, 6);
v_infoState_2551_ = lean_ctor_get(v___x_2543_, 7);
v_snapshotTasks_2552_ = lean_ctor_get(v___x_2543_, 8);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2554_ = v___x_2543_;
v_isShared_2555_ = v_isSharedCheck_2582_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_snapshotTasks_2552_);
lean_inc(v_infoState_2551_);
lean_inc(v_messages_2550_);
lean_inc(v_cache_2549_);
lean_inc(v_traceState_2544_);
lean_inc(v_auxDeclNGen_2548_);
lean_inc(v_ngen_2547_);
lean_inc(v_nextMacroScope_2546_);
lean_inc(v_env_2545_);
lean_dec(v___x_2543_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2582_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
uint64_t v_tid_2556_; lean_object* v_traces_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2581_; 
v_tid_2556_ = lean_ctor_get_uint64(v_traceState_2544_, sizeof(void*)*1);
v_traces_2557_ = lean_ctor_get(v_traceState_2544_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v_traceState_2544_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2559_ = v_traceState_2544_;
v_isShared_2560_ = v_isSharedCheck_2581_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_traces_2557_);
lean_dec(v_traceState_2544_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2581_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; double v___x_2563_; uint8_t v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2572_; 
v___x_2561_ = lean_box(0);
v___x_2562_ = lean_box(0);
v___x_2563_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0);
v___x_2564_ = 0;
v___x_2565_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2566_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2566_, 0, v_cls_2530_);
lean_ctor_set(v___x_2566_, 1, v___x_2562_);
lean_ctor_set(v___x_2566_, 2, v___x_2565_);
lean_ctor_set_float(v___x_2566_, sizeof(void*)*3, v___x_2563_);
lean_ctor_set_float(v___x_2566_, sizeof(void*)*3 + 8, v___x_2563_);
lean_ctor_set_uint8(v___x_2566_, sizeof(void*)*3 + 16, v___x_2564_);
v___x_2567_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__1));
v___x_2568_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2566_);
lean_ctor_set(v___x_2568_, 1, v_a_2539_);
lean_ctor_set(v___x_2568_, 2, v___x_2567_);
lean_inc(v_ref_2537_);
v___x_2569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2569_, 0, v_ref_2537_);
lean_ctor_set(v___x_2569_, 1, v___x_2568_);
v___x_2570_ = l_Lean_PersistentArray_push___redArg(v_traces_2557_, v___x_2569_);
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v___x_2570_);
v___x_2572_ = v___x_2559_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2570_);
lean_ctor_set_uint64(v_reuseFailAlloc_2580_, sizeof(void*)*1, v_tid_2556_);
v___x_2572_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
lean_object* v___x_2574_; 
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 4, v___x_2572_);
v___x_2574_ = v___x_2554_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_env_2545_);
lean_ctor_set(v_reuseFailAlloc_2579_, 1, v_nextMacroScope_2546_);
lean_ctor_set(v_reuseFailAlloc_2579_, 2, v_ngen_2547_);
lean_ctor_set(v_reuseFailAlloc_2579_, 3, v_auxDeclNGen_2548_);
lean_ctor_set(v_reuseFailAlloc_2579_, 4, v___x_2572_);
lean_ctor_set(v_reuseFailAlloc_2579_, 5, v_cache_2549_);
lean_ctor_set(v_reuseFailAlloc_2579_, 6, v_messages_2550_);
lean_ctor_set(v_reuseFailAlloc_2579_, 7, v_infoState_2551_);
lean_ctor_set(v_reuseFailAlloc_2579_, 8, v_snapshotTasks_2552_);
v___x_2574_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2575_ = lean_st_ref_put(v___y_2535_, v___x_2574_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 0, v___x_2561_);
v___x_2577_ = v___x_2541_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2561_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg___boxed(lean_object* v_cls_2584_, lean_object* v_msg_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_2584_, v_msg_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
return v_res_2591_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2593_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__0));
v___x_2594_ = l_Lean_stringToMessageData(v___x_2593_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(lean_object* v___x_2595_, lean_object* v___f_2596_, lean_object* v___x_2597_, lean_object* v___x_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v___x_2606_; lean_object* v_a_2608_; lean_object* v___y_2612_; lean_object* v___x_2626_; 
v___x_2606_ = lean_st_mk_ref(v___x_2595_);
v___x_2626_ = l_Lean_Elab_Tactic_saveState___redArg(v___x_2606_, v___y_2600_, v___y_2602_, v___y_2604_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; lean_object* v___x_2628_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_a_2627_);
lean_dec_ref_known(v___x_2626_, 1);
v___x_2628_ = l_Lean_Elab_Tactic_Try_collectTryCoreSuggestions(v___x_2598_, v___x_2597_, v___x_2606_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; 
lean_dec(v_a_2627_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec_ref(v___x_2597_);
lean_dec_ref(v___f_2596_);
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_a_2629_);
lean_dec_ref_known(v___x_2628_, 1);
v_a_2608_ = v_a_2629_;
goto v___jp_2607_;
}
else
{
lean_object* v_a_2630_; uint8_t v___y_2632_; uint8_t v___x_2676_; 
v_a_2630_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_a_2630_);
v___x_2676_ = l_Lean_Exception_isInterrupt(v_a_2630_);
if (v___x_2676_ == 0)
{
uint8_t v___x_2677_; 
lean_inc(v_a_2630_);
v___x_2677_ = l_Lean_Exception_isRuntime(v_a_2630_);
v___y_2632_ = v___x_2677_;
goto v___jp_2631_;
}
else
{
v___y_2632_ = v___x_2676_;
goto v___jp_2631_;
}
v___jp_2631_:
{
if (v___y_2632_ == 0)
{
lean_object* v___x_2633_; 
lean_dec_ref_known(v___x_2628_, 1);
v___x_2633_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2627_, v___y_2632_, v___x_2606_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2666_; 
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2666_ == 0)
{
lean_object* v_unused_2667_; 
v_unused_2667_ = lean_ctor_get(v___x_2633_, 0);
lean_dec(v_unused_2667_);
v___x_2635_ = v___x_2633_;
v_isShared_2636_ = v_isSharedCheck_2666_;
goto v_resetjp_2634_;
}
else
{
lean_dec(v___x_2633_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2666_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
uint8_t v___x_2637_; 
v___x_2637_ = l_Lean_Exception_isInterrupt(v_a_2630_);
if (v___x_2637_ == 0)
{
uint8_t v___x_2638_; 
lean_inc(v_a_2630_);
v___x_2638_ = l_Lean_Exception_isMaxRecDepth(v_a_2630_);
if (v___x_2638_ == 0)
{
lean_object* v_toCold_2639_; lean_object* v_options_2640_; uint8_t v_hasTrace_2641_; 
lean_del_object(v___x_2635_);
v_toCold_2639_ = lean_ctor_get(v___y_2603_, 0);
v_options_2640_ = lean_ctor_get(v_toCold_2639_, 2);
v_hasTrace_2641_ = lean_ctor_get_uint8(v_options_2640_, sizeof(void*)*1);
if (v_hasTrace_2641_ == 0)
{
lean_dec(v_a_2630_);
goto v___jp_2623_;
}
else
{
lean_object* v_inheritedTraceOptions_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; uint8_t v___x_2645_; 
v_inheritedTraceOptions_2642_ = lean_ctor_get(v_toCold_2639_, 11);
v___x_2643_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2644_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_2645_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2642_, v_options_2640_, v___x_2644_);
if (v___x_2645_ == 0)
{
lean_dec(v_a_2630_);
goto v___jp_2623_;
}
else
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2646_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_2647_ = l_Lean_Exception_toMessageData(v_a_2630_);
v___x_2648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2646_);
lean_ctor_set(v___x_2648_, 1, v___x_2647_);
v___x_2649_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v___x_2643_, v___x_2648_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; lean_object* v___x_2651_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2650_);
lean_dec_ref_known(v___x_2649_, 1);
lean_inc(v___x_2606_);
v___x_2651_ = lean_apply_10(v___f_2596_, v_a_2650_, v___x_2597_, v___x_2606_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, lean_box(0));
v___y_2612_ = v___x_2651_;
goto v___jp_2611_;
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
lean_dec(v___x_2606_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec_ref(v___x_2597_);
lean_dec_ref(v___f_2596_);
v_a_2652_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2649_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2649_);
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
else
{
lean_object* v___x_2661_; 
lean_dec(v___x_2606_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec_ref(v___x_2597_);
lean_dec_ref(v___f_2596_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set_tag(v___x_2635_, 1);
lean_ctor_set(v___x_2635_, 0, v_a_2630_);
v___x_2661_ = v___x_2635_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_a_2630_);
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
lean_object* v___x_2664_; 
lean_dec(v___x_2606_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec_ref(v___x_2597_);
lean_dec_ref(v___f_2596_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set_tag(v___x_2635_, 1);
lean_ctor_set(v___x_2635_, 0, v_a_2630_);
v___x_2664_ = v___x_2635_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2630_);
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
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
lean_dec(v_a_2630_);
lean_dec(v___x_2606_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec_ref(v___x_2597_);
lean_dec_ref(v___f_2596_);
v_a_2668_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2633_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2633_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
else
{
lean_dec(v_a_2630_);
lean_dec(v_a_2627_);
lean_dec(v___x_2606_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec_ref(v___x_2597_);
lean_dec_ref(v___f_2596_);
return v___x_2628_;
}
}
}
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
lean_dec(v___x_2606_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec_ref(v___x_2598_);
lean_dec_ref(v___x_2597_);
lean_dec_ref(v___f_2596_);
v_a_2678_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v___x_2626_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2626_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2678_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
v___jp_2607_:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2609_ = lean_st_ref_get(v___x_2606_);
lean_dec(v___x_2606_);
lean_dec(v___x_2609_);
v___x_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2610_, 0, v_a_2608_);
return v___x_2610_;
}
v___jp_2611_:
{
if (lean_obj_tag(v___y_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v_a_2614_; 
v_a_2613_ = lean_ctor_get(v___y_2612_, 0);
lean_inc(v_a_2613_);
lean_dec_ref_known(v___y_2612_, 1);
v_a_2614_ = lean_ctor_get(v_a_2613_, 0);
lean_inc(v_a_2614_);
lean_dec(v_a_2613_);
v_a_2608_ = v_a_2614_;
goto v___jp_2607_;
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_dec(v___x_2606_);
v_a_2615_ = lean_ctor_get(v___y_2612_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___y_2612_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___y_2612_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___y_2612_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
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
v___jp_2623_:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = lean_box(0);
lean_inc(v___x_2606_);
v___x_2625_ = lean_apply_10(v___f_2596_, v___x_2624_, v___x_2597_, v___x_2606_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, lean_box(0));
v___y_2612_ = v___x_2625_;
goto v___jp_2611_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed(lean_object* v___x_2686_, lean_object* v___f_2687_, lean_object* v___x_2688_, lean_object* v___x_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(v___x_2686_, v___f_2687_, v___x_2688_, v___x_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(lean_object* v___x_2698_, uint8_t v___x_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2698_, v___x_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed(lean_object* v___x_2708_, lean_object* v___x_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
uint8_t v___x_11309__boxed_2717_; lean_object* v_res_2718_; 
v___x_11309__boxed_2717_ = lean_unbox(v___x_2709_);
v_res_2718_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(v___x_2708_, v___x_11309__boxed_2717_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(lean_object* v_cls_2719_, lean_object* v_msg_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v_ref_2726_; lean_object* v___x_2727_; lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2772_; 
v_ref_2726_ = lean_ctor_get(v___y_2723_, 2);
v___x_2727_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2730_ = v___x_2727_;
v_isShared_2731_ = v_isSharedCheck_2772_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2727_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2772_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2732_; lean_object* v_traceState_2733_; lean_object* v_env_2734_; lean_object* v_nextMacroScope_2735_; lean_object* v_ngen_2736_; lean_object* v_auxDeclNGen_2737_; lean_object* v_cache_2738_; lean_object* v_messages_2739_; lean_object* v_infoState_2740_; lean_object* v_snapshotTasks_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2771_; 
v___x_2732_ = lean_st_ref_take(v___y_2724_);
v_traceState_2733_ = lean_ctor_get(v___x_2732_, 4);
v_env_2734_ = lean_ctor_get(v___x_2732_, 0);
v_nextMacroScope_2735_ = lean_ctor_get(v___x_2732_, 1);
v_ngen_2736_ = lean_ctor_get(v___x_2732_, 2);
v_auxDeclNGen_2737_ = lean_ctor_get(v___x_2732_, 3);
v_cache_2738_ = lean_ctor_get(v___x_2732_, 5);
v_messages_2739_ = lean_ctor_get(v___x_2732_, 6);
v_infoState_2740_ = lean_ctor_get(v___x_2732_, 7);
v_snapshotTasks_2741_ = lean_ctor_get(v___x_2732_, 8);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2743_ = v___x_2732_;
v_isShared_2744_ = v_isSharedCheck_2771_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_snapshotTasks_2741_);
lean_inc(v_infoState_2740_);
lean_inc(v_messages_2739_);
lean_inc(v_cache_2738_);
lean_inc(v_traceState_2733_);
lean_inc(v_auxDeclNGen_2737_);
lean_inc(v_ngen_2736_);
lean_inc(v_nextMacroScope_2735_);
lean_inc(v_env_2734_);
lean_dec(v___x_2732_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2771_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
uint64_t v_tid_2745_; lean_object* v_traces_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2770_; 
v_tid_2745_ = lean_ctor_get_uint64(v_traceState_2733_, sizeof(void*)*1);
v_traces_2746_ = lean_ctor_get(v_traceState_2733_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v_traceState_2733_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2748_ = v_traceState_2733_;
v_isShared_2749_ = v_isSharedCheck_2770_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_traces_2746_);
lean_dec(v_traceState_2733_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2770_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; double v___x_2752_; uint8_t v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2761_; 
v___x_2750_ = lean_box(0);
v___x_2751_ = lean_box(0);
v___x_2752_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0);
v___x_2753_ = 0;
v___x_2754_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2755_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2755_, 0, v_cls_2719_);
lean_ctor_set(v___x_2755_, 1, v___x_2751_);
lean_ctor_set(v___x_2755_, 2, v___x_2754_);
lean_ctor_set_float(v___x_2755_, sizeof(void*)*3, v___x_2752_);
lean_ctor_set_float(v___x_2755_, sizeof(void*)*3 + 8, v___x_2752_);
lean_ctor_set_uint8(v___x_2755_, sizeof(void*)*3 + 16, v___x_2753_);
v___x_2756_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__1));
v___x_2757_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2755_);
lean_ctor_set(v___x_2757_, 1, v_a_2728_);
lean_ctor_set(v___x_2757_, 2, v___x_2756_);
lean_inc(v_ref_2726_);
v___x_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2758_, 0, v_ref_2726_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
v___x_2759_ = l_Lean_PersistentArray_push___redArg(v_traces_2746_, v___x_2758_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 0, v___x_2759_);
v___x_2761_ = v___x_2748_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2759_);
lean_ctor_set_uint64(v_reuseFailAlloc_2769_, sizeof(void*)*1, v_tid_2745_);
v___x_2761_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
lean_object* v___x_2763_; 
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 4, v___x_2761_);
v___x_2763_ = v___x_2743_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_env_2734_);
lean_ctor_set(v_reuseFailAlloc_2768_, 1, v_nextMacroScope_2735_);
lean_ctor_set(v_reuseFailAlloc_2768_, 2, v_ngen_2736_);
lean_ctor_set(v_reuseFailAlloc_2768_, 3, v_auxDeclNGen_2737_);
lean_ctor_set(v_reuseFailAlloc_2768_, 4, v___x_2761_);
lean_ctor_set(v_reuseFailAlloc_2768_, 5, v_cache_2738_);
lean_ctor_set(v_reuseFailAlloc_2768_, 6, v_messages_2739_);
lean_ctor_set(v_reuseFailAlloc_2768_, 7, v_infoState_2740_);
lean_ctor_set(v_reuseFailAlloc_2768_, 8, v_snapshotTasks_2741_);
v___x_2763_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
lean_object* v___x_2764_; lean_object* v___x_2766_; 
v___x_2764_ = lean_st_ref_put(v___y_2724_, v___x_2763_);
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 0, v___x_2750_);
v___x_2766_ = v___x_2730_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v___x_2750_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3___boxed(lean_object* v_cls_2773_, lean_object* v_msg_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v_cls_2773_, v_msg_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
return v_res_2780_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2782_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__0));
v___x_2783_ = l_Lean_stringToMessageData(v___x_2782_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(lean_object* v___f_2784_, lean_object* v_term_2785_, lean_object* v___x_2786_, lean_object* v___x_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v___y_2794_; lean_object* v___x_2815_; 
v___x_2815_ = l_Lean_Elab_Term_TermElabM_run___redArg(v_term_2785_, v___x_2786_, v___x_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2824_; 
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec_ref(v___f_2784_);
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2818_ = v___x_2815_;
v_isShared_2819_ = v_isSharedCheck_2824_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2815_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2824_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v_fst_2820_; lean_object* v___x_2822_; 
v_fst_2820_ = lean_ctor_get(v_a_2816_, 0);
lean_inc(v_fst_2820_);
lean_dec(v_a_2816_);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 0, v_fst_2820_);
v___x_2822_ = v___x_2818_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_fst_2820_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2865_; 
v_a_2825_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2827_ = v___x_2815_;
v_isShared_2828_ = v_isSharedCheck_2865_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2815_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2865_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
uint8_t v___y_2830_; uint8_t v___x_2863_; 
v___x_2863_ = l_Lean_Exception_isInterrupt(v_a_2825_);
if (v___x_2863_ == 0)
{
uint8_t v___x_2864_; 
lean_inc(v_a_2825_);
v___x_2864_ = l_Lean_Exception_isRuntime(v_a_2825_);
v___y_2830_ = v___x_2864_;
goto v___jp_2829_;
}
else
{
v___y_2830_ = v___x_2863_;
goto v___jp_2829_;
}
v___jp_2829_:
{
if (v___y_2830_ == 0)
{
uint8_t v___x_2831_; 
v___x_2831_ = l_Lean_Exception_isInterrupt(v_a_2825_);
if (v___x_2831_ == 0)
{
uint8_t v___x_2832_; 
lean_inc(v_a_2825_);
v___x_2832_ = l_Lean_Exception_isMaxRecDepth(v_a_2825_);
if (v___x_2832_ == 0)
{
lean_object* v_toCold_2833_; lean_object* v_options_2834_; uint8_t v_hasTrace_2835_; 
lean_del_object(v___x_2827_);
v_toCold_2833_ = lean_ctor_get(v___y_2790_, 0);
v_options_2834_ = lean_ctor_get(v_toCold_2833_, 2);
v_hasTrace_2835_ = lean_ctor_get_uint8(v_options_2834_, sizeof(void*)*1);
if (v_hasTrace_2835_ == 0)
{
lean_dec(v_a_2825_);
goto v___jp_2812_;
}
else
{
lean_object* v_inheritedTraceOptions_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; uint8_t v___x_2839_; 
v_inheritedTraceOptions_2836_ = lean_ctor_get(v_toCold_2833_, 11);
v___x_2837_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2838_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_2839_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2836_, v_options_2834_, v___x_2838_);
if (v___x_2839_ == 0)
{
lean_dec(v_a_2825_);
goto v___jp_2812_;
}
else
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2840_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1);
v___x_2841_ = l_Lean_Exception_toMessageData(v_a_2825_);
v___x_2842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2840_);
lean_ctor_set(v___x_2842_, 1, v___x_2841_);
v___x_2843_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_2837_, v___x_2842_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; lean_object* v___x_2845_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_a_2844_);
lean_dec_ref_known(v___x_2843_, 1);
v___x_2845_ = lean_apply_6(v___f_2784_, v_a_2844_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, lean_box(0));
v___y_2794_ = v___x_2845_;
goto v___jp_2793_;
}
else
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec_ref(v___f_2784_);
v_a_2846_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2843_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2843_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2846_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
}
}
else
{
lean_object* v___x_2855_; 
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec_ref(v___f_2784_);
if (v_isShared_2828_ == 0)
{
v___x_2855_ = v___x_2827_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2825_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
else
{
lean_object* v___x_2858_; 
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec_ref(v___f_2784_);
if (v_isShared_2828_ == 0)
{
v___x_2858_ = v___x_2827_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2825_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
else
{
lean_object* v___x_2861_; 
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec_ref(v___f_2784_);
if (v_isShared_2828_ == 0)
{
v___x_2861_ = v___x_2827_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2825_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
}
v___jp_2793_:
{
if (lean_obj_tag(v___y_2794_) == 0)
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2803_; 
v_a_2795_ = lean_ctor_get(v___y_2794_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___y_2794_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2797_ = v___y_2794_;
v_isShared_2798_ = v_isSharedCheck_2803_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___y_2794_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2803_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v_a_2799_; lean_object* v___x_2801_; 
v_a_2799_ = lean_ctor_get(v_a_2795_, 0);
lean_inc(v_a_2799_);
lean_dec(v_a_2795_);
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 0, v_a_2799_);
v___x_2801_ = v___x_2797_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2799_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
v_a_2804_ = lean_ctor_get(v___y_2794_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___y_2794_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___y_2794_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___y_2794_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2804_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
}
v___jp_2812_:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2813_ = lean_box(0);
v___x_2814_ = lean_apply_6(v___f_2784_, v___x_2813_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, lean_box(0));
v___y_2794_ = v___x_2814_;
goto v___jp_2793_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___boxed(lean_object* v___f_2866_, lean_object* v_term_2867_, lean_object* v___x_2868_, lean_object* v___x_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(v___f_2866_, v_term_2867_, v___x_2868_, v___x_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_2876_, lean_object* v_vals_2877_, lean_object* v_i_2878_, lean_object* v_k_2879_){
_start:
{
lean_object* v___x_2880_; uint8_t v___x_2881_; 
v___x_2880_ = lean_array_get_size(v_keys_2876_);
v___x_2881_ = lean_nat_dec_lt(v_i_2878_, v___x_2880_);
if (v___x_2881_ == 0)
{
lean_object* v___x_2882_; 
lean_dec(v_i_2878_);
v___x_2882_ = lean_box(0);
return v___x_2882_;
}
else
{
lean_object* v_k_x27_2883_; uint8_t v___x_2884_; 
v_k_x27_2883_ = lean_array_fget_borrowed(v_keys_2876_, v_i_2878_);
v___x_2884_ = l_Lean_instBEqMVarId_beq(v_k_2879_, v_k_x27_2883_);
if (v___x_2884_ == 0)
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2885_ = lean_unsigned_to_nat(1u);
v___x_2886_ = lean_nat_add(v_i_2878_, v___x_2885_);
lean_dec(v_i_2878_);
v_i_2878_ = v___x_2886_;
goto _start;
}
else
{
lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2888_ = lean_array_fget_borrowed(v_vals_2877_, v_i_2878_);
lean_dec(v_i_2878_);
lean_inc(v___x_2888_);
v___x_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2888_);
return v___x_2889_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_2890_, lean_object* v_vals_2891_, lean_object* v_i_2892_, lean_object* v_k_2893_){
_start:
{
lean_object* v_res_2894_; 
v_res_2894_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_keys_2890_, v_vals_2891_, v_i_2892_, v_k_2893_);
lean_dec(v_k_2893_);
lean_dec_ref(v_vals_2891_);
lean_dec_ref(v_keys_2890_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(lean_object* v_x_2895_, size_t v_x_2896_, lean_object* v_x_2897_){
_start:
{
if (lean_obj_tag(v_x_2895_) == 0)
{
lean_object* v_es_2898_; lean_object* v___x_2899_; size_t v___x_2900_; size_t v___x_2901_; lean_object* v_j_2902_; lean_object* v___x_2903_; 
v_es_2898_ = lean_ctor_get(v_x_2895_, 0);
v___x_2899_ = lean_box(2);
v___x_2900_ = ((size_t)31ULL);
v___x_2901_ = lean_usize_land(v_x_2896_, v___x_2900_);
v_j_2902_ = lean_usize_to_nat(v___x_2901_);
v___x_2903_ = lean_array_get_borrowed(v___x_2899_, v_es_2898_, v_j_2902_);
lean_dec(v_j_2902_);
switch(lean_obj_tag(v___x_2903_))
{
case 0:
{
lean_object* v_key_2904_; lean_object* v_val_2905_; uint8_t v___x_2906_; 
v_key_2904_ = lean_ctor_get(v___x_2903_, 0);
v_val_2905_ = lean_ctor_get(v___x_2903_, 1);
v___x_2906_ = l_Lean_instBEqMVarId_beq(v_x_2897_, v_key_2904_);
if (v___x_2906_ == 0)
{
lean_object* v___x_2907_; 
v___x_2907_ = lean_box(0);
return v___x_2907_;
}
else
{
lean_object* v___x_2908_; 
lean_inc(v_val_2905_);
v___x_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2908_, 0, v_val_2905_);
return v___x_2908_;
}
}
case 1:
{
lean_object* v_node_2909_; size_t v___x_2910_; size_t v___x_2911_; 
v_node_2909_ = lean_ctor_get(v___x_2903_, 0);
v___x_2910_ = ((size_t)5ULL);
v___x_2911_ = lean_usize_shift_right(v_x_2896_, v___x_2910_);
v_x_2895_ = v_node_2909_;
v_x_2896_ = v___x_2911_;
goto _start;
}
default: 
{
lean_object* v___x_2913_; 
v___x_2913_ = lean_box(0);
return v___x_2913_;
}
}
}
else
{
lean_object* v_ks_2914_; lean_object* v_vs_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v_ks_2914_ = lean_ctor_get(v_x_2895_, 0);
v_vs_2915_ = lean_ctor_get(v_x_2895_, 1);
v___x_2916_ = lean_unsigned_to_nat(0u);
v___x_2917_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_ks_2914_, v_vs_2915_, v___x_2916_, v_x_2897_);
return v___x_2917_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg___boxed(lean_object* v_x_2918_, lean_object* v_x_2919_, lean_object* v_x_2920_){
_start:
{
size_t v_x_11628__boxed_2921_; lean_object* v_res_2922_; 
v_x_11628__boxed_2921_ = lean_unbox_usize(v_x_2919_);
lean_dec(v_x_2919_);
v_res_2922_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_2918_, v_x_11628__boxed_2921_, v_x_2920_);
lean_dec(v_x_2920_);
lean_dec_ref(v_x_2918_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(lean_object* v_x_2923_, lean_object* v_x_2924_){
_start:
{
uint64_t v___x_2925_; size_t v___x_2926_; lean_object* v___x_2927_; 
v___x_2925_ = l_Lean_instHashableMVarId_hash(v_x_2924_);
v___x_2926_ = lean_uint64_to_usize(v___x_2925_);
v___x_2927_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_2923_, v___x_2926_, v_x_2924_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg___boxed(lean_object* v_x_2928_, lean_object* v_x_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_x_2928_, v_x_2929_);
lean_dec(v_x_2929_);
lean_dec_ref(v_x_2928_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(lean_object* v_c_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_){
_start:
{
lean_object* v_mctx_2960_; lean_object* v_env_2961_; lean_object* v_opts_2962_; lean_object* v_namingCtx_2963_; lean_object* v_goal_2964_; lean_object* v_decls_2965_; lean_object* v___x_2966_; 
v_mctx_2960_ = lean_ctor_get(v_c_2956_, 3);
lean_inc_ref(v_mctx_2960_);
v_env_2961_ = lean_ctor_get(v_c_2956_, 2);
lean_inc_ref(v_env_2961_);
v_opts_2962_ = lean_ctor_get(v_c_2956_, 4);
lean_inc_ref(v_opts_2962_);
v_namingCtx_2963_ = lean_ctor_get(v_c_2956_, 5);
lean_inc_ref(v_namingCtx_2963_);
v_goal_2964_ = lean_ctor_get(v_c_2956_, 6);
lean_inc(v_goal_2964_);
lean_dec_ref(v_c_2956_);
v_decls_2965_ = lean_ctor_get(v_mctx_2960_, 5);
v___x_2966_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_decls_2965_, v_goal_2964_);
if (lean_obj_tag(v___x_2966_) == 1)
{
lean_object* v_val_2967_; lean_object* v_lctx_2968_; lean_object* v___f_2969_; lean_object* v___f_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___f_2975_; lean_object* v___x_2976_; uint8_t v___x_2977_; lean_object* v___x_2978_; lean_object* v_term_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___f_2982_; lean_object* v___x_2983_; 
v_val_2967_ = lean_ctor_get(v___x_2966_, 0);
lean_inc(v_val_2967_);
lean_dec_ref_known(v___x_2966_, 1);
v_lctx_2968_ = lean_ctor_get(v_val_2967_, 1);
lean_inc_ref(v_lctx_2968_);
lean_dec(v_val_2967_);
v___f_2969_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__0));
v___f_2970_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__1));
v___x_2971_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__3));
v___x_2972_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__4));
v___x_2973_ = lean_box(0);
lean_inc(v_goal_2964_);
v___x_2974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2974_, 0, v_goal_2964_);
lean_ctor_set(v___x_2974_, 1, v___x_2973_);
v___f_2975_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed), 11, 4);
lean_closure_set(v___f_2975_, 0, v___x_2974_);
lean_closure_set(v___f_2975_, 1, v___f_2969_);
lean_closure_set(v___f_2975_, 2, v___x_2972_);
lean_closure_set(v___f_2975_, 3, v___x_2971_);
v___x_2976_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed), 10, 3);
lean_closure_set(v___x_2976_, 0, lean_box(0));
lean_closure_set(v___x_2976_, 1, v_goal_2964_);
lean_closure_set(v___x_2976_, 2, v___f_2975_);
v___x_2977_ = 1;
v___x_2978_ = lean_box(v___x_2977_);
v_term_2979_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed), 9, 2);
lean_closure_set(v_term_2979_, 0, v___x_2976_);
lean_closure_set(v_term_2979_, 1, v___x_2978_);
v___x_2980_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__6));
v___x_2981_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__7));
v___f_2982_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___boxed), 9, 4);
lean_closure_set(v___f_2982_, 0, v___f_2970_);
lean_closure_set(v___f_2982_, 1, v_term_2979_);
lean_closure_set(v___f_2982_, 2, v___x_2980_);
lean_closure_set(v___f_2982_, 3, v___x_2981_);
v___x_2983_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_2961_, v_mctx_2960_, v_lctx_2968_, v_opts_2962_, v_namingCtx_2963_, v___f_2982_, v_a_2957_, v_a_2958_);
return v___x_2983_;
}
else
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
lean_dec(v___x_2966_);
lean_dec(v_goal_2964_);
lean_dec_ref(v_namingCtx_2963_);
lean_dec_ref(v_opts_2962_);
lean_dec_ref(v_env_2961_);
lean_dec_ref(v_mctx_2960_);
v___x_2984_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__0));
v___x_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2984_);
return v___x_2985_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___boxed(lean_object* v_c_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(v_c_2986_, v_a_2987_, v_a_2988_);
lean_dec(v_a_2988_);
lean_dec_ref(v_a_2987_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0(lean_object* v_00_u03b2_2991_, lean_object* v_x_2992_, lean_object* v_x_2993_){
_start:
{
lean_object* v___x_2994_; 
v___x_2994_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_x_2992_, v_x_2993_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___boxed(lean_object* v_00_u03b2_2995_, lean_object* v_x_2996_, lean_object* v_x_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0(v_00_u03b2_2995_, v_x_2996_, v_x_2997_);
lean_dec(v_x_2997_);
lean_dec_ref(v_x_2996_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(lean_object* v_cls_2999_, lean_object* v_msg_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
lean_object* v___x_3010_; 
v___x_3010_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_2999_, v_msg_3000_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___boxed(lean_object* v_cls_3011_, lean_object* v_msg_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(v_cls_3011_, v_msg_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v___y_3014_);
lean_dec_ref(v___y_3013_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(lean_object* v_00_u03b2_3023_, lean_object* v_x_3024_, size_t v_x_3025_, lean_object* v_x_3026_){
_start:
{
lean_object* v___x_3027_; 
v___x_3027_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_3024_, v_x_3025_, v_x_3026_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3028_, lean_object* v_x_3029_, lean_object* v_x_3030_, lean_object* v_x_3031_){
_start:
{
size_t v_x_11885__boxed_3032_; lean_object* v_res_3033_; 
v_x_11885__boxed_3032_ = lean_unbox_usize(v_x_3030_);
lean_dec(v_x_3030_);
v_res_3033_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(v_00_u03b2_3028_, v_x_3029_, v_x_11885__boxed_3032_, v_x_3031_);
lean_dec(v_x_3031_);
lean_dec_ref(v_x_3029_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3034_, lean_object* v_keys_3035_, lean_object* v_vals_3036_, lean_object* v_heq_3037_, lean_object* v_i_3038_, lean_object* v_k_3039_){
_start:
{
lean_object* v___x_3040_; 
v___x_3040_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_keys_3035_, v_vals_3036_, v_i_3038_, v_k_3039_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3041_, lean_object* v_keys_3042_, lean_object* v_vals_3043_, lean_object* v_heq_3044_, lean_object* v_i_3045_, lean_object* v_k_3046_){
_start:
{
lean_object* v_res_3047_; 
v_res_3047_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2(v_00_u03b2_3041_, v_keys_3042_, v_vals_3043_, v_heq_3044_, v_i_3045_, v_k_3046_);
lean_dec(v_k_3046_);
lean_dec_ref(v_vals_3043_);
lean_dec_ref(v_keys_3042_);
return v_res_3047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(uint8_t v___x_3050_, lean_object* v___x_3051_, lean_object* v_ref_3052_, lean_object* v_a_3053_, lean_object* v___x_3054_, lean_object* v___x_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_){
_start:
{
if (v___x_3050_ == 0)
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; uint8_t v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3051_);
v___x_3060_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__0));
v___x_3061_ = lean_box(0);
v___x_3062_ = 4;
v___x_3063_ = l_Lean_MessageData_nil;
v___x_3064_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_3052_, v_a_3053_, v___x_3059_, v___x_3060_, v___x_3061_, v___x_3062_, v___x_3063_, v___y_3056_, v___y_3057_);
return v___x_3064_;
}
else
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; uint8_t v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3065_ = lean_array_get(v___x_3054_, v_a_3053_, v___x_3055_);
lean_dec_ref(v_a_3053_);
v___x_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3051_);
v___x_3067_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__1));
v___x_3068_ = lean_box(0);
v___x_3069_ = 4;
v___x_3070_ = l_Lean_MessageData_nil;
v___x_3071_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_3052_, v___x_3065_, v___x_3066_, v___x_3067_, v___x_3068_, v___x_3069_, v___x_3070_, v___y_3056_, v___y_3057_);
return v___x_3071_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed(lean_object* v___x_3072_, lean_object* v___x_3073_, lean_object* v_ref_3074_, lean_object* v_a_3075_, lean_object* v___x_3076_, lean_object* v___x_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
uint8_t v___x_3494__boxed_3081_; lean_object* v_res_3082_; 
v___x_3494__boxed_3081_ = lean_unbox(v___x_3072_);
v_res_3082_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(v___x_3494__boxed_3081_, v___x_3073_, v_ref_3074_, v_a_3075_, v___x_3076_, v___x_3077_, v___y_3078_, v___y_3079_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___x_3077_);
lean_dec_ref(v___x_3076_);
return v_res_3082_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_3083_, uint8_t v___y_3084_, lean_object* v_x_3085_){
_start:
{
if (lean_obj_tag(v_x_3085_) == 1)
{
lean_object* v_pre_3086_; 
v_pre_3086_ = lean_ctor_get(v_x_3085_, 0);
if (lean_obj_tag(v_pre_3086_) == 0)
{
lean_object* v_str_3087_; lean_object* v___x_3088_; uint8_t v___x_3089_; 
v_str_3087_ = lean_ctor_get(v_x_3085_, 1);
v___x_3088_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__1));
v___x_3089_ = lean_string_dec_eq(v_str_3087_, v___x_3088_);
if (v___x_3089_ == 0)
{
return v___x_3089_;
}
else
{
return v_suppressElabErrors_3083_;
}
}
else
{
return v___y_3084_;
}
}
else
{
return v___y_3084_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_3090_, lean_object* v___y_3091_, lean_object* v_x_3092_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3093_; uint8_t v___y_3547__boxed_3094_; uint8_t v_res_3095_; lean_object* v_r_3096_; 
v_suppressElabErrors_boxed_3093_ = lean_unbox(v_suppressElabErrors_3090_);
v___y_3547__boxed_3094_ = lean_unbox(v___y_3091_);
v_res_3095_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_3093_, v___y_3547__boxed_3094_, v_x_3092_);
lean_dec(v_x_3092_);
v_r_3096_ = lean_box(v_res_3095_);
return v_r_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(lean_object* v_ref_3097_, lean_object* v_msgData_3098_, uint8_t v_severity_3099_, uint8_t v_isSilent_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_){
_start:
{
lean_object* v___y_3105_; uint8_t v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; uint8_t v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; uint8_t v___y_3170_; uint8_t v___y_3171_; lean_object* v___y_3172_; uint8_t v___y_3173_; lean_object* v___y_3174_; uint8_t v___y_3198_; uint8_t v___y_3199_; lean_object* v___y_3200_; uint8_t v___y_3201_; lean_object* v___y_3202_; uint8_t v___y_3206_; uint8_t v___y_3207_; uint8_t v___y_3208_; uint8_t v___x_3223_; uint8_t v___y_3225_; uint8_t v___y_3226_; uint8_t v___y_3227_; uint8_t v___y_3229_; uint8_t v___x_3241_; 
v___x_3223_ = 2;
v___x_3241_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3099_, v___x_3223_);
if (v___x_3241_ == 0)
{
v___y_3229_ = v___x_3241_;
goto v___jp_3228_;
}
else
{
uint8_t v___x_3242_; 
lean_inc_ref(v_msgData_3098_);
v___x_3242_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3098_);
v___y_3229_ = v___x_3242_;
goto v___jp_3228_;
}
v___jp_3104_:
{
lean_object* v___x_3113_; 
v___x_3113_ = l_Lean_Elab_Command_getScope___redArg(v___y_3112_);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3114_; lean_object* v_currNamespace_3115_; lean_object* v___x_3116_; 
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_a_3114_);
lean_dec_ref_known(v___x_3113_, 1);
v_currNamespace_3115_ = lean_ctor_get(v_a_3114_, 2);
lean_inc(v_currNamespace_3115_);
lean_dec(v_a_3114_);
v___x_3116_ = l_Lean_Elab_Command_getScope___redArg(v___y_3112_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3152_; 
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3119_ = v___x_3116_;
v_isShared_3120_ = v_isSharedCheck_3152_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3116_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3152_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v_openDecls_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v_env_3126_; lean_object* v_messages_3127_; lean_object* v_scopes_3128_; lean_object* v_usedQuotCtxts_3129_; lean_object* v_nextMacroScope_3130_; lean_object* v_maxRecDepth_3131_; lean_object* v_ngen_3132_; lean_object* v_auxDeclNGen_3133_; lean_object* v_infoState_3134_; lean_object* v_traceState_3135_; lean_object* v_snapshotTasks_3136_; lean_object* v_prevLinterStates_3137_; lean_object* v_codeQualityEntryTasks_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3151_; 
v_openDecls_3121_ = lean_ctor_get(v_a_3117_, 3);
lean_inc(v_openDecls_3121_);
lean_dec(v_a_3117_);
v___x_3122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3122_, 0, v_currNamespace_3115_);
lean_ctor_set(v___x_3122_, 1, v_openDecls_3121_);
v___x_3123_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3122_);
lean_ctor_set(v___x_3123_, 1, v___y_3111_);
lean_inc_ref(v___y_3107_);
lean_inc_ref(v___y_3108_);
v___x_3124_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3124_, 0, v___y_3108_);
lean_ctor_set(v___x_3124_, 1, v___y_3110_);
lean_ctor_set(v___x_3124_, 2, v___y_3105_);
lean_ctor_set(v___x_3124_, 3, v___y_3107_);
lean_ctor_set(v___x_3124_, 4, v___x_3123_);
lean_ctor_set_uint8(v___x_3124_, sizeof(void*)*5, v___y_3106_);
lean_ctor_set_uint8(v___x_3124_, sizeof(void*)*5 + 1, v___y_3109_);
lean_ctor_set_uint8(v___x_3124_, sizeof(void*)*5 + 2, v_isSilent_3100_);
v___x_3125_ = lean_st_ref_take(v___y_3112_);
v_env_3126_ = lean_ctor_get(v___x_3125_, 0);
v_messages_3127_ = lean_ctor_get(v___x_3125_, 1);
v_scopes_3128_ = lean_ctor_get(v___x_3125_, 2);
v_usedQuotCtxts_3129_ = lean_ctor_get(v___x_3125_, 3);
v_nextMacroScope_3130_ = lean_ctor_get(v___x_3125_, 4);
v_maxRecDepth_3131_ = lean_ctor_get(v___x_3125_, 5);
v_ngen_3132_ = lean_ctor_get(v___x_3125_, 6);
v_auxDeclNGen_3133_ = lean_ctor_get(v___x_3125_, 7);
v_infoState_3134_ = lean_ctor_get(v___x_3125_, 8);
v_traceState_3135_ = lean_ctor_get(v___x_3125_, 9);
v_snapshotTasks_3136_ = lean_ctor_get(v___x_3125_, 10);
v_prevLinterStates_3137_ = lean_ctor_get(v___x_3125_, 11);
v_codeQualityEntryTasks_3138_ = lean_ctor_get(v___x_3125_, 12);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3140_ = v___x_3125_;
v_isShared_3141_ = v_isSharedCheck_3151_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3138_);
lean_inc(v_prevLinterStates_3137_);
lean_inc(v_snapshotTasks_3136_);
lean_inc(v_traceState_3135_);
lean_inc(v_infoState_3134_);
lean_inc(v_auxDeclNGen_3133_);
lean_inc(v_ngen_3132_);
lean_inc(v_maxRecDepth_3131_);
lean_inc(v_nextMacroScope_3130_);
lean_inc(v_usedQuotCtxts_3129_);
lean_inc(v_scopes_3128_);
lean_inc(v_messages_3127_);
lean_inc(v_env_3126_);
lean_dec(v___x_3125_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3151_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3145_; 
v___x_3142_ = lean_box(0);
v___x_3143_ = l_Lean_MessageLog_add(v___x_3124_, v_messages_3127_);
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 1, v___x_3143_);
v___x_3145_ = v___x_3140_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_env_3126_);
lean_ctor_set(v_reuseFailAlloc_3150_, 1, v___x_3143_);
lean_ctor_set(v_reuseFailAlloc_3150_, 2, v_scopes_3128_);
lean_ctor_set(v_reuseFailAlloc_3150_, 3, v_usedQuotCtxts_3129_);
lean_ctor_set(v_reuseFailAlloc_3150_, 4, v_nextMacroScope_3130_);
lean_ctor_set(v_reuseFailAlloc_3150_, 5, v_maxRecDepth_3131_);
lean_ctor_set(v_reuseFailAlloc_3150_, 6, v_ngen_3132_);
lean_ctor_set(v_reuseFailAlloc_3150_, 7, v_auxDeclNGen_3133_);
lean_ctor_set(v_reuseFailAlloc_3150_, 8, v_infoState_3134_);
lean_ctor_set(v_reuseFailAlloc_3150_, 9, v_traceState_3135_);
lean_ctor_set(v_reuseFailAlloc_3150_, 10, v_snapshotTasks_3136_);
lean_ctor_set(v_reuseFailAlloc_3150_, 11, v_prevLinterStates_3137_);
lean_ctor_set(v_reuseFailAlloc_3150_, 12, v_codeQualityEntryTasks_3138_);
v___x_3145_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
lean_object* v___x_3146_; lean_object* v___x_3148_; 
v___x_3146_ = lean_st_ref_put(v___y_3112_, v___x_3145_);
if (v_isShared_3120_ == 0)
{
lean_ctor_set(v___x_3119_, 0, v___x_3142_);
v___x_3148_ = v___x_3119_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v___x_3142_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
}
}
else
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
lean_dec(v_currNamespace_3115_);
lean_dec_ref(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3105_);
v_a_3153_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3155_ = v___x_3116_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3116_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3153_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
}
else
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
lean_dec_ref(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3105_);
v_a_3161_ = lean_ctor_get(v___x_3113_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3163_ = v___x_3113_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3113_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3164_ == 0)
{
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3161_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
}
v___jp_3169_:
{
lean_object* v_fileName_3175_; lean_object* v_fileMap_3176_; uint8_t v_suppressElabErrors_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___f_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3196_; 
v_fileName_3175_ = lean_ctor_get(v___y_3101_, 0);
v_fileMap_3176_ = lean_ctor_get(v___y_3101_, 1);
v_suppressElabErrors_3177_ = lean_ctor_get_uint8(v___y_3101_, sizeof(void*)*10);
v___x_3178_ = lean_box(v_suppressElabErrors_3177_);
v___x_3179_ = lean_box(v___y_3170_);
v___f_3180_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3180_, 0, v___x_3178_);
lean_closure_set(v___f_3180_, 1, v___x_3179_);
v___x_3181_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3098_);
v___x_3182_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(v___x_3181_, v___y_3102_);
v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3185_ = v___x_3182_;
v_isShared_3186_ = v_isSharedCheck_3196_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3182_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3196_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
lean_inc_ref_n(v_fileMap_3176_, 2);
v___x_3187_ = l_Lean_FileMap_toPosition(v_fileMap_3176_, v___y_3172_);
lean_dec(v___y_3172_);
v___x_3188_ = l_Lean_FileMap_toPosition(v_fileMap_3176_, v___y_3174_);
lean_dec(v___y_3174_);
v___x_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3188_);
v___x_3190_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
if (v_suppressElabErrors_3177_ == 0)
{
lean_del_object(v___x_3185_);
lean_dec_ref(v___f_3180_);
v___y_3105_ = v___x_3189_;
v___y_3106_ = v___y_3171_;
v___y_3107_ = v___x_3190_;
v___y_3108_ = v_fileName_3175_;
v___y_3109_ = v___y_3173_;
v___y_3110_ = v___x_3187_;
v___y_3111_ = v_a_3183_;
v___y_3112_ = v___y_3102_;
goto v___jp_3104_;
}
else
{
uint8_t v___x_3191_; 
lean_inc(v_a_3183_);
v___x_3191_ = l_Lean_MessageData_hasTag(v___f_3180_, v_a_3183_);
if (v___x_3191_ == 0)
{
lean_object* v___x_3192_; lean_object* v___x_3194_; 
lean_dec_ref_known(v___x_3189_, 1);
lean_dec_ref(v___x_3187_);
lean_dec(v_a_3183_);
v___x_3192_ = lean_box(0);
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 0, v___x_3192_);
v___x_3194_ = v___x_3185_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v___x_3192_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
else
{
lean_del_object(v___x_3185_);
v___y_3105_ = v___x_3189_;
v___y_3106_ = v___y_3171_;
v___y_3107_ = v___x_3190_;
v___y_3108_ = v_fileName_3175_;
v___y_3109_ = v___y_3173_;
v___y_3110_ = v___x_3187_;
v___y_3111_ = v_a_3183_;
v___y_3112_ = v___y_3102_;
goto v___jp_3104_;
}
}
}
}
v___jp_3197_:
{
lean_object* v___x_3203_; 
v___x_3203_ = l_Lean_Syntax_getTailPos_x3f(v___y_3200_, v___y_3199_);
lean_dec(v___y_3200_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_inc(v___y_3202_);
v___y_3170_ = v___y_3198_;
v___y_3171_ = v___y_3199_;
v___y_3172_ = v___y_3202_;
v___y_3173_ = v___y_3201_;
v___y_3174_ = v___y_3202_;
goto v___jp_3169_;
}
else
{
lean_object* v_val_3204_; 
v_val_3204_ = lean_ctor_get(v___x_3203_, 0);
lean_inc(v_val_3204_);
lean_dec_ref_known(v___x_3203_, 1);
v___y_3170_ = v___y_3198_;
v___y_3171_ = v___y_3199_;
v___y_3172_ = v___y_3202_;
v___y_3173_ = v___y_3201_;
v___y_3174_ = v_val_3204_;
goto v___jp_3169_;
}
}
v___jp_3205_:
{
lean_object* v___x_3209_; 
v___x_3209_ = l_Lean_Elab_Command_getRef___redArg(v___y_3101_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v_a_3210_; lean_object* v_ref_3211_; lean_object* v___x_3212_; 
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
lean_inc(v_a_3210_);
lean_dec_ref_known(v___x_3209_, 1);
v_ref_3211_ = l_Lean_replaceRef(v_ref_3097_, v_a_3210_);
lean_dec(v_a_3210_);
v___x_3212_ = l_Lean_Syntax_getPos_x3f(v_ref_3211_, v___y_3207_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v___x_3213_; 
v___x_3213_ = lean_unsigned_to_nat(0u);
v___y_3198_ = v___y_3206_;
v___y_3199_ = v___y_3207_;
v___y_3200_ = v_ref_3211_;
v___y_3201_ = v___y_3208_;
v___y_3202_ = v___x_3213_;
goto v___jp_3197_;
}
else
{
lean_object* v_val_3214_; 
v_val_3214_ = lean_ctor_get(v___x_3212_, 0);
lean_inc(v_val_3214_);
lean_dec_ref_known(v___x_3212_, 1);
v___y_3198_ = v___y_3206_;
v___y_3199_ = v___y_3207_;
v___y_3200_ = v_ref_3211_;
v___y_3201_ = v___y_3208_;
v___y_3202_ = v_val_3214_;
goto v___jp_3197_;
}
}
else
{
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3222_; 
lean_dec_ref(v_msgData_3098_);
v_a_3215_ = lean_ctor_get(v___x_3209_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3217_ = v___x_3209_;
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___x_3209_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3220_; 
if (v_isShared_3218_ == 0)
{
v___x_3220_ = v___x_3217_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3215_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
}
v___jp_3224_:
{
if (v___y_3227_ == 0)
{
v___y_3206_ = v___y_3225_;
v___y_3207_ = v___y_3226_;
v___y_3208_ = v_severity_3099_;
goto v___jp_3205_;
}
else
{
v___y_3206_ = v___y_3225_;
v___y_3207_ = v___y_3226_;
v___y_3208_ = v___x_3223_;
goto v___jp_3205_;
}
}
v___jp_3228_:
{
if (v___y_3229_ == 0)
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v_scopes_3232_; lean_object* v___x_3233_; lean_object* v_opts_3234_; uint8_t v___x_3235_; uint8_t v___x_3236_; 
v___x_3230_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3231_ = lean_st_ref_get(v___y_3102_);
v_scopes_3232_ = lean_ctor_get(v___x_3231_, 2);
lean_inc(v_scopes_3232_);
lean_dec(v___x_3231_);
v___x_3233_ = l_List_head_x21___redArg(v___x_3230_, v_scopes_3232_);
lean_dec(v_scopes_3232_);
v_opts_3234_ = lean_ctor_get(v___x_3233_, 1);
lean_inc_ref(v_opts_3234_);
lean_dec(v___x_3233_);
v___x_3235_ = 1;
v___x_3236_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3099_, v___x_3235_);
if (v___x_3236_ == 0)
{
lean_dec_ref(v_opts_3234_);
v___y_3225_ = v___y_3229_;
v___y_3226_ = v___y_3229_;
v___y_3227_ = v___x_3236_;
goto v___jp_3224_;
}
else
{
lean_object* v___x_3237_; uint8_t v___x_3238_; 
v___x_3237_ = l_Lean_warningAsError;
v___x_3238_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_3234_, v___x_3237_);
lean_dec_ref(v_opts_3234_);
v___y_3225_ = v___y_3229_;
v___y_3226_ = v___y_3229_;
v___y_3227_ = v___x_3238_;
goto v___jp_3224_;
}
}
else
{
lean_object* v___x_3239_; lean_object* v___x_3240_; 
lean_dec_ref(v_msgData_3098_);
v___x_3239_ = lean_box(0);
v___x_3240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3239_);
return v___x_3240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___boxed(lean_object* v_ref_3243_, lean_object* v_msgData_3244_, lean_object* v_severity_3245_, lean_object* v_isSilent_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
uint8_t v_severity_boxed_3250_; uint8_t v_isSilent_boxed_3251_; lean_object* v_res_3252_; 
v_severity_boxed_3250_ = lean_unbox(v_severity_3245_);
v_isSilent_boxed_3251_ = lean_unbox(v_isSilent_3246_);
v_res_3252_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3243_, v_msgData_3244_, v_severity_boxed_3250_, v_isSilent_boxed_3251_, v___y_3247_, v___y_3248_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v_ref_3243_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(lean_object* v_ref_3253_, lean_object* v_msgData_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
uint8_t v___x_3258_; uint8_t v___x_3259_; lean_object* v___x_3260_; 
v___x_3258_ = 0;
v___x_3259_ = 0;
v___x_3260_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3253_, v_msgData_3254_, v___x_3258_, v___x_3259_, v___y_3255_, v___y_3256_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0___boxed(lean_object* v_ref_3261_, lean_object* v_msgData_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_){
_start:
{
lean_object* v_res_3266_; 
v_res_3266_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3261_, v_msgData_3262_, v___y_3263_, v___y_3264_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3263_);
lean_dec(v_ref_3261_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(lean_object* v___x_3268_, lean_object* v_x_3269_){
_start:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3270_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___closed__0));
v___x_3271_ = lean_string_append(v___x_3270_, v___x_3268_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed(lean_object* v___x_3272_, lean_object* v_x_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(v___x_3272_, v_x_3273_);
lean_dec_ref(v_x_3273_);
lean_dec_ref(v___x_3272_);
return v_res_3274_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3276_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__0));
v___x_3277_ = l_Lean_stringToMessageData(v___x_3276_);
return v___x_3277_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3279_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__2));
v___x_3280_ = l_Lean_stringToMessageData(v___x_3279_);
return v___x_3280_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3282_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__4));
v___x_3283_ = l_Lean_stringToMessageData(v___x_3282_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(lean_object* v___x_3284_, uint8_t v___x_3285_, lean_object* v___x_3286_, lean_object* v_insertPos_3287_, lean_object* v_cmdLine_3288_, lean_object* v_ref_3289_, size_t v_sz_3290_, size_t v_i_3291_, lean_object* v_bs_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_){
_start:
{
uint8_t v___x_3296_; 
v___x_3296_ = lean_usize_dec_lt(v_i_3291_, v_sz_3290_);
if (v___x_3296_ == 0)
{
lean_object* v___x_3297_; 
lean_dec_ref(v___x_3286_);
lean_dec_ref(v___x_3284_);
v___x_3297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3297_, 0, v_bs_3292_);
return v___x_3297_;
}
else
{
lean_object* v_v_3298_; lean_object* v___x_3299_; lean_object* v_bs_x27_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v_v_3298_ = lean_array_uget(v_bs_3292_, v_i_3291_);
v___x_3299_ = lean_unsigned_to_nat(0u);
v_bs_x27_3300_ = lean_array_uset(v_bs_3292_, v_i_3291_, v___x_3299_);
lean_inc(v_v_3298_);
v___x_3301_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppTactic___boxed), 4, 1);
lean_closure_set(v___x_3301_, 0, v_v_3298_);
v___x_3302_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_3301_, v___y_3293_, v___y_3294_);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_object* v_a_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___f_3306_; lean_object* v___x_3307_; 
v_a_3303_ = lean_ctor_get(v___x_3302_, 0);
lean_inc(v_a_3303_);
lean_dec_ref_known(v___x_3302_, 1);
v___x_3304_ = l_Std_Format_defWidth;
v___x_3305_ = l_Std_Format_pretty(v_a_3303_, v___x_3304_, v___x_3299_, v___x_3299_);
lean_inc_ref(v___x_3305_);
v___f_3306_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3306_, 0, v___x_3305_);
lean_inc_ref(v___x_3284_);
v___x_3307_ = lean_string_append(v___x_3284_, v___x_3305_);
lean_dec_ref(v___x_3305_);
if (v___x_3285_ == 0)
{
goto v___jp_3308_;
}
else
{
lean_object* v___x_3319_; lean_object* v_line_3320_; lean_object* v_column_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3356_; 
lean_inc_ref(v___x_3286_);
v___x_3319_ = l_Lean_FileMap_toPosition(v___x_3286_, v_insertPos_3287_);
v_line_3320_ = lean_ctor_get(v___x_3319_, 0);
v_column_3321_ = lean_ctor_get(v___x_3319_, 1);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3323_ = v___x_3319_;
v_isShared_3324_ = v_isSharedCheck_3356_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_column_3321_);
lean_inc(v_line_3320_);
lean_dec(v___x_3319_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3356_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3333_; 
v___x_3325_ = lean_nat_sub(v_line_3320_, v_cmdLine_3288_);
lean_dec(v_line_3320_);
v___x_3326_ = lean_unsigned_to_nat(1u);
v___x_3327_ = lean_nat_add(v___x_3325_, v___x_3326_);
lean_dec(v___x_3325_);
v___x_3328_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1);
lean_inc_ref(v___x_3307_);
v___x_3329_ = l_String_quote(v___x_3307_);
v___x_3330_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3329_);
v___x_3331_ = l_Lean_MessageData_ofFormat(v___x_3330_);
if (v_isShared_3324_ == 0)
{
lean_ctor_set_tag(v___x_3323_, 7);
lean_ctor_set(v___x_3323_, 1, v___x_3331_);
lean_ctor_set(v___x_3323_, 0, v___x_3328_);
v___x_3333_ = v___x_3323_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v___x_3328_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v___x_3331_);
v___x_3333_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3334_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3);
v___x_3335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3333_);
lean_ctor_set(v___x_3335_, 1, v___x_3334_);
v___x_3336_ = l_Nat_reprFast(v___x_3327_);
v___x_3337_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3336_);
v___x_3338_ = l_Lean_MessageData_ofFormat(v___x_3337_);
v___x_3339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3335_);
lean_ctor_set(v___x_3339_, 1, v___x_3338_);
v___x_3340_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5);
v___x_3341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3339_);
lean_ctor_set(v___x_3341_, 1, v___x_3340_);
v___x_3342_ = l_Nat_reprFast(v_column_3321_);
v___x_3343_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3342_);
v___x_3344_ = l_Lean_MessageData_ofFormat(v___x_3343_);
v___x_3345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3341_);
lean_ctor_set(v___x_3345_, 1, v___x_3344_);
v___x_3346_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3289_, v___x_3345_, v___y_3293_, v___y_3294_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_dec_ref_known(v___x_3346_, 1);
goto v___jp_3308_;
}
else
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3354_; 
lean_dec_ref(v___x_3307_);
lean_dec_ref(v___f_3306_);
lean_dec_ref(v_bs_x27_3300_);
lean_dec(v_v_3298_);
lean_dec_ref(v___x_3286_);
lean_dec_ref(v___x_3284_);
v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3346_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3349_ = v___x_3346_;
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3346_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3352_; 
if (v_isShared_3350_ == 0)
{
v___x_3352_ = v___x_3349_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_a_3347_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
}
}
}
v___jp_3308_:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; size_t v___x_3315_; size_t v___x_3316_; lean_object* v___x_3317_; 
v___x_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3307_);
v___x_3310_ = lean_box(0);
v___x_3311_ = l_Lean_MessageData_ofSyntax(v_v_3298_);
v___x_3312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3311_);
v___x_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3313_, 0, v___f_3306_);
v___x_3314_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3309_);
lean_ctor_set(v___x_3314_, 1, v___x_3310_);
lean_ctor_set(v___x_3314_, 2, v___x_3310_);
lean_ctor_set(v___x_3314_, 3, v___x_3310_);
lean_ctor_set(v___x_3314_, 4, v___x_3312_);
lean_ctor_set(v___x_3314_, 5, v___x_3313_);
v___x_3315_ = ((size_t)1ULL);
v___x_3316_ = lean_usize_add(v_i_3291_, v___x_3315_);
v___x_3317_ = lean_array_uset(v_bs_x27_3300_, v_i_3291_, v___x_3314_);
v_i_3291_ = v___x_3316_;
v_bs_3292_ = v___x_3317_;
goto _start;
}
}
else
{
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3364_; 
lean_dec_ref(v_bs_x27_3300_);
lean_dec(v_v_3298_);
lean_dec_ref(v___x_3286_);
lean_dec_ref(v___x_3284_);
v_a_3357_ = lean_ctor_get(v___x_3302_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3359_ = v___x_3302_;
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3302_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3362_; 
if (v_isShared_3360_ == 0)
{
v___x_3362_ = v___x_3359_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_a_3357_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___boxed(lean_object* v___x_3365_, lean_object* v___x_3366_, lean_object* v___x_3367_, lean_object* v_insertPos_3368_, lean_object* v_cmdLine_3369_, lean_object* v_ref_3370_, lean_object* v_sz_3371_, lean_object* v_i_3372_, lean_object* v_bs_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_){
_start:
{
uint8_t v___x_3859__boxed_3377_; size_t v_sz_boxed_3378_; size_t v_i_boxed_3379_; lean_object* v_res_3380_; 
v___x_3859__boxed_3377_ = lean_unbox(v___x_3366_);
v_sz_boxed_3378_ = lean_unbox_usize(v_sz_3371_);
lean_dec(v_sz_3371_);
v_i_boxed_3379_ = lean_unbox_usize(v_i_3372_);
lean_dec(v_i_3372_);
v_res_3380_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3365_, v___x_3859__boxed_3377_, v___x_3367_, v_insertPos_3368_, v_cmdLine_3369_, v_ref_3370_, v_sz_boxed_3378_, v_i_boxed_3379_, v_bs_3373_, v___y_3374_, v___y_3375_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
lean_dec(v_ref_3370_);
lean_dec(v_cmdLine_3369_);
lean_dec(v_insertPos_3368_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(lean_object* v_tacticSeq_3381_, lean_object* v_ref_3382_, lean_object* v_insertPos_3383_, lean_object* v_suggs_3384_, lean_object* v_cmdLine_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_){
_start:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; uint8_t v___x_3391_; 
v___x_3389_ = lean_array_get_size(v_suggs_3384_);
v___x_3390_ = lean_unsigned_to_nat(0u);
v___x_3391_ = lean_nat_dec_eq(v___x_3389_, v___x_3390_);
if (v___x_3391_ == 0)
{
lean_object* v_fileMap_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v_scopes_3398_; lean_object* v___x_3399_; lean_object* v_opts_3400_; lean_object* v___x_3401_; uint8_t v___x_3402_; size_t v_sz_3403_; size_t v___x_3404_; lean_object* v___x_3405_; 
v_fileMap_3392_ = lean_ctor_get(v_a_3386_, 1);
v___x_3393_ = l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default;
lean_inc_ref_n(v_fileMap_3392_, 2);
v___x_3394_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(v_tacticSeq_3381_, v_fileMap_3392_);
lean_inc(v_insertPos_3383_);
v___x_3395_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx(v_insertPos_3383_);
v___x_3396_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3397_ = lean_st_ref_get(v_a_3387_);
v_scopes_3398_ = lean_ctor_get(v___x_3397_, 2);
lean_inc(v_scopes_3398_);
lean_dec(v___x_3397_);
v___x_3399_ = l_List_head_x21___redArg(v___x_3396_, v_scopes_3398_);
lean_dec(v_scopes_3398_);
v_opts_3400_ = lean_ctor_get(v___x_3399_, 1);
lean_inc_ref(v_opts_3400_);
lean_dec(v___x_3399_);
v___x_3401_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_debug_autoTry_showEdits;
v___x_3402_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_3400_, v___x_3401_);
lean_dec_ref(v_opts_3400_);
v_sz_3403_ = lean_array_size(v_suggs_3384_);
v___x_3404_ = ((size_t)0ULL);
v___x_3405_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3394_, v___x_3402_, v_fileMap_3392_, v_insertPos_3383_, v_cmdLine_3385_, v_ref_3382_, v_sz_3403_, v___x_3404_, v_suggs_3384_, v_a_3386_, v_a_3387_);
lean_dec(v_insertPos_3383_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; uint8_t v___x_3409_; lean_object* v___x_3410_; lean_object* v___y_3411_; lean_object* v___x_3412_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
lean_dec_ref_known(v___x_3405_, 1);
v___x_3407_ = lean_array_get_size(v_a_3406_);
v___x_3408_ = lean_unsigned_to_nat(1u);
v___x_3409_ = lean_nat_dec_eq(v___x_3407_, v___x_3408_);
v___x_3410_ = lean_box(v___x_3409_);
v___y_3411_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed), 9, 6);
lean_closure_set(v___y_3411_, 0, v___x_3410_);
lean_closure_set(v___y_3411_, 1, v___x_3395_);
lean_closure_set(v___y_3411_, 2, v_ref_3382_);
lean_closure_set(v___y_3411_, 3, v_a_3406_);
lean_closure_set(v___y_3411_, 4, v___x_3393_);
lean_closure_set(v___y_3411_, 5, v___x_3390_);
v___x_3412_ = l_Lean_Elab_Command_liftCoreM___redArg(v___y_3411_, v_a_3386_, v_a_3387_);
return v___x_3412_;
}
else
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
lean_dec(v___x_3395_);
lean_dec(v_ref_3382_);
v_a_3413_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3415_ = v___x_3405_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3405_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_a_3413_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
else
{
lean_object* v___x_3421_; lean_object* v___x_3422_; 
lean_dec_ref(v_suggs_3384_);
lean_dec(v_insertPos_3383_);
lean_dec(v_ref_3382_);
v___x_3421_ = lean_box(0);
v___x_3422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3421_);
return v___x_3422_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___boxed(lean_object* v_tacticSeq_3423_, lean_object* v_ref_3424_, lean_object* v_insertPos_3425_, lean_object* v_suggs_3426_, lean_object* v_cmdLine_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_){
_start:
{
lean_object* v_res_3431_; 
v_res_3431_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(v_tacticSeq_3423_, v_ref_3424_, v_insertPos_3425_, v_suggs_3426_, v_cmdLine_3427_, v_a_3428_, v_a_3429_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec(v_cmdLine_3427_);
lean_dec(v_tacticSeq_3423_);
return v_res_3431_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(lean_object* v_x_3432_){
_start:
{
uint8_t v___x_3433_; 
v___x_3433_ = 0;
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0___boxed(lean_object* v_x_3434_){
_start:
{
uint8_t v_res_3435_; lean_object* v_r_3436_; 
v_res_3435_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(v_x_3434_);
lean_dec(v_x_3434_);
v_r_3436_ = lean_box(v_res_3435_);
return v_r_3436_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7(void){
_start:
{
lean_object* v___x_3453_; 
v___x_3453_ = l_Array_mkArray0___redArg();
return v___x_3453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(lean_object* v___f_3457_, lean_object* v_ref_3458_, lean_object* v_goal_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_){
_start:
{
lean_object* v_toCold_3468_; lean_object* v_currRecDepth_3469_; lean_object* v_ref_3470_; uint8_t v_diag_3471_; uint8_t v_suppressElabErrors_3472_; uint8_t v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; uint8_t v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v_ref_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
v_toCold_3468_ = lean_ctor_get(v___y_3462_, 0);
v_currRecDepth_3469_ = lean_ctor_get(v___y_3462_, 1);
v_ref_3470_ = lean_ctor_get(v___y_3462_, 2);
v_diag_3471_ = lean_ctor_get_uint8(v___y_3462_, sizeof(void*)*3);
v_suppressElabErrors_3472_ = lean_ctor_get_uint8(v___y_3462_, sizeof(void*)*3 + 1);
v___x_3473_ = 0;
v___x_3474_ = l_Lean_SourceInfo_fromRef(v_ref_3470_, v___x_3473_);
v___x_3475_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__1));
v___x_3476_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__2));
lean_inc_n(v___x_3474_, 3);
v___x_3477_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3474_);
lean_ctor_set(v___x_3477_, 1, v___x_3476_);
v___x_3478_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__4));
v___x_3479_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__6));
v___x_3480_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7);
v___x_3481_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3474_);
lean_ctor_set(v___x_3481_, 1, v___x_3479_);
lean_ctor_set(v___x_3481_, 2, v___x_3480_);
v___x_3482_ = l_Lean_Syntax_node1(v___x_3474_, v___x_3478_, v___x_3481_);
v___x_3483_ = l_Lean_Syntax_node2(v___x_3474_, v___x_3475_, v___x_3477_, v___x_3482_);
v___x_3484_ = lean_box(0);
v___x_3485_ = lean_box(0);
v___x_3486_ = 1;
v___x_3487_ = lean_box(1);
v___x_3488_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__5));
v___x_3489_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_3489_, 0, v___x_3484_);
lean_ctor_set(v___x_3489_, 1, v___x_3485_);
lean_ctor_set(v___x_3489_, 2, v___x_3484_);
lean_ctor_set(v___x_3489_, 3, v___f_3457_);
lean_ctor_set(v___x_3489_, 4, v___x_3487_);
lean_ctor_set(v___x_3489_, 5, v___x_3487_);
lean_ctor_set(v___x_3489_, 6, v___x_3484_);
lean_ctor_set(v___x_3489_, 7, v___x_3488_);
lean_ctor_set_uint8(v___x_3489_, sizeof(void*)*8, v___x_3486_);
lean_ctor_set_uint8(v___x_3489_, sizeof(void*)*8 + 1, v___x_3486_);
lean_ctor_set_uint8(v___x_3489_, sizeof(void*)*8 + 2, v___x_3486_);
lean_ctor_set_uint8(v___x_3489_, sizeof(void*)*8 + 3, v___x_3486_);
lean_ctor_set_uint8(v___x_3489_, sizeof(void*)*8 + 4, v___x_3473_);
lean_ctor_set_uint8(v___x_3489_, sizeof(void*)*8 + 5, v___x_3473_);
lean_ctor_set_uint8(v___x_3489_, sizeof(void*)*8 + 6, v___x_3473_);
lean_ctor_set_uint8(v___x_3489_, sizeof(void*)*8 + 7, v___x_3473_);
lean_ctor_set_uint8(v___x_3489_, sizeof(void*)*8 + 8, v___x_3486_);
lean_ctor_set_uint8(v___x_3489_, sizeof(void*)*8 + 9, v___x_3473_);
lean_ctor_set_uint8(v___x_3489_, sizeof(void*)*8 + 10, v___x_3486_);
v___x_3490_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__8));
v___x_3491_ = lean_box(0);
v_ref_3492_ = l_Lean_replaceRef(v_ref_3458_, v_ref_3470_);
lean_inc(v_currRecDepth_3469_);
lean_inc_ref(v_toCold_3468_);
v___x_3493_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3493_, 0, v_toCold_3468_);
lean_ctor_set(v___x_3493_, 1, v_currRecDepth_3469_);
lean_ctor_set(v___x_3493_, 2, v_ref_3492_);
lean_ctor_set_uint8(v___x_3493_, sizeof(void*)*3, v_diag_3471_);
lean_ctor_set_uint8(v___x_3493_, sizeof(void*)*3 + 1, v_suppressElabErrors_3472_);
v___x_3494_ = l_Lean_Elab_runTactic(v_goal_3459_, v___x_3483_, v___x_3489_, v___x_3490_, v___y_3460_, v___y_3461_, v___x_3493_, v___y_3463_);
lean_dec_ref_known(v___x_3493_, 3);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3501_; 
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3501_ == 0)
{
lean_object* v_unused_3502_; 
v_unused_3502_ = lean_ctor_get(v___x_3494_, 0);
lean_dec(v_unused_3502_);
v___x_3496_ = v___x_3494_;
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
else
{
lean_dec(v___x_3494_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3499_; 
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 0, v___x_3491_);
v___x_3499_ = v___x_3496_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v___x_3491_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
else
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3528_; 
v_a_3503_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3505_ = v___x_3494_;
v_isShared_3506_ = v_isSharedCheck_3528_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3494_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3528_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3508_; 
lean_inc(v_a_3503_);
if (v_isShared_3506_ == 0)
{
v___x_3508_ = v___x_3505_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_a_3503_);
v___x_3508_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
uint8_t v___y_3510_; uint8_t v___y_3522_; uint8_t v___x_3525_; 
v___x_3525_ = l_Lean_Exception_isInterrupt(v_a_3503_);
if (v___x_3525_ == 0)
{
uint8_t v___x_3526_; 
lean_inc(v_a_3503_);
v___x_3526_ = l_Lean_Exception_isRuntime(v_a_3503_);
v___y_3522_ = v___x_3526_;
goto v___jp_3521_;
}
else
{
v___y_3522_ = v___x_3525_;
goto v___jp_3521_;
}
v___jp_3509_:
{
if (v___y_3510_ == 0)
{
lean_object* v_options_3511_; uint8_t v_hasTrace_3512_; 
lean_dec_ref(v___x_3508_);
v_options_3511_ = lean_ctor_get(v_toCold_3468_, 2);
v_hasTrace_3512_ = lean_ctor_get_uint8(v_options_3511_, sizeof(void*)*1);
if (v_hasTrace_3512_ == 0)
{
lean_dec(v_a_3503_);
goto v___jp_3465_;
}
else
{
lean_object* v_inheritedTraceOptions_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; uint8_t v___x_3516_; 
v_inheritedTraceOptions_3513_ = lean_ctor_get(v_toCold_3468_, 11);
v___x_3514_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3515_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_3516_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3513_, v_options_3511_, v___x_3515_);
if (v___x_3516_ == 0)
{
lean_dec(v_a_3503_);
goto v___jp_3465_;
}
else
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3517_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_3518_ = l_Lean_Exception_toMessageData(v_a_3503_);
v___x_3519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3517_);
lean_ctor_set(v___x_3519_, 1, v___x_3518_);
v___x_3520_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_3514_, v___x_3519_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
return v___x_3520_;
}
}
}
else
{
lean_dec(v_a_3503_);
return v___x_3508_;
}
}
v___jp_3521_:
{
if (v___y_3522_ == 0)
{
uint8_t v___x_3523_; 
v___x_3523_ = l_Lean_Exception_isInterrupt(v_a_3503_);
if (v___x_3523_ == 0)
{
uint8_t v___x_3524_; 
lean_inc(v_a_3503_);
v___x_3524_ = l_Lean_Exception_isMaxRecDepth(v_a_3503_);
v___y_3510_ = v___x_3524_;
goto v___jp_3509_;
}
else
{
v___y_3510_ = v___x_3523_;
goto v___jp_3509_;
}
}
else
{
lean_dec(v_a_3503_);
return v___x_3508_;
}
}
}
}
}
v___jp_3465_:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3466_ = lean_box(0);
v___x_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3466_);
return v___x_3467_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___boxed(lean_object* v___f_3529_, lean_object* v_ref_3530_, lean_object* v_goal_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(v___f_3529_, v_ref_3530_, v_goal_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v_ref_3530_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(lean_object* v_c_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_){
_start:
{
lean_object* v_mctx_3543_; lean_object* v_ref_3544_; lean_object* v_env_3545_; lean_object* v_opts_3546_; lean_object* v_namingCtx_3547_; lean_object* v_goal_3548_; lean_object* v_decls_3549_; lean_object* v___x_3550_; 
v_mctx_3543_ = lean_ctor_get(v_c_3539_, 3);
lean_inc_ref(v_mctx_3543_);
v_ref_3544_ = lean_ctor_get(v_c_3539_, 1);
lean_inc(v_ref_3544_);
v_env_3545_ = lean_ctor_get(v_c_3539_, 2);
lean_inc_ref(v_env_3545_);
v_opts_3546_ = lean_ctor_get(v_c_3539_, 4);
lean_inc_ref(v_opts_3546_);
v_namingCtx_3547_ = lean_ctor_get(v_c_3539_, 5);
lean_inc_ref(v_namingCtx_3547_);
v_goal_3548_ = lean_ctor_get(v_c_3539_, 6);
lean_inc(v_goal_3548_);
lean_dec_ref(v_c_3539_);
v_decls_3549_ = lean_ctor_get(v_mctx_3543_, 5);
v___x_3550_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_decls_3549_, v_goal_3548_);
if (lean_obj_tag(v___x_3550_) == 1)
{
lean_object* v_val_3551_; lean_object* v_lctx_3552_; lean_object* v___f_3553_; lean_object* v___f_3554_; lean_object* v___x_3555_; 
v_val_3551_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_val_3551_);
lean_dec_ref_known(v___x_3550_, 1);
v_lctx_3552_ = lean_ctor_get(v_val_3551_, 1);
lean_inc_ref(v_lctx_3552_);
lean_dec(v_val_3551_);
v___f_3553_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___closed__0));
v___f_3554_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___boxed), 8, 3);
lean_closure_set(v___f_3554_, 0, v___f_3553_);
lean_closure_set(v___f_3554_, 1, v_ref_3544_);
lean_closure_set(v___f_3554_, 2, v_goal_3548_);
v___x_3555_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_3545_, v_mctx_3543_, v_lctx_3552_, v_opts_3546_, v_namingCtx_3547_, v___f_3554_, v_a_3540_, v_a_3541_);
return v___x_3555_;
}
else
{
lean_object* v___x_3556_; lean_object* v___x_3557_; 
lean_dec(v___x_3550_);
lean_dec(v_goal_3548_);
lean_dec_ref(v_namingCtx_3547_);
lean_dec_ref(v_opts_3546_);
lean_dec_ref(v_env_3545_);
lean_dec(v_ref_3544_);
lean_dec_ref(v_mctx_3543_);
v___x_3556_ = lean_box(0);
v___x_3557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3556_);
return v___x_3557_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___boxed(lean_object* v_c_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(v_c_3558_, v_a_3559_, v_a_3560_);
lean_dec(v_a_3560_);
lean_dec_ref(v_a_3559_);
return v_res_3562_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(lean_object* v___x_3563_, lean_object* v_val_3564_, lean_object* v_as_3565_, size_t v_i_3566_, size_t v_stop_3567_){
_start:
{
uint8_t v___x_3572_; uint8_t v___x_3573_; 
v___x_3572_ = 0;
v___x_3573_ = lean_usize_dec_eq(v_i_3566_, v_stop_3567_);
if (v___x_3573_ == 0)
{
lean_object* v___x_3574_; lean_object* v_pos_3575_; uint8_t v_severity_3576_; lean_object* v_data_3577_; lean_object* v___f_3578_; uint8_t v___x_3579_; lean_object* v___x_3580_; uint8_t v___x_3581_; uint8_t v___y_3583_; 
v___x_3574_ = lean_array_uget_borrowed(v_as_3565_, v_i_3566_);
v_pos_3575_ = lean_ctor_get(v___x_3574_, 1);
v_severity_3576_ = lean_ctor_get_uint8(v___x_3574_, sizeof(void*)*5 + 1);
v_data_3577_ = lean_ctor_get(v___x_3574_, 4);
v___f_3578_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
v___x_3579_ = 1;
lean_inc_ref(v_pos_3575_);
v___x_3580_ = l_Lean_FileMap_ofPosition(v___x_3563_, v_pos_3575_);
v___x_3581_ = l_Lean_Syntax_Range_contains(v_val_3564_, v___x_3580_, v___x_3579_);
lean_dec(v___x_3580_);
if (v_severity_3576_ == 2)
{
v___y_3583_ = v___x_3579_;
goto v___jp_3582_;
}
else
{
v___y_3583_ = v___x_3572_;
goto v___jp_3582_;
}
v___jp_3582_:
{
if (v___x_3581_ == 0)
{
goto v___jp_3568_;
}
else
{
if (v___y_3583_ == 0)
{
goto v___jp_3568_;
}
else
{
uint8_t v___x_3584_; 
lean_inc(v_data_3577_);
v___x_3584_ = l_Lean_MessageData_hasTag(v___f_3578_, v_data_3577_);
if (v___x_3584_ == 0)
{
return v___x_3579_;
}
else
{
goto v___jp_3568_;
}
}
}
}
}
else
{
return v___x_3572_;
}
v___jp_3568_:
{
size_t v___x_3569_; size_t v___x_3570_; 
v___x_3569_ = ((size_t)1ULL);
v___x_3570_ = lean_usize_add(v_i_3566_, v___x_3569_);
v_i_3566_ = v___x_3570_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1___boxed(lean_object* v___x_3585_, lean_object* v_val_3586_, lean_object* v_as_3587_, lean_object* v_i_3588_, lean_object* v_stop_3589_){
_start:
{
size_t v_i_boxed_3590_; size_t v_stop_boxed_3591_; uint8_t v_res_3592_; lean_object* v_r_3593_; 
v_i_boxed_3590_ = lean_unbox_usize(v_i_3588_);
lean_dec(v_i_3588_);
v_stop_boxed_3591_ = lean_unbox_usize(v_stop_3589_);
lean_dec(v_stop_3589_);
v_res_3592_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3585_, v_val_3586_, v_as_3587_, v_i_boxed_3590_, v_stop_boxed_3591_);
lean_dec_ref(v_as_3587_);
lean_dec_ref(v_val_3586_);
lean_dec_ref(v___x_3585_);
v_r_3593_ = lean_box(v_res_3592_);
return v_r_3593_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(lean_object* v___x_3594_, lean_object* v_val_3595_, lean_object* v_x_3596_){
_start:
{
if (lean_obj_tag(v_x_3596_) == 0)
{
lean_object* v_cs_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; uint8_t v___x_3600_; 
v_cs_3597_ = lean_ctor_get(v_x_3596_, 0);
v___x_3598_ = lean_unsigned_to_nat(0u);
v___x_3599_ = lean_array_get_size(v_cs_3597_);
v___x_3600_ = lean_nat_dec_lt(v___x_3598_, v___x_3599_);
if (v___x_3600_ == 0)
{
return v___x_3600_;
}
else
{
if (v___x_3600_ == 0)
{
return v___x_3600_;
}
else
{
size_t v___x_3601_; size_t v___x_3602_; uint8_t v___x_3603_; 
v___x_3601_ = ((size_t)0ULL);
v___x_3602_ = lean_usize_of_nat(v___x_3599_);
v___x_3603_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3594_, v_val_3595_, v_cs_3597_, v___x_3601_, v___x_3602_);
return v___x_3603_;
}
}
}
else
{
lean_object* v_vs_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; uint8_t v___x_3607_; 
v_vs_3604_ = lean_ctor_get(v_x_3596_, 0);
v___x_3605_ = lean_unsigned_to_nat(0u);
v___x_3606_ = lean_array_get_size(v_vs_3604_);
v___x_3607_ = lean_nat_dec_lt(v___x_3605_, v___x_3606_);
if (v___x_3607_ == 0)
{
return v___x_3607_;
}
else
{
if (v___x_3607_ == 0)
{
return v___x_3607_;
}
else
{
size_t v___x_3608_; size_t v___x_3609_; uint8_t v___x_3610_; 
v___x_3608_ = ((size_t)0ULL);
v___x_3609_ = lean_usize_of_nat(v___x_3606_);
v___x_3610_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3594_, v_val_3595_, v_vs_3604_, v___x_3608_, v___x_3609_);
return v___x_3610_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(lean_object* v___x_3611_, lean_object* v_val_3612_, lean_object* v_as_3613_, size_t v_i_3614_, size_t v_stop_3615_){
_start:
{
uint8_t v___x_3616_; 
v___x_3616_ = lean_usize_dec_eq(v_i_3614_, v_stop_3615_);
if (v___x_3616_ == 0)
{
lean_object* v___x_3617_; uint8_t v___x_3618_; 
v___x_3617_ = lean_array_uget_borrowed(v_as_3613_, v_i_3614_);
v___x_3618_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3611_, v_val_3612_, v___x_3617_);
if (v___x_3618_ == 0)
{
size_t v___x_3619_; size_t v___x_3620_; 
v___x_3619_ = ((size_t)1ULL);
v___x_3620_ = lean_usize_add(v_i_3614_, v___x_3619_);
v_i_3614_ = v___x_3620_;
goto _start;
}
else
{
return v___x_3618_;
}
}
else
{
uint8_t v___x_3622_; 
v___x_3622_ = 0;
return v___x_3622_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3623_, lean_object* v_val_3624_, lean_object* v_as_3625_, lean_object* v_i_3626_, lean_object* v_stop_3627_){
_start:
{
size_t v_i_boxed_3628_; size_t v_stop_boxed_3629_; uint8_t v_res_3630_; lean_object* v_r_3631_; 
v_i_boxed_3628_ = lean_unbox_usize(v_i_3626_);
lean_dec(v_i_3626_);
v_stop_boxed_3629_ = lean_unbox_usize(v_stop_3627_);
lean_dec(v_stop_3627_);
v_res_3630_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3623_, v_val_3624_, v_as_3625_, v_i_boxed_3628_, v_stop_boxed_3629_);
lean_dec_ref(v_as_3625_);
lean_dec_ref(v_val_3624_);
lean_dec_ref(v___x_3623_);
v_r_3631_ = lean_box(v_res_3630_);
return v_r_3631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0___boxed(lean_object* v___x_3632_, lean_object* v_val_3633_, lean_object* v_x_3634_){
_start:
{
uint8_t v_res_3635_; lean_object* v_r_3636_; 
v_res_3635_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3632_, v_val_3633_, v_x_3634_);
lean_dec_ref(v_x_3634_);
lean_dec_ref(v_val_3633_);
lean_dec_ref(v___x_3632_);
v_r_3636_ = lean_box(v_res_3635_);
return v_r_3636_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(lean_object* v___x_3637_, lean_object* v_val_3638_, lean_object* v_t_3639_){
_start:
{
lean_object* v_root_3640_; lean_object* v_tail_3641_; uint8_t v___x_3642_; 
v_root_3640_ = lean_ctor_get(v_t_3639_, 0);
v_tail_3641_ = lean_ctor_get(v_t_3639_, 1);
v___x_3642_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3637_, v_val_3638_, v_root_3640_);
if (v___x_3642_ == 0)
{
lean_object* v___x_3643_; lean_object* v___x_3644_; uint8_t v___x_3645_; 
v___x_3643_ = lean_unsigned_to_nat(0u);
v___x_3644_ = lean_array_get_size(v_tail_3641_);
v___x_3645_ = lean_nat_dec_lt(v___x_3643_, v___x_3644_);
if (v___x_3645_ == 0)
{
return v___x_3645_;
}
else
{
if (v___x_3645_ == 0)
{
return v___x_3645_;
}
else
{
size_t v___x_3646_; size_t v___x_3647_; uint8_t v___x_3648_; 
v___x_3646_ = ((size_t)0ULL);
v___x_3647_ = lean_usize_of_nat(v___x_3644_);
v___x_3648_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3637_, v_val_3638_, v_tail_3641_, v___x_3646_, v___x_3647_);
return v___x_3648_;
}
}
}
else
{
return v___x_3642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0___boxed(lean_object* v___x_3649_, lean_object* v_val_3650_, lean_object* v_t_3651_){
_start:
{
uint8_t v_res_3652_; lean_object* v_r_3653_; 
v_res_3652_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v___x_3649_, v_val_3650_, v_t_3651_);
lean_dec_ref(v_t_3651_);
lean_dec_ref(v_val_3650_);
lean_dec_ref(v___x_3649_);
v_r_3653_ = lean_box(v_res_3652_);
return v_r_3653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(lean_object* v_stx_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_){
_start:
{
uint8_t v___x_3658_; lean_object* v___x_3659_; 
v___x_3658_ = 0;
v___x_3659_ = l_Lean_Syntax_getRange_x3f(v_stx_3654_, v___x_3658_);
if (lean_obj_tag(v___x_3659_) == 1)
{
lean_object* v_val_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3673_; 
v_val_3660_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3662_ = v___x_3659_;
v_isShared_3663_ = v_isSharedCheck_3673_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_val_3660_);
lean_dec(v___x_3659_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3673_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v_fileMap_3664_; lean_object* v___x_3665_; lean_object* v_messages_3666_; lean_object* v___x_3667_; uint8_t v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3671_; 
v_fileMap_3664_ = lean_ctor_get(v_a_3655_, 1);
v___x_3665_ = lean_st_ref_get(v_a_3656_);
v_messages_3666_ = lean_ctor_get(v___x_3665_, 1);
lean_inc_ref(v_messages_3666_);
lean_dec(v___x_3665_);
v___x_3667_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_3666_);
v___x_3668_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v_fileMap_3664_, v_val_3660_, v___x_3667_);
lean_dec_ref(v___x_3667_);
lean_dec(v_val_3660_);
v___x_3669_ = lean_box(v___x_3668_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set_tag(v___x_3662_, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3669_);
v___x_3671_ = v___x_3662_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3669_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
else
{
lean_object* v___x_3674_; lean_object* v___x_3675_; 
lean_dec(v___x_3659_);
v___x_3674_ = lean_box(v___x_3658_);
v___x_3675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3675_, 0, v___x_3674_);
return v___x_3675_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError___boxed(lean_object* v_stx_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(v_stx_3676_, v_a_3677_, v_a_3678_);
lean_dec(v_a_3678_);
lean_dec_ref(v_a_3677_);
lean_dec(v_stx_3676_);
return v_res_3680_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(lean_object* v_tree_3681_, lean_object* v_fileMap_3682_, lean_object* v_c_3683_){
_start:
{
lean_object* v___y_3685_; lean_object* v_kind_3689_; lean_object* v_ref_3690_; lean_object* v___y_3692_; 
v_kind_3689_ = lean_ctor_get(v_c_3683_, 0);
lean_inc(v_kind_3689_);
v_ref_3690_ = lean_ctor_get(v_c_3683_, 1);
lean_inc(v_ref_3690_);
lean_dec_ref(v_c_3683_);
if (lean_obj_tag(v_kind_3689_) == 0)
{
lean_object* v_insertPos_3708_; 
lean_dec(v_ref_3690_);
v_insertPos_3708_ = lean_ctor_get(v_kind_3689_, 1);
lean_inc(v_insertPos_3708_);
v___y_3692_ = v_insertPos_3708_;
goto v___jp_3691_;
}
else
{
uint8_t v___x_3709_; lean_object* v___x_3710_; 
v___x_3709_ = 0;
v___x_3710_ = l_Lean_Syntax_getPos_x3f(v_ref_3690_, v___x_3709_);
lean_dec(v_ref_3690_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v___x_3711_; 
v___x_3711_ = lean_unsigned_to_nat(0u);
v___y_3692_ = v___x_3711_;
goto v___jp_3691_;
}
else
{
lean_object* v_val_3712_; 
v_val_3712_ = lean_ctor_get(v___x_3710_, 0);
lean_inc(v_val_3712_);
lean_dec_ref_known(v___x_3710_, 1);
v___y_3692_ = v_val_3712_;
goto v___jp_3691_;
}
}
v___jp_3684_:
{
lean_object* v___x_3686_; lean_object* v___x_3687_; uint8_t v___x_3688_; 
v___x_3686_ = l_List_lengthTR___redArg(v___y_3685_);
lean_dec(v___y_3685_);
v___x_3687_ = lean_unsigned_to_nat(1u);
v___x_3688_ = lean_nat_dec_eq(v___x_3686_, v___x_3687_);
lean_dec(v___x_3686_);
return v___x_3688_;
}
v___jp_3691_:
{
lean_object* v___x_3693_; 
v___x_3693_ = l_Lean_Elab_InfoTree_goalsAt_x3f(v_fileMap_3682_, v_tree_3681_, v___y_3692_);
if (lean_obj_tag(v___x_3693_) == 1)
{
lean_object* v_tail_3694_; 
v_tail_3694_ = lean_ctor_get(v___x_3693_, 1);
lean_inc(v_tail_3694_);
if (lean_obj_tag(v_tail_3694_) == 0)
{
if (lean_obj_tag(v_kind_3689_) == 0)
{
lean_object* v_head_3695_; lean_object* v_tacticSeq_3696_; uint8_t v___x_3697_; lean_object* v___x_3698_; 
v_head_3695_ = lean_ctor_get(v___x_3693_, 0);
lean_inc(v_head_3695_);
lean_dec_ref_known(v___x_3693_, 2);
v_tacticSeq_3696_ = lean_ctor_get(v_kind_3689_, 0);
lean_inc(v_tacticSeq_3696_);
lean_dec_ref_known(v_kind_3689_, 2);
v___x_3697_ = 0;
v___x_3698_ = l_Lean_Syntax_getPos_x3f(v_tacticSeq_3696_, v___x_3697_);
lean_dec(v_tacticSeq_3696_);
if (lean_obj_tag(v___x_3698_) == 0)
{
lean_object* v_tacticInfo_3699_; lean_object* v_goalsBefore_3700_; 
v_tacticInfo_3699_ = lean_ctor_get(v_head_3695_, 1);
lean_inc_ref(v_tacticInfo_3699_);
lean_dec(v_head_3695_);
v_goalsBefore_3700_ = lean_ctor_get(v_tacticInfo_3699_, 2);
lean_inc(v_goalsBefore_3700_);
lean_dec_ref(v_tacticInfo_3699_);
v___y_3685_ = v_goalsBefore_3700_;
goto v___jp_3684_;
}
else
{
lean_object* v_tacticInfo_3701_; lean_object* v_goalsAfter_3702_; 
lean_dec_ref_known(v___x_3698_, 1);
v_tacticInfo_3701_ = lean_ctor_get(v_head_3695_, 1);
lean_inc_ref(v_tacticInfo_3701_);
lean_dec(v_head_3695_);
v_goalsAfter_3702_ = lean_ctor_get(v_tacticInfo_3701_, 4);
lean_inc(v_goalsAfter_3702_);
lean_dec_ref(v_tacticInfo_3701_);
v___y_3685_ = v_goalsAfter_3702_;
goto v___jp_3684_;
}
}
else
{
lean_object* v_head_3703_; lean_object* v_tacticInfo_3704_; lean_object* v_goalsBefore_3705_; 
v_head_3703_ = lean_ctor_get(v___x_3693_, 0);
lean_inc(v_head_3703_);
lean_dec_ref_known(v___x_3693_, 2);
v_tacticInfo_3704_ = lean_ctor_get(v_head_3703_, 1);
lean_inc_ref(v_tacticInfo_3704_);
lean_dec(v_head_3703_);
v_goalsBefore_3705_ = lean_ctor_get(v_tacticInfo_3704_, 2);
lean_inc(v_goalsBefore_3705_);
lean_dec_ref(v_tacticInfo_3704_);
v___y_3685_ = v_goalsBefore_3705_;
goto v___jp_3684_;
}
}
else
{
uint8_t v___x_3706_; 
lean_dec_ref_known(v___x_3693_, 2);
lean_dec(v_tail_3694_);
lean_dec(v_kind_3689_);
v___x_3706_ = 0;
return v___x_3706_;
}
}
else
{
uint8_t v___x_3707_; 
lean_dec(v___x_3693_);
lean_dec(v_kind_3689_);
v___x_3707_ = 0;
return v___x_3707_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos___boxed(lean_object* v_tree_3713_, lean_object* v_fileMap_3714_, lean_object* v_c_3715_){
_start:
{
uint8_t v_res_3716_; lean_object* v_r_3717_; 
v_res_3716_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(v_tree_3713_, v_fileMap_3714_, v_c_3715_);
v_r_3717_ = lean_box(v_res_3716_);
return v_r_3717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(lean_object* v___y_3718_){
_start:
{
lean_object* v___x_3720_; lean_object* v_infoState_3721_; lean_object* v_trees_3722_; lean_object* v___x_3723_; 
v___x_3720_ = lean_st_ref_get(v___y_3718_);
v_infoState_3721_ = lean_ctor_get(v___x_3720_, 8);
lean_inc_ref(v_infoState_3721_);
lean_dec(v___x_3720_);
v_trees_3722_ = lean_ctor_get(v_infoState_3721_, 2);
lean_inc_ref(v_trees_3722_);
lean_dec_ref(v_infoState_3721_);
v___x_3723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3723_, 0, v_trees_3722_);
return v___x_3723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg___boxed(lean_object* v___y_3724_, lean_object* v___y_3725_){
_start:
{
lean_object* v_res_3726_; 
v_res_3726_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_3724_);
lean_dec(v___y_3724_);
return v_res_3726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
lean_object* v___x_3730_; 
v___x_3730_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_3728_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___boxed(lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_){
_start:
{
lean_object* v_res_3734_; 
v_res_3734_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(v___y_3731_, v___y_3732_);
lean_dec(v___y_3732_);
lean_dec_ref(v___y_3731_);
return v_res_3734_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3736_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__0));
v___x_3737_ = l_Lean_stringToMessageData(v___x_3736_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(lean_object* v_tree_3738_, lean_object* v___x_3739_, lean_object* v___x_3740_, lean_object* v_as_3741_, size_t v_sz_3742_, size_t v_i_3743_, lean_object* v_b_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
lean_object* v_a_3749_; uint8_t v___x_3753_; 
v___x_3753_ = lean_usize_dec_lt(v_i_3743_, v_sz_3742_);
if (v___x_3753_ == 0)
{
lean_object* v___x_3754_; 
lean_dec_ref(v___x_3739_);
lean_dec_ref(v_tree_3738_);
v___x_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3754_, 0, v_b_3744_);
return v___x_3754_;
}
else
{
lean_object* v___x_3755_; lean_object* v_a_3756_; uint8_t v___x_3757_; 
v___x_3755_ = lean_box(0);
v_a_3756_ = lean_array_uget_borrowed(v_as_3741_, v_i_3743_);
lean_inc(v_a_3756_);
lean_inc_ref(v___x_3739_);
lean_inc_ref(v_tree_3738_);
v___x_3757_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(v_tree_3738_, v___x_3739_, v_a_3756_);
if (v___x_3757_ == 0)
{
lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v_scopes_3763_; lean_object* v___x_3764_; lean_object* v_opts_3765_; uint8_t v_hasTrace_3766_; 
v___x_3758_ = l_Lean_inheritedTraceOptions;
v___x_3759_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3760_ = lean_st_ref_get(v___x_3758_);
v___x_3761_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3762_ = lean_st_ref_get(v___y_3746_);
v_scopes_3763_ = lean_ctor_get(v___x_3762_, 2);
lean_inc(v_scopes_3763_);
lean_dec(v___x_3762_);
v___x_3764_ = l_List_head_x21___redArg(v___x_3761_, v_scopes_3763_);
lean_dec(v_scopes_3763_);
v_opts_3765_ = lean_ctor_get(v___x_3764_, 1);
lean_inc_ref(v_opts_3765_);
lean_dec(v___x_3764_);
v_hasTrace_3766_ = lean_ctor_get_uint8(v_opts_3765_, sizeof(void*)*1);
if (v_hasTrace_3766_ == 0)
{
lean_dec_ref(v_opts_3765_);
lean_dec(v___x_3760_);
v_a_3749_ = v___x_3755_;
goto v___jp_3748_;
}
else
{
lean_object* v___x_3767_; uint8_t v___x_3768_; 
v___x_3767_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_3768_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3760_, v_opts_3765_, v___x_3767_);
lean_dec_ref(v_opts_3765_);
lean_dec(v___x_3760_);
if (v___x_3768_ == 0)
{
v_a_3749_ = v___x_3755_;
goto v___jp_3748_;
}
else
{
lean_object* v___x_3769_; lean_object* v___x_3770_; 
v___x_3769_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1);
v___x_3770_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_3759_, v___x_3769_, v___y_3745_, v___y_3746_);
if (lean_obj_tag(v___x_3770_) == 0)
{
lean_dec_ref_known(v___x_3770_, 1);
v_a_3749_ = v___x_3755_;
goto v___jp_3748_;
}
else
{
lean_dec_ref(v___x_3739_);
lean_dec_ref(v_tree_3738_);
return v___x_3770_;
}
}
}
}
else
{
lean_object* v_kind_3771_; 
v_kind_3771_ = lean_ctor_get(v_a_3756_, 0);
if (lean_obj_tag(v_kind_3771_) == 0)
{
lean_object* v_ref_3772_; lean_object* v_tacticSeq_3773_; lean_object* v_insertPos_3774_; lean_object* v___x_3775_; 
v_ref_3772_ = lean_ctor_get(v_a_3756_, 1);
v_tacticSeq_3773_ = lean_ctor_get(v_kind_3771_, 0);
v_insertPos_3774_ = lean_ctor_get(v_kind_3771_, 1);
lean_inc(v_a_3756_);
v___x_3775_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(v_a_3756_, v___y_3745_, v___y_3746_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v_a_3776_; lean_object* v___x_3777_; 
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
lean_inc(v_a_3776_);
lean_dec_ref_known(v___x_3775_, 1);
lean_inc(v_insertPos_3774_);
lean_inc(v_ref_3772_);
v___x_3777_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(v_tacticSeq_3773_, v_ref_3772_, v_insertPos_3774_, v_a_3776_, v___x_3740_, v___y_3745_, v___y_3746_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_dec_ref_known(v___x_3777_, 1);
v_a_3749_ = v___x_3755_;
goto v___jp_3748_;
}
else
{
lean_dec_ref(v___x_3739_);
lean_dec_ref(v_tree_3738_);
return v___x_3777_;
}
}
else
{
lean_object* v_a_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3785_; 
lean_dec_ref(v___x_3739_);
lean_dec_ref(v_tree_3738_);
v_a_3778_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3780_ = v___x_3775_;
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_a_3778_);
lean_dec(v___x_3775_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3783_; 
if (v_isShared_3781_ == 0)
{
v___x_3783_ = v___x_3780_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_a_3778_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
return v___x_3783_;
}
}
}
}
else
{
lean_object* v___x_3786_; 
lean_inc(v_a_3756_);
v___x_3786_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(v_a_3756_, v___y_3745_, v___y_3746_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_dec_ref_known(v___x_3786_, 1);
v_a_3749_ = v___x_3755_;
goto v___jp_3748_;
}
else
{
lean_dec_ref(v___x_3739_);
lean_dec_ref(v_tree_3738_);
return v___x_3786_;
}
}
}
}
v___jp_3748_:
{
size_t v___x_3750_; size_t v___x_3751_; 
v___x_3750_ = ((size_t)1ULL);
v___x_3751_ = lean_usize_add(v_i_3743_, v___x_3750_);
v_i_3743_ = v___x_3751_;
v_b_3744_ = v_a_3749_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___boxed(lean_object* v_tree_3787_, lean_object* v___x_3788_, lean_object* v___x_3789_, lean_object* v_as_3790_, lean_object* v_sz_3791_, lean_object* v_i_3792_, lean_object* v_b_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
size_t v_sz_boxed_3797_; size_t v_i_boxed_3798_; lean_object* v_res_3799_; 
v_sz_boxed_3797_ = lean_unbox_usize(v_sz_3791_);
lean_dec(v_sz_3791_);
v_i_boxed_3798_ = lean_unbox_usize(v_i_3792_);
lean_dec(v_i_3792_);
v_res_3799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_tree_3787_, v___x_3788_, v___x_3789_, v_as_3790_, v_sz_boxed_3797_, v_i_boxed_3798_, v_b_3793_, v___y_3794_, v___y_3795_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
lean_dec_ref(v_as_3790_);
lean_dec(v___x_3789_);
return v_res_3799_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3804_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__1));
v___x_3805_ = l_Lean_stringToMessageData(v___x_3804_);
return v___x_3805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(lean_object* v_stx_3806_, lean_object* v___x_3807_, lean_object* v___x_3808_, lean_object* v___x_3809_, lean_object* v___x_3810_, lean_object* v_as_3811_, size_t v_sz_3812_, size_t v_i_3813_, lean_object* v_b_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_){
_start:
{
uint8_t v___x_3818_; 
v___x_3818_ = lean_usize_dec_lt(v_i_3813_, v_sz_3812_);
if (v___x_3818_ == 0)
{
lean_object* v___x_3819_; 
lean_dec_ref(v___x_3809_);
lean_dec(v_stx_3806_);
v___x_3819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3819_, 0, v_b_3814_);
return v___x_3819_;
}
else
{
lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v_a_3823_; lean_object* v___x_3824_; 
lean_dec_ref(v_b_3814_);
v___x_3820_ = lean_box(0);
v___x_3821_ = l_Lean_inheritedTraceOptions;
v___x_3822_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_3823_ = lean_array_uget_borrowed(v_as_3811_, v_i_3813_);
lean_inc(v_a_3823_);
lean_inc(v_stx_3806_);
v___x_3824_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3806_, v___x_3807_, v_a_3823_, v___x_3808_, v___y_3815_, v___y_3816_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3825_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v_scopes_3847_; lean_object* v___x_3848_; lean_object* v_opts_3849_; uint8_t v_hasTrace_3850_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
lean_inc(v_a_3825_);
lean_dec_ref_known(v___x_3824_, 1);
v___x_3844_ = lean_st_ref_get(v___x_3821_);
v___x_3845_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3846_ = lean_st_ref_get(v___y_3816_);
v_scopes_3847_ = lean_ctor_get(v___x_3846_, 2);
lean_inc(v_scopes_3847_);
lean_dec(v___x_3846_);
v___x_3848_ = l_List_head_x21___redArg(v___x_3845_, v_scopes_3847_);
lean_dec(v_scopes_3847_);
v_opts_3849_ = lean_ctor_get(v___x_3848_, 1);
lean_inc_ref(v_opts_3849_);
lean_dec(v___x_3848_);
v_hasTrace_3850_ = lean_ctor_get_uint8(v_opts_3849_, sizeof(void*)*1);
if (v_hasTrace_3850_ == 0)
{
lean_dec_ref(v_opts_3849_);
lean_dec(v___x_3844_);
v___y_3827_ = v___y_3815_;
v___y_3828_ = v___y_3816_;
goto v___jp_3826_;
}
else
{
lean_object* v___x_3851_; uint8_t v___x_3852_; 
v___x_3851_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_3852_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3844_, v_opts_3849_, v___x_3851_);
lean_dec_ref(v_opts_3849_);
lean_dec(v___x_3844_);
if (v___x_3852_ == 0)
{
v___y_3827_ = v___y_3815_;
v___y_3828_ = v___y_3816_;
goto v___jp_3826_;
}
else
{
lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; 
v___x_3853_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_3854_ = lean_array_get_size(v_a_3825_);
v___x_3855_ = l_Nat_reprFast(v___x_3854_);
v___x_3856_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3856_, 0, v___x_3855_);
v___x_3857_ = l_Lean_MessageData_ofFormat(v___x_3856_);
v___x_3858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3853_);
lean_ctor_set(v___x_3858_, 1, v___x_3857_);
v___x_3859_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_3822_, v___x_3858_, v___y_3815_, v___y_3816_);
if (lean_obj_tag(v___x_3859_) == 0)
{
lean_dec_ref_known(v___x_3859_, 1);
v___y_3827_ = v___y_3815_;
v___y_3828_ = v___y_3816_;
goto v___jp_3826_;
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec(v_a_3825_);
lean_dec_ref(v___x_3809_);
lean_dec(v_stx_3806_);
v_a_3860_ = lean_ctor_get(v___x_3859_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3859_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3859_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3859_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
}
v___jp_3826_:
{
size_t v_sz_3829_; size_t v___x_3830_; lean_object* v___x_3831_; 
v_sz_3829_ = lean_array_size(v_a_3825_);
v___x_3830_ = ((size_t)0ULL);
lean_inc_ref(v___x_3809_);
lean_inc(v_a_3823_);
v___x_3831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_3823_, v___x_3809_, v___x_3810_, v_a_3825_, v_sz_3829_, v___x_3830_, v___x_3820_, v___y_3827_, v___y_3828_);
lean_dec(v_a_3825_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_object* v___x_3832_; size_t v___x_3833_; size_t v___x_3834_; 
lean_dec_ref_known(v___x_3831_, 1);
v___x_3832_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_3833_ = ((size_t)1ULL);
v___x_3834_ = lean_usize_add(v_i_3813_, v___x_3833_);
v_i_3813_ = v___x_3834_;
v_b_3814_ = v___x_3832_;
goto _start;
}
else
{
lean_object* v_a_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3843_; 
lean_dec_ref(v___x_3809_);
lean_dec(v_stx_3806_);
v_a_3836_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3838_ = v___x_3831_;
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_a_3836_);
lean_dec(v___x_3831_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3841_; 
if (v_isShared_3839_ == 0)
{
v___x_3841_ = v___x_3838_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_a_3836_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
}
}
}
else
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3875_; 
lean_dec_ref(v___x_3809_);
lean_dec(v_stx_3806_);
v_a_3868_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3875_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3870_ = v___x_3824_;
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3824_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3873_; 
if (v_isShared_3871_ == 0)
{
v___x_3873_ = v___x_3870_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_a_3868_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___boxed(lean_object* v_stx_3876_, lean_object* v___x_3877_, lean_object* v___x_3878_, lean_object* v___x_3879_, lean_object* v___x_3880_, lean_object* v_as_3881_, lean_object* v_sz_3882_, lean_object* v_i_3883_, lean_object* v_b_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_){
_start:
{
size_t v_sz_boxed_3888_; size_t v_i_boxed_3889_; lean_object* v_res_3890_; 
v_sz_boxed_3888_ = lean_unbox_usize(v_sz_3882_);
lean_dec(v_sz_3882_);
v_i_boxed_3889_ = lean_unbox_usize(v_i_3883_);
lean_dec(v_i_3883_);
v_res_3890_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_3876_, v___x_3877_, v___x_3878_, v___x_3879_, v___x_3880_, v_as_3881_, v_sz_boxed_3888_, v_i_boxed_3889_, v_b_3884_, v___y_3885_, v___y_3886_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
lean_dec_ref(v_as_3881_);
lean_dec(v___x_3880_);
lean_dec_ref(v___x_3878_);
lean_dec_ref(v___x_3877_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(lean_object* v_stx_3891_, lean_object* v___x_3892_, lean_object* v___x_3893_, lean_object* v___x_3894_, lean_object* v___x_3895_, lean_object* v_as_3896_, size_t v_sz_3897_, size_t v_i_3898_, lean_object* v_b_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_){
_start:
{
uint8_t v___x_3903_; 
v___x_3903_ = lean_usize_dec_lt(v_i_3898_, v_sz_3897_);
if (v___x_3903_ == 0)
{
lean_object* v___x_3904_; 
lean_dec_ref(v___x_3894_);
lean_dec(v_stx_3891_);
v___x_3904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3904_, 0, v_b_3899_);
return v___x_3904_;
}
else
{
lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v_a_3908_; lean_object* v___x_3909_; 
lean_dec_ref(v_b_3899_);
v___x_3905_ = lean_box(0);
v___x_3906_ = l_Lean_inheritedTraceOptions;
v___x_3907_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_3908_ = lean_array_uget_borrowed(v_as_3896_, v_i_3898_);
lean_inc(v_a_3908_);
lean_inc(v_stx_3891_);
v___x_3909_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3891_, v___x_3892_, v_a_3908_, v___x_3893_, v___y_3900_, v___y_3901_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v_scopes_3932_; lean_object* v___x_3933_; lean_object* v_opts_3934_; uint8_t v_hasTrace_3935_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_a_3910_);
lean_dec_ref_known(v___x_3909_, 1);
v___x_3929_ = lean_st_ref_get(v___x_3906_);
v___x_3930_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3931_ = lean_st_ref_get(v___y_3901_);
v_scopes_3932_ = lean_ctor_get(v___x_3931_, 2);
lean_inc(v_scopes_3932_);
lean_dec(v___x_3931_);
v___x_3933_ = l_List_head_x21___redArg(v___x_3930_, v_scopes_3932_);
lean_dec(v_scopes_3932_);
v_opts_3934_ = lean_ctor_get(v___x_3933_, 1);
lean_inc_ref(v_opts_3934_);
lean_dec(v___x_3933_);
v_hasTrace_3935_ = lean_ctor_get_uint8(v_opts_3934_, sizeof(void*)*1);
if (v_hasTrace_3935_ == 0)
{
lean_dec_ref(v_opts_3934_);
lean_dec(v___x_3929_);
v___y_3912_ = v___y_3900_;
v___y_3913_ = v___y_3901_;
goto v___jp_3911_;
}
else
{
lean_object* v___x_3936_; uint8_t v___x_3937_; 
v___x_3936_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_3937_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3929_, v_opts_3934_, v___x_3936_);
lean_dec_ref(v_opts_3934_);
lean_dec(v___x_3929_);
if (v___x_3937_ == 0)
{
v___y_3912_ = v___y_3900_;
v___y_3913_ = v___y_3901_;
goto v___jp_3911_;
}
else
{
lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3938_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_3939_ = lean_array_get_size(v_a_3910_);
v___x_3940_ = l_Nat_reprFast(v___x_3939_);
v___x_3941_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3941_, 0, v___x_3940_);
v___x_3942_ = l_Lean_MessageData_ofFormat(v___x_3941_);
v___x_3943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3938_);
lean_ctor_set(v___x_3943_, 1, v___x_3942_);
v___x_3944_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_3907_, v___x_3943_, v___y_3900_, v___y_3901_);
if (lean_obj_tag(v___x_3944_) == 0)
{
lean_dec_ref_known(v___x_3944_, 1);
v___y_3912_ = v___y_3900_;
v___y_3913_ = v___y_3901_;
goto v___jp_3911_;
}
else
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3952_; 
lean_dec(v_a_3910_);
lean_dec_ref(v___x_3894_);
lean_dec(v_stx_3891_);
v_a_3945_ = lean_ctor_get(v___x_3944_, 0);
v_isSharedCheck_3952_ = !lean_is_exclusive(v___x_3944_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3947_ = v___x_3944_;
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v___x_3944_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3950_; 
if (v_isShared_3948_ == 0)
{
v___x_3950_ = v___x_3947_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v_a_3945_);
v___x_3950_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
return v___x_3950_;
}
}
}
}
}
v___jp_3911_:
{
size_t v_sz_3914_; size_t v___x_3915_; lean_object* v___x_3916_; 
v_sz_3914_ = lean_array_size(v_a_3910_);
v___x_3915_ = ((size_t)0ULL);
lean_inc_ref(v___x_3894_);
lean_inc(v_a_3908_);
v___x_3916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_3908_, v___x_3894_, v___x_3895_, v_a_3910_, v_sz_3914_, v___x_3915_, v___x_3905_, v___y_3912_, v___y_3913_);
lean_dec(v_a_3910_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v___x_3917_; size_t v___x_3918_; size_t v___x_3919_; lean_object* v___x_3920_; 
lean_dec_ref_known(v___x_3916_, 1);
v___x_3917_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_3918_ = ((size_t)1ULL);
v___x_3919_ = lean_usize_add(v_i_3898_, v___x_3918_);
v___x_3920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_3891_, v___x_3892_, v___x_3893_, v___x_3894_, v___x_3895_, v_as_3896_, v_sz_3897_, v___x_3919_, v___x_3917_, v___y_3900_, v___y_3901_);
return v___x_3920_;
}
else
{
lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3928_; 
lean_dec_ref(v___x_3894_);
lean_dec(v_stx_3891_);
v_a_3921_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3923_ = v___x_3916_;
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v___x_3916_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3926_; 
if (v_isShared_3924_ == 0)
{
v___x_3926_ = v___x_3923_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_a_3921_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
}
}
else
{
lean_object* v_a_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3960_; 
lean_dec_ref(v___x_3894_);
lean_dec(v_stx_3891_);
v_a_3953_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3960_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3960_ == 0)
{
v___x_3955_ = v___x_3909_;
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_a_3953_);
lean_dec(v___x_3909_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3958_; 
if (v_isShared_3956_ == 0)
{
v___x_3958_ = v___x_3955_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_a_3953_);
v___x_3958_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
return v___x_3958_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3___boxed(lean_object* v_stx_3961_, lean_object* v___x_3962_, lean_object* v___x_3963_, lean_object* v___x_3964_, lean_object* v___x_3965_, lean_object* v_as_3966_, lean_object* v_sz_3967_, lean_object* v_i_3968_, lean_object* v_b_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_){
_start:
{
size_t v_sz_boxed_3973_; size_t v_i_boxed_3974_; lean_object* v_res_3975_; 
v_sz_boxed_3973_ = lean_unbox_usize(v_sz_3967_);
lean_dec(v_sz_3967_);
v_i_boxed_3974_ = lean_unbox_usize(v_i_3968_);
lean_dec(v_i_3968_);
v_res_3975_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(v_stx_3961_, v___x_3962_, v___x_3963_, v___x_3964_, v___x_3965_, v_as_3966_, v_sz_boxed_3973_, v_i_boxed_3974_, v_b_3969_, v___y_3970_, v___y_3971_);
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3970_);
lean_dec_ref(v_as_3966_);
lean_dec(v___x_3965_);
lean_dec_ref(v___x_3963_);
lean_dec_ref(v___x_3962_);
return v_res_3975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(lean_object* v_stx_3979_, lean_object* v___x_3980_, lean_object* v___x_3981_, lean_object* v___x_3982_, lean_object* v___x_3983_, lean_object* v_as_3984_, size_t v_sz_3985_, size_t v_i_3986_, lean_object* v_b_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
uint8_t v___x_3991_; 
v___x_3991_ = lean_usize_dec_lt(v_i_3986_, v_sz_3985_);
if (v___x_3991_ == 0)
{
lean_object* v___x_3992_; 
lean_dec_ref(v___x_3982_);
lean_dec(v_stx_3979_);
v___x_3992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3992_, 0, v_b_3987_);
return v___x_3992_;
}
else
{
lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v_a_3996_; lean_object* v___x_3997_; 
lean_dec_ref(v_b_3987_);
v___x_3993_ = lean_box(0);
v___x_3994_ = l_Lean_inheritedTraceOptions;
v___x_3995_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_3996_ = lean_array_uget_borrowed(v_as_3984_, v_i_3986_);
lean_inc(v_a_3996_);
lean_inc(v_stx_3979_);
v___x_3997_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3979_, v___x_3980_, v_a_3996_, v___x_3981_, v___y_3988_, v___y_3989_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_object* v_a_3998_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v_scopes_4020_; lean_object* v___x_4021_; lean_object* v_opts_4022_; uint8_t v_hasTrace_4023_; 
v_a_3998_ = lean_ctor_get(v___x_3997_, 0);
lean_inc(v_a_3998_);
lean_dec_ref_known(v___x_3997_, 1);
v___x_4017_ = lean_st_ref_get(v___x_3994_);
v___x_4018_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4019_ = lean_st_ref_get(v___y_3989_);
v_scopes_4020_ = lean_ctor_get(v___x_4019_, 2);
lean_inc(v_scopes_4020_);
lean_dec(v___x_4019_);
v___x_4021_ = l_List_head_x21___redArg(v___x_4018_, v_scopes_4020_);
lean_dec(v_scopes_4020_);
v_opts_4022_ = lean_ctor_get(v___x_4021_, 1);
lean_inc_ref(v_opts_4022_);
lean_dec(v___x_4021_);
v_hasTrace_4023_ = lean_ctor_get_uint8(v_opts_4022_, sizeof(void*)*1);
if (v_hasTrace_4023_ == 0)
{
lean_dec_ref(v_opts_4022_);
lean_dec(v___x_4017_);
v___y_4000_ = v___y_3988_;
v___y_4001_ = v___y_3989_;
goto v___jp_3999_;
}
else
{
lean_object* v___x_4024_; uint8_t v___x_4025_; 
v___x_4024_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_4025_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4017_, v_opts_4022_, v___x_4024_);
lean_dec_ref(v_opts_4022_);
lean_dec(v___x_4017_);
if (v___x_4025_ == 0)
{
v___y_4000_ = v___y_3988_;
v___y_4001_ = v___y_3989_;
goto v___jp_3999_;
}
else
{
lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4026_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_4027_ = lean_array_get_size(v_a_3998_);
v___x_4028_ = l_Nat_reprFast(v___x_4027_);
v___x_4029_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4029_, 0, v___x_4028_);
v___x_4030_ = l_Lean_MessageData_ofFormat(v___x_4029_);
v___x_4031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4026_);
lean_ctor_set(v___x_4031_, 1, v___x_4030_);
v___x_4032_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_3995_, v___x_4031_, v___y_3988_, v___y_3989_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_dec_ref_known(v___x_4032_, 1);
v___y_4000_ = v___y_3988_;
v___y_4001_ = v___y_3989_;
goto v___jp_3999_;
}
else
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4040_; 
lean_dec(v_a_3998_);
lean_dec_ref(v___x_3982_);
lean_dec(v_stx_3979_);
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4035_ = v___x_4032_;
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_4032_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4038_; 
if (v_isShared_4036_ == 0)
{
v___x_4038_ = v___x_4035_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_a_4033_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
return v___x_4038_;
}
}
}
}
}
v___jp_3999_:
{
size_t v_sz_4002_; size_t v___x_4003_; lean_object* v___x_4004_; 
v_sz_4002_ = lean_array_size(v_a_3998_);
v___x_4003_ = ((size_t)0ULL);
lean_inc_ref(v___x_3982_);
lean_inc(v_a_3996_);
v___x_4004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_3996_, v___x_3982_, v___x_3983_, v_a_3998_, v_sz_4002_, v___x_4003_, v___x_3993_, v___y_4000_, v___y_4001_);
lean_dec(v_a_3998_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v___x_4005_; size_t v___x_4006_; size_t v___x_4007_; 
lean_dec_ref_known(v___x_4004_, 1);
v___x_4005_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_4006_ = ((size_t)1ULL);
v___x_4007_ = lean_usize_add(v_i_3986_, v___x_4006_);
v_i_3986_ = v___x_4007_;
v_b_3987_ = v___x_4005_;
goto _start;
}
else
{
lean_object* v_a_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4016_; 
lean_dec_ref(v___x_3982_);
lean_dec(v_stx_3979_);
v_a_4009_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4016_ == 0)
{
v___x_4011_ = v___x_4004_;
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_a_4009_);
lean_dec(v___x_4004_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4014_; 
if (v_isShared_4012_ == 0)
{
v___x_4014_ = v___x_4011_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_a_4009_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
}
}
else
{
lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4048_; 
lean_dec_ref(v___x_3982_);
lean_dec(v_stx_3979_);
v_a_4041_ = lean_ctor_get(v___x_3997_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4043_ = v___x_3997_;
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___x_3997_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4046_; 
if (v_isShared_4044_ == 0)
{
v___x_4046_ = v___x_4043_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_a_4041_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
return v___x_4046_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_stx_4049_, lean_object* v___x_4050_, lean_object* v___x_4051_, lean_object* v___x_4052_, lean_object* v___x_4053_, lean_object* v_as_4054_, lean_object* v_sz_4055_, lean_object* v_i_4056_, lean_object* v_b_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_){
_start:
{
size_t v_sz_boxed_4061_; size_t v_i_boxed_4062_; lean_object* v_res_4063_; 
v_sz_boxed_4061_ = lean_unbox_usize(v_sz_4055_);
lean_dec(v_sz_4055_);
v_i_boxed_4062_ = lean_unbox_usize(v_i_4056_);
lean_dec(v_i_4056_);
v_res_4063_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4049_, v___x_4050_, v___x_4051_, v___x_4052_, v___x_4053_, v_as_4054_, v_sz_boxed_4061_, v_i_boxed_4062_, v_b_4057_, v___y_4058_, v___y_4059_);
lean_dec(v___y_4059_);
lean_dec_ref(v___y_4058_);
lean_dec_ref(v_as_4054_);
lean_dec(v___x_4053_);
lean_dec_ref(v___x_4051_);
lean_dec_ref(v___x_4050_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(lean_object* v_stx_4064_, lean_object* v___x_4065_, lean_object* v___x_4066_, lean_object* v___x_4067_, lean_object* v___x_4068_, lean_object* v_as_4069_, size_t v_sz_4070_, size_t v_i_4071_, lean_object* v_b_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_){
_start:
{
uint8_t v___x_4076_; 
v___x_4076_ = lean_usize_dec_lt(v_i_4071_, v_sz_4070_);
if (v___x_4076_ == 0)
{
lean_object* v___x_4077_; 
lean_dec_ref(v___x_4067_);
lean_dec(v_stx_4064_);
v___x_4077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4077_, 0, v_b_4072_);
return v___x_4077_;
}
else
{
lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v_a_4081_; lean_object* v___x_4082_; 
lean_dec_ref(v_b_4072_);
v___x_4078_ = lean_box(0);
v___x_4079_ = l_Lean_inheritedTraceOptions;
v___x_4080_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_4081_ = lean_array_uget_borrowed(v_as_4069_, v_i_4071_);
lean_inc(v_a_4081_);
lean_inc(v_stx_4064_);
v___x_4082_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_4064_, v___x_4065_, v_a_4081_, v___x_4066_, v___y_4073_, v___y_4074_);
if (lean_obj_tag(v___x_4082_) == 0)
{
lean_object* v_a_4083_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v_scopes_4105_; lean_object* v___x_4106_; lean_object* v_opts_4107_; uint8_t v_hasTrace_4108_; 
v_a_4083_ = lean_ctor_get(v___x_4082_, 0);
lean_inc(v_a_4083_);
lean_dec_ref_known(v___x_4082_, 1);
v___x_4102_ = lean_st_ref_get(v___x_4079_);
v___x_4103_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4104_ = lean_st_ref_get(v___y_4074_);
v_scopes_4105_ = lean_ctor_get(v___x_4104_, 2);
lean_inc(v_scopes_4105_);
lean_dec(v___x_4104_);
v___x_4106_ = l_List_head_x21___redArg(v___x_4103_, v_scopes_4105_);
lean_dec(v_scopes_4105_);
v_opts_4107_ = lean_ctor_get(v___x_4106_, 1);
lean_inc_ref(v_opts_4107_);
lean_dec(v___x_4106_);
v_hasTrace_4108_ = lean_ctor_get_uint8(v_opts_4107_, sizeof(void*)*1);
if (v_hasTrace_4108_ == 0)
{
lean_dec_ref(v_opts_4107_);
lean_dec(v___x_4102_);
v___y_4085_ = v___y_4073_;
v___y_4086_ = v___y_4074_;
goto v___jp_4084_;
}
else
{
lean_object* v___x_4109_; uint8_t v___x_4110_; 
v___x_4109_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_4110_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4102_, v_opts_4107_, v___x_4109_);
lean_dec_ref(v_opts_4107_);
lean_dec(v___x_4102_);
if (v___x_4110_ == 0)
{
v___y_4085_ = v___y_4073_;
v___y_4086_ = v___y_4074_;
goto v___jp_4084_;
}
else
{
lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
v___x_4111_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_4112_ = lean_array_get_size(v_a_4083_);
v___x_4113_ = l_Nat_reprFast(v___x_4112_);
v___x_4114_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4114_, 0, v___x_4113_);
v___x_4115_ = l_Lean_MessageData_ofFormat(v___x_4114_);
v___x_4116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4116_, 0, v___x_4111_);
lean_ctor_set(v___x_4116_, 1, v___x_4115_);
v___x_4117_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_4080_, v___x_4116_, v___y_4073_, v___y_4074_);
if (lean_obj_tag(v___x_4117_) == 0)
{
lean_dec_ref_known(v___x_4117_, 1);
v___y_4085_ = v___y_4073_;
v___y_4086_ = v___y_4074_;
goto v___jp_4084_;
}
else
{
lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4125_; 
lean_dec(v_a_4083_);
lean_dec_ref(v___x_4067_);
lean_dec(v_stx_4064_);
v_a_4118_ = lean_ctor_get(v___x_4117_, 0);
v_isSharedCheck_4125_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4125_ == 0)
{
v___x_4120_ = v___x_4117_;
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_a_4118_);
lean_dec(v___x_4117_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4123_; 
if (v_isShared_4121_ == 0)
{
v___x_4123_ = v___x_4120_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_a_4118_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
return v___x_4123_;
}
}
}
}
}
v___jp_4084_:
{
size_t v_sz_4087_; size_t v___x_4088_; lean_object* v___x_4089_; 
v_sz_4087_ = lean_array_size(v_a_4083_);
v___x_4088_ = ((size_t)0ULL);
lean_inc_ref(v___x_4067_);
lean_inc(v_a_4081_);
v___x_4089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4081_, v___x_4067_, v___x_4068_, v_a_4083_, v_sz_4087_, v___x_4088_, v___x_4078_, v___y_4085_, v___y_4086_);
lean_dec(v_a_4083_);
if (lean_obj_tag(v___x_4089_) == 0)
{
lean_object* v___x_4090_; size_t v___x_4091_; size_t v___x_4092_; lean_object* v___x_4093_; 
lean_dec_ref_known(v___x_4089_, 1);
v___x_4090_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_4091_ = ((size_t)1ULL);
v___x_4092_ = lean_usize_add(v_i_4071_, v___x_4091_);
v___x_4093_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4064_, v___x_4065_, v___x_4066_, v___x_4067_, v___x_4068_, v_as_4069_, v_sz_4070_, v___x_4092_, v___x_4090_, v___y_4073_, v___y_4074_);
return v___x_4093_;
}
else
{
lean_object* v_a_4094_; lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4101_; 
lean_dec_ref(v___x_4067_);
lean_dec(v_stx_4064_);
v_a_4094_ = lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4101_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4101_ == 0)
{
v___x_4096_ = v___x_4089_;
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
else
{
lean_inc(v_a_4094_);
lean_dec(v___x_4089_);
v___x_4096_ = lean_box(0);
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
v_resetjp_4095_:
{
lean_object* v___x_4099_; 
if (v_isShared_4097_ == 0)
{
v___x_4099_ = v___x_4096_;
goto v_reusejp_4098_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v_a_4094_);
v___x_4099_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4098_;
}
v_reusejp_4098_:
{
return v___x_4099_;
}
}
}
}
}
else
{
lean_object* v_a_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4133_; 
lean_dec_ref(v___x_4067_);
lean_dec(v_stx_4064_);
v_a_4126_ = lean_ctor_get(v___x_4082_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v___x_4082_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4128_ = v___x_4082_;
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_a_4126_);
lean_dec(v___x_4082_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4131_; 
if (v_isShared_4129_ == 0)
{
v___x_4131_ = v___x_4128_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_a_4126_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4___boxed(lean_object* v_stx_4134_, lean_object* v___x_4135_, lean_object* v___x_4136_, lean_object* v___x_4137_, lean_object* v___x_4138_, lean_object* v_as_4139_, lean_object* v_sz_4140_, lean_object* v_i_4141_, lean_object* v_b_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_){
_start:
{
size_t v_sz_boxed_4146_; size_t v_i_boxed_4147_; lean_object* v_res_4148_; 
v_sz_boxed_4146_ = lean_unbox_usize(v_sz_4140_);
lean_dec(v_sz_4140_);
v_i_boxed_4147_ = lean_unbox_usize(v_i_4141_);
lean_dec(v_i_4141_);
v_res_4148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(v_stx_4134_, v___x_4135_, v___x_4136_, v___x_4137_, v___x_4138_, v_as_4139_, v_sz_boxed_4146_, v_i_boxed_4147_, v_b_4142_, v___y_4143_, v___y_4144_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
lean_dec_ref(v_as_4139_);
lean_dec(v___x_4138_);
lean_dec_ref(v___x_4136_);
lean_dec_ref(v___x_4135_);
return v_res_4148_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(lean_object* v_init_4149_, lean_object* v_stx_4150_, lean_object* v___x_4151_, lean_object* v___x_4152_, lean_object* v___x_4153_, lean_object* v___x_4154_, lean_object* v_n_4155_, lean_object* v_b_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_){
_start:
{
if (lean_obj_tag(v_n_4155_) == 0)
{
lean_object* v_cs_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; size_t v_sz_4163_; size_t v___x_4164_; lean_object* v___x_4165_; 
v_cs_4160_ = lean_ctor_get(v_n_4155_, 0);
v___x_4161_ = lean_box(0);
v___x_4162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4162_, 0, v___x_4161_);
lean_ctor_set(v___x_4162_, 1, v_b_4156_);
v_sz_4163_ = lean_array_size(v_cs_4160_);
v___x_4164_ = ((size_t)0ULL);
v___x_4165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(v_init_4149_, v_stx_4150_, v___x_4151_, v___x_4152_, v___x_4153_, v___x_4154_, v_cs_4160_, v_sz_4163_, v___x_4164_, v___x_4162_, v___y_4157_, v___y_4158_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4180_; 
v_a_4166_ = lean_ctor_get(v___x_4165_, 0);
v_isSharedCheck_4180_ = !lean_is_exclusive(v___x_4165_);
if (v_isSharedCheck_4180_ == 0)
{
v___x_4168_ = v___x_4165_;
v_isShared_4169_ = v_isSharedCheck_4180_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___x_4165_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4180_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v_fst_4170_; 
v_fst_4170_ = lean_ctor_get(v_a_4166_, 0);
if (lean_obj_tag(v_fst_4170_) == 0)
{
lean_object* v_snd_4171_; lean_object* v___x_4172_; lean_object* v___x_4174_; 
v_snd_4171_ = lean_ctor_get(v_a_4166_, 1);
lean_inc(v_snd_4171_);
lean_dec(v_a_4166_);
v___x_4172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4172_, 0, v_snd_4171_);
if (v_isShared_4169_ == 0)
{
lean_ctor_set(v___x_4168_, 0, v___x_4172_);
v___x_4174_ = v___x_4168_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v___x_4172_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
else
{
lean_object* v_val_4176_; lean_object* v___x_4178_; 
lean_inc_ref(v_fst_4170_);
lean_dec(v_a_4166_);
v_val_4176_ = lean_ctor_get(v_fst_4170_, 0);
lean_inc(v_val_4176_);
lean_dec_ref_known(v_fst_4170_, 1);
if (v_isShared_4169_ == 0)
{
lean_ctor_set(v___x_4168_, 0, v_val_4176_);
v___x_4178_ = v___x_4168_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v_val_4176_);
v___x_4178_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
return v___x_4178_;
}
}
}
}
else
{
lean_object* v_a_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4188_; 
v_a_4181_ = lean_ctor_get(v___x_4165_, 0);
v_isSharedCheck_4188_ = !lean_is_exclusive(v___x_4165_);
if (v_isSharedCheck_4188_ == 0)
{
v___x_4183_ = v___x_4165_;
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
else
{
lean_inc(v_a_4181_);
lean_dec(v___x_4165_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
lean_object* v___x_4186_; 
if (v_isShared_4184_ == 0)
{
v___x_4186_ = v___x_4183_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_a_4181_);
v___x_4186_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
return v___x_4186_;
}
}
}
}
else
{
lean_object* v_vs_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; size_t v_sz_4192_; size_t v___x_4193_; lean_object* v___x_4194_; 
v_vs_4189_ = lean_ctor_get(v_n_4155_, 0);
v___x_4190_ = lean_box(0);
v___x_4191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4190_);
lean_ctor_set(v___x_4191_, 1, v_b_4156_);
v_sz_4192_ = lean_array_size(v_vs_4189_);
v___x_4193_ = ((size_t)0ULL);
v___x_4194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(v_stx_4150_, v___x_4151_, v___x_4152_, v___x_4153_, v___x_4154_, v_vs_4189_, v_sz_4192_, v___x_4193_, v___x_4191_, v___y_4157_, v___y_4158_);
if (lean_obj_tag(v___x_4194_) == 0)
{
lean_object* v_a_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4209_; 
v_a_4195_ = lean_ctor_get(v___x_4194_, 0);
v_isSharedCheck_4209_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4197_ = v___x_4194_;
v_isShared_4198_ = v_isSharedCheck_4209_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_a_4195_);
lean_dec(v___x_4194_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4209_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v_fst_4199_; 
v_fst_4199_ = lean_ctor_get(v_a_4195_, 0);
if (lean_obj_tag(v_fst_4199_) == 0)
{
lean_object* v_snd_4200_; lean_object* v___x_4201_; lean_object* v___x_4203_; 
v_snd_4200_ = lean_ctor_get(v_a_4195_, 1);
lean_inc(v_snd_4200_);
lean_dec(v_a_4195_);
v___x_4201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4201_, 0, v_snd_4200_);
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 0, v___x_4201_);
v___x_4203_ = v___x_4197_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v___x_4201_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
return v___x_4203_;
}
}
else
{
lean_object* v_val_4205_; lean_object* v___x_4207_; 
lean_inc_ref(v_fst_4199_);
lean_dec(v_a_4195_);
v_val_4205_ = lean_ctor_get(v_fst_4199_, 0);
lean_inc(v_val_4205_);
lean_dec_ref_known(v_fst_4199_, 1);
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 0, v_val_4205_);
v___x_4207_ = v___x_4197_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v_val_4205_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
return v___x_4207_;
}
}
}
}
else
{
lean_object* v_a_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4217_; 
v_a_4210_ = lean_ctor_get(v___x_4194_, 0);
v_isSharedCheck_4217_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_4212_ = v___x_4194_;
v_isShared_4213_ = v_isSharedCheck_4217_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_a_4210_);
lean_dec(v___x_4194_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4217_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
lean_object* v___x_4215_; 
if (v_isShared_4213_ == 0)
{
v___x_4215_ = v___x_4212_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v_a_4210_);
v___x_4215_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
return v___x_4215_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(lean_object* v_init_4218_, lean_object* v_stx_4219_, lean_object* v___x_4220_, lean_object* v___x_4221_, lean_object* v___x_4222_, lean_object* v___x_4223_, lean_object* v_as_4224_, size_t v_sz_4225_, size_t v_i_4226_, lean_object* v_b_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_){
_start:
{
uint8_t v___x_4231_; 
v___x_4231_ = lean_usize_dec_lt(v_i_4226_, v_sz_4225_);
if (v___x_4231_ == 0)
{
lean_object* v___x_4232_; 
lean_dec_ref(v___x_4222_);
lean_dec(v_stx_4219_);
v___x_4232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4232_, 0, v_b_4227_);
return v___x_4232_;
}
else
{
lean_object* v_snd_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4267_; 
v_snd_4233_ = lean_ctor_get(v_b_4227_, 1);
v_isSharedCheck_4267_ = !lean_is_exclusive(v_b_4227_);
if (v_isSharedCheck_4267_ == 0)
{
lean_object* v_unused_4268_; 
v_unused_4268_ = lean_ctor_get(v_b_4227_, 0);
lean_dec(v_unused_4268_);
v___x_4235_ = v_b_4227_;
v_isShared_4236_ = v_isSharedCheck_4267_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_snd_4233_);
lean_dec(v_b_4227_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4267_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4237_; lean_object* v_a_4238_; lean_object* v___x_4239_; 
v___x_4237_ = lean_box(0);
v_a_4238_ = lean_array_uget_borrowed(v_as_4224_, v_i_4226_);
lean_inc(v_snd_4233_);
lean_inc_ref(v___x_4222_);
lean_inc(v_stx_4219_);
v___x_4239_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4218_, v_stx_4219_, v___x_4220_, v___x_4221_, v___x_4222_, v___x_4223_, v_a_4238_, v_snd_4233_, v___y_4228_, v___y_4229_);
if (lean_obj_tag(v___x_4239_) == 0)
{
lean_object* v_a_4240_; lean_object* v___x_4242_; uint8_t v_isShared_4243_; uint8_t v_isSharedCheck_4258_; 
v_a_4240_ = lean_ctor_get(v___x_4239_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_4239_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4242_ = v___x_4239_;
v_isShared_4243_ = v_isSharedCheck_4258_;
goto v_resetjp_4241_;
}
else
{
lean_inc(v_a_4240_);
lean_dec(v___x_4239_);
v___x_4242_ = lean_box(0);
v_isShared_4243_ = v_isSharedCheck_4258_;
goto v_resetjp_4241_;
}
v_resetjp_4241_:
{
if (lean_obj_tag(v_a_4240_) == 0)
{
lean_object* v___x_4244_; lean_object* v___x_4246_; 
lean_dec_ref(v___x_4222_);
lean_dec(v_stx_4219_);
v___x_4244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4244_, 0, v_a_4240_);
if (v_isShared_4236_ == 0)
{
lean_ctor_set(v___x_4235_, 0, v___x_4244_);
v___x_4246_ = v___x_4235_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v___x_4244_);
lean_ctor_set(v_reuseFailAlloc_4250_, 1, v_snd_4233_);
v___x_4246_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
lean_object* v___x_4248_; 
if (v_isShared_4243_ == 0)
{
lean_ctor_set(v___x_4242_, 0, v___x_4246_);
v___x_4248_ = v___x_4242_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v___x_4246_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
else
{
lean_object* v_a_4251_; lean_object* v___x_4253_; 
lean_del_object(v___x_4242_);
lean_dec(v_snd_4233_);
v_a_4251_ = lean_ctor_get(v_a_4240_, 0);
lean_inc(v_a_4251_);
lean_dec_ref_known(v_a_4240_, 1);
if (v_isShared_4236_ == 0)
{
lean_ctor_set(v___x_4235_, 1, v_a_4251_);
lean_ctor_set(v___x_4235_, 0, v___x_4237_);
v___x_4253_ = v___x_4235_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v___x_4237_);
lean_ctor_set(v_reuseFailAlloc_4257_, 1, v_a_4251_);
v___x_4253_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
size_t v___x_4254_; size_t v___x_4255_; 
v___x_4254_ = ((size_t)1ULL);
v___x_4255_ = lean_usize_add(v_i_4226_, v___x_4254_);
v_i_4226_ = v___x_4255_;
v_b_4227_ = v___x_4253_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4266_; 
lean_del_object(v___x_4235_);
lean_dec(v_snd_4233_);
lean_dec_ref(v___x_4222_);
lean_dec(v_stx_4219_);
v_a_4259_ = lean_ctor_get(v___x_4239_, 0);
v_isSharedCheck_4266_ = !lean_is_exclusive(v___x_4239_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4261_ = v___x_4239_;
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_a_4259_);
lean_dec(v___x_4239_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v___x_4264_; 
if (v_isShared_4262_ == 0)
{
v___x_4264_ = v___x_4261_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_a_4259_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3___boxed(lean_object* v_init_4269_, lean_object* v_stx_4270_, lean_object* v___x_4271_, lean_object* v___x_4272_, lean_object* v___x_4273_, lean_object* v___x_4274_, lean_object* v_as_4275_, lean_object* v_sz_4276_, lean_object* v_i_4277_, lean_object* v_b_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_){
_start:
{
size_t v_sz_boxed_4282_; size_t v_i_boxed_4283_; lean_object* v_res_4284_; 
v_sz_boxed_4282_ = lean_unbox_usize(v_sz_4276_);
lean_dec(v_sz_4276_);
v_i_boxed_4283_ = lean_unbox_usize(v_i_4277_);
lean_dec(v_i_4277_);
v_res_4284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(v_init_4269_, v_stx_4270_, v___x_4271_, v___x_4272_, v___x_4273_, v___x_4274_, v_as_4275_, v_sz_boxed_4282_, v_i_boxed_4283_, v_b_4278_, v___y_4279_, v___y_4280_);
lean_dec(v___y_4280_);
lean_dec_ref(v___y_4279_);
lean_dec_ref(v_as_4275_);
lean_dec(v___x_4274_);
lean_dec_ref(v___x_4272_);
lean_dec_ref(v___x_4271_);
return v_res_4284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2___boxed(lean_object* v_init_4285_, lean_object* v_stx_4286_, lean_object* v___x_4287_, lean_object* v___x_4288_, lean_object* v___x_4289_, lean_object* v___x_4290_, lean_object* v_n_4291_, lean_object* v_b_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_){
_start:
{
lean_object* v_res_4296_; 
v_res_4296_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4285_, v_stx_4286_, v___x_4287_, v___x_4288_, v___x_4289_, v___x_4290_, v_n_4291_, v_b_4292_, v___y_4293_, v___y_4294_);
lean_dec(v___y_4294_);
lean_dec_ref(v___y_4293_);
lean_dec_ref(v_n_4291_);
lean_dec(v___x_4290_);
lean_dec_ref(v___x_4288_);
lean_dec_ref(v___x_4287_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(lean_object* v___x_4297_, lean_object* v___x_4298_, lean_object* v_stx_4299_, lean_object* v___x_4300_, lean_object* v___x_4301_, lean_object* v_t_4302_, lean_object* v_init_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_){
_start:
{
lean_object* v_root_4307_; lean_object* v_tail_4308_; lean_object* v___x_4309_; 
v_root_4307_ = lean_ctor_get(v_t_4302_, 0);
v_tail_4308_ = lean_ctor_get(v_t_4302_, 1);
lean_inc_ref(v___x_4297_);
lean_inc(v_stx_4299_);
v___x_4309_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4303_, v_stx_4299_, v___x_4300_, v___x_4301_, v___x_4297_, v___x_4298_, v_root_4307_, v_init_4303_, v___y_4304_, v___y_4305_);
if (lean_obj_tag(v___x_4309_) == 0)
{
lean_object* v_a_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4346_; 
v_a_4310_ = lean_ctor_get(v___x_4309_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4309_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4312_ = v___x_4309_;
v_isShared_4313_ = v_isSharedCheck_4346_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_a_4310_);
lean_dec(v___x_4309_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4346_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
if (lean_obj_tag(v_a_4310_) == 0)
{
lean_object* v_a_4314_; lean_object* v___x_4316_; 
lean_dec(v_stx_4299_);
lean_dec_ref(v___x_4297_);
v_a_4314_ = lean_ctor_get(v_a_4310_, 0);
lean_inc(v_a_4314_);
lean_dec_ref_known(v_a_4310_, 1);
if (v_isShared_4313_ == 0)
{
lean_ctor_set(v___x_4312_, 0, v_a_4314_);
v___x_4316_ = v___x_4312_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v_a_4314_);
v___x_4316_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
return v___x_4316_;
}
}
else
{
lean_object* v_a_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; size_t v_sz_4321_; size_t v___x_4322_; lean_object* v___x_4323_; 
lean_del_object(v___x_4312_);
v_a_4318_ = lean_ctor_get(v_a_4310_, 0);
lean_inc(v_a_4318_);
lean_dec_ref_known(v_a_4310_, 1);
v___x_4319_ = lean_box(0);
v___x_4320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4320_, 0, v___x_4319_);
lean_ctor_set(v___x_4320_, 1, v_a_4318_);
v_sz_4321_ = lean_array_size(v_tail_4308_);
v___x_4322_ = ((size_t)0ULL);
v___x_4323_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(v_stx_4299_, v___x_4300_, v___x_4301_, v___x_4297_, v___x_4298_, v_tail_4308_, v_sz_4321_, v___x_4322_, v___x_4320_, v___y_4304_, v___y_4305_);
if (lean_obj_tag(v___x_4323_) == 0)
{
lean_object* v_a_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4337_; 
v_a_4324_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4337_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4337_ == 0)
{
v___x_4326_ = v___x_4323_;
v_isShared_4327_ = v_isSharedCheck_4337_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_a_4324_);
lean_dec(v___x_4323_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4337_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v_fst_4328_; 
v_fst_4328_ = lean_ctor_get(v_a_4324_, 0);
if (lean_obj_tag(v_fst_4328_) == 0)
{
lean_object* v_snd_4329_; lean_object* v___x_4331_; 
v_snd_4329_ = lean_ctor_get(v_a_4324_, 1);
lean_inc(v_snd_4329_);
lean_dec(v_a_4324_);
if (v_isShared_4327_ == 0)
{
lean_ctor_set(v___x_4326_, 0, v_snd_4329_);
v___x_4331_ = v___x_4326_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v_snd_4329_);
v___x_4331_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
return v___x_4331_;
}
}
else
{
lean_object* v_val_4333_; lean_object* v___x_4335_; 
lean_inc_ref(v_fst_4328_);
lean_dec(v_a_4324_);
v_val_4333_ = lean_ctor_get(v_fst_4328_, 0);
lean_inc(v_val_4333_);
lean_dec_ref_known(v_fst_4328_, 1);
if (v_isShared_4327_ == 0)
{
lean_ctor_set(v___x_4326_, 0, v_val_4333_);
v___x_4335_ = v___x_4326_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4336_; 
v_reuseFailAlloc_4336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4336_, 0, v_val_4333_);
v___x_4335_ = v_reuseFailAlloc_4336_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
return v___x_4335_;
}
}
}
}
else
{
lean_object* v_a_4338_; lean_object* v___x_4340_; uint8_t v_isShared_4341_; uint8_t v_isSharedCheck_4345_; 
v_a_4338_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4345_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4345_ == 0)
{
v___x_4340_ = v___x_4323_;
v_isShared_4341_ = v_isSharedCheck_4345_;
goto v_resetjp_4339_;
}
else
{
lean_inc(v_a_4338_);
lean_dec(v___x_4323_);
v___x_4340_ = lean_box(0);
v_isShared_4341_ = v_isSharedCheck_4345_;
goto v_resetjp_4339_;
}
v_resetjp_4339_:
{
lean_object* v___x_4343_; 
if (v_isShared_4341_ == 0)
{
v___x_4343_ = v___x_4340_;
goto v_reusejp_4342_;
}
else
{
lean_object* v_reuseFailAlloc_4344_; 
v_reuseFailAlloc_4344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4344_, 0, v_a_4338_);
v___x_4343_ = v_reuseFailAlloc_4344_;
goto v_reusejp_4342_;
}
v_reusejp_4342_:
{
return v___x_4343_;
}
}
}
}
}
}
else
{
lean_object* v_a_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4354_; 
lean_dec(v_stx_4299_);
lean_dec_ref(v___x_4297_);
v_a_4347_ = lean_ctor_get(v___x_4309_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4309_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4349_ = v___x_4309_;
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_a_4347_);
lean_dec(v___x_4309_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v___x_4352_; 
if (v_isShared_4350_ == 0)
{
v___x_4352_ = v___x_4349_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_a_4347_);
v___x_4352_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
return v___x_4352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2___boxed(lean_object* v___x_4355_, lean_object* v___x_4356_, lean_object* v_stx_4357_, lean_object* v___x_4358_, lean_object* v___x_4359_, lean_object* v_t_4360_, lean_object* v_init_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_){
_start:
{
lean_object* v_res_4365_; 
v_res_4365_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___x_4355_, v___x_4356_, v_stx_4357_, v___x_4358_, v___x_4359_, v_t_4360_, v_init_4361_, v___y_4362_, v___y_4363_);
lean_dec(v___y_4363_);
lean_dec_ref(v___y_4362_);
lean_dec_ref(v_t_4360_);
lean_dec_ref(v___x_4359_);
lean_dec_ref(v___x_4358_);
lean_dec(v___x_4356_);
return v_res_4365_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4367_; lean_object* v___x_4368_; 
v___x_4367_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__0));
v___x_4368_ = l_Lean_stringToMessageData(v___x_4367_);
return v___x_4368_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4372_; lean_object* v___x_4373_; 
v___x_4372_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__4));
v___x_4373_ = l_Lean_stringToMessageData(v___x_4372_);
return v___x_4373_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; 
v___x_4375_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__6));
v___x_4376_ = l_Lean_stringToMessageData(v___x_4375_);
return v___x_4376_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9(void){
_start:
{
lean_object* v___x_4378_; lean_object* v___x_4379_; 
v___x_4378_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__8));
v___x_4379_ = l_Lean_stringToMessageData(v___x_4378_);
return v___x_4379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(lean_object* v_stx_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_){
_start:
{
lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v_scopes_4389_; lean_object* v___x_4390_; lean_object* v_opts_4391_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; uint8_t v___y_4415_; lean_object* v___y_4416_; lean_object* v___y_4417_; lean_object* v___y_4423_; uint8_t v___y_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4432_; lean_object* v___y_4433_; uint8_t v___y_4434_; uint8_t v___y_4435_; lean_object* v___y_4436_; uint8_t v___y_4445_; lean_object* v___y_4446_; uint8_t v___y_4447_; uint8_t v___y_4448_; lean_object* v___y_4449_; lean_object* v___y_4450_; uint8_t v___y_4459_; uint8_t v___y_4460_; uint8_t v___y_4461_; uint8_t v___y_4495_; lean_object* v___x_4502_; uint8_t v___x_4503_; 
v___x_4387_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4388_ = lean_st_ref_get(v___y_4382_);
v_scopes_4389_ = lean_ctor_get(v___x_4388_, 2);
lean_inc(v_scopes_4389_);
lean_dec(v___x_4388_);
v___x_4390_ = l_List_head_x21___redArg(v___x_4387_, v_scopes_4389_);
lean_dec(v_scopes_4389_);
v_opts_4391_ = lean_ctor_get(v___x_4390_, 1);
lean_inc_ref(v_opts_4391_);
lean_dec(v___x_4390_);
v___x_4502_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_4503_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4391_, v___x_4502_);
if (v___x_4503_ == 0)
{
lean_object* v___x_4504_; uint8_t v___x_4505_; 
v___x_4504_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_4505_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4391_, v___x_4504_);
v___y_4495_ = v___x_4505_;
goto v___jp_4494_;
}
else
{
v___y_4495_ = v___x_4503_;
goto v___jp_4494_;
}
v___jp_4384_:
{
lean_object* v___x_4385_; lean_object* v___x_4386_; 
v___x_4385_ = lean_box(0);
v___x_4386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4386_, 0, v___x_4385_);
return v___x_4386_;
}
v___jp_4392_:
{
lean_object* v___x_4397_; lean_object* v_line_4398_; lean_object* v___x_4399_; lean_object* v_messages_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v_a_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; 
lean_inc_ref_n(v___y_4393_, 2);
v___x_4397_ = l_Lean_FileMap_toPosition(v___y_4393_, v___y_4396_);
lean_dec(v___y_4396_);
v_line_4398_ = lean_ctor_get(v___x_4397_, 0);
lean_inc(v_line_4398_);
lean_dec_ref(v___x_4397_);
v___x_4399_ = lean_st_ref_get(v___y_4394_);
v_messages_4400_ = lean_ctor_get(v___x_4399_, 1);
lean_inc_ref(v_messages_4400_);
lean_dec(v___x_4399_);
v___x_4401_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_4400_);
v___x_4402_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_4394_);
v_a_4403_ = lean_ctor_get(v___x_4402_, 0);
lean_inc(v_a_4403_);
lean_dec_ref(v___x_4402_);
v___x_4404_ = lean_box(0);
v___x_4405_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___y_4393_, v_line_4398_, v_stx_4380_, v_opts_4391_, v___x_4401_, v_a_4403_, v___x_4404_, v___y_4395_, v___y_4394_);
lean_dec(v_a_4403_);
lean_dec_ref(v___x_4401_);
lean_dec_ref(v_opts_4391_);
lean_dec(v_line_4398_);
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4412_; 
v_isSharedCheck_4412_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4412_ == 0)
{
lean_object* v_unused_4413_; 
v_unused_4413_ = lean_ctor_get(v___x_4405_, 0);
lean_dec(v_unused_4413_);
v___x_4407_ = v___x_4405_;
v_isShared_4408_ = v_isSharedCheck_4412_;
goto v_resetjp_4406_;
}
else
{
lean_dec(v___x_4405_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4412_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
lean_object* v___x_4410_; 
if (v_isShared_4408_ == 0)
{
lean_ctor_set(v___x_4407_, 0, v___x_4404_);
v___x_4410_ = v___x_4407_;
goto v_reusejp_4409_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v___x_4404_);
v___x_4410_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4409_;
}
v_reusejp_4409_:
{
return v___x_4410_;
}
}
}
else
{
return v___x_4405_;
}
}
v___jp_4414_:
{
lean_object* v_fileMap_4418_; lean_object* v___x_4419_; 
v_fileMap_4418_ = lean_ctor_get(v___y_4416_, 1);
v___x_4419_ = l_Lean_Syntax_getPos_x3f(v_stx_4380_, v___y_4415_);
if (lean_obj_tag(v___x_4419_) == 0)
{
lean_object* v___x_4420_; 
v___x_4420_ = lean_unsigned_to_nat(0u);
v___y_4393_ = v_fileMap_4418_;
v___y_4394_ = v___y_4417_;
v___y_4395_ = v___y_4416_;
v___y_4396_ = v___x_4420_;
goto v___jp_4392_;
}
else
{
lean_object* v_val_4421_; 
v_val_4421_ = lean_ctor_get(v___x_4419_, 0);
lean_inc(v_val_4421_);
lean_dec_ref_known(v___x_4419_, 1);
v___y_4393_ = v_fileMap_4418_;
v___y_4394_ = v___y_4417_;
v___y_4395_ = v___y_4416_;
v___y_4396_ = v_val_4421_;
goto v___jp_4392_;
}
}
v___jp_4422_:
{
lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; 
lean_inc_ref(v___y_4426_);
v___x_4427_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4427_, 0, v___y_4426_);
v___x_4428_ = l_Lean_MessageData_ofFormat(v___x_4427_);
v___x_4429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4429_, 0, v___y_4425_);
lean_ctor_set(v___x_4429_, 1, v___x_4428_);
lean_inc(v___y_4423_);
v___x_4430_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___y_4423_, v___x_4429_, v___y_4381_, v___y_4382_);
if (lean_obj_tag(v___x_4430_) == 0)
{
lean_dec_ref_known(v___x_4430_, 1);
v___y_4415_ = v___y_4424_;
v___y_4416_ = v___y_4381_;
v___y_4417_ = v___y_4382_;
goto v___jp_4414_;
}
else
{
lean_dec_ref(v_opts_4391_);
lean_dec(v_stx_4380_);
return v___x_4430_;
}
}
v___jp_4431_:
{
lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; 
lean_inc_ref(v___y_4436_);
v___x_4437_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4437_, 0, v___y_4436_);
v___x_4438_ = l_Lean_MessageData_ofFormat(v___x_4437_);
v___x_4439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4439_, 0, v___y_4432_);
lean_ctor_set(v___x_4439_, 1, v___x_4438_);
v___x_4440_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1);
v___x_4441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4441_, 0, v___x_4439_);
lean_ctor_set(v___x_4441_, 1, v___x_4440_);
if (v___y_4435_ == 0)
{
lean_object* v___x_4442_; 
v___x_4442_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4423_ = v___y_4433_;
v___y_4424_ = v___y_4434_;
v___y_4425_ = v___x_4441_;
v___y_4426_ = v___x_4442_;
goto v___jp_4422_;
}
else
{
lean_object* v___x_4443_; 
v___x_4443_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4423_ = v___y_4433_;
v___y_4424_ = v___y_4434_;
v___y_4425_ = v___x_4441_;
v___y_4426_ = v___x_4443_;
goto v___jp_4422_;
}
}
v___jp_4444_:
{
lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; 
lean_inc_ref(v___y_4450_);
v___x_4451_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4451_, 0, v___y_4450_);
v___x_4452_ = l_Lean_MessageData_ofFormat(v___x_4451_);
lean_inc_ref(v___y_4449_);
v___x_4453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4453_, 0, v___y_4449_);
lean_ctor_set(v___x_4453_, 1, v___x_4452_);
v___x_4454_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5);
v___x_4455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4455_, 0, v___x_4453_);
lean_ctor_set(v___x_4455_, 1, v___x_4454_);
if (v___y_4445_ == 0)
{
lean_object* v___x_4456_; 
v___x_4456_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4432_ = v___x_4455_;
v___y_4433_ = v___y_4446_;
v___y_4434_ = v___y_4447_;
v___y_4435_ = v___y_4448_;
v___y_4436_ = v___x_4456_;
goto v___jp_4431_;
}
else
{
lean_object* v___x_4457_; 
v___x_4457_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4432_ = v___x_4455_;
v___y_4433_ = v___y_4446_;
v___y_4434_ = v___y_4447_;
v___y_4435_ = v___y_4448_;
v___y_4436_ = v___x_4457_;
goto v___jp_4431_;
}
}
v___jp_4458_:
{
lean_object* v___x_4462_; lean_object* v_a_4463_; uint8_t v___x_4464_; 
v___x_4462_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(v_stx_4380_, v___y_4381_, v___y_4382_);
v_a_4463_ = lean_ctor_get(v___x_4462_, 0);
lean_inc(v_a_4463_);
lean_dec_ref(v___x_4462_);
v___x_4464_ = lean_unbox(v_a_4463_);
if (v___x_4464_ == 0)
{
lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v_scopes_4469_; lean_object* v___x_4470_; lean_object* v_opts_4471_; uint8_t v_hasTrace_4472_; 
v___x_4465_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4466_ = l_Lean_inheritedTraceOptions;
v___x_4467_ = lean_st_ref_get(v___x_4466_);
v___x_4468_ = lean_st_ref_get(v___y_4382_);
v_scopes_4469_ = lean_ctor_get(v___x_4468_, 2);
lean_inc(v_scopes_4469_);
lean_dec(v___x_4468_);
v___x_4470_ = l_List_head_x21___redArg(v___x_4387_, v_scopes_4469_);
lean_dec(v_scopes_4469_);
v_opts_4471_ = lean_ctor_get(v___x_4470_, 1);
lean_inc_ref(v_opts_4471_);
lean_dec(v___x_4470_);
v_hasTrace_4472_ = lean_ctor_get_uint8(v_opts_4471_, sizeof(void*)*1);
if (v_hasTrace_4472_ == 0)
{
uint8_t v___x_4473_; 
lean_dec_ref(v_opts_4471_);
lean_dec(v___x_4467_);
v___x_4473_ = lean_unbox(v_a_4463_);
lean_dec(v_a_4463_);
v___y_4415_ = v___x_4473_;
v___y_4416_ = v___y_4381_;
v___y_4417_ = v___y_4382_;
goto v___jp_4414_;
}
else
{
lean_object* v___x_4474_; uint8_t v___x_4475_; 
v___x_4474_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_4475_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4467_, v_opts_4471_, v___x_4474_);
lean_dec_ref(v_opts_4471_);
lean_dec(v___x_4467_);
if (v___x_4475_ == 0)
{
uint8_t v___x_4476_; 
v___x_4476_ = lean_unbox(v_a_4463_);
lean_dec(v_a_4463_);
v___y_4415_ = v___x_4476_;
v___y_4416_ = v___y_4381_;
v___y_4417_ = v___y_4382_;
goto v___jp_4414_;
}
else
{
lean_object* v___x_4477_; 
v___x_4477_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7);
if (v___y_4460_ == 0)
{
lean_object* v___x_4478_; uint8_t v___x_4479_; 
v___x_4478_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___x_4479_ = lean_unbox(v_a_4463_);
lean_dec(v_a_4463_);
v___y_4445_ = v___y_4459_;
v___y_4446_ = v___x_4465_;
v___y_4447_ = v___x_4479_;
v___y_4448_ = v___y_4461_;
v___y_4449_ = v___x_4477_;
v___y_4450_ = v___x_4478_;
goto v___jp_4444_;
}
else
{
lean_object* v___x_4480_; uint8_t v___x_4481_; 
v___x_4480_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___x_4481_ = lean_unbox(v_a_4463_);
lean_dec(v_a_4463_);
v___y_4445_ = v___y_4459_;
v___y_4446_ = v___x_4465_;
v___y_4447_ = v___x_4481_;
v___y_4448_ = v___y_4461_;
v___y_4449_ = v___x_4477_;
v___y_4450_ = v___x_4480_;
goto v___jp_4444_;
}
}
}
}
else
{
lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v_scopes_4486_; lean_object* v___x_4487_; lean_object* v_opts_4488_; uint8_t v_hasTrace_4489_; 
lean_dec(v_a_4463_);
lean_dec_ref(v_opts_4391_);
lean_dec(v_stx_4380_);
v___x_4482_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4483_ = l_Lean_inheritedTraceOptions;
v___x_4484_ = lean_st_ref_get(v___x_4483_);
v___x_4485_ = lean_st_ref_get(v___y_4382_);
v_scopes_4486_ = lean_ctor_get(v___x_4485_, 2);
lean_inc(v_scopes_4486_);
lean_dec(v___x_4485_);
v___x_4487_ = l_List_head_x21___redArg(v___x_4387_, v_scopes_4486_);
lean_dec(v_scopes_4486_);
v_opts_4488_ = lean_ctor_get(v___x_4487_, 1);
lean_inc_ref(v_opts_4488_);
lean_dec(v___x_4487_);
v_hasTrace_4489_ = lean_ctor_get_uint8(v_opts_4488_, sizeof(void*)*1);
if (v_hasTrace_4489_ == 0)
{
lean_dec_ref(v_opts_4488_);
lean_dec(v___x_4484_);
goto v___jp_4384_;
}
else
{
lean_object* v___x_4490_; uint8_t v___x_4491_; 
v___x_4490_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_4491_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4484_, v_opts_4488_, v___x_4490_);
lean_dec_ref(v_opts_4488_);
lean_dec(v___x_4484_);
if (v___x_4491_ == 0)
{
goto v___jp_4384_;
}
else
{
lean_object* v___x_4492_; lean_object* v___x_4493_; 
v___x_4492_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9);
v___x_4493_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_4482_, v___x_4492_, v___y_4381_, v___y_4382_);
if (lean_obj_tag(v___x_4493_) == 0)
{
lean_dec_ref_known(v___x_4493_, 1);
goto v___jp_4384_;
}
else
{
return v___x_4493_;
}
}
}
}
}
v___jp_4494_:
{
lean_object* v___x_4496_; uint8_t v___x_4497_; lean_object* v___x_4498_; uint8_t v___x_4499_; 
v___x_4496_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
v___x_4497_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4391_, v___x_4496_);
v___x_4498_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v___x_4499_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4391_, v___x_4498_);
if (v___y_4495_ == 0)
{
if (v___x_4497_ == 0)
{
if (v___x_4499_ == 0)
{
lean_object* v___x_4500_; lean_object* v___x_4501_; 
lean_dec_ref(v_opts_4391_);
lean_dec(v_stx_4380_);
v___x_4500_ = lean_box(0);
v___x_4501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4501_, 0, v___x_4500_);
return v___x_4501_;
}
else
{
v___y_4459_ = v___x_4497_;
v___y_4460_ = v___y_4495_;
v___y_4461_ = v___x_4499_;
goto v___jp_4458_;
}
}
else
{
v___y_4459_ = v___x_4497_;
v___y_4460_ = v___y_4495_;
v___y_4461_ = v___x_4499_;
goto v___jp_4458_;
}
}
else
{
v___y_4459_ = v___x_4497_;
v___y_4460_ = v___y_4495_;
v___y_4461_ = v___x_4499_;
goto v___jp_4458_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___boxed(lean_object* v_stx_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_){
_start:
{
lean_object* v_res_4510_; 
v_res_4510_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(v_stx_4506_, v___y_4507_, v___y_4508_);
lean_dec(v___y_4508_);
lean_dec_ref(v___y_4507_);
return v_res_4510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4523_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook));
v___x_4524_ = l_Lean_Elab_Command_addLinter(v___x_4523_);
return v___x_4524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2____boxed(lean_object* v_a_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_();
return v_res_4526_;
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
