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
lean_object* v___x_336_; uint8_t v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v_fileName_363_; lean_object* v_fileMap_364_; lean_object* v_ref_365_; lean_object* v_cancelTk_x3f_366_; lean_object* v_a_368_; lean_object* v_a_375_; lean_object* v_currNamespace_377_; lean_object* v_openDecls_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v_env_384_; lean_object* v___x_385_; lean_object* v___y_387_; uint8_t v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___y_479_; uint8_t v___y_480_; uint8_t v___y_481_; lean_object* v___x_501_; uint8_t v___x_502_; lean_object* v___y_504_; lean_object* v___y_505_; uint8_t v___y_535_; uint8_t v___x_555_; 
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
v___x_501_ = l_Lean_diagnostics;
v___x_502_ = lean_uint8_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23);
v___x_555_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_384_);
lean_dec_ref(v_env_384_);
if (v___x_555_ == 0)
{
if (v___x_502_ == 0)
{
lean_inc(v___x_359_);
v___y_504_ = v___x_383_;
v___y_505_ = v___x_359_;
goto v___jp_503_;
}
else
{
v___y_535_ = v___x_555_;
goto v___jp_534_;
}
}
else
{
v___y_535_ = v___x_502_;
goto v___jp_534_;
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
lean_object* v___x_391_; lean_object* v_fileName_392_; lean_object* v_fileMap_393_; lean_object* v_currRecDepth_394_; lean_object* v_ref_395_; lean_object* v_currNamespace_396_; lean_object* v_openDecls_397_; lean_object* v_initHeartbeats_398_; lean_object* v_maxHeartbeats_399_; lean_object* v_quotContext_400_; lean_object* v_currMacroScope_401_; lean_object* v_cancelTk_x3f_402_; uint8_t v_suppressElabErrors_403_; lean_object* v_inheritedTraceOptions_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_473_; 
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
v_isSharedCheck_473_ = !lean_is_exclusive(v___y_389_);
if (v_isSharedCheck_473_ == 0)
{
lean_object* v_unused_474_; lean_object* v_unused_475_; 
v_unused_474_ = lean_ctor_get(v___y_389_, 4);
lean_dec(v_unused_474_);
v_unused_475_ = lean_ctor_get(v___y_389_, 2);
lean_dec(v_unused_475_);
v___x_406_ = v___y_389_;
v_isShared_407_ = v_isSharedCheck_473_;
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
v_isShared_407_ = v_isSharedCheck_473_;
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
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_fileName_392_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v_fileMap_393_);
lean_ctor_set(v_reuseFailAlloc_472_, 2, v_opts_330_);
lean_ctor_set(v_reuseFailAlloc_472_, 3, v_currRecDepth_394_);
lean_ctor_set(v_reuseFailAlloc_472_, 4, v___x_408_);
lean_ctor_set(v_reuseFailAlloc_472_, 5, v_ref_395_);
lean_ctor_set(v_reuseFailAlloc_472_, 6, v_currNamespace_396_);
lean_ctor_set(v_reuseFailAlloc_472_, 7, v_openDecls_397_);
lean_ctor_set(v_reuseFailAlloc_472_, 8, v_initHeartbeats_398_);
lean_ctor_set(v_reuseFailAlloc_472_, 9, v_maxHeartbeats_399_);
lean_ctor_set(v_reuseFailAlloc_472_, 10, v_quotContext_400_);
lean_ctor_set(v_reuseFailAlloc_472_, 11, v_currMacroScope_401_);
lean_ctor_set(v_reuseFailAlloc_472_, 12, v_cancelTk_x3f_402_);
lean_ctor_set(v_reuseFailAlloc_472_, 13, v_inheritedTraceOptions_404_);
lean_ctor_set_uint8(v_reuseFailAlloc_472_, sizeof(void*)*14 + 1, v_suppressElabErrors_403_);
v___x_410_ = v_reuseFailAlloc_472_;
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
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_456_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_456_ == 0)
{
v___x_414_ = v___x_411_;
v_isShared_415_ = v_isSharedCheck_456_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_456_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v_traceState_419_; lean_object* v_traceState_420_; lean_object* v_env_421_; lean_object* v_messages_422_; lean_object* v_scopes_423_; lean_object* v_usedQuotCtxts_424_; lean_object* v_nextMacroScope_425_; lean_object* v_maxRecDepth_426_; lean_object* v_ngen_427_; lean_object* v_auxDeclNGen_428_; lean_object* v_infoState_429_; lean_object* v_snapshotTasks_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_454_; 
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
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_454_ == 0)
{
lean_object* v_unused_455_; 
v_unused_455_ = lean_ctor_get(v___x_418_, 9);
lean_dec(v_unused_455_);
v___x_432_ = v___x_418_;
v_isShared_433_ = v_isSharedCheck_454_;
goto v_resetjp_431_;
}
else
{
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
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_454_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v_messages_434_; uint64_t v_tid_435_; lean_object* v_traces_436_; lean_object* v_traces_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_453_; 
v_messages_434_ = lean_ctor_get(v___x_417_, 6);
lean_inc_ref(v_messages_434_);
lean_dec(v___x_417_);
v_tid_435_ = lean_ctor_get_uint64(v_traceState_419_, sizeof(void*)*1);
v_traces_436_ = lean_ctor_get(v_traceState_419_, 0);
lean_inc_ref(v_traces_436_);
lean_dec_ref(v_traceState_419_);
v_traces_437_ = lean_ctor_get(v_traceState_420_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v_traceState_420_);
if (v_isSharedCheck_453_ == 0)
{
v___x_439_ = v_traceState_420_;
v_isShared_440_ = v_isSharedCheck_453_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_traces_437_);
lean_dec(v_traceState_420_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_453_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_441_ = l_Lean_MessageLog_append(v_messages_422_, v_messages_434_);
v___x_442_ = l_Lean_PersistentArray_append___redArg(v_traces_436_, v_traces_437_);
lean_dec_ref(v_traces_437_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_442_);
v___x_444_ = v___x_439_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_452_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_446_; 
lean_ctor_set_uint64(v___x_444_, sizeof(void*)*1, v_tid_435_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 9, v___x_444_);
lean_ctor_set(v___x_432_, 1, v___x_441_);
v___x_446_ = v___x_432_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_env_421_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v___x_441_);
lean_ctor_set(v_reuseFailAlloc_451_, 2, v_scopes_423_);
lean_ctor_set(v_reuseFailAlloc_451_, 3, v_usedQuotCtxts_424_);
lean_ctor_set(v_reuseFailAlloc_451_, 4, v_nextMacroScope_425_);
lean_ctor_set(v_reuseFailAlloc_451_, 5, v_maxRecDepth_426_);
lean_ctor_set(v_reuseFailAlloc_451_, 6, v_ngen_427_);
lean_ctor_set(v_reuseFailAlloc_451_, 7, v_auxDeclNGen_428_);
lean_ctor_set(v_reuseFailAlloc_451_, 8, v_infoState_429_);
lean_ctor_set(v_reuseFailAlloc_451_, 9, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_451_, 10, v_snapshotTasks_430_);
v___x_446_ = v_reuseFailAlloc_451_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_447_ = lean_st_ref_set(v_a_334_, v___x_446_);
if (v_isShared_415_ == 0)
{
v___x_449_ = v___x_414_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_a_412_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_457_; 
lean_dec(v___x_391_);
lean_dec(v___x_359_);
v_a_457_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_457_);
lean_dec_ref_known(v___x_411_, 1);
if (lean_obj_tag(v_a_457_) == 0)
{
lean_object* v_msg_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v_msg_458_ = lean_ctor_get(v_a_457_, 1);
lean_inc_ref(v_msg_458_);
lean_dec_ref_known(v_a_457_, 2);
v___x_459_ = l_Lean_MessageData_toString(v_msg_458_);
v___x_460_ = lean_mk_io_user_error(v___x_459_);
v_a_368_ = v___x_460_;
goto v___jp_367_;
}
else
{
lean_object* v_id_461_; lean_object* v___x_462_; 
v_id_461_ = lean_ctor_get(v_a_457_, 0);
lean_inc(v_id_461_);
lean_dec_ref_known(v_a_457_, 2);
v___x_462_ = l_Lean_InternalExceptionId_getName(v_id_461_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
lean_dec(v_id_461_);
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref_known(v___x_462_, 1);
v___x_464_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20));
v___x_465_ = l_Lean_Name_toString(v_a_463_, v___x_339_);
v___x_466_ = lean_string_append(v___x_464_, v___x_465_);
lean_dec_ref(v___x_465_);
v_a_375_ = v___x_466_;
goto v___jp_374_;
}
else
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
lean_dec_ref_known(v___x_462_, 1);
v___x_467_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21));
v___x_468_ = l_Nat_reprFast(v_id_461_);
v___x_469_ = lean_string_append(v___x_467_, v___x_468_);
lean_dec_ref(v___x_468_);
v___x_470_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__22));
v___x_471_ = lean_string_append(v___x_469_, v___x_470_);
v_a_375_ = v___x_471_;
goto v___jp_374_;
}
}
}
}
}
}
v___jp_476_:
{
if (v___y_481_ == 0)
{
lean_object* v___x_482_; lean_object* v_env_483_; lean_object* v_nextMacroScope_484_; lean_object* v_ngen_485_; lean_object* v_auxDeclNGen_486_; lean_object* v_traceState_487_; lean_object* v_messages_488_; lean_object* v_infoState_489_; lean_object* v_snapshotTasks_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_499_; 
v___x_482_ = lean_st_ref_take(v___y_478_);
v_env_483_ = lean_ctor_get(v___x_482_, 0);
v_nextMacroScope_484_ = lean_ctor_get(v___x_482_, 1);
v_ngen_485_ = lean_ctor_get(v___x_482_, 2);
v_auxDeclNGen_486_ = lean_ctor_get(v___x_482_, 3);
v_traceState_487_ = lean_ctor_get(v___x_482_, 4);
v_messages_488_ = lean_ctor_get(v___x_482_, 6);
v_infoState_489_ = lean_ctor_get(v___x_482_, 7);
v_snapshotTasks_490_ = lean_ctor_get(v___x_482_, 8);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_499_ == 0)
{
lean_object* v_unused_500_; 
v_unused_500_ = lean_ctor_get(v___x_482_, 5);
lean_dec(v_unused_500_);
v___x_492_ = v___x_482_;
v_isShared_493_ = v_isSharedCheck_499_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_snapshotTasks_490_);
lean_inc(v_infoState_489_);
lean_inc(v_messages_488_);
lean_inc(v_traceState_487_);
lean_inc(v_auxDeclNGen_486_);
lean_inc(v_ngen_485_);
lean_inc(v_nextMacroScope_484_);
lean_inc(v_env_483_);
lean_dec(v___x_482_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_499_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_494_; lean_object* v___x_496_; 
v___x_494_ = l_Lean_Kernel_enableDiag(v_env_483_, v___y_480_);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 5, v___x_348_);
lean_ctor_set(v___x_492_, 0, v___x_494_);
v___x_496_ = v___x_492_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_494_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_nextMacroScope_484_);
lean_ctor_set(v_reuseFailAlloc_498_, 2, v_ngen_485_);
lean_ctor_set(v_reuseFailAlloc_498_, 3, v_auxDeclNGen_486_);
lean_ctor_set(v_reuseFailAlloc_498_, 4, v_traceState_487_);
lean_ctor_set(v_reuseFailAlloc_498_, 5, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_498_, 6, v_messages_488_);
lean_ctor_set(v_reuseFailAlloc_498_, 7, v_infoState_489_);
lean_ctor_set(v_reuseFailAlloc_498_, 8, v_snapshotTasks_490_);
v___x_496_ = v_reuseFailAlloc_498_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
lean_object* v___x_497_; 
v___x_497_ = lean_st_ref_set(v___y_478_, v___x_496_);
v___y_387_ = v___y_477_;
v___y_388_ = v___y_480_;
v___y_389_ = v___y_479_;
v___y_390_ = v___y_478_;
goto v___jp_386_;
}
}
}
else
{
v___y_387_ = v___y_477_;
v___y_388_ = v___y_480_;
v___y_389_ = v___y_479_;
v___y_390_ = v___y_478_;
goto v___jp_386_;
}
}
v___jp_503_:
{
lean_object* v___x_506_; lean_object* v_fileName_507_; lean_object* v_fileMap_508_; lean_object* v_currRecDepth_509_; lean_object* v_ref_510_; lean_object* v_currNamespace_511_; lean_object* v_openDecls_512_; lean_object* v_initHeartbeats_513_; lean_object* v_maxHeartbeats_514_; lean_object* v_quotContext_515_; lean_object* v_currMacroScope_516_; lean_object* v_cancelTk_x3f_517_; uint8_t v_suppressElabErrors_518_; lean_object* v_inheritedTraceOptions_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_531_; 
v___x_506_ = lean_st_ref_get(v___y_505_);
v_fileName_507_ = lean_ctor_get(v___y_504_, 0);
v_fileMap_508_ = lean_ctor_get(v___y_504_, 1);
v_currRecDepth_509_ = lean_ctor_get(v___y_504_, 3);
v_ref_510_ = lean_ctor_get(v___y_504_, 5);
v_currNamespace_511_ = lean_ctor_get(v___y_504_, 6);
v_openDecls_512_ = lean_ctor_get(v___y_504_, 7);
v_initHeartbeats_513_ = lean_ctor_get(v___y_504_, 8);
v_maxHeartbeats_514_ = lean_ctor_get(v___y_504_, 9);
v_quotContext_515_ = lean_ctor_get(v___y_504_, 10);
v_currMacroScope_516_ = lean_ctor_get(v___y_504_, 11);
v_cancelTk_x3f_517_ = lean_ctor_get(v___y_504_, 12);
v_suppressElabErrors_518_ = lean_ctor_get_uint8(v___y_504_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_519_ = lean_ctor_get(v___y_504_, 13);
v_isSharedCheck_531_ = !lean_is_exclusive(v___y_504_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; lean_object* v_unused_533_; 
v_unused_532_ = lean_ctor_get(v___y_504_, 4);
lean_dec(v_unused_532_);
v_unused_533_ = lean_ctor_get(v___y_504_, 2);
lean_dec(v_unused_533_);
v___x_521_ = v___y_504_;
v_isShared_522_ = v_isSharedCheck_531_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_inheritedTraceOptions_519_);
lean_inc(v_cancelTk_x3f_517_);
lean_inc(v_currMacroScope_516_);
lean_inc(v_quotContext_515_);
lean_inc(v_maxHeartbeats_514_);
lean_inc(v_initHeartbeats_513_);
lean_inc(v_openDecls_512_);
lean_inc(v_currNamespace_511_);
lean_inc(v_ref_510_);
lean_inc(v_currRecDepth_509_);
lean_inc(v_fileMap_508_);
lean_inc(v_fileName_507_);
lean_dec(v___y_504_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_531_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v_env_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
v_env_523_ = lean_ctor_get(v___x_506_, 0);
lean_inc_ref(v_env_523_);
lean_dec(v___x_506_);
v___x_524_ = l_Lean_maxRecDepth;
v___x_525_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 4, v___x_525_);
lean_ctor_set(v___x_521_, 2, v___x_379_);
v___x_527_ = v___x_521_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_fileName_507_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_fileMap_508_);
lean_ctor_set(v_reuseFailAlloc_530_, 2, v___x_379_);
lean_ctor_set(v_reuseFailAlloc_530_, 3, v_currRecDepth_509_);
lean_ctor_set(v_reuseFailAlloc_530_, 4, v___x_525_);
lean_ctor_set(v_reuseFailAlloc_530_, 5, v_ref_510_);
lean_ctor_set(v_reuseFailAlloc_530_, 6, v_currNamespace_511_);
lean_ctor_set(v_reuseFailAlloc_530_, 7, v_openDecls_512_);
lean_ctor_set(v_reuseFailAlloc_530_, 8, v_initHeartbeats_513_);
lean_ctor_set(v_reuseFailAlloc_530_, 9, v_maxHeartbeats_514_);
lean_ctor_set(v_reuseFailAlloc_530_, 10, v_quotContext_515_);
lean_ctor_set(v_reuseFailAlloc_530_, 11, v_currMacroScope_516_);
lean_ctor_set(v_reuseFailAlloc_530_, 12, v_cancelTk_x3f_517_);
lean_ctor_set(v_reuseFailAlloc_530_, 13, v_inheritedTraceOptions_519_);
lean_ctor_set_uint8(v_reuseFailAlloc_530_, sizeof(void*)*14 + 1, v_suppressElabErrors_518_);
v___x_527_ = v_reuseFailAlloc_530_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
uint8_t v___x_528_; uint8_t v___x_529_; 
lean_ctor_set_uint8(v___x_527_, sizeof(void*)*14, v___x_502_);
v___x_528_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_330_, v___x_501_);
v___x_529_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_523_);
lean_dec_ref(v_env_523_);
if (v___x_529_ == 0)
{
if (v___x_528_ == 0)
{
v___y_387_ = v___x_524_;
v___y_388_ = v___x_528_;
v___y_389_ = v___x_527_;
v___y_390_ = v___y_505_;
goto v___jp_386_;
}
else
{
v___y_477_ = v___x_524_;
v___y_478_ = v___y_505_;
v___y_479_ = v___x_527_;
v___y_480_ = v___x_528_;
v___y_481_ = v___x_529_;
goto v___jp_476_;
}
}
else
{
v___y_477_ = v___x_524_;
v___y_478_ = v___y_505_;
v___y_479_ = v___x_527_;
v___y_480_ = v___x_528_;
v___y_481_ = v___x_528_;
goto v___jp_476_;
}
}
}
}
v___jp_534_:
{
if (v___y_535_ == 0)
{
lean_object* v___x_536_; lean_object* v_env_537_; lean_object* v_nextMacroScope_538_; lean_object* v_ngen_539_; lean_object* v_auxDeclNGen_540_; lean_object* v_traceState_541_; lean_object* v_messages_542_; lean_object* v_infoState_543_; lean_object* v_snapshotTasks_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_553_; 
v___x_536_ = lean_st_ref_take(v___x_359_);
v_env_537_ = lean_ctor_get(v___x_536_, 0);
v_nextMacroScope_538_ = lean_ctor_get(v___x_536_, 1);
v_ngen_539_ = lean_ctor_get(v___x_536_, 2);
v_auxDeclNGen_540_ = lean_ctor_get(v___x_536_, 3);
v_traceState_541_ = lean_ctor_get(v___x_536_, 4);
v_messages_542_ = lean_ctor_get(v___x_536_, 6);
v_infoState_543_ = lean_ctor_get(v___x_536_, 7);
v_snapshotTasks_544_ = lean_ctor_get(v___x_536_, 8);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_553_ == 0)
{
lean_object* v_unused_554_; 
v_unused_554_ = lean_ctor_get(v___x_536_, 5);
lean_dec(v_unused_554_);
v___x_546_ = v___x_536_;
v_isShared_547_ = v_isSharedCheck_553_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_snapshotTasks_544_);
lean_inc(v_infoState_543_);
lean_inc(v_messages_542_);
lean_inc(v_traceState_541_);
lean_inc(v_auxDeclNGen_540_);
lean_inc(v_ngen_539_);
lean_inc(v_nextMacroScope_538_);
lean_inc(v_env_537_);
lean_dec(v___x_536_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_553_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_548_ = l_Lean_Kernel_enableDiag(v_env_537_, v___x_502_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 5, v___x_348_);
lean_ctor_set(v___x_546_, 0, v___x_548_);
v___x_550_ = v___x_546_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_nextMacroScope_538_);
lean_ctor_set(v_reuseFailAlloc_552_, 2, v_ngen_539_);
lean_ctor_set(v_reuseFailAlloc_552_, 3, v_auxDeclNGen_540_);
lean_ctor_set(v_reuseFailAlloc_552_, 4, v_traceState_541_);
lean_ctor_set(v_reuseFailAlloc_552_, 5, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_552_, 6, v_messages_542_);
lean_ctor_set(v_reuseFailAlloc_552_, 7, v_infoState_543_);
lean_ctor_set(v_reuseFailAlloc_552_, 8, v_snapshotTasks_544_);
v___x_550_ = v_reuseFailAlloc_552_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_551_; 
v___x_551_ = lean_st_ref_set(v___x_359_, v___x_550_);
lean_inc(v___x_359_);
v___y_504_ = v___x_383_;
v___y_505_ = v___x_359_;
goto v___jp_503_;
}
}
}
else
{
lean_inc(v___x_359_);
v___y_504_ = v___x_383_;
v___y_505_ = v___x_359_;
goto v___jp_503_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___boxed(lean_object* v_env_556_, lean_object* v_mctx_557_, lean_object* v_lctx_558_, lean_object* v_opts_559_, lean_object* v_namingCtx_560_, lean_object* v_x_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_556_, v_mctx_557_, v_lctx_558_, v_opts_559_, v_namingCtx_560_, v_x_561_, v_a_562_, v_a_563_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec_ref(v_namingCtx_560_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope(lean_object* v_00_u03b1_566_, lean_object* v_env_567_, lean_object* v_mctx_568_, lean_object* v_lctx_569_, lean_object* v_opts_570_, lean_object* v_namingCtx_571_, lean_object* v_x_572_, lean_object* v_a_573_, lean_object* v_a_574_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_567_, v_mctx_568_, v_lctx_569_, v_opts_570_, v_namingCtx_571_, v_x_572_, v_a_573_, v_a_574_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___boxed(lean_object* v_00_u03b1_577_, lean_object* v_env_578_, lean_object* v_mctx_579_, lean_object* v_lctx_580_, lean_object* v_opts_581_, lean_object* v_namingCtx_582_, lean_object* v_x_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope(v_00_u03b1_577_, v_env_578_, v_mctx_579_, v_lctx_580_, v_opts_581_, v_namingCtx_582_, v_x_583_, v_a_584_, v_a_585_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
lean_dec_ref(v_namingCtx_582_);
return v_res_587_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(lean_object* v_stx_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_Syntax_getKind(v_stx_591_);
if (lean_obj_tag(v___x_592_) == 1)
{
lean_object* v_pre_593_; 
v_pre_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_pre_593_);
if (lean_obj_tag(v_pre_593_) == 1)
{
lean_object* v_pre_594_; 
v_pre_594_ = lean_ctor_get(v_pre_593_, 0);
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
if (lean_obj_tag(v_pre_596_) == 0)
{
lean_object* v_str_597_; lean_object* v_str_598_; lean_object* v_str_599_; lean_object* v_str_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v_str_597_ = lean_ctor_get(v___x_592_, 1);
lean_inc_ref(v_str_597_);
lean_dec_ref_known(v___x_592_, 2);
v_str_598_ = lean_ctor_get(v_pre_593_, 1);
lean_inc_ref(v_str_598_);
lean_dec_ref_known(v_pre_593_, 2);
v_str_599_ = lean_ctor_get(v_pre_594_, 1);
lean_inc_ref(v_str_599_);
lean_dec_ref_known(v_pre_594_, 2);
v_str_600_ = lean_ctor_get(v_pre_595_, 1);
lean_inc_ref(v_str_600_);
lean_dec_ref_known(v_pre_595_, 2);
v___x_601_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_602_ = lean_string_dec_eq(v_str_600_, v___x_601_);
lean_dec_ref(v_str_600_);
if (v___x_602_ == 0)
{
lean_dec_ref(v_str_599_);
lean_dec_ref(v_str_598_);
lean_dec_ref(v_str_597_);
return v___x_602_;
}
else
{
lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_603_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0));
v___x_604_ = lean_string_dec_eq(v_str_599_, v___x_603_);
lean_dec_ref(v_str_599_);
if (v___x_604_ == 0)
{
lean_dec_ref(v_str_598_);
lean_dec_ref(v_str_597_);
return v___x_604_;
}
else
{
lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_605_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_606_ = lean_string_dec_eq(v_str_598_, v___x_605_);
lean_dec_ref(v_str_598_);
if (v___x_606_ == 0)
{
lean_dec_ref(v_str_597_);
return v___x_606_;
}
else
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__1));
v___x_608_ = lean_string_dec_eq(v_str_597_, v___x_607_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_609_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__2));
v___x_610_ = lean_string_dec_eq(v_str_597_, v___x_609_);
lean_dec_ref(v_str_597_);
return v___x_610_;
}
else
{
lean_dec_ref(v_str_597_);
return v___x_608_;
}
}
}
}
}
else
{
uint8_t v___x_611_; 
lean_dec_ref_known(v_pre_595_, 2);
lean_dec_ref_known(v_pre_594_, 2);
lean_dec_ref_known(v_pre_593_, 2);
lean_dec_ref_known(v___x_592_, 2);
v___x_611_ = 0;
return v___x_611_;
}
}
else
{
uint8_t v___x_612_; 
lean_dec(v_pre_595_);
lean_dec_ref_known(v_pre_594_, 2);
lean_dec_ref_known(v_pre_593_, 2);
lean_dec_ref_known(v___x_592_, 2);
v___x_612_ = 0;
return v___x_612_;
}
}
else
{
uint8_t v___x_613_; 
lean_dec(v_pre_594_);
lean_dec_ref_known(v_pre_593_, 2);
lean_dec_ref_known(v___x_592_, 2);
v___x_613_ = 0;
return v___x_613_;
}
}
else
{
uint8_t v___x_614_; 
lean_dec_ref_known(v___x_592_, 2);
lean_dec(v_pre_593_);
v___x_614_ = 0;
return v___x_614_;
}
}
else
{
uint8_t v___x_615_; 
lean_dec(v___x_592_);
v___x_615_ = 0;
return v___x_615_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___boxed(lean_object* v_stx_616_){
_start:
{
uint8_t v_res_617_; lean_object* v_r_618_; 
v_res_617_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(v_stx_616_);
v_r_618_ = lean_box(v_res_617_);
return v_r_618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx(lean_object* v_x_619_){
_start:
{
if (lean_obj_tag(v_x_619_) == 0)
{
lean_object* v___x_620_; 
v___x_620_ = lean_unsigned_to_nat(0u);
return v___x_620_;
}
else
{
lean_object* v___x_621_; 
v___x_621_ = lean_unsigned_to_nat(1u);
return v___x_621_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx___boxed(lean_object* v_x_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx(v_x_622_);
lean_dec(v_x_622_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(lean_object* v_t_624_, lean_object* v_k_625_){
_start:
{
if (lean_obj_tag(v_t_624_) == 0)
{
lean_object* v_tacticSeq_626_; lean_object* v_insertPos_627_; lean_object* v___x_628_; 
v_tacticSeq_626_ = lean_ctor_get(v_t_624_, 0);
lean_inc(v_tacticSeq_626_);
v_insertPos_627_ = lean_ctor_get(v_t_624_, 1);
lean_inc(v_insertPos_627_);
lean_dec_ref_known(v_t_624_, 2);
v___x_628_ = lean_apply_2(v_k_625_, v_tacticSeq_626_, v_insertPos_627_);
return v___x_628_;
}
else
{
return v_k_625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim(lean_object* v_motive_629_, lean_object* v_ctorIdx_630_, lean_object* v_t_631_, lean_object* v_h_632_, lean_object* v_k_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_631_, v_k_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___boxed(lean_object* v_motive_635_, lean_object* v_ctorIdx_636_, lean_object* v_t_637_, lean_object* v_h_638_, lean_object* v_k_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim(v_motive_635_, v_ctorIdx_636_, v_t_637_, v_h_638_, v_k_639_);
lean_dec(v_ctorIdx_636_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_unsolvedGoal_elim___redArg(lean_object* v_t_641_, lean_object* v_unsolvedGoal_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_641_, v_unsolvedGoal_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_unsolvedGoal_elim(lean_object* v_motive_644_, lean_object* v_t_645_, lean_object* v_h_646_, lean_object* v_unsolvedGoal_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_645_, v_unsolvedGoal_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_sorryTactic_elim___redArg(lean_object* v_t_649_, lean_object* v_sorryTactic_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_649_, v_sorryTactic_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_sorryTactic_elim(lean_object* v_motive_652_, lean_object* v_t_653_, lean_object* v_h_654_, lean_object* v_sorryTactic_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_653_, v_sorryTactic_655_);
return v___x_656_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed__const__1(void){
_start:
{
uint32_t v___x_660_; lean_object* v___x_661_; 
v___x_660_ = 32;
v___x_661_ = lean_box_uint32(v___x_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(lean_object* v_tacticSeq_662_, lean_object* v_fileMap_663_){
_start:
{
uint8_t v___x_664_; lean_object* v___x_665_; 
v___x_664_ = 0;
v___x_665_ = l_Lean_Syntax_getPos_x3f(v_tacticSeq_662_, v___x_664_);
if (lean_obj_tag(v___x_665_) == 1)
{
lean_object* v_val_666_; lean_object* v___x_667_; 
v_val_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_val_666_);
lean_dec_ref_known(v___x_665_, 1);
v___x_667_ = l_Lean_Syntax_getTailPos_x3f(v_tacticSeq_662_, v___x_664_);
if (lean_obj_tag(v___x_667_) == 1)
{
lean_object* v_val_668_; lean_object* v_startPos_669_; lean_object* v_line_670_; lean_object* v_column_671_; lean_object* v_endPos_672_; lean_object* v_line_673_; uint8_t v___x_674_; 
v_val_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_val_668_);
lean_dec_ref_known(v___x_667_, 1);
lean_inc_ref(v_fileMap_663_);
v_startPos_669_ = l_Lean_FileMap_toPosition(v_fileMap_663_, v_val_666_);
lean_dec(v_val_666_);
v_line_670_ = lean_ctor_get(v_startPos_669_, 0);
lean_inc(v_line_670_);
v_column_671_ = lean_ctor_get(v_startPos_669_, 1);
lean_inc(v_column_671_);
lean_dec_ref(v_startPos_669_);
v_endPos_672_ = l_Lean_FileMap_toPosition(v_fileMap_663_, v_val_668_);
lean_dec(v_val_668_);
v_line_673_ = lean_ctor_get(v_endPos_672_, 0);
lean_inc(v_line_673_);
lean_dec_ref(v_endPos_672_);
v___x_674_ = lean_nat_dec_eq(v_line_670_, v_line_673_);
lean_dec(v_line_673_);
lean_dec(v_line_670_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_675_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__0));
v___x_676_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed__const__1;
v___x_677_ = l_List_replicateTR___redArg(v_column_671_, v___x_676_);
v___x_678_ = lean_string_mk(v___x_677_);
v___x_679_ = lean_string_append(v___x_675_, v___x_678_);
lean_dec_ref(v___x_678_);
return v___x_679_;
}
else
{
lean_object* v___x_680_; 
lean_dec(v_column_671_);
v___x_680_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__1));
return v___x_680_;
}
}
else
{
lean_object* v___x_681_; 
lean_dec(v___x_667_);
lean_dec(v_val_666_);
lean_dec_ref(v_fileMap_663_);
v___x_681_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__2));
return v___x_681_;
}
}
else
{
lean_object* v___x_682_; 
lean_dec(v___x_665_);
lean_dec_ref(v_fileMap_663_);
v___x_682_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__2));
return v___x_682_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed(lean_object* v_tacticSeq_683_, lean_object* v_fileMap_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(v_tacticSeq_683_, v_fileMap_684_);
lean_dec(v_tacticSeq_683_);
return v_res_685_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_688_ = lean_string_utf8_byte_size(v___x_687_);
return v___x_688_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_689_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1);
v___x_690_ = lean_unsigned_to_nat(0u);
v___x_691_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_692_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v___x_690_);
lean_ctor_set(v___x_692_, 2, v___x_689_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx(lean_object* v_p_693_){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_694_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_695_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2);
lean_inc(v_p_693_);
v___x_696_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set(v___x_696_, 1, v_p_693_);
lean_ctor_set(v___x_696_, 2, v___x_695_);
lean_ctor_set(v___x_696_, 3, v_p_693_);
v___x_697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
lean_ctor_set(v___x_697_, 1, v___x_694_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(lean_object* v_range_698_){
_start:
{
lean_object* v_start_699_; lean_object* v_stop_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_710_; 
v_start_699_ = lean_ctor_get(v_range_698_, 0);
v_stop_700_ = lean_ctor_get(v_range_698_, 1);
v_isSharedCheck_710_ = !lean_is_exclusive(v_range_698_);
if (v_isSharedCheck_710_ == 0)
{
v___x_702_ = v_range_698_;
v_isShared_703_ = v_isSharedCheck_710_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_stop_700_);
lean_inc(v_start_699_);
lean_dec(v_range_698_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_710_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_704_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_705_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2);
v___x_706_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
lean_ctor_set(v___x_706_, 1, v_start_699_);
lean_ctor_set(v___x_706_, 2, v___x_705_);
lean_ctor_set(v___x_706_, 3, v_stop_700_);
if (v_isShared_703_ == 0)
{
lean_ctor_set_tag(v___x_702_, 2);
lean_ctor_set(v___x_702_, 1, v___x_704_);
lean_ctor_set(v___x_702_, 0, v___x_706_);
v___x_708_ = v___x_702_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v___x_704_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(lean_object* v_mc_x3f_711_, lean_object* v_nc_x3f_712_, lean_object* v_msg_713_, lean_object* v_acc_714_){
_start:
{
switch(lean_obj_tag(v_msg_713_))
{
case 3:
{
lean_object* v_a_715_; lean_object* v_a_716_; lean_object* v___x_717_; 
lean_dec(v_mc_x3f_711_);
v_a_715_ = lean_ctor_get(v_msg_713_, 0);
v_a_716_ = lean_ctor_get(v_msg_713_, 1);
lean_inc_ref(v_a_715_);
v___x_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_717_, 0, v_a_715_);
v_mc_x3f_711_ = v___x_717_;
v_msg_713_ = v_a_716_;
goto _start;
}
case 4:
{
lean_object* v_a_719_; lean_object* v_a_720_; lean_object* v___x_721_; 
lean_dec(v_nc_x3f_712_);
v_a_719_ = lean_ctor_get(v_msg_713_, 0);
v_a_720_ = lean_ctor_get(v_msg_713_, 1);
lean_inc_ref(v_a_719_);
v___x_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_721_, 0, v_a_719_);
v_nc_x3f_712_ = v___x_721_;
v_msg_713_ = v_a_720_;
goto _start;
}
case 5:
{
lean_object* v_a_723_; 
v_a_723_ = lean_ctor_get(v_msg_713_, 1);
v_msg_713_ = v_a_723_;
goto _start;
}
case 6:
{
lean_object* v_a_725_; 
v_a_725_ = lean_ctor_get(v_msg_713_, 0);
v_msg_713_ = v_a_725_;
goto _start;
}
case 8:
{
lean_object* v_a_727_; 
v_a_727_ = lean_ctor_get(v_msg_713_, 1);
v_msg_713_ = v_a_727_;
goto _start;
}
case 7:
{
lean_object* v_a_729_; lean_object* v_a_730_; lean_object* v___x_731_; 
v_a_729_ = lean_ctor_get(v_msg_713_, 0);
v_a_730_ = lean_ctor_get(v_msg_713_, 1);
lean_inc(v_nc_x3f_712_);
lean_inc(v_mc_x3f_711_);
v___x_731_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_711_, v_nc_x3f_712_, v_a_729_, v_acc_714_);
v_msg_713_ = v_a_730_;
v_acc_714_ = v___x_731_;
goto _start;
}
case 2:
{
lean_object* v_a_733_; 
v_a_733_ = lean_ctor_get(v_msg_713_, 1);
v_msg_713_ = v_a_733_;
goto _start;
}
case 9:
{
lean_object* v_msg_735_; lean_object* v_children_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v_msg_735_ = lean_ctor_get(v_msg_713_, 1);
v_children_736_ = lean_ctor_get(v_msg_713_, 2);
lean_inc(v_nc_x3f_712_);
lean_inc(v_mc_x3f_711_);
v___x_737_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_711_, v_nc_x3f_712_, v_msg_735_, v_acc_714_);
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = lean_array_get_size(v_children_736_);
v___x_740_ = lean_nat_dec_lt(v___x_738_, v___x_739_);
if (v___x_740_ == 0)
{
lean_dec(v_nc_x3f_712_);
lean_dec(v_mc_x3f_711_);
return v___x_737_;
}
else
{
uint8_t v___x_741_; 
v___x_741_ = lean_nat_dec_le(v___x_739_, v___x_739_);
if (v___x_741_ == 0)
{
if (v___x_740_ == 0)
{
lean_dec(v_nc_x3f_712_);
lean_dec(v_mc_x3f_711_);
return v___x_737_;
}
else
{
size_t v___x_742_; size_t v___x_743_; lean_object* v___x_744_; 
v___x_742_ = ((size_t)0ULL);
v___x_743_ = lean_usize_of_nat(v___x_739_);
v___x_744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_711_, v_nc_x3f_712_, v_children_736_, v___x_742_, v___x_743_, v___x_737_);
return v___x_744_;
}
}
else
{
size_t v___x_745_; size_t v___x_746_; lean_object* v___x_747_; 
v___x_745_ = ((size_t)0ULL);
v___x_746_ = lean_usize_of_nat(v___x_739_);
v___x_747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_711_, v_nc_x3f_712_, v_children_736_, v___x_745_, v___x_746_, v___x_737_);
return v___x_747_;
}
}
}
case 1:
{
if (lean_obj_tag(v_mc_x3f_711_) == 1)
{
if (lean_obj_tag(v_nc_x3f_712_) == 1)
{
lean_object* v_a_748_; lean_object* v_val_749_; lean_object* v_val_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v_a_748_ = lean_ctor_get(v_msg_713_, 0);
v_val_749_ = lean_ctor_get(v_mc_x3f_711_, 0);
lean_inc(v_val_749_);
lean_dec_ref_known(v_mc_x3f_711_, 1);
v_val_750_ = lean_ctor_get(v_nc_x3f_712_, 0);
lean_inc(v_val_750_);
lean_dec_ref_known(v_nc_x3f_712_, 1);
lean_inc(v_a_748_);
v___x_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_751_, 0, v_val_750_);
lean_ctor_set(v___x_751_, 1, v_a_748_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v_val_749_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = lean_array_push(v_acc_714_, v___x_752_);
return v___x_753_;
}
else
{
lean_dec_ref_known(v_mc_x3f_711_, 1);
lean_dec(v_nc_x3f_712_);
return v_acc_714_;
}
}
else
{
lean_dec(v_nc_x3f_712_);
lean_dec(v_mc_x3f_711_);
return v_acc_714_;
}
}
default: 
{
lean_dec(v_nc_x3f_712_);
lean_dec(v_mc_x3f_711_);
return v_acc_714_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(lean_object* v_mc_x3f_754_, lean_object* v_nc_x3f_755_, lean_object* v_as_756_, size_t v_i_757_, size_t v_stop_758_, lean_object* v_b_759_){
_start:
{
uint8_t v___x_760_; 
v___x_760_ = lean_usize_dec_eq(v_i_757_, v_stop_758_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; lean_object* v___x_762_; size_t v___x_763_; size_t v___x_764_; 
v___x_761_ = lean_array_uget_borrowed(v_as_756_, v_i_757_);
lean_inc(v_nc_x3f_755_);
lean_inc(v_mc_x3f_754_);
v___x_762_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_754_, v_nc_x3f_755_, v___x_761_, v_b_759_);
v___x_763_ = ((size_t)1ULL);
v___x_764_ = lean_usize_add(v_i_757_, v___x_763_);
v_i_757_ = v___x_764_;
v_b_759_ = v___x_762_;
goto _start;
}
else
{
lean_dec(v_nc_x3f_755_);
lean_dec(v_mc_x3f_754_);
return v_b_759_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0___boxed(lean_object* v_mc_x3f_766_, lean_object* v_nc_x3f_767_, lean_object* v_as_768_, lean_object* v_i_769_, lean_object* v_stop_770_, lean_object* v_b_771_){
_start:
{
size_t v_i_boxed_772_; size_t v_stop_boxed_773_; lean_object* v_res_774_; 
v_i_boxed_772_ = lean_unbox_usize(v_i_769_);
lean_dec(v_i_769_);
v_stop_boxed_773_ = lean_unbox_usize(v_stop_770_);
lean_dec(v_stop_770_);
v_res_774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_766_, v_nc_x3f_767_, v_as_768_, v_i_boxed_772_, v_stop_boxed_773_, v_b_771_);
lean_dec_ref(v_as_768_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go___boxed(lean_object* v_mc_x3f_775_, lean_object* v_nc_x3f_776_, lean_object* v_msg_777_, lean_object* v_acc_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_775_, v_nc_x3f_776_, v_msg_777_, v_acc_778_);
lean_dec_ref(v_msg_777_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(lean_object* v_msg_782_){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_783_ = lean_box(0);
v___x_784_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___closed__0));
v___x_785_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v___x_783_, v___x_783_, v_msg_782_, v___x_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___boxed(lean_object* v_msg_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_msg_786_);
lean_dec_ref(v_msg_786_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f(lean_object* v_range_790_, lean_object* v_stx_791_){
_start:
{
lean_object* v___x_792_; 
lean_inc(v_stx_791_);
v___x_792_ = l_Lean_Syntax_getKind(v_stx_791_);
if (lean_obj_tag(v___x_792_) == 1)
{
lean_object* v_pre_793_; 
v_pre_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_pre_793_);
if (lean_obj_tag(v_pre_793_) == 1)
{
lean_object* v_pre_794_; 
v_pre_794_ = lean_ctor_get(v_pre_793_, 0);
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
if (lean_obj_tag(v_pre_796_) == 0)
{
lean_object* v_str_797_; lean_object* v_str_798_; lean_object* v_str_799_; lean_object* v_str_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v_str_797_ = lean_ctor_get(v___x_792_, 1);
lean_inc_ref(v_str_797_);
lean_dec_ref_known(v___x_792_, 2);
v_str_798_ = lean_ctor_get(v_pre_793_, 1);
lean_inc_ref(v_str_798_);
lean_dec_ref_known(v_pre_793_, 2);
v_str_799_ = lean_ctor_get(v_pre_794_, 1);
lean_inc_ref(v_str_799_);
lean_dec_ref_known(v_pre_794_, 2);
v_str_800_ = lean_ctor_get(v_pre_795_, 1);
lean_inc_ref(v_str_800_);
lean_dec_ref_known(v_pre_795_, 2);
v___x_801_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_802_ = lean_string_dec_eq(v_str_800_, v___x_801_);
lean_dec_ref(v_str_800_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; 
lean_dec_ref(v_str_799_);
lean_dec_ref(v_str_798_);
lean_dec_ref(v_str_797_);
lean_dec(v_stx_791_);
lean_dec_ref(v_range_790_);
v___x_803_ = lean_box(0);
return v___x_803_;
}
else
{
lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_804_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0));
v___x_805_ = lean_string_dec_eq(v_str_799_, v___x_804_);
lean_dec_ref(v_str_799_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; 
lean_dec_ref(v_str_798_);
lean_dec_ref(v_str_797_);
lean_dec(v_stx_791_);
lean_dec_ref(v_range_790_);
v___x_806_ = lean_box(0);
return v___x_806_;
}
else
{
lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_807_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_808_ = lean_string_dec_eq(v_str_798_, v___x_807_);
lean_dec_ref(v_str_798_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; 
lean_dec_ref(v_str_797_);
lean_dec(v_stx_791_);
lean_dec_ref(v_range_790_);
v___x_809_ = lean_box(0);
return v___x_809_;
}
else
{
lean_object* v___x_810_; uint8_t v___x_811_; 
v___x_810_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__0));
v___x_811_ = lean_string_dec_eq(v_str_797_, v___x_810_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_812_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__1));
v___x_813_ = lean_string_dec_eq(v_str_797_, v___x_812_);
lean_dec_ref(v_str_797_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; 
lean_dec(v_stx_791_);
lean_dec_ref(v_range_790_);
v___x_814_ = lean_box(0);
return v___x_814_;
}
else
{
lean_object* v___x_815_; lean_object* v_body_816_; lean_object* v___y_818_; lean_object* v___x_821_; 
v___x_815_ = lean_unsigned_to_nat(1u);
v_body_816_ = l_Lean_Syntax_getArg(v_stx_791_, v___x_815_);
v___x_821_ = l_Lean_Syntax_getTailPos_x3f(v_body_816_, v___x_811_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_822_ = lean_unsigned_to_nat(2u);
v___x_823_ = l_Lean_Syntax_getArg(v_stx_791_, v___x_822_);
lean_dec(v_stx_791_);
v___x_824_ = l_Lean_Syntax_getPos_x3f(v___x_823_, v___x_811_);
lean_dec(v___x_823_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v_stop_825_; 
v_stop_825_ = lean_ctor_get(v_range_790_, 1);
lean_inc(v_stop_825_);
lean_dec_ref(v_range_790_);
v___y_818_ = v_stop_825_;
goto v___jp_817_;
}
else
{
lean_object* v_val_826_; 
lean_dec_ref(v_range_790_);
v_val_826_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_val_826_);
lean_dec_ref_known(v___x_824_, 1);
v___y_818_ = v_val_826_;
goto v___jp_817_;
}
}
else
{
lean_object* v_val_827_; 
lean_dec(v_stx_791_);
lean_dec_ref(v_range_790_);
v_val_827_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_val_827_);
lean_dec_ref_known(v___x_821_, 1);
v___y_818_ = v_val_827_;
goto v___jp_817_;
}
v___jp_817_:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_819_, 0, v_body_816_);
lean_ctor_set(v___x_819_, 1, v___y_818_);
v___x_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
return v___x_820_;
}
}
}
else
{
lean_object* v___x_828_; lean_object* v_body_829_; lean_object* v___y_831_; uint8_t v___x_834_; lean_object* v___x_835_; 
lean_dec_ref(v_str_797_);
v___x_828_ = lean_unsigned_to_nat(0u);
v_body_829_ = l_Lean_Syntax_getArg(v_stx_791_, v___x_828_);
lean_dec(v_stx_791_);
v___x_834_ = 0;
v___x_835_ = l_Lean_Syntax_getTailPos_x3f(v_body_829_, v___x_834_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_stop_836_; 
v_stop_836_ = lean_ctor_get(v_range_790_, 1);
lean_inc(v_stop_836_);
lean_dec_ref(v_range_790_);
v___y_831_ = v_stop_836_;
goto v___jp_830_;
}
else
{
lean_object* v_val_837_; 
lean_dec_ref(v_range_790_);
v_val_837_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_val_837_);
lean_dec_ref_known(v___x_835_, 1);
v___y_831_ = v_val_837_;
goto v___jp_830_;
}
v___jp_830_:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_832_, 0, v_body_829_);
lean_ctor_set(v___x_832_, 1, v___y_831_);
v___x_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
return v___x_833_;
}
}
}
}
}
}
else
{
lean_object* v___x_838_; 
lean_dec_ref_known(v_pre_795_, 2);
lean_dec_ref_known(v_pre_794_, 2);
lean_dec_ref_known(v_pre_793_, 2);
lean_dec_ref_known(v___x_792_, 2);
lean_dec(v_stx_791_);
lean_dec_ref(v_range_790_);
v___x_838_ = lean_box(0);
return v___x_838_;
}
}
else
{
lean_object* v___x_839_; 
lean_dec_ref_known(v_pre_794_, 2);
lean_dec(v_pre_795_);
lean_dec_ref_known(v_pre_793_, 2);
lean_dec_ref_known(v___x_792_, 2);
lean_dec(v_stx_791_);
lean_dec_ref(v_range_790_);
v___x_839_ = lean_box(0);
return v___x_839_;
}
}
else
{
lean_object* v___x_840_; 
lean_dec(v_pre_794_);
lean_dec_ref_known(v_pre_793_, 2);
lean_dec_ref_known(v___x_792_, 2);
lean_dec(v_stx_791_);
lean_dec_ref(v_range_790_);
v___x_840_ = lean_box(0);
return v___x_840_;
}
}
else
{
lean_object* v___x_841_; 
lean_dec(v_pre_793_);
lean_dec_ref_known(v___x_792_, 2);
lean_dec(v_stx_791_);
lean_dec_ref(v_range_790_);
v___x_841_ = lean_box(0);
return v___x_841_;
}
}
else
{
lean_object* v___x_842_; 
lean_dec(v___x_792_);
lean_dec(v_stx_791_);
lean_dec_ref(v_range_790_);
v___x_842_ = lean_box(0);
return v___x_842_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(lean_object* v_range_846_, lean_object* v_stx_847_){
_start:
{
lean_object* v___x_848_; 
lean_inc(v_stx_847_);
lean_inc_ref(v_range_846_);
v___x_848_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f(v_range_846_, v_stx_847_);
if (lean_obj_tag(v___x_848_) == 1)
{
lean_dec(v_stx_847_);
lean_dec_ref(v_range_846_);
return v___x_848_;
}
else
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; size_t v_sz_852_; size_t v___x_853_; lean_object* v___x_854_; lean_object* v_fst_855_; 
lean_dec(v___x_848_);
v___x_849_ = l_Lean_Syntax_getArgs(v_stx_847_);
lean_dec(v_stx_847_);
v___x_850_ = lean_box(0);
v___x_851_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v_sz_852_ = lean_array_size(v___x_849_);
v___x_853_ = ((size_t)0ULL);
v___x_854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(v_range_846_, v___x_849_, v_sz_852_, v___x_853_, v___x_851_);
lean_dec_ref(v___x_849_);
v_fst_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_fst_855_);
lean_dec_ref(v___x_854_);
if (lean_obj_tag(v_fst_855_) == 0)
{
return v___x_850_;
}
else
{
lean_object* v_val_856_; 
v_val_856_ = lean_ctor_get(v_fst_855_, 0);
lean_inc(v_val_856_);
lean_dec_ref_known(v_fst_855_, 1);
return v_val_856_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(lean_object* v_range_857_, lean_object* v_as_858_, size_t v_sz_859_, size_t v_i_860_, lean_object* v_b_861_){
_start:
{
uint8_t v___x_862_; 
v___x_862_ = lean_usize_dec_lt(v_i_860_, v_sz_859_);
if (v___x_862_ == 0)
{
lean_dec_ref(v_range_857_);
lean_inc_ref(v_b_861_);
return v_b_861_;
}
else
{
lean_object* v___x_863_; lean_object* v_a_864_; lean_object* v___x_865_; 
v___x_863_ = lean_box(0);
v_a_864_ = lean_array_uget_borrowed(v_as_858_, v_i_860_);
lean_inc(v_a_864_);
lean_inc_ref(v_range_857_);
v___x_865_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(v_range_857_, v_a_864_);
if (lean_obj_tag(v___x_865_) == 1)
{
lean_object* v___x_866_; lean_object* v___x_867_; 
lean_dec_ref(v_range_857_);
v___x_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
v___x_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
lean_ctor_set(v___x_867_, 1, v___x_863_);
return v___x_867_;
}
else
{
lean_object* v___x_868_; size_t v___x_869_; size_t v___x_870_; 
lean_dec(v___x_865_);
v___x_868_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v___x_869_ = ((size_t)1ULL);
v___x_870_ = lean_usize_add(v_i_860_, v___x_869_);
v_i_860_ = v___x_870_;
v_b_861_ = v___x_868_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___boxed(lean_object* v_range_872_, lean_object* v_as_873_, lean_object* v_sz_874_, lean_object* v_i_875_, lean_object* v_b_876_){
_start:
{
size_t v_sz_boxed_877_; size_t v_i_boxed_878_; lean_object* v_res_879_; 
v_sz_boxed_877_ = lean_unbox_usize(v_sz_874_);
lean_dec(v_sz_874_);
v_i_boxed_878_ = lean_unbox_usize(v_i_875_);
lean_dec(v_i_875_);
v_res_879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(v_range_872_, v_as_873_, v_sz_boxed_877_, v_i_boxed_878_, v_b_876_);
lean_dec_ref(v_b_876_);
lean_dec_ref(v_as_873_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(lean_object* v_range_880_, lean_object* v_stx_881_){
_start:
{
uint8_t v___x_882_; lean_object* v___x_883_; 
v___x_882_ = 0;
v___x_883_ = l_Lean_Syntax_getRange_x3f(v_stx_881_, v___x_882_);
if (lean_obj_tag(v___x_883_) == 1)
{
lean_object* v_val_884_; uint8_t v___x_885_; 
v_val_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_val_884_);
lean_dec_ref_known(v___x_883_, 1);
v___x_885_ = l_Lean_Syntax_Range_includes(v_val_884_, v_range_880_, v___x_882_, v___x_882_);
lean_dec(v_val_884_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; 
lean_dec(v_stx_881_);
lean_dec_ref(v_range_880_);
v___x_886_ = lean_box(0);
return v___x_886_;
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; size_t v_sz_889_; size_t v___x_890_; lean_object* v___x_891_; lean_object* v_fst_892_; 
v___x_887_ = l_Lean_Syntax_getArgs(v_stx_881_);
v___x_888_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v_sz_889_ = lean_array_size(v___x_887_);
v___x_890_ = ((size_t)0ULL);
lean_inc_ref(v_range_880_);
v___x_891_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(v_range_880_, v___x_887_, v_sz_889_, v___x_890_, v___x_888_);
lean_dec_ref(v___x_887_);
v_fst_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_fst_892_);
lean_dec_ref(v___x_891_);
if (lean_obj_tag(v_fst_892_) == 0)
{
lean_object* v___x_893_; 
v___x_893_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(v_range_880_, v_stx_881_);
return v___x_893_;
}
else
{
lean_object* v_val_894_; 
lean_dec(v_stx_881_);
lean_dec_ref(v_range_880_);
v_val_894_ = lean_ctor_get(v_fst_892_, 0);
lean_inc(v_val_894_);
lean_dec_ref_known(v_fst_892_, 1);
return v_val_894_;
}
}
}
else
{
lean_object* v___x_895_; 
lean_dec(v___x_883_);
lean_dec(v_stx_881_);
lean_dec_ref(v_range_880_);
v___x_895_ = lean_box(0);
return v___x_895_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(lean_object* v_range_896_, lean_object* v_as_897_, size_t v_sz_898_, size_t v_i_899_, lean_object* v_b_900_){
_start:
{
uint8_t v___x_901_; 
v___x_901_ = lean_usize_dec_lt(v_i_899_, v_sz_898_);
if (v___x_901_ == 0)
{
lean_dec_ref(v_range_896_);
lean_inc_ref(v_b_900_);
return v_b_900_;
}
else
{
lean_object* v___x_902_; lean_object* v_a_903_; lean_object* v___x_904_; 
v___x_902_ = lean_box(0);
v_a_903_ = lean_array_uget_borrowed(v_as_897_, v_i_899_);
lean_inc(v_a_903_);
lean_inc_ref(v_range_896_);
v___x_904_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v_range_896_, v_a_903_);
if (lean_obj_tag(v___x_904_) == 1)
{
lean_object* v___x_905_; lean_object* v___x_906_; 
lean_dec_ref(v_range_896_);
v___x_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
v___x_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
lean_ctor_set(v___x_906_, 1, v___x_902_);
return v___x_906_;
}
else
{
lean_object* v___x_907_; size_t v___x_908_; size_t v___x_909_; 
lean_dec(v___x_904_);
v___x_907_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v___x_908_ = ((size_t)1ULL);
v___x_909_ = lean_usize_add(v_i_899_, v___x_908_);
v_i_899_ = v___x_909_;
v_b_900_ = v___x_907_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0___boxed(lean_object* v_range_911_, lean_object* v_as_912_, lean_object* v_sz_913_, lean_object* v_i_914_, lean_object* v_b_915_){
_start:
{
size_t v_sz_boxed_916_; size_t v_i_boxed_917_; lean_object* v_res_918_; 
v_sz_boxed_916_ = lean_unbox_usize(v_sz_913_);
lean_dec(v_sz_913_);
v_i_boxed_917_ = lean_unbox_usize(v_i_914_);
lean_dec(v_i_914_);
v_res_918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(v_range_911_, v_as_912_, v_sz_boxed_916_, v_i_boxed_917_, v_b_915_);
lean_dec_ref(v_b_915_);
lean_dec_ref(v_as_912_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody(lean_object* v_cmd_919_, lean_object* v_range_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v_range_920_, v_cmd_919_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0(lean_object* v_ctx_922_, lean_object* v_info_923_, lean_object* v_acc_924_){
_start:
{
if (lean_obj_tag(v_info_923_) == 0)
{
lean_object* v_i_925_; lean_object* v_toElabInfo_926_; lean_object* v_mctxBefore_927_; lean_object* v_goalsBefore_928_; lean_object* v_stx_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_947_; 
v_i_925_ = lean_ctor_get(v_info_923_, 0);
lean_inc_ref(v_i_925_);
lean_dec_ref_known(v_info_923_, 1);
v_toElabInfo_926_ = lean_ctor_get(v_i_925_, 0);
lean_inc_ref(v_toElabInfo_926_);
v_mctxBefore_927_ = lean_ctor_get(v_i_925_, 1);
lean_inc_ref(v_mctxBefore_927_);
v_goalsBefore_928_ = lean_ctor_get(v_i_925_, 2);
lean_inc(v_goalsBefore_928_);
lean_dec_ref(v_i_925_);
v_stx_929_ = lean_ctor_get(v_toElabInfo_926_, 1);
v_isSharedCheck_947_ = !lean_is_exclusive(v_toElabInfo_926_);
if (v_isSharedCheck_947_ == 0)
{
lean_object* v_unused_948_; 
v_unused_948_ = lean_ctor_get(v_toElabInfo_926_, 0);
lean_dec(v_unused_948_);
v___x_931_ = v_toElabInfo_926_;
v_isShared_932_ = v_isSharedCheck_947_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_stx_929_);
lean_dec(v_toElabInfo_926_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_947_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
uint8_t v___x_933_; 
lean_inc(v_stx_929_);
v___x_933_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(v_stx_929_);
if (v___x_933_ == 0)
{
lean_del_object(v___x_931_);
lean_dec(v_stx_929_);
lean_dec(v_goalsBefore_928_);
lean_dec_ref(v_mctxBefore_927_);
return v_acc_924_;
}
else
{
lean_object* v___x_934_; 
v___x_934_ = l_List_head_x3f___redArg(v_goalsBefore_928_);
lean_dec(v_goalsBefore_928_);
if (lean_obj_tag(v___x_934_) == 1)
{
lean_object* v_toCommandContextInfo_935_; lean_object* v_val_936_; lean_object* v_env_937_; lean_object* v_options_938_; lean_object* v_currNamespace_939_; lean_object* v_openDecls_940_; lean_object* v_namingCtx_942_; 
v_toCommandContextInfo_935_ = lean_ctor_get(v_ctx_922_, 0);
v_val_936_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_val_936_);
lean_dec_ref_known(v___x_934_, 1);
v_env_937_ = lean_ctor_get(v_toCommandContextInfo_935_, 0);
v_options_938_ = lean_ctor_get(v_toCommandContextInfo_935_, 4);
v_currNamespace_939_ = lean_ctor_get(v_toCommandContextInfo_935_, 5);
v_openDecls_940_ = lean_ctor_get(v_toCommandContextInfo_935_, 6);
lean_inc(v_openDecls_940_);
lean_inc(v_currNamespace_939_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 1, v_openDecls_940_);
lean_ctor_set(v___x_931_, 0, v_currNamespace_939_);
v_namingCtx_942_ = v___x_931_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_currNamespace_939_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_openDecls_940_);
v_namingCtx_942_ = v_reuseFailAlloc_946_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_943_ = lean_box(1);
lean_inc_ref(v_options_938_);
lean_inc_ref(v_env_937_);
v___x_944_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v_stx_929_);
lean_ctor_set(v___x_944_, 2, v_env_937_);
lean_ctor_set(v___x_944_, 3, v_mctxBefore_927_);
lean_ctor_set(v___x_944_, 4, v_options_938_);
lean_ctor_set(v___x_944_, 5, v_namingCtx_942_);
lean_ctor_set(v___x_944_, 6, v_val_936_);
v___x_945_ = lean_array_push(v_acc_924_, v___x_944_);
return v___x_945_;
}
}
else
{
lean_dec(v___x_934_);
lean_del_object(v___x_931_);
lean_dec(v_stx_929_);
lean_dec_ref(v_mctxBefore_927_);
return v_acc_924_;
}
}
}
}
else
{
lean_dec_ref(v_info_923_);
return v_acc_924_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0___boxed(lean_object* v_ctx_949_, lean_object* v_info_950_, lean_object* v_acc_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0(v_ctx_949_, v_info_950_, v_acc_951_);
lean_dec_ref(v_ctx_949_);
return v_res_952_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_953_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__0);
v___x_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
return v___x_955_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_956_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1);
v___x_957_ = lean_unsigned_to_nat(0u);
v___x_958_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
lean_ctor_set(v___x_958_, 2, v___x_957_);
lean_ctor_set(v___x_958_, 3, v___x_957_);
lean_ctor_set(v___x_958_, 4, v___x_956_);
lean_ctor_set(v___x_958_, 5, v___x_956_);
lean_ctor_set(v___x_958_, 6, v___x_956_);
lean_ctor_set(v___x_958_, 7, v___x_956_);
lean_ctor_set(v___x_958_, 8, v___x_956_);
lean_ctor_set(v___x_958_, 9, v___x_956_);
return v___x_958_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_959_ = lean_unsigned_to_nat(32u);
v___x_960_ = lean_mk_empty_array_with_capacity(v___x_959_);
v___x_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
return v___x_961_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_962_ = ((size_t)5ULL);
v___x_963_ = lean_unsigned_to_nat(0u);
v___x_964_ = lean_unsigned_to_nat(32u);
v___x_965_ = lean_mk_empty_array_with_capacity(v___x_964_);
v___x_966_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__3);
v___x_967_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_967_, 0, v___x_966_);
lean_ctor_set(v___x_967_, 1, v___x_965_);
lean_ctor_set(v___x_967_, 2, v___x_963_);
lean_ctor_set(v___x_967_, 3, v___x_963_);
lean_ctor_set_usize(v___x_967_, 4, v___x_962_);
return v___x_967_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_968_ = lean_box(1);
v___x_969_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__4);
v___x_970_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1);
v___x_971_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
lean_ctor_set(v___x_971_, 1, v___x_969_);
lean_ctor_set(v___x_971_, 2, v___x_968_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(lean_object* v_msgData_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_975_; lean_object* v_env_976_; lean_object* v___x_977_; lean_object* v_scopes_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v_opts_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_975_ = lean_st_ref_get(v___y_973_);
v_env_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc_ref(v_env_976_);
lean_dec(v___x_975_);
v___x_977_ = lean_st_ref_get(v___y_973_);
v_scopes_978_ = lean_ctor_get(v___x_977_, 2);
lean_inc(v_scopes_978_);
lean_dec(v___x_977_);
v___x_979_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_980_ = l_List_head_x21___redArg(v___x_979_, v_scopes_978_);
lean_dec(v_scopes_978_);
v_opts_981_ = lean_ctor_get(v___x_980_, 1);
lean_inc_ref(v_opts_981_);
lean_dec(v___x_980_);
v___x_982_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__2);
v___x_983_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__5);
v___x_984_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_984_, 0, v_env_976_);
lean_ctor_set(v___x_984_, 1, v___x_982_);
lean_ctor_set(v___x_984_, 2, v___x_983_);
lean_ctor_set(v___x_984_, 3, v_opts_981_);
v___x_985_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
lean_ctor_set(v___x_985_, 1, v_msgData_972_);
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___boxed(lean_object* v_msgData_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(v_msgData_987_, v___y_988_);
lean_dec(v___y_988_);
return v_res_990_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0(void){
_start:
{
lean_object* v___x_991_; double v___x_992_; 
v___x_991_ = lean_unsigned_to_nat(0u);
v___x_992_ = lean_float_of_nat(v___x_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(lean_object* v_cls_995_, lean_object* v_msg_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_Elab_Command_getRef___redArg(v___y_997_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1049_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1002_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(v_msg_996_, v___y_998_);
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1049_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1049_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; lean_object* v_traceState_1008_; lean_object* v_env_1009_; lean_object* v_messages_1010_; lean_object* v_scopes_1011_; lean_object* v_usedQuotCtxts_1012_; lean_object* v_nextMacroScope_1013_; lean_object* v_maxRecDepth_1014_; lean_object* v_ngen_1015_; lean_object* v_auxDeclNGen_1016_; lean_object* v_infoState_1017_; lean_object* v_snapshotTasks_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1048_; 
v___x_1007_ = lean_st_ref_take(v___y_998_);
v_traceState_1008_ = lean_ctor_get(v___x_1007_, 9);
v_env_1009_ = lean_ctor_get(v___x_1007_, 0);
v_messages_1010_ = lean_ctor_get(v___x_1007_, 1);
v_scopes_1011_ = lean_ctor_get(v___x_1007_, 2);
v_usedQuotCtxts_1012_ = lean_ctor_get(v___x_1007_, 3);
v_nextMacroScope_1013_ = lean_ctor_get(v___x_1007_, 4);
v_maxRecDepth_1014_ = lean_ctor_get(v___x_1007_, 5);
v_ngen_1015_ = lean_ctor_get(v___x_1007_, 6);
v_auxDeclNGen_1016_ = lean_ctor_get(v___x_1007_, 7);
v_infoState_1017_ = lean_ctor_get(v___x_1007_, 8);
v_snapshotTasks_1018_ = lean_ctor_get(v___x_1007_, 10);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1020_ = v___x_1007_;
v_isShared_1021_ = v_isSharedCheck_1048_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_snapshotTasks_1018_);
lean_inc(v_traceState_1008_);
lean_inc(v_infoState_1017_);
lean_inc(v_auxDeclNGen_1016_);
lean_inc(v_ngen_1015_);
lean_inc(v_maxRecDepth_1014_);
lean_inc(v_nextMacroScope_1013_);
lean_inc(v_usedQuotCtxts_1012_);
lean_inc(v_scopes_1011_);
lean_inc(v_messages_1010_);
lean_inc(v_env_1009_);
lean_dec(v___x_1007_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1048_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
uint64_t v_tid_1022_; lean_object* v_traces_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1047_; 
v_tid_1022_ = lean_ctor_get_uint64(v_traceState_1008_, sizeof(void*)*1);
v_traces_1023_ = lean_ctor_get(v_traceState_1008_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_traceState_1008_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1025_ = v_traceState_1008_;
v_isShared_1026_ = v_isSharedCheck_1047_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_traces_1023_);
lean_dec(v_traceState_1008_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1047_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1027_; double v___x_1028_; uint8_t v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1027_ = lean_box(0);
v___x_1028_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0);
v___x_1029_ = 0;
v___x_1030_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_1031_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1031_, 0, v_cls_995_);
lean_ctor_set(v___x_1031_, 1, v___x_1027_);
lean_ctor_set(v___x_1031_, 2, v___x_1030_);
lean_ctor_set_float(v___x_1031_, sizeof(void*)*3, v___x_1028_);
lean_ctor_set_float(v___x_1031_, sizeof(void*)*3 + 8, v___x_1028_);
lean_ctor_set_uint8(v___x_1031_, sizeof(void*)*3 + 16, v___x_1029_);
v___x_1032_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__1));
v___x_1033_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1031_);
lean_ctor_set(v___x_1033_, 1, v_a_1003_);
lean_ctor_set(v___x_1033_, 2, v___x_1032_);
v___x_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1034_, 0, v_a_1001_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v___x_1035_ = l_Lean_PersistentArray_push___redArg(v_traces_1023_, v___x_1034_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1035_);
v___x_1037_ = v___x_1025_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1035_);
lean_ctor_set_uint64(v_reuseFailAlloc_1046_, sizeof(void*)*1, v_tid_1022_);
v___x_1037_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1039_; 
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 9, v___x_1037_);
v___x_1039_ = v___x_1020_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_env_1009_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_messages_1010_);
lean_ctor_set(v_reuseFailAlloc_1045_, 2, v_scopes_1011_);
lean_ctor_set(v_reuseFailAlloc_1045_, 3, v_usedQuotCtxts_1012_);
lean_ctor_set(v_reuseFailAlloc_1045_, 4, v_nextMacroScope_1013_);
lean_ctor_set(v_reuseFailAlloc_1045_, 5, v_maxRecDepth_1014_);
lean_ctor_set(v_reuseFailAlloc_1045_, 6, v_ngen_1015_);
lean_ctor_set(v_reuseFailAlloc_1045_, 7, v_auxDeclNGen_1016_);
lean_ctor_set(v_reuseFailAlloc_1045_, 8, v_infoState_1017_);
lean_ctor_set(v_reuseFailAlloc_1045_, 9, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1045_, 10, v_snapshotTasks_1018_);
v___x_1039_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
v___x_1040_ = lean_st_ref_set(v___y_998_, v___x_1039_);
v___x_1041_ = lean_box(0);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_1041_);
v___x_1043_ = v___x_1005_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1041_);
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
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec_ref(v_msg_996_);
lean_dec(v_cls_995_);
v_a_1050_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1000_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1000_);
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
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___boxed(lean_object* v_cls_1058_, lean_object* v_msg_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v_cls_1058_, v_msg_1059_, v___y_1060_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
return v_res_1063_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0(lean_object* v_x_1068_){
_start:
{
lean_object* v___x_1069_; uint8_t v___x_1070_; 
v___x_1069_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0___closed__1));
v___x_1070_ = lean_name_eq(v_x_1068_, v___x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0___boxed(lean_object* v_x_1071_){
_start:
{
uint8_t v_res_1072_; lean_object* v_r_1073_; 
v_res_1072_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0(v_x_1071_);
lean_dec(v_x_1071_);
v_r_1073_ = lean_box(v_res_1072_);
return v_r_1073_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(lean_object* v_a_1074_, lean_object* v_x_1075_){
_start:
{
if (lean_obj_tag(v_x_1075_) == 0)
{
uint8_t v___x_1076_; 
v___x_1076_ = 0;
return v___x_1076_;
}
else
{
lean_object* v_key_1077_; lean_object* v_tail_1078_; uint8_t v___y_1080_; lean_object* v_fst_1082_; lean_object* v_snd_1083_; lean_object* v_fst_1084_; lean_object* v_snd_1085_; uint8_t v___x_1086_; 
v_key_1077_ = lean_ctor_get(v_x_1075_, 0);
v_tail_1078_ = lean_ctor_get(v_x_1075_, 2);
v_fst_1082_ = lean_ctor_get(v_key_1077_, 0);
v_snd_1083_ = lean_ctor_get(v_key_1077_, 1);
v_fst_1084_ = lean_ctor_get(v_a_1074_, 0);
v_snd_1085_ = lean_ctor_get(v_a_1074_, 1);
v___x_1086_ = l_Lean_Syntax_instBEqRange_beq(v_fst_1082_, v_fst_1084_);
if (v___x_1086_ == 0)
{
v___y_1080_ = v___x_1086_;
goto v___jp_1079_;
}
else
{
uint8_t v___x_1087_; 
v___x_1087_ = l_Lean_instBEqMVarId_beq(v_snd_1083_, v_snd_1085_);
v___y_1080_ = v___x_1087_;
goto v___jp_1079_;
}
v___jp_1079_:
{
if (v___y_1080_ == 0)
{
v_x_1075_ = v_tail_1078_;
goto _start;
}
else
{
return v___y_1080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg___boxed(lean_object* v_a_1088_, lean_object* v_x_1089_){
_start:
{
uint8_t v_res_1090_; lean_object* v_r_1091_; 
v_res_1090_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(v_a_1088_, v_x_1089_);
lean_dec(v_x_1089_);
lean_dec_ref(v_a_1088_);
v_r_1091_ = lean_box(v_res_1090_);
return v_r_1091_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(lean_object* v_m_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v_buckets_1094_; lean_object* v_fst_1095_; lean_object* v_snd_1096_; lean_object* v___x_1097_; uint64_t v___x_1098_; uint64_t v___x_1099_; uint64_t v___x_1100_; uint64_t v___x_1101_; uint64_t v___x_1102_; uint64_t v_fold_1103_; uint64_t v___x_1104_; uint64_t v___x_1105_; uint64_t v___x_1106_; size_t v___x_1107_; size_t v___x_1108_; size_t v___x_1109_; size_t v___x_1110_; size_t v___x_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; 
v_buckets_1094_ = lean_ctor_get(v_m_1092_, 1);
v_fst_1095_ = lean_ctor_get(v_a_1093_, 0);
v_snd_1096_ = lean_ctor_get(v_a_1093_, 1);
v___x_1097_ = lean_array_get_size(v_buckets_1094_);
v___x_1098_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1095_);
v___x_1099_ = l_Lean_instHashableMVarId_hash(v_snd_1096_);
v___x_1100_ = lean_uint64_mix_hash(v___x_1098_, v___x_1099_);
v___x_1101_ = 32ULL;
v___x_1102_ = lean_uint64_shift_right(v___x_1100_, v___x_1101_);
v_fold_1103_ = lean_uint64_xor(v___x_1100_, v___x_1102_);
v___x_1104_ = 16ULL;
v___x_1105_ = lean_uint64_shift_right(v_fold_1103_, v___x_1104_);
v___x_1106_ = lean_uint64_xor(v_fold_1103_, v___x_1105_);
v___x_1107_ = lean_uint64_to_usize(v___x_1106_);
v___x_1108_ = lean_usize_of_nat(v___x_1097_);
v___x_1109_ = ((size_t)1ULL);
v___x_1110_ = lean_usize_sub(v___x_1108_, v___x_1109_);
v___x_1111_ = lean_usize_land(v___x_1107_, v___x_1110_);
v___x_1112_ = lean_array_uget_borrowed(v_buckets_1094_, v___x_1111_);
v___x_1113_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(v_a_1093_, v___x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg___boxed(lean_object* v_m_1114_, lean_object* v_a_1115_){
_start:
{
uint8_t v_res_1116_; lean_object* v_r_1117_; 
v_res_1116_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(v_m_1114_, v_a_1115_);
lean_dec_ref(v_a_1115_);
lean_dec_ref(v_m_1114_);
v_r_1117_ = lean_box(v_res_1116_);
return v_r_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3_spec__8___redArg(lean_object* v_x_1118_, lean_object* v_x_1119_){
_start:
{
if (lean_obj_tag(v_x_1119_) == 0)
{
return v_x_1118_;
}
else
{
lean_object* v_key_1120_; lean_object* v_value_1121_; lean_object* v_tail_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1149_; 
v_key_1120_ = lean_ctor_get(v_x_1119_, 0);
v_value_1121_ = lean_ctor_get(v_x_1119_, 1);
v_tail_1122_ = lean_ctor_get(v_x_1119_, 2);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_x_1119_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1124_ = v_x_1119_;
v_isShared_1125_ = v_isSharedCheck_1149_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_tail_1122_);
lean_inc(v_value_1121_);
lean_inc(v_key_1120_);
lean_dec(v_x_1119_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1149_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v_fst_1126_; lean_object* v_snd_1127_; lean_object* v___x_1128_; uint64_t v___x_1129_; uint64_t v___x_1130_; uint64_t v___x_1131_; uint64_t v___x_1132_; uint64_t v___x_1133_; uint64_t v_fold_1134_; uint64_t v___x_1135_; uint64_t v___x_1136_; uint64_t v___x_1137_; size_t v___x_1138_; size_t v___x_1139_; size_t v___x_1140_; size_t v___x_1141_; size_t v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1145_; 
v_fst_1126_ = lean_ctor_get(v_key_1120_, 0);
v_snd_1127_ = lean_ctor_get(v_key_1120_, 1);
v___x_1128_ = lean_array_get_size(v_x_1118_);
v___x_1129_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1126_);
v___x_1130_ = l_Lean_instHashableMVarId_hash(v_snd_1127_);
v___x_1131_ = lean_uint64_mix_hash(v___x_1129_, v___x_1130_);
v___x_1132_ = 32ULL;
v___x_1133_ = lean_uint64_shift_right(v___x_1131_, v___x_1132_);
v_fold_1134_ = lean_uint64_xor(v___x_1131_, v___x_1133_);
v___x_1135_ = 16ULL;
v___x_1136_ = lean_uint64_shift_right(v_fold_1134_, v___x_1135_);
v___x_1137_ = lean_uint64_xor(v_fold_1134_, v___x_1136_);
v___x_1138_ = lean_uint64_to_usize(v___x_1137_);
v___x_1139_ = lean_usize_of_nat(v___x_1128_);
v___x_1140_ = ((size_t)1ULL);
v___x_1141_ = lean_usize_sub(v___x_1139_, v___x_1140_);
v___x_1142_ = lean_usize_land(v___x_1138_, v___x_1141_);
v___x_1143_ = lean_array_uget_borrowed(v_x_1118_, v___x_1142_);
lean_inc(v___x_1143_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 2, v___x_1143_);
v___x_1145_ = v___x_1124_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_key_1120_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_value_1121_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1146_; 
v___x_1146_ = lean_array_uset(v_x_1118_, v___x_1142_, v___x_1145_);
v_x_1118_ = v___x_1146_;
v_x_1119_ = v_tail_1122_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3___redArg(lean_object* v_i_1150_, lean_object* v_source_1151_, lean_object* v_target_1152_){
_start:
{
lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1153_ = lean_array_get_size(v_source_1151_);
v___x_1154_ = lean_nat_dec_lt(v_i_1150_, v___x_1153_);
if (v___x_1154_ == 0)
{
lean_dec_ref(v_source_1151_);
lean_dec(v_i_1150_);
return v_target_1152_;
}
else
{
lean_object* v_es_1155_; lean_object* v___x_1156_; lean_object* v_source_1157_; lean_object* v_target_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v_es_1155_ = lean_array_fget(v_source_1151_, v_i_1150_);
v___x_1156_ = lean_box(0);
v_source_1157_ = lean_array_fset(v_source_1151_, v_i_1150_, v___x_1156_);
v_target_1158_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3_spec__8___redArg(v_target_1152_, v_es_1155_);
v___x_1159_ = lean_unsigned_to_nat(1u);
v___x_1160_ = lean_nat_add(v_i_1150_, v___x_1159_);
lean_dec(v_i_1150_);
v_i_1150_ = v___x_1160_;
v_source_1151_ = v_source_1157_;
v_target_1152_ = v_target_1158_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2___redArg(lean_object* v_data_1162_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v_nbuckets_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1163_ = lean_array_get_size(v_data_1162_);
v___x_1164_ = lean_unsigned_to_nat(2u);
v_nbuckets_1165_ = lean_nat_mul(v___x_1163_, v___x_1164_);
v___x_1166_ = lean_unsigned_to_nat(0u);
v___x_1167_ = lean_box(0);
v___x_1168_ = lean_mk_array(v_nbuckets_1165_, v___x_1167_);
v___x_1169_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3___redArg(v___x_1166_, v_data_1162_, v___x_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(lean_object* v_m_1170_, lean_object* v_a_1171_, lean_object* v_b_1172_){
_start:
{
lean_object* v_size_1173_; lean_object* v_buckets_1174_; lean_object* v_fst_1175_; lean_object* v_snd_1176_; lean_object* v___x_1177_; uint64_t v___x_1178_; uint64_t v___x_1179_; uint64_t v___x_1180_; uint64_t v___x_1181_; uint64_t v___x_1182_; uint64_t v_fold_1183_; uint64_t v___x_1184_; uint64_t v___x_1185_; uint64_t v___x_1186_; size_t v___x_1187_; size_t v___x_1188_; size_t v___x_1189_; size_t v___x_1190_; size_t v___x_1191_; lean_object* v_bkt_1192_; uint8_t v___x_1193_; 
v_size_1173_ = lean_ctor_get(v_m_1170_, 0);
v_buckets_1174_ = lean_ctor_get(v_m_1170_, 1);
v_fst_1175_ = lean_ctor_get(v_a_1171_, 0);
v_snd_1176_ = lean_ctor_get(v_a_1171_, 1);
v___x_1177_ = lean_array_get_size(v_buckets_1174_);
v___x_1178_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1175_);
v___x_1179_ = l_Lean_instHashableMVarId_hash(v_snd_1176_);
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
v_bkt_1192_ = lean_array_uget_borrowed(v_buckets_1174_, v___x_1191_);
v___x_1193_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(v_a_1171_, v_bkt_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1214_; 
lean_inc_ref(v_buckets_1174_);
lean_inc(v_size_1173_);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_m_1170_);
if (v_isSharedCheck_1214_ == 0)
{
lean_object* v_unused_1215_; lean_object* v_unused_1216_; 
v_unused_1215_ = lean_ctor_get(v_m_1170_, 1);
lean_dec(v_unused_1215_);
v_unused_1216_ = lean_ctor_get(v_m_1170_, 0);
lean_dec(v_unused_1216_);
v___x_1195_ = v_m_1170_;
v_isShared_1196_ = v_isSharedCheck_1214_;
goto v_resetjp_1194_;
}
else
{
lean_dec(v_m_1170_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1214_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1197_; lean_object* v_size_x27_1198_; lean_object* v___x_1199_; lean_object* v_buckets_x27_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; uint8_t v___x_1206_; 
v___x_1197_ = lean_unsigned_to_nat(1u);
v_size_x27_1198_ = lean_nat_add(v_size_1173_, v___x_1197_);
lean_dec(v_size_1173_);
lean_inc(v_bkt_1192_);
v___x_1199_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1199_, 0, v_a_1171_);
lean_ctor_set(v___x_1199_, 1, v_b_1172_);
lean_ctor_set(v___x_1199_, 2, v_bkt_1192_);
v_buckets_x27_1200_ = lean_array_uset(v_buckets_1174_, v___x_1191_, v___x_1199_);
v___x_1201_ = lean_unsigned_to_nat(4u);
v___x_1202_ = lean_nat_mul(v_size_x27_1198_, v___x_1201_);
v___x_1203_ = lean_unsigned_to_nat(3u);
v___x_1204_ = lean_nat_div(v___x_1202_, v___x_1203_);
lean_dec(v___x_1202_);
v___x_1205_ = lean_array_get_size(v_buckets_x27_1200_);
v___x_1206_ = lean_nat_dec_le(v___x_1204_, v___x_1205_);
lean_dec(v___x_1204_);
if (v___x_1206_ == 0)
{
lean_object* v_val_1207_; lean_object* v___x_1209_; 
v_val_1207_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2___redArg(v_buckets_x27_1200_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 1, v_val_1207_);
lean_ctor_set(v___x_1195_, 0, v_size_x27_1198_);
v___x_1209_ = v___x_1195_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_size_x27_1198_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_val_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
else
{
lean_object* v___x_1212_; 
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 1, v_buckets_x27_1200_);
lean_ctor_set(v___x_1195_, 0, v_size_x27_1198_);
v___x_1212_ = v___x_1195_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_size_x27_1198_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_buckets_x27_1200_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
else
{
lean_dec(v_b_1172_);
lean_dec_ref(v_a_1171_);
return v_m_1170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(lean_object* v___x_1217_, lean_object* v_fst_1218_, lean_object* v_snd_1219_, lean_object* v___x_1220_, lean_object* v_as_1221_, size_t v_sz_1222_, size_t v_i_1223_, lean_object* v_b_1224_){
_start:
{
lean_object* v_a_1227_; uint8_t v___x_1231_; 
v___x_1231_ = lean_usize_dec_lt(v_i_1223_, v_sz_1222_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; 
lean_dec(v___x_1220_);
lean_dec(v_snd_1219_);
lean_dec(v_fst_1218_);
lean_dec_ref(v___x_1217_);
v___x_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1232_, 0, v_b_1224_);
return v___x_1232_;
}
else
{
lean_object* v_a_1233_; lean_object* v_snd_1234_; lean_object* v_fst_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1271_; 
v_a_1233_ = lean_array_uget(v_as_1221_, v_i_1223_);
v_snd_1234_ = lean_ctor_get(v_a_1233_, 1);
v_fst_1235_ = lean_ctor_get(v_a_1233_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v_a_1233_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1237_ = v_a_1233_;
v_isShared_1238_ = v_isSharedCheck_1271_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_snd_1234_);
lean_inc(v_fst_1235_);
lean_dec(v_a_1233_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1271_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v_fst_1239_; lean_object* v_snd_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1270_; 
v_fst_1239_ = lean_ctor_get(v_snd_1234_, 0);
v_snd_1240_ = lean_ctor_get(v_snd_1234_, 1);
v_isSharedCheck_1270_ = !lean_is_exclusive(v_snd_1234_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1242_ = v_snd_1234_;
v_isShared_1243_ = v_isSharedCheck_1270_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_snd_1240_);
lean_inc(v_fst_1239_);
lean_dec(v_snd_1234_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1270_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v_fst_1244_; lean_object* v_snd_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1269_; 
v_fst_1244_ = lean_ctor_get(v_b_1224_, 0);
v_snd_1245_ = lean_ctor_get(v_b_1224_, 1);
v_isSharedCheck_1269_ = !lean_is_exclusive(v_b_1224_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1247_ = v_b_1224_;
v_isShared_1248_ = v_isSharedCheck_1269_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_snd_1245_);
lean_inc(v_fst_1244_);
lean_dec(v_b_1224_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1269_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
lean_inc(v_snd_1240_);
lean_inc_ref(v___x_1217_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 1, v_snd_1240_);
lean_ctor_set(v___x_1247_, 0, v___x_1217_);
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1217_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v_snd_1240_);
v___x_1250_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
uint8_t v___x_1251_; 
v___x_1251_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(v_snd_1245_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_object* v_env_1252_; lean_object* v_mctx_1253_; lean_object* v_opts_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1258_; 
v_env_1252_ = lean_ctor_get(v_fst_1235_, 0);
lean_inc_ref(v_env_1252_);
v_mctx_1253_ = lean_ctor_get(v_fst_1235_, 1);
lean_inc_ref(v_mctx_1253_);
v_opts_1254_ = lean_ctor_get(v_fst_1235_, 3);
lean_inc_ref(v_opts_1254_);
lean_dec(v_fst_1235_);
v___x_1255_ = lean_box(0);
v___x_1256_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_snd_1245_, v___x_1250_, v___x_1255_);
lean_inc(v_snd_1219_);
lean_inc(v_fst_1218_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 1, v_snd_1219_);
lean_ctor_set(v___x_1237_, 0, v_fst_1218_);
v___x_1258_ = v___x_1237_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_fst_1218_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_snd_1219_);
v___x_1258_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1262_; 
lean_inc(v___x_1220_);
v___x_1259_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
lean_ctor_set(v___x_1259_, 1, v___x_1220_);
lean_ctor_set(v___x_1259_, 2, v_env_1252_);
lean_ctor_set(v___x_1259_, 3, v_mctx_1253_);
lean_ctor_set(v___x_1259_, 4, v_opts_1254_);
lean_ctor_set(v___x_1259_, 5, v_fst_1239_);
lean_ctor_set(v___x_1259_, 6, v_snd_1240_);
v___x_1260_ = lean_array_push(v_fst_1244_, v___x_1259_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 1, v___x_1256_);
lean_ctor_set(v___x_1242_, 0, v___x_1260_);
v___x_1262_ = v___x_1242_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1260_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v___x_1256_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
v_a_1227_ = v___x_1262_;
goto v___jp_1226_;
}
}
}
else
{
lean_object* v___x_1266_; 
lean_dec_ref(v___x_1250_);
lean_dec(v_snd_1240_);
lean_dec(v_fst_1239_);
lean_del_object(v___x_1237_);
lean_dec(v_fst_1235_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 1, v_snd_1245_);
lean_ctor_set(v___x_1242_, 0, v_fst_1244_);
v___x_1266_ = v___x_1242_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_fst_1244_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_snd_1245_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
v_a_1227_ = v___x_1266_;
goto v___jp_1226_;
}
}
}
}
}
}
}
v___jp_1226_:
{
size_t v___x_1228_; size_t v___x_1229_; 
v___x_1228_ = ((size_t)1ULL);
v___x_1229_ = lean_usize_add(v_i_1223_, v___x_1228_);
v_i_1223_ = v___x_1229_;
v_b_1224_ = v_a_1227_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg___boxed(lean_object* v___x_1272_, lean_object* v_fst_1273_, lean_object* v_snd_1274_, lean_object* v___x_1275_, lean_object* v_as_1276_, lean_object* v_sz_1277_, lean_object* v_i_1278_, lean_object* v_b_1279_, lean_object* v___y_1280_){
_start:
{
size_t v_sz_boxed_1281_; size_t v_i_boxed_1282_; lean_object* v_res_1283_; 
v_sz_boxed_1281_ = lean_unbox_usize(v_sz_1277_);
lean_dec(v_sz_1277_);
v_i_boxed_1282_ = lean_unbox_usize(v_i_1278_);
lean_dec(v_i_1278_);
v_res_1283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1272_, v_fst_1273_, v_snd_1274_, v___x_1275_, v_as_1276_, v_sz_boxed_1281_, v_i_boxed_1282_, v_b_1279_);
lean_dec_ref(v_as_1276_);
return v_res_1283_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1288_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1289_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__2));
v___x_1290_ = l_Lean_Name_append(v___x_1289_, v___x_1288_);
return v___x_1290_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__4));
v___x_1293_ = l_Lean_stringToMessageData(v___x_1292_);
return v___x_1293_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__6));
v___x_1296_ = l_Lean_stringToMessageData(v___x_1295_);
return v___x_1296_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__8));
v___x_1299_ = l_Lean_stringToMessageData(v___x_1298_);
return v___x_1299_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__10));
v___x_1302_ = l_Lean_stringToMessageData(v___x_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12(lean_object* v___x_1303_, lean_object* v_val_1304_, lean_object* v_cmd_1305_, uint8_t v_onUnsolved_1306_, uint8_t v___y_1307_, lean_object* v_as_1308_, size_t v_sz_1309_, size_t v_i_1310_, lean_object* v_b_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
uint8_t v___x_1315_; 
v___x_1315_ = lean_usize_dec_lt(v_i_1310_, v_sz_1309_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; 
lean_dec(v_cmd_1305_);
v___x_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1316_, 0, v_b_1311_);
return v___x_1316_;
}
else
{
lean_object* v_snd_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1465_; 
v_snd_1317_ = lean_ctor_get(v_b_1311_, 1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_b_1311_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; 
v_unused_1466_ = lean_ctor_get(v_b_1311_, 0);
lean_dec(v_unused_1466_);
v___x_1319_ = v_b_1311_;
v_isShared_1320_ = v_isSharedCheck_1465_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_snd_1317_);
lean_dec(v_b_1311_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1465_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v_fst_1321_; lean_object* v_snd_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1464_; 
v_fst_1321_ = lean_ctor_get(v_snd_1317_, 0);
v_snd_1322_ = lean_ctor_get(v_snd_1317_, 1);
v_isSharedCheck_1464_ = !lean_is_exclusive(v_snd_1317_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1324_ = v_snd_1317_;
v_isShared_1325_ = v_isSharedCheck_1464_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_snd_1322_);
lean_inc(v_fst_1321_);
lean_dec(v_snd_1317_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1464_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v_a_1326_; lean_object* v_pos_1327_; lean_object* v_endPos_1328_; uint8_t v_severity_1329_; lean_object* v_data_1330_; lean_object* v___x_1331_; lean_object* v_a_1333_; 
v_a_1326_ = lean_array_uget_borrowed(v_as_1308_, v_i_1310_);
v_pos_1327_ = lean_ctor_get(v_a_1326_, 1);
v_endPos_1328_ = lean_ctor_get(v_a_1326_, 2);
lean_inc(v_endPos_1328_);
v_severity_1329_ = lean_ctor_get_uint8(v_a_1326_, sizeof(void*)*5 + 1);
v_data_1330_ = lean_ctor_get(v_a_1326_, 4);
v___x_1331_ = lean_box(0);
if (v_severity_1329_ == 2)
{
lean_object* v___f_1346_; uint8_t v___x_1347_; 
v___f_1346_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
lean_inc(v_data_1330_);
v___x_1347_ = l_Lean_MessageData_hasTag(v___f_1346_, v_data_1330_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; 
lean_dec(v_endPos_1328_);
lean_del_object(v___x_1319_);
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v_fst_1321_);
lean_ctor_set(v___x_1348_, 1, v_snd_1322_);
v_a_1333_ = v___x_1348_;
goto v___jp_1332_;
}
else
{
if (lean_obj_tag(v_endPos_1328_) == 1)
{
lean_object* v_val_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1461_; 
v_val_1349_ = lean_ctor_get(v_endPos_1328_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_endPos_1328_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1351_ = v_endPos_1328_;
v_isShared_1352_ = v_isSharedCheck_1461_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_val_1349_);
lean_dec(v_endPos_1328_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1461_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; uint8_t v___x_1356_; uint8_t v___x_1357_; 
lean_inc_ref(v_pos_1327_);
v___x_1353_ = l_Lean_FileMap_ofPosition(v___x_1303_, v_pos_1327_);
v___x_1354_ = l_Lean_FileMap_ofPosition(v___x_1303_, v_val_1349_);
lean_inc(v___x_1354_);
lean_inc(v___x_1353_);
v___x_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1353_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = 0;
v___x_1357_ = l_Lean_Syntax_Range_includes(v_val_1304_, v___x_1355_, v___x_1356_, v___x_1356_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; 
lean_dec_ref_known(v___x_1355_, 2);
lean_dec(v___x_1354_);
lean_dec(v___x_1353_);
lean_del_object(v___x_1351_);
lean_del_object(v___x_1319_);
v___x_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1358_, 0, v_fst_1321_);
lean_ctor_set(v___x_1358_, 1, v_snd_1322_);
v_a_1333_ = v___x_1358_;
goto v___jp_1332_;
}
else
{
lean_object* v___x_1359_; 
lean_inc(v_cmd_1305_);
lean_inc_ref(v___x_1355_);
v___x_1359_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1355_, v_cmd_1305_);
if (lean_obj_tag(v___x_1359_) == 1)
{
lean_object* v_val_1360_; lean_object* v_fst_1361_; lean_object* v_snd_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1425_; 
lean_dec(v___x_1354_);
lean_dec(v___x_1353_);
lean_del_object(v___x_1351_);
v_val_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_val_1360_);
lean_dec_ref_known(v___x_1359_, 1);
v_fst_1361_ = lean_ctor_get(v_val_1360_, 0);
v_snd_1362_ = lean_ctor_get(v_val_1360_, 1);
v_isSharedCheck_1425_ = !lean_is_exclusive(v_val_1360_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1364_ = v_val_1360_;
v_isShared_1365_ = v_isSharedCheck_1425_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_snd_1362_);
lean_inc(v_fst_1361_);
lean_dec(v_val_1360_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1425_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; uint8_t v___y_1423_; lean_object* v___x_1424_; 
v___x_1424_ = l_Lean_Syntax_getPos_x3f(v_fst_1361_, v___x_1356_);
if (lean_obj_tag(v___x_1424_) == 0)
{
v___y_1423_ = v___x_1357_;
goto v___jp_1422_;
}
else
{
lean_dec_ref_known(v___x_1424_, 1);
v___y_1423_ = v___x_1356_;
goto v___jp_1422_;
}
v___jp_1366_:
{
lean_object* v___x_1372_; 
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 1, v_snd_1322_);
lean_ctor_set(v___x_1364_, 0, v_fst_1321_);
v___x_1372_ = v___x_1364_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_fst_1321_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_snd_1322_);
v___x_1372_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
size_t v_sz_1373_; size_t v___x_1374_; lean_object* v___x_1375_; 
v_sz_1373_ = lean_array_size(v___y_1367_);
v___x_1374_ = ((size_t)0ULL);
v___x_1375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1355_, v_fst_1361_, v_snd_1362_, v___y_1368_, v___y_1367_, v_sz_1373_, v___x_1374_, v___x_1372_);
lean_dec_ref(v___y_1367_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v_fst_1377_; lean_object* v_snd_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref_known(v___x_1375_, 1);
v_fst_1377_ = lean_ctor_get(v_a_1376_, 0);
v_snd_1378_ = lean_ctor_get(v_a_1376_, 1);
v_isSharedCheck_1385_ = !lean_is_exclusive(v_a_1376_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v_a_1376_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_snd_1378_);
lean_inc(v_fst_1377_);
lean_dec(v_a_1376_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_fst_1377_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_snd_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
v_a_1333_ = v___x_1383_;
goto v___jp_1332_;
}
}
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_del_object(v___x_1324_);
lean_dec(v_cmd_1305_);
v_a_1386_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1375_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1375_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
}
v___jp_1395_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; 
lean_inc_ref(v___x_1355_);
v___x_1396_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1355_);
v___x_1397_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1330_);
v___x_1398_ = lean_array_get_size(v___x_1397_);
v___x_1399_ = lean_unsigned_to_nat(0u);
v___x_1400_ = lean_nat_dec_eq(v___x_1398_, v___x_1399_);
if (v___x_1400_ == 0)
{
v___y_1367_ = v___x_1397_;
v___y_1368_ = v___x_1396_;
v___y_1369_ = v___y_1312_;
v___y_1370_ = v___y_1313_;
goto v___jp_1366_;
}
else
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v_scopes_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v_opts_1407_; uint8_t v_hasTrace_1408_; 
v___x_1401_ = l_Lean_inheritedTraceOptions;
v___x_1402_ = lean_st_ref_get(v___x_1401_);
v___x_1403_ = lean_st_ref_get(v___y_1313_);
v_scopes_1404_ = lean_ctor_get(v___x_1403_, 2);
lean_inc(v_scopes_1404_);
lean_dec(v___x_1403_);
v___x_1405_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1406_ = l_List_head_x21___redArg(v___x_1405_, v_scopes_1404_);
lean_dec(v_scopes_1404_);
v_opts_1407_ = lean_ctor_get(v___x_1406_, 1);
lean_inc_ref(v_opts_1407_);
lean_dec(v___x_1406_);
v_hasTrace_1408_ = lean_ctor_get_uint8(v_opts_1407_, sizeof(void*)*1);
if (v_hasTrace_1408_ == 0)
{
lean_dec_ref(v_opts_1407_);
lean_dec(v___x_1402_);
v___y_1367_ = v___x_1397_;
v___y_1368_ = v___x_1396_;
v___y_1369_ = v___y_1312_;
v___y_1370_ = v___y_1313_;
goto v___jp_1366_;
}
else
{
lean_object* v___x_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; 
v___x_1409_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1410_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1411_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1402_, v_opts_1407_, v___x_1410_);
lean_dec_ref(v_opts_1407_);
lean_dec(v___x_1402_);
if (v___x_1411_ == 0)
{
v___y_1367_ = v___x_1397_;
v___y_1368_ = v___x_1396_;
v___y_1369_ = v___y_1312_;
v___y_1370_ = v___y_1313_;
goto v___jp_1366_;
}
else
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5);
v___x_1413_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1409_, v___x_1412_, v___y_1312_, v___y_1313_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_dec_ref_known(v___x_1413_, 1);
v___y_1367_ = v___x_1397_;
v___y_1368_ = v___x_1396_;
v___y_1369_ = v___y_1312_;
v___y_1370_ = v___y_1313_;
goto v___jp_1366_;
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec_ref(v___x_1397_);
lean_dec(v___x_1396_);
lean_del_object(v___x_1364_);
lean_dec(v_snd_1362_);
lean_dec(v_fst_1361_);
lean_dec_ref_known(v___x_1355_, 2);
lean_del_object(v___x_1324_);
lean_dec(v_snd_1322_);
lean_dec(v_fst_1321_);
lean_dec(v_cmd_1305_);
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
}
}
}
v___jp_1422_:
{
if (v_onUnsolved_1306_ == 0)
{
if (v___y_1307_ == 0)
{
lean_del_object(v___x_1364_);
lean_dec(v_snd_1362_);
lean_dec(v_fst_1361_);
lean_dec_ref_known(v___x_1355_, 2);
goto v___jp_1340_;
}
else
{
if (v___y_1423_ == 0)
{
lean_del_object(v___x_1364_);
lean_dec(v_snd_1362_);
lean_dec(v_fst_1361_);
lean_dec_ref_known(v___x_1355_, 2);
goto v___jp_1340_;
}
else
{
lean_del_object(v___x_1319_);
goto v___jp_1395_;
}
}
}
else
{
lean_del_object(v___x_1319_);
goto v___jp_1395_;
}
}
}
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v_scopes_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v_opts_1432_; uint8_t v_hasTrace_1433_; 
lean_dec(v___x_1359_);
lean_dec_ref_known(v___x_1355_, 2);
lean_del_object(v___x_1319_);
v___x_1426_ = l_Lean_inheritedTraceOptions;
v___x_1427_ = lean_st_ref_get(v___x_1426_);
v___x_1428_ = lean_st_ref_get(v___y_1313_);
v_scopes_1429_ = lean_ctor_get(v___x_1428_, 2);
lean_inc(v_scopes_1429_);
lean_dec(v___x_1428_);
v___x_1430_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1431_ = l_List_head_x21___redArg(v___x_1430_, v_scopes_1429_);
lean_dec(v_scopes_1429_);
v_opts_1432_ = lean_ctor_get(v___x_1431_, 1);
lean_inc_ref(v_opts_1432_);
lean_dec(v___x_1431_);
v_hasTrace_1433_ = lean_ctor_get_uint8(v_opts_1432_, sizeof(void*)*1);
if (v_hasTrace_1433_ == 0)
{
lean_dec_ref(v_opts_1432_);
lean_dec(v___x_1427_);
lean_dec(v___x_1354_);
lean_dec(v___x_1353_);
lean_del_object(v___x_1351_);
goto v___jp_1344_;
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1434_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1435_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1436_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1427_, v_opts_1432_, v___x_1435_);
lean_dec_ref(v_opts_1432_);
lean_dec(v___x_1427_);
if (v___x_1436_ == 0)
{
lean_dec(v___x_1354_);
lean_dec(v___x_1353_);
lean_del_object(v___x_1351_);
goto v___jp_1344_;
}
else
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1437_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7);
v___x_1438_ = l_Nat_reprFast(v___x_1353_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set_tag(v___x_1351_, 3);
lean_ctor_set(v___x_1351_, 0, v___x_1438_);
v___x_1440_ = v___x_1351_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1441_ = l_Lean_MessageData_ofFormat(v___x_1440_);
v___x_1442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1437_);
lean_ctor_set(v___x_1442_, 1, v___x_1441_);
v___x_1443_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9);
v___x_1444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1442_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
v___x_1445_ = l_Nat_reprFast(v___x_1354_);
v___x_1446_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
v___x_1447_ = l_Lean_MessageData_ofFormat(v___x_1446_);
v___x_1448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1444_);
lean_ctor_set(v___x_1448_, 1, v___x_1447_);
v___x_1449_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11);
v___x_1450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1448_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
v___x_1451_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1434_, v___x_1450_, v___y_1312_, v___y_1313_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_dec_ref_known(v___x_1451_, 1);
goto v___jp_1344_;
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_del_object(v___x_1324_);
lean_dec(v_snd_1322_);
lean_dec(v_fst_1321_);
lean_dec(v_cmd_1305_);
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1451_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1451_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
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
lean_object* v___x_1462_; 
lean_dec(v_endPos_1328_);
lean_del_object(v___x_1319_);
v___x_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1462_, 0, v_fst_1321_);
lean_ctor_set(v___x_1462_, 1, v_snd_1322_);
v_a_1333_ = v___x_1462_;
goto v___jp_1332_;
}
}
}
else
{
lean_object* v___x_1463_; 
lean_dec(v_endPos_1328_);
lean_del_object(v___x_1319_);
v___x_1463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1463_, 0, v_fst_1321_);
lean_ctor_set(v___x_1463_, 1, v_snd_1322_);
v_a_1333_ = v___x_1463_;
goto v___jp_1332_;
}
v___jp_1332_:
{
lean_object* v___x_1335_; 
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 1, v_a_1333_);
lean_ctor_set(v___x_1324_, 0, v___x_1331_);
v___x_1335_ = v___x_1324_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1331_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_a_1333_);
v___x_1335_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
size_t v___x_1336_; size_t v___x_1337_; 
v___x_1336_ = ((size_t)1ULL);
v___x_1337_ = lean_usize_add(v_i_1310_, v___x_1336_);
v_i_1310_ = v___x_1337_;
v_b_1311_ = v___x_1335_;
goto _start;
}
}
v___jp_1340_:
{
lean_object* v___x_1342_; 
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 1, v_snd_1322_);
lean_ctor_set(v___x_1319_, 0, v_fst_1321_);
v___x_1342_ = v___x_1319_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_fst_1321_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_snd_1322_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
v_a_1333_ = v___x_1342_;
goto v___jp_1332_;
}
}
v___jp_1344_:
{
lean_object* v___x_1345_; 
v___x_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1345_, 0, v_fst_1321_);
lean_ctor_set(v___x_1345_, 1, v_snd_1322_);
v_a_1333_ = v___x_1345_;
goto v___jp_1332_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___boxed(lean_object* v___x_1467_, lean_object* v_val_1468_, lean_object* v_cmd_1469_, lean_object* v_onUnsolved_1470_, lean_object* v___y_1471_, lean_object* v_as_1472_, lean_object* v_sz_1473_, lean_object* v_i_1474_, lean_object* v_b_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
uint8_t v_onUnsolved_boxed_1479_; uint8_t v___y_14951__boxed_1480_; size_t v_sz_boxed_1481_; size_t v_i_boxed_1482_; lean_object* v_res_1483_; 
v_onUnsolved_boxed_1479_ = lean_unbox(v_onUnsolved_1470_);
v___y_14951__boxed_1480_ = lean_unbox(v___y_1471_);
v_sz_boxed_1481_ = lean_unbox_usize(v_sz_1473_);
lean_dec(v_sz_1473_);
v_i_boxed_1482_ = lean_unbox_usize(v_i_1474_);
lean_dec(v_i_1474_);
v_res_1483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12(v___x_1467_, v_val_1468_, v_cmd_1469_, v_onUnsolved_boxed_1479_, v___y_14951__boxed_1480_, v_as_1472_, v_sz_boxed_1481_, v_i_boxed_1482_, v_b_1475_, v___y_1476_, v___y_1477_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec_ref(v_as_1472_);
lean_dec_ref(v_val_1468_);
lean_dec_ref(v___x_1467_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8(lean_object* v___x_1484_, lean_object* v_val_1485_, lean_object* v_cmd_1486_, uint8_t v_onUnsolved_1487_, uint8_t v___y_1488_, lean_object* v_as_1489_, size_t v_sz_1490_, size_t v_i_1491_, lean_object* v_b_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
uint8_t v___x_1496_; 
v___x_1496_ = lean_usize_dec_lt(v_i_1491_, v_sz_1490_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; 
lean_dec(v_cmd_1486_);
v___x_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1497_, 0, v_b_1492_);
return v___x_1497_;
}
else
{
lean_object* v_snd_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1646_; 
v_snd_1498_ = lean_ctor_get(v_b_1492_, 1);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_b_1492_);
if (v_isSharedCheck_1646_ == 0)
{
lean_object* v_unused_1647_; 
v_unused_1647_ = lean_ctor_get(v_b_1492_, 0);
lean_dec(v_unused_1647_);
v___x_1500_ = v_b_1492_;
v_isShared_1501_ = v_isSharedCheck_1646_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_snd_1498_);
lean_dec(v_b_1492_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1646_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v_fst_1502_; lean_object* v_snd_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1645_; 
v_fst_1502_ = lean_ctor_get(v_snd_1498_, 0);
v_snd_1503_ = lean_ctor_get(v_snd_1498_, 1);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_snd_1498_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1505_ = v_snd_1498_;
v_isShared_1506_ = v_isSharedCheck_1645_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_snd_1503_);
lean_inc(v_fst_1502_);
lean_dec(v_snd_1498_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1645_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v_a_1507_; lean_object* v_pos_1508_; lean_object* v_endPos_1509_; uint8_t v_severity_1510_; lean_object* v_data_1511_; lean_object* v___x_1512_; lean_object* v_a_1514_; 
v_a_1507_ = lean_array_uget_borrowed(v_as_1489_, v_i_1491_);
v_pos_1508_ = lean_ctor_get(v_a_1507_, 1);
v_endPos_1509_ = lean_ctor_get(v_a_1507_, 2);
lean_inc(v_endPos_1509_);
v_severity_1510_ = lean_ctor_get_uint8(v_a_1507_, sizeof(void*)*5 + 1);
v_data_1511_ = lean_ctor_get(v_a_1507_, 4);
v___x_1512_ = lean_box(0);
if (v_severity_1510_ == 2)
{
lean_object* v___f_1527_; uint8_t v___x_1528_; 
v___f_1527_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
lean_inc(v_data_1511_);
v___x_1528_ = l_Lean_MessageData_hasTag(v___f_1527_, v_data_1511_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; 
lean_dec(v_endPos_1509_);
lean_del_object(v___x_1500_);
v___x_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1529_, 0, v_fst_1502_);
lean_ctor_set(v___x_1529_, 1, v_snd_1503_);
v_a_1514_ = v___x_1529_;
goto v___jp_1513_;
}
else
{
if (lean_obj_tag(v_endPos_1509_) == 1)
{
lean_object* v_val_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1642_; 
v_val_1530_ = lean_ctor_get(v_endPos_1509_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_endPos_1509_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1532_ = v_endPos_1509_;
v_isShared_1533_ = v_isSharedCheck_1642_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_val_1530_);
lean_dec(v_endPos_1509_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1642_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; uint8_t v___x_1538_; 
lean_inc_ref(v_pos_1508_);
v___x_1534_ = l_Lean_FileMap_ofPosition(v___x_1484_, v_pos_1508_);
v___x_1535_ = l_Lean_FileMap_ofPosition(v___x_1484_, v_val_1530_);
lean_inc(v___x_1535_);
lean_inc(v___x_1534_);
v___x_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1534_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = 0;
v___x_1538_ = l_Lean_Syntax_Range_includes(v_val_1485_, v___x_1536_, v___x_1537_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; 
lean_dec_ref_known(v___x_1536_, 2);
lean_dec(v___x_1535_);
lean_dec(v___x_1534_);
lean_del_object(v___x_1532_);
lean_del_object(v___x_1500_);
v___x_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1539_, 0, v_fst_1502_);
lean_ctor_set(v___x_1539_, 1, v_snd_1503_);
v_a_1514_ = v___x_1539_;
goto v___jp_1513_;
}
else
{
lean_object* v___x_1540_; 
lean_inc(v_cmd_1486_);
lean_inc_ref(v___x_1536_);
v___x_1540_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1536_, v_cmd_1486_);
if (lean_obj_tag(v___x_1540_) == 1)
{
lean_object* v_val_1541_; lean_object* v_fst_1542_; lean_object* v_snd_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1606_; 
lean_dec(v___x_1535_);
lean_dec(v___x_1534_);
lean_del_object(v___x_1532_);
v_val_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_val_1541_);
lean_dec_ref_known(v___x_1540_, 1);
v_fst_1542_ = lean_ctor_get(v_val_1541_, 0);
v_snd_1543_ = lean_ctor_get(v_val_1541_, 1);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_val_1541_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1545_ = v_val_1541_;
v_isShared_1546_ = v_isSharedCheck_1606_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_snd_1543_);
lean_inc(v_fst_1542_);
lean_dec(v_val_1541_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1606_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; uint8_t v___y_1604_; lean_object* v___x_1605_; 
v___x_1605_ = l_Lean_Syntax_getPos_x3f(v_fst_1542_, v___x_1537_);
if (lean_obj_tag(v___x_1605_) == 0)
{
v___y_1604_ = v___x_1538_;
goto v___jp_1603_;
}
else
{
lean_dec_ref_known(v___x_1605_, 1);
v___y_1604_ = v___x_1537_;
goto v___jp_1603_;
}
v___jp_1547_:
{
lean_object* v___x_1553_; 
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 1, v_snd_1503_);
lean_ctor_set(v___x_1545_, 0, v_fst_1502_);
v___x_1553_ = v___x_1545_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_fst_1502_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_snd_1503_);
v___x_1553_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
size_t v_sz_1554_; size_t v___x_1555_; lean_object* v___x_1556_; 
v_sz_1554_ = lean_array_size(v___y_1548_);
v___x_1555_ = ((size_t)0ULL);
v___x_1556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1536_, v_fst_1542_, v_snd_1543_, v___y_1549_, v___y_1548_, v_sz_1554_, v___x_1555_, v___x_1553_);
lean_dec_ref(v___y_1548_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v_fst_1558_; lean_object* v_snd_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref_known(v___x_1556_, 1);
v_fst_1558_ = lean_ctor_get(v_a_1557_, 0);
v_snd_1559_ = lean_ctor_get(v_a_1557_, 1);
v_isSharedCheck_1566_ = !lean_is_exclusive(v_a_1557_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v_a_1557_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_snd_1559_);
lean_inc(v_fst_1558_);
lean_dec(v_a_1557_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_fst_1558_);
lean_ctor_set(v_reuseFailAlloc_1565_, 1, v_snd_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
v_a_1514_ = v___x_1564_;
goto v___jp_1513_;
}
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_del_object(v___x_1505_);
lean_dec(v_cmd_1486_);
v_a_1567_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1556_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1556_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
}
v___jp_1576_:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; uint8_t v___x_1581_; 
lean_inc_ref(v___x_1536_);
v___x_1577_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1536_);
v___x_1578_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1511_);
v___x_1579_ = lean_array_get_size(v___x_1578_);
v___x_1580_ = lean_unsigned_to_nat(0u);
v___x_1581_ = lean_nat_dec_eq(v___x_1579_, v___x_1580_);
if (v___x_1581_ == 0)
{
v___y_1548_ = v___x_1578_;
v___y_1549_ = v___x_1577_;
v___y_1550_ = v___y_1493_;
v___y_1551_ = v___y_1494_;
goto v___jp_1547_;
}
else
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v_scopes_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v_opts_1588_; uint8_t v_hasTrace_1589_; 
v___x_1582_ = l_Lean_inheritedTraceOptions;
v___x_1583_ = lean_st_ref_get(v___x_1582_);
v___x_1584_ = lean_st_ref_get(v___y_1494_);
v_scopes_1585_ = lean_ctor_get(v___x_1584_, 2);
lean_inc(v_scopes_1585_);
lean_dec(v___x_1584_);
v___x_1586_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1587_ = l_List_head_x21___redArg(v___x_1586_, v_scopes_1585_);
lean_dec(v_scopes_1585_);
v_opts_1588_ = lean_ctor_get(v___x_1587_, 1);
lean_inc_ref(v_opts_1588_);
lean_dec(v___x_1587_);
v_hasTrace_1589_ = lean_ctor_get_uint8(v_opts_1588_, sizeof(void*)*1);
if (v_hasTrace_1589_ == 0)
{
lean_dec_ref(v_opts_1588_);
lean_dec(v___x_1583_);
v___y_1548_ = v___x_1578_;
v___y_1549_ = v___x_1577_;
v___y_1550_ = v___y_1493_;
v___y_1551_ = v___y_1494_;
goto v___jp_1547_;
}
else
{
lean_object* v___x_1590_; lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1590_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1591_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1592_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1583_, v_opts_1588_, v___x_1591_);
lean_dec_ref(v_opts_1588_);
lean_dec(v___x_1583_);
if (v___x_1592_ == 0)
{
v___y_1548_ = v___x_1578_;
v___y_1549_ = v___x_1577_;
v___y_1550_ = v___y_1493_;
v___y_1551_ = v___y_1494_;
goto v___jp_1547_;
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5);
v___x_1594_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1590_, v___x_1593_, v___y_1493_, v___y_1494_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_dec_ref_known(v___x_1594_, 1);
v___y_1548_ = v___x_1578_;
v___y_1549_ = v___x_1577_;
v___y_1550_ = v___y_1493_;
v___y_1551_ = v___y_1494_;
goto v___jp_1547_;
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec_ref(v___x_1578_);
lean_dec(v___x_1577_);
lean_del_object(v___x_1545_);
lean_dec(v_snd_1543_);
lean_dec(v_fst_1542_);
lean_dec_ref_known(v___x_1536_, 2);
lean_del_object(v___x_1505_);
lean_dec(v_snd_1503_);
lean_dec(v_fst_1502_);
lean_dec(v_cmd_1486_);
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1594_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1594_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
}
}
}
v___jp_1603_:
{
if (v_onUnsolved_1487_ == 0)
{
if (v___y_1488_ == 0)
{
lean_del_object(v___x_1545_);
lean_dec(v_snd_1543_);
lean_dec(v_fst_1542_);
lean_dec_ref_known(v___x_1536_, 2);
goto v___jp_1521_;
}
else
{
if (v___y_1604_ == 0)
{
lean_del_object(v___x_1545_);
lean_dec(v_snd_1543_);
lean_dec(v_fst_1542_);
lean_dec_ref_known(v___x_1536_, 2);
goto v___jp_1521_;
}
else
{
lean_del_object(v___x_1500_);
goto v___jp_1576_;
}
}
}
else
{
lean_del_object(v___x_1500_);
goto v___jp_1576_;
}
}
}
}
else
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v_scopes_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v_opts_1613_; uint8_t v_hasTrace_1614_; 
lean_dec(v___x_1540_);
lean_dec_ref_known(v___x_1536_, 2);
lean_del_object(v___x_1500_);
v___x_1607_ = l_Lean_inheritedTraceOptions;
v___x_1608_ = lean_st_ref_get(v___x_1607_);
v___x_1609_ = lean_st_ref_get(v___y_1494_);
v_scopes_1610_ = lean_ctor_get(v___x_1609_, 2);
lean_inc(v_scopes_1610_);
lean_dec(v___x_1609_);
v___x_1611_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1612_ = l_List_head_x21___redArg(v___x_1611_, v_scopes_1610_);
lean_dec(v_scopes_1610_);
v_opts_1613_ = lean_ctor_get(v___x_1612_, 1);
lean_inc_ref(v_opts_1613_);
lean_dec(v___x_1612_);
v_hasTrace_1614_ = lean_ctor_get_uint8(v_opts_1613_, sizeof(void*)*1);
if (v_hasTrace_1614_ == 0)
{
lean_dec_ref(v_opts_1613_);
lean_dec(v___x_1608_);
lean_dec(v___x_1535_);
lean_dec(v___x_1534_);
lean_del_object(v___x_1532_);
goto v___jp_1525_;
}
else
{
lean_object* v___x_1615_; lean_object* v___x_1616_; uint8_t v___x_1617_; 
v___x_1615_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1616_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1617_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1608_, v_opts_1613_, v___x_1616_);
lean_dec_ref(v_opts_1613_);
lean_dec(v___x_1608_);
if (v___x_1617_ == 0)
{
lean_dec(v___x_1535_);
lean_dec(v___x_1534_);
lean_del_object(v___x_1532_);
goto v___jp_1525_;
}
else
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1621_; 
v___x_1618_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7);
v___x_1619_ = l_Nat_reprFast(v___x_1534_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set_tag(v___x_1532_, 3);
lean_ctor_set(v___x_1532_, 0, v___x_1619_);
v___x_1621_ = v___x_1532_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1622_ = l_Lean_MessageData_ofFormat(v___x_1621_);
v___x_1623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1618_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
v___x_1624_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9);
v___x_1625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1623_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
v___x_1626_ = l_Nat_reprFast(v___x_1535_);
v___x_1627_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
v___x_1628_ = l_Lean_MessageData_ofFormat(v___x_1627_);
v___x_1629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1625_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
v___x_1630_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11);
v___x_1631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1629_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1615_, v___x_1631_, v___y_1493_, v___y_1494_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_dec_ref_known(v___x_1632_, 1);
goto v___jp_1525_;
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_del_object(v___x_1505_);
lean_dec(v_snd_1503_);
lean_dec(v_fst_1502_);
lean_dec(v_cmd_1486_);
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1632_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1632_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
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
lean_object* v___x_1643_; 
lean_dec(v_endPos_1509_);
lean_del_object(v___x_1500_);
v___x_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1643_, 0, v_fst_1502_);
lean_ctor_set(v___x_1643_, 1, v_snd_1503_);
v_a_1514_ = v___x_1643_;
goto v___jp_1513_;
}
}
}
else
{
lean_object* v___x_1644_; 
lean_dec(v_endPos_1509_);
lean_del_object(v___x_1500_);
v___x_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1644_, 0, v_fst_1502_);
lean_ctor_set(v___x_1644_, 1, v_snd_1503_);
v_a_1514_ = v___x_1644_;
goto v___jp_1513_;
}
v___jp_1513_:
{
lean_object* v___x_1516_; 
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 1, v_a_1514_);
lean_ctor_set(v___x_1505_, 0, v___x_1512_);
v___x_1516_ = v___x_1505_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1520_, 1, v_a_1514_);
v___x_1516_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
size_t v___x_1517_; size_t v___x_1518_; lean_object* v___x_1519_; 
v___x_1517_ = ((size_t)1ULL);
v___x_1518_ = lean_usize_add(v_i_1491_, v___x_1517_);
v___x_1519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12(v___x_1484_, v_val_1485_, v_cmd_1486_, v_onUnsolved_1487_, v___y_1488_, v_as_1489_, v_sz_1490_, v___x_1518_, v___x_1516_, v___y_1493_, v___y_1494_);
return v___x_1519_;
}
}
v___jp_1521_:
{
lean_object* v___x_1523_; 
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 1, v_snd_1503_);
lean_ctor_set(v___x_1500_, 0, v_fst_1502_);
v___x_1523_ = v___x_1500_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_fst_1502_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_snd_1503_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
v_a_1514_ = v___x_1523_;
goto v___jp_1513_;
}
}
v___jp_1525_:
{
lean_object* v___x_1526_; 
v___x_1526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1526_, 0, v_fst_1502_);
lean_ctor_set(v___x_1526_, 1, v_snd_1503_);
v_a_1514_ = v___x_1526_;
goto v___jp_1513_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___boxed(lean_object* v___x_1648_, lean_object* v_val_1649_, lean_object* v_cmd_1650_, lean_object* v_onUnsolved_1651_, lean_object* v___y_1652_, lean_object* v_as_1653_, lean_object* v_sz_1654_, lean_object* v_i_1655_, lean_object* v_b_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
uint8_t v_onUnsolved_boxed_1660_; uint8_t v___y_15292__boxed_1661_; size_t v_sz_boxed_1662_; size_t v_i_boxed_1663_; lean_object* v_res_1664_; 
v_onUnsolved_boxed_1660_ = lean_unbox(v_onUnsolved_1651_);
v___y_15292__boxed_1661_ = lean_unbox(v___y_1652_);
v_sz_boxed_1662_ = lean_unbox_usize(v_sz_1654_);
lean_dec(v_sz_1654_);
v_i_boxed_1663_ = lean_unbox_usize(v_i_1655_);
lean_dec(v_i_1655_);
v_res_1664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8(v___x_1648_, v_val_1649_, v_cmd_1650_, v_onUnsolved_boxed_1660_, v___y_15292__boxed_1661_, v_as_1653_, v_sz_boxed_1662_, v_i_boxed_1663_, v_b_1656_, v___y_1657_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec_ref(v_as_1653_);
lean_dec_ref(v_val_1649_);
lean_dec_ref(v___x_1648_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10_spec__12(lean_object* v___x_1665_, lean_object* v_val_1666_, lean_object* v_cmd_1667_, uint8_t v_onUnsolved_1668_, uint8_t v___y_1669_, lean_object* v_as_1670_, size_t v_sz_1671_, size_t v_i_1672_, lean_object* v_b_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
uint8_t v___x_1677_; 
v___x_1677_ = lean_usize_dec_lt(v_i_1672_, v_sz_1671_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; 
lean_dec(v_cmd_1667_);
v___x_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1678_, 0, v_b_1673_);
return v___x_1678_;
}
else
{
lean_object* v_snd_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1827_; 
v_snd_1679_ = lean_ctor_get(v_b_1673_, 1);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_b_1673_);
if (v_isSharedCheck_1827_ == 0)
{
lean_object* v_unused_1828_; 
v_unused_1828_ = lean_ctor_get(v_b_1673_, 0);
lean_dec(v_unused_1828_);
v___x_1681_ = v_b_1673_;
v_isShared_1682_ = v_isSharedCheck_1827_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_snd_1679_);
lean_dec(v_b_1673_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1827_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v_fst_1683_; lean_object* v_snd_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1826_; 
v_fst_1683_ = lean_ctor_get(v_snd_1679_, 0);
v_snd_1684_ = lean_ctor_get(v_snd_1679_, 1);
v_isSharedCheck_1826_ = !lean_is_exclusive(v_snd_1679_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1686_ = v_snd_1679_;
v_isShared_1687_ = v_isSharedCheck_1826_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_snd_1684_);
lean_inc(v_fst_1683_);
lean_dec(v_snd_1679_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1826_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v_a_1688_; lean_object* v_pos_1689_; lean_object* v_endPos_1690_; uint8_t v_severity_1691_; lean_object* v_data_1692_; lean_object* v___x_1693_; lean_object* v_a_1695_; 
v_a_1688_ = lean_array_uget_borrowed(v_as_1670_, v_i_1672_);
v_pos_1689_ = lean_ctor_get(v_a_1688_, 1);
v_endPos_1690_ = lean_ctor_get(v_a_1688_, 2);
lean_inc(v_endPos_1690_);
v_severity_1691_ = lean_ctor_get_uint8(v_a_1688_, sizeof(void*)*5 + 1);
v_data_1692_ = lean_ctor_get(v_a_1688_, 4);
v___x_1693_ = lean_box(0);
if (v_severity_1691_ == 2)
{
lean_object* v___f_1708_; uint8_t v___x_1709_; 
v___f_1708_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
lean_inc(v_data_1692_);
v___x_1709_ = l_Lean_MessageData_hasTag(v___f_1708_, v_data_1692_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; 
lean_dec(v_endPos_1690_);
lean_del_object(v___x_1681_);
v___x_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1710_, 0, v_fst_1683_);
lean_ctor_set(v___x_1710_, 1, v_snd_1684_);
v_a_1695_ = v___x_1710_;
goto v___jp_1694_;
}
else
{
if (lean_obj_tag(v_endPos_1690_) == 1)
{
lean_object* v_val_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1823_; 
v_val_1711_ = lean_ctor_get(v_endPos_1690_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_endPos_1690_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1713_ = v_endPos_1690_;
v_isShared_1714_ = v_isSharedCheck_1823_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_val_1711_);
lean_dec(v_endPos_1690_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1823_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; uint8_t v___x_1719_; 
lean_inc_ref(v_pos_1689_);
v___x_1715_ = l_Lean_FileMap_ofPosition(v___x_1665_, v_pos_1689_);
v___x_1716_ = l_Lean_FileMap_ofPosition(v___x_1665_, v_val_1711_);
lean_inc(v___x_1716_);
lean_inc(v___x_1715_);
v___x_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1715_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
v___x_1718_ = 0;
v___x_1719_ = l_Lean_Syntax_Range_includes(v_val_1666_, v___x_1717_, v___x_1718_, v___x_1718_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; 
lean_dec_ref_known(v___x_1717_, 2);
lean_dec(v___x_1716_);
lean_dec(v___x_1715_);
lean_del_object(v___x_1713_);
lean_del_object(v___x_1681_);
v___x_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1720_, 0, v_fst_1683_);
lean_ctor_set(v___x_1720_, 1, v_snd_1684_);
v_a_1695_ = v___x_1720_;
goto v___jp_1694_;
}
else
{
lean_object* v___x_1721_; 
lean_inc(v_cmd_1667_);
lean_inc_ref(v___x_1717_);
v___x_1721_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1717_, v_cmd_1667_);
if (lean_obj_tag(v___x_1721_) == 1)
{
lean_object* v_val_1722_; lean_object* v_fst_1723_; lean_object* v_snd_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1787_; 
lean_dec(v___x_1716_);
lean_dec(v___x_1715_);
lean_del_object(v___x_1713_);
v_val_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_val_1722_);
lean_dec_ref_known(v___x_1721_, 1);
v_fst_1723_ = lean_ctor_get(v_val_1722_, 0);
v_snd_1724_ = lean_ctor_get(v_val_1722_, 1);
v_isSharedCheck_1787_ = !lean_is_exclusive(v_val_1722_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1726_ = v_val_1722_;
v_isShared_1727_ = v_isSharedCheck_1787_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_snd_1724_);
lean_inc(v_fst_1723_);
lean_dec(v_val_1722_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1787_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; uint8_t v___y_1785_; lean_object* v___x_1786_; 
v___x_1786_ = l_Lean_Syntax_getPos_x3f(v_fst_1723_, v___x_1718_);
if (lean_obj_tag(v___x_1786_) == 0)
{
v___y_1785_ = v___x_1719_;
goto v___jp_1784_;
}
else
{
lean_dec_ref_known(v___x_1786_, 1);
v___y_1785_ = v___x_1718_;
goto v___jp_1784_;
}
v___jp_1728_:
{
lean_object* v___x_1734_; 
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 1, v_snd_1684_);
lean_ctor_set(v___x_1726_, 0, v_fst_1683_);
v___x_1734_ = v___x_1726_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_fst_1683_);
lean_ctor_set(v_reuseFailAlloc_1756_, 1, v_snd_1684_);
v___x_1734_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
size_t v_sz_1735_; size_t v___x_1736_; lean_object* v___x_1737_; 
v_sz_1735_ = lean_array_size(v___y_1730_);
v___x_1736_ = ((size_t)0ULL);
v___x_1737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1717_, v_fst_1723_, v_snd_1724_, v___y_1729_, v___y_1730_, v_sz_1735_, v___x_1736_, v___x_1734_);
lean_dec_ref(v___y_1730_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v_fst_1739_; lean_object* v_snd_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_a_1738_);
lean_dec_ref_known(v___x_1737_, 1);
v_fst_1739_ = lean_ctor_get(v_a_1738_, 0);
v_snd_1740_ = lean_ctor_get(v_a_1738_, 1);
v_isSharedCheck_1747_ = !lean_is_exclusive(v_a_1738_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v_a_1738_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_snd_1740_);
lean_inc(v_fst_1739_);
lean_dec(v_a_1738_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_fst_1739_);
lean_ctor_set(v_reuseFailAlloc_1746_, 1, v_snd_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
v_a_1695_ = v___x_1745_;
goto v___jp_1694_;
}
}
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
lean_del_object(v___x_1686_);
lean_dec(v_cmd_1667_);
v_a_1748_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1737_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1737_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
}
v___jp_1757_:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; uint8_t v___x_1762_; 
lean_inc_ref(v___x_1717_);
v___x_1758_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1717_);
v___x_1759_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1692_);
v___x_1760_ = lean_array_get_size(v___x_1759_);
v___x_1761_ = lean_unsigned_to_nat(0u);
v___x_1762_ = lean_nat_dec_eq(v___x_1760_, v___x_1761_);
if (v___x_1762_ == 0)
{
v___y_1729_ = v___x_1758_;
v___y_1730_ = v___x_1759_;
v___y_1731_ = v___y_1674_;
v___y_1732_ = v___y_1675_;
goto v___jp_1728_;
}
else
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v_scopes_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v_opts_1769_; uint8_t v_hasTrace_1770_; 
v___x_1763_ = l_Lean_inheritedTraceOptions;
v___x_1764_ = lean_st_ref_get(v___x_1763_);
v___x_1765_ = lean_st_ref_get(v___y_1675_);
v_scopes_1766_ = lean_ctor_get(v___x_1765_, 2);
lean_inc(v_scopes_1766_);
lean_dec(v___x_1765_);
v___x_1767_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1768_ = l_List_head_x21___redArg(v___x_1767_, v_scopes_1766_);
lean_dec(v_scopes_1766_);
v_opts_1769_ = lean_ctor_get(v___x_1768_, 1);
lean_inc_ref(v_opts_1769_);
lean_dec(v___x_1768_);
v_hasTrace_1770_ = lean_ctor_get_uint8(v_opts_1769_, sizeof(void*)*1);
if (v_hasTrace_1770_ == 0)
{
lean_dec_ref(v_opts_1769_);
lean_dec(v___x_1764_);
v___y_1729_ = v___x_1758_;
v___y_1730_ = v___x_1759_;
v___y_1731_ = v___y_1674_;
v___y_1732_ = v___y_1675_;
goto v___jp_1728_;
}
else
{
lean_object* v___x_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1771_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1772_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1773_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1764_, v_opts_1769_, v___x_1772_);
lean_dec_ref(v_opts_1769_);
lean_dec(v___x_1764_);
if (v___x_1773_ == 0)
{
v___y_1729_ = v___x_1758_;
v___y_1730_ = v___x_1759_;
v___y_1731_ = v___y_1674_;
v___y_1732_ = v___y_1675_;
goto v___jp_1728_;
}
else
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5);
v___x_1775_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1771_, v___x_1774_, v___y_1674_, v___y_1675_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_dec_ref_known(v___x_1775_, 1);
v___y_1729_ = v___x_1758_;
v___y_1730_ = v___x_1759_;
v___y_1731_ = v___y_1674_;
v___y_1732_ = v___y_1675_;
goto v___jp_1728_;
}
else
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
lean_dec_ref(v___x_1759_);
lean_dec(v___x_1758_);
lean_del_object(v___x_1726_);
lean_dec(v_snd_1724_);
lean_dec(v_fst_1723_);
lean_dec_ref_known(v___x_1717_, 2);
lean_del_object(v___x_1686_);
lean_dec(v_snd_1684_);
lean_dec(v_fst_1683_);
lean_dec(v_cmd_1667_);
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1775_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
}
}
}
v___jp_1784_:
{
if (v_onUnsolved_1668_ == 0)
{
if (v___y_1669_ == 0)
{
lean_del_object(v___x_1726_);
lean_dec(v_snd_1724_);
lean_dec(v_fst_1723_);
lean_dec_ref_known(v___x_1717_, 2);
goto v___jp_1702_;
}
else
{
if (v___y_1785_ == 0)
{
lean_del_object(v___x_1726_);
lean_dec(v_snd_1724_);
lean_dec(v_fst_1723_);
lean_dec_ref_known(v___x_1717_, 2);
goto v___jp_1702_;
}
else
{
lean_del_object(v___x_1681_);
goto v___jp_1757_;
}
}
}
else
{
lean_del_object(v___x_1681_);
goto v___jp_1757_;
}
}
}
}
else
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v_scopes_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v_opts_1794_; uint8_t v_hasTrace_1795_; 
lean_dec(v___x_1721_);
lean_dec_ref_known(v___x_1717_, 2);
lean_del_object(v___x_1681_);
v___x_1788_ = l_Lean_inheritedTraceOptions;
v___x_1789_ = lean_st_ref_get(v___x_1788_);
v___x_1790_ = lean_st_ref_get(v___y_1675_);
v_scopes_1791_ = lean_ctor_get(v___x_1790_, 2);
lean_inc(v_scopes_1791_);
lean_dec(v___x_1790_);
v___x_1792_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1793_ = l_List_head_x21___redArg(v___x_1792_, v_scopes_1791_);
lean_dec(v_scopes_1791_);
v_opts_1794_ = lean_ctor_get(v___x_1793_, 1);
lean_inc_ref(v_opts_1794_);
lean_dec(v___x_1793_);
v_hasTrace_1795_ = lean_ctor_get_uint8(v_opts_1794_, sizeof(void*)*1);
if (v_hasTrace_1795_ == 0)
{
lean_dec_ref(v_opts_1794_);
lean_dec(v___x_1789_);
lean_dec(v___x_1716_);
lean_dec(v___x_1715_);
lean_del_object(v___x_1713_);
goto v___jp_1706_;
}
else
{
lean_object* v___x_1796_; lean_object* v___x_1797_; uint8_t v___x_1798_; 
v___x_1796_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1797_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1798_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1789_, v_opts_1794_, v___x_1797_);
lean_dec_ref(v_opts_1794_);
lean_dec(v___x_1789_);
if (v___x_1798_ == 0)
{
lean_dec(v___x_1716_);
lean_dec(v___x_1715_);
lean_del_object(v___x_1713_);
goto v___jp_1706_;
}
else
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1802_; 
v___x_1799_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7);
v___x_1800_ = l_Nat_reprFast(v___x_1715_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set_tag(v___x_1713_, 3);
lean_ctor_set(v___x_1713_, 0, v___x_1800_);
v___x_1802_ = v___x_1713_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1800_);
v___x_1802_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1803_ = l_Lean_MessageData_ofFormat(v___x_1802_);
v___x_1804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1799_);
lean_ctor_set(v___x_1804_, 1, v___x_1803_);
v___x_1805_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9);
v___x_1806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1804_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v___x_1807_ = l_Nat_reprFast(v___x_1716_);
v___x_1808_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
v___x_1809_ = l_Lean_MessageData_ofFormat(v___x_1808_);
v___x_1810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1806_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
v___x_1811_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11);
v___x_1812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1810_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1796_, v___x_1812_, v___y_1674_, v___y_1675_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_dec_ref_known(v___x_1813_, 1);
goto v___jp_1706_;
}
else
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
lean_del_object(v___x_1686_);
lean_dec(v_snd_1684_);
lean_dec(v_fst_1683_);
lean_dec(v_cmd_1667_);
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1816_ = v___x_1813_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1813_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1814_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
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
lean_object* v___x_1824_; 
lean_dec(v_endPos_1690_);
lean_del_object(v___x_1681_);
v___x_1824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1824_, 0, v_fst_1683_);
lean_ctor_set(v___x_1824_, 1, v_snd_1684_);
v_a_1695_ = v___x_1824_;
goto v___jp_1694_;
}
}
}
else
{
lean_object* v___x_1825_; 
lean_dec(v_endPos_1690_);
lean_del_object(v___x_1681_);
v___x_1825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1825_, 0, v_fst_1683_);
lean_ctor_set(v___x_1825_, 1, v_snd_1684_);
v_a_1695_ = v___x_1825_;
goto v___jp_1694_;
}
v___jp_1694_:
{
lean_object* v___x_1697_; 
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 1, v_a_1695_);
lean_ctor_set(v___x_1686_, 0, v___x_1693_);
v___x_1697_ = v___x_1686_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1693_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v_a_1695_);
v___x_1697_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
size_t v___x_1698_; size_t v___x_1699_; 
v___x_1698_ = ((size_t)1ULL);
v___x_1699_ = lean_usize_add(v_i_1672_, v___x_1698_);
v_i_1672_ = v___x_1699_;
v_b_1673_ = v___x_1697_;
goto _start;
}
}
v___jp_1702_:
{
lean_object* v___x_1704_; 
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 1, v_snd_1684_);
lean_ctor_set(v___x_1681_, 0, v_fst_1683_);
v___x_1704_ = v___x_1681_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_fst_1683_);
lean_ctor_set(v_reuseFailAlloc_1705_, 1, v_snd_1684_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
v_a_1695_ = v___x_1704_;
goto v___jp_1694_;
}
}
v___jp_1706_:
{
lean_object* v___x_1707_; 
v___x_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1707_, 0, v_fst_1683_);
lean_ctor_set(v___x_1707_, 1, v_snd_1684_);
v_a_1695_ = v___x_1707_;
goto v___jp_1694_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10_spec__12___boxed(lean_object* v___x_1829_, lean_object* v_val_1830_, lean_object* v_cmd_1831_, lean_object* v_onUnsolved_1832_, lean_object* v___y_1833_, lean_object* v_as_1834_, lean_object* v_sz_1835_, lean_object* v_i_1836_, lean_object* v_b_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
uint8_t v_onUnsolved_boxed_1841_; uint8_t v___y_15624__boxed_1842_; size_t v_sz_boxed_1843_; size_t v_i_boxed_1844_; lean_object* v_res_1845_; 
v_onUnsolved_boxed_1841_ = lean_unbox(v_onUnsolved_1832_);
v___y_15624__boxed_1842_ = lean_unbox(v___y_1833_);
v_sz_boxed_1843_ = lean_unbox_usize(v_sz_1835_);
lean_dec(v_sz_1835_);
v_i_boxed_1844_ = lean_unbox_usize(v_i_1836_);
lean_dec(v_i_1836_);
v_res_1845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10_spec__12(v___x_1829_, v_val_1830_, v_cmd_1831_, v_onUnsolved_boxed_1841_, v___y_15624__boxed_1842_, v_as_1834_, v_sz_boxed_1843_, v_i_boxed_1844_, v_b_1837_, v___y_1838_, v___y_1839_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec_ref(v_as_1834_);
lean_dec_ref(v_val_1830_);
lean_dec_ref(v___x_1829_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10(lean_object* v___x_1846_, lean_object* v_val_1847_, lean_object* v_cmd_1848_, uint8_t v_onUnsolved_1849_, uint8_t v___y_1850_, lean_object* v_as_1851_, size_t v_sz_1852_, size_t v_i_1853_, lean_object* v_b_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
uint8_t v___x_1858_; 
v___x_1858_ = lean_usize_dec_lt(v_i_1853_, v_sz_1852_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1859_; 
lean_dec(v_cmd_1848_);
v___x_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1859_, 0, v_b_1854_);
return v___x_1859_;
}
else
{
lean_object* v_snd_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_2008_; 
v_snd_1860_ = lean_ctor_get(v_b_1854_, 1);
v_isSharedCheck_2008_ = !lean_is_exclusive(v_b_1854_);
if (v_isSharedCheck_2008_ == 0)
{
lean_object* v_unused_2009_; 
v_unused_2009_ = lean_ctor_get(v_b_1854_, 0);
lean_dec(v_unused_2009_);
v___x_1862_ = v_b_1854_;
v_isShared_1863_ = v_isSharedCheck_2008_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_snd_1860_);
lean_dec(v_b_1854_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_2008_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v_fst_1864_; lean_object* v_snd_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_2007_; 
v_fst_1864_ = lean_ctor_get(v_snd_1860_, 0);
v_snd_1865_ = lean_ctor_get(v_snd_1860_, 1);
v_isSharedCheck_2007_ = !lean_is_exclusive(v_snd_1860_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1867_ = v_snd_1860_;
v_isShared_1868_ = v_isSharedCheck_2007_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_snd_1865_);
lean_inc(v_fst_1864_);
lean_dec(v_snd_1860_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_2007_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v_a_1869_; lean_object* v_pos_1870_; lean_object* v_endPos_1871_; uint8_t v_severity_1872_; lean_object* v_data_1873_; lean_object* v___x_1874_; lean_object* v_a_1876_; 
v_a_1869_ = lean_array_uget_borrowed(v_as_1851_, v_i_1853_);
v_pos_1870_ = lean_ctor_get(v_a_1869_, 1);
v_endPos_1871_ = lean_ctor_get(v_a_1869_, 2);
lean_inc(v_endPos_1871_);
v_severity_1872_ = lean_ctor_get_uint8(v_a_1869_, sizeof(void*)*5 + 1);
v_data_1873_ = lean_ctor_get(v_a_1869_, 4);
v___x_1874_ = lean_box(0);
if (v_severity_1872_ == 2)
{
lean_object* v___f_1889_; uint8_t v___x_1890_; 
v___f_1889_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
lean_inc(v_data_1873_);
v___x_1890_ = l_Lean_MessageData_hasTag(v___f_1889_, v_data_1873_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; 
lean_dec(v_endPos_1871_);
lean_del_object(v___x_1862_);
v___x_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1891_, 0, v_fst_1864_);
lean_ctor_set(v___x_1891_, 1, v_snd_1865_);
v_a_1876_ = v___x_1891_;
goto v___jp_1875_;
}
else
{
if (lean_obj_tag(v_endPos_1871_) == 1)
{
lean_object* v_val_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_2004_; 
v_val_1892_ = lean_ctor_get(v_endPos_1871_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v_endPos_1871_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1894_ = v_endPos_1871_;
v_isShared_1895_ = v_isSharedCheck_2004_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_val_1892_);
lean_dec(v_endPos_1871_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_2004_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; uint8_t v___x_1899_; uint8_t v___x_1900_; 
lean_inc_ref(v_pos_1870_);
v___x_1896_ = l_Lean_FileMap_ofPosition(v___x_1846_, v_pos_1870_);
v___x_1897_ = l_Lean_FileMap_ofPosition(v___x_1846_, v_val_1892_);
lean_inc(v___x_1897_);
lean_inc(v___x_1896_);
v___x_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1896_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
v___x_1899_ = 0;
v___x_1900_ = l_Lean_Syntax_Range_includes(v_val_1847_, v___x_1898_, v___x_1899_, v___x_1899_);
if (v___x_1900_ == 0)
{
lean_object* v___x_1901_; 
lean_dec_ref_known(v___x_1898_, 2);
lean_dec(v___x_1897_);
lean_dec(v___x_1896_);
lean_del_object(v___x_1894_);
lean_del_object(v___x_1862_);
v___x_1901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1901_, 0, v_fst_1864_);
lean_ctor_set(v___x_1901_, 1, v_snd_1865_);
v_a_1876_ = v___x_1901_;
goto v___jp_1875_;
}
else
{
lean_object* v___x_1902_; 
lean_inc(v_cmd_1848_);
lean_inc_ref(v___x_1898_);
v___x_1902_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1898_, v_cmd_1848_);
if (lean_obj_tag(v___x_1902_) == 1)
{
lean_object* v_val_1903_; lean_object* v_fst_1904_; lean_object* v_snd_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1968_; 
lean_dec(v___x_1897_);
lean_dec(v___x_1896_);
lean_del_object(v___x_1894_);
v_val_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_val_1903_);
lean_dec_ref_known(v___x_1902_, 1);
v_fst_1904_ = lean_ctor_get(v_val_1903_, 0);
v_snd_1905_ = lean_ctor_get(v_val_1903_, 1);
v_isSharedCheck_1968_ = !lean_is_exclusive(v_val_1903_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1907_ = v_val_1903_;
v_isShared_1908_ = v_isSharedCheck_1968_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_snd_1905_);
lean_inc(v_fst_1904_);
lean_dec(v_val_1903_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1968_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; uint8_t v___y_1966_; lean_object* v___x_1967_; 
v___x_1967_ = l_Lean_Syntax_getPos_x3f(v_fst_1904_, v___x_1899_);
if (lean_obj_tag(v___x_1967_) == 0)
{
v___y_1966_ = v___x_1900_;
goto v___jp_1965_;
}
else
{
lean_dec_ref_known(v___x_1967_, 1);
v___y_1966_ = v___x_1899_;
goto v___jp_1965_;
}
v___jp_1909_:
{
lean_object* v___x_1915_; 
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 1, v_snd_1865_);
lean_ctor_set(v___x_1907_, 0, v_fst_1864_);
v___x_1915_ = v___x_1907_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_fst_1864_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v_snd_1865_);
v___x_1915_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
size_t v_sz_1916_; size_t v___x_1917_; lean_object* v___x_1918_; 
v_sz_1916_ = lean_array_size(v___y_1910_);
v___x_1917_ = ((size_t)0ULL);
v___x_1918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1898_, v_fst_1904_, v_snd_1905_, v___y_1911_, v___y_1910_, v_sz_1916_, v___x_1917_, v___x_1915_);
lean_dec_ref(v___y_1910_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v_fst_1920_; lean_object* v_snd_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1919_);
lean_dec_ref_known(v___x_1918_, 1);
v_fst_1920_ = lean_ctor_get(v_a_1919_, 0);
v_snd_1921_ = lean_ctor_get(v_a_1919_, 1);
v_isSharedCheck_1928_ = !lean_is_exclusive(v_a_1919_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v_a_1919_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_snd_1921_);
lean_inc(v_fst_1920_);
lean_dec(v_a_1919_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_fst_1920_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_snd_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
v_a_1876_ = v___x_1926_;
goto v___jp_1875_;
}
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_del_object(v___x_1867_);
lean_dec(v_cmd_1848_);
v_a_1929_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1918_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1918_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
}
v___jp_1938_:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; uint8_t v___x_1943_; 
lean_inc_ref(v___x_1898_);
v___x_1939_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1898_);
v___x_1940_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1873_);
v___x_1941_ = lean_array_get_size(v___x_1940_);
v___x_1942_ = lean_unsigned_to_nat(0u);
v___x_1943_ = lean_nat_dec_eq(v___x_1941_, v___x_1942_);
if (v___x_1943_ == 0)
{
v___y_1910_ = v___x_1940_;
v___y_1911_ = v___x_1939_;
v___y_1912_ = v___y_1855_;
v___y_1913_ = v___y_1856_;
goto v___jp_1909_;
}
else
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v_scopes_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v_opts_1950_; uint8_t v_hasTrace_1951_; 
v___x_1944_ = l_Lean_inheritedTraceOptions;
v___x_1945_ = lean_st_ref_get(v___x_1944_);
v___x_1946_ = lean_st_ref_get(v___y_1856_);
v_scopes_1947_ = lean_ctor_get(v___x_1946_, 2);
lean_inc(v_scopes_1947_);
lean_dec(v___x_1946_);
v___x_1948_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1949_ = l_List_head_x21___redArg(v___x_1948_, v_scopes_1947_);
lean_dec(v_scopes_1947_);
v_opts_1950_ = lean_ctor_get(v___x_1949_, 1);
lean_inc_ref(v_opts_1950_);
lean_dec(v___x_1949_);
v_hasTrace_1951_ = lean_ctor_get_uint8(v_opts_1950_, sizeof(void*)*1);
if (v_hasTrace_1951_ == 0)
{
lean_dec_ref(v_opts_1950_);
lean_dec(v___x_1945_);
v___y_1910_ = v___x_1940_;
v___y_1911_ = v___x_1939_;
v___y_1912_ = v___y_1855_;
v___y_1913_ = v___y_1856_;
goto v___jp_1909_;
}
else
{
lean_object* v___x_1952_; lean_object* v___x_1953_; uint8_t v___x_1954_; 
v___x_1952_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1953_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1954_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1945_, v_opts_1950_, v___x_1953_);
lean_dec_ref(v_opts_1950_);
lean_dec(v___x_1945_);
if (v___x_1954_ == 0)
{
v___y_1910_ = v___x_1940_;
v___y_1911_ = v___x_1939_;
v___y_1912_ = v___y_1855_;
v___y_1913_ = v___y_1856_;
goto v___jp_1909_;
}
else
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5);
v___x_1956_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1952_, v___x_1955_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_dec_ref_known(v___x_1956_, 1);
v___y_1910_ = v___x_1940_;
v___y_1911_ = v___x_1939_;
v___y_1912_ = v___y_1855_;
v___y_1913_ = v___y_1856_;
goto v___jp_1909_;
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_dec_ref(v___x_1940_);
lean_dec(v___x_1939_);
lean_del_object(v___x_1907_);
lean_dec(v_snd_1905_);
lean_dec(v_fst_1904_);
lean_dec_ref_known(v___x_1898_, 2);
lean_del_object(v___x_1867_);
lean_dec(v_snd_1865_);
lean_dec(v_fst_1864_);
lean_dec(v_cmd_1848_);
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1956_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1956_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
}
}
}
v___jp_1965_:
{
if (v_onUnsolved_1849_ == 0)
{
if (v___y_1850_ == 0)
{
lean_del_object(v___x_1907_);
lean_dec(v_snd_1905_);
lean_dec(v_fst_1904_);
lean_dec_ref_known(v___x_1898_, 2);
goto v___jp_1883_;
}
else
{
if (v___y_1966_ == 0)
{
lean_del_object(v___x_1907_);
lean_dec(v_snd_1905_);
lean_dec(v_fst_1904_);
lean_dec_ref_known(v___x_1898_, 2);
goto v___jp_1883_;
}
else
{
lean_del_object(v___x_1862_);
goto v___jp_1938_;
}
}
}
else
{
lean_del_object(v___x_1862_);
goto v___jp_1938_;
}
}
}
}
else
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v_scopes_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v_opts_1975_; uint8_t v_hasTrace_1976_; 
lean_dec(v___x_1902_);
lean_dec_ref_known(v___x_1898_, 2);
lean_del_object(v___x_1862_);
v___x_1969_ = l_Lean_inheritedTraceOptions;
v___x_1970_ = lean_st_ref_get(v___x_1969_);
v___x_1971_ = lean_st_ref_get(v___y_1856_);
v_scopes_1972_ = lean_ctor_get(v___x_1971_, 2);
lean_inc(v_scopes_1972_);
lean_dec(v___x_1971_);
v___x_1973_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1974_ = l_List_head_x21___redArg(v___x_1973_, v_scopes_1972_);
lean_dec(v_scopes_1972_);
v_opts_1975_ = lean_ctor_get(v___x_1974_, 1);
lean_inc_ref(v_opts_1975_);
lean_dec(v___x_1974_);
v_hasTrace_1976_ = lean_ctor_get_uint8(v_opts_1975_, sizeof(void*)*1);
if (v_hasTrace_1976_ == 0)
{
lean_dec_ref(v_opts_1975_);
lean_dec(v___x_1970_);
lean_dec(v___x_1897_);
lean_dec(v___x_1896_);
lean_del_object(v___x_1894_);
goto v___jp_1887_;
}
else
{
lean_object* v___x_1977_; lean_object* v___x_1978_; uint8_t v___x_1979_; 
v___x_1977_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1978_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1979_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1970_, v_opts_1975_, v___x_1978_);
lean_dec_ref(v_opts_1975_);
lean_dec(v___x_1970_);
if (v___x_1979_ == 0)
{
lean_dec(v___x_1897_);
lean_dec(v___x_1896_);
lean_del_object(v___x_1894_);
goto v___jp_1887_;
}
else
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1983_; 
v___x_1980_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7);
v___x_1981_ = l_Nat_reprFast(v___x_1896_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set_tag(v___x_1894_, 3);
lean_ctor_set(v___x_1894_, 0, v___x_1981_);
v___x_1983_ = v___x_1894_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1981_);
v___x_1983_ = v_reuseFailAlloc_2003_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1984_ = l_Lean_MessageData_ofFormat(v___x_1983_);
v___x_1985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1980_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
v___x_1986_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9);
v___x_1987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1985_);
lean_ctor_set(v___x_1987_, 1, v___x_1986_);
v___x_1988_ = l_Nat_reprFast(v___x_1897_);
v___x_1989_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
v___x_1990_ = l_Lean_MessageData_ofFormat(v___x_1989_);
v___x_1991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1987_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
v___x_1992_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11);
v___x_1993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1991_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___x_1994_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1977_, v___x_1993_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_dec_ref_known(v___x_1994_, 1);
goto v___jp_1887_;
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
lean_del_object(v___x_1867_);
lean_dec(v_snd_1865_);
lean_dec(v_fst_1864_);
lean_dec(v_cmd_1848_);
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1994_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1994_);
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
}
}
}
}
}
else
{
lean_object* v___x_2005_; 
lean_dec(v_endPos_1871_);
lean_del_object(v___x_1862_);
v___x_2005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2005_, 0, v_fst_1864_);
lean_ctor_set(v___x_2005_, 1, v_snd_1865_);
v_a_1876_ = v___x_2005_;
goto v___jp_1875_;
}
}
}
else
{
lean_object* v___x_2006_; 
lean_dec(v_endPos_1871_);
lean_del_object(v___x_1862_);
v___x_2006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2006_, 0, v_fst_1864_);
lean_ctor_set(v___x_2006_, 1, v_snd_1865_);
v_a_1876_ = v___x_2006_;
goto v___jp_1875_;
}
v___jp_1875_:
{
lean_object* v___x_1878_; 
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 1, v_a_1876_);
lean_ctor_set(v___x_1867_, 0, v___x_1874_);
v___x_1878_ = v___x_1867_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1874_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v_a_1876_);
v___x_1878_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
size_t v___x_1879_; size_t v___x_1880_; lean_object* v___x_1881_; 
v___x_1879_ = ((size_t)1ULL);
v___x_1880_ = lean_usize_add(v_i_1853_, v___x_1879_);
v___x_1881_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10_spec__12(v___x_1846_, v_val_1847_, v_cmd_1848_, v_onUnsolved_1849_, v___y_1850_, v_as_1851_, v_sz_1852_, v___x_1880_, v___x_1878_, v___y_1855_, v___y_1856_);
return v___x_1881_;
}
}
v___jp_1883_:
{
lean_object* v___x_1885_; 
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 1, v_snd_1865_);
lean_ctor_set(v___x_1862_, 0, v_fst_1864_);
v___x_1885_ = v___x_1862_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_fst_1864_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v_snd_1865_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
v_a_1876_ = v___x_1885_;
goto v___jp_1875_;
}
}
v___jp_1887_:
{
lean_object* v___x_1888_; 
v___x_1888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1888_, 0, v_fst_1864_);
lean_ctor_set(v___x_1888_, 1, v_snd_1865_);
v_a_1876_ = v___x_1888_;
goto v___jp_1875_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10___boxed(lean_object* v___x_2010_, lean_object* v_val_2011_, lean_object* v_cmd_2012_, lean_object* v_onUnsolved_2013_, lean_object* v___y_2014_, lean_object* v_as_2015_, lean_object* v_sz_2016_, lean_object* v_i_2017_, lean_object* v_b_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
uint8_t v_onUnsolved_boxed_2022_; uint8_t v___y_15956__boxed_2023_; size_t v_sz_boxed_2024_; size_t v_i_boxed_2025_; lean_object* v_res_2026_; 
v_onUnsolved_boxed_2022_ = lean_unbox(v_onUnsolved_2013_);
v___y_15956__boxed_2023_ = lean_unbox(v___y_2014_);
v_sz_boxed_2024_ = lean_unbox_usize(v_sz_2016_);
lean_dec(v_sz_2016_);
v_i_boxed_2025_ = lean_unbox_usize(v_i_2017_);
lean_dec(v_i_2017_);
v_res_2026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10(v___x_2010_, v_val_2011_, v_cmd_2012_, v_onUnsolved_boxed_2022_, v___y_15956__boxed_2023_, v_as_2015_, v_sz_boxed_2024_, v_i_boxed_2025_, v_b_2018_, v___y_2019_, v___y_2020_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec_ref(v_as_2015_);
lean_dec_ref(v_val_2011_);
lean_dec_ref(v___x_2010_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(lean_object* v_init_2027_, lean_object* v___x_2028_, lean_object* v_val_2029_, lean_object* v_cmd_2030_, uint8_t v_onUnsolved_2031_, uint8_t v___y_2032_, lean_object* v_n_2033_, lean_object* v_b_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
if (lean_obj_tag(v_n_2033_) == 0)
{
lean_object* v_cs_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; size_t v_sz_2041_; size_t v___x_2042_; lean_object* v___x_2043_; 
v_cs_2038_ = lean_ctor_get(v_n_2033_, 0);
v___x_2039_ = lean_box(0);
v___x_2040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
lean_ctor_set(v___x_2040_, 1, v_b_2034_);
v_sz_2041_ = lean_array_size(v_cs_2038_);
v___x_2042_ = ((size_t)0ULL);
v___x_2043_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__9(v_init_2027_, v___x_2028_, v_val_2029_, v_cmd_2030_, v_onUnsolved_2031_, v___y_2032_, v_cs_2038_, v_sz_2041_, v___x_2042_, v___x_2040_, v___y_2035_, v___y_2036_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2058_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2046_ = v___x_2043_;
v_isShared_2047_ = v_isSharedCheck_2058_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2043_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2058_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v_fst_2048_; 
v_fst_2048_ = lean_ctor_get(v_a_2044_, 0);
if (lean_obj_tag(v_fst_2048_) == 0)
{
lean_object* v_snd_2049_; lean_object* v___x_2050_; lean_object* v___x_2052_; 
v_snd_2049_ = lean_ctor_get(v_a_2044_, 1);
lean_inc(v_snd_2049_);
lean_dec(v_a_2044_);
v___x_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2050_, 0, v_snd_2049_);
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 0, v___x_2050_);
v___x_2052_ = v___x_2046_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
else
{
lean_object* v_val_2054_; lean_object* v___x_2056_; 
lean_inc_ref(v_fst_2048_);
lean_dec(v_a_2044_);
v_val_2054_ = lean_ctor_get(v_fst_2048_, 0);
lean_inc(v_val_2054_);
lean_dec_ref_known(v_fst_2048_, 1);
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 0, v_val_2054_);
v___x_2056_ = v___x_2046_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_val_2054_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
v_a_2059_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2043_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2043_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
else
{
lean_object* v_vs_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; size_t v_sz_2070_; size_t v___x_2071_; lean_object* v___x_2072_; 
v_vs_2067_ = lean_ctor_get(v_n_2033_, 0);
v___x_2068_ = lean_box(0);
v___x_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
lean_ctor_set(v___x_2069_, 1, v_b_2034_);
v_sz_2070_ = lean_array_size(v_vs_2067_);
v___x_2071_ = ((size_t)0ULL);
v___x_2072_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10(v___x_2028_, v_val_2029_, v_cmd_2030_, v_onUnsolved_2031_, v___y_2032_, v_vs_2067_, v_sz_2070_, v___x_2071_, v___x_2069_, v___y_2035_, v___y_2036_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2087_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2075_ = v___x_2072_;
v_isShared_2076_ = v_isSharedCheck_2087_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2072_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2087_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v_fst_2077_; 
v_fst_2077_ = lean_ctor_get(v_a_2073_, 0);
if (lean_obj_tag(v_fst_2077_) == 0)
{
lean_object* v_snd_2078_; lean_object* v___x_2079_; lean_object* v___x_2081_; 
v_snd_2078_ = lean_ctor_get(v_a_2073_, 1);
lean_inc(v_snd_2078_);
lean_dec(v_a_2073_);
v___x_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2079_, 0, v_snd_2078_);
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 0, v___x_2079_);
v___x_2081_ = v___x_2075_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
else
{
lean_object* v_val_2083_; lean_object* v___x_2085_; 
lean_inc_ref(v_fst_2077_);
lean_dec(v_a_2073_);
v_val_2083_ = lean_ctor_get(v_fst_2077_, 0);
lean_inc(v_val_2083_);
lean_dec_ref_known(v_fst_2077_, 1);
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 0, v_val_2083_);
v___x_2085_ = v___x_2075_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_val_2083_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
v_a_2088_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2072_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2072_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__9(lean_object* v_init_2096_, lean_object* v___x_2097_, lean_object* v_val_2098_, lean_object* v_cmd_2099_, uint8_t v_onUnsolved_2100_, uint8_t v___y_2101_, lean_object* v_as_2102_, size_t v_sz_2103_, size_t v_i_2104_, lean_object* v_b_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
uint8_t v___x_2109_; 
v___x_2109_ = lean_usize_dec_lt(v_i_2104_, v_sz_2103_);
if (v___x_2109_ == 0)
{
lean_object* v___x_2110_; 
lean_dec(v_cmd_2099_);
v___x_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2110_, 0, v_b_2105_);
return v___x_2110_;
}
else
{
lean_object* v_snd_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2145_; 
v_snd_2111_ = lean_ctor_get(v_b_2105_, 1);
v_isSharedCheck_2145_ = !lean_is_exclusive(v_b_2105_);
if (v_isSharedCheck_2145_ == 0)
{
lean_object* v_unused_2146_; 
v_unused_2146_ = lean_ctor_get(v_b_2105_, 0);
lean_dec(v_unused_2146_);
v___x_2113_ = v_b_2105_;
v_isShared_2114_ = v_isSharedCheck_2145_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_snd_2111_);
lean_dec(v_b_2105_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2145_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v_a_2115_; lean_object* v___x_2116_; 
v_a_2115_ = lean_array_uget_borrowed(v_as_2102_, v_i_2104_);
lean_inc(v_snd_2111_);
lean_inc(v_cmd_2099_);
v___x_2116_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(v_init_2096_, v___x_2097_, v_val_2098_, v_cmd_2099_, v_onUnsolved_2100_, v___y_2101_, v_a_2115_, v_snd_2111_, v___y_2106_, v___y_2107_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2136_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2119_ = v___x_2116_;
v_isShared_2120_ = v_isSharedCheck_2136_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2116_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2136_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
if (lean_obj_tag(v_a_2117_) == 0)
{
lean_object* v___x_2121_; lean_object* v___x_2123_; 
lean_dec(v_cmd_2099_);
v___x_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2121_, 0, v_a_2117_);
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v___x_2121_);
v___x_2123_ = v___x_2113_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2121_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v_snd_2111_);
v___x_2123_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
lean_object* v___x_2125_; 
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 0, v___x_2123_);
v___x_2125_ = v___x_2119_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2123_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
else
{
lean_object* v_a_2128_; lean_object* v___x_2129_; lean_object* v___x_2131_; 
lean_del_object(v___x_2119_);
lean_dec(v_snd_2111_);
v_a_2128_ = lean_ctor_get(v_a_2117_, 0);
lean_inc(v_a_2128_);
lean_dec_ref_known(v_a_2117_, 1);
v___x_2129_ = lean_box(0);
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 1, v_a_2128_);
lean_ctor_set(v___x_2113_, 0, v___x_2129_);
v___x_2131_ = v___x_2113_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2129_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v_a_2128_);
v___x_2131_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
size_t v___x_2132_; size_t v___x_2133_; 
v___x_2132_ = ((size_t)1ULL);
v___x_2133_ = lean_usize_add(v_i_2104_, v___x_2132_);
v_i_2104_ = v___x_2133_;
v_b_2105_ = v___x_2131_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_del_object(v___x_2113_);
lean_dec(v_snd_2111_);
lean_dec(v_cmd_2099_);
v_a_2137_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2116_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2116_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__9___boxed(lean_object* v_init_2147_, lean_object* v___x_2148_, lean_object* v_val_2149_, lean_object* v_cmd_2150_, lean_object* v_onUnsolved_2151_, lean_object* v___y_2152_, lean_object* v_as_2153_, lean_object* v_sz_2154_, lean_object* v_i_2155_, lean_object* v_b_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
uint8_t v_onUnsolved_boxed_2160_; uint8_t v___y_16257__boxed_2161_; size_t v_sz_boxed_2162_; size_t v_i_boxed_2163_; lean_object* v_res_2164_; 
v_onUnsolved_boxed_2160_ = lean_unbox(v_onUnsolved_2151_);
v___y_16257__boxed_2161_ = lean_unbox(v___y_2152_);
v_sz_boxed_2162_ = lean_unbox_usize(v_sz_2154_);
lean_dec(v_sz_2154_);
v_i_boxed_2163_ = lean_unbox_usize(v_i_2155_);
lean_dec(v_i_2155_);
v_res_2164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__9(v_init_2147_, v___x_2148_, v_val_2149_, v_cmd_2150_, v_onUnsolved_boxed_2160_, v___y_16257__boxed_2161_, v_as_2153_, v_sz_boxed_2162_, v_i_boxed_2163_, v_b_2156_, v___y_2157_, v___y_2158_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec_ref(v_as_2153_);
lean_dec_ref(v_val_2149_);
lean_dec_ref(v___x_2148_);
lean_dec_ref(v_init_2147_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___boxed(lean_object* v_init_2165_, lean_object* v___x_2166_, lean_object* v_val_2167_, lean_object* v_cmd_2168_, lean_object* v_onUnsolved_2169_, lean_object* v___y_2170_, lean_object* v_n_2171_, lean_object* v_b_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
uint8_t v_onUnsolved_boxed_2176_; uint8_t v___y_16279__boxed_2177_; lean_object* v_res_2178_; 
v_onUnsolved_boxed_2176_ = lean_unbox(v_onUnsolved_2169_);
v___y_16279__boxed_2177_ = lean_unbox(v___y_2170_);
v_res_2178_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(v_init_2165_, v___x_2166_, v_val_2167_, v_cmd_2168_, v_onUnsolved_boxed_2176_, v___y_16279__boxed_2177_, v_n_2171_, v_b_2172_, v___y_2173_, v___y_2174_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec_ref(v_n_2171_);
lean_dec_ref(v_val_2167_);
lean_dec_ref(v___x_2166_);
lean_dec_ref(v_init_2165_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(lean_object* v___x_2179_, lean_object* v_val_2180_, lean_object* v_cmd_2181_, uint8_t v_onUnsolved_2182_, uint8_t v___y_2183_, lean_object* v_t_2184_, lean_object* v_init_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v_root_2189_; lean_object* v_tail_2190_; lean_object* v___x_2191_; 
v_root_2189_ = lean_ctor_get(v_t_2184_, 0);
v_tail_2190_ = lean_ctor_get(v_t_2184_, 1);
lean_inc(v_cmd_2181_);
lean_inc_ref(v_init_2185_);
v___x_2191_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(v_init_2185_, v___x_2179_, v_val_2180_, v_cmd_2181_, v_onUnsolved_2182_, v___y_2183_, v_root_2189_, v_init_2185_, v___y_2186_, v___y_2187_);
lean_dec_ref(v_init_2185_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2228_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2194_ = v___x_2191_;
v_isShared_2195_ = v_isSharedCheck_2228_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2191_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2228_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
if (lean_obj_tag(v_a_2192_) == 0)
{
lean_object* v_a_2196_; lean_object* v___x_2198_; 
lean_dec(v_cmd_2181_);
v_a_2196_ = lean_ctor_get(v_a_2192_, 0);
lean_inc(v_a_2196_);
lean_dec_ref_known(v_a_2192_, 1);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 0, v_a_2196_);
v___x_2198_ = v___x_2194_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2196_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; size_t v_sz_2203_; size_t v___x_2204_; lean_object* v___x_2205_; 
lean_del_object(v___x_2194_);
v_a_2200_ = lean_ctor_get(v_a_2192_, 0);
lean_inc(v_a_2200_);
lean_dec_ref_known(v_a_2192_, 1);
v___x_2201_ = lean_box(0);
v___x_2202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
lean_ctor_set(v___x_2202_, 1, v_a_2200_);
v_sz_2203_ = lean_array_size(v_tail_2190_);
v___x_2204_ = ((size_t)0ULL);
v___x_2205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8(v___x_2179_, v_val_2180_, v_cmd_2181_, v_onUnsolved_2182_, v___y_2183_, v_tail_2190_, v_sz_2203_, v___x_2204_, v___x_2202_, v___y_2186_, v___y_2187_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2219_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2208_ = v___x_2205_;
v_isShared_2209_ = v_isSharedCheck_2219_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2205_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2219_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v_fst_2210_; 
v_fst_2210_ = lean_ctor_get(v_a_2206_, 0);
if (lean_obj_tag(v_fst_2210_) == 0)
{
lean_object* v_snd_2211_; lean_object* v___x_2213_; 
v_snd_2211_ = lean_ctor_get(v_a_2206_, 1);
lean_inc(v_snd_2211_);
lean_dec(v_a_2206_);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v_snd_2211_);
v___x_2213_ = v___x_2208_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_snd_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
else
{
lean_object* v_val_2215_; lean_object* v___x_2217_; 
lean_inc_ref(v_fst_2210_);
lean_dec(v_a_2206_);
v_val_2215_ = lean_ctor_get(v_fst_2210_, 0);
lean_inc(v_val_2215_);
lean_dec_ref_known(v_fst_2210_, 1);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v_val_2215_);
v___x_2217_ = v___x_2208_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_val_2215_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
v_a_2220_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2205_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2205_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
}
}
else
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2236_; 
lean_dec(v_cmd_2181_);
v_a_2229_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2231_ = v___x_2191_;
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2191_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2232_ == 0)
{
v___x_2234_ = v___x_2231_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2229_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___boxed(lean_object* v___x_2237_, lean_object* v_val_2238_, lean_object* v_cmd_2239_, lean_object* v_onUnsolved_2240_, lean_object* v___y_2241_, lean_object* v_t_2242_, lean_object* v_init_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
uint8_t v_onUnsolved_boxed_2247_; uint8_t v___y_16470__boxed_2248_; lean_object* v_res_2249_; 
v_onUnsolved_boxed_2247_ = lean_unbox(v_onUnsolved_2240_);
v___y_16470__boxed_2248_ = lean_unbox(v___y_2241_);
v_res_2249_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_2237_, v_val_2238_, v_cmd_2239_, v_onUnsolved_boxed_2247_, v___y_16470__boxed_2248_, v_t_2242_, v_init_2243_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec_ref(v_t_2242_);
lean_dec_ref(v_val_2238_);
lean_dec_ref(v___x_2237_);
return v_res_2249_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0(void){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2250_ = lean_box(0);
v___x_2251_ = lean_unsigned_to_nat(16u);
v___x_2252_ = lean_mk_array(v___x_2251_, v___x_2250_);
return v___x_2252_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1(void){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2253_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0);
v___x_2254_ = lean_unsigned_to_nat(0u);
v___x_2255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
lean_ctor_set(v___x_2255_, 1, v___x_2253_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(lean_object* v_cmd_2259_, lean_object* v_opts_2260_, lean_object* v_tree_2261_, lean_object* v_msgs_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_){
_start:
{
lean_object* v___y_2267_; lean_object* v___y_2268_; uint8_t v___y_2269_; lean_object* v___y_2270_; uint8_t v___y_2271_; uint8_t v___y_2272_; uint8_t v___y_2298_; uint8_t v___y_2299_; lean_object* v_acc_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; lean_object* v___f_2304_; uint8_t v___y_2306_; lean_object* v___x_2313_; uint8_t v___x_2314_; 
v___f_2304_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__2));
v___x_2313_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_2314_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2260_, v___x_2313_);
if (v___x_2314_ == 0)
{
lean_object* v___x_2315_; uint8_t v___x_2316_; 
v___x_2315_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_2316_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2260_, v___x_2315_);
v___y_2306_ = v___x_2316_;
goto v___jp_2305_;
}
else
{
v___y_2306_ = v___x_2314_;
goto v___jp_2305_;
}
v___jp_2266_:
{
lean_object* v___x_2273_; 
v___x_2273_ = l_Lean_Syntax_getRange_x3f(v_cmd_2259_, v___y_2272_);
if (lean_obj_tag(v___x_2273_) == 1)
{
lean_object* v_val_2274_; lean_object* v_fileMap_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v_val_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_val_2274_);
lean_dec_ref_known(v___x_2273_, 1);
v_fileMap_2275_ = lean_ctor_get(v___y_2267_, 1);
v___x_2276_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1);
v___x_2277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___y_2268_);
lean_ctor_set(v___x_2277_, 1, v___x_2276_);
v___x_2278_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v_fileMap_2275_, v_val_2274_, v_cmd_2259_, v___y_2269_, v___y_2271_, v_msgs_2262_, v___x_2277_, v___y_2267_, v___y_2270_);
lean_dec(v_val_2274_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2287_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2281_ = v___x_2278_;
v_isShared_2282_ = v_isSharedCheck_2287_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2278_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2287_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v_fst_2283_; lean_object* v___x_2285_; 
v_fst_2283_ = lean_ctor_get(v_a_2279_, 0);
lean_inc(v_fst_2283_);
lean_dec(v_a_2279_);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 0, v_fst_2283_);
v___x_2285_ = v___x_2281_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_fst_2283_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
v_a_2288_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___x_2278_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2278_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
else
{
lean_object* v___x_2296_; 
lean_dec(v___x_2273_);
lean_dec(v_cmd_2259_);
v___x_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2296_, 0, v___y_2268_);
return v___x_2296_;
}
}
v___jp_2297_:
{
if (v___y_2298_ == 0)
{
if (v___y_2299_ == 0)
{
lean_object* v___x_2303_; 
lean_dec(v_cmd_2259_);
v___x_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2303_, 0, v_acc_2300_);
return v___x_2303_;
}
else
{
v___y_2267_ = v___y_2301_;
v___y_2268_ = v_acc_2300_;
v___y_2269_ = v___y_2298_;
v___y_2270_ = v___y_2302_;
v___y_2271_ = v___y_2299_;
v___y_2272_ = v___y_2299_;
goto v___jp_2266_;
}
}
else
{
v___y_2267_ = v___y_2301_;
v___y_2268_ = v_acc_2300_;
v___y_2269_ = v___y_2298_;
v___y_2270_ = v___y_2302_;
v___y_2271_ = v___y_2299_;
v___y_2272_ = v___y_2298_;
goto v___jp_2266_;
}
}
v___jp_2305_:
{
lean_object* v___x_2307_; uint8_t v_onUnsolved_2308_; lean_object* v___x_2309_; uint8_t v_onSorry_2310_; lean_object* v_acc_2311_; 
v___x_2307_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
v_onUnsolved_2308_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2260_, v___x_2307_);
v___x_2309_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v_onSorry_2310_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2260_, v___x_2309_);
v_acc_2311_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__3));
if (v_onSorry_2310_ == 0)
{
lean_dec_ref(v_tree_2261_);
v___y_2298_ = v_onUnsolved_2308_;
v___y_2299_ = v___y_2306_;
v_acc_2300_ = v_acc_2311_;
v___y_2301_ = v_a_2263_;
v___y_2302_ = v_a_2264_;
goto v___jp_2297_;
}
else
{
lean_object* v_acc_2312_; 
v_acc_2312_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_2304_, v_acc_2311_, v_tree_2261_);
v___y_2298_ = v_onUnsolved_2308_;
v___y_2299_ = v___y_2306_;
v_acc_2300_ = v_acc_2312_;
v___y_2301_ = v_a_2263_;
v___y_2302_ = v_a_2264_;
goto v___jp_2297_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___boxed(lean_object* v_cmd_2317_, lean_object* v_opts_2318_, lean_object* v_tree_2319_, lean_object* v_msgs_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_cmd_2317_, v_opts_2318_, v_tree_2319_, v_msgs_2320_, v_a_2321_, v_a_2322_);
lean_dec(v_a_2322_);
lean_dec_ref(v_a_2321_);
lean_dec_ref(v_msgs_2320_);
lean_dec_ref(v_opts_2318_);
return v_res_2324_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(lean_object* v_00_u03b2_2325_, lean_object* v_m_2326_, lean_object* v_a_2327_){
_start:
{
uint8_t v___x_2328_; 
v___x_2328_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(v_m_2326_, v_a_2327_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___boxed(lean_object* v_00_u03b2_2329_, lean_object* v_m_2330_, lean_object* v_a_2331_){
_start:
{
uint8_t v_res_2332_; lean_object* v_r_2333_; 
v_res_2332_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_00_u03b2_2329_, v_m_2330_, v_a_2331_);
lean_dec_ref(v_a_2331_);
lean_dec_ref(v_m_2330_);
v_r_2333_ = lean_box(v_res_2332_);
return v_r_2333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1(lean_object* v_00_u03b2_2334_, lean_object* v_m_2335_, lean_object* v_a_2336_, lean_object* v_b_2337_){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_m_2335_, v_a_2336_, v_b_2337_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2(lean_object* v___x_2339_, lean_object* v_fst_2340_, lean_object* v_snd_2341_, lean_object* v___x_2342_, lean_object* v_as_2343_, size_t v_sz_2344_, size_t v_i_2345_, lean_object* v_b_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_2339_, v_fst_2340_, v_snd_2341_, v___x_2342_, v_as_2343_, v_sz_2344_, v_i_2345_, v_b_2346_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___boxed(lean_object* v___x_2351_, lean_object* v_fst_2352_, lean_object* v_snd_2353_, lean_object* v___x_2354_, lean_object* v_as_2355_, lean_object* v_sz_2356_, lean_object* v_i_2357_, lean_object* v_b_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
size_t v_sz_boxed_2362_; size_t v_i_boxed_2363_; lean_object* v_res_2364_; 
v_sz_boxed_2362_ = lean_unbox_usize(v_sz_2356_);
lean_dec(v_sz_2356_);
v_i_boxed_2363_ = lean_unbox_usize(v_i_2357_);
lean_dec(v_i_2357_);
v_res_2364_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2(v___x_2351_, v_fst_2352_, v_snd_2353_, v___x_2354_, v_as_2355_, v_sz_boxed_2362_, v_i_boxed_2363_, v_b_2358_, v___y_2359_, v___y_2360_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec_ref(v_as_2355_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5(lean_object* v_msgData_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
lean_object* v___x_2369_; 
v___x_2369_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(v_msgData_2365_, v___y_2367_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___boxed(lean_object* v_msgData_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5(v_msgData_2370_, v___y_2371_, v___y_2372_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
return v_res_2374_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0(lean_object* v_00_u03b2_2375_, lean_object* v_a_2376_, lean_object* v_x_2377_){
_start:
{
uint8_t v___x_2378_; 
v___x_2378_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(v_a_2376_, v_x_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2379_, lean_object* v_a_2380_, lean_object* v_x_2381_){
_start:
{
uint8_t v_res_2382_; lean_object* v_r_2383_; 
v_res_2382_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0(v_00_u03b2_2379_, v_a_2380_, v_x_2381_);
lean_dec(v_x_2381_);
lean_dec_ref(v_a_2380_);
v_r_2383_ = lean_box(v_res_2382_);
return v_r_2383_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2(lean_object* v_00_u03b2_2384_, lean_object* v_data_2385_){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2___redArg(v_data_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2387_, lean_object* v_i_2388_, lean_object* v_source_2389_, lean_object* v_target_2390_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3___redArg(v_i_2388_, v_source_2389_, v_target_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3_spec__8(lean_object* v_00_u03b2_2392_, lean_object* v_x_2393_, lean_object* v_x_2394_){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3_spec__8___redArg(v_x_2393_, v_x_2394_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(lean_object* v_x_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v___x_2404_; 
lean_inc(v___y_2398_);
lean_inc_ref(v___y_2397_);
v___x_2404_ = lean_apply_7(v_x_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, lean_box(0));
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed(lean_object* v_x_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(v_x_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(lean_object* v_mvarId_2414_, lean_object* v_x_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v___f_2423_; lean_object* v___x_2424_; 
lean_inc(v___y_2417_);
lean_inc_ref(v___y_2416_);
v___f_2423_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2423_, 0, v_x_2415_);
lean_closure_set(v___f_2423_, 1, v___y_2416_);
lean_closure_set(v___f_2423_, 2, v___y_2417_);
v___x_2424_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2414_, v___f_2423_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2424_) == 0)
{
return v___x_2424_;
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___x_2424_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2424_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___boxed(lean_object* v_mvarId_2433_, lean_object* v_x_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2433_, v_x_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(lean_object* v_00_u03b1_2443_, lean_object* v_mvarId_2444_, lean_object* v_x_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2444_, v_x_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed(lean_object* v_00_u03b1_2454_, lean_object* v_mvarId_2455_, lean_object* v_x_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(v_00_u03b1_2454_, v_mvarId_2455_, v_x_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(lean_object* v_____r_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2479_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___boxed(lean_object* v_____r_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(v_____r_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(lean_object* v_____r_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2498_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1___boxed(lean_object* v_____r_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(v_____r_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
return v_res_2506_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(uint8_t v___x_2507_, lean_object* v_x_2508_){
_start:
{
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2___boxed(lean_object* v___x_2509_, lean_object* v_x_2510_){
_start:
{
uint8_t v___x_11848__boxed_2511_; uint8_t v_res_2512_; lean_object* v_r_2513_; 
v___x_11848__boxed_2511_ = lean_unbox(v___x_2509_);
v_res_2512_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(v___x_11848__boxed_2511_, v_x_2510_);
lean_dec(v_x_2510_);
v_r_2513_ = lean_box(v_res_2512_);
return v_r_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(lean_object* v_msgData_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v___x_2520_; lean_object* v_env_2521_; lean_object* v___x_2522_; lean_object* v_mctx_2523_; lean_object* v_lctx_2524_; lean_object* v_options_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2520_ = lean_st_ref_get(v___y_2518_);
v_env_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc_ref(v_env_2521_);
lean_dec(v___x_2520_);
v___x_2522_ = lean_st_ref_get(v___y_2516_);
v_mctx_2523_ = lean_ctor_get(v___x_2522_, 0);
lean_inc_ref(v_mctx_2523_);
lean_dec(v___x_2522_);
v_lctx_2524_ = lean_ctor_get(v___y_2515_, 2);
v_options_2525_ = lean_ctor_get(v___y_2517_, 2);
lean_inc_ref(v_options_2525_);
lean_inc_ref(v_lctx_2524_);
v___x_2526_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2526_, 0, v_env_2521_);
lean_ctor_set(v___x_2526_, 1, v_mctx_2523_);
lean_ctor_set(v___x_2526_, 2, v_lctx_2524_);
lean_ctor_set(v___x_2526_, 3, v_options_2525_);
v___x_2527_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
lean_ctor_set(v___x_2527_, 1, v_msgData_2514_);
v___x_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2___boxed(lean_object* v_msgData_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msgData_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(lean_object* v_cls_2536_, lean_object* v_msg_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
lean_object* v_ref_2543_; lean_object* v___x_2544_; lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2589_; 
v_ref_2543_ = lean_ctor_get(v___y_2540_, 5);
v___x_2544_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2547_ = v___x_2544_;
v_isShared_2548_ = v_isSharedCheck_2589_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2544_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2589_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2549_; lean_object* v_traceState_2550_; lean_object* v_env_2551_; lean_object* v_nextMacroScope_2552_; lean_object* v_ngen_2553_; lean_object* v_auxDeclNGen_2554_; lean_object* v_cache_2555_; lean_object* v_messages_2556_; lean_object* v_infoState_2557_; lean_object* v_snapshotTasks_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2588_; 
v___x_2549_ = lean_st_ref_take(v___y_2541_);
v_traceState_2550_ = lean_ctor_get(v___x_2549_, 4);
v_env_2551_ = lean_ctor_get(v___x_2549_, 0);
v_nextMacroScope_2552_ = lean_ctor_get(v___x_2549_, 1);
v_ngen_2553_ = lean_ctor_get(v___x_2549_, 2);
v_auxDeclNGen_2554_ = lean_ctor_get(v___x_2549_, 3);
v_cache_2555_ = lean_ctor_get(v___x_2549_, 5);
v_messages_2556_ = lean_ctor_get(v___x_2549_, 6);
v_infoState_2557_ = lean_ctor_get(v___x_2549_, 7);
v_snapshotTasks_2558_ = lean_ctor_get(v___x_2549_, 8);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2560_ = v___x_2549_;
v_isShared_2561_ = v_isSharedCheck_2588_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_snapshotTasks_2558_);
lean_inc(v_infoState_2557_);
lean_inc(v_messages_2556_);
lean_inc(v_cache_2555_);
lean_inc(v_traceState_2550_);
lean_inc(v_auxDeclNGen_2554_);
lean_inc(v_ngen_2553_);
lean_inc(v_nextMacroScope_2552_);
lean_inc(v_env_2551_);
lean_dec(v___x_2549_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2588_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
uint64_t v_tid_2562_; lean_object* v_traces_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2587_; 
v_tid_2562_ = lean_ctor_get_uint64(v_traceState_2550_, sizeof(void*)*1);
v_traces_2563_ = lean_ctor_get(v_traceState_2550_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v_traceState_2550_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2565_ = v_traceState_2550_;
v_isShared_2566_ = v_isSharedCheck_2587_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_traces_2563_);
lean_dec(v_traceState_2550_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2587_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2567_; double v___x_2568_; uint8_t v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2567_ = lean_box(0);
v___x_2568_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0);
v___x_2569_ = 0;
v___x_2570_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2571_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2571_, 0, v_cls_2536_);
lean_ctor_set(v___x_2571_, 1, v___x_2567_);
lean_ctor_set(v___x_2571_, 2, v___x_2570_);
lean_ctor_set_float(v___x_2571_, sizeof(void*)*3, v___x_2568_);
lean_ctor_set_float(v___x_2571_, sizeof(void*)*3 + 8, v___x_2568_);
lean_ctor_set_uint8(v___x_2571_, sizeof(void*)*3 + 16, v___x_2569_);
v___x_2572_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__1));
v___x_2573_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2571_);
lean_ctor_set(v___x_2573_, 1, v_a_2545_);
lean_ctor_set(v___x_2573_, 2, v___x_2572_);
lean_inc(v_ref_2543_);
v___x_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2574_, 0, v_ref_2543_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
v___x_2575_ = l_Lean_PersistentArray_push___redArg(v_traces_2563_, v___x_2574_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 0, v___x_2575_);
v___x_2577_ = v___x_2565_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2575_);
lean_ctor_set_uint64(v_reuseFailAlloc_2586_, sizeof(void*)*1, v_tid_2562_);
v___x_2577_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v___x_2579_; 
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 4, v___x_2577_);
v___x_2579_ = v___x_2560_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_env_2551_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v_nextMacroScope_2552_);
lean_ctor_set(v_reuseFailAlloc_2585_, 2, v_ngen_2553_);
lean_ctor_set(v_reuseFailAlloc_2585_, 3, v_auxDeclNGen_2554_);
lean_ctor_set(v_reuseFailAlloc_2585_, 4, v___x_2577_);
lean_ctor_set(v_reuseFailAlloc_2585_, 5, v_cache_2555_);
lean_ctor_set(v_reuseFailAlloc_2585_, 6, v_messages_2556_);
lean_ctor_set(v_reuseFailAlloc_2585_, 7, v_infoState_2557_);
lean_ctor_set(v_reuseFailAlloc_2585_, 8, v_snapshotTasks_2558_);
v___x_2579_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2583_; 
v___x_2580_ = lean_st_ref_set(v___y_2541_, v___x_2579_);
v___x_2581_ = lean_box(0);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 0, v___x_2581_);
v___x_2583_ = v___x_2547_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2581_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg___boxed(lean_object* v_cls_2590_, lean_object* v_msg_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_2590_, v_msg_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
return v_res_2597_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2599_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__0));
v___x_2600_ = l_Lean_stringToMessageData(v___x_2599_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(lean_object* v___x_2601_, lean_object* v___x_2602_, lean_object* v___x_2603_, lean_object* v___f_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v___x_2612_; lean_object* v_a_2614_; lean_object* v___y_2618_; lean_object* v___x_2632_; 
v___x_2612_ = lean_st_mk_ref(v___x_2601_);
v___x_2632_ = l_Lean_Elab_Tactic_saveState___redArg(v___x_2612_, v___y_2606_, v___y_2608_, v___y_2610_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; lean_object* v___x_2634_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_a_2633_);
lean_dec_ref_known(v___x_2632_, 1);
v___x_2634_ = l_Lean_Elab_Tactic_Try_collectTryCoreSuggestions(v___x_2602_, v___x_2603_, v___x_2612_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_a_2635_; 
lean_dec(v_a_2633_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v___f_2604_);
lean_dec_ref(v___x_2603_);
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
lean_inc(v_a_2635_);
lean_dec_ref_known(v___x_2634_, 1);
v_a_2614_ = v_a_2635_;
goto v___jp_2613_;
}
else
{
lean_object* v_a_2636_; uint8_t v___y_2638_; uint8_t v___x_2681_; 
v_a_2636_ = lean_ctor_get(v___x_2634_, 0);
lean_inc(v_a_2636_);
v___x_2681_ = l_Lean_Exception_isInterrupt(v_a_2636_);
if (v___x_2681_ == 0)
{
uint8_t v___x_2682_; 
lean_inc(v_a_2636_);
v___x_2682_ = l_Lean_Exception_isRuntime(v_a_2636_);
v___y_2638_ = v___x_2682_;
goto v___jp_2637_;
}
else
{
v___y_2638_ = v___x_2681_;
goto v___jp_2637_;
}
v___jp_2637_:
{
if (v___y_2638_ == 0)
{
lean_object* v___x_2639_; 
lean_dec_ref_known(v___x_2634_, 1);
v___x_2639_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2633_, v___y_2638_, v___x_2612_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2671_; 
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2671_ == 0)
{
lean_object* v_unused_2672_; 
v_unused_2672_ = lean_ctor_get(v___x_2639_, 0);
lean_dec(v_unused_2672_);
v___x_2641_ = v___x_2639_;
v_isShared_2642_ = v_isSharedCheck_2671_;
goto v_resetjp_2640_;
}
else
{
lean_dec(v___x_2639_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2671_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
uint8_t v___x_2643_; 
v___x_2643_ = l_Lean_Exception_isInterrupt(v_a_2636_);
if (v___x_2643_ == 0)
{
uint8_t v___x_2644_; 
lean_inc(v_a_2636_);
v___x_2644_ = l_Lean_Exception_isMaxRecDepth(v_a_2636_);
if (v___x_2644_ == 0)
{
lean_object* v_options_2645_; uint8_t v_hasTrace_2646_; 
lean_del_object(v___x_2641_);
v_options_2645_ = lean_ctor_get(v___y_2609_, 2);
v_hasTrace_2646_ = lean_ctor_get_uint8(v_options_2645_, sizeof(void*)*1);
if (v_hasTrace_2646_ == 0)
{
lean_dec(v_a_2636_);
goto v___jp_2629_;
}
else
{
lean_object* v_inheritedTraceOptions_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; uint8_t v___x_2650_; 
v_inheritedTraceOptions_2647_ = lean_ctor_get(v___y_2609_, 13);
v___x_2648_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2649_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_2650_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2647_, v_options_2645_, v___x_2649_);
if (v___x_2650_ == 0)
{
lean_dec(v_a_2636_);
goto v___jp_2629_;
}
else
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2651_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_2652_ = l_Lean_Exception_toMessageData(v_a_2636_);
v___x_2653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2651_);
lean_ctor_set(v___x_2653_, 1, v___x_2652_);
v___x_2654_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v___x_2648_, v___x_2653_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; lean_object* v___x_2656_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2655_);
lean_dec_ref_known(v___x_2654_, 1);
lean_inc(v___x_2612_);
v___x_2656_ = lean_apply_10(v___f_2604_, v_a_2655_, v___x_2603_, v___x_2612_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, lean_box(0));
v___y_2618_ = v___x_2656_;
goto v___jp_2617_;
}
else
{
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2664_; 
lean_dec(v___x_2612_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v___f_2604_);
lean_dec_ref(v___x_2603_);
v_a_2657_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2659_ = v___x_2654_;
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2654_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2662_; 
if (v_isShared_2660_ == 0)
{
v___x_2662_ = v___x_2659_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_a_2657_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
}
}
}
else
{
lean_object* v___x_2666_; 
lean_dec(v___x_2612_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v___f_2604_);
lean_dec_ref(v___x_2603_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set_tag(v___x_2641_, 1);
lean_ctor_set(v___x_2641_, 0, v_a_2636_);
v___x_2666_ = v___x_2641_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2636_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
else
{
lean_object* v___x_2669_; 
lean_dec(v___x_2612_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v___f_2604_);
lean_dec_ref(v___x_2603_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set_tag(v___x_2641_, 1);
lean_ctor_set(v___x_2641_, 0, v_a_2636_);
v___x_2669_ = v___x_2641_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2636_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
else
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2680_; 
lean_dec(v_a_2636_);
lean_dec(v___x_2612_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v___f_2604_);
lean_dec_ref(v___x_2603_);
v_a_2673_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2675_ = v___x_2639_;
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2639_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2678_; 
if (v_isShared_2676_ == 0)
{
v___x_2678_ = v___x_2675_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2673_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
else
{
lean_dec(v_a_2636_);
lean_dec(v_a_2633_);
lean_dec(v___x_2612_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v___f_2604_);
lean_dec_ref(v___x_2603_);
return v___x_2634_;
}
}
}
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2690_; 
lean_dec(v___x_2612_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v___f_2604_);
lean_dec_ref(v___x_2603_);
lean_dec_ref(v___x_2602_);
v_a_2683_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2685_ = v___x_2632_;
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2632_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2688_; 
if (v_isShared_2686_ == 0)
{
v___x_2688_ = v___x_2685_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_a_2683_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
v___jp_2613_:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2615_ = lean_st_ref_get(v___x_2612_);
lean_dec(v___x_2612_);
lean_dec(v___x_2615_);
v___x_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2616_, 0, v_a_2614_);
return v___x_2616_;
}
v___jp_2617_:
{
if (lean_obj_tag(v___y_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v_a_2620_; 
v_a_2619_ = lean_ctor_get(v___y_2618_, 0);
lean_inc(v_a_2619_);
lean_dec_ref_known(v___y_2618_, 1);
v_a_2620_ = lean_ctor_get(v_a_2619_, 0);
lean_inc(v_a_2620_);
lean_dec(v_a_2619_);
v_a_2614_ = v_a_2620_;
goto v___jp_2613_;
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec(v___x_2612_);
v_a_2621_ = lean_ctor_get(v___y_2618_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___y_2618_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___y_2618_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___y_2618_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
v___jp_2629_:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2630_ = lean_box(0);
lean_inc(v___x_2612_);
v___x_2631_ = lean_apply_10(v___f_2604_, v___x_2630_, v___x_2603_, v___x_2612_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, lean_box(0));
v___y_2618_ = v___x_2631_;
goto v___jp_2617_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed(lean_object* v___x_2691_, lean_object* v___x_2692_, lean_object* v___x_2693_, lean_object* v___f_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(v___x_2691_, v___x_2692_, v___x_2693_, v___f_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(lean_object* v___x_2703_, uint8_t v___x_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v___x_2712_; 
v___x_2712_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2703_, v___x_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed(lean_object* v___x_2713_, lean_object* v___x_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
uint8_t v___x_12177__boxed_2722_; lean_object* v_res_2723_; 
v___x_12177__boxed_2722_ = lean_unbox(v___x_2714_);
v_res_2723_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(v___x_2713_, v___x_12177__boxed_2722_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(lean_object* v_cls_2724_, lean_object* v_msg_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v_ref_2731_; lean_object* v___x_2732_; lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2777_; 
v_ref_2731_ = lean_ctor_get(v___y_2728_, 5);
v___x_2732_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2735_ = v___x_2732_;
v_isShared_2736_ = v_isSharedCheck_2777_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___x_2732_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2777_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2737_; lean_object* v_traceState_2738_; lean_object* v_env_2739_; lean_object* v_nextMacroScope_2740_; lean_object* v_ngen_2741_; lean_object* v_auxDeclNGen_2742_; lean_object* v_cache_2743_; lean_object* v_messages_2744_; lean_object* v_infoState_2745_; lean_object* v_snapshotTasks_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2776_; 
v___x_2737_ = lean_st_ref_take(v___y_2729_);
v_traceState_2738_ = lean_ctor_get(v___x_2737_, 4);
v_env_2739_ = lean_ctor_get(v___x_2737_, 0);
v_nextMacroScope_2740_ = lean_ctor_get(v___x_2737_, 1);
v_ngen_2741_ = lean_ctor_get(v___x_2737_, 2);
v_auxDeclNGen_2742_ = lean_ctor_get(v___x_2737_, 3);
v_cache_2743_ = lean_ctor_get(v___x_2737_, 5);
v_messages_2744_ = lean_ctor_get(v___x_2737_, 6);
v_infoState_2745_ = lean_ctor_get(v___x_2737_, 7);
v_snapshotTasks_2746_ = lean_ctor_get(v___x_2737_, 8);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2748_ = v___x_2737_;
v_isShared_2749_ = v_isSharedCheck_2776_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_snapshotTasks_2746_);
lean_inc(v_infoState_2745_);
lean_inc(v_messages_2744_);
lean_inc(v_cache_2743_);
lean_inc(v_traceState_2738_);
lean_inc(v_auxDeclNGen_2742_);
lean_inc(v_ngen_2741_);
lean_inc(v_nextMacroScope_2740_);
lean_inc(v_env_2739_);
lean_dec(v___x_2737_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2776_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
uint64_t v_tid_2750_; lean_object* v_traces_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2775_; 
v_tid_2750_ = lean_ctor_get_uint64(v_traceState_2738_, sizeof(void*)*1);
v_traces_2751_ = lean_ctor_get(v_traceState_2738_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v_traceState_2738_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2753_ = v_traceState_2738_;
v_isShared_2754_ = v_isSharedCheck_2775_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_traces_2751_);
lean_dec(v_traceState_2738_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2775_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2755_; double v___x_2756_; uint8_t v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2765_; 
v___x_2755_ = lean_box(0);
v___x_2756_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0);
v___x_2757_ = 0;
v___x_2758_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2759_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2759_, 0, v_cls_2724_);
lean_ctor_set(v___x_2759_, 1, v___x_2755_);
lean_ctor_set(v___x_2759_, 2, v___x_2758_);
lean_ctor_set_float(v___x_2759_, sizeof(void*)*3, v___x_2756_);
lean_ctor_set_float(v___x_2759_, sizeof(void*)*3 + 8, v___x_2756_);
lean_ctor_set_uint8(v___x_2759_, sizeof(void*)*3 + 16, v___x_2757_);
v___x_2760_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__1));
v___x_2761_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2759_);
lean_ctor_set(v___x_2761_, 1, v_a_2733_);
lean_ctor_set(v___x_2761_, 2, v___x_2760_);
lean_inc(v_ref_2731_);
v___x_2762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2762_, 0, v_ref_2731_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
v___x_2763_ = l_Lean_PersistentArray_push___redArg(v_traces_2751_, v___x_2762_);
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 0, v___x_2763_);
v___x_2765_ = v___x_2753_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2763_);
lean_ctor_set_uint64(v_reuseFailAlloc_2774_, sizeof(void*)*1, v_tid_2750_);
v___x_2765_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
lean_object* v___x_2767_; 
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 4, v___x_2765_);
v___x_2767_ = v___x_2748_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_env_2739_);
lean_ctor_set(v_reuseFailAlloc_2773_, 1, v_nextMacroScope_2740_);
lean_ctor_set(v_reuseFailAlloc_2773_, 2, v_ngen_2741_);
lean_ctor_set(v_reuseFailAlloc_2773_, 3, v_auxDeclNGen_2742_);
lean_ctor_set(v_reuseFailAlloc_2773_, 4, v___x_2765_);
lean_ctor_set(v_reuseFailAlloc_2773_, 5, v_cache_2743_);
lean_ctor_set(v_reuseFailAlloc_2773_, 6, v_messages_2744_);
lean_ctor_set(v_reuseFailAlloc_2773_, 7, v_infoState_2745_);
lean_ctor_set(v_reuseFailAlloc_2773_, 8, v_snapshotTasks_2746_);
v___x_2767_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2771_; 
v___x_2768_ = lean_st_ref_set(v___y_2729_, v___x_2767_);
v___x_2769_ = lean_box(0);
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 0, v___x_2769_);
v___x_2771_ = v___x_2735_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v___x_2769_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3___boxed(lean_object* v_cls_2778_, lean_object* v_msg_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v_cls_2778_, v_msg_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
return v_res_2785_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__0));
v___x_2788_ = l_Lean_stringToMessageData(v___x_2787_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(lean_object* v_term_2789_, lean_object* v___x_2790_, lean_object* v___x_2791_, lean_object* v___f_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v___y_2799_; lean_object* v___x_2817_; 
v___x_2817_ = l_Lean_Elab_Term_TermElabM_run___redArg(v_term_2789_, v___x_2790_, v___x_2791_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2826_; 
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec_ref(v___f_2792_);
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2820_ = v___x_2817_;
v_isShared_2821_ = v_isSharedCheck_2826_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2817_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2826_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v_fst_2822_; lean_object* v___x_2824_; 
v_fst_2822_ = lean_ctor_get(v_a_2818_, 0);
lean_inc(v_fst_2822_);
lean_dec(v_a_2818_);
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 0, v_fst_2822_);
v___x_2824_ = v___x_2820_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_fst_2822_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
else
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2869_; 
v_a_2827_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2829_ = v___x_2817_;
v_isShared_2830_ = v_isSharedCheck_2869_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2817_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2869_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
uint8_t v___y_2835_; uint8_t v___x_2867_; 
v___x_2867_ = l_Lean_Exception_isInterrupt(v_a_2827_);
if (v___x_2867_ == 0)
{
uint8_t v___x_2868_; 
lean_inc(v_a_2827_);
v___x_2868_ = l_Lean_Exception_isRuntime(v_a_2827_);
v___y_2835_ = v___x_2868_;
goto v___jp_2834_;
}
else
{
v___y_2835_ = v___x_2867_;
goto v___jp_2834_;
}
v___jp_2831_:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = lean_box(0);
v___x_2833_ = lean_apply_6(v___f_2792_, v___x_2832_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, lean_box(0));
v___y_2799_ = v___x_2833_;
goto v___jp_2798_;
}
v___jp_2834_:
{
if (v___y_2835_ == 0)
{
uint8_t v___x_2836_; 
v___x_2836_ = l_Lean_Exception_isInterrupt(v_a_2827_);
if (v___x_2836_ == 0)
{
uint8_t v___x_2837_; 
lean_inc(v_a_2827_);
v___x_2837_ = l_Lean_Exception_isMaxRecDepth(v_a_2827_);
if (v___x_2837_ == 0)
{
lean_object* v_options_2838_; uint8_t v_hasTrace_2839_; 
lean_del_object(v___x_2829_);
v_options_2838_ = lean_ctor_get(v___y_2795_, 2);
v_hasTrace_2839_ = lean_ctor_get_uint8(v_options_2838_, sizeof(void*)*1);
if (v_hasTrace_2839_ == 0)
{
lean_dec(v_a_2827_);
goto v___jp_2831_;
}
else
{
lean_object* v_inheritedTraceOptions_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; uint8_t v___x_2843_; 
v_inheritedTraceOptions_2840_ = lean_ctor_get(v___y_2795_, 13);
v___x_2841_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2842_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_2843_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2840_, v_options_2838_, v___x_2842_);
if (v___x_2843_ == 0)
{
lean_dec(v_a_2827_);
goto v___jp_2831_;
}
else
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2844_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1);
v___x_2845_ = l_Lean_Exception_toMessageData(v_a_2827_);
v___x_2846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2844_);
lean_ctor_set(v___x_2846_, 1, v___x_2845_);
v___x_2847_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_2841_, v___x_2846_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_a_2848_; lean_object* v___x_2849_; 
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc(v_a_2848_);
lean_dec_ref_known(v___x_2847_, 1);
v___x_2849_ = lean_apply_6(v___f_2792_, v_a_2848_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, lean_box(0));
v___y_2799_ = v___x_2849_;
goto v___jp_2798_;
}
else
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec_ref(v___f_2792_);
v_a_2850_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2847_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2847_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2855_; 
if (v_isShared_2853_ == 0)
{
v___x_2855_ = v___x_2852_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
}
}
else
{
lean_object* v___x_2859_; 
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec_ref(v___f_2792_);
if (v_isShared_2830_ == 0)
{
v___x_2859_ = v___x_2829_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2827_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
else
{
lean_object* v___x_2862_; 
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec_ref(v___f_2792_);
if (v_isShared_2830_ == 0)
{
v___x_2862_ = v___x_2829_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2827_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
else
{
lean_object* v___x_2865_; 
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec_ref(v___f_2792_);
if (v_isShared_2830_ == 0)
{
v___x_2865_ = v___x_2829_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2827_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
}
v___jp_2798_:
{
if (lean_obj_tag(v___y_2799_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2808_; 
v_a_2800_ = lean_ctor_get(v___y_2799_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___y_2799_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2802_ = v___y_2799_;
v_isShared_2803_ = v_isSharedCheck_2808_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___y_2799_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2808_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v_a_2804_; lean_object* v___x_2806_; 
v_a_2804_ = lean_ctor_get(v_a_2800_, 0);
lean_inc(v_a_2804_);
lean_dec(v_a_2800_);
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 0, v_a_2804_);
v___x_2806_ = v___x_2802_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2804_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
else
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
v_a_2809_ = lean_ctor_get(v___y_2799_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___y_2799_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___y_2799_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___y_2799_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___boxed(lean_object* v_term_2870_, lean_object* v___x_2871_, lean_object* v___x_2872_, lean_object* v___f_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(v_term_2870_, v___x_2871_, v___x_2872_, v___f_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_2880_, lean_object* v_vals_2881_, lean_object* v_i_2882_, lean_object* v_k_2883_){
_start:
{
lean_object* v___x_2884_; uint8_t v___x_2885_; 
v___x_2884_ = lean_array_get_size(v_keys_2880_);
v___x_2885_ = lean_nat_dec_lt(v_i_2882_, v___x_2884_);
if (v___x_2885_ == 0)
{
lean_object* v___x_2886_; 
lean_dec(v_i_2882_);
v___x_2886_ = lean_box(0);
return v___x_2886_;
}
else
{
lean_object* v_k_x27_2887_; uint8_t v___x_2888_; 
v_k_x27_2887_ = lean_array_fget_borrowed(v_keys_2880_, v_i_2882_);
v___x_2888_ = l_Lean_instBEqMVarId_beq(v_k_2883_, v_k_x27_2887_);
if (v___x_2888_ == 0)
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2889_ = lean_unsigned_to_nat(1u);
v___x_2890_ = lean_nat_add(v_i_2882_, v___x_2889_);
lean_dec(v_i_2882_);
v_i_2882_ = v___x_2890_;
goto _start;
}
else
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2892_ = lean_array_fget_borrowed(v_vals_2881_, v_i_2882_);
lean_dec(v_i_2882_);
lean_inc(v___x_2892_);
v___x_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2892_);
return v___x_2893_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_2894_, lean_object* v_vals_2895_, lean_object* v_i_2896_, lean_object* v_k_2897_){
_start:
{
lean_object* v_res_2898_; 
v_res_2898_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_keys_2894_, v_vals_2895_, v_i_2896_, v_k_2897_);
lean_dec(v_k_2897_);
lean_dec_ref(v_vals_2895_);
lean_dec_ref(v_keys_2894_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(lean_object* v_x_2899_, size_t v_x_2900_, lean_object* v_x_2901_){
_start:
{
if (lean_obj_tag(v_x_2899_) == 0)
{
lean_object* v_es_2902_; lean_object* v___x_2903_; size_t v___x_2904_; size_t v___x_2905_; lean_object* v_j_2906_; lean_object* v___x_2907_; 
v_es_2902_ = lean_ctor_get(v_x_2899_, 0);
v___x_2903_ = lean_box(2);
v___x_2904_ = ((size_t)31ULL);
v___x_2905_ = lean_usize_land(v_x_2900_, v___x_2904_);
v_j_2906_ = lean_usize_to_nat(v___x_2905_);
v___x_2907_ = lean_array_get_borrowed(v___x_2903_, v_es_2902_, v_j_2906_);
lean_dec(v_j_2906_);
switch(lean_obj_tag(v___x_2907_))
{
case 0:
{
lean_object* v_key_2908_; lean_object* v_val_2909_; uint8_t v___x_2910_; 
v_key_2908_ = lean_ctor_get(v___x_2907_, 0);
v_val_2909_ = lean_ctor_get(v___x_2907_, 1);
v___x_2910_ = l_Lean_instBEqMVarId_beq(v_x_2901_, v_key_2908_);
if (v___x_2910_ == 0)
{
lean_object* v___x_2911_; 
v___x_2911_ = lean_box(0);
return v___x_2911_;
}
else
{
lean_object* v___x_2912_; 
lean_inc(v_val_2909_);
v___x_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2912_, 0, v_val_2909_);
return v___x_2912_;
}
}
case 1:
{
lean_object* v_node_2913_; size_t v___x_2914_; size_t v___x_2915_; 
v_node_2913_ = lean_ctor_get(v___x_2907_, 0);
v___x_2914_ = ((size_t)5ULL);
v___x_2915_ = lean_usize_shift_right(v_x_2900_, v___x_2914_);
v_x_2899_ = v_node_2913_;
v_x_2900_ = v___x_2915_;
goto _start;
}
default: 
{
lean_object* v___x_2917_; 
v___x_2917_ = lean_box(0);
return v___x_2917_;
}
}
}
else
{
lean_object* v_ks_2918_; lean_object* v_vs_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v_ks_2918_ = lean_ctor_get(v_x_2899_, 0);
v_vs_2919_ = lean_ctor_get(v_x_2899_, 1);
v___x_2920_ = lean_unsigned_to_nat(0u);
v___x_2921_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_ks_2918_, v_vs_2919_, v___x_2920_, v_x_2901_);
return v___x_2921_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg___boxed(lean_object* v_x_2922_, lean_object* v_x_2923_, lean_object* v_x_2924_){
_start:
{
size_t v_x_12496__boxed_2925_; lean_object* v_res_2926_; 
v_x_12496__boxed_2925_ = lean_unbox_usize(v_x_2923_);
lean_dec(v_x_2923_);
v_res_2926_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_2922_, v_x_12496__boxed_2925_, v_x_2924_);
lean_dec(v_x_2924_);
lean_dec_ref(v_x_2922_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(lean_object* v_x_2927_, lean_object* v_x_2928_){
_start:
{
uint64_t v___x_2929_; size_t v___x_2930_; lean_object* v___x_2931_; 
v___x_2929_ = l_Lean_instHashableMVarId_hash(v_x_2928_);
v___x_2930_ = lean_uint64_to_usize(v___x_2929_);
v___x_2931_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_2927_, v___x_2930_, v_x_2928_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg___boxed(lean_object* v_x_2932_, lean_object* v_x_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_x_2932_, v_x_2933_);
lean_dec(v_x_2933_);
lean_dec_ref(v_x_2932_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(lean_object* v_c_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_){
_start:
{
lean_object* v_mctx_2964_; lean_object* v_env_2965_; lean_object* v_opts_2966_; lean_object* v_namingCtx_2967_; lean_object* v_goal_2968_; lean_object* v_decls_2969_; lean_object* v___x_2970_; 
v_mctx_2964_ = lean_ctor_get(v_c_2960_, 3);
lean_inc_ref(v_mctx_2964_);
v_env_2965_ = lean_ctor_get(v_c_2960_, 2);
lean_inc_ref(v_env_2965_);
v_opts_2966_ = lean_ctor_get(v_c_2960_, 4);
lean_inc_ref(v_opts_2966_);
v_namingCtx_2967_ = lean_ctor_get(v_c_2960_, 5);
lean_inc_ref(v_namingCtx_2967_);
v_goal_2968_ = lean_ctor_get(v_c_2960_, 6);
lean_inc(v_goal_2968_);
lean_dec_ref(v_c_2960_);
v_decls_2969_ = lean_ctor_get(v_mctx_2964_, 5);
v___x_2970_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_decls_2969_, v_goal_2968_);
if (lean_obj_tag(v___x_2970_) == 1)
{
lean_object* v_val_2971_; lean_object* v_lctx_2972_; lean_object* v___f_2973_; lean_object* v___f_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___f_2979_; lean_object* v___x_2980_; uint8_t v___x_2981_; lean_object* v___x_2982_; lean_object* v_term_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___f_2986_; lean_object* v___x_2987_; 
v_val_2971_ = lean_ctor_get(v___x_2970_, 0);
lean_inc(v_val_2971_);
lean_dec_ref_known(v___x_2970_, 1);
v_lctx_2972_ = lean_ctor_get(v_val_2971_, 1);
lean_inc_ref(v_lctx_2972_);
lean_dec(v_val_2971_);
v___f_2973_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__0));
v___f_2974_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__1));
v___x_2975_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__3));
v___x_2976_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__4));
v___x_2977_ = lean_box(0);
lean_inc(v_goal_2968_);
v___x_2978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2978_, 0, v_goal_2968_);
lean_ctor_set(v___x_2978_, 1, v___x_2977_);
v___f_2979_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed), 11, 4);
lean_closure_set(v___f_2979_, 0, v___x_2978_);
lean_closure_set(v___f_2979_, 1, v___x_2975_);
lean_closure_set(v___f_2979_, 2, v___x_2976_);
lean_closure_set(v___f_2979_, 3, v___f_2973_);
v___x_2980_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed), 10, 3);
lean_closure_set(v___x_2980_, 0, lean_box(0));
lean_closure_set(v___x_2980_, 1, v_goal_2968_);
lean_closure_set(v___x_2980_, 2, v___f_2979_);
v___x_2981_ = 1;
v___x_2982_ = lean_box(v___x_2981_);
v_term_2983_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed), 9, 2);
lean_closure_set(v_term_2983_, 0, v___x_2980_);
lean_closure_set(v_term_2983_, 1, v___x_2982_);
v___x_2984_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__6));
v___x_2985_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__7));
v___f_2986_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___boxed), 9, 4);
lean_closure_set(v___f_2986_, 0, v_term_2983_);
lean_closure_set(v___f_2986_, 1, v___x_2984_);
lean_closure_set(v___f_2986_, 2, v___x_2985_);
lean_closure_set(v___f_2986_, 3, v___f_2974_);
v___x_2987_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_2965_, v_mctx_2964_, v_lctx_2972_, v_opts_2966_, v_namingCtx_2967_, v___f_2986_, v_a_2961_, v_a_2962_);
lean_dec_ref(v_namingCtx_2967_);
return v___x_2987_;
}
else
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
lean_dec(v___x_2970_);
lean_dec(v_goal_2968_);
lean_dec_ref(v_namingCtx_2967_);
lean_dec_ref(v_opts_2966_);
lean_dec_ref(v_env_2965_);
lean_dec_ref(v_mctx_2964_);
v___x_2988_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__0));
v___x_2989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2988_);
return v___x_2989_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___boxed(lean_object* v_c_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(v_c_2990_, v_a_2991_, v_a_2992_);
lean_dec(v_a_2992_);
lean_dec_ref(v_a_2991_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0(lean_object* v_00_u03b2_2995_, lean_object* v_x_2996_, lean_object* v_x_2997_){
_start:
{
lean_object* v___x_2998_; 
v___x_2998_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_x_2996_, v_x_2997_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___boxed(lean_object* v_00_u03b2_2999_, lean_object* v_x_3000_, lean_object* v_x_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0(v_00_u03b2_2999_, v_x_3000_, v_x_3001_);
lean_dec(v_x_3001_);
lean_dec_ref(v_x_3000_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(lean_object* v_cls_3003_, lean_object* v_msg_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_){
_start:
{
lean_object* v___x_3014_; 
v___x_3014_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_3003_, v_msg_3004_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___boxed(lean_object* v_cls_3015_, lean_object* v_msg_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(v_cls_3015_, v_msg_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(lean_object* v_00_u03b2_3027_, lean_object* v_x_3028_, size_t v_x_3029_, lean_object* v_x_3030_){
_start:
{
lean_object* v___x_3031_; 
v___x_3031_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_3028_, v_x_3029_, v_x_3030_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3032_, lean_object* v_x_3033_, lean_object* v_x_3034_, lean_object* v_x_3035_){
_start:
{
size_t v_x_12753__boxed_3036_; lean_object* v_res_3037_; 
v_x_12753__boxed_3036_ = lean_unbox_usize(v_x_3034_);
lean_dec(v_x_3034_);
v_res_3037_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(v_00_u03b2_3032_, v_x_3033_, v_x_12753__boxed_3036_, v_x_3035_);
lean_dec(v_x_3035_);
lean_dec_ref(v_x_3033_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3038_, lean_object* v_keys_3039_, lean_object* v_vals_3040_, lean_object* v_heq_3041_, lean_object* v_i_3042_, lean_object* v_k_3043_){
_start:
{
lean_object* v___x_3044_; 
v___x_3044_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_keys_3039_, v_vals_3040_, v_i_3042_, v_k_3043_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3045_, lean_object* v_keys_3046_, lean_object* v_vals_3047_, lean_object* v_heq_3048_, lean_object* v_i_3049_, lean_object* v_k_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2(v_00_u03b2_3045_, v_keys_3046_, v_vals_3047_, v_heq_3048_, v_i_3049_, v_k_3050_);
lean_dec(v_k_3050_);
lean_dec_ref(v_vals_3047_);
lean_dec_ref(v_keys_3046_);
return v_res_3051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(uint8_t v___x_3054_, lean_object* v___x_3055_, lean_object* v_ref_3056_, lean_object* v_a_3057_, lean_object* v___x_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
if (v___x_3054_ == 0)
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; uint8_t v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3055_);
v___x_3063_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__0));
v___x_3064_ = lean_box(0);
v___x_3065_ = 4;
v___x_3066_ = l_Lean_MessageData_nil;
v___x_3067_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_3056_, v_a_3057_, v___x_3062_, v___x_3063_, v___x_3064_, v___x_3065_, v___x_3066_, v___y_3059_, v___y_3060_);
return v___x_3067_;
}
else
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; uint8_t v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3068_ = l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default;
v___x_3069_ = lean_array_get(v___x_3068_, v_a_3057_, v___x_3058_);
lean_dec_ref(v_a_3057_);
v___x_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3055_);
v___x_3071_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__1));
v___x_3072_ = lean_box(0);
v___x_3073_ = 4;
v___x_3074_ = l_Lean_MessageData_nil;
v___x_3075_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_3056_, v___x_3069_, v___x_3070_, v___x_3071_, v___x_3072_, v___x_3073_, v___x_3074_, v___y_3059_, v___y_3060_);
return v___x_3075_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed(lean_object* v___x_3076_, lean_object* v___x_3077_, lean_object* v_ref_3078_, lean_object* v_a_3079_, lean_object* v___x_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
uint8_t v___x_3918__boxed_3084_; lean_object* v_res_3085_; 
v___x_3918__boxed_3084_ = lean_unbox(v___x_3076_);
v_res_3085_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(v___x_3918__boxed_3084_, v___x_3077_, v_ref_3078_, v_a_3079_, v___x_3080_, v___y_3081_, v___y_3082_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec(v___x_3080_);
return v_res_3085_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(uint8_t v___y_3086_, uint8_t v_suppressElabErrors_3087_, lean_object* v_x_3088_){
_start:
{
if (lean_obj_tag(v_x_3088_) == 1)
{
lean_object* v_pre_3089_; 
v_pre_3089_ = lean_ctor_get(v_x_3088_, 0);
if (lean_obj_tag(v_pre_3089_) == 0)
{
lean_object* v_str_3090_; lean_object* v___x_3091_; uint8_t v___x_3092_; 
v_str_3090_ = lean_ctor_get(v_x_3088_, 1);
v___x_3091_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__1));
v___x_3092_ = lean_string_dec_eq(v_str_3090_, v___x_3091_);
if (v___x_3092_ == 0)
{
return v___y_3086_;
}
else
{
return v_suppressElabErrors_3087_;
}
}
else
{
return v___y_3086_;
}
}
else
{
return v___y_3086_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed(lean_object* v___y_3093_, lean_object* v_suppressElabErrors_3094_, lean_object* v_x_3095_){
_start:
{
uint8_t v___y_3970__boxed_3096_; uint8_t v_suppressElabErrors_boxed_3097_; uint8_t v_res_3098_; lean_object* v_r_3099_; 
v___y_3970__boxed_3096_ = lean_unbox(v___y_3093_);
v_suppressElabErrors_boxed_3097_ = lean_unbox(v_suppressElabErrors_3094_);
v_res_3098_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(v___y_3970__boxed_3096_, v_suppressElabErrors_boxed_3097_, v_x_3095_);
lean_dec(v_x_3095_);
v_r_3099_ = lean_box(v_res_3098_);
return v_r_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(lean_object* v_ref_3100_, lean_object* v_msgData_3101_, uint8_t v_severity_3102_, uint8_t v_isSilent_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
uint8_t v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; uint8_t v___y_3114_; lean_object* v___y_3115_; uint8_t v___y_3171_; uint8_t v___y_3172_; lean_object* v___y_3173_; uint8_t v___y_3174_; lean_object* v___y_3175_; uint8_t v___y_3199_; uint8_t v___y_3200_; lean_object* v___y_3201_; uint8_t v___y_3202_; lean_object* v___y_3203_; uint8_t v___y_3207_; uint8_t v___y_3208_; uint8_t v___y_3209_; uint8_t v___x_3224_; uint8_t v___y_3226_; uint8_t v___y_3227_; uint8_t v___y_3228_; uint8_t v___y_3230_; uint8_t v___x_3242_; 
v___x_3224_ = 2;
v___x_3242_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3102_, v___x_3224_);
if (v___x_3242_ == 0)
{
v___y_3230_ = v___x_3242_;
goto v___jp_3229_;
}
else
{
uint8_t v___x_3243_; 
lean_inc_ref(v_msgData_3101_);
v___x_3243_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3101_);
v___y_3230_ = v___x_3243_;
goto v___jp_3229_;
}
v___jp_3107_:
{
lean_object* v___x_3116_; 
v___x_3116_ = l_Lean_Elab_Command_getScope___redArg(v___y_3115_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_a_3117_; lean_object* v___x_3118_; 
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_a_3117_);
lean_dec_ref_known(v___x_3116_, 1);
v___x_3118_ = l_Lean_Elab_Command_getScope___redArg(v___y_3115_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3153_; 
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3121_ = v___x_3118_;
v_isShared_3122_ = v_isSharedCheck_3153_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3118_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3153_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3123_; lean_object* v_currNamespace_3124_; lean_object* v_openDecls_3125_; lean_object* v_env_3126_; lean_object* v_messages_3127_; lean_object* v_scopes_3128_; lean_object* v_usedQuotCtxts_3129_; lean_object* v_nextMacroScope_3130_; lean_object* v_maxRecDepth_3131_; lean_object* v_ngen_3132_; lean_object* v_auxDeclNGen_3133_; lean_object* v_infoState_3134_; lean_object* v_traceState_3135_; lean_object* v_snapshotTasks_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3152_; 
v___x_3123_ = lean_st_ref_take(v___y_3115_);
v_currNamespace_3124_ = lean_ctor_get(v_a_3117_, 2);
lean_inc(v_currNamespace_3124_);
lean_dec(v_a_3117_);
v_openDecls_3125_ = lean_ctor_get(v_a_3119_, 3);
lean_inc(v_openDecls_3125_);
lean_dec(v_a_3119_);
v_env_3126_ = lean_ctor_get(v___x_3123_, 0);
v_messages_3127_ = lean_ctor_get(v___x_3123_, 1);
v_scopes_3128_ = lean_ctor_get(v___x_3123_, 2);
v_usedQuotCtxts_3129_ = lean_ctor_get(v___x_3123_, 3);
v_nextMacroScope_3130_ = lean_ctor_get(v___x_3123_, 4);
v_maxRecDepth_3131_ = lean_ctor_get(v___x_3123_, 5);
v_ngen_3132_ = lean_ctor_get(v___x_3123_, 6);
v_auxDeclNGen_3133_ = lean_ctor_get(v___x_3123_, 7);
v_infoState_3134_ = lean_ctor_get(v___x_3123_, 8);
v_traceState_3135_ = lean_ctor_get(v___x_3123_, 9);
v_snapshotTasks_3136_ = lean_ctor_get(v___x_3123_, 10);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3138_ = v___x_3123_;
v_isShared_3139_ = v_isSharedCheck_3152_;
goto v_resetjp_3137_;
}
else
{
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
lean_dec(v___x_3123_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3152_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3145_; 
v___x_3140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3140_, 0, v_currNamespace_3124_);
lean_ctor_set(v___x_3140_, 1, v_openDecls_3125_);
v___x_3141_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3140_);
lean_ctor_set(v___x_3141_, 1, v___y_3111_);
lean_inc_ref(v___y_3112_);
lean_inc_ref(v___y_3113_);
v___x_3142_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3142_, 0, v___y_3113_);
lean_ctor_set(v___x_3142_, 1, v___y_3109_);
lean_ctor_set(v___x_3142_, 2, v___y_3110_);
lean_ctor_set(v___x_3142_, 3, v___y_3112_);
lean_ctor_set(v___x_3142_, 4, v___x_3141_);
lean_ctor_set_uint8(v___x_3142_, sizeof(void*)*5, v___y_3114_);
lean_ctor_set_uint8(v___x_3142_, sizeof(void*)*5 + 1, v___y_3108_);
lean_ctor_set_uint8(v___x_3142_, sizeof(void*)*5 + 2, v_isSilent_3103_);
v___x_3143_ = l_Lean_MessageLog_add(v___x_3142_, v_messages_3127_);
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 1, v___x_3143_);
v___x_3145_ = v___x_3138_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_env_3126_);
lean_ctor_set(v_reuseFailAlloc_3151_, 1, v___x_3143_);
lean_ctor_set(v_reuseFailAlloc_3151_, 2, v_scopes_3128_);
lean_ctor_set(v_reuseFailAlloc_3151_, 3, v_usedQuotCtxts_3129_);
lean_ctor_set(v_reuseFailAlloc_3151_, 4, v_nextMacroScope_3130_);
lean_ctor_set(v_reuseFailAlloc_3151_, 5, v_maxRecDepth_3131_);
lean_ctor_set(v_reuseFailAlloc_3151_, 6, v_ngen_3132_);
lean_ctor_set(v_reuseFailAlloc_3151_, 7, v_auxDeclNGen_3133_);
lean_ctor_set(v_reuseFailAlloc_3151_, 8, v_infoState_3134_);
lean_ctor_set(v_reuseFailAlloc_3151_, 9, v_traceState_3135_);
lean_ctor_set(v_reuseFailAlloc_3151_, 10, v_snapshotTasks_3136_);
v___x_3145_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3149_; 
v___x_3146_ = lean_st_ref_set(v___y_3115_, v___x_3145_);
v___x_3147_ = lean_box(0);
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 0, v___x_3147_);
v___x_3149_ = v___x_3121_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3147_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
lean_dec(v_a_3117_);
lean_dec_ref(v___y_3111_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
v_a_3154_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_3118_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3118_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3154_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
lean_dec_ref(v___y_3111_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
v_a_3162_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3116_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3116_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
v___jp_3170_:
{
lean_object* v_fileName_3176_; lean_object* v_fileMap_3177_; uint8_t v_suppressElabErrors_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3197_; 
v_fileName_3176_ = lean_ctor_get(v___y_3104_, 0);
v_fileMap_3177_ = lean_ctor_get(v___y_3104_, 1);
v_suppressElabErrors_3178_ = lean_ctor_get_uint8(v___y_3104_, sizeof(void*)*10);
v___x_3179_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3101_);
v___x_3180_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(v___x_3179_, v___y_3105_);
v_a_3181_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3183_ = v___x_3180_;
v_isShared_3184_ = v_isSharedCheck_3197_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3180_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3197_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
lean_inc_ref_n(v_fileMap_3177_, 2);
v___x_3185_ = l_Lean_FileMap_toPosition(v_fileMap_3177_, v___y_3173_);
lean_dec(v___y_3173_);
v___x_3186_ = l_Lean_FileMap_toPosition(v_fileMap_3177_, v___y_3175_);
lean_dec(v___y_3175_);
v___x_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3186_);
v___x_3188_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
if (v_suppressElabErrors_3178_ == 0)
{
lean_del_object(v___x_3183_);
v___y_3108_ = v___y_3172_;
v___y_3109_ = v___x_3185_;
v___y_3110_ = v___x_3187_;
v___y_3111_ = v_a_3181_;
v___y_3112_ = v___x_3188_;
v___y_3113_ = v_fileName_3176_;
v___y_3114_ = v___y_3174_;
v___y_3115_ = v___y_3105_;
goto v___jp_3107_;
}
else
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___f_3191_; uint8_t v___x_3192_; 
v___x_3189_ = lean_box(v___y_3171_);
v___x_3190_ = lean_box(v_suppressElabErrors_3178_);
v___f_3191_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3191_, 0, v___x_3189_);
lean_closure_set(v___f_3191_, 1, v___x_3190_);
lean_inc(v_a_3181_);
v___x_3192_ = l_Lean_MessageData_hasTag(v___f_3191_, v_a_3181_);
if (v___x_3192_ == 0)
{
lean_object* v___x_3193_; lean_object* v___x_3195_; 
lean_dec_ref_known(v___x_3187_, 1);
lean_dec_ref(v___x_3185_);
lean_dec(v_a_3181_);
v___x_3193_ = lean_box(0);
if (v_isShared_3184_ == 0)
{
lean_ctor_set(v___x_3183_, 0, v___x_3193_);
v___x_3195_ = v___x_3183_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v___x_3193_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
else
{
lean_del_object(v___x_3183_);
v___y_3108_ = v___y_3172_;
v___y_3109_ = v___x_3185_;
v___y_3110_ = v___x_3187_;
v___y_3111_ = v_a_3181_;
v___y_3112_ = v___x_3188_;
v___y_3113_ = v_fileName_3176_;
v___y_3114_ = v___y_3174_;
v___y_3115_ = v___y_3105_;
goto v___jp_3107_;
}
}
}
}
v___jp_3198_:
{
lean_object* v___x_3204_; 
v___x_3204_ = l_Lean_Syntax_getTailPos_x3f(v___y_3201_, v___y_3202_);
lean_dec(v___y_3201_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_inc(v___y_3203_);
v___y_3171_ = v___y_3199_;
v___y_3172_ = v___y_3200_;
v___y_3173_ = v___y_3203_;
v___y_3174_ = v___y_3202_;
v___y_3175_ = v___y_3203_;
goto v___jp_3170_;
}
else
{
lean_object* v_val_3205_; 
v_val_3205_ = lean_ctor_get(v___x_3204_, 0);
lean_inc(v_val_3205_);
lean_dec_ref_known(v___x_3204_, 1);
v___y_3171_ = v___y_3199_;
v___y_3172_ = v___y_3200_;
v___y_3173_ = v___y_3203_;
v___y_3174_ = v___y_3202_;
v___y_3175_ = v_val_3205_;
goto v___jp_3170_;
}
}
v___jp_3206_:
{
lean_object* v___x_3210_; 
v___x_3210_ = l_Lean_Elab_Command_getRef___redArg(v___y_3104_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; lean_object* v_ref_3212_; lean_object* v___x_3213_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_a_3211_);
lean_dec_ref_known(v___x_3210_, 1);
v_ref_3212_ = l_Lean_replaceRef(v_ref_3100_, v_a_3211_);
lean_dec(v_a_3211_);
v___x_3213_ = l_Lean_Syntax_getPos_x3f(v_ref_3212_, v___y_3208_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v___x_3214_; 
v___x_3214_ = lean_unsigned_to_nat(0u);
v___y_3199_ = v___y_3207_;
v___y_3200_ = v___y_3209_;
v___y_3201_ = v_ref_3212_;
v___y_3202_ = v___y_3208_;
v___y_3203_ = v___x_3214_;
goto v___jp_3198_;
}
else
{
lean_object* v_val_3215_; 
v_val_3215_ = lean_ctor_get(v___x_3213_, 0);
lean_inc(v_val_3215_);
lean_dec_ref_known(v___x_3213_, 1);
v___y_3199_ = v___y_3207_;
v___y_3200_ = v___y_3209_;
v___y_3201_ = v_ref_3212_;
v___y_3202_ = v___y_3208_;
v___y_3203_ = v_val_3215_;
goto v___jp_3198_;
}
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_dec_ref(v_msgData_3101_);
v_a_3216_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3210_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3210_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
v___jp_3225_:
{
if (v___y_3228_ == 0)
{
v___y_3207_ = v___y_3226_;
v___y_3208_ = v___y_3227_;
v___y_3209_ = v_severity_3102_;
goto v___jp_3206_;
}
else
{
v___y_3207_ = v___y_3226_;
v___y_3208_ = v___y_3227_;
v___y_3209_ = v___x_3224_;
goto v___jp_3206_;
}
}
v___jp_3229_:
{
if (v___y_3230_ == 0)
{
lean_object* v___x_3231_; lean_object* v_scopes_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v_opts_3235_; uint8_t v___x_3236_; uint8_t v___x_3237_; 
v___x_3231_ = lean_st_ref_get(v___y_3105_);
v_scopes_3232_ = lean_ctor_get(v___x_3231_, 2);
lean_inc(v_scopes_3232_);
lean_dec(v___x_3231_);
v___x_3233_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3234_ = l_List_head_x21___redArg(v___x_3233_, v_scopes_3232_);
lean_dec(v_scopes_3232_);
v_opts_3235_ = lean_ctor_get(v___x_3234_, 1);
lean_inc_ref(v_opts_3235_);
lean_dec(v___x_3234_);
v___x_3236_ = 1;
v___x_3237_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3102_, v___x_3236_);
if (v___x_3237_ == 0)
{
lean_dec_ref(v_opts_3235_);
v___y_3226_ = v___y_3230_;
v___y_3227_ = v___y_3230_;
v___y_3228_ = v___x_3237_;
goto v___jp_3225_;
}
else
{
lean_object* v___x_3238_; uint8_t v___x_3239_; 
v___x_3238_ = l_Lean_warningAsError;
v___x_3239_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_3235_, v___x_3238_);
lean_dec_ref(v_opts_3235_);
v___y_3226_ = v___y_3230_;
v___y_3227_ = v___y_3230_;
v___y_3228_ = v___x_3239_;
goto v___jp_3225_;
}
}
else
{
lean_object* v___x_3240_; lean_object* v___x_3241_; 
lean_dec_ref(v_msgData_3101_);
v___x_3240_ = lean_box(0);
v___x_3241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3240_);
return v___x_3241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___boxed(lean_object* v_ref_3244_, lean_object* v_msgData_3245_, lean_object* v_severity_3246_, lean_object* v_isSilent_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_){
_start:
{
uint8_t v_severity_boxed_3251_; uint8_t v_isSilent_boxed_3252_; lean_object* v_res_3253_; 
v_severity_boxed_3251_ = lean_unbox(v_severity_3246_);
v_isSilent_boxed_3252_ = lean_unbox(v_isSilent_3247_);
v_res_3253_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3244_, v_msgData_3245_, v_severity_boxed_3251_, v_isSilent_boxed_3252_, v___y_3248_, v___y_3249_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v_ref_3244_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(lean_object* v_ref_3254_, lean_object* v_msgData_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
uint8_t v___x_3259_; uint8_t v___x_3260_; lean_object* v___x_3261_; 
v___x_3259_ = 0;
v___x_3260_ = 0;
v___x_3261_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3254_, v_msgData_3255_, v___x_3259_, v___x_3260_, v___y_3256_, v___y_3257_);
return v___x_3261_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0___boxed(lean_object* v_ref_3262_, lean_object* v_msgData_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
lean_object* v_res_3267_; 
v_res_3267_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3262_, v_msgData_3263_, v___y_3264_, v___y_3265_);
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
lean_dec(v_ref_3262_);
return v_res_3267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(lean_object* v___x_3269_, lean_object* v_x_3270_){
_start:
{
lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3271_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___closed__0));
v___x_3272_ = lean_string_append(v___x_3271_, v___x_3269_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed(lean_object* v___x_3273_, lean_object* v_x_3274_){
_start:
{
lean_object* v_res_3275_; 
v_res_3275_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(v___x_3273_, v_x_3274_);
lean_dec_ref(v_x_3274_);
lean_dec_ref(v___x_3273_);
return v_res_3275_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3277_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__0));
v___x_3278_ = l_Lean_stringToMessageData(v___x_3277_);
return v___x_3278_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3280_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__2));
v___x_3281_ = l_Lean_stringToMessageData(v___x_3280_);
return v___x_3281_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3283_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__4));
v___x_3284_ = l_Lean_stringToMessageData(v___x_3283_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(lean_object* v___x_3285_, uint8_t v___x_3286_, lean_object* v___x_3287_, lean_object* v_insertPos_3288_, lean_object* v_cmdLine_3289_, lean_object* v_ref_3290_, size_t v_sz_3291_, size_t v_i_3292_, lean_object* v_bs_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
uint8_t v___x_3297_; 
v___x_3297_ = lean_usize_dec_lt(v_i_3292_, v_sz_3291_);
if (v___x_3297_ == 0)
{
lean_object* v___x_3298_; 
lean_dec_ref(v___x_3287_);
lean_dec_ref(v___x_3285_);
v___x_3298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3298_, 0, v_bs_3293_);
return v___x_3298_;
}
else
{
lean_object* v_v_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v_v_3299_ = lean_array_uget(v_bs_3293_, v_i_3292_);
lean_inc(v_v_3299_);
v___x_3300_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppTactic___boxed), 4, 1);
lean_closure_set(v___x_3300_, 0, v_v_3299_);
v___x_3301_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_3300_, v___y_3294_, v___y_3295_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3302_; lean_object* v___x_3303_; lean_object* v_bs_x27_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___f_3307_; lean_object* v___x_3308_; 
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
lean_inc(v_a_3302_);
lean_dec_ref_known(v___x_3301_, 1);
v___x_3303_ = lean_unsigned_to_nat(0u);
v_bs_x27_3304_ = lean_array_uset(v_bs_3293_, v_i_3292_, v___x_3303_);
v___x_3305_ = l_Std_Format_defWidth;
v___x_3306_ = l_Std_Format_pretty(v_a_3302_, v___x_3305_, v___x_3303_, v___x_3303_);
lean_inc_ref(v___x_3306_);
v___f_3307_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3307_, 0, v___x_3306_);
lean_inc_ref(v___x_3285_);
v___x_3308_ = lean_string_append(v___x_3285_, v___x_3306_);
lean_dec_ref(v___x_3306_);
if (v___x_3286_ == 0)
{
goto v___jp_3309_;
}
else
{
lean_object* v___x_3320_; lean_object* v_line_3321_; lean_object* v_column_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3357_; 
lean_inc_ref(v___x_3287_);
v___x_3320_ = l_Lean_FileMap_toPosition(v___x_3287_, v_insertPos_3288_);
v_line_3321_ = lean_ctor_get(v___x_3320_, 0);
v_column_3322_ = lean_ctor_get(v___x_3320_, 1);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3320_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3324_ = v___x_3320_;
v_isShared_3325_ = v_isSharedCheck_3357_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_column_3322_);
lean_inc(v_line_3321_);
lean_dec(v___x_3320_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3357_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3334_; 
v___x_3326_ = lean_nat_sub(v_line_3321_, v_cmdLine_3289_);
lean_dec(v_line_3321_);
v___x_3327_ = lean_unsigned_to_nat(1u);
v___x_3328_ = lean_nat_add(v___x_3326_, v___x_3327_);
lean_dec(v___x_3326_);
v___x_3329_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1);
lean_inc_ref(v___x_3308_);
v___x_3330_ = l_String_quote(v___x_3308_);
v___x_3331_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3330_);
v___x_3332_ = l_Lean_MessageData_ofFormat(v___x_3331_);
if (v_isShared_3325_ == 0)
{
lean_ctor_set_tag(v___x_3324_, 7);
lean_ctor_set(v___x_3324_, 1, v___x_3332_);
lean_ctor_set(v___x_3324_, 0, v___x_3329_);
v___x_3334_ = v___x_3324_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3329_);
lean_ctor_set(v_reuseFailAlloc_3356_, 1, v___x_3332_);
v___x_3334_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3335_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3);
v___x_3336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3334_);
lean_ctor_set(v___x_3336_, 1, v___x_3335_);
v___x_3337_ = l_Nat_reprFast(v___x_3328_);
v___x_3338_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3337_);
v___x_3339_ = l_Lean_MessageData_ofFormat(v___x_3338_);
v___x_3340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3336_);
lean_ctor_set(v___x_3340_, 1, v___x_3339_);
v___x_3341_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5);
v___x_3342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3340_);
lean_ctor_set(v___x_3342_, 1, v___x_3341_);
v___x_3343_ = l_Nat_reprFast(v_column_3322_);
v___x_3344_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3343_);
v___x_3345_ = l_Lean_MessageData_ofFormat(v___x_3344_);
v___x_3346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3342_);
lean_ctor_set(v___x_3346_, 1, v___x_3345_);
v___x_3347_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3290_, v___x_3346_, v___y_3294_, v___y_3295_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_dec_ref_known(v___x_3347_, 1);
goto v___jp_3309_;
}
else
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3355_; 
lean_dec_ref(v___x_3308_);
lean_dec_ref(v___f_3307_);
lean_dec_ref(v_bs_x27_3304_);
lean_dec(v_v_3299_);
lean_dec_ref(v___x_3287_);
lean_dec_ref(v___x_3285_);
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3350_ = v___x_3347_;
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3347_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3353_; 
if (v_isShared_3351_ == 0)
{
v___x_3353_ = v___x_3350_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_a_3348_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
}
}
v___jp_3309_:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; size_t v___x_3316_; size_t v___x_3317_; lean_object* v___x_3318_; 
v___x_3310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3308_);
v___x_3311_ = lean_box(0);
v___x_3312_ = l_Lean_MessageData_ofSyntax(v_v_3299_);
v___x_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3312_);
v___x_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3314_, 0, v___f_3307_);
v___x_3315_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3310_);
lean_ctor_set(v___x_3315_, 1, v___x_3311_);
lean_ctor_set(v___x_3315_, 2, v___x_3311_);
lean_ctor_set(v___x_3315_, 3, v___x_3311_);
lean_ctor_set(v___x_3315_, 4, v___x_3313_);
lean_ctor_set(v___x_3315_, 5, v___x_3314_);
v___x_3316_ = ((size_t)1ULL);
v___x_3317_ = lean_usize_add(v_i_3292_, v___x_3316_);
v___x_3318_ = lean_array_uset(v_bs_x27_3304_, v_i_3292_, v___x_3315_);
v_i_3292_ = v___x_3317_;
v_bs_3293_ = v___x_3318_;
goto _start;
}
}
else
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3365_; 
lean_dec(v_v_3299_);
lean_dec_ref(v_bs_3293_);
lean_dec_ref(v___x_3287_);
lean_dec_ref(v___x_3285_);
v_a_3358_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3360_ = v___x_3301_;
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3301_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
if (v_isShared_3361_ == 0)
{
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_a_3358_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___boxed(lean_object* v___x_3366_, lean_object* v___x_3367_, lean_object* v___x_3368_, lean_object* v_insertPos_3369_, lean_object* v_cmdLine_3370_, lean_object* v_ref_3371_, lean_object* v_sz_3372_, lean_object* v_i_3373_, lean_object* v_bs_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
uint8_t v___x_4282__boxed_3378_; size_t v_sz_boxed_3379_; size_t v_i_boxed_3380_; lean_object* v_res_3381_; 
v___x_4282__boxed_3378_ = lean_unbox(v___x_3367_);
v_sz_boxed_3379_ = lean_unbox_usize(v_sz_3372_);
lean_dec(v_sz_3372_);
v_i_boxed_3380_ = lean_unbox_usize(v_i_3373_);
lean_dec(v_i_3373_);
v_res_3381_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3366_, v___x_4282__boxed_3378_, v___x_3368_, v_insertPos_3369_, v_cmdLine_3370_, v_ref_3371_, v_sz_boxed_3379_, v_i_boxed_3380_, v_bs_3374_, v___y_3375_, v___y_3376_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
lean_dec(v_ref_3371_);
lean_dec(v_cmdLine_3370_);
lean_dec(v_insertPos_3369_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(lean_object* v_tacticSeq_3382_, lean_object* v_ref_3383_, lean_object* v_insertPos_3384_, lean_object* v_suggs_3385_, lean_object* v_cmdLine_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_){
_start:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; uint8_t v___x_3392_; 
v___x_3390_ = lean_array_get_size(v_suggs_3385_);
v___x_3391_ = lean_unsigned_to_nat(0u);
v___x_3392_ = lean_nat_dec_eq(v___x_3390_, v___x_3391_);
if (v___x_3392_ == 0)
{
lean_object* v___x_3393_; lean_object* v_fileMap_3394_; lean_object* v_scopes_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v_opts_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; uint8_t v___x_3401_; size_t v_sz_3402_; size_t v___x_3403_; lean_object* v___x_3404_; 
v___x_3393_ = lean_st_ref_get(v_a_3388_);
v_fileMap_3394_ = lean_ctor_get(v_a_3387_, 1);
v_scopes_3395_ = lean_ctor_get(v___x_3393_, 2);
lean_inc(v_scopes_3395_);
lean_dec(v___x_3393_);
v___x_3396_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3397_ = l_List_head_x21___redArg(v___x_3396_, v_scopes_3395_);
lean_dec(v_scopes_3395_);
v_opts_3398_ = lean_ctor_get(v___x_3397_, 1);
lean_inc_ref(v_opts_3398_);
lean_dec(v___x_3397_);
lean_inc_ref_n(v_fileMap_3394_, 2);
v___x_3399_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(v_tacticSeq_3382_, v_fileMap_3394_);
v___x_3400_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_debug_autoTry_showEdits;
v___x_3401_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_3398_, v___x_3400_);
lean_dec_ref(v_opts_3398_);
v_sz_3402_ = lean_array_size(v_suggs_3385_);
v___x_3403_ = ((size_t)0ULL);
v___x_3404_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3399_, v___x_3401_, v_fileMap_3394_, v_insertPos_3384_, v_cmdLine_3386_, v_ref_3383_, v_sz_3402_, v___x_3403_, v_suggs_3385_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_a_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; uint8_t v___x_3409_; lean_object* v___x_3410_; lean_object* v___y_3411_; lean_object* v___x_3412_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_a_3405_);
lean_dec_ref_known(v___x_3404_, 1);
v___x_3406_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx(v_insertPos_3384_);
v___x_3407_ = lean_array_get_size(v_a_3405_);
v___x_3408_ = lean_unsigned_to_nat(1u);
v___x_3409_ = lean_nat_dec_eq(v___x_3407_, v___x_3408_);
v___x_3410_ = lean_box(v___x_3409_);
v___y_3411_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed), 8, 5);
lean_closure_set(v___y_3411_, 0, v___x_3410_);
lean_closure_set(v___y_3411_, 1, v___x_3406_);
lean_closure_set(v___y_3411_, 2, v_ref_3383_);
lean_closure_set(v___y_3411_, 3, v_a_3405_);
lean_closure_set(v___y_3411_, 4, v___x_3391_);
v___x_3412_ = l_Lean_Elab_Command_liftCoreM___redArg(v___y_3411_, v_a_3387_, v_a_3388_);
return v___x_3412_;
}
else
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
lean_dec(v_insertPos_3384_);
lean_dec(v_ref_3383_);
v_a_3413_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3415_ = v___x_3404_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3404_);
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
lean_dec_ref(v_suggs_3385_);
lean_dec(v_insertPos_3384_);
lean_dec(v_ref_3383_);
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
v___x_3453_ = l_Array_mkArray0(lean_box(0));
return v___x_3453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(lean_object* v___f_3457_, lean_object* v_ref_3458_, lean_object* v_goal_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_){
_start:
{
lean_object* v_fileName_3465_; lean_object* v_fileMap_3466_; lean_object* v_options_3467_; lean_object* v_currRecDepth_3468_; lean_object* v_maxRecDepth_3469_; lean_object* v_ref_3470_; lean_object* v_currNamespace_3471_; lean_object* v_openDecls_3472_; lean_object* v_initHeartbeats_3473_; lean_object* v_maxHeartbeats_3474_; lean_object* v_quotContext_3475_; lean_object* v_currMacroScope_3476_; uint8_t v_diag_3477_; lean_object* v_cancelTk_x3f_3478_; uint8_t v_suppressElabErrors_3479_; lean_object* v_inheritedTraceOptions_3480_; uint8_t v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; uint8_t v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v_ref_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; 
v_fileName_3465_ = lean_ctor_get(v___y_3462_, 0);
v_fileMap_3466_ = lean_ctor_get(v___y_3462_, 1);
v_options_3467_ = lean_ctor_get(v___y_3462_, 2);
v_currRecDepth_3468_ = lean_ctor_get(v___y_3462_, 3);
v_maxRecDepth_3469_ = lean_ctor_get(v___y_3462_, 4);
v_ref_3470_ = lean_ctor_get(v___y_3462_, 5);
v_currNamespace_3471_ = lean_ctor_get(v___y_3462_, 6);
v_openDecls_3472_ = lean_ctor_get(v___y_3462_, 7);
v_initHeartbeats_3473_ = lean_ctor_get(v___y_3462_, 8);
v_maxHeartbeats_3474_ = lean_ctor_get(v___y_3462_, 9);
v_quotContext_3475_ = lean_ctor_get(v___y_3462_, 10);
v_currMacroScope_3476_ = lean_ctor_get(v___y_3462_, 11);
v_diag_3477_ = lean_ctor_get_uint8(v___y_3462_, sizeof(void*)*14);
v_cancelTk_x3f_3478_ = lean_ctor_get(v___y_3462_, 12);
v_suppressElabErrors_3479_ = lean_ctor_get_uint8(v___y_3462_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3480_ = lean_ctor_get(v___y_3462_, 13);
v___x_3481_ = 0;
v___x_3482_ = l_Lean_SourceInfo_fromRef(v_ref_3470_, v___x_3481_);
v___x_3483_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__1));
v___x_3484_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__2));
lean_inc_n(v___x_3482_, 3);
v___x_3485_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3482_);
lean_ctor_set(v___x_3485_, 1, v___x_3484_);
v___x_3486_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__4));
v___x_3487_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__6));
v___x_3488_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7);
v___x_3489_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3482_);
lean_ctor_set(v___x_3489_, 1, v___x_3487_);
lean_ctor_set(v___x_3489_, 2, v___x_3488_);
v___x_3490_ = l_Lean_Syntax_node1(v___x_3482_, v___x_3486_, v___x_3489_);
v___x_3491_ = l_Lean_Syntax_node2(v___x_3482_, v___x_3483_, v___x_3485_, v___x_3490_);
v___x_3492_ = lean_box(0);
v___x_3493_ = lean_box(0);
v___x_3494_ = 1;
v___x_3495_ = lean_box(1);
v___x_3496_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__5));
v___x_3497_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_3497_, 0, v___x_3492_);
lean_ctor_set(v___x_3497_, 1, v___x_3493_);
lean_ctor_set(v___x_3497_, 2, v___x_3492_);
lean_ctor_set(v___x_3497_, 3, v___f_3457_);
lean_ctor_set(v___x_3497_, 4, v___x_3495_);
lean_ctor_set(v___x_3497_, 5, v___x_3495_);
lean_ctor_set(v___x_3497_, 6, v___x_3492_);
lean_ctor_set(v___x_3497_, 7, v___x_3496_);
lean_ctor_set_uint8(v___x_3497_, sizeof(void*)*8, v___x_3494_);
lean_ctor_set_uint8(v___x_3497_, sizeof(void*)*8 + 1, v___x_3494_);
lean_ctor_set_uint8(v___x_3497_, sizeof(void*)*8 + 2, v___x_3494_);
lean_ctor_set_uint8(v___x_3497_, sizeof(void*)*8 + 3, v___x_3494_);
lean_ctor_set_uint8(v___x_3497_, sizeof(void*)*8 + 4, v___x_3481_);
lean_ctor_set_uint8(v___x_3497_, sizeof(void*)*8 + 5, v___x_3481_);
lean_ctor_set_uint8(v___x_3497_, sizeof(void*)*8 + 6, v___x_3481_);
lean_ctor_set_uint8(v___x_3497_, sizeof(void*)*8 + 7, v___x_3481_);
lean_ctor_set_uint8(v___x_3497_, sizeof(void*)*8 + 8, v___x_3494_);
lean_ctor_set_uint8(v___x_3497_, sizeof(void*)*8 + 9, v___x_3481_);
lean_ctor_set_uint8(v___x_3497_, sizeof(void*)*8 + 10, v___x_3494_);
v___x_3498_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__8));
v_ref_3499_ = l_Lean_replaceRef(v_ref_3458_, v_ref_3470_);
lean_inc_ref(v_inheritedTraceOptions_3480_);
lean_inc(v_cancelTk_x3f_3478_);
lean_inc(v_currMacroScope_3476_);
lean_inc(v_quotContext_3475_);
lean_inc(v_maxHeartbeats_3474_);
lean_inc(v_initHeartbeats_3473_);
lean_inc(v_openDecls_3472_);
lean_inc(v_currNamespace_3471_);
lean_inc(v_maxRecDepth_3469_);
lean_inc(v_currRecDepth_3468_);
lean_inc_ref(v_options_3467_);
lean_inc_ref(v_fileMap_3466_);
lean_inc_ref(v_fileName_3465_);
v___x_3500_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3500_, 0, v_fileName_3465_);
lean_ctor_set(v___x_3500_, 1, v_fileMap_3466_);
lean_ctor_set(v___x_3500_, 2, v_options_3467_);
lean_ctor_set(v___x_3500_, 3, v_currRecDepth_3468_);
lean_ctor_set(v___x_3500_, 4, v_maxRecDepth_3469_);
lean_ctor_set(v___x_3500_, 5, v_ref_3499_);
lean_ctor_set(v___x_3500_, 6, v_currNamespace_3471_);
lean_ctor_set(v___x_3500_, 7, v_openDecls_3472_);
lean_ctor_set(v___x_3500_, 8, v_initHeartbeats_3473_);
lean_ctor_set(v___x_3500_, 9, v_maxHeartbeats_3474_);
lean_ctor_set(v___x_3500_, 10, v_quotContext_3475_);
lean_ctor_set(v___x_3500_, 11, v_currMacroScope_3476_);
lean_ctor_set(v___x_3500_, 12, v_cancelTk_x3f_3478_);
lean_ctor_set(v___x_3500_, 13, v_inheritedTraceOptions_3480_);
lean_ctor_set_uint8(v___x_3500_, sizeof(void*)*14, v_diag_3477_);
lean_ctor_set_uint8(v___x_3500_, sizeof(void*)*14 + 1, v_suppressElabErrors_3479_);
v___x_3501_ = l_Lean_Elab_runTactic(v_goal_3459_, v___x_3491_, v___x_3497_, v___x_3498_, v___y_3460_, v___y_3461_, v___x_3500_, v___y_3463_);
lean_dec_ref_known(v___x_3500_, 14);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3509_; 
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3509_ == 0)
{
lean_object* v_unused_3510_; 
v_unused_3510_ = lean_ctor_get(v___x_3501_, 0);
lean_dec(v_unused_3510_);
v___x_3503_ = v___x_3501_;
v_isShared_3504_ = v_isSharedCheck_3509_;
goto v_resetjp_3502_;
}
else
{
lean_dec(v___x_3501_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3509_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3505_; lean_object* v___x_3507_; 
v___x_3505_ = lean_box(0);
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 0, v___x_3505_);
v___x_3507_ = v___x_3503_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3505_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
else
{
lean_object* v_a_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3537_; 
v_a_3511_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3513_ = v___x_3501_;
v_isShared_3514_ = v_isSharedCheck_3537_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_a_3511_);
lean_dec(v___x_3501_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3537_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3520_; uint8_t v___y_3522_; uint8_t v___y_3532_; uint8_t v___x_3535_; 
lean_inc(v_a_3511_);
v___x_3520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3520_, 0, v_a_3511_);
v___x_3535_ = l_Lean_Exception_isInterrupt(v_a_3511_);
if (v___x_3535_ == 0)
{
uint8_t v___x_3536_; 
lean_inc(v_a_3511_);
v___x_3536_ = l_Lean_Exception_isRuntime(v_a_3511_);
v___y_3532_ = v___x_3536_;
goto v___jp_3531_;
}
else
{
v___y_3532_ = v___x_3535_;
goto v___jp_3531_;
}
v___jp_3515_:
{
lean_object* v___x_3516_; lean_object* v___x_3518_; 
v___x_3516_ = lean_box(0);
if (v_isShared_3514_ == 0)
{
lean_ctor_set_tag(v___x_3513_, 0);
lean_ctor_set(v___x_3513_, 0, v___x_3516_);
v___x_3518_ = v___x_3513_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_3516_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
v___jp_3521_:
{
if (v___y_3522_ == 0)
{
uint8_t v_hasTrace_3523_; 
lean_dec_ref_known(v___x_3520_, 1);
v_hasTrace_3523_ = lean_ctor_get_uint8(v_options_3467_, sizeof(void*)*1);
if (v_hasTrace_3523_ == 0)
{
lean_dec(v_a_3511_);
goto v___jp_3515_;
}
else
{
lean_object* v___x_3524_; lean_object* v___x_3525_; uint8_t v___x_3526_; 
v___x_3524_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3525_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_3526_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3480_, v_options_3467_, v___x_3525_);
if (v___x_3526_ == 0)
{
lean_dec(v_a_3511_);
goto v___jp_3515_;
}
else
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
lean_del_object(v___x_3513_);
v___x_3527_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_3528_ = l_Lean_Exception_toMessageData(v_a_3511_);
v___x_3529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3527_);
lean_ctor_set(v___x_3529_, 1, v___x_3528_);
v___x_3530_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_3524_, v___x_3529_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
return v___x_3530_;
}
}
}
else
{
lean_del_object(v___x_3513_);
lean_dec(v_a_3511_);
return v___x_3520_;
}
}
v___jp_3531_:
{
if (v___y_3532_ == 0)
{
uint8_t v___x_3533_; 
v___x_3533_ = l_Lean_Exception_isInterrupt(v_a_3511_);
if (v___x_3533_ == 0)
{
uint8_t v___x_3534_; 
lean_inc(v_a_3511_);
v___x_3534_ = l_Lean_Exception_isMaxRecDepth(v_a_3511_);
v___y_3522_ = v___x_3534_;
goto v___jp_3521_;
}
else
{
v___y_3522_ = v___x_3533_;
goto v___jp_3521_;
}
}
else
{
lean_del_object(v___x_3513_);
lean_dec(v_a_3511_);
return v___x_3520_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___boxed(lean_object* v___f_3538_, lean_object* v_ref_3539_, lean_object* v_goal_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
lean_object* v_res_3546_; 
v_res_3546_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(v___f_3538_, v_ref_3539_, v_goal_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
lean_dec(v_ref_3539_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(lean_object* v_c_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_){
_start:
{
lean_object* v_mctx_3552_; lean_object* v_ref_3553_; lean_object* v_env_3554_; lean_object* v_opts_3555_; lean_object* v_namingCtx_3556_; lean_object* v_goal_3557_; lean_object* v_decls_3558_; lean_object* v___x_3559_; 
v_mctx_3552_ = lean_ctor_get(v_c_3548_, 3);
lean_inc_ref(v_mctx_3552_);
v_ref_3553_ = lean_ctor_get(v_c_3548_, 1);
lean_inc(v_ref_3553_);
v_env_3554_ = lean_ctor_get(v_c_3548_, 2);
lean_inc_ref(v_env_3554_);
v_opts_3555_ = lean_ctor_get(v_c_3548_, 4);
lean_inc_ref(v_opts_3555_);
v_namingCtx_3556_ = lean_ctor_get(v_c_3548_, 5);
lean_inc_ref(v_namingCtx_3556_);
v_goal_3557_ = lean_ctor_get(v_c_3548_, 6);
lean_inc(v_goal_3557_);
lean_dec_ref(v_c_3548_);
v_decls_3558_ = lean_ctor_get(v_mctx_3552_, 5);
v___x_3559_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_decls_3558_, v_goal_3557_);
if (lean_obj_tag(v___x_3559_) == 1)
{
lean_object* v_val_3560_; lean_object* v_lctx_3561_; lean_object* v___f_3562_; lean_object* v___f_3563_; lean_object* v___x_3564_; 
v_val_3560_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_val_3560_);
lean_dec_ref_known(v___x_3559_, 1);
v_lctx_3561_ = lean_ctor_get(v_val_3560_, 1);
lean_inc_ref(v_lctx_3561_);
lean_dec(v_val_3560_);
v___f_3562_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___closed__0));
v___f_3563_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___boxed), 8, 3);
lean_closure_set(v___f_3563_, 0, v___f_3562_);
lean_closure_set(v___f_3563_, 1, v_ref_3553_);
lean_closure_set(v___f_3563_, 2, v_goal_3557_);
v___x_3564_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_3554_, v_mctx_3552_, v_lctx_3561_, v_opts_3555_, v_namingCtx_3556_, v___f_3563_, v_a_3549_, v_a_3550_);
lean_dec_ref(v_namingCtx_3556_);
return v___x_3564_;
}
else
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
lean_dec(v___x_3559_);
lean_dec(v_goal_3557_);
lean_dec_ref(v_namingCtx_3556_);
lean_dec_ref(v_opts_3555_);
lean_dec_ref(v_env_3554_);
lean_dec(v_ref_3553_);
lean_dec_ref(v_mctx_3552_);
v___x_3565_ = lean_box(0);
v___x_3566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3565_);
return v___x_3566_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___boxed(lean_object* v_c_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_){
_start:
{
lean_object* v_res_3571_; 
v_res_3571_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(v_c_3567_, v_a_3568_, v_a_3569_);
lean_dec(v_a_3569_);
lean_dec_ref(v_a_3568_);
return v_res_3571_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(lean_object* v___x_3572_, lean_object* v_val_3573_, lean_object* v_as_3574_, size_t v_i_3575_, size_t v_stop_3576_){
_start:
{
uint8_t v___x_3581_; uint8_t v___x_3582_; 
v___x_3581_ = 0;
v___x_3582_ = lean_usize_dec_eq(v_i_3575_, v_stop_3576_);
if (v___x_3582_ == 0)
{
lean_object* v___x_3583_; lean_object* v_pos_3584_; uint8_t v_severity_3585_; lean_object* v_data_3586_; lean_object* v___f_3587_; uint8_t v___x_3588_; lean_object* v___x_3589_; uint8_t v___x_3590_; uint8_t v___y_3592_; 
v___x_3583_ = lean_array_uget_borrowed(v_as_3574_, v_i_3575_);
v_pos_3584_ = lean_ctor_get(v___x_3583_, 1);
v_severity_3585_ = lean_ctor_get_uint8(v___x_3583_, sizeof(void*)*5 + 1);
v_data_3586_ = lean_ctor_get(v___x_3583_, 4);
v___f_3587_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
v___x_3588_ = 1;
lean_inc_ref(v_pos_3584_);
v___x_3589_ = l_Lean_FileMap_ofPosition(v___x_3572_, v_pos_3584_);
v___x_3590_ = l_Lean_Syntax_Range_contains(v_val_3573_, v___x_3589_, v___x_3588_);
lean_dec(v___x_3589_);
if (v_severity_3585_ == 2)
{
v___y_3592_ = v___x_3588_;
goto v___jp_3591_;
}
else
{
v___y_3592_ = v___x_3581_;
goto v___jp_3591_;
}
v___jp_3591_:
{
if (v___x_3590_ == 0)
{
goto v___jp_3577_;
}
else
{
if (v___y_3592_ == 0)
{
goto v___jp_3577_;
}
else
{
uint8_t v___x_3593_; 
lean_inc(v_data_3586_);
v___x_3593_ = l_Lean_MessageData_hasTag(v___f_3587_, v_data_3586_);
if (v___x_3593_ == 0)
{
return v___x_3588_;
}
else
{
if (v___x_3582_ == 0)
{
goto v___jp_3577_;
}
else
{
return v___x_3588_;
}
}
}
}
}
}
else
{
return v___x_3581_;
}
v___jp_3577_:
{
size_t v___x_3578_; size_t v___x_3579_; 
v___x_3578_ = ((size_t)1ULL);
v___x_3579_ = lean_usize_add(v_i_3575_, v___x_3578_);
v_i_3575_ = v___x_3579_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1___boxed(lean_object* v___x_3594_, lean_object* v_val_3595_, lean_object* v_as_3596_, lean_object* v_i_3597_, lean_object* v_stop_3598_){
_start:
{
size_t v_i_boxed_3599_; size_t v_stop_boxed_3600_; uint8_t v_res_3601_; lean_object* v_r_3602_; 
v_i_boxed_3599_ = lean_unbox_usize(v_i_3597_);
lean_dec(v_i_3597_);
v_stop_boxed_3600_ = lean_unbox_usize(v_stop_3598_);
lean_dec(v_stop_3598_);
v_res_3601_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3594_, v_val_3595_, v_as_3596_, v_i_boxed_3599_, v_stop_boxed_3600_);
lean_dec_ref(v_as_3596_);
lean_dec_ref(v_val_3595_);
lean_dec_ref(v___x_3594_);
v_r_3602_ = lean_box(v_res_3601_);
return v_r_3602_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(lean_object* v___x_3603_, lean_object* v_val_3604_, lean_object* v_x_3605_){
_start:
{
if (lean_obj_tag(v_x_3605_) == 0)
{
lean_object* v_cs_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; uint8_t v___x_3609_; 
v_cs_3606_ = lean_ctor_get(v_x_3605_, 0);
v___x_3607_ = lean_unsigned_to_nat(0u);
v___x_3608_ = lean_array_get_size(v_cs_3606_);
v___x_3609_ = lean_nat_dec_lt(v___x_3607_, v___x_3608_);
if (v___x_3609_ == 0)
{
return v___x_3609_;
}
else
{
if (v___x_3609_ == 0)
{
return v___x_3609_;
}
else
{
size_t v___x_3610_; size_t v___x_3611_; uint8_t v___x_3612_; 
v___x_3610_ = ((size_t)0ULL);
v___x_3611_ = lean_usize_of_nat(v___x_3608_);
v___x_3612_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3603_, v_val_3604_, v_cs_3606_, v___x_3610_, v___x_3611_);
return v___x_3612_;
}
}
}
else
{
lean_object* v_vs_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; uint8_t v___x_3616_; 
v_vs_3613_ = lean_ctor_get(v_x_3605_, 0);
v___x_3614_ = lean_unsigned_to_nat(0u);
v___x_3615_ = lean_array_get_size(v_vs_3613_);
v___x_3616_ = lean_nat_dec_lt(v___x_3614_, v___x_3615_);
if (v___x_3616_ == 0)
{
return v___x_3616_;
}
else
{
if (v___x_3616_ == 0)
{
return v___x_3616_;
}
else
{
size_t v___x_3617_; size_t v___x_3618_; uint8_t v___x_3619_; 
v___x_3617_ = ((size_t)0ULL);
v___x_3618_ = lean_usize_of_nat(v___x_3615_);
v___x_3619_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3603_, v_val_3604_, v_vs_3613_, v___x_3617_, v___x_3618_);
return v___x_3619_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(lean_object* v___x_3620_, lean_object* v_val_3621_, lean_object* v_as_3622_, size_t v_i_3623_, size_t v_stop_3624_){
_start:
{
uint8_t v___x_3625_; 
v___x_3625_ = lean_usize_dec_eq(v_i_3623_, v_stop_3624_);
if (v___x_3625_ == 0)
{
lean_object* v___x_3626_; uint8_t v___x_3627_; 
v___x_3626_ = lean_array_uget_borrowed(v_as_3622_, v_i_3623_);
v___x_3627_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3620_, v_val_3621_, v___x_3626_);
if (v___x_3627_ == 0)
{
size_t v___x_3628_; size_t v___x_3629_; 
v___x_3628_ = ((size_t)1ULL);
v___x_3629_ = lean_usize_add(v_i_3623_, v___x_3628_);
v_i_3623_ = v___x_3629_;
goto _start;
}
else
{
return v___x_3627_;
}
}
else
{
uint8_t v___x_3631_; 
v___x_3631_ = 0;
return v___x_3631_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3632_, lean_object* v_val_3633_, lean_object* v_as_3634_, lean_object* v_i_3635_, lean_object* v_stop_3636_){
_start:
{
size_t v_i_boxed_3637_; size_t v_stop_boxed_3638_; uint8_t v_res_3639_; lean_object* v_r_3640_; 
v_i_boxed_3637_ = lean_unbox_usize(v_i_3635_);
lean_dec(v_i_3635_);
v_stop_boxed_3638_ = lean_unbox_usize(v_stop_3636_);
lean_dec(v_stop_3636_);
v_res_3639_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3632_, v_val_3633_, v_as_3634_, v_i_boxed_3637_, v_stop_boxed_3638_);
lean_dec_ref(v_as_3634_);
lean_dec_ref(v_val_3633_);
lean_dec_ref(v___x_3632_);
v_r_3640_ = lean_box(v_res_3639_);
return v_r_3640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0___boxed(lean_object* v___x_3641_, lean_object* v_val_3642_, lean_object* v_x_3643_){
_start:
{
uint8_t v_res_3644_; lean_object* v_r_3645_; 
v_res_3644_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3641_, v_val_3642_, v_x_3643_);
lean_dec_ref(v_x_3643_);
lean_dec_ref(v_val_3642_);
lean_dec_ref(v___x_3641_);
v_r_3645_ = lean_box(v_res_3644_);
return v_r_3645_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(lean_object* v___x_3646_, lean_object* v_val_3647_, lean_object* v_t_3648_){
_start:
{
lean_object* v_root_3649_; lean_object* v_tail_3650_; uint8_t v___x_3651_; 
v_root_3649_ = lean_ctor_get(v_t_3648_, 0);
v_tail_3650_ = lean_ctor_get(v_t_3648_, 1);
v___x_3651_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3646_, v_val_3647_, v_root_3649_);
if (v___x_3651_ == 0)
{
lean_object* v___x_3652_; lean_object* v___x_3653_; uint8_t v___x_3654_; 
v___x_3652_ = lean_unsigned_to_nat(0u);
v___x_3653_ = lean_array_get_size(v_tail_3650_);
v___x_3654_ = lean_nat_dec_lt(v___x_3652_, v___x_3653_);
if (v___x_3654_ == 0)
{
return v___x_3651_;
}
else
{
if (v___x_3654_ == 0)
{
return v___x_3651_;
}
else
{
size_t v___x_3655_; size_t v___x_3656_; uint8_t v___x_3657_; 
v___x_3655_ = ((size_t)0ULL);
v___x_3656_ = lean_usize_of_nat(v___x_3653_);
v___x_3657_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3646_, v_val_3647_, v_tail_3650_, v___x_3655_, v___x_3656_);
return v___x_3657_;
}
}
}
else
{
return v___x_3651_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0___boxed(lean_object* v___x_3658_, lean_object* v_val_3659_, lean_object* v_t_3660_){
_start:
{
uint8_t v_res_3661_; lean_object* v_r_3662_; 
v_res_3661_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v___x_3658_, v_val_3659_, v_t_3660_);
lean_dec_ref(v_t_3660_);
lean_dec_ref(v_val_3659_);
lean_dec_ref(v___x_3658_);
v_r_3662_ = lean_box(v_res_3661_);
return v_r_3662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(lean_object* v_stx_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_){
_start:
{
uint8_t v___x_3667_; lean_object* v___x_3668_; 
v___x_3667_ = 0;
v___x_3668_ = l_Lean_Syntax_getRange_x3f(v_stx_3663_, v___x_3667_);
if (lean_obj_tag(v___x_3668_) == 1)
{
lean_object* v_val_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3682_; 
v_val_3669_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3671_ = v___x_3668_;
v_isShared_3672_ = v_isSharedCheck_3682_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_val_3669_);
lean_dec(v___x_3668_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3682_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3673_; lean_object* v_fileMap_3674_; lean_object* v_messages_3675_; lean_object* v___x_3676_; uint8_t v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3680_; 
v___x_3673_ = lean_st_ref_get(v_a_3665_);
v_fileMap_3674_ = lean_ctor_get(v_a_3664_, 1);
v_messages_3675_ = lean_ctor_get(v___x_3673_, 1);
lean_inc_ref(v_messages_3675_);
lean_dec(v___x_3673_);
v___x_3676_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_3675_);
v___x_3677_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v_fileMap_3674_, v_val_3669_, v___x_3676_);
lean_dec_ref(v___x_3676_);
lean_dec(v_val_3669_);
v___x_3678_ = lean_box(v___x_3677_);
if (v_isShared_3672_ == 0)
{
lean_ctor_set_tag(v___x_3671_, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3678_);
v___x_3680_ = v___x_3671_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v___x_3678_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
else
{
lean_object* v___x_3683_; lean_object* v___x_3684_; 
lean_dec(v___x_3668_);
v___x_3683_ = lean_box(v___x_3667_);
v___x_3684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3684_, 0, v___x_3683_);
return v___x_3684_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError___boxed(lean_object* v_stx_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_){
_start:
{
lean_object* v_res_3689_; 
v_res_3689_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(v_stx_3685_, v_a_3686_, v_a_3687_);
lean_dec(v_a_3687_);
lean_dec_ref(v_a_3686_);
lean_dec(v_stx_3685_);
return v_res_3689_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(lean_object* v_tree_3690_, lean_object* v_fileMap_3691_, lean_object* v_c_3692_){
_start:
{
lean_object* v___y_3694_; lean_object* v_kind_3698_; lean_object* v_ref_3699_; lean_object* v___y_3701_; 
v_kind_3698_ = lean_ctor_get(v_c_3692_, 0);
lean_inc(v_kind_3698_);
v_ref_3699_ = lean_ctor_get(v_c_3692_, 1);
lean_inc(v_ref_3699_);
lean_dec_ref(v_c_3692_);
if (lean_obj_tag(v_kind_3698_) == 0)
{
lean_object* v_insertPos_3717_; 
lean_dec(v_ref_3699_);
v_insertPos_3717_ = lean_ctor_get(v_kind_3698_, 1);
lean_inc(v_insertPos_3717_);
v___y_3701_ = v_insertPos_3717_;
goto v___jp_3700_;
}
else
{
uint8_t v___x_3718_; lean_object* v___x_3719_; 
v___x_3718_ = 0;
v___x_3719_ = l_Lean_Syntax_getPos_x3f(v_ref_3699_, v___x_3718_);
lean_dec(v_ref_3699_);
if (lean_obj_tag(v___x_3719_) == 0)
{
lean_object* v___x_3720_; 
v___x_3720_ = lean_unsigned_to_nat(0u);
v___y_3701_ = v___x_3720_;
goto v___jp_3700_;
}
else
{
lean_object* v_val_3721_; 
v_val_3721_ = lean_ctor_get(v___x_3719_, 0);
lean_inc(v_val_3721_);
lean_dec_ref_known(v___x_3719_, 1);
v___y_3701_ = v_val_3721_;
goto v___jp_3700_;
}
}
v___jp_3693_:
{
lean_object* v___x_3695_; lean_object* v___x_3696_; uint8_t v___x_3697_; 
v___x_3695_ = l_List_lengthTR___redArg(v___y_3694_);
lean_dec(v___y_3694_);
v___x_3696_ = lean_unsigned_to_nat(1u);
v___x_3697_ = lean_nat_dec_eq(v___x_3695_, v___x_3696_);
lean_dec(v___x_3695_);
return v___x_3697_;
}
v___jp_3700_:
{
lean_object* v___x_3702_; 
v___x_3702_ = l_Lean_Elab_InfoTree_goalsAt_x3f(v_fileMap_3691_, v_tree_3690_, v___y_3701_);
if (lean_obj_tag(v___x_3702_) == 1)
{
lean_object* v_tail_3703_; 
v_tail_3703_ = lean_ctor_get(v___x_3702_, 1);
lean_inc(v_tail_3703_);
if (lean_obj_tag(v_tail_3703_) == 0)
{
if (lean_obj_tag(v_kind_3698_) == 0)
{
lean_object* v_head_3704_; lean_object* v_tacticSeq_3705_; uint8_t v___x_3706_; lean_object* v___x_3707_; 
v_head_3704_ = lean_ctor_get(v___x_3702_, 0);
lean_inc(v_head_3704_);
lean_dec_ref_known(v___x_3702_, 2);
v_tacticSeq_3705_ = lean_ctor_get(v_kind_3698_, 0);
lean_inc(v_tacticSeq_3705_);
lean_dec_ref_known(v_kind_3698_, 2);
v___x_3706_ = 0;
v___x_3707_ = l_Lean_Syntax_getPos_x3f(v_tacticSeq_3705_, v___x_3706_);
lean_dec(v_tacticSeq_3705_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_tacticInfo_3708_; lean_object* v_goalsBefore_3709_; 
v_tacticInfo_3708_ = lean_ctor_get(v_head_3704_, 1);
lean_inc_ref(v_tacticInfo_3708_);
lean_dec(v_head_3704_);
v_goalsBefore_3709_ = lean_ctor_get(v_tacticInfo_3708_, 2);
lean_inc(v_goalsBefore_3709_);
lean_dec_ref(v_tacticInfo_3708_);
v___y_3694_ = v_goalsBefore_3709_;
goto v___jp_3693_;
}
else
{
lean_object* v_tacticInfo_3710_; lean_object* v_goalsAfter_3711_; 
lean_dec_ref_known(v___x_3707_, 1);
v_tacticInfo_3710_ = lean_ctor_get(v_head_3704_, 1);
lean_inc_ref(v_tacticInfo_3710_);
lean_dec(v_head_3704_);
v_goalsAfter_3711_ = lean_ctor_get(v_tacticInfo_3710_, 4);
lean_inc(v_goalsAfter_3711_);
lean_dec_ref(v_tacticInfo_3710_);
v___y_3694_ = v_goalsAfter_3711_;
goto v___jp_3693_;
}
}
else
{
lean_object* v_head_3712_; lean_object* v_tacticInfo_3713_; lean_object* v_goalsBefore_3714_; 
v_head_3712_ = lean_ctor_get(v___x_3702_, 0);
lean_inc(v_head_3712_);
lean_dec_ref_known(v___x_3702_, 2);
v_tacticInfo_3713_ = lean_ctor_get(v_head_3712_, 1);
lean_inc_ref(v_tacticInfo_3713_);
lean_dec(v_head_3712_);
v_goalsBefore_3714_ = lean_ctor_get(v_tacticInfo_3713_, 2);
lean_inc(v_goalsBefore_3714_);
lean_dec_ref(v_tacticInfo_3713_);
v___y_3694_ = v_goalsBefore_3714_;
goto v___jp_3693_;
}
}
else
{
uint8_t v___x_3715_; 
lean_dec_ref_known(v___x_3702_, 2);
lean_dec(v_tail_3703_);
lean_dec(v_kind_3698_);
v___x_3715_ = 0;
return v___x_3715_;
}
}
else
{
uint8_t v___x_3716_; 
lean_dec(v___x_3702_);
lean_dec(v_kind_3698_);
v___x_3716_ = 0;
return v___x_3716_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos___boxed(lean_object* v_tree_3722_, lean_object* v_fileMap_3723_, lean_object* v_c_3724_){
_start:
{
uint8_t v_res_3725_; lean_object* v_r_3726_; 
v_res_3725_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(v_tree_3722_, v_fileMap_3723_, v_c_3724_);
v_r_3726_ = lean_box(v_res_3725_);
return v_r_3726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(lean_object* v___y_3727_){
_start:
{
lean_object* v___x_3729_; lean_object* v_infoState_3730_; lean_object* v_trees_3731_; lean_object* v___x_3732_; 
v___x_3729_ = lean_st_ref_get(v___y_3727_);
v_infoState_3730_ = lean_ctor_get(v___x_3729_, 8);
lean_inc_ref(v_infoState_3730_);
lean_dec(v___x_3729_);
v_trees_3731_ = lean_ctor_get(v_infoState_3730_, 2);
lean_inc_ref(v_trees_3731_);
lean_dec_ref(v_infoState_3730_);
v___x_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3732_, 0, v_trees_3731_);
return v___x_3732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg___boxed(lean_object* v___y_3733_, lean_object* v___y_3734_){
_start:
{
lean_object* v_res_3735_; 
v_res_3735_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_3733_);
lean_dec(v___y_3733_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
lean_object* v___x_3739_; 
v___x_3739_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_3737_);
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___boxed(lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_){
_start:
{
lean_object* v_res_3743_; 
v_res_3743_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(v___y_3740_, v___y_3741_);
lean_dec(v___y_3741_);
lean_dec_ref(v___y_3740_);
return v_res_3743_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3745_; lean_object* v___x_3746_; 
v___x_3745_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__0));
v___x_3746_ = l_Lean_stringToMessageData(v___x_3745_);
return v___x_3746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(lean_object* v_tree_3747_, lean_object* v___x_3748_, lean_object* v___x_3749_, lean_object* v_as_3750_, size_t v_sz_3751_, size_t v_i_3752_, lean_object* v_b_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_){
_start:
{
lean_object* v_a_3758_; uint8_t v___x_3762_; 
v___x_3762_ = lean_usize_dec_lt(v_i_3752_, v_sz_3751_);
if (v___x_3762_ == 0)
{
lean_object* v___x_3763_; 
lean_dec_ref(v___x_3748_);
lean_dec_ref(v_tree_3747_);
v___x_3763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3763_, 0, v_b_3753_);
return v___x_3763_;
}
else
{
lean_object* v___x_3764_; lean_object* v_a_3765_; uint8_t v___x_3766_; 
v___x_3764_ = lean_box(0);
v_a_3765_ = lean_array_uget_borrowed(v_as_3750_, v_i_3752_);
lean_inc(v_a_3765_);
lean_inc_ref(v___x_3748_);
lean_inc_ref(v_tree_3747_);
v___x_3766_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(v_tree_3747_, v___x_3748_, v_a_3765_);
if (v___x_3766_ == 0)
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v_scopes_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v_opts_3773_; uint8_t v_hasTrace_3774_; 
v___x_3767_ = l_Lean_inheritedTraceOptions;
v___x_3768_ = lean_st_ref_get(v___x_3767_);
v___x_3769_ = lean_st_ref_get(v___y_3755_);
v_scopes_3770_ = lean_ctor_get(v___x_3769_, 2);
lean_inc(v_scopes_3770_);
lean_dec(v___x_3769_);
v___x_3771_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3772_ = l_List_head_x21___redArg(v___x_3771_, v_scopes_3770_);
lean_dec(v_scopes_3770_);
v_opts_3773_ = lean_ctor_get(v___x_3772_, 1);
lean_inc_ref(v_opts_3773_);
lean_dec(v___x_3772_);
v_hasTrace_3774_ = lean_ctor_get_uint8(v_opts_3773_, sizeof(void*)*1);
if (v_hasTrace_3774_ == 0)
{
lean_dec_ref(v_opts_3773_);
lean_dec(v___x_3768_);
v_a_3758_ = v___x_3764_;
goto v___jp_3757_;
}
else
{
lean_object* v___x_3775_; lean_object* v___x_3776_; uint8_t v___x_3777_; 
v___x_3775_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3776_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_3777_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3768_, v_opts_3773_, v___x_3776_);
lean_dec_ref(v_opts_3773_);
lean_dec(v___x_3768_);
if (v___x_3777_ == 0)
{
v_a_3758_ = v___x_3764_;
goto v___jp_3757_;
}
else
{
lean_object* v___x_3778_; lean_object* v___x_3779_; 
v___x_3778_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1);
v___x_3779_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_3775_, v___x_3778_, v___y_3754_, v___y_3755_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_dec_ref_known(v___x_3779_, 1);
v_a_3758_ = v___x_3764_;
goto v___jp_3757_;
}
else
{
lean_dec_ref(v___x_3748_);
lean_dec_ref(v_tree_3747_);
return v___x_3779_;
}
}
}
}
else
{
lean_object* v_kind_3780_; 
v_kind_3780_ = lean_ctor_get(v_a_3765_, 0);
if (lean_obj_tag(v_kind_3780_) == 0)
{
lean_object* v_ref_3781_; lean_object* v_tacticSeq_3782_; lean_object* v_insertPos_3783_; lean_object* v___x_3784_; 
v_ref_3781_ = lean_ctor_get(v_a_3765_, 1);
v_tacticSeq_3782_ = lean_ctor_get(v_kind_3780_, 0);
v_insertPos_3783_ = lean_ctor_get(v_kind_3780_, 1);
lean_inc(v_a_3765_);
v___x_3784_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(v_a_3765_, v___y_3754_, v___y_3755_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_a_3785_; lean_object* v___x_3786_; 
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
lean_inc(v_a_3785_);
lean_dec_ref_known(v___x_3784_, 1);
lean_inc(v_insertPos_3783_);
lean_inc(v_ref_3781_);
v___x_3786_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(v_tacticSeq_3782_, v_ref_3781_, v_insertPos_3783_, v_a_3785_, v___x_3749_, v___y_3754_, v___y_3755_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_dec_ref_known(v___x_3786_, 1);
v_a_3758_ = v___x_3764_;
goto v___jp_3757_;
}
else
{
lean_dec_ref(v___x_3748_);
lean_dec_ref(v_tree_3747_);
return v___x_3786_;
}
}
else
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3794_; 
lean_dec_ref(v___x_3748_);
lean_dec_ref(v_tree_3747_);
v_a_3787_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3789_ = v___x_3784_;
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3784_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3792_; 
if (v_isShared_3790_ == 0)
{
v___x_3792_ = v___x_3789_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_a_3787_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
else
{
lean_object* v___x_3795_; 
lean_inc(v_a_3765_);
v___x_3795_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(v_a_3765_, v___y_3754_, v___y_3755_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_dec_ref_known(v___x_3795_, 1);
v_a_3758_ = v___x_3764_;
goto v___jp_3757_;
}
else
{
lean_dec_ref(v___x_3748_);
lean_dec_ref(v_tree_3747_);
return v___x_3795_;
}
}
}
}
v___jp_3757_:
{
size_t v___x_3759_; size_t v___x_3760_; 
v___x_3759_ = ((size_t)1ULL);
v___x_3760_ = lean_usize_add(v_i_3752_, v___x_3759_);
v_i_3752_ = v___x_3760_;
v_b_3753_ = v_a_3758_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___boxed(lean_object* v_tree_3796_, lean_object* v___x_3797_, lean_object* v___x_3798_, lean_object* v_as_3799_, lean_object* v_sz_3800_, lean_object* v_i_3801_, lean_object* v_b_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
size_t v_sz_boxed_3806_; size_t v_i_boxed_3807_; lean_object* v_res_3808_; 
v_sz_boxed_3806_ = lean_unbox_usize(v_sz_3800_);
lean_dec(v_sz_3800_);
v_i_boxed_3807_ = lean_unbox_usize(v_i_3801_);
lean_dec(v_i_3801_);
v_res_3808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_tree_3796_, v___x_3797_, v___x_3798_, v_as_3799_, v_sz_boxed_3806_, v_i_boxed_3807_, v_b_3802_, v___y_3803_, v___y_3804_);
lean_dec(v___y_3804_);
lean_dec_ref(v___y_3803_);
lean_dec_ref(v_as_3799_);
lean_dec(v___x_3798_);
return v_res_3808_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3813_; lean_object* v___x_3814_; 
v___x_3813_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__1));
v___x_3814_ = l_Lean_stringToMessageData(v___x_3813_);
return v___x_3814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(lean_object* v_stx_3815_, lean_object* v___x_3816_, lean_object* v___x_3817_, lean_object* v___x_3818_, lean_object* v___x_3819_, lean_object* v_as_3820_, size_t v_sz_3821_, size_t v_i_3822_, lean_object* v_b_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_){
_start:
{
uint8_t v___x_3827_; 
v___x_3827_ = lean_usize_dec_lt(v_i_3822_, v_sz_3821_);
if (v___x_3827_ == 0)
{
lean_object* v___x_3828_; 
lean_dec_ref(v___x_3818_);
lean_dec(v_stx_3815_);
v___x_3828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3828_, 0, v_b_3823_);
return v___x_3828_;
}
else
{
lean_object* v_a_3829_; lean_object* v___x_3830_; 
lean_dec_ref(v_b_3823_);
v_a_3829_ = lean_array_uget_borrowed(v_as_3820_, v_i_3822_);
lean_inc(v_a_3829_);
lean_inc(v_stx_3815_);
v___x_3830_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3815_, v___x_3816_, v_a_3829_, v___x_3817_, v___y_3824_, v___y_3825_);
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v_a_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v_scopes_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v_opts_3838_; uint8_t v_hasTrace_3839_; lean_object* v___x_3840_; lean_object* v___y_3842_; lean_object* v___y_3843_; 
v_a_3831_ = lean_ctor_get(v___x_3830_, 0);
lean_inc(v_a_3831_);
lean_dec_ref_known(v___x_3830_, 1);
v___x_3832_ = l_Lean_inheritedTraceOptions;
v___x_3833_ = lean_st_ref_get(v___x_3832_);
v___x_3834_ = lean_st_ref_get(v___y_3825_);
v_scopes_3835_ = lean_ctor_get(v___x_3834_, 2);
lean_inc(v_scopes_3835_);
lean_dec(v___x_3834_);
v___x_3836_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3837_ = l_List_head_x21___redArg(v___x_3836_, v_scopes_3835_);
lean_dec(v_scopes_3835_);
v_opts_3838_ = lean_ctor_get(v___x_3837_, 1);
lean_inc_ref(v_opts_3838_);
lean_dec(v___x_3837_);
v_hasTrace_3839_ = lean_ctor_get_uint8(v_opts_3838_, sizeof(void*)*1);
v___x_3840_ = lean_box(0);
if (v_hasTrace_3839_ == 0)
{
lean_dec_ref(v_opts_3838_);
lean_dec(v___x_3833_);
v___y_3842_ = v___y_3824_;
v___y_3843_ = v___y_3825_;
goto v___jp_3841_;
}
else
{
lean_object* v___x_3859_; lean_object* v___x_3860_; uint8_t v___x_3861_; 
v___x_3859_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3860_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_3861_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3833_, v_opts_3838_, v___x_3860_);
lean_dec_ref(v_opts_3838_);
lean_dec(v___x_3833_);
if (v___x_3861_ == 0)
{
v___y_3842_ = v___y_3824_;
v___y_3843_ = v___y_3825_;
goto v___jp_3841_;
}
else
{
lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3862_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_3863_ = lean_array_get_size(v_a_3831_);
v___x_3864_ = l_Nat_reprFast(v___x_3863_);
v___x_3865_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3864_);
v___x_3866_ = l_Lean_MessageData_ofFormat(v___x_3865_);
v___x_3867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3862_);
lean_ctor_set(v___x_3867_, 1, v___x_3866_);
v___x_3868_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_3859_, v___x_3867_, v___y_3824_, v___y_3825_);
if (lean_obj_tag(v___x_3868_) == 0)
{
lean_dec_ref_known(v___x_3868_, 1);
v___y_3842_ = v___y_3824_;
v___y_3843_ = v___y_3825_;
goto v___jp_3841_;
}
else
{
lean_object* v_a_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3876_; 
lean_dec(v_a_3831_);
lean_dec_ref(v___x_3818_);
lean_dec(v_stx_3815_);
v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3868_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3871_ = v___x_3868_;
v_isShared_3872_ = v_isSharedCheck_3876_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_a_3869_);
lean_dec(v___x_3868_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3876_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___x_3874_; 
if (v_isShared_3872_ == 0)
{
v___x_3874_ = v___x_3871_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_a_3869_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
}
}
}
v___jp_3841_:
{
size_t v_sz_3844_; size_t v___x_3845_; lean_object* v___x_3846_; 
v_sz_3844_ = lean_array_size(v_a_3831_);
v___x_3845_ = ((size_t)0ULL);
lean_inc_ref(v___x_3818_);
lean_inc(v_a_3829_);
v___x_3846_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_3829_, v___x_3818_, v___x_3819_, v_a_3831_, v_sz_3844_, v___x_3845_, v___x_3840_, v___y_3842_, v___y_3843_);
lean_dec(v_a_3831_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_object* v___x_3847_; size_t v___x_3848_; size_t v___x_3849_; 
lean_dec_ref_known(v___x_3846_, 1);
v___x_3847_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_3848_ = ((size_t)1ULL);
v___x_3849_ = lean_usize_add(v_i_3822_, v___x_3848_);
v_i_3822_ = v___x_3849_;
v_b_3823_ = v___x_3847_;
goto _start;
}
else
{
lean_object* v_a_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3858_; 
lean_dec_ref(v___x_3818_);
lean_dec(v_stx_3815_);
v_a_3851_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_3858_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3853_ = v___x_3846_;
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_a_3851_);
lean_dec(v___x_3846_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3856_; 
if (v_isShared_3854_ == 0)
{
v___x_3856_ = v___x_3853_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_a_3851_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
}
}
}
else
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3884_; 
lean_dec_ref(v___x_3818_);
lean_dec(v_stx_3815_);
v_a_3877_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3879_ = v___x_3830_;
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3830_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_a_3877_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___boxed(lean_object* v_stx_3885_, lean_object* v___x_3886_, lean_object* v___x_3887_, lean_object* v___x_3888_, lean_object* v___x_3889_, lean_object* v_as_3890_, lean_object* v_sz_3891_, lean_object* v_i_3892_, lean_object* v_b_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_){
_start:
{
size_t v_sz_boxed_3897_; size_t v_i_boxed_3898_; lean_object* v_res_3899_; 
v_sz_boxed_3897_ = lean_unbox_usize(v_sz_3891_);
lean_dec(v_sz_3891_);
v_i_boxed_3898_ = lean_unbox_usize(v_i_3892_);
lean_dec(v_i_3892_);
v_res_3899_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_3885_, v___x_3886_, v___x_3887_, v___x_3888_, v___x_3889_, v_as_3890_, v_sz_boxed_3897_, v_i_boxed_3898_, v_b_3893_, v___y_3894_, v___y_3895_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec_ref(v_as_3890_);
lean_dec(v___x_3889_);
lean_dec_ref(v___x_3887_);
lean_dec_ref(v___x_3886_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(lean_object* v_stx_3900_, lean_object* v___x_3901_, lean_object* v___x_3902_, lean_object* v___x_3903_, lean_object* v___x_3904_, lean_object* v_as_3905_, size_t v_sz_3906_, size_t v_i_3907_, lean_object* v_b_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_){
_start:
{
uint8_t v___x_3912_; 
v___x_3912_ = lean_usize_dec_lt(v_i_3907_, v_sz_3906_);
if (v___x_3912_ == 0)
{
lean_object* v___x_3913_; 
lean_dec_ref(v___x_3903_);
lean_dec(v_stx_3900_);
v___x_3913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3913_, 0, v_b_3908_);
return v___x_3913_;
}
else
{
lean_object* v_a_3914_; lean_object* v___x_3915_; 
lean_dec_ref(v_b_3908_);
v_a_3914_ = lean_array_uget_borrowed(v_as_3905_, v_i_3907_);
lean_inc(v_a_3914_);
lean_inc(v_stx_3900_);
v___x_3915_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3900_, v___x_3901_, v_a_3914_, v___x_3902_, v___y_3909_, v___y_3910_);
if (lean_obj_tag(v___x_3915_) == 0)
{
lean_object* v_a_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v_scopes_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v_opts_3923_; uint8_t v_hasTrace_3924_; lean_object* v___x_3925_; lean_object* v___y_3927_; lean_object* v___y_3928_; 
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
lean_inc(v_a_3916_);
lean_dec_ref_known(v___x_3915_, 1);
v___x_3917_ = l_Lean_inheritedTraceOptions;
v___x_3918_ = lean_st_ref_get(v___x_3917_);
v___x_3919_ = lean_st_ref_get(v___y_3910_);
v_scopes_3920_ = lean_ctor_get(v___x_3919_, 2);
lean_inc(v_scopes_3920_);
lean_dec(v___x_3919_);
v___x_3921_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3922_ = l_List_head_x21___redArg(v___x_3921_, v_scopes_3920_);
lean_dec(v_scopes_3920_);
v_opts_3923_ = lean_ctor_get(v___x_3922_, 1);
lean_inc_ref(v_opts_3923_);
lean_dec(v___x_3922_);
v_hasTrace_3924_ = lean_ctor_get_uint8(v_opts_3923_, sizeof(void*)*1);
v___x_3925_ = lean_box(0);
if (v_hasTrace_3924_ == 0)
{
lean_dec_ref(v_opts_3923_);
lean_dec(v___x_3918_);
v___y_3927_ = v___y_3909_;
v___y_3928_ = v___y_3910_;
goto v___jp_3926_;
}
else
{
lean_object* v___x_3944_; lean_object* v___x_3945_; uint8_t v___x_3946_; 
v___x_3944_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3945_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_3946_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3918_, v_opts_3923_, v___x_3945_);
lean_dec_ref(v_opts_3923_);
lean_dec(v___x_3918_);
if (v___x_3946_ == 0)
{
v___y_3927_ = v___y_3909_;
v___y_3928_ = v___y_3910_;
goto v___jp_3926_;
}
else
{
lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; 
v___x_3947_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_3948_ = lean_array_get_size(v_a_3916_);
v___x_3949_ = l_Nat_reprFast(v___x_3948_);
v___x_3950_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3949_);
v___x_3951_ = l_Lean_MessageData_ofFormat(v___x_3950_);
v___x_3952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3947_);
lean_ctor_set(v___x_3952_, 1, v___x_3951_);
v___x_3953_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_3944_, v___x_3952_, v___y_3909_, v___y_3910_);
if (lean_obj_tag(v___x_3953_) == 0)
{
lean_dec_ref_known(v___x_3953_, 1);
v___y_3927_ = v___y_3909_;
v___y_3928_ = v___y_3910_;
goto v___jp_3926_;
}
else
{
lean_object* v_a_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3961_; 
lean_dec(v_a_3916_);
lean_dec_ref(v___x_3903_);
lean_dec(v_stx_3900_);
v_a_3954_ = lean_ctor_get(v___x_3953_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v___x_3953_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3956_ = v___x_3953_;
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_a_3954_);
lean_dec(v___x_3953_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3959_; 
if (v_isShared_3957_ == 0)
{
v___x_3959_ = v___x_3956_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_a_3954_);
v___x_3959_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
return v___x_3959_;
}
}
}
}
}
v___jp_3926_:
{
size_t v_sz_3929_; size_t v___x_3930_; lean_object* v___x_3931_; 
v_sz_3929_ = lean_array_size(v_a_3916_);
v___x_3930_ = ((size_t)0ULL);
lean_inc_ref(v___x_3903_);
lean_inc(v_a_3914_);
v___x_3931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_3914_, v___x_3903_, v___x_3904_, v_a_3916_, v_sz_3929_, v___x_3930_, v___x_3925_, v___y_3927_, v___y_3928_);
lean_dec(v_a_3916_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v___x_3932_; size_t v___x_3933_; size_t v___x_3934_; lean_object* v___x_3935_; 
lean_dec_ref_known(v___x_3931_, 1);
v___x_3932_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_3933_ = ((size_t)1ULL);
v___x_3934_ = lean_usize_add(v_i_3907_, v___x_3933_);
v___x_3935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_3900_, v___x_3901_, v___x_3902_, v___x_3903_, v___x_3904_, v_as_3905_, v_sz_3906_, v___x_3934_, v___x_3932_, v___y_3909_, v___y_3910_);
return v___x_3935_;
}
else
{
lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3943_; 
lean_dec_ref(v___x_3903_);
lean_dec(v_stx_3900_);
v_a_3936_ = lean_ctor_get(v___x_3931_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3931_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3938_ = v___x_3931_;
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v___x_3931_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3941_; 
if (v_isShared_3939_ == 0)
{
v___x_3941_ = v___x_3938_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_a_3936_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
}
}
}
else
{
lean_object* v_a_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3969_; 
lean_dec_ref(v___x_3903_);
lean_dec(v_stx_3900_);
v_a_3962_ = lean_ctor_get(v___x_3915_, 0);
v_isSharedCheck_3969_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_3969_ == 0)
{
v___x_3964_ = v___x_3915_;
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_a_3962_);
lean_dec(v___x_3915_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v___x_3967_; 
if (v_isShared_3965_ == 0)
{
v___x_3967_ = v___x_3964_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_a_3962_);
v___x_3967_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
return v___x_3967_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3___boxed(lean_object* v_stx_3970_, lean_object* v___x_3971_, lean_object* v___x_3972_, lean_object* v___x_3973_, lean_object* v___x_3974_, lean_object* v_as_3975_, lean_object* v_sz_3976_, lean_object* v_i_3977_, lean_object* v_b_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_){
_start:
{
size_t v_sz_boxed_3982_; size_t v_i_boxed_3983_; lean_object* v_res_3984_; 
v_sz_boxed_3982_ = lean_unbox_usize(v_sz_3976_);
lean_dec(v_sz_3976_);
v_i_boxed_3983_ = lean_unbox_usize(v_i_3977_);
lean_dec(v_i_3977_);
v_res_3984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(v_stx_3970_, v___x_3971_, v___x_3972_, v___x_3973_, v___x_3974_, v_as_3975_, v_sz_boxed_3982_, v_i_boxed_3983_, v_b_3978_, v___y_3979_, v___y_3980_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
lean_dec_ref(v_as_3975_);
lean_dec(v___x_3974_);
lean_dec_ref(v___x_3972_);
lean_dec_ref(v___x_3971_);
return v_res_3984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(lean_object* v_stx_3988_, lean_object* v___x_3989_, lean_object* v___x_3990_, lean_object* v___x_3991_, lean_object* v___x_3992_, lean_object* v_as_3993_, size_t v_sz_3994_, size_t v_i_3995_, lean_object* v_b_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_){
_start:
{
uint8_t v___x_4000_; 
v___x_4000_ = lean_usize_dec_lt(v_i_3995_, v_sz_3994_);
if (v___x_4000_ == 0)
{
lean_object* v___x_4001_; 
lean_dec_ref(v___x_3991_);
lean_dec(v_stx_3988_);
v___x_4001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4001_, 0, v_b_3996_);
return v___x_4001_;
}
else
{
lean_object* v_a_4002_; lean_object* v___x_4003_; 
lean_dec_ref(v_b_3996_);
v_a_4002_ = lean_array_uget_borrowed(v_as_3993_, v_i_3995_);
lean_inc(v_a_4002_);
lean_inc(v_stx_3988_);
v___x_4003_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3988_, v___x_3989_, v_a_4002_, v___x_3990_, v___y_3997_, v___y_3998_);
if (lean_obj_tag(v___x_4003_) == 0)
{
lean_object* v_a_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v_scopes_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v_opts_4011_; uint8_t v_hasTrace_4012_; lean_object* v___x_4013_; lean_object* v___y_4015_; lean_object* v___y_4016_; 
v_a_4004_ = lean_ctor_get(v___x_4003_, 0);
lean_inc(v_a_4004_);
lean_dec_ref_known(v___x_4003_, 1);
v___x_4005_ = l_Lean_inheritedTraceOptions;
v___x_4006_ = lean_st_ref_get(v___x_4005_);
v___x_4007_ = lean_st_ref_get(v___y_3998_);
v_scopes_4008_ = lean_ctor_get(v___x_4007_, 2);
lean_inc(v_scopes_4008_);
lean_dec(v___x_4007_);
v___x_4009_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4010_ = l_List_head_x21___redArg(v___x_4009_, v_scopes_4008_);
lean_dec(v_scopes_4008_);
v_opts_4011_ = lean_ctor_get(v___x_4010_, 1);
lean_inc_ref(v_opts_4011_);
lean_dec(v___x_4010_);
v_hasTrace_4012_ = lean_ctor_get_uint8(v_opts_4011_, sizeof(void*)*1);
v___x_4013_ = lean_box(0);
if (v_hasTrace_4012_ == 0)
{
lean_dec_ref(v_opts_4011_);
lean_dec(v___x_4006_);
v___y_4015_ = v___y_3997_;
v___y_4016_ = v___y_3998_;
goto v___jp_4014_;
}
else
{
lean_object* v___x_4032_; lean_object* v___x_4033_; uint8_t v___x_4034_; 
v___x_4032_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4033_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_4034_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4006_, v_opts_4011_, v___x_4033_);
lean_dec_ref(v_opts_4011_);
lean_dec(v___x_4006_);
if (v___x_4034_ == 0)
{
v___y_4015_ = v___y_3997_;
v___y_4016_ = v___y_3998_;
goto v___jp_4014_;
}
else
{
lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
v___x_4035_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_4036_ = lean_array_get_size(v_a_4004_);
v___x_4037_ = l_Nat_reprFast(v___x_4036_);
v___x_4038_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4037_);
v___x_4039_ = l_Lean_MessageData_ofFormat(v___x_4038_);
v___x_4040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4040_, 0, v___x_4035_);
lean_ctor_set(v___x_4040_, 1, v___x_4039_);
v___x_4041_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_4032_, v___x_4040_, v___y_3997_, v___y_3998_);
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_dec_ref_known(v___x_4041_, 1);
v___y_4015_ = v___y_3997_;
v___y_4016_ = v___y_3998_;
goto v___jp_4014_;
}
else
{
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4049_; 
lean_dec(v_a_4004_);
lean_dec_ref(v___x_3991_);
lean_dec(v_stx_3988_);
v_a_4042_ = lean_ctor_get(v___x_4041_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4044_ = v___x_4041_;
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___x_4041_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4047_; 
if (v_isShared_4045_ == 0)
{
v___x_4047_ = v___x_4044_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_a_4042_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
}
}
}
v___jp_4014_:
{
size_t v_sz_4017_; size_t v___x_4018_; lean_object* v___x_4019_; 
v_sz_4017_ = lean_array_size(v_a_4004_);
v___x_4018_ = ((size_t)0ULL);
lean_inc_ref(v___x_3991_);
lean_inc(v_a_4002_);
v___x_4019_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4002_, v___x_3991_, v___x_3992_, v_a_4004_, v_sz_4017_, v___x_4018_, v___x_4013_, v___y_4015_, v___y_4016_);
lean_dec(v_a_4004_);
if (lean_obj_tag(v___x_4019_) == 0)
{
lean_object* v___x_4020_; size_t v___x_4021_; size_t v___x_4022_; 
lean_dec_ref_known(v___x_4019_, 1);
v___x_4020_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_4021_ = ((size_t)1ULL);
v___x_4022_ = lean_usize_add(v_i_3995_, v___x_4021_);
v_i_3995_ = v___x_4022_;
v_b_3996_ = v___x_4020_;
goto _start;
}
else
{
lean_object* v_a_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4031_; 
lean_dec_ref(v___x_3991_);
lean_dec(v_stx_3988_);
v_a_4024_ = lean_ctor_get(v___x_4019_, 0);
v_isSharedCheck_4031_ = !lean_is_exclusive(v___x_4019_);
if (v_isSharedCheck_4031_ == 0)
{
v___x_4026_ = v___x_4019_;
v_isShared_4027_ = v_isSharedCheck_4031_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_a_4024_);
lean_dec(v___x_4019_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4031_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v___x_4029_; 
if (v_isShared_4027_ == 0)
{
v___x_4029_ = v___x_4026_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v_a_4024_);
v___x_4029_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
return v___x_4029_;
}
}
}
}
}
else
{
lean_object* v_a_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4057_; 
lean_dec_ref(v___x_3991_);
lean_dec(v_stx_3988_);
v_a_4050_ = lean_ctor_get(v___x_4003_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_4003_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4052_ = v___x_4003_;
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_a_4050_);
lean_dec(v___x_4003_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___x_4055_; 
if (v_isShared_4053_ == 0)
{
v___x_4055_ = v___x_4052_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_a_4050_);
v___x_4055_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
return v___x_4055_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_stx_4058_, lean_object* v___x_4059_, lean_object* v___x_4060_, lean_object* v___x_4061_, lean_object* v___x_4062_, lean_object* v_as_4063_, lean_object* v_sz_4064_, lean_object* v_i_4065_, lean_object* v_b_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
size_t v_sz_boxed_4070_; size_t v_i_boxed_4071_; lean_object* v_res_4072_; 
v_sz_boxed_4070_ = lean_unbox_usize(v_sz_4064_);
lean_dec(v_sz_4064_);
v_i_boxed_4071_ = lean_unbox_usize(v_i_4065_);
lean_dec(v_i_4065_);
v_res_4072_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4058_, v___x_4059_, v___x_4060_, v___x_4061_, v___x_4062_, v_as_4063_, v_sz_boxed_4070_, v_i_boxed_4071_, v_b_4066_, v___y_4067_, v___y_4068_);
lean_dec(v___y_4068_);
lean_dec_ref(v___y_4067_);
lean_dec_ref(v_as_4063_);
lean_dec(v___x_4062_);
lean_dec_ref(v___x_4060_);
lean_dec_ref(v___x_4059_);
return v_res_4072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(lean_object* v_stx_4073_, lean_object* v___x_4074_, lean_object* v___x_4075_, lean_object* v___x_4076_, lean_object* v___x_4077_, lean_object* v_as_4078_, size_t v_sz_4079_, size_t v_i_4080_, lean_object* v_b_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
uint8_t v___x_4085_; 
v___x_4085_ = lean_usize_dec_lt(v_i_4080_, v_sz_4079_);
if (v___x_4085_ == 0)
{
lean_object* v___x_4086_; 
lean_dec_ref(v___x_4076_);
lean_dec(v_stx_4073_);
v___x_4086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4086_, 0, v_b_4081_);
return v___x_4086_;
}
else
{
lean_object* v_a_4087_; lean_object* v___x_4088_; 
lean_dec_ref(v_b_4081_);
v_a_4087_ = lean_array_uget_borrowed(v_as_4078_, v_i_4080_);
lean_inc(v_a_4087_);
lean_inc(v_stx_4073_);
v___x_4088_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_4073_, v___x_4074_, v_a_4087_, v___x_4075_, v___y_4082_, v___y_4083_);
if (lean_obj_tag(v___x_4088_) == 0)
{
lean_object* v_a_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v_scopes_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v_opts_4096_; uint8_t v_hasTrace_4097_; lean_object* v___x_4098_; lean_object* v___y_4100_; lean_object* v___y_4101_; 
v_a_4089_ = lean_ctor_get(v___x_4088_, 0);
lean_inc(v_a_4089_);
lean_dec_ref_known(v___x_4088_, 1);
v___x_4090_ = l_Lean_inheritedTraceOptions;
v___x_4091_ = lean_st_ref_get(v___x_4090_);
v___x_4092_ = lean_st_ref_get(v___y_4083_);
v_scopes_4093_ = lean_ctor_get(v___x_4092_, 2);
lean_inc(v_scopes_4093_);
lean_dec(v___x_4092_);
v___x_4094_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4095_ = l_List_head_x21___redArg(v___x_4094_, v_scopes_4093_);
lean_dec(v_scopes_4093_);
v_opts_4096_ = lean_ctor_get(v___x_4095_, 1);
lean_inc_ref(v_opts_4096_);
lean_dec(v___x_4095_);
v_hasTrace_4097_ = lean_ctor_get_uint8(v_opts_4096_, sizeof(void*)*1);
v___x_4098_ = lean_box(0);
if (v_hasTrace_4097_ == 0)
{
lean_dec_ref(v_opts_4096_);
lean_dec(v___x_4091_);
v___y_4100_ = v___y_4082_;
v___y_4101_ = v___y_4083_;
goto v___jp_4099_;
}
else
{
lean_object* v___x_4117_; lean_object* v___x_4118_; uint8_t v___x_4119_; 
v___x_4117_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4118_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_4119_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4091_, v_opts_4096_, v___x_4118_);
lean_dec_ref(v_opts_4096_);
lean_dec(v___x_4091_);
if (v___x_4119_ == 0)
{
v___y_4100_ = v___y_4082_;
v___y_4101_ = v___y_4083_;
goto v___jp_4099_;
}
else
{
lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; 
v___x_4120_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_4121_ = lean_array_get_size(v_a_4089_);
v___x_4122_ = l_Nat_reprFast(v___x_4121_);
v___x_4123_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4123_, 0, v___x_4122_);
v___x_4124_ = l_Lean_MessageData_ofFormat(v___x_4123_);
v___x_4125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4120_);
lean_ctor_set(v___x_4125_, 1, v___x_4124_);
v___x_4126_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_4117_, v___x_4125_, v___y_4082_, v___y_4083_);
if (lean_obj_tag(v___x_4126_) == 0)
{
lean_dec_ref_known(v___x_4126_, 1);
v___y_4100_ = v___y_4082_;
v___y_4101_ = v___y_4083_;
goto v___jp_4099_;
}
else
{
lean_object* v_a_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4134_; 
lean_dec(v_a_4089_);
lean_dec_ref(v___x_4076_);
lean_dec(v_stx_4073_);
v_a_4127_ = lean_ctor_get(v___x_4126_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4129_ = v___x_4126_;
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_a_4127_);
lean_dec(v___x_4126_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v___x_4132_; 
if (v_isShared_4130_ == 0)
{
v___x_4132_ = v___x_4129_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_a_4127_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
}
}
}
v___jp_4099_:
{
size_t v_sz_4102_; size_t v___x_4103_; lean_object* v___x_4104_; 
v_sz_4102_ = lean_array_size(v_a_4089_);
v___x_4103_ = ((size_t)0ULL);
lean_inc_ref(v___x_4076_);
lean_inc(v_a_4087_);
v___x_4104_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4087_, v___x_4076_, v___x_4077_, v_a_4089_, v_sz_4102_, v___x_4103_, v___x_4098_, v___y_4100_, v___y_4101_);
lean_dec(v_a_4089_);
if (lean_obj_tag(v___x_4104_) == 0)
{
lean_object* v___x_4105_; size_t v___x_4106_; size_t v___x_4107_; lean_object* v___x_4108_; 
lean_dec_ref_known(v___x_4104_, 1);
v___x_4105_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_4106_ = ((size_t)1ULL);
v___x_4107_ = lean_usize_add(v_i_4080_, v___x_4106_);
v___x_4108_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4073_, v___x_4074_, v___x_4075_, v___x_4076_, v___x_4077_, v_as_4078_, v_sz_4079_, v___x_4107_, v___x_4105_, v___y_4082_, v___y_4083_);
return v___x_4108_;
}
else
{
lean_object* v_a_4109_; lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4116_; 
lean_dec_ref(v___x_4076_);
lean_dec(v_stx_4073_);
v_a_4109_ = lean_ctor_get(v___x_4104_, 0);
v_isSharedCheck_4116_ = !lean_is_exclusive(v___x_4104_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4111_ = v___x_4104_;
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
else
{
lean_inc(v_a_4109_);
lean_dec(v___x_4104_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v___x_4114_; 
if (v_isShared_4112_ == 0)
{
v___x_4114_ = v___x_4111_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v_a_4109_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
return v___x_4114_;
}
}
}
}
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4142_; 
lean_dec_ref(v___x_4076_);
lean_dec(v_stx_4073_);
v_a_4135_ = lean_ctor_get(v___x_4088_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4088_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4137_ = v___x_4088_;
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4088_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4140_; 
if (v_isShared_4138_ == 0)
{
v___x_4140_ = v___x_4137_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_a_4135_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4___boxed(lean_object* v_stx_4143_, lean_object* v___x_4144_, lean_object* v___x_4145_, lean_object* v___x_4146_, lean_object* v___x_4147_, lean_object* v_as_4148_, lean_object* v_sz_4149_, lean_object* v_i_4150_, lean_object* v_b_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_){
_start:
{
size_t v_sz_boxed_4155_; size_t v_i_boxed_4156_; lean_object* v_res_4157_; 
v_sz_boxed_4155_ = lean_unbox_usize(v_sz_4149_);
lean_dec(v_sz_4149_);
v_i_boxed_4156_ = lean_unbox_usize(v_i_4150_);
lean_dec(v_i_4150_);
v_res_4157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(v_stx_4143_, v___x_4144_, v___x_4145_, v___x_4146_, v___x_4147_, v_as_4148_, v_sz_boxed_4155_, v_i_boxed_4156_, v_b_4151_, v___y_4152_, v___y_4153_);
lean_dec(v___y_4153_);
lean_dec_ref(v___y_4152_);
lean_dec_ref(v_as_4148_);
lean_dec(v___x_4147_);
lean_dec_ref(v___x_4145_);
lean_dec_ref(v___x_4144_);
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(lean_object* v_init_4158_, lean_object* v_stx_4159_, lean_object* v___x_4160_, lean_object* v___x_4161_, lean_object* v___x_4162_, lean_object* v___x_4163_, lean_object* v_n_4164_, lean_object* v_b_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_){
_start:
{
if (lean_obj_tag(v_n_4164_) == 0)
{
lean_object* v_cs_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; size_t v_sz_4172_; size_t v___x_4173_; lean_object* v___x_4174_; 
v_cs_4169_ = lean_ctor_get(v_n_4164_, 0);
v___x_4170_ = lean_box(0);
v___x_4171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4170_);
lean_ctor_set(v___x_4171_, 1, v_b_4165_);
v_sz_4172_ = lean_array_size(v_cs_4169_);
v___x_4173_ = ((size_t)0ULL);
v___x_4174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(v_init_4158_, v_stx_4159_, v___x_4160_, v___x_4161_, v___x_4162_, v___x_4163_, v_cs_4169_, v_sz_4172_, v___x_4173_, v___x_4171_, v___y_4166_, v___y_4167_);
if (lean_obj_tag(v___x_4174_) == 0)
{
lean_object* v_a_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4189_; 
v_a_4175_ = lean_ctor_get(v___x_4174_, 0);
v_isSharedCheck_4189_ = !lean_is_exclusive(v___x_4174_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4177_ = v___x_4174_;
v_isShared_4178_ = v_isSharedCheck_4189_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_a_4175_);
lean_dec(v___x_4174_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4189_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v_fst_4179_; 
v_fst_4179_ = lean_ctor_get(v_a_4175_, 0);
if (lean_obj_tag(v_fst_4179_) == 0)
{
lean_object* v_snd_4180_; lean_object* v___x_4181_; lean_object* v___x_4183_; 
v_snd_4180_ = lean_ctor_get(v_a_4175_, 1);
lean_inc(v_snd_4180_);
lean_dec(v_a_4175_);
v___x_4181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4181_, 0, v_snd_4180_);
if (v_isShared_4178_ == 0)
{
lean_ctor_set(v___x_4177_, 0, v___x_4181_);
v___x_4183_ = v___x_4177_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4184_, 0, v___x_4181_);
v___x_4183_ = v_reuseFailAlloc_4184_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
return v___x_4183_;
}
}
else
{
lean_object* v_val_4185_; lean_object* v___x_4187_; 
lean_inc_ref(v_fst_4179_);
lean_dec(v_a_4175_);
v_val_4185_ = lean_ctor_get(v_fst_4179_, 0);
lean_inc(v_val_4185_);
lean_dec_ref_known(v_fst_4179_, 1);
if (v_isShared_4178_ == 0)
{
lean_ctor_set(v___x_4177_, 0, v_val_4185_);
v___x_4187_ = v___x_4177_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_val_4185_);
v___x_4187_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
return v___x_4187_;
}
}
}
}
else
{
lean_object* v_a_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4197_; 
v_a_4190_ = lean_ctor_get(v___x_4174_, 0);
v_isSharedCheck_4197_ = !lean_is_exclusive(v___x_4174_);
if (v_isSharedCheck_4197_ == 0)
{
v___x_4192_ = v___x_4174_;
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_a_4190_);
lean_dec(v___x_4174_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v___x_4195_; 
if (v_isShared_4193_ == 0)
{
v___x_4195_ = v___x_4192_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v_a_4190_);
v___x_4195_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
return v___x_4195_;
}
}
}
}
else
{
lean_object* v_vs_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; size_t v_sz_4201_; size_t v___x_4202_; lean_object* v___x_4203_; 
v_vs_4198_ = lean_ctor_get(v_n_4164_, 0);
v___x_4199_ = lean_box(0);
v___x_4200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4200_, 0, v___x_4199_);
lean_ctor_set(v___x_4200_, 1, v_b_4165_);
v_sz_4201_ = lean_array_size(v_vs_4198_);
v___x_4202_ = ((size_t)0ULL);
v___x_4203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(v_stx_4159_, v___x_4160_, v___x_4161_, v___x_4162_, v___x_4163_, v_vs_4198_, v_sz_4201_, v___x_4202_, v___x_4200_, v___y_4166_, v___y_4167_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v_a_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4218_; 
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4206_ = v___x_4203_;
v_isShared_4207_ = v_isSharedCheck_4218_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_a_4204_);
lean_dec(v___x_4203_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4218_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v_fst_4208_; 
v_fst_4208_ = lean_ctor_get(v_a_4204_, 0);
if (lean_obj_tag(v_fst_4208_) == 0)
{
lean_object* v_snd_4209_; lean_object* v___x_4210_; lean_object* v___x_4212_; 
v_snd_4209_ = lean_ctor_get(v_a_4204_, 1);
lean_inc(v_snd_4209_);
lean_dec(v_a_4204_);
v___x_4210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4210_, 0, v_snd_4209_);
if (v_isShared_4207_ == 0)
{
lean_ctor_set(v___x_4206_, 0, v___x_4210_);
v___x_4212_ = v___x_4206_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v___x_4210_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
else
{
lean_object* v_val_4214_; lean_object* v___x_4216_; 
lean_inc_ref(v_fst_4208_);
lean_dec(v_a_4204_);
v_val_4214_ = lean_ctor_get(v_fst_4208_, 0);
lean_inc(v_val_4214_);
lean_dec_ref_known(v_fst_4208_, 1);
if (v_isShared_4207_ == 0)
{
lean_ctor_set(v___x_4206_, 0, v_val_4214_);
v___x_4216_ = v___x_4206_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_val_4214_);
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
lean_object* v_a_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4226_; 
v_a_4219_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4221_ = v___x_4203_;
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_a_4219_);
lean_dec(v___x_4203_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___x_4224_; 
if (v_isShared_4222_ == 0)
{
v___x_4224_ = v___x_4221_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_a_4219_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(lean_object* v_init_4227_, lean_object* v_stx_4228_, lean_object* v___x_4229_, lean_object* v___x_4230_, lean_object* v___x_4231_, lean_object* v___x_4232_, lean_object* v_as_4233_, size_t v_sz_4234_, size_t v_i_4235_, lean_object* v_b_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_){
_start:
{
uint8_t v___x_4240_; 
v___x_4240_ = lean_usize_dec_lt(v_i_4235_, v_sz_4234_);
if (v___x_4240_ == 0)
{
lean_object* v___x_4241_; 
lean_dec_ref(v___x_4231_);
lean_dec(v_stx_4228_);
v___x_4241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4241_, 0, v_b_4236_);
return v___x_4241_;
}
else
{
lean_object* v_snd_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4276_; 
v_snd_4242_ = lean_ctor_get(v_b_4236_, 1);
v_isSharedCheck_4276_ = !lean_is_exclusive(v_b_4236_);
if (v_isSharedCheck_4276_ == 0)
{
lean_object* v_unused_4277_; 
v_unused_4277_ = lean_ctor_get(v_b_4236_, 0);
lean_dec(v_unused_4277_);
v___x_4244_ = v_b_4236_;
v_isShared_4245_ = v_isSharedCheck_4276_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_snd_4242_);
lean_dec(v_b_4236_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4276_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v_a_4246_; lean_object* v___x_4247_; 
v_a_4246_ = lean_array_uget_borrowed(v_as_4233_, v_i_4235_);
lean_inc(v_snd_4242_);
lean_inc_ref(v___x_4231_);
lean_inc(v_stx_4228_);
v___x_4247_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4227_, v_stx_4228_, v___x_4229_, v___x_4230_, v___x_4231_, v___x_4232_, v_a_4246_, v_snd_4242_, v___y_4237_, v___y_4238_);
if (lean_obj_tag(v___x_4247_) == 0)
{
lean_object* v_a_4248_; lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4267_; 
v_a_4248_ = lean_ctor_get(v___x_4247_, 0);
v_isSharedCheck_4267_ = !lean_is_exclusive(v___x_4247_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4250_ = v___x_4247_;
v_isShared_4251_ = v_isSharedCheck_4267_;
goto v_resetjp_4249_;
}
else
{
lean_inc(v_a_4248_);
lean_dec(v___x_4247_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4267_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
if (lean_obj_tag(v_a_4248_) == 0)
{
lean_object* v___x_4252_; lean_object* v___x_4254_; 
lean_dec_ref(v___x_4231_);
lean_dec(v_stx_4228_);
v___x_4252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4252_, 0, v_a_4248_);
if (v_isShared_4245_ == 0)
{
lean_ctor_set(v___x_4244_, 0, v___x_4252_);
v___x_4254_ = v___x_4244_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v___x_4252_);
lean_ctor_set(v_reuseFailAlloc_4258_, 1, v_snd_4242_);
v___x_4254_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
lean_object* v___x_4256_; 
if (v_isShared_4251_ == 0)
{
lean_ctor_set(v___x_4250_, 0, v___x_4254_);
v___x_4256_ = v___x_4250_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v___x_4254_);
v___x_4256_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
return v___x_4256_;
}
}
}
else
{
lean_object* v_a_4259_; lean_object* v___x_4260_; lean_object* v___x_4262_; 
lean_del_object(v___x_4250_);
lean_dec(v_snd_4242_);
v_a_4259_ = lean_ctor_get(v_a_4248_, 0);
lean_inc(v_a_4259_);
lean_dec_ref_known(v_a_4248_, 1);
v___x_4260_ = lean_box(0);
if (v_isShared_4245_ == 0)
{
lean_ctor_set(v___x_4244_, 1, v_a_4259_);
lean_ctor_set(v___x_4244_, 0, v___x_4260_);
v___x_4262_ = v___x_4244_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v___x_4260_);
lean_ctor_set(v_reuseFailAlloc_4266_, 1, v_a_4259_);
v___x_4262_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
size_t v___x_4263_; size_t v___x_4264_; 
v___x_4263_ = ((size_t)1ULL);
v___x_4264_ = lean_usize_add(v_i_4235_, v___x_4263_);
v_i_4235_ = v___x_4264_;
v_b_4236_ = v___x_4262_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4268_; lean_object* v___x_4270_; uint8_t v_isShared_4271_; uint8_t v_isSharedCheck_4275_; 
lean_del_object(v___x_4244_);
lean_dec(v_snd_4242_);
lean_dec_ref(v___x_4231_);
lean_dec(v_stx_4228_);
v_a_4268_ = lean_ctor_get(v___x_4247_, 0);
v_isSharedCheck_4275_ = !lean_is_exclusive(v___x_4247_);
if (v_isSharedCheck_4275_ == 0)
{
v___x_4270_ = v___x_4247_;
v_isShared_4271_ = v_isSharedCheck_4275_;
goto v_resetjp_4269_;
}
else
{
lean_inc(v_a_4268_);
lean_dec(v___x_4247_);
v___x_4270_ = lean_box(0);
v_isShared_4271_ = v_isSharedCheck_4275_;
goto v_resetjp_4269_;
}
v_resetjp_4269_:
{
lean_object* v___x_4273_; 
if (v_isShared_4271_ == 0)
{
v___x_4273_ = v___x_4270_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v_a_4268_);
v___x_4273_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
return v___x_4273_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3___boxed(lean_object* v_init_4278_, lean_object* v_stx_4279_, lean_object* v___x_4280_, lean_object* v___x_4281_, lean_object* v___x_4282_, lean_object* v___x_4283_, lean_object* v_as_4284_, lean_object* v_sz_4285_, lean_object* v_i_4286_, lean_object* v_b_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_){
_start:
{
size_t v_sz_boxed_4291_; size_t v_i_boxed_4292_; lean_object* v_res_4293_; 
v_sz_boxed_4291_ = lean_unbox_usize(v_sz_4285_);
lean_dec(v_sz_4285_);
v_i_boxed_4292_ = lean_unbox_usize(v_i_4286_);
lean_dec(v_i_4286_);
v_res_4293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(v_init_4278_, v_stx_4279_, v___x_4280_, v___x_4281_, v___x_4282_, v___x_4283_, v_as_4284_, v_sz_boxed_4291_, v_i_boxed_4292_, v_b_4287_, v___y_4288_, v___y_4289_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
lean_dec_ref(v_as_4284_);
lean_dec(v___x_4283_);
lean_dec_ref(v___x_4281_);
lean_dec_ref(v___x_4280_);
return v_res_4293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2___boxed(lean_object* v_init_4294_, lean_object* v_stx_4295_, lean_object* v___x_4296_, lean_object* v___x_4297_, lean_object* v___x_4298_, lean_object* v___x_4299_, lean_object* v_n_4300_, lean_object* v_b_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_){
_start:
{
lean_object* v_res_4305_; 
v_res_4305_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4294_, v_stx_4295_, v___x_4296_, v___x_4297_, v___x_4298_, v___x_4299_, v_n_4300_, v_b_4301_, v___y_4302_, v___y_4303_);
lean_dec(v___y_4303_);
lean_dec_ref(v___y_4302_);
lean_dec_ref(v_n_4300_);
lean_dec(v___x_4299_);
lean_dec_ref(v___x_4297_);
lean_dec_ref(v___x_4296_);
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(lean_object* v___x_4306_, lean_object* v___x_4307_, lean_object* v_stx_4308_, lean_object* v___x_4309_, lean_object* v___x_4310_, lean_object* v_t_4311_, lean_object* v_init_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_){
_start:
{
lean_object* v_root_4316_; lean_object* v_tail_4317_; lean_object* v___x_4318_; 
v_root_4316_ = lean_ctor_get(v_t_4311_, 0);
v_tail_4317_ = lean_ctor_get(v_t_4311_, 1);
lean_inc_ref(v___x_4306_);
lean_inc(v_stx_4308_);
v___x_4318_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4312_, v_stx_4308_, v___x_4309_, v___x_4310_, v___x_4306_, v___x_4307_, v_root_4316_, v_init_4312_, v___y_4313_, v___y_4314_);
if (lean_obj_tag(v___x_4318_) == 0)
{
lean_object* v_a_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4355_; 
v_a_4319_ = lean_ctor_get(v___x_4318_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4318_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4321_ = v___x_4318_;
v_isShared_4322_ = v_isSharedCheck_4355_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_a_4319_);
lean_dec(v___x_4318_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4355_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
if (lean_obj_tag(v_a_4319_) == 0)
{
lean_object* v_a_4323_; lean_object* v___x_4325_; 
lean_dec(v_stx_4308_);
lean_dec_ref(v___x_4306_);
v_a_4323_ = lean_ctor_get(v_a_4319_, 0);
lean_inc(v_a_4323_);
lean_dec_ref_known(v_a_4319_, 1);
if (v_isShared_4322_ == 0)
{
lean_ctor_set(v___x_4321_, 0, v_a_4323_);
v___x_4325_ = v___x_4321_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_a_4323_);
v___x_4325_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
return v___x_4325_;
}
}
else
{
lean_object* v_a_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; size_t v_sz_4330_; size_t v___x_4331_; lean_object* v___x_4332_; 
lean_del_object(v___x_4321_);
v_a_4327_ = lean_ctor_get(v_a_4319_, 0);
lean_inc(v_a_4327_);
lean_dec_ref_known(v_a_4319_, 1);
v___x_4328_ = lean_box(0);
v___x_4329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4329_, 0, v___x_4328_);
lean_ctor_set(v___x_4329_, 1, v_a_4327_);
v_sz_4330_ = lean_array_size(v_tail_4317_);
v___x_4331_ = ((size_t)0ULL);
v___x_4332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(v_stx_4308_, v___x_4309_, v___x_4310_, v___x_4306_, v___x_4307_, v_tail_4317_, v_sz_4330_, v___x_4331_, v___x_4329_, v___y_4313_, v___y_4314_);
if (lean_obj_tag(v___x_4332_) == 0)
{
lean_object* v_a_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4346_; 
v_a_4333_ = lean_ctor_get(v___x_4332_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4332_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4335_ = v___x_4332_;
v_isShared_4336_ = v_isSharedCheck_4346_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_a_4333_);
lean_dec(v___x_4332_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4346_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
lean_object* v_fst_4337_; 
v_fst_4337_ = lean_ctor_get(v_a_4333_, 0);
if (lean_obj_tag(v_fst_4337_) == 0)
{
lean_object* v_snd_4338_; lean_object* v___x_4340_; 
v_snd_4338_ = lean_ctor_get(v_a_4333_, 1);
lean_inc(v_snd_4338_);
lean_dec(v_a_4333_);
if (v_isShared_4336_ == 0)
{
lean_ctor_set(v___x_4335_, 0, v_snd_4338_);
v___x_4340_ = v___x_4335_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_snd_4338_);
v___x_4340_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
return v___x_4340_;
}
}
else
{
lean_object* v_val_4342_; lean_object* v___x_4344_; 
lean_inc_ref(v_fst_4337_);
lean_dec(v_a_4333_);
v_val_4342_ = lean_ctor_get(v_fst_4337_, 0);
lean_inc(v_val_4342_);
lean_dec_ref_known(v_fst_4337_, 1);
if (v_isShared_4336_ == 0)
{
lean_ctor_set(v___x_4335_, 0, v_val_4342_);
v___x_4344_ = v___x_4335_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_val_4342_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
}
}
else
{
lean_object* v_a_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4354_; 
v_a_4347_ = lean_ctor_get(v___x_4332_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4332_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4349_ = v___x_4332_;
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_a_4347_);
lean_dec(v___x_4332_);
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
}
else
{
lean_object* v_a_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4363_; 
lean_dec(v_stx_4308_);
lean_dec_ref(v___x_4306_);
v_a_4356_ = lean_ctor_get(v___x_4318_, 0);
v_isSharedCheck_4363_ = !lean_is_exclusive(v___x_4318_);
if (v_isSharedCheck_4363_ == 0)
{
v___x_4358_ = v___x_4318_;
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_a_4356_);
lean_dec(v___x_4318_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v___x_4361_; 
if (v_isShared_4359_ == 0)
{
v___x_4361_ = v___x_4358_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v_a_4356_);
v___x_4361_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
return v___x_4361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2___boxed(lean_object* v___x_4364_, lean_object* v___x_4365_, lean_object* v_stx_4366_, lean_object* v___x_4367_, lean_object* v___x_4368_, lean_object* v_t_4369_, lean_object* v_init_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_){
_start:
{
lean_object* v_res_4374_; 
v_res_4374_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___x_4364_, v___x_4365_, v_stx_4366_, v___x_4367_, v___x_4368_, v_t_4369_, v_init_4370_, v___y_4371_, v___y_4372_);
lean_dec(v___y_4372_);
lean_dec_ref(v___y_4371_);
lean_dec_ref(v_t_4369_);
lean_dec_ref(v___x_4368_);
lean_dec_ref(v___x_4367_);
lean_dec(v___x_4365_);
return v_res_4374_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4376_; lean_object* v___x_4377_; 
v___x_4376_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__0));
v___x_4377_ = l_Lean_stringToMessageData(v___x_4376_);
return v___x_4377_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4381_; lean_object* v___x_4382_; 
v___x_4381_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__4));
v___x_4382_ = l_Lean_stringToMessageData(v___x_4381_);
return v___x_4382_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4384_; lean_object* v___x_4385_; 
v___x_4384_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__6));
v___x_4385_ = l_Lean_stringToMessageData(v___x_4384_);
return v___x_4385_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9(void){
_start:
{
lean_object* v___x_4387_; lean_object* v___x_4388_; 
v___x_4387_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__8));
v___x_4388_ = l_Lean_stringToMessageData(v___x_4387_);
return v___x_4388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(lean_object* v_stx_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_){
_start:
{
lean_object* v___x_4396_; lean_object* v_scopes_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v_opts_4400_; lean_object* v___y_4402_; lean_object* v___y_4403_; lean_object* v___y_4404_; lean_object* v___y_4405_; uint8_t v___y_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4432_; uint8_t v___y_4433_; lean_object* v___y_4434_; lean_object* v___y_4435_; lean_object* v___y_4441_; uint8_t v___y_4442_; lean_object* v___y_4443_; uint8_t v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4454_; uint8_t v___y_4455_; lean_object* v___y_4456_; uint8_t v___y_4457_; uint8_t v___y_4458_; lean_object* v___y_4459_; uint8_t v___y_4468_; uint8_t v___y_4469_; uint8_t v___y_4470_; uint8_t v___y_4504_; lean_object* v___x_4511_; uint8_t v___x_4512_; 
v___x_4396_ = lean_st_ref_get(v___y_4391_);
v_scopes_4397_ = lean_ctor_get(v___x_4396_, 2);
lean_inc(v_scopes_4397_);
lean_dec(v___x_4396_);
v___x_4398_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4399_ = l_List_head_x21___redArg(v___x_4398_, v_scopes_4397_);
lean_dec(v_scopes_4397_);
v_opts_4400_ = lean_ctor_get(v___x_4399_, 1);
lean_inc_ref(v_opts_4400_);
lean_dec(v___x_4399_);
v___x_4511_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_4512_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4400_, v___x_4511_);
if (v___x_4512_ == 0)
{
lean_object* v___x_4513_; uint8_t v___x_4514_; 
v___x_4513_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_4514_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4400_, v___x_4513_);
v___y_4504_ = v___x_4514_;
goto v___jp_4503_;
}
else
{
v___y_4504_ = v___x_4512_;
goto v___jp_4503_;
}
v___jp_4393_:
{
lean_object* v___x_4394_; lean_object* v___x_4395_; 
v___x_4394_ = lean_box(0);
v___x_4395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4394_);
return v___x_4395_;
}
v___jp_4401_:
{
lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v_a_4408_; lean_object* v___x_4409_; lean_object* v_line_4410_; lean_object* v_messages_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
v___x_4406_ = lean_st_ref_get(v___y_4403_);
v___x_4407_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_4403_);
v_a_4408_ = lean_ctor_get(v___x_4407_, 0);
lean_inc(v_a_4408_);
lean_dec_ref(v___x_4407_);
lean_inc_ref_n(v___y_4404_, 2);
v___x_4409_ = l_Lean_FileMap_toPosition(v___y_4404_, v___y_4405_);
lean_dec(v___y_4405_);
v_line_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_line_4410_);
lean_dec_ref(v___x_4409_);
v_messages_4411_ = lean_ctor_get(v___x_4406_, 1);
lean_inc_ref(v_messages_4411_);
lean_dec(v___x_4406_);
v___x_4412_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_4411_);
v___x_4413_ = lean_box(0);
v___x_4414_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___y_4404_, v_line_4410_, v_stx_4389_, v_opts_4400_, v___x_4412_, v_a_4408_, v___x_4413_, v___y_4402_, v___y_4403_);
lean_dec(v_a_4408_);
lean_dec_ref(v___x_4412_);
lean_dec_ref(v_opts_4400_);
lean_dec(v_line_4410_);
if (lean_obj_tag(v___x_4414_) == 0)
{
lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4421_; 
v_isSharedCheck_4421_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4421_ == 0)
{
lean_object* v_unused_4422_; 
v_unused_4422_ = lean_ctor_get(v___x_4414_, 0);
lean_dec(v_unused_4422_);
v___x_4416_ = v___x_4414_;
v_isShared_4417_ = v_isSharedCheck_4421_;
goto v_resetjp_4415_;
}
else
{
lean_dec(v___x_4414_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4421_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
lean_object* v___x_4419_; 
if (v_isShared_4417_ == 0)
{
lean_ctor_set(v___x_4416_, 0, v___x_4413_);
v___x_4419_ = v___x_4416_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v___x_4413_);
v___x_4419_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
return v___x_4419_;
}
}
}
else
{
return v___x_4414_;
}
}
v___jp_4423_:
{
lean_object* v_fileMap_4427_; lean_object* v___x_4428_; 
v_fileMap_4427_ = lean_ctor_get(v___y_4425_, 1);
v___x_4428_ = l_Lean_Syntax_getPos_x3f(v_stx_4389_, v___y_4424_);
if (lean_obj_tag(v___x_4428_) == 0)
{
lean_object* v___x_4429_; 
v___x_4429_ = lean_unsigned_to_nat(0u);
v___y_4402_ = v___y_4425_;
v___y_4403_ = v___y_4426_;
v___y_4404_ = v_fileMap_4427_;
v___y_4405_ = v___x_4429_;
goto v___jp_4401_;
}
else
{
lean_object* v_val_4430_; 
v_val_4430_ = lean_ctor_get(v___x_4428_, 0);
lean_inc(v_val_4430_);
lean_dec_ref_known(v___x_4428_, 1);
v___y_4402_ = v___y_4425_;
v___y_4403_ = v___y_4426_;
v___y_4404_ = v_fileMap_4427_;
v___y_4405_ = v_val_4430_;
goto v___jp_4401_;
}
}
v___jp_4431_:
{
lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; 
lean_inc_ref(v___y_4435_);
v___x_4436_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4436_, 0, v___y_4435_);
v___x_4437_ = l_Lean_MessageData_ofFormat(v___x_4436_);
v___x_4438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4438_, 0, v___y_4434_);
lean_ctor_set(v___x_4438_, 1, v___x_4437_);
lean_inc(v___y_4432_);
v___x_4439_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___y_4432_, v___x_4438_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4439_) == 0)
{
lean_dec_ref_known(v___x_4439_, 1);
v___y_4424_ = v___y_4433_;
v___y_4425_ = v___y_4390_;
v___y_4426_ = v___y_4391_;
goto v___jp_4423_;
}
else
{
lean_dec_ref(v_opts_4400_);
lean_dec(v_stx_4389_);
return v___x_4439_;
}
}
v___jp_4440_:
{
lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; 
lean_inc_ref(v___y_4445_);
v___x_4446_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4446_, 0, v___y_4445_);
v___x_4447_ = l_Lean_MessageData_ofFormat(v___x_4446_);
v___x_4448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4448_, 0, v___y_4443_);
lean_ctor_set(v___x_4448_, 1, v___x_4447_);
v___x_4449_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1);
v___x_4450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4450_, 0, v___x_4448_);
lean_ctor_set(v___x_4450_, 1, v___x_4449_);
if (v___y_4444_ == 0)
{
lean_object* v___x_4451_; 
v___x_4451_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4432_ = v___y_4441_;
v___y_4433_ = v___y_4442_;
v___y_4434_ = v___x_4450_;
v___y_4435_ = v___x_4451_;
goto v___jp_4431_;
}
else
{
lean_object* v___x_4452_; 
v___x_4452_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4432_ = v___y_4441_;
v___y_4433_ = v___y_4442_;
v___y_4434_ = v___x_4450_;
v___y_4435_ = v___x_4452_;
goto v___jp_4431_;
}
}
v___jp_4453_:
{
lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; 
lean_inc_ref(v___y_4459_);
v___x_4460_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4460_, 0, v___y_4459_);
v___x_4461_ = l_Lean_MessageData_ofFormat(v___x_4460_);
lean_inc_ref(v___y_4456_);
v___x_4462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4462_, 0, v___y_4456_);
lean_ctor_set(v___x_4462_, 1, v___x_4461_);
v___x_4463_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5);
v___x_4464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4464_, 0, v___x_4462_);
lean_ctor_set(v___x_4464_, 1, v___x_4463_);
if (v___y_4457_ == 0)
{
lean_object* v___x_4465_; 
v___x_4465_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4441_ = v___y_4454_;
v___y_4442_ = v___y_4455_;
v___y_4443_ = v___x_4464_;
v___y_4444_ = v___y_4458_;
v___y_4445_ = v___x_4465_;
goto v___jp_4440_;
}
else
{
lean_object* v___x_4466_; 
v___x_4466_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4441_ = v___y_4454_;
v___y_4442_ = v___y_4455_;
v___y_4443_ = v___x_4464_;
v___y_4444_ = v___y_4458_;
v___y_4445_ = v___x_4466_;
goto v___jp_4440_;
}
}
v___jp_4467_:
{
lean_object* v___x_4471_; lean_object* v_a_4472_; uint8_t v___x_4473_; 
v___x_4471_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(v_stx_4389_, v___y_4390_, v___y_4391_);
v_a_4472_ = lean_ctor_get(v___x_4471_, 0);
lean_inc(v_a_4472_);
lean_dec_ref(v___x_4471_);
v___x_4473_ = lean_unbox(v_a_4472_);
if (v___x_4473_ == 0)
{
lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v_scopes_4477_; lean_object* v___x_4478_; lean_object* v_opts_4479_; uint8_t v_hasTrace_4480_; 
v___x_4474_ = l_Lean_inheritedTraceOptions;
v___x_4475_ = lean_st_ref_get(v___x_4474_);
v___x_4476_ = lean_st_ref_get(v___y_4391_);
v_scopes_4477_ = lean_ctor_get(v___x_4476_, 2);
lean_inc(v_scopes_4477_);
lean_dec(v___x_4476_);
v___x_4478_ = l_List_head_x21___redArg(v___x_4398_, v_scopes_4477_);
lean_dec(v_scopes_4477_);
v_opts_4479_ = lean_ctor_get(v___x_4478_, 1);
lean_inc_ref(v_opts_4479_);
lean_dec(v___x_4478_);
v_hasTrace_4480_ = lean_ctor_get_uint8(v_opts_4479_, sizeof(void*)*1);
if (v_hasTrace_4480_ == 0)
{
uint8_t v___x_4481_; 
lean_dec_ref(v_opts_4479_);
lean_dec(v___x_4475_);
v___x_4481_ = lean_unbox(v_a_4472_);
lean_dec(v_a_4472_);
v___y_4424_ = v___x_4481_;
v___y_4425_ = v___y_4390_;
v___y_4426_ = v___y_4391_;
goto v___jp_4423_;
}
else
{
lean_object* v___x_4482_; lean_object* v___x_4483_; uint8_t v___x_4484_; 
v___x_4482_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4483_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_4484_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4475_, v_opts_4479_, v___x_4483_);
lean_dec_ref(v_opts_4479_);
lean_dec(v___x_4475_);
if (v___x_4484_ == 0)
{
uint8_t v___x_4485_; 
v___x_4485_ = lean_unbox(v_a_4472_);
lean_dec(v_a_4472_);
v___y_4424_ = v___x_4485_;
v___y_4425_ = v___y_4390_;
v___y_4426_ = v___y_4391_;
goto v___jp_4423_;
}
else
{
lean_object* v___x_4486_; 
v___x_4486_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7);
if (v___y_4468_ == 0)
{
lean_object* v___x_4487_; uint8_t v___x_4488_; 
v___x_4487_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___x_4488_ = lean_unbox(v_a_4472_);
lean_dec(v_a_4472_);
v___y_4454_ = v___x_4482_;
v___y_4455_ = v___x_4488_;
v___y_4456_ = v___x_4486_;
v___y_4457_ = v___y_4469_;
v___y_4458_ = v___y_4470_;
v___y_4459_ = v___x_4487_;
goto v___jp_4453_;
}
else
{
lean_object* v___x_4489_; uint8_t v___x_4490_; 
v___x_4489_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___x_4490_ = lean_unbox(v_a_4472_);
lean_dec(v_a_4472_);
v___y_4454_ = v___x_4482_;
v___y_4455_ = v___x_4490_;
v___y_4456_ = v___x_4486_;
v___y_4457_ = v___y_4469_;
v___y_4458_ = v___y_4470_;
v___y_4459_ = v___x_4489_;
goto v___jp_4453_;
}
}
}
}
else
{
lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v_scopes_4494_; lean_object* v___x_4495_; lean_object* v_opts_4496_; uint8_t v_hasTrace_4497_; 
lean_dec(v_a_4472_);
lean_dec_ref(v_opts_4400_);
lean_dec(v_stx_4389_);
v___x_4491_ = l_Lean_inheritedTraceOptions;
v___x_4492_ = lean_st_ref_get(v___x_4491_);
v___x_4493_ = lean_st_ref_get(v___y_4391_);
v_scopes_4494_ = lean_ctor_get(v___x_4493_, 2);
lean_inc(v_scopes_4494_);
lean_dec(v___x_4493_);
v___x_4495_ = l_List_head_x21___redArg(v___x_4398_, v_scopes_4494_);
lean_dec(v_scopes_4494_);
v_opts_4496_ = lean_ctor_get(v___x_4495_, 1);
lean_inc_ref(v_opts_4496_);
lean_dec(v___x_4495_);
v_hasTrace_4497_ = lean_ctor_get_uint8(v_opts_4496_, sizeof(void*)*1);
if (v_hasTrace_4497_ == 0)
{
lean_dec_ref(v_opts_4496_);
lean_dec(v___x_4492_);
goto v___jp_4393_;
}
else
{
lean_object* v___x_4498_; lean_object* v___x_4499_; uint8_t v___x_4500_; 
v___x_4498_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4499_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_4500_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4492_, v_opts_4496_, v___x_4499_);
lean_dec_ref(v_opts_4496_);
lean_dec(v___x_4492_);
if (v___x_4500_ == 0)
{
goto v___jp_4393_;
}
else
{
lean_object* v___x_4501_; lean_object* v___x_4502_; 
v___x_4501_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9);
v___x_4502_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_4498_, v___x_4501_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4502_) == 0)
{
lean_dec_ref_known(v___x_4502_, 1);
goto v___jp_4393_;
}
else
{
return v___x_4502_;
}
}
}
}
}
v___jp_4503_:
{
lean_object* v___x_4505_; uint8_t v___x_4506_; lean_object* v___x_4507_; uint8_t v___x_4508_; 
v___x_4505_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
v___x_4506_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4400_, v___x_4505_);
v___x_4507_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v___x_4508_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4400_, v___x_4507_);
if (v___y_4504_ == 0)
{
if (v___x_4506_ == 0)
{
if (v___x_4508_ == 0)
{
lean_object* v___x_4509_; lean_object* v___x_4510_; 
lean_dec_ref(v_opts_4400_);
lean_dec(v_stx_4389_);
v___x_4509_ = lean_box(0);
v___x_4510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4509_);
return v___x_4510_;
}
else
{
v___y_4468_ = v___y_4504_;
v___y_4469_ = v___x_4506_;
v___y_4470_ = v___x_4508_;
goto v___jp_4467_;
}
}
else
{
v___y_4468_ = v___y_4504_;
v___y_4469_ = v___x_4506_;
v___y_4470_ = v___x_4508_;
goto v___jp_4467_;
}
}
else
{
v___y_4468_ = v___y_4504_;
v___y_4469_ = v___x_4506_;
v___y_4470_ = v___x_4508_;
goto v___jp_4467_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___boxed(lean_object* v_stx_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_){
_start:
{
lean_object* v_res_4519_; 
v_res_4519_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(v_stx_4515_, v___y_4516_, v___y_4517_);
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
return v_res_4519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4532_; lean_object* v___x_4533_; 
v___x_4532_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook));
v___x_4533_ = l_Lean_Elab_Command_addLinter(v___x_4532_);
return v___x_4533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2____boxed(lean_object* v_a_4534_){
_start:
{
lean_object* v_res_4535_; 
v_res_4535_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_();
return v_res_4535_;
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
