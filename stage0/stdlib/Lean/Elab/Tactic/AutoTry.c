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
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v_nbuckets_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1185_ = lean_array_get_size(v_data_1184_);
v___x_1186_ = lean_unsigned_to_nat(2u);
v_nbuckets_1187_ = lean_nat_mul(v___x_1185_, v___x_1186_);
v___x_1188_ = lean_unsigned_to_nat(0u);
v___x_1189_ = lean_box(0);
v___x_1190_ = lean_mk_array(v_nbuckets_1187_, v___x_1189_);
v___x_1191_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3___redArg(v___x_1188_, v_data_1184_, v___x_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(lean_object* v_m_1192_, lean_object* v_a_1193_, lean_object* v_b_1194_){
_start:
{
lean_object* v_size_1195_; lean_object* v_buckets_1196_; lean_object* v_fst_1197_; lean_object* v_snd_1198_; lean_object* v___x_1199_; uint64_t v___x_1200_; uint64_t v___x_1201_; uint64_t v___x_1202_; uint64_t v___x_1203_; uint64_t v___x_1204_; uint64_t v_fold_1205_; uint64_t v___x_1206_; uint64_t v___x_1207_; uint64_t v___x_1208_; size_t v___x_1209_; size_t v___x_1210_; size_t v___x_1211_; size_t v___x_1212_; size_t v___x_1213_; lean_object* v_bkt_1214_; uint8_t v___x_1215_; 
v_size_1195_ = lean_ctor_get(v_m_1192_, 0);
v_buckets_1196_ = lean_ctor_get(v_m_1192_, 1);
v_fst_1197_ = lean_ctor_get(v_a_1193_, 0);
v_snd_1198_ = lean_ctor_get(v_a_1193_, 1);
v___x_1199_ = lean_array_get_size(v_buckets_1196_);
v___x_1200_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1197_);
v___x_1201_ = l_Lean_instHashableMVarId_hash(v_snd_1198_);
v___x_1202_ = lean_uint64_mix_hash(v___x_1200_, v___x_1201_);
v___x_1203_ = 32ULL;
v___x_1204_ = lean_uint64_shift_right(v___x_1202_, v___x_1203_);
v_fold_1205_ = lean_uint64_xor(v___x_1202_, v___x_1204_);
v___x_1206_ = 16ULL;
v___x_1207_ = lean_uint64_shift_right(v_fold_1205_, v___x_1206_);
v___x_1208_ = lean_uint64_xor(v_fold_1205_, v___x_1207_);
v___x_1209_ = lean_uint64_to_usize(v___x_1208_);
v___x_1210_ = lean_usize_of_nat(v___x_1199_);
v___x_1211_ = ((size_t)1ULL);
v___x_1212_ = lean_usize_sub(v___x_1210_, v___x_1211_);
v___x_1213_ = lean_usize_land(v___x_1209_, v___x_1212_);
v_bkt_1214_ = lean_array_uget_borrowed(v_buckets_1196_, v___x_1213_);
v___x_1215_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(v_a_1193_, v_bkt_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1236_; 
lean_inc_ref(v_buckets_1196_);
lean_inc(v_size_1195_);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_m_1192_);
if (v_isSharedCheck_1236_ == 0)
{
lean_object* v_unused_1237_; lean_object* v_unused_1238_; 
v_unused_1237_ = lean_ctor_get(v_m_1192_, 1);
lean_dec(v_unused_1237_);
v_unused_1238_ = lean_ctor_get(v_m_1192_, 0);
lean_dec(v_unused_1238_);
v___x_1217_ = v_m_1192_;
v_isShared_1218_ = v_isSharedCheck_1236_;
goto v_resetjp_1216_;
}
else
{
lean_dec(v_m_1192_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1236_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v_size_x27_1220_; lean_object* v___x_1221_; lean_object* v_buckets_x27_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; uint8_t v___x_1228_; 
v___x_1219_ = lean_unsigned_to_nat(1u);
v_size_x27_1220_ = lean_nat_add(v_size_1195_, v___x_1219_);
lean_dec(v_size_1195_);
lean_inc(v_bkt_1214_);
v___x_1221_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1221_, 0, v_a_1193_);
lean_ctor_set(v___x_1221_, 1, v_b_1194_);
lean_ctor_set(v___x_1221_, 2, v_bkt_1214_);
v_buckets_x27_1222_ = lean_array_uset(v_buckets_1196_, v___x_1213_, v___x_1221_);
v___x_1223_ = lean_unsigned_to_nat(4u);
v___x_1224_ = lean_nat_mul(v_size_x27_1220_, v___x_1223_);
v___x_1225_ = lean_unsigned_to_nat(3u);
v___x_1226_ = lean_nat_div(v___x_1224_, v___x_1225_);
lean_dec(v___x_1224_);
v___x_1227_ = lean_array_get_size(v_buckets_x27_1222_);
v___x_1228_ = lean_nat_dec_le(v___x_1226_, v___x_1227_);
lean_dec(v___x_1226_);
if (v___x_1228_ == 0)
{
lean_object* v_val_1229_; lean_object* v___x_1231_; 
v_val_1229_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2___redArg(v_buckets_x27_1222_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 1, v_val_1229_);
lean_ctor_set(v___x_1217_, 0, v_size_x27_1220_);
v___x_1231_ = v___x_1217_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_size_x27_1220_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v_val_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
else
{
lean_object* v___x_1234_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 1, v_buckets_x27_1222_);
lean_ctor_set(v___x_1217_, 0, v_size_x27_1220_);
v___x_1234_ = v___x_1217_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_size_x27_1220_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_buckets_x27_1222_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
else
{
lean_dec(v_b_1194_);
lean_dec_ref(v_a_1193_);
return v_m_1192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(lean_object* v___x_1239_, lean_object* v_fst_1240_, lean_object* v_snd_1241_, lean_object* v___x_1242_, lean_object* v_as_1243_, size_t v_sz_1244_, size_t v_i_1245_, lean_object* v_b_1246_){
_start:
{
lean_object* v_a_1249_; uint8_t v___x_1253_; 
v___x_1253_ = lean_usize_dec_lt(v_i_1245_, v_sz_1244_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; 
lean_dec(v___x_1242_);
lean_dec(v_snd_1241_);
lean_dec(v_fst_1240_);
lean_dec_ref(v___x_1239_);
v___x_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1254_, 0, v_b_1246_);
return v___x_1254_;
}
else
{
lean_object* v_a_1255_; lean_object* v_snd_1256_; lean_object* v_fst_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1293_; 
v_a_1255_ = lean_array_uget(v_as_1243_, v_i_1245_);
v_snd_1256_ = lean_ctor_get(v_a_1255_, 1);
v_fst_1257_ = lean_ctor_get(v_a_1255_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_a_1255_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1259_ = v_a_1255_;
v_isShared_1260_ = v_isSharedCheck_1293_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_snd_1256_);
lean_inc(v_fst_1257_);
lean_dec(v_a_1255_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1293_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v_fst_1261_; lean_object* v_snd_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1292_; 
v_fst_1261_ = lean_ctor_get(v_snd_1256_, 0);
v_snd_1262_ = lean_ctor_get(v_snd_1256_, 1);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_snd_1256_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1264_ = v_snd_1256_;
v_isShared_1265_ = v_isSharedCheck_1292_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_snd_1262_);
lean_inc(v_fst_1261_);
lean_dec(v_snd_1256_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1292_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v_fst_1266_; lean_object* v_snd_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1291_; 
v_fst_1266_ = lean_ctor_get(v_b_1246_, 0);
v_snd_1267_ = lean_ctor_get(v_b_1246_, 1);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_b_1246_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1269_ = v_b_1246_;
v_isShared_1270_ = v_isSharedCheck_1291_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_snd_1267_);
lean_inc(v_fst_1266_);
lean_dec(v_b_1246_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1291_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
lean_inc(v_snd_1262_);
lean_inc_ref(v___x_1239_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 1, v_snd_1262_);
lean_ctor_set(v___x_1269_, 0, v___x_1239_);
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_snd_1262_);
v___x_1272_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
uint8_t v___x_1273_; 
v___x_1273_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(v_snd_1267_, v___x_1272_);
if (v___x_1273_ == 0)
{
lean_object* v_env_1274_; lean_object* v_mctx_1275_; lean_object* v_opts_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1280_; 
v_env_1274_ = lean_ctor_get(v_fst_1257_, 0);
lean_inc_ref(v_env_1274_);
v_mctx_1275_ = lean_ctor_get(v_fst_1257_, 1);
lean_inc_ref(v_mctx_1275_);
v_opts_1276_ = lean_ctor_get(v_fst_1257_, 3);
lean_inc_ref(v_opts_1276_);
lean_dec(v_fst_1257_);
v___x_1277_ = lean_box(0);
v___x_1278_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_snd_1267_, v___x_1272_, v___x_1277_);
lean_inc(v_snd_1241_);
lean_inc(v_fst_1240_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 1, v_snd_1241_);
lean_ctor_set(v___x_1259_, 0, v_fst_1240_);
v___x_1280_ = v___x_1259_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_fst_1240_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_snd_1241_);
v___x_1280_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1284_; 
lean_inc(v___x_1242_);
v___x_1281_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
lean_ctor_set(v___x_1281_, 1, v___x_1242_);
lean_ctor_set(v___x_1281_, 2, v_env_1274_);
lean_ctor_set(v___x_1281_, 3, v_mctx_1275_);
lean_ctor_set(v___x_1281_, 4, v_opts_1276_);
lean_ctor_set(v___x_1281_, 5, v_fst_1261_);
lean_ctor_set(v___x_1281_, 6, v_snd_1262_);
v___x_1282_ = lean_array_push(v_fst_1266_, v___x_1281_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 1, v___x_1278_);
lean_ctor_set(v___x_1264_, 0, v___x_1282_);
v___x_1284_ = v___x_1264_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1282_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v___x_1278_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
v_a_1249_ = v___x_1284_;
goto v___jp_1248_;
}
}
}
else
{
lean_object* v___x_1288_; 
lean_dec_ref(v___x_1272_);
lean_dec(v_snd_1262_);
lean_dec(v_fst_1261_);
lean_del_object(v___x_1259_);
lean_dec(v_fst_1257_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 1, v_snd_1267_);
lean_ctor_set(v___x_1264_, 0, v_fst_1266_);
v___x_1288_ = v___x_1264_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_fst_1266_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_snd_1267_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
v_a_1249_ = v___x_1288_;
goto v___jp_1248_;
}
}
}
}
}
}
}
v___jp_1248_:
{
size_t v___x_1250_; size_t v___x_1251_; 
v___x_1250_ = ((size_t)1ULL);
v___x_1251_ = lean_usize_add(v_i_1245_, v___x_1250_);
v_i_1245_ = v___x_1251_;
v_b_1246_ = v_a_1249_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg___boxed(lean_object* v___x_1294_, lean_object* v_fst_1295_, lean_object* v_snd_1296_, lean_object* v___x_1297_, lean_object* v_as_1298_, lean_object* v_sz_1299_, lean_object* v_i_1300_, lean_object* v_b_1301_, lean_object* v___y_1302_){
_start:
{
size_t v_sz_boxed_1303_; size_t v_i_boxed_1304_; lean_object* v_res_1305_; 
v_sz_boxed_1303_ = lean_unbox_usize(v_sz_1299_);
lean_dec(v_sz_1299_);
v_i_boxed_1304_ = lean_unbox_usize(v_i_1300_);
lean_dec(v_i_1300_);
v_res_1305_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1294_, v_fst_1295_, v_snd_1296_, v___x_1297_, v_as_1298_, v_sz_boxed_1303_, v_i_boxed_1304_, v_b_1301_);
lean_dec_ref(v_as_1298_);
return v_res_1305_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3(void){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1310_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1311_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__2));
v___x_1312_ = l_Lean_Name_append(v___x_1311_, v___x_1310_);
return v___x_1312_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__4));
v___x_1315_ = l_Lean_stringToMessageData(v___x_1314_);
return v___x_1315_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7(void){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__6));
v___x_1318_ = l_Lean_stringToMessageData(v___x_1317_);
return v___x_1318_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__8));
v___x_1321_ = l_Lean_stringToMessageData(v___x_1320_);
return v___x_1321_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11(void){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__10));
v___x_1324_ = l_Lean_stringToMessageData(v___x_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12(lean_object* v___x_1325_, lean_object* v_val_1326_, lean_object* v_cmd_1327_, uint8_t v_onUnsolved_1328_, uint8_t v___y_1329_, lean_object* v_as_1330_, size_t v_sz_1331_, size_t v_i_1332_, lean_object* v_b_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
uint8_t v___x_1337_; 
v___x_1337_ = lean_usize_dec_lt(v_i_1332_, v_sz_1331_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; 
lean_dec(v_cmd_1327_);
v___x_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1338_, 0, v_b_1333_);
return v___x_1338_;
}
else
{
lean_object* v_snd_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1487_; 
v_snd_1339_ = lean_ctor_get(v_b_1333_, 1);
v_isSharedCheck_1487_ = !lean_is_exclusive(v_b_1333_);
if (v_isSharedCheck_1487_ == 0)
{
lean_object* v_unused_1488_; 
v_unused_1488_ = lean_ctor_get(v_b_1333_, 0);
lean_dec(v_unused_1488_);
v___x_1341_ = v_b_1333_;
v_isShared_1342_ = v_isSharedCheck_1487_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_snd_1339_);
lean_dec(v_b_1333_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1487_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v_fst_1343_; lean_object* v_snd_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1486_; 
v_fst_1343_ = lean_ctor_get(v_snd_1339_, 0);
v_snd_1344_ = lean_ctor_get(v_snd_1339_, 1);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_snd_1339_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1346_ = v_snd_1339_;
v_isShared_1347_ = v_isSharedCheck_1486_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_snd_1344_);
lean_inc(v_fst_1343_);
lean_dec(v_snd_1339_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1486_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v_a_1348_; lean_object* v_pos_1349_; lean_object* v_endPos_1350_; uint8_t v_severity_1351_; lean_object* v_data_1352_; lean_object* v___x_1353_; lean_object* v_a_1355_; 
v_a_1348_ = lean_array_uget_borrowed(v_as_1330_, v_i_1332_);
v_pos_1349_ = lean_ctor_get(v_a_1348_, 1);
v_endPos_1350_ = lean_ctor_get(v_a_1348_, 2);
lean_inc(v_endPos_1350_);
v_severity_1351_ = lean_ctor_get_uint8(v_a_1348_, sizeof(void*)*5 + 1);
v_data_1352_ = lean_ctor_get(v_a_1348_, 4);
v___x_1353_ = lean_box(0);
if (v_severity_1351_ == 2)
{
lean_object* v___f_1368_; uint8_t v___x_1369_; 
v___f_1368_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
lean_inc(v_data_1352_);
v___x_1369_ = l_Lean_MessageData_hasTag(v___f_1368_, v_data_1352_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; 
lean_dec(v_endPos_1350_);
lean_del_object(v___x_1341_);
v___x_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1370_, 0, v_fst_1343_);
lean_ctor_set(v___x_1370_, 1, v_snd_1344_);
v_a_1355_ = v___x_1370_;
goto v___jp_1354_;
}
else
{
if (lean_obj_tag(v_endPos_1350_) == 1)
{
lean_object* v_val_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1483_; 
v_val_1371_ = lean_ctor_get(v_endPos_1350_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_endPos_1350_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1373_ = v_endPos_1350_;
v_isShared_1374_ = v_isSharedCheck_1483_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_val_1371_);
lean_dec(v_endPos_1350_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1483_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; uint8_t v___x_1379_; 
lean_inc_ref(v_pos_1349_);
v___x_1375_ = l_Lean_FileMap_ofPosition(v___x_1325_, v_pos_1349_);
v___x_1376_ = l_Lean_FileMap_ofPosition(v___x_1325_, v_val_1371_);
lean_inc(v___x_1376_);
lean_inc(v___x_1375_);
v___x_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1375_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
v___x_1378_ = 0;
v___x_1379_ = l_Lean_Syntax_Range_includes(v_val_1326_, v___x_1377_, v___x_1378_, v___x_1378_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; 
lean_dec_ref_known(v___x_1377_, 2);
lean_dec(v___x_1376_);
lean_dec(v___x_1375_);
lean_del_object(v___x_1373_);
lean_del_object(v___x_1341_);
v___x_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1380_, 0, v_fst_1343_);
lean_ctor_set(v___x_1380_, 1, v_snd_1344_);
v_a_1355_ = v___x_1380_;
goto v___jp_1354_;
}
else
{
lean_object* v___x_1381_; 
lean_inc(v_cmd_1327_);
lean_inc_ref(v___x_1377_);
v___x_1381_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1377_, v_cmd_1327_);
if (lean_obj_tag(v___x_1381_) == 1)
{
lean_object* v_val_1382_; lean_object* v_fst_1383_; lean_object* v_snd_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1447_; 
lean_dec(v___x_1376_);
lean_dec(v___x_1375_);
lean_del_object(v___x_1373_);
v_val_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_val_1382_);
lean_dec_ref_known(v___x_1381_, 1);
v_fst_1383_ = lean_ctor_get(v_val_1382_, 0);
v_snd_1384_ = lean_ctor_get(v_val_1382_, 1);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_val_1382_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1386_ = v_val_1382_;
v_isShared_1387_ = v_isSharedCheck_1447_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_snd_1384_);
lean_inc(v_fst_1383_);
lean_dec(v_val_1382_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1447_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; uint8_t v___y_1445_; lean_object* v___x_1446_; 
v___x_1446_ = l_Lean_Syntax_getPos_x3f(v_fst_1383_, v___x_1378_);
if (lean_obj_tag(v___x_1446_) == 0)
{
v___y_1445_ = v___x_1379_;
goto v___jp_1444_;
}
else
{
lean_dec_ref_known(v___x_1446_, 1);
v___y_1445_ = v___x_1378_;
goto v___jp_1444_;
}
v___jp_1388_:
{
lean_object* v___x_1394_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 1, v_snd_1344_);
lean_ctor_set(v___x_1386_, 0, v_fst_1343_);
v___x_1394_ = v___x_1386_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_fst_1343_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_snd_1344_);
v___x_1394_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
size_t v_sz_1395_; size_t v___x_1396_; lean_object* v___x_1397_; 
v_sz_1395_ = lean_array_size(v___y_1389_);
v___x_1396_ = ((size_t)0ULL);
v___x_1397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1377_, v_fst_1383_, v_snd_1384_, v___y_1390_, v___y_1389_, v_sz_1395_, v___x_1396_, v___x_1394_);
lean_dec_ref(v___y_1389_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v_fst_1399_; lean_object* v_snd_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
lean_dec_ref_known(v___x_1397_, 1);
v_fst_1399_ = lean_ctor_get(v_a_1398_, 0);
v_snd_1400_ = lean_ctor_get(v_a_1398_, 1);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_a_1398_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v_a_1398_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_snd_1400_);
lean_inc(v_fst_1399_);
lean_dec(v_a_1398_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_fst_1399_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_snd_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
v_a_1355_ = v___x_1405_;
goto v___jp_1354_;
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_del_object(v___x_1346_);
lean_dec(v_cmd_1327_);
v_a_1408_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1397_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1397_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
v___jp_1417_:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
lean_inc_ref(v___x_1377_);
v___x_1418_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1377_);
v___x_1419_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1352_);
v___x_1420_ = lean_array_get_size(v___x_1419_);
v___x_1421_ = lean_unsigned_to_nat(0u);
v___x_1422_ = lean_nat_dec_eq(v___x_1420_, v___x_1421_);
if (v___x_1422_ == 0)
{
v___y_1389_ = v___x_1419_;
v___y_1390_ = v___x_1418_;
v___y_1391_ = v___y_1334_;
v___y_1392_ = v___y_1335_;
goto v___jp_1388_;
}
else
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v_scopes_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v_opts_1429_; uint8_t v_hasTrace_1430_; 
v___x_1423_ = l_Lean_inheritedTraceOptions;
v___x_1424_ = lean_st_ref_get(v___x_1423_);
v___x_1425_ = lean_st_ref_get(v___y_1335_);
v_scopes_1426_ = lean_ctor_get(v___x_1425_, 2);
lean_inc(v_scopes_1426_);
lean_dec(v___x_1425_);
v___x_1427_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1428_ = l_List_head_x21___redArg(v___x_1427_, v_scopes_1426_);
lean_dec(v_scopes_1426_);
v_opts_1429_ = lean_ctor_get(v___x_1428_, 1);
lean_inc_ref(v_opts_1429_);
lean_dec(v___x_1428_);
v_hasTrace_1430_ = lean_ctor_get_uint8(v_opts_1429_, sizeof(void*)*1);
if (v_hasTrace_1430_ == 0)
{
lean_dec_ref(v_opts_1429_);
lean_dec(v___x_1424_);
v___y_1389_ = v___x_1419_;
v___y_1390_ = v___x_1418_;
v___y_1391_ = v___y_1334_;
v___y_1392_ = v___y_1335_;
goto v___jp_1388_;
}
else
{
lean_object* v___x_1431_; lean_object* v___x_1432_; uint8_t v___x_1433_; 
v___x_1431_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1432_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1433_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1424_, v_opts_1429_, v___x_1432_);
lean_dec_ref(v_opts_1429_);
lean_dec(v___x_1424_);
if (v___x_1433_ == 0)
{
v___y_1389_ = v___x_1419_;
v___y_1390_ = v___x_1418_;
v___y_1391_ = v___y_1334_;
v___y_1392_ = v___y_1335_;
goto v___jp_1388_;
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5);
v___x_1435_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1431_, v___x_1434_, v___y_1334_, v___y_1335_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_dec_ref_known(v___x_1435_, 1);
v___y_1389_ = v___x_1419_;
v___y_1390_ = v___x_1418_;
v___y_1391_ = v___y_1334_;
v___y_1392_ = v___y_1335_;
goto v___jp_1388_;
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_dec_ref(v___x_1419_);
lean_dec(v___x_1418_);
lean_del_object(v___x_1386_);
lean_dec(v_snd_1384_);
lean_dec(v_fst_1383_);
lean_dec_ref_known(v___x_1377_, 2);
lean_del_object(v___x_1346_);
lean_dec(v_snd_1344_);
lean_dec(v_fst_1343_);
lean_dec(v_cmd_1327_);
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1435_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1435_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
}
}
v___jp_1444_:
{
if (v_onUnsolved_1328_ == 0)
{
if (v___y_1329_ == 0)
{
lean_del_object(v___x_1386_);
lean_dec(v_snd_1384_);
lean_dec(v_fst_1383_);
lean_dec_ref_known(v___x_1377_, 2);
goto v___jp_1362_;
}
else
{
if (v___y_1445_ == 0)
{
lean_del_object(v___x_1386_);
lean_dec(v_snd_1384_);
lean_dec(v_fst_1383_);
lean_dec_ref_known(v___x_1377_, 2);
goto v___jp_1362_;
}
else
{
lean_del_object(v___x_1341_);
goto v___jp_1417_;
}
}
}
else
{
lean_del_object(v___x_1341_);
goto v___jp_1417_;
}
}
}
}
else
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v_scopes_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v_opts_1454_; uint8_t v_hasTrace_1455_; 
lean_dec(v___x_1381_);
lean_dec_ref_known(v___x_1377_, 2);
lean_del_object(v___x_1341_);
v___x_1448_ = l_Lean_inheritedTraceOptions;
v___x_1449_ = lean_st_ref_get(v___x_1448_);
v___x_1450_ = lean_st_ref_get(v___y_1335_);
v_scopes_1451_ = lean_ctor_get(v___x_1450_, 2);
lean_inc(v_scopes_1451_);
lean_dec(v___x_1450_);
v___x_1452_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1453_ = l_List_head_x21___redArg(v___x_1452_, v_scopes_1451_);
lean_dec(v_scopes_1451_);
v_opts_1454_ = lean_ctor_get(v___x_1453_, 1);
lean_inc_ref(v_opts_1454_);
lean_dec(v___x_1453_);
v_hasTrace_1455_ = lean_ctor_get_uint8(v_opts_1454_, sizeof(void*)*1);
if (v_hasTrace_1455_ == 0)
{
lean_dec_ref(v_opts_1454_);
lean_dec(v___x_1449_);
lean_dec(v___x_1376_);
lean_dec(v___x_1375_);
lean_del_object(v___x_1373_);
goto v___jp_1366_;
}
else
{
lean_object* v___x_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; 
v___x_1456_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1457_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1458_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1449_, v_opts_1454_, v___x_1457_);
lean_dec_ref(v_opts_1454_);
lean_dec(v___x_1449_);
if (v___x_1458_ == 0)
{
lean_dec(v___x_1376_);
lean_dec(v___x_1375_);
lean_del_object(v___x_1373_);
goto v___jp_1366_;
}
else
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1462_; 
v___x_1459_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7);
v___x_1460_ = l_Nat_reprFast(v___x_1375_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set_tag(v___x_1373_, 3);
lean_ctor_set(v___x_1373_, 0, v___x_1460_);
v___x_1462_ = v___x_1373_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1463_ = l_Lean_MessageData_ofFormat(v___x_1462_);
v___x_1464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1459_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
v___x_1465_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9);
v___x_1466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1464_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
v___x_1467_ = l_Nat_reprFast(v___x_1376_);
v___x_1468_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
v___x_1469_ = l_Lean_MessageData_ofFormat(v___x_1468_);
v___x_1470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1466_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
v___x_1471_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11);
v___x_1472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1470_);
lean_ctor_set(v___x_1472_, 1, v___x_1471_);
v___x_1473_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1456_, v___x_1472_, v___y_1334_, v___y_1335_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_dec_ref_known(v___x_1473_, 1);
goto v___jp_1366_;
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
lean_del_object(v___x_1346_);
lean_dec(v_snd_1344_);
lean_dec(v_fst_1343_);
lean_dec(v_cmd_1327_);
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1473_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1473_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
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
lean_object* v___x_1484_; 
lean_dec(v_endPos_1350_);
lean_del_object(v___x_1341_);
v___x_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1484_, 0, v_fst_1343_);
lean_ctor_set(v___x_1484_, 1, v_snd_1344_);
v_a_1355_ = v___x_1484_;
goto v___jp_1354_;
}
}
}
else
{
lean_object* v___x_1485_; 
lean_dec(v_endPos_1350_);
lean_del_object(v___x_1341_);
v___x_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1485_, 0, v_fst_1343_);
lean_ctor_set(v___x_1485_, 1, v_snd_1344_);
v_a_1355_ = v___x_1485_;
goto v___jp_1354_;
}
v___jp_1354_:
{
lean_object* v___x_1357_; 
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 1, v_a_1355_);
lean_ctor_set(v___x_1346_, 0, v___x_1353_);
v___x_1357_ = v___x_1346_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_a_1355_);
v___x_1357_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
size_t v___x_1358_; size_t v___x_1359_; 
v___x_1358_ = ((size_t)1ULL);
v___x_1359_ = lean_usize_add(v_i_1332_, v___x_1358_);
v_i_1332_ = v___x_1359_;
v_b_1333_ = v___x_1357_;
goto _start;
}
}
v___jp_1362_:
{
lean_object* v___x_1364_; 
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 1, v_snd_1344_);
lean_ctor_set(v___x_1341_, 0, v_fst_1343_);
v___x_1364_ = v___x_1341_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_fst_1343_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_snd_1344_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
v_a_1355_ = v___x_1364_;
goto v___jp_1354_;
}
}
v___jp_1366_:
{
lean_object* v___x_1367_; 
v___x_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1367_, 0, v_fst_1343_);
lean_ctor_set(v___x_1367_, 1, v_snd_1344_);
v_a_1355_ = v___x_1367_;
goto v___jp_1354_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___boxed(lean_object* v___x_1489_, lean_object* v_val_1490_, lean_object* v_cmd_1491_, lean_object* v_onUnsolved_1492_, lean_object* v___y_1493_, lean_object* v_as_1494_, lean_object* v_sz_1495_, lean_object* v_i_1496_, lean_object* v_b_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
uint8_t v_onUnsolved_boxed_1501_; uint8_t v___y_11924__boxed_1502_; size_t v_sz_boxed_1503_; size_t v_i_boxed_1504_; lean_object* v_res_1505_; 
v_onUnsolved_boxed_1501_ = lean_unbox(v_onUnsolved_1492_);
v___y_11924__boxed_1502_ = lean_unbox(v___y_1493_);
v_sz_boxed_1503_ = lean_unbox_usize(v_sz_1495_);
lean_dec(v_sz_1495_);
v_i_boxed_1504_ = lean_unbox_usize(v_i_1496_);
lean_dec(v_i_1496_);
v_res_1505_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12(v___x_1489_, v_val_1490_, v_cmd_1491_, v_onUnsolved_boxed_1501_, v___y_11924__boxed_1502_, v_as_1494_, v_sz_boxed_1503_, v_i_boxed_1504_, v_b_1497_, v___y_1498_, v___y_1499_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec_ref(v_as_1494_);
lean_dec_ref(v_val_1490_);
lean_dec_ref(v___x_1489_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8(lean_object* v___x_1506_, lean_object* v_val_1507_, lean_object* v_cmd_1508_, uint8_t v_onUnsolved_1509_, uint8_t v___y_1510_, lean_object* v_as_1511_, size_t v_sz_1512_, size_t v_i_1513_, lean_object* v_b_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
uint8_t v___x_1518_; 
v___x_1518_ = lean_usize_dec_lt(v_i_1513_, v_sz_1512_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; 
lean_dec(v_cmd_1508_);
v___x_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1519_, 0, v_b_1514_);
return v___x_1519_;
}
else
{
lean_object* v_snd_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1668_; 
v_snd_1520_ = lean_ctor_get(v_b_1514_, 1);
v_isSharedCheck_1668_ = !lean_is_exclusive(v_b_1514_);
if (v_isSharedCheck_1668_ == 0)
{
lean_object* v_unused_1669_; 
v_unused_1669_ = lean_ctor_get(v_b_1514_, 0);
lean_dec(v_unused_1669_);
v___x_1522_ = v_b_1514_;
v_isShared_1523_ = v_isSharedCheck_1668_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_snd_1520_);
lean_dec(v_b_1514_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1668_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v_fst_1524_; lean_object* v_snd_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1667_; 
v_fst_1524_ = lean_ctor_get(v_snd_1520_, 0);
v_snd_1525_ = lean_ctor_get(v_snd_1520_, 1);
v_isSharedCheck_1667_ = !lean_is_exclusive(v_snd_1520_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1527_ = v_snd_1520_;
v_isShared_1528_ = v_isSharedCheck_1667_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_snd_1525_);
lean_inc(v_fst_1524_);
lean_dec(v_snd_1520_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1667_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v_a_1529_; lean_object* v_pos_1530_; lean_object* v_endPos_1531_; uint8_t v_severity_1532_; lean_object* v_data_1533_; lean_object* v___x_1534_; lean_object* v_a_1536_; 
v_a_1529_ = lean_array_uget_borrowed(v_as_1511_, v_i_1513_);
v_pos_1530_ = lean_ctor_get(v_a_1529_, 1);
v_endPos_1531_ = lean_ctor_get(v_a_1529_, 2);
lean_inc(v_endPos_1531_);
v_severity_1532_ = lean_ctor_get_uint8(v_a_1529_, sizeof(void*)*5 + 1);
v_data_1533_ = lean_ctor_get(v_a_1529_, 4);
v___x_1534_ = lean_box(0);
if (v_severity_1532_ == 2)
{
lean_object* v___f_1549_; uint8_t v___x_1550_; 
v___f_1549_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
lean_inc(v_data_1533_);
v___x_1550_ = l_Lean_MessageData_hasTag(v___f_1549_, v_data_1533_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; 
lean_dec(v_endPos_1531_);
lean_del_object(v___x_1522_);
v___x_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1551_, 0, v_fst_1524_);
lean_ctor_set(v___x_1551_, 1, v_snd_1525_);
v_a_1536_ = v___x_1551_;
goto v___jp_1535_;
}
else
{
if (lean_obj_tag(v_endPos_1531_) == 1)
{
lean_object* v_val_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1664_; 
v_val_1552_ = lean_ctor_get(v_endPos_1531_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_endPos_1531_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1554_ = v_endPos_1531_;
v_isShared_1555_ = v_isSharedCheck_1664_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_val_1552_);
lean_dec(v_endPos_1531_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1664_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; uint8_t v___x_1560_; 
lean_inc_ref(v_pos_1530_);
v___x_1556_ = l_Lean_FileMap_ofPosition(v___x_1506_, v_pos_1530_);
v___x_1557_ = l_Lean_FileMap_ofPosition(v___x_1506_, v_val_1552_);
lean_inc(v___x_1557_);
lean_inc(v___x_1556_);
v___x_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1556_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = 0;
v___x_1560_ = l_Lean_Syntax_Range_includes(v_val_1507_, v___x_1558_, v___x_1559_, v___x_1559_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; 
lean_dec_ref_known(v___x_1558_, 2);
lean_dec(v___x_1557_);
lean_dec(v___x_1556_);
lean_del_object(v___x_1554_);
lean_del_object(v___x_1522_);
v___x_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1561_, 0, v_fst_1524_);
lean_ctor_set(v___x_1561_, 1, v_snd_1525_);
v_a_1536_ = v___x_1561_;
goto v___jp_1535_;
}
else
{
lean_object* v___x_1562_; 
lean_inc(v_cmd_1508_);
lean_inc_ref(v___x_1558_);
v___x_1562_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1558_, v_cmd_1508_);
if (lean_obj_tag(v___x_1562_) == 1)
{
lean_object* v_val_1563_; lean_object* v_fst_1564_; lean_object* v_snd_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1628_; 
lean_dec(v___x_1557_);
lean_dec(v___x_1556_);
lean_del_object(v___x_1554_);
v_val_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_val_1563_);
lean_dec_ref_known(v___x_1562_, 1);
v_fst_1564_ = lean_ctor_get(v_val_1563_, 0);
v_snd_1565_ = lean_ctor_get(v_val_1563_, 1);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_val_1563_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1567_ = v_val_1563_;
v_isShared_1568_ = v_isSharedCheck_1628_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_snd_1565_);
lean_inc(v_fst_1564_);
lean_dec(v_val_1563_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1628_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; uint8_t v___y_1626_; lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_Syntax_getPos_x3f(v_fst_1564_, v___x_1559_);
if (lean_obj_tag(v___x_1627_) == 0)
{
v___y_1626_ = v___x_1560_;
goto v___jp_1625_;
}
else
{
lean_dec_ref_known(v___x_1627_, 1);
v___y_1626_ = v___x_1559_;
goto v___jp_1625_;
}
v___jp_1569_:
{
lean_object* v___x_1575_; 
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 1, v_snd_1525_);
lean_ctor_set(v___x_1567_, 0, v_fst_1524_);
v___x_1575_ = v___x_1567_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_fst_1524_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_snd_1525_);
v___x_1575_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
size_t v_sz_1576_; size_t v___x_1577_; lean_object* v___x_1578_; 
v_sz_1576_ = lean_array_size(v___y_1571_);
v___x_1577_ = ((size_t)0ULL);
v___x_1578_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1558_, v_fst_1564_, v_snd_1565_, v___y_1570_, v___y_1571_, v_sz_1576_, v___x_1577_, v___x_1575_);
lean_dec_ref(v___y_1571_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; lean_object* v_fst_1580_; lean_object* v_snd_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1579_);
lean_dec_ref_known(v___x_1578_, 1);
v_fst_1580_ = lean_ctor_get(v_a_1579_, 0);
v_snd_1581_ = lean_ctor_get(v_a_1579_, 1);
v_isSharedCheck_1588_ = !lean_is_exclusive(v_a_1579_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v_a_1579_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_snd_1581_);
lean_inc(v_fst_1580_);
lean_dec(v_a_1579_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_fst_1580_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v_snd_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
v_a_1536_ = v___x_1586_;
goto v___jp_1535_;
}
}
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_del_object(v___x_1527_);
lean_dec(v_cmd_1508_);
v_a_1589_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1578_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1578_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
}
v___jp_1598_:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; 
lean_inc_ref(v___x_1558_);
v___x_1599_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1558_);
v___x_1600_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1533_);
v___x_1601_ = lean_array_get_size(v___x_1600_);
v___x_1602_ = lean_unsigned_to_nat(0u);
v___x_1603_ = lean_nat_dec_eq(v___x_1601_, v___x_1602_);
if (v___x_1603_ == 0)
{
v___y_1570_ = v___x_1599_;
v___y_1571_ = v___x_1600_;
v___y_1572_ = v___y_1515_;
v___y_1573_ = v___y_1516_;
goto v___jp_1569_;
}
else
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v_scopes_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v_opts_1610_; uint8_t v_hasTrace_1611_; 
v___x_1604_ = l_Lean_inheritedTraceOptions;
v___x_1605_ = lean_st_ref_get(v___x_1604_);
v___x_1606_ = lean_st_ref_get(v___y_1516_);
v_scopes_1607_ = lean_ctor_get(v___x_1606_, 2);
lean_inc(v_scopes_1607_);
lean_dec(v___x_1606_);
v___x_1608_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1609_ = l_List_head_x21___redArg(v___x_1608_, v_scopes_1607_);
lean_dec(v_scopes_1607_);
v_opts_1610_ = lean_ctor_get(v___x_1609_, 1);
lean_inc_ref(v_opts_1610_);
lean_dec(v___x_1609_);
v_hasTrace_1611_ = lean_ctor_get_uint8(v_opts_1610_, sizeof(void*)*1);
if (v_hasTrace_1611_ == 0)
{
lean_dec_ref(v_opts_1610_);
lean_dec(v___x_1605_);
v___y_1570_ = v___x_1599_;
v___y_1571_ = v___x_1600_;
v___y_1572_ = v___y_1515_;
v___y_1573_ = v___y_1516_;
goto v___jp_1569_;
}
else
{
lean_object* v___x_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v___x_1612_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1613_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1614_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1605_, v_opts_1610_, v___x_1613_);
lean_dec_ref(v_opts_1610_);
lean_dec(v___x_1605_);
if (v___x_1614_ == 0)
{
v___y_1570_ = v___x_1599_;
v___y_1571_ = v___x_1600_;
v___y_1572_ = v___y_1515_;
v___y_1573_ = v___y_1516_;
goto v___jp_1569_;
}
else
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5);
v___x_1616_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1612_, v___x_1615_, v___y_1515_, v___y_1516_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_dec_ref_known(v___x_1616_, 1);
v___y_1570_ = v___x_1599_;
v___y_1571_ = v___x_1600_;
v___y_1572_ = v___y_1515_;
v___y_1573_ = v___y_1516_;
goto v___jp_1569_;
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
lean_dec_ref(v___x_1600_);
lean_dec(v___x_1599_);
lean_del_object(v___x_1567_);
lean_dec(v_snd_1565_);
lean_dec(v_fst_1564_);
lean_dec_ref_known(v___x_1558_, 2);
lean_del_object(v___x_1527_);
lean_dec(v_snd_1525_);
lean_dec(v_fst_1524_);
lean_dec(v_cmd_1508_);
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1616_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1616_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
}
}
}
v___jp_1625_:
{
if (v_onUnsolved_1509_ == 0)
{
if (v___y_1510_ == 0)
{
lean_del_object(v___x_1567_);
lean_dec(v_snd_1565_);
lean_dec(v_fst_1564_);
lean_dec_ref_known(v___x_1558_, 2);
goto v___jp_1543_;
}
else
{
if (v___y_1626_ == 0)
{
lean_del_object(v___x_1567_);
lean_dec(v_snd_1565_);
lean_dec(v_fst_1564_);
lean_dec_ref_known(v___x_1558_, 2);
goto v___jp_1543_;
}
else
{
lean_del_object(v___x_1522_);
goto v___jp_1598_;
}
}
}
else
{
lean_del_object(v___x_1522_);
goto v___jp_1598_;
}
}
}
}
else
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v_scopes_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v_opts_1635_; uint8_t v_hasTrace_1636_; 
lean_dec(v___x_1562_);
lean_dec_ref_known(v___x_1558_, 2);
lean_del_object(v___x_1522_);
v___x_1629_ = l_Lean_inheritedTraceOptions;
v___x_1630_ = lean_st_ref_get(v___x_1629_);
v___x_1631_ = lean_st_ref_get(v___y_1516_);
v_scopes_1632_ = lean_ctor_get(v___x_1631_, 2);
lean_inc(v_scopes_1632_);
lean_dec(v___x_1631_);
v___x_1633_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1634_ = l_List_head_x21___redArg(v___x_1633_, v_scopes_1632_);
lean_dec(v_scopes_1632_);
v_opts_1635_ = lean_ctor_get(v___x_1634_, 1);
lean_inc_ref(v_opts_1635_);
lean_dec(v___x_1634_);
v_hasTrace_1636_ = lean_ctor_get_uint8(v_opts_1635_, sizeof(void*)*1);
if (v_hasTrace_1636_ == 0)
{
lean_dec_ref(v_opts_1635_);
lean_dec(v___x_1630_);
lean_dec(v___x_1557_);
lean_dec(v___x_1556_);
lean_del_object(v___x_1554_);
goto v___jp_1547_;
}
else
{
lean_object* v___x_1637_; lean_object* v___x_1638_; uint8_t v___x_1639_; 
v___x_1637_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1638_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1639_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1630_, v_opts_1635_, v___x_1638_);
lean_dec_ref(v_opts_1635_);
lean_dec(v___x_1630_);
if (v___x_1639_ == 0)
{
lean_dec(v___x_1557_);
lean_dec(v___x_1556_);
lean_del_object(v___x_1554_);
goto v___jp_1547_;
}
else
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1643_; 
v___x_1640_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7);
v___x_1641_ = l_Nat_reprFast(v___x_1556_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set_tag(v___x_1554_, 3);
lean_ctor_set(v___x_1554_, 0, v___x_1641_);
v___x_1643_ = v___x_1554_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1641_);
v___x_1643_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1644_ = l_Lean_MessageData_ofFormat(v___x_1643_);
v___x_1645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1640_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9);
v___x_1647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1645_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = l_Nat_reprFast(v___x_1557_);
v___x_1649_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
v___x_1650_ = l_Lean_MessageData_ofFormat(v___x_1649_);
v___x_1651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1647_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11);
v___x_1653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1651_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1637_, v___x_1653_, v___y_1515_, v___y_1516_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_dec_ref_known(v___x_1654_, 1);
goto v___jp_1547_;
}
else
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
lean_del_object(v___x_1527_);
lean_dec(v_snd_1525_);
lean_dec(v_fst_1524_);
lean_dec(v_cmd_1508_);
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1657_ = v___x_1654_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1654_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1655_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
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
lean_object* v___x_1665_; 
lean_dec(v_endPos_1531_);
lean_del_object(v___x_1522_);
v___x_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1665_, 0, v_fst_1524_);
lean_ctor_set(v___x_1665_, 1, v_snd_1525_);
v_a_1536_ = v___x_1665_;
goto v___jp_1535_;
}
}
}
else
{
lean_object* v___x_1666_; 
lean_dec(v_endPos_1531_);
lean_del_object(v___x_1522_);
v___x_1666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1666_, 0, v_fst_1524_);
lean_ctor_set(v___x_1666_, 1, v_snd_1525_);
v_a_1536_ = v___x_1666_;
goto v___jp_1535_;
}
v___jp_1535_:
{
lean_object* v___x_1538_; 
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 1, v_a_1536_);
lean_ctor_set(v___x_1527_, 0, v___x_1534_);
v___x_1538_ = v___x_1527_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1534_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_a_1536_);
v___x_1538_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
size_t v___x_1539_; size_t v___x_1540_; lean_object* v___x_1541_; 
v___x_1539_ = ((size_t)1ULL);
v___x_1540_ = lean_usize_add(v_i_1513_, v___x_1539_);
v___x_1541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12(v___x_1506_, v_val_1507_, v_cmd_1508_, v_onUnsolved_1509_, v___y_1510_, v_as_1511_, v_sz_1512_, v___x_1540_, v___x_1538_, v___y_1515_, v___y_1516_);
return v___x_1541_;
}
}
v___jp_1543_:
{
lean_object* v___x_1545_; 
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 1, v_snd_1525_);
lean_ctor_set(v___x_1522_, 0, v_fst_1524_);
v___x_1545_ = v___x_1522_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_fst_1524_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v_snd_1525_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
v_a_1536_ = v___x_1545_;
goto v___jp_1535_;
}
}
v___jp_1547_:
{
lean_object* v___x_1548_; 
v___x_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1548_, 0, v_fst_1524_);
lean_ctor_set(v___x_1548_, 1, v_snd_1525_);
v_a_1536_ = v___x_1548_;
goto v___jp_1535_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___boxed(lean_object* v___x_1670_, lean_object* v_val_1671_, lean_object* v_cmd_1672_, lean_object* v_onUnsolved_1673_, lean_object* v___y_1674_, lean_object* v_as_1675_, lean_object* v_sz_1676_, lean_object* v_i_1677_, lean_object* v_b_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
uint8_t v_onUnsolved_boxed_1682_; uint8_t v___y_12265__boxed_1683_; size_t v_sz_boxed_1684_; size_t v_i_boxed_1685_; lean_object* v_res_1686_; 
v_onUnsolved_boxed_1682_ = lean_unbox(v_onUnsolved_1673_);
v___y_12265__boxed_1683_ = lean_unbox(v___y_1674_);
v_sz_boxed_1684_ = lean_unbox_usize(v_sz_1676_);
lean_dec(v_sz_1676_);
v_i_boxed_1685_ = lean_unbox_usize(v_i_1677_);
lean_dec(v_i_1677_);
v_res_1686_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8(v___x_1670_, v_val_1671_, v_cmd_1672_, v_onUnsolved_boxed_1682_, v___y_12265__boxed_1683_, v_as_1675_, v_sz_boxed_1684_, v_i_boxed_1685_, v_b_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec_ref(v_as_1675_);
lean_dec_ref(v_val_1671_);
lean_dec_ref(v___x_1670_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10_spec__12(lean_object* v___x_1687_, lean_object* v_val_1688_, lean_object* v_cmd_1689_, uint8_t v_onUnsolved_1690_, uint8_t v___y_1691_, lean_object* v_as_1692_, size_t v_sz_1693_, size_t v_i_1694_, lean_object* v_b_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
uint8_t v___x_1699_; 
v___x_1699_ = lean_usize_dec_lt(v_i_1694_, v_sz_1693_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; 
lean_dec(v_cmd_1689_);
v___x_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1700_, 0, v_b_1695_);
return v___x_1700_;
}
else
{
lean_object* v_snd_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1849_; 
v_snd_1701_ = lean_ctor_get(v_b_1695_, 1);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_b_1695_);
if (v_isSharedCheck_1849_ == 0)
{
lean_object* v_unused_1850_; 
v_unused_1850_ = lean_ctor_get(v_b_1695_, 0);
lean_dec(v_unused_1850_);
v___x_1703_ = v_b_1695_;
v_isShared_1704_ = v_isSharedCheck_1849_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_snd_1701_);
lean_dec(v_b_1695_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1849_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v_fst_1705_; lean_object* v_snd_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1848_; 
v_fst_1705_ = lean_ctor_get(v_snd_1701_, 0);
v_snd_1706_ = lean_ctor_get(v_snd_1701_, 1);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_snd_1701_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1708_ = v_snd_1701_;
v_isShared_1709_ = v_isSharedCheck_1848_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_snd_1706_);
lean_inc(v_fst_1705_);
lean_dec(v_snd_1701_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1848_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v_a_1710_; lean_object* v_pos_1711_; lean_object* v_endPos_1712_; uint8_t v_severity_1713_; lean_object* v_data_1714_; lean_object* v___x_1715_; lean_object* v_a_1717_; 
v_a_1710_ = lean_array_uget_borrowed(v_as_1692_, v_i_1694_);
v_pos_1711_ = lean_ctor_get(v_a_1710_, 1);
v_endPos_1712_ = lean_ctor_get(v_a_1710_, 2);
lean_inc(v_endPos_1712_);
v_severity_1713_ = lean_ctor_get_uint8(v_a_1710_, sizeof(void*)*5 + 1);
v_data_1714_ = lean_ctor_get(v_a_1710_, 4);
v___x_1715_ = lean_box(0);
if (v_severity_1713_ == 2)
{
lean_object* v___f_1730_; uint8_t v___x_1731_; 
v___f_1730_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
lean_inc(v_data_1714_);
v___x_1731_ = l_Lean_MessageData_hasTag(v___f_1730_, v_data_1714_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; 
lean_dec(v_endPos_1712_);
lean_del_object(v___x_1703_);
v___x_1732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1732_, 0, v_fst_1705_);
lean_ctor_set(v___x_1732_, 1, v_snd_1706_);
v_a_1717_ = v___x_1732_;
goto v___jp_1716_;
}
else
{
if (lean_obj_tag(v_endPos_1712_) == 1)
{
lean_object* v_val_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1845_; 
v_val_1733_ = lean_ctor_get(v_endPos_1712_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v_endPos_1712_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1735_ = v_endPos_1712_;
v_isShared_1736_ = v_isSharedCheck_1845_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_val_1733_);
lean_dec(v_endPos_1712_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1845_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; uint8_t v___x_1740_; uint8_t v___x_1741_; 
lean_inc_ref(v_pos_1711_);
v___x_1737_ = l_Lean_FileMap_ofPosition(v___x_1687_, v_pos_1711_);
v___x_1738_ = l_Lean_FileMap_ofPosition(v___x_1687_, v_val_1733_);
lean_inc(v___x_1738_);
lean_inc(v___x_1737_);
v___x_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1737_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
v___x_1740_ = 0;
v___x_1741_ = l_Lean_Syntax_Range_includes(v_val_1688_, v___x_1739_, v___x_1740_, v___x_1740_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1742_; 
lean_dec_ref_known(v___x_1739_, 2);
lean_dec(v___x_1738_);
lean_dec(v___x_1737_);
lean_del_object(v___x_1735_);
lean_del_object(v___x_1703_);
v___x_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1742_, 0, v_fst_1705_);
lean_ctor_set(v___x_1742_, 1, v_snd_1706_);
v_a_1717_ = v___x_1742_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_1743_; 
lean_inc(v_cmd_1689_);
lean_inc_ref(v___x_1739_);
v___x_1743_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1739_, v_cmd_1689_);
if (lean_obj_tag(v___x_1743_) == 1)
{
lean_object* v_val_1744_; lean_object* v_fst_1745_; lean_object* v_snd_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1809_; 
lean_dec(v___x_1738_);
lean_dec(v___x_1737_);
lean_del_object(v___x_1735_);
v_val_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_val_1744_);
lean_dec_ref_known(v___x_1743_, 1);
v_fst_1745_ = lean_ctor_get(v_val_1744_, 0);
v_snd_1746_ = lean_ctor_get(v_val_1744_, 1);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_val_1744_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1748_ = v_val_1744_;
v_isShared_1749_ = v_isSharedCheck_1809_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_snd_1746_);
lean_inc(v_fst_1745_);
lean_dec(v_val_1744_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1809_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; uint8_t v___y_1807_; lean_object* v___x_1808_; 
v___x_1808_ = l_Lean_Syntax_getPos_x3f(v_fst_1745_, v___x_1740_);
if (lean_obj_tag(v___x_1808_) == 0)
{
v___y_1807_ = v___x_1741_;
goto v___jp_1806_;
}
else
{
lean_dec_ref_known(v___x_1808_, 1);
v___y_1807_ = v___x_1740_;
goto v___jp_1806_;
}
v___jp_1750_:
{
lean_object* v___x_1756_; 
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 1, v_snd_1706_);
lean_ctor_set(v___x_1748_, 0, v_fst_1705_);
v___x_1756_ = v___x_1748_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_fst_1705_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v_snd_1706_);
v___x_1756_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
size_t v_sz_1757_; size_t v___x_1758_; lean_object* v___x_1759_; 
v_sz_1757_ = lean_array_size(v___y_1752_);
v___x_1758_ = ((size_t)0ULL);
v___x_1759_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1739_, v_fst_1745_, v_snd_1746_, v___y_1751_, v___y_1752_, v_sz_1757_, v___x_1758_, v___x_1756_);
lean_dec_ref(v___y_1752_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; lean_object* v_fst_1761_; lean_object* v_snd_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_a_1760_);
lean_dec_ref_known(v___x_1759_, 1);
v_fst_1761_ = lean_ctor_get(v_a_1760_, 0);
v_snd_1762_ = lean_ctor_get(v_a_1760_, 1);
v_isSharedCheck_1769_ = !lean_is_exclusive(v_a_1760_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v_a_1760_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_snd_1762_);
lean_inc(v_fst_1761_);
lean_dec(v_a_1760_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_fst_1761_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_snd_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
v_a_1717_ = v___x_1767_;
goto v___jp_1716_;
}
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_del_object(v___x_1708_);
lean_dec(v_cmd_1689_);
v_a_1770_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1759_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1759_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
}
v___jp_1779_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
lean_inc_ref(v___x_1739_);
v___x_1780_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1739_);
v___x_1781_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1714_);
v___x_1782_ = lean_array_get_size(v___x_1781_);
v___x_1783_ = lean_unsigned_to_nat(0u);
v___x_1784_ = lean_nat_dec_eq(v___x_1782_, v___x_1783_);
if (v___x_1784_ == 0)
{
v___y_1751_ = v___x_1780_;
v___y_1752_ = v___x_1781_;
v___y_1753_ = v___y_1696_;
v___y_1754_ = v___y_1697_;
goto v___jp_1750_;
}
else
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v_scopes_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v_opts_1791_; uint8_t v_hasTrace_1792_; 
v___x_1785_ = l_Lean_inheritedTraceOptions;
v___x_1786_ = lean_st_ref_get(v___x_1785_);
v___x_1787_ = lean_st_ref_get(v___y_1697_);
v_scopes_1788_ = lean_ctor_get(v___x_1787_, 2);
lean_inc(v_scopes_1788_);
lean_dec(v___x_1787_);
v___x_1789_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1790_ = l_List_head_x21___redArg(v___x_1789_, v_scopes_1788_);
lean_dec(v_scopes_1788_);
v_opts_1791_ = lean_ctor_get(v___x_1790_, 1);
lean_inc_ref(v_opts_1791_);
lean_dec(v___x_1790_);
v_hasTrace_1792_ = lean_ctor_get_uint8(v_opts_1791_, sizeof(void*)*1);
if (v_hasTrace_1792_ == 0)
{
lean_dec_ref(v_opts_1791_);
lean_dec(v___x_1786_);
v___y_1751_ = v___x_1780_;
v___y_1752_ = v___x_1781_;
v___y_1753_ = v___y_1696_;
v___y_1754_ = v___y_1697_;
goto v___jp_1750_;
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1794_; uint8_t v___x_1795_; 
v___x_1793_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1794_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1795_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1786_, v_opts_1791_, v___x_1794_);
lean_dec_ref(v_opts_1791_);
lean_dec(v___x_1786_);
if (v___x_1795_ == 0)
{
v___y_1751_ = v___x_1780_;
v___y_1752_ = v___x_1781_;
v___y_1753_ = v___y_1696_;
v___y_1754_ = v___y_1697_;
goto v___jp_1750_;
}
else
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5);
v___x_1797_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1793_, v___x_1796_, v___y_1696_, v___y_1697_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_dec_ref_known(v___x_1797_, 1);
v___y_1751_ = v___x_1780_;
v___y_1752_ = v___x_1781_;
v___y_1753_ = v___y_1696_;
v___y_1754_ = v___y_1697_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
lean_dec_ref(v___x_1781_);
lean_dec(v___x_1780_);
lean_del_object(v___x_1748_);
lean_dec(v_snd_1746_);
lean_dec(v_fst_1745_);
lean_dec_ref_known(v___x_1739_, 2);
lean_del_object(v___x_1708_);
lean_dec(v_snd_1706_);
lean_dec(v_fst_1705_);
lean_dec(v_cmd_1689_);
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
}
}
}
v___jp_1806_:
{
if (v_onUnsolved_1690_ == 0)
{
if (v___y_1691_ == 0)
{
lean_del_object(v___x_1748_);
lean_dec(v_snd_1746_);
lean_dec(v_fst_1745_);
lean_dec_ref_known(v___x_1739_, 2);
goto v___jp_1724_;
}
else
{
if (v___y_1807_ == 0)
{
lean_del_object(v___x_1748_);
lean_dec(v_snd_1746_);
lean_dec(v_fst_1745_);
lean_dec_ref_known(v___x_1739_, 2);
goto v___jp_1724_;
}
else
{
lean_del_object(v___x_1703_);
goto v___jp_1779_;
}
}
}
else
{
lean_del_object(v___x_1703_);
goto v___jp_1779_;
}
}
}
}
else
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v_scopes_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v_opts_1816_; uint8_t v_hasTrace_1817_; 
lean_dec(v___x_1743_);
lean_dec_ref_known(v___x_1739_, 2);
lean_del_object(v___x_1703_);
v___x_1810_ = l_Lean_inheritedTraceOptions;
v___x_1811_ = lean_st_ref_get(v___x_1810_);
v___x_1812_ = lean_st_ref_get(v___y_1697_);
v_scopes_1813_ = lean_ctor_get(v___x_1812_, 2);
lean_inc(v_scopes_1813_);
lean_dec(v___x_1812_);
v___x_1814_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1815_ = l_List_head_x21___redArg(v___x_1814_, v_scopes_1813_);
lean_dec(v_scopes_1813_);
v_opts_1816_ = lean_ctor_get(v___x_1815_, 1);
lean_inc_ref(v_opts_1816_);
lean_dec(v___x_1815_);
v_hasTrace_1817_ = lean_ctor_get_uint8(v_opts_1816_, sizeof(void*)*1);
if (v_hasTrace_1817_ == 0)
{
lean_dec_ref(v_opts_1816_);
lean_dec(v___x_1811_);
lean_dec(v___x_1738_);
lean_dec(v___x_1737_);
lean_del_object(v___x_1735_);
goto v___jp_1728_;
}
else
{
lean_object* v___x_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; 
v___x_1818_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1819_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1820_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1811_, v_opts_1816_, v___x_1819_);
lean_dec_ref(v_opts_1816_);
lean_dec(v___x_1811_);
if (v___x_1820_ == 0)
{
lean_dec(v___x_1738_);
lean_dec(v___x_1737_);
lean_del_object(v___x_1735_);
goto v___jp_1728_;
}
else
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1824_; 
v___x_1821_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7);
v___x_1822_ = l_Nat_reprFast(v___x_1737_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set_tag(v___x_1735_, 3);
lean_ctor_set(v___x_1735_, 0, v___x_1822_);
v___x_1824_ = v___x_1735_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1822_);
v___x_1824_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1825_ = l_Lean_MessageData_ofFormat(v___x_1824_);
v___x_1826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1821_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
v___x_1827_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9);
v___x_1828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1826_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
v___x_1829_ = l_Nat_reprFast(v___x_1738_);
v___x_1830_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
v___x_1831_ = l_Lean_MessageData_ofFormat(v___x_1830_);
v___x_1832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1828_);
lean_ctor_set(v___x_1832_, 1, v___x_1831_);
v___x_1833_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11);
v___x_1834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1832_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
v___x_1835_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1818_, v___x_1834_, v___y_1696_, v___y_1697_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_dec_ref_known(v___x_1835_, 1);
goto v___jp_1728_;
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
lean_del_object(v___x_1708_);
lean_dec(v_snd_1706_);
lean_dec(v_fst_1705_);
lean_dec(v_cmd_1689_);
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
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
lean_object* v___x_1846_; 
lean_dec(v_endPos_1712_);
lean_del_object(v___x_1703_);
v___x_1846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1846_, 0, v_fst_1705_);
lean_ctor_set(v___x_1846_, 1, v_snd_1706_);
v_a_1717_ = v___x_1846_;
goto v___jp_1716_;
}
}
}
else
{
lean_object* v___x_1847_; 
lean_dec(v_endPos_1712_);
lean_del_object(v___x_1703_);
v___x_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1847_, 0, v_fst_1705_);
lean_ctor_set(v___x_1847_, 1, v_snd_1706_);
v_a_1717_ = v___x_1847_;
goto v___jp_1716_;
}
v___jp_1716_:
{
lean_object* v___x_1719_; 
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 1, v_a_1717_);
lean_ctor_set(v___x_1708_, 0, v___x_1715_);
v___x_1719_ = v___x_1708_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1715_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_a_1717_);
v___x_1719_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
size_t v___x_1720_; size_t v___x_1721_; 
v___x_1720_ = ((size_t)1ULL);
v___x_1721_ = lean_usize_add(v_i_1694_, v___x_1720_);
v_i_1694_ = v___x_1721_;
v_b_1695_ = v___x_1719_;
goto _start;
}
}
v___jp_1724_:
{
lean_object* v___x_1726_; 
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 1, v_snd_1706_);
lean_ctor_set(v___x_1703_, 0, v_fst_1705_);
v___x_1726_ = v___x_1703_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_fst_1705_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v_snd_1706_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
v_a_1717_ = v___x_1726_;
goto v___jp_1716_;
}
}
v___jp_1728_:
{
lean_object* v___x_1729_; 
v___x_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1729_, 0, v_fst_1705_);
lean_ctor_set(v___x_1729_, 1, v_snd_1706_);
v_a_1717_ = v___x_1729_;
goto v___jp_1716_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10_spec__12___boxed(lean_object* v___x_1851_, lean_object* v_val_1852_, lean_object* v_cmd_1853_, lean_object* v_onUnsolved_1854_, lean_object* v___y_1855_, lean_object* v_as_1856_, lean_object* v_sz_1857_, lean_object* v_i_1858_, lean_object* v_b_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
uint8_t v_onUnsolved_boxed_1863_; uint8_t v___y_12597__boxed_1864_; size_t v_sz_boxed_1865_; size_t v_i_boxed_1866_; lean_object* v_res_1867_; 
v_onUnsolved_boxed_1863_ = lean_unbox(v_onUnsolved_1854_);
v___y_12597__boxed_1864_ = lean_unbox(v___y_1855_);
v_sz_boxed_1865_ = lean_unbox_usize(v_sz_1857_);
lean_dec(v_sz_1857_);
v_i_boxed_1866_ = lean_unbox_usize(v_i_1858_);
lean_dec(v_i_1858_);
v_res_1867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10_spec__12(v___x_1851_, v_val_1852_, v_cmd_1853_, v_onUnsolved_boxed_1863_, v___y_12597__boxed_1864_, v_as_1856_, v_sz_boxed_1865_, v_i_boxed_1866_, v_b_1859_, v___y_1860_, v___y_1861_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec_ref(v_as_1856_);
lean_dec_ref(v_val_1852_);
lean_dec_ref(v___x_1851_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10(lean_object* v___x_1868_, lean_object* v_val_1869_, lean_object* v_cmd_1870_, uint8_t v_onUnsolved_1871_, uint8_t v___y_1872_, lean_object* v_as_1873_, size_t v_sz_1874_, size_t v_i_1875_, lean_object* v_b_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
uint8_t v___x_1880_; 
v___x_1880_ = lean_usize_dec_lt(v_i_1875_, v_sz_1874_);
if (v___x_1880_ == 0)
{
lean_object* v___x_1881_; 
lean_dec(v_cmd_1870_);
v___x_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1881_, 0, v_b_1876_);
return v___x_1881_;
}
else
{
lean_object* v_snd_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_2030_; 
v_snd_1882_ = lean_ctor_get(v_b_1876_, 1);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_b_1876_);
if (v_isSharedCheck_2030_ == 0)
{
lean_object* v_unused_2031_; 
v_unused_2031_ = lean_ctor_get(v_b_1876_, 0);
lean_dec(v_unused_2031_);
v___x_1884_ = v_b_1876_;
v_isShared_1885_ = v_isSharedCheck_2030_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_snd_1882_);
lean_dec(v_b_1876_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_2030_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v_fst_1886_; lean_object* v_snd_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_2029_; 
v_fst_1886_ = lean_ctor_get(v_snd_1882_, 0);
v_snd_1887_ = lean_ctor_get(v_snd_1882_, 1);
v_isSharedCheck_2029_ = !lean_is_exclusive(v_snd_1882_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_1889_ = v_snd_1882_;
v_isShared_1890_ = v_isSharedCheck_2029_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_snd_1887_);
lean_inc(v_fst_1886_);
lean_dec(v_snd_1882_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_2029_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v_a_1891_; lean_object* v_pos_1892_; lean_object* v_endPos_1893_; uint8_t v_severity_1894_; lean_object* v_data_1895_; lean_object* v___x_1896_; lean_object* v_a_1898_; 
v_a_1891_ = lean_array_uget_borrowed(v_as_1873_, v_i_1875_);
v_pos_1892_ = lean_ctor_get(v_a_1891_, 1);
v_endPos_1893_ = lean_ctor_get(v_a_1891_, 2);
lean_inc(v_endPos_1893_);
v_severity_1894_ = lean_ctor_get_uint8(v_a_1891_, sizeof(void*)*5 + 1);
v_data_1895_ = lean_ctor_get(v_a_1891_, 4);
v___x_1896_ = lean_box(0);
if (v_severity_1894_ == 2)
{
lean_object* v___f_1911_; uint8_t v___x_1912_; 
v___f_1911_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
lean_inc(v_data_1895_);
v___x_1912_ = l_Lean_MessageData_hasTag(v___f_1911_, v_data_1895_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; 
lean_dec(v_endPos_1893_);
lean_del_object(v___x_1884_);
v___x_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1913_, 0, v_fst_1886_);
lean_ctor_set(v___x_1913_, 1, v_snd_1887_);
v_a_1898_ = v___x_1913_;
goto v___jp_1897_;
}
else
{
if (lean_obj_tag(v_endPos_1893_) == 1)
{
lean_object* v_val_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_2026_; 
v_val_1914_ = lean_ctor_get(v_endPos_1893_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_endPos_1893_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_1916_ = v_endPos_1893_;
v_isShared_1917_ = v_isSharedCheck_2026_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_val_1914_);
lean_dec(v_endPos_1893_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_2026_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; uint8_t v___x_1922_; 
lean_inc_ref(v_pos_1892_);
v___x_1918_ = l_Lean_FileMap_ofPosition(v___x_1868_, v_pos_1892_);
v___x_1919_ = l_Lean_FileMap_ofPosition(v___x_1868_, v_val_1914_);
lean_inc(v___x_1919_);
lean_inc(v___x_1918_);
v___x_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1918_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = 0;
v___x_1922_ = l_Lean_Syntax_Range_includes(v_val_1869_, v___x_1920_, v___x_1921_, v___x_1921_);
if (v___x_1922_ == 0)
{
lean_object* v___x_1923_; 
lean_dec_ref_known(v___x_1920_, 2);
lean_dec(v___x_1919_);
lean_dec(v___x_1918_);
lean_del_object(v___x_1916_);
lean_del_object(v___x_1884_);
v___x_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1923_, 0, v_fst_1886_);
lean_ctor_set(v___x_1923_, 1, v_snd_1887_);
v_a_1898_ = v___x_1923_;
goto v___jp_1897_;
}
else
{
lean_object* v___x_1924_; 
lean_inc(v_cmd_1870_);
lean_inc_ref(v___x_1920_);
v___x_1924_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1920_, v_cmd_1870_);
if (lean_obj_tag(v___x_1924_) == 1)
{
lean_object* v_val_1925_; lean_object* v_fst_1926_; lean_object* v_snd_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1990_; 
lean_dec(v___x_1919_);
lean_dec(v___x_1918_);
lean_del_object(v___x_1916_);
v_val_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_val_1925_);
lean_dec_ref_known(v___x_1924_, 1);
v_fst_1926_ = lean_ctor_get(v_val_1925_, 0);
v_snd_1927_ = lean_ctor_get(v_val_1925_, 1);
v_isSharedCheck_1990_ = !lean_is_exclusive(v_val_1925_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1929_ = v_val_1925_;
v_isShared_1930_ = v_isSharedCheck_1990_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_snd_1927_);
lean_inc(v_fst_1926_);
lean_dec(v_val_1925_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1990_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; uint8_t v___y_1988_; lean_object* v___x_1989_; 
v___x_1989_ = l_Lean_Syntax_getPos_x3f(v_fst_1926_, v___x_1921_);
if (lean_obj_tag(v___x_1989_) == 0)
{
v___y_1988_ = v___x_1922_;
goto v___jp_1987_;
}
else
{
lean_dec_ref_known(v___x_1989_, 1);
v___y_1988_ = v___x_1921_;
goto v___jp_1987_;
}
v___jp_1931_:
{
lean_object* v___x_1937_; 
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 1, v_snd_1887_);
lean_ctor_set(v___x_1929_, 0, v_fst_1886_);
v___x_1937_ = v___x_1929_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_fst_1886_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_snd_1887_);
v___x_1937_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
size_t v_sz_1938_; size_t v___x_1939_; lean_object* v___x_1940_; 
v_sz_1938_ = lean_array_size(v___y_1932_);
v___x_1939_ = ((size_t)0ULL);
v___x_1940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1920_, v_fst_1926_, v_snd_1927_, v___y_1933_, v___y_1932_, v_sz_1938_, v___x_1939_, v___x_1937_);
lean_dec_ref(v___y_1932_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; lean_object* v_fst_1942_; lean_object* v_snd_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_a_1941_);
lean_dec_ref_known(v___x_1940_, 1);
v_fst_1942_ = lean_ctor_get(v_a_1941_, 0);
v_snd_1943_ = lean_ctor_get(v_a_1941_, 1);
v_isSharedCheck_1950_ = !lean_is_exclusive(v_a_1941_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v_a_1941_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_snd_1943_);
lean_inc(v_fst_1942_);
lean_dec(v_a_1941_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_fst_1942_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_snd_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
v_a_1898_ = v___x_1948_;
goto v___jp_1897_;
}
}
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
lean_del_object(v___x_1889_);
lean_dec(v_cmd_1870_);
v_a_1951_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1940_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1940_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
}
v___jp_1960_:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; uint8_t v___x_1965_; 
lean_inc_ref(v___x_1920_);
v___x_1961_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1920_);
v___x_1962_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1895_);
v___x_1963_ = lean_array_get_size(v___x_1962_);
v___x_1964_ = lean_unsigned_to_nat(0u);
v___x_1965_ = lean_nat_dec_eq(v___x_1963_, v___x_1964_);
if (v___x_1965_ == 0)
{
v___y_1932_ = v___x_1962_;
v___y_1933_ = v___x_1961_;
v___y_1934_ = v___y_1877_;
v___y_1935_ = v___y_1878_;
goto v___jp_1931_;
}
else
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v_scopes_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v_opts_1972_; uint8_t v_hasTrace_1973_; 
v___x_1966_ = l_Lean_inheritedTraceOptions;
v___x_1967_ = lean_st_ref_get(v___x_1966_);
v___x_1968_ = lean_st_ref_get(v___y_1878_);
v_scopes_1969_ = lean_ctor_get(v___x_1968_, 2);
lean_inc(v_scopes_1969_);
lean_dec(v___x_1968_);
v___x_1970_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1971_ = l_List_head_x21___redArg(v___x_1970_, v_scopes_1969_);
lean_dec(v_scopes_1969_);
v_opts_1972_ = lean_ctor_get(v___x_1971_, 1);
lean_inc_ref(v_opts_1972_);
lean_dec(v___x_1971_);
v_hasTrace_1973_ = lean_ctor_get_uint8(v_opts_1972_, sizeof(void*)*1);
if (v_hasTrace_1973_ == 0)
{
lean_dec_ref(v_opts_1972_);
lean_dec(v___x_1967_);
v___y_1932_ = v___x_1962_;
v___y_1933_ = v___x_1961_;
v___y_1934_ = v___y_1877_;
v___y_1935_ = v___y_1878_;
goto v___jp_1931_;
}
else
{
lean_object* v___x_1974_; lean_object* v___x_1975_; uint8_t v___x_1976_; 
v___x_1974_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1975_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1976_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1967_, v_opts_1972_, v___x_1975_);
lean_dec_ref(v_opts_1972_);
lean_dec(v___x_1967_);
if (v___x_1976_ == 0)
{
v___y_1932_ = v___x_1962_;
v___y_1933_ = v___x_1961_;
v___y_1934_ = v___y_1877_;
v___y_1935_ = v___y_1878_;
goto v___jp_1931_;
}
else
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5);
v___x_1978_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1974_, v___x_1977_, v___y_1877_, v___y_1878_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_dec_ref_known(v___x_1978_, 1);
v___y_1932_ = v___x_1962_;
v___y_1933_ = v___x_1961_;
v___y_1934_ = v___y_1877_;
v___y_1935_ = v___y_1878_;
goto v___jp_1931_;
}
else
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
lean_dec_ref(v___x_1962_);
lean_dec(v___x_1961_);
lean_del_object(v___x_1929_);
lean_dec(v_snd_1927_);
lean_dec(v_fst_1926_);
lean_dec_ref_known(v___x_1920_, 2);
lean_del_object(v___x_1889_);
lean_dec(v_snd_1887_);
lean_dec(v_fst_1886_);
lean_dec(v_cmd_1870_);
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1981_ = v___x_1978_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1978_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1979_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
}
}
}
v___jp_1987_:
{
if (v_onUnsolved_1871_ == 0)
{
if (v___y_1872_ == 0)
{
lean_del_object(v___x_1929_);
lean_dec(v_snd_1927_);
lean_dec(v_fst_1926_);
lean_dec_ref_known(v___x_1920_, 2);
goto v___jp_1905_;
}
else
{
if (v___y_1988_ == 0)
{
lean_del_object(v___x_1929_);
lean_dec(v_snd_1927_);
lean_dec(v_fst_1926_);
lean_dec_ref_known(v___x_1920_, 2);
goto v___jp_1905_;
}
else
{
lean_del_object(v___x_1884_);
goto v___jp_1960_;
}
}
}
else
{
lean_del_object(v___x_1884_);
goto v___jp_1960_;
}
}
}
}
else
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v_scopes_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v_opts_1997_; uint8_t v_hasTrace_1998_; 
lean_dec(v___x_1924_);
lean_dec_ref_known(v___x_1920_, 2);
lean_del_object(v___x_1884_);
v___x_1991_ = l_Lean_inheritedTraceOptions;
v___x_1992_ = lean_st_ref_get(v___x_1991_);
v___x_1993_ = lean_st_ref_get(v___y_1878_);
v_scopes_1994_ = lean_ctor_get(v___x_1993_, 2);
lean_inc(v_scopes_1994_);
lean_dec(v___x_1993_);
v___x_1995_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1996_ = l_List_head_x21___redArg(v___x_1995_, v_scopes_1994_);
lean_dec(v_scopes_1994_);
v_opts_1997_ = lean_ctor_get(v___x_1996_, 1);
lean_inc_ref(v_opts_1997_);
lean_dec(v___x_1996_);
v_hasTrace_1998_ = lean_ctor_get_uint8(v_opts_1997_, sizeof(void*)*1);
if (v_hasTrace_1998_ == 0)
{
lean_dec_ref(v_opts_1997_);
lean_dec(v___x_1992_);
lean_dec(v___x_1919_);
lean_dec(v___x_1918_);
lean_del_object(v___x_1916_);
goto v___jp_1909_;
}
else
{
lean_object* v___x_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; 
v___x_1999_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2000_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_2001_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1992_, v_opts_1997_, v___x_2000_);
lean_dec_ref(v_opts_1997_);
lean_dec(v___x_1992_);
if (v___x_2001_ == 0)
{
lean_dec(v___x_1919_);
lean_dec(v___x_1918_);
lean_del_object(v___x_1916_);
goto v___jp_1909_;
}
else
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_2002_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7);
v___x_2003_ = l_Nat_reprFast(v___x_1918_);
if (v_isShared_1917_ == 0)
{
lean_ctor_set_tag(v___x_1916_, 3);
lean_ctor_set(v___x_1916_, 0, v___x_2003_);
v___x_2005_ = v___x_1916_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2003_);
v___x_2005_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2006_ = l_Lean_MessageData_ofFormat(v___x_2005_);
v___x_2007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2002_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
v___x_2008_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9);
v___x_2009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2007_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
v___x_2010_ = l_Nat_reprFast(v___x_1919_);
v___x_2011_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
v___x_2012_ = l_Lean_MessageData_ofFormat(v___x_2011_);
v___x_2013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2009_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
v___x_2014_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11);
v___x_2015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2013_);
lean_ctor_set(v___x_2015_, 1, v___x_2014_);
v___x_2016_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1999_, v___x_2015_, v___y_1877_, v___y_1878_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_dec_ref_known(v___x_2016_, 1);
goto v___jp_1909_;
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_del_object(v___x_1889_);
lean_dec(v_snd_1887_);
lean_dec(v_fst_1886_);
lean_dec(v_cmd_1870_);
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_2016_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2016_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
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
lean_object* v___x_2027_; 
lean_dec(v_endPos_1893_);
lean_del_object(v___x_1884_);
v___x_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2027_, 0, v_fst_1886_);
lean_ctor_set(v___x_2027_, 1, v_snd_1887_);
v_a_1898_ = v___x_2027_;
goto v___jp_1897_;
}
}
}
else
{
lean_object* v___x_2028_; 
lean_dec(v_endPos_1893_);
lean_del_object(v___x_1884_);
v___x_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2028_, 0, v_fst_1886_);
lean_ctor_set(v___x_2028_, 1, v_snd_1887_);
v_a_1898_ = v___x_2028_;
goto v___jp_1897_;
}
v___jp_1897_:
{
lean_object* v___x_1900_; 
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 1, v_a_1898_);
lean_ctor_set(v___x_1889_, 0, v___x_1896_);
v___x_1900_ = v___x_1889_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1896_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v_a_1898_);
v___x_1900_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
size_t v___x_1901_; size_t v___x_1902_; lean_object* v___x_1903_; 
v___x_1901_ = ((size_t)1ULL);
v___x_1902_ = lean_usize_add(v_i_1875_, v___x_1901_);
v___x_1903_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10_spec__12(v___x_1868_, v_val_1869_, v_cmd_1870_, v_onUnsolved_1871_, v___y_1872_, v_as_1873_, v_sz_1874_, v___x_1902_, v___x_1900_, v___y_1877_, v___y_1878_);
return v___x_1903_;
}
}
v___jp_1905_:
{
lean_object* v___x_1907_; 
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 1, v_snd_1887_);
lean_ctor_set(v___x_1884_, 0, v_fst_1886_);
v___x_1907_ = v___x_1884_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_fst_1886_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_snd_1887_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
v_a_1898_ = v___x_1907_;
goto v___jp_1897_;
}
}
v___jp_1909_:
{
lean_object* v___x_1910_; 
v___x_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1910_, 0, v_fst_1886_);
lean_ctor_set(v___x_1910_, 1, v_snd_1887_);
v_a_1898_ = v___x_1910_;
goto v___jp_1897_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10___boxed(lean_object* v___x_2032_, lean_object* v_val_2033_, lean_object* v_cmd_2034_, lean_object* v_onUnsolved_2035_, lean_object* v___y_2036_, lean_object* v_as_2037_, lean_object* v_sz_2038_, lean_object* v_i_2039_, lean_object* v_b_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
uint8_t v_onUnsolved_boxed_2044_; uint8_t v___y_12929__boxed_2045_; size_t v_sz_boxed_2046_; size_t v_i_boxed_2047_; lean_object* v_res_2048_; 
v_onUnsolved_boxed_2044_ = lean_unbox(v_onUnsolved_2035_);
v___y_12929__boxed_2045_ = lean_unbox(v___y_2036_);
v_sz_boxed_2046_ = lean_unbox_usize(v_sz_2038_);
lean_dec(v_sz_2038_);
v_i_boxed_2047_ = lean_unbox_usize(v_i_2039_);
lean_dec(v_i_2039_);
v_res_2048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10(v___x_2032_, v_val_2033_, v_cmd_2034_, v_onUnsolved_boxed_2044_, v___y_12929__boxed_2045_, v_as_2037_, v_sz_boxed_2046_, v_i_boxed_2047_, v_b_2040_, v___y_2041_, v___y_2042_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec_ref(v_as_2037_);
lean_dec_ref(v_val_2033_);
lean_dec_ref(v___x_2032_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(lean_object* v_init_2049_, lean_object* v___x_2050_, lean_object* v_val_2051_, lean_object* v_cmd_2052_, uint8_t v_onUnsolved_2053_, uint8_t v___y_2054_, lean_object* v_n_2055_, lean_object* v_b_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
if (lean_obj_tag(v_n_2055_) == 0)
{
lean_object* v_cs_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; size_t v_sz_2063_; size_t v___x_2064_; lean_object* v___x_2065_; 
v_cs_2060_ = lean_ctor_get(v_n_2055_, 0);
v___x_2061_ = lean_box(0);
v___x_2062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
lean_ctor_set(v___x_2062_, 1, v_b_2056_);
v_sz_2063_ = lean_array_size(v_cs_2060_);
v___x_2064_ = ((size_t)0ULL);
v___x_2065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__9(v_init_2049_, v___x_2050_, v_val_2051_, v_cmd_2052_, v_onUnsolved_2053_, v___y_2054_, v_cs_2060_, v_sz_2063_, v___x_2064_, v___x_2062_, v___y_2057_, v___y_2058_);
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
else
{
lean_object* v_vs_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; size_t v_sz_2092_; size_t v___x_2093_; lean_object* v___x_2094_; 
v_vs_2089_ = lean_ctor_get(v_n_2055_, 0);
v___x_2090_ = lean_box(0);
v___x_2091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
lean_ctor_set(v___x_2091_, 1, v_b_2056_);
v_sz_2092_ = lean_array_size(v_vs_2089_);
v___x_2093_ = ((size_t)0ULL);
v___x_2094_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10(v___x_2050_, v_val_2051_, v_cmd_2052_, v_onUnsolved_2053_, v___y_2054_, v_vs_2089_, v_sz_2092_, v___x_2093_, v___x_2091_, v___y_2057_, v___y_2058_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2109_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2109_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2109_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v_fst_2099_; 
v_fst_2099_ = lean_ctor_get(v_a_2095_, 0);
if (lean_obj_tag(v_fst_2099_) == 0)
{
lean_object* v_snd_2100_; lean_object* v___x_2101_; lean_object* v___x_2103_; 
v_snd_2100_ = lean_ctor_get(v_a_2095_, 1);
lean_inc(v_snd_2100_);
lean_dec(v_a_2095_);
v___x_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2101_, 0, v_snd_2100_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2101_);
v___x_2103_ = v___x_2097_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2101_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
else
{
lean_object* v_val_2105_; lean_object* v___x_2107_; 
lean_inc_ref(v_fst_2099_);
lean_dec(v_a_2095_);
v_val_2105_ = lean_ctor_get(v_fst_2099_, 0);
lean_inc(v_val_2105_);
lean_dec_ref_known(v_fst_2099_, 1);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v_val_2105_);
v___x_2107_ = v___x_2097_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_val_2105_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
v_a_2110_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2094_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2094_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__9(lean_object* v_init_2118_, lean_object* v___x_2119_, lean_object* v_val_2120_, lean_object* v_cmd_2121_, uint8_t v_onUnsolved_2122_, uint8_t v___y_2123_, lean_object* v_as_2124_, size_t v_sz_2125_, size_t v_i_2126_, lean_object* v_b_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
uint8_t v___x_2131_; 
v___x_2131_ = lean_usize_dec_lt(v_i_2126_, v_sz_2125_);
if (v___x_2131_ == 0)
{
lean_object* v___x_2132_; 
lean_dec(v_cmd_2121_);
v___x_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2132_, 0, v_b_2127_);
return v___x_2132_;
}
else
{
lean_object* v_snd_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2167_; 
v_snd_2133_ = lean_ctor_get(v_b_2127_, 1);
v_isSharedCheck_2167_ = !lean_is_exclusive(v_b_2127_);
if (v_isSharedCheck_2167_ == 0)
{
lean_object* v_unused_2168_; 
v_unused_2168_ = lean_ctor_get(v_b_2127_, 0);
lean_dec(v_unused_2168_);
v___x_2135_ = v_b_2127_;
v_isShared_2136_ = v_isSharedCheck_2167_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_snd_2133_);
lean_dec(v_b_2127_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2167_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v_a_2137_; lean_object* v___x_2138_; 
v_a_2137_ = lean_array_uget_borrowed(v_as_2124_, v_i_2126_);
lean_inc(v_snd_2133_);
lean_inc(v_cmd_2121_);
v___x_2138_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(v_init_2118_, v___x_2119_, v_val_2120_, v_cmd_2121_, v_onUnsolved_2122_, v___y_2123_, v_a_2137_, v_snd_2133_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2158_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2141_ = v___x_2138_;
v_isShared_2142_ = v_isSharedCheck_2158_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2138_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2158_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
if (lean_obj_tag(v_a_2139_) == 0)
{
lean_object* v___x_2143_; lean_object* v___x_2145_; 
lean_dec(v_cmd_2121_);
v___x_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2143_, 0, v_a_2139_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v___x_2143_);
v___x_2145_ = v___x_2135_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2143_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_snd_2133_);
v___x_2145_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
lean_object* v___x_2147_; 
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 0, v___x_2145_);
v___x_2147_ = v___x_2141_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2145_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
else
{
lean_object* v_a_2150_; lean_object* v___x_2151_; lean_object* v___x_2153_; 
lean_del_object(v___x_2141_);
lean_dec(v_snd_2133_);
v_a_2150_ = lean_ctor_get(v_a_2139_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v_a_2139_, 1);
v___x_2151_ = lean_box(0);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 1, v_a_2150_);
lean_ctor_set(v___x_2135_, 0, v___x_2151_);
v___x_2153_ = v___x_2135_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2151_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_a_2150_);
v___x_2153_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
size_t v___x_2154_; size_t v___x_2155_; 
v___x_2154_ = ((size_t)1ULL);
v___x_2155_ = lean_usize_add(v_i_2126_, v___x_2154_);
v_i_2126_ = v___x_2155_;
v_b_2127_ = v___x_2153_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_del_object(v___x_2135_);
lean_dec(v_snd_2133_);
lean_dec(v_cmd_2121_);
v_a_2159_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2138_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2138_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__9___boxed(lean_object* v_init_2169_, lean_object* v___x_2170_, lean_object* v_val_2171_, lean_object* v_cmd_2172_, lean_object* v_onUnsolved_2173_, lean_object* v___y_2174_, lean_object* v_as_2175_, lean_object* v_sz_2176_, lean_object* v_i_2177_, lean_object* v_b_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
uint8_t v_onUnsolved_boxed_2182_; uint8_t v___y_13230__boxed_2183_; size_t v_sz_boxed_2184_; size_t v_i_boxed_2185_; lean_object* v_res_2186_; 
v_onUnsolved_boxed_2182_ = lean_unbox(v_onUnsolved_2173_);
v___y_13230__boxed_2183_ = lean_unbox(v___y_2174_);
v_sz_boxed_2184_ = lean_unbox_usize(v_sz_2176_);
lean_dec(v_sz_2176_);
v_i_boxed_2185_ = lean_unbox_usize(v_i_2177_);
lean_dec(v_i_2177_);
v_res_2186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__9(v_init_2169_, v___x_2170_, v_val_2171_, v_cmd_2172_, v_onUnsolved_boxed_2182_, v___y_13230__boxed_2183_, v_as_2175_, v_sz_boxed_2184_, v_i_boxed_2185_, v_b_2178_, v___y_2179_, v___y_2180_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec_ref(v_as_2175_);
lean_dec_ref(v_val_2171_);
lean_dec_ref(v___x_2170_);
lean_dec_ref(v_init_2169_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___boxed(lean_object* v_init_2187_, lean_object* v___x_2188_, lean_object* v_val_2189_, lean_object* v_cmd_2190_, lean_object* v_onUnsolved_2191_, lean_object* v___y_2192_, lean_object* v_n_2193_, lean_object* v_b_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
uint8_t v_onUnsolved_boxed_2198_; uint8_t v___y_13252__boxed_2199_; lean_object* v_res_2200_; 
v_onUnsolved_boxed_2198_ = lean_unbox(v_onUnsolved_2191_);
v___y_13252__boxed_2199_ = lean_unbox(v___y_2192_);
v_res_2200_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(v_init_2187_, v___x_2188_, v_val_2189_, v_cmd_2190_, v_onUnsolved_boxed_2198_, v___y_13252__boxed_2199_, v_n_2193_, v_b_2194_, v___y_2195_, v___y_2196_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec_ref(v_n_2193_);
lean_dec_ref(v_val_2189_);
lean_dec_ref(v___x_2188_);
lean_dec_ref(v_init_2187_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(lean_object* v___x_2201_, lean_object* v_val_2202_, lean_object* v_cmd_2203_, uint8_t v_onUnsolved_2204_, uint8_t v___y_2205_, lean_object* v_t_2206_, lean_object* v_init_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v_root_2211_; lean_object* v_tail_2212_; lean_object* v___x_2213_; 
v_root_2211_ = lean_ctor_get(v_t_2206_, 0);
v_tail_2212_ = lean_ctor_get(v_t_2206_, 1);
lean_inc(v_cmd_2203_);
lean_inc_ref(v_init_2207_);
v___x_2213_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(v_init_2207_, v___x_2201_, v_val_2202_, v_cmd_2203_, v_onUnsolved_2204_, v___y_2205_, v_root_2211_, v_init_2207_, v___y_2208_, v___y_2209_);
lean_dec_ref(v_init_2207_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2250_; 
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2216_ = v___x_2213_;
v_isShared_2217_ = v_isSharedCheck_2250_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2213_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2250_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
if (lean_obj_tag(v_a_2214_) == 0)
{
lean_object* v_a_2218_; lean_object* v___x_2220_; 
lean_dec(v_cmd_2203_);
v_a_2218_ = lean_ctor_get(v_a_2214_, 0);
lean_inc(v_a_2218_);
lean_dec_ref_known(v_a_2214_, 1);
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 0, v_a_2218_);
v___x_2220_ = v___x_2216_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2218_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; size_t v_sz_2225_; size_t v___x_2226_; lean_object* v___x_2227_; 
lean_del_object(v___x_2216_);
v_a_2222_ = lean_ctor_get(v_a_2214_, 0);
lean_inc(v_a_2222_);
lean_dec_ref_known(v_a_2214_, 1);
v___x_2223_ = lean_box(0);
v___x_2224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
lean_ctor_set(v___x_2224_, 1, v_a_2222_);
v_sz_2225_ = lean_array_size(v_tail_2212_);
v___x_2226_ = ((size_t)0ULL);
v___x_2227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8(v___x_2201_, v_val_2202_, v_cmd_2203_, v_onUnsolved_2204_, v___y_2205_, v_tail_2212_, v_sz_2225_, v___x_2226_, v___x_2224_, v___y_2208_, v___y_2209_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2241_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2230_ = v___x_2227_;
v_isShared_2231_ = v_isSharedCheck_2241_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2227_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2241_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v_fst_2232_; 
v_fst_2232_ = lean_ctor_get(v_a_2228_, 0);
if (lean_obj_tag(v_fst_2232_) == 0)
{
lean_object* v_snd_2233_; lean_object* v___x_2235_; 
v_snd_2233_ = lean_ctor_get(v_a_2228_, 1);
lean_inc(v_snd_2233_);
lean_dec(v_a_2228_);
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 0, v_snd_2233_);
v___x_2235_ = v___x_2230_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_snd_2233_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
else
{
lean_object* v_val_2237_; lean_object* v___x_2239_; 
lean_inc_ref(v_fst_2232_);
lean_dec(v_a_2228_);
v_val_2237_ = lean_ctor_get(v_fst_2232_, 0);
lean_inc(v_val_2237_);
lean_dec_ref_known(v_fst_2232_, 1);
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 0, v_val_2237_);
v___x_2239_ = v___x_2230_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_val_2237_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
else
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
v_a_2242_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2244_ = v___x_2227_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2227_);
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
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
lean_dec(v_cmd_2203_);
v_a_2251_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2213_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2213_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___boxed(lean_object* v___x_2259_, lean_object* v_val_2260_, lean_object* v_cmd_2261_, lean_object* v_onUnsolved_2262_, lean_object* v___y_2263_, lean_object* v_t_2264_, lean_object* v_init_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
uint8_t v_onUnsolved_boxed_2269_; uint8_t v___y_13443__boxed_2270_; lean_object* v_res_2271_; 
v_onUnsolved_boxed_2269_ = lean_unbox(v_onUnsolved_2262_);
v___y_13443__boxed_2270_ = lean_unbox(v___y_2263_);
v_res_2271_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_2259_, v_val_2260_, v_cmd_2261_, v_onUnsolved_boxed_2269_, v___y_13443__boxed_2270_, v_t_2264_, v_init_2265_, v___y_2266_, v___y_2267_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec_ref(v_t_2264_);
lean_dec_ref(v_val_2260_);
lean_dec_ref(v___x_2259_);
return v_res_2271_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0(void){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2272_ = lean_box(0);
v___x_2273_ = lean_unsigned_to_nat(16u);
v___x_2274_ = lean_mk_array(v___x_2273_, v___x_2272_);
return v___x_2274_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1(void){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2275_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0);
v___x_2276_ = lean_unsigned_to_nat(0u);
v___x_2277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
lean_ctor_set(v___x_2277_, 1, v___x_2275_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(lean_object* v_cmd_2281_, lean_object* v_opts_2282_, lean_object* v_tree_2283_, lean_object* v_msgs_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_){
_start:
{
uint8_t v___y_2289_; lean_object* v___y_2290_; uint8_t v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; uint8_t v___y_2294_; uint8_t v___y_2320_; uint8_t v___y_2321_; lean_object* v_acc_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___f_2326_; uint8_t v___y_2328_; lean_object* v___x_2335_; uint8_t v___x_2336_; 
v___f_2326_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__2));
v___x_2335_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_2336_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2282_, v___x_2335_);
if (v___x_2336_ == 0)
{
lean_object* v___x_2337_; uint8_t v___x_2338_; 
v___x_2337_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_2338_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2282_, v___x_2337_);
v___y_2328_ = v___x_2338_;
goto v___jp_2327_;
}
else
{
v___y_2328_ = v___x_2336_;
goto v___jp_2327_;
}
v___jp_2288_:
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Lean_Syntax_getRange_x3f(v_cmd_2281_, v___y_2294_);
if (lean_obj_tag(v___x_2295_) == 1)
{
lean_object* v_val_2296_; lean_object* v_fileMap_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v_val_2296_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_val_2296_);
lean_dec_ref_known(v___x_2295_, 1);
v_fileMap_2297_ = lean_ctor_get(v___y_2293_, 1);
v___x_2298_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1);
v___x_2299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___y_2290_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
v___x_2300_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v_fileMap_2297_, v_val_2296_, v_cmd_2281_, v___y_2291_, v___y_2289_, v_msgs_2284_, v___x_2299_, v___y_2293_, v___y_2292_);
lean_dec(v_val_2296_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2309_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2303_ = v___x_2300_;
v_isShared_2304_ = v_isSharedCheck_2309_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2300_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2309_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v_fst_2305_; lean_object* v___x_2307_; 
v_fst_2305_ = lean_ctor_get(v_a_2301_, 0);
lean_inc(v_fst_2305_);
lean_dec(v_a_2301_);
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 0, v_fst_2305_);
v___x_2307_ = v___x_2303_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_fst_2305_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
v_a_2310_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2300_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2300_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
else
{
lean_object* v___x_2318_; 
lean_dec(v___x_2295_);
lean_dec(v_cmd_2281_);
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v___y_2290_);
return v___x_2318_;
}
}
v___jp_2319_:
{
if (v___y_2321_ == 0)
{
if (v___y_2320_ == 0)
{
lean_object* v___x_2325_; 
lean_dec(v_cmd_2281_);
v___x_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2325_, 0, v_acc_2322_);
return v___x_2325_;
}
else
{
v___y_2289_ = v___y_2320_;
v___y_2290_ = v_acc_2322_;
v___y_2291_ = v___y_2321_;
v___y_2292_ = v___y_2324_;
v___y_2293_ = v___y_2323_;
v___y_2294_ = v___y_2320_;
goto v___jp_2288_;
}
}
else
{
v___y_2289_ = v___y_2320_;
v___y_2290_ = v_acc_2322_;
v___y_2291_ = v___y_2321_;
v___y_2292_ = v___y_2324_;
v___y_2293_ = v___y_2323_;
v___y_2294_ = v___y_2321_;
goto v___jp_2288_;
}
}
v___jp_2327_:
{
lean_object* v___x_2329_; uint8_t v_onUnsolved_2330_; lean_object* v___x_2331_; uint8_t v_onSorry_2332_; lean_object* v_acc_2333_; 
v___x_2329_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
v_onUnsolved_2330_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2282_, v___x_2329_);
v___x_2331_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v_onSorry_2332_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2282_, v___x_2331_);
v_acc_2333_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__3));
if (v_onSorry_2332_ == 0)
{
lean_dec_ref(v_tree_2283_);
v___y_2320_ = v___y_2328_;
v___y_2321_ = v_onUnsolved_2330_;
v_acc_2322_ = v_acc_2333_;
v___y_2323_ = v_a_2285_;
v___y_2324_ = v_a_2286_;
goto v___jp_2319_;
}
else
{
lean_object* v_acc_2334_; 
v_acc_2334_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_2326_, v_acc_2333_, v_tree_2283_);
v___y_2320_ = v___y_2328_;
v___y_2321_ = v_onUnsolved_2330_;
v_acc_2322_ = v_acc_2334_;
v___y_2323_ = v_a_2285_;
v___y_2324_ = v_a_2286_;
goto v___jp_2319_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___boxed(lean_object* v_cmd_2339_, lean_object* v_opts_2340_, lean_object* v_tree_2341_, lean_object* v_msgs_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_cmd_2339_, v_opts_2340_, v_tree_2341_, v_msgs_2342_, v_a_2343_, v_a_2344_);
lean_dec(v_a_2344_);
lean_dec_ref(v_a_2343_);
lean_dec_ref(v_msgs_2342_);
lean_dec_ref(v_opts_2340_);
return v_res_2346_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(lean_object* v_00_u03b2_2347_, lean_object* v_m_2348_, lean_object* v_a_2349_){
_start:
{
uint8_t v___x_2350_; 
v___x_2350_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(v_m_2348_, v_a_2349_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___boxed(lean_object* v_00_u03b2_2351_, lean_object* v_m_2352_, lean_object* v_a_2353_){
_start:
{
uint8_t v_res_2354_; lean_object* v_r_2355_; 
v_res_2354_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_00_u03b2_2351_, v_m_2352_, v_a_2353_);
lean_dec_ref(v_a_2353_);
lean_dec_ref(v_m_2352_);
v_r_2355_ = lean_box(v_res_2354_);
return v_r_2355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1(lean_object* v_00_u03b2_2356_, lean_object* v_m_2357_, lean_object* v_a_2358_, lean_object* v_b_2359_){
_start:
{
lean_object* v___x_2360_; 
v___x_2360_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_m_2357_, v_a_2358_, v_b_2359_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2(lean_object* v___x_2361_, lean_object* v_fst_2362_, lean_object* v_snd_2363_, lean_object* v___x_2364_, lean_object* v_as_2365_, size_t v_sz_2366_, size_t v_i_2367_, lean_object* v_b_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_2361_, v_fst_2362_, v_snd_2363_, v___x_2364_, v_as_2365_, v_sz_2366_, v_i_2367_, v_b_2368_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___boxed(lean_object* v___x_2373_, lean_object* v_fst_2374_, lean_object* v_snd_2375_, lean_object* v___x_2376_, lean_object* v_as_2377_, lean_object* v_sz_2378_, lean_object* v_i_2379_, lean_object* v_b_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
size_t v_sz_boxed_2384_; size_t v_i_boxed_2385_; lean_object* v_res_2386_; 
v_sz_boxed_2384_ = lean_unbox_usize(v_sz_2378_);
lean_dec(v_sz_2378_);
v_i_boxed_2385_ = lean_unbox_usize(v_i_2379_);
lean_dec(v_i_2379_);
v_res_2386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2(v___x_2373_, v_fst_2374_, v_snd_2375_, v___x_2376_, v_as_2377_, v_sz_boxed_2384_, v_i_boxed_2385_, v_b_2380_, v___y_2381_, v___y_2382_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec_ref(v_as_2377_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5(lean_object* v_msgData_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(v_msgData_2387_, v___y_2389_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___boxed(lean_object* v_msgData_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5(v_msgData_2392_, v___y_2393_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
return v_res_2396_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0(lean_object* v_00_u03b2_2397_, lean_object* v_a_2398_, lean_object* v_x_2399_){
_start:
{
uint8_t v___x_2400_; 
v___x_2400_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(v_a_2398_, v_x_2399_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2401_, lean_object* v_a_2402_, lean_object* v_x_2403_){
_start:
{
uint8_t v_res_2404_; lean_object* v_r_2405_; 
v_res_2404_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0(v_00_u03b2_2401_, v_a_2402_, v_x_2403_);
lean_dec(v_x_2403_);
lean_dec_ref(v_a_2402_);
v_r_2405_ = lean_box(v_res_2404_);
return v_r_2405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2(lean_object* v_00_u03b2_2406_, lean_object* v_data_2407_){
_start:
{
lean_object* v___x_2408_; 
v___x_2408_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2___redArg(v_data_2407_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2409_, lean_object* v_i_2410_, lean_object* v_source_2411_, lean_object* v_target_2412_){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3___redArg(v_i_2410_, v_source_2411_, v_target_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3_spec__8(lean_object* v_00_u03b2_2414_, lean_object* v_x_2415_, lean_object* v_x_2416_){
_start:
{
lean_object* v___x_2417_; 
v___x_2417_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3_spec__8___redArg(v_x_2415_, v_x_2416_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(lean_object* v_x_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
lean_object* v___x_2426_; 
lean_inc(v___y_2420_);
lean_inc_ref(v___y_2419_);
v___x_2426_ = lean_apply_7(v_x_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, lean_box(0));
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed(lean_object* v_x_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(v_x_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(lean_object* v_mvarId_2436_, lean_object* v_x_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v___f_2445_; lean_object* v___x_2446_; 
lean_inc(v___y_2439_);
lean_inc_ref(v___y_2438_);
v___f_2445_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2445_, 0, v_x_2437_);
lean_closure_set(v___f_2445_, 1, v___y_2438_);
lean_closure_set(v___f_2445_, 2, v___y_2439_);
v___x_2446_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2436_, v___f_2445_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
if (lean_obj_tag(v___x_2446_) == 0)
{
return v___x_2446_;
}
else
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2454_; 
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2449_ = v___x_2446_;
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v___x_2446_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2452_; 
if (v_isShared_2450_ == 0)
{
v___x_2452_ = v___x_2449_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2447_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___boxed(lean_object* v_mvarId_2455_, lean_object* v_x_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2455_, v_x_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(lean_object* v_00_u03b1_2465_, lean_object* v_mvarId_2466_, lean_object* v_x_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2466_, v_x_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed(lean_object* v_00_u03b1_2476_, lean_object* v_mvarId_2477_, lean_object* v_x_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(v_00_u03b1_2476_, v_mvarId_2477_, v_x_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(lean_object* v_____r_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2501_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2501_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___boxed(lean_object* v_____r_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(v_____r_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(lean_object* v_____r_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1___boxed(lean_object* v_____r_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(v_____r_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
return v_res_2528_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(uint8_t v___x_2529_, lean_object* v_x_2530_){
_start:
{
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2___boxed(lean_object* v___x_2531_, lean_object* v_x_2532_){
_start:
{
uint8_t v___x_10973__boxed_2533_; uint8_t v_res_2534_; lean_object* v_r_2535_; 
v___x_10973__boxed_2533_ = lean_unbox(v___x_2531_);
v_res_2534_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(v___x_10973__boxed_2533_, v_x_2532_);
lean_dec(v_x_2532_);
v_r_2535_ = lean_box(v_res_2534_);
return v_r_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(lean_object* v_msgData_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v___x_2542_; lean_object* v_env_2543_; lean_object* v___x_2544_; lean_object* v_toCold_2545_; lean_object* v_mctx_2546_; lean_object* v_lctx_2547_; lean_object* v_options_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2542_ = lean_st_ref_get(v___y_2540_);
v_env_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc_ref(v_env_2543_);
lean_dec(v___x_2542_);
v___x_2544_ = lean_st_ref_get(v___y_2538_);
v_toCold_2545_ = lean_ctor_get(v___y_2539_, 0);
v_mctx_2546_ = lean_ctor_get(v___x_2544_, 0);
lean_inc_ref(v_mctx_2546_);
lean_dec(v___x_2544_);
v_lctx_2547_ = lean_ctor_get(v___y_2537_, 2);
v_options_2548_ = lean_ctor_get(v_toCold_2545_, 2);
lean_inc_ref(v_options_2548_);
lean_inc_ref(v_lctx_2547_);
v___x_2549_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2549_, 0, v_env_2543_);
lean_ctor_set(v___x_2549_, 1, v_mctx_2546_);
lean_ctor_set(v___x_2549_, 2, v_lctx_2547_);
lean_ctor_set(v___x_2549_, 3, v_options_2548_);
v___x_2550_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
lean_ctor_set(v___x_2550_, 1, v_msgData_2536_);
v___x_2551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2550_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2___boxed(lean_object* v_msgData_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msgData_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(lean_object* v_cls_2559_, lean_object* v_msg_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v_ref_2566_; lean_object* v___x_2567_; lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2612_; 
v_ref_2566_ = lean_ctor_get(v___y_2563_, 2);
v___x_2567_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2570_ = v___x_2567_;
v_isShared_2571_ = v_isSharedCheck_2612_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2567_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2612_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; lean_object* v_traceState_2573_; lean_object* v_env_2574_; lean_object* v_nextMacroScope_2575_; lean_object* v_ngen_2576_; lean_object* v_auxDeclNGen_2577_; lean_object* v_cache_2578_; lean_object* v_messages_2579_; lean_object* v_infoState_2580_; lean_object* v_snapshotTasks_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2611_; 
v___x_2572_ = lean_st_ref_take(v___y_2564_);
v_traceState_2573_ = lean_ctor_get(v___x_2572_, 4);
v_env_2574_ = lean_ctor_get(v___x_2572_, 0);
v_nextMacroScope_2575_ = lean_ctor_get(v___x_2572_, 1);
v_ngen_2576_ = lean_ctor_get(v___x_2572_, 2);
v_auxDeclNGen_2577_ = lean_ctor_get(v___x_2572_, 3);
v_cache_2578_ = lean_ctor_get(v___x_2572_, 5);
v_messages_2579_ = lean_ctor_get(v___x_2572_, 6);
v_infoState_2580_ = lean_ctor_get(v___x_2572_, 7);
v_snapshotTasks_2581_ = lean_ctor_get(v___x_2572_, 8);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2583_ = v___x_2572_;
v_isShared_2584_ = v_isSharedCheck_2611_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_snapshotTasks_2581_);
lean_inc(v_infoState_2580_);
lean_inc(v_messages_2579_);
lean_inc(v_cache_2578_);
lean_inc(v_traceState_2573_);
lean_inc(v_auxDeclNGen_2577_);
lean_inc(v_ngen_2576_);
lean_inc(v_nextMacroScope_2575_);
lean_inc(v_env_2574_);
lean_dec(v___x_2572_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2611_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
uint64_t v_tid_2585_; lean_object* v_traces_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2610_; 
v_tid_2585_ = lean_ctor_get_uint64(v_traceState_2573_, sizeof(void*)*1);
v_traces_2586_ = lean_ctor_get(v_traceState_2573_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v_traceState_2573_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2588_ = v_traceState_2573_;
v_isShared_2589_ = v_isSharedCheck_2610_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_traces_2586_);
lean_dec(v_traceState_2573_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2610_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2590_; double v___x_2591_; uint8_t v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2600_; 
v___x_2590_ = lean_box(0);
v___x_2591_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0);
v___x_2592_ = 0;
v___x_2593_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2594_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2594_, 0, v_cls_2559_);
lean_ctor_set(v___x_2594_, 1, v___x_2590_);
lean_ctor_set(v___x_2594_, 2, v___x_2593_);
lean_ctor_set_float(v___x_2594_, sizeof(void*)*3, v___x_2591_);
lean_ctor_set_float(v___x_2594_, sizeof(void*)*3 + 8, v___x_2591_);
lean_ctor_set_uint8(v___x_2594_, sizeof(void*)*3 + 16, v___x_2592_);
v___x_2595_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__1));
v___x_2596_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2594_);
lean_ctor_set(v___x_2596_, 1, v_a_2568_);
lean_ctor_set(v___x_2596_, 2, v___x_2595_);
lean_inc(v_ref_2566_);
v___x_2597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2597_, 0, v_ref_2566_);
lean_ctor_set(v___x_2597_, 1, v___x_2596_);
v___x_2598_ = l_Lean_PersistentArray_push___redArg(v_traces_2586_, v___x_2597_);
if (v_isShared_2589_ == 0)
{
lean_ctor_set(v___x_2588_, 0, v___x_2598_);
v___x_2600_ = v___x_2588_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2598_);
lean_ctor_set_uint64(v_reuseFailAlloc_2609_, sizeof(void*)*1, v_tid_2585_);
v___x_2600_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
lean_object* v___x_2602_; 
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 4, v___x_2600_);
v___x_2602_ = v___x_2583_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_env_2574_);
lean_ctor_set(v_reuseFailAlloc_2608_, 1, v_nextMacroScope_2575_);
lean_ctor_set(v_reuseFailAlloc_2608_, 2, v_ngen_2576_);
lean_ctor_set(v_reuseFailAlloc_2608_, 3, v_auxDeclNGen_2577_);
lean_ctor_set(v_reuseFailAlloc_2608_, 4, v___x_2600_);
lean_ctor_set(v_reuseFailAlloc_2608_, 5, v_cache_2578_);
lean_ctor_set(v_reuseFailAlloc_2608_, 6, v_messages_2579_);
lean_ctor_set(v_reuseFailAlloc_2608_, 7, v_infoState_2580_);
lean_ctor_set(v_reuseFailAlloc_2608_, 8, v_snapshotTasks_2581_);
v___x_2602_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2606_; 
v___x_2603_ = lean_st_ref_put(v___y_2564_, v___x_2602_);
v___x_2604_ = lean_box(0);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 0, v___x_2604_);
v___x_2606_ = v___x_2570_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2604_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg___boxed(lean_object* v_cls_2613_, lean_object* v_msg_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_2613_, v_msg_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
return v_res_2620_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2622_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__0));
v___x_2623_ = l_Lean_stringToMessageData(v___x_2622_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(lean_object* v___x_2624_, lean_object* v___x_2625_, lean_object* v___x_2626_, lean_object* v___f_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v___x_2635_; lean_object* v_a_2637_; lean_object* v___y_2641_; lean_object* v___x_2655_; 
v___x_2635_ = lean_st_mk_ref(v___x_2624_);
v___x_2655_ = l_Lean_Elab_Tactic_saveState___redArg(v___x_2635_, v___y_2629_, v___y_2631_, v___y_2633_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; lean_object* v___x_2657_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2656_);
lean_dec_ref_known(v___x_2655_, 1);
v___x_2657_ = l_Lean_Elab_Tactic_Try_collectTryCoreSuggestions(v___x_2625_, v___x_2626_, v___x_2635_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; 
lean_dec(v_a_2656_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec_ref(v___f_2627_);
lean_dec_ref(v___x_2626_);
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2658_);
lean_dec_ref_known(v___x_2657_, 1);
v_a_2637_ = v_a_2658_;
goto v___jp_2636_;
}
else
{
lean_object* v_a_2659_; uint8_t v___y_2661_; uint8_t v___x_2705_; 
v_a_2659_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2659_);
v___x_2705_ = l_Lean_Exception_isInterrupt(v_a_2659_);
if (v___x_2705_ == 0)
{
uint8_t v___x_2706_; 
lean_inc(v_a_2659_);
v___x_2706_ = l_Lean_Exception_isRuntime(v_a_2659_);
v___y_2661_ = v___x_2706_;
goto v___jp_2660_;
}
else
{
v___y_2661_ = v___x_2705_;
goto v___jp_2660_;
}
v___jp_2660_:
{
if (v___y_2661_ == 0)
{
lean_object* v___x_2662_; 
lean_dec_ref_known(v___x_2657_, 1);
v___x_2662_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2656_, v___y_2661_, v___x_2635_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2695_; 
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2695_ == 0)
{
lean_object* v_unused_2696_; 
v_unused_2696_ = lean_ctor_get(v___x_2662_, 0);
lean_dec(v_unused_2696_);
v___x_2664_ = v___x_2662_;
v_isShared_2665_ = v_isSharedCheck_2695_;
goto v_resetjp_2663_;
}
else
{
lean_dec(v___x_2662_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2695_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
uint8_t v___x_2666_; 
v___x_2666_ = l_Lean_Exception_isInterrupt(v_a_2659_);
if (v___x_2666_ == 0)
{
uint8_t v___x_2667_; 
lean_inc(v_a_2659_);
v___x_2667_ = l_Lean_Exception_isMaxRecDepth(v_a_2659_);
if (v___x_2667_ == 0)
{
lean_object* v_toCold_2668_; lean_object* v_options_2669_; uint8_t v_hasTrace_2670_; 
lean_del_object(v___x_2664_);
v_toCold_2668_ = lean_ctor_get(v___y_2632_, 0);
v_options_2669_ = lean_ctor_get(v_toCold_2668_, 2);
v_hasTrace_2670_ = lean_ctor_get_uint8(v_options_2669_, sizeof(void*)*1);
if (v_hasTrace_2670_ == 0)
{
lean_dec(v_a_2659_);
goto v___jp_2652_;
}
else
{
lean_object* v_inheritedTraceOptions_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; uint8_t v___x_2674_; 
v_inheritedTraceOptions_2671_ = lean_ctor_get(v_toCold_2668_, 11);
v___x_2672_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2673_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_2674_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2671_, v_options_2669_, v___x_2673_);
if (v___x_2674_ == 0)
{
lean_dec(v_a_2659_);
goto v___jp_2652_;
}
else
{
lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2675_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_2676_ = l_Lean_Exception_toMessageData(v_a_2659_);
v___x_2677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2675_);
lean_ctor_set(v___x_2677_, 1, v___x_2676_);
v___x_2678_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v___x_2672_, v___x_2677_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v___x_2680_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref_known(v___x_2678_, 1);
lean_inc(v___x_2635_);
v___x_2680_ = lean_apply_10(v___f_2627_, v_a_2679_, v___x_2626_, v___x_2635_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, lean_box(0));
v___y_2641_ = v___x_2680_;
goto v___jp_2640_;
}
else
{
lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2688_; 
lean_dec(v___x_2635_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec_ref(v___f_2627_);
lean_dec_ref(v___x_2626_);
v_a_2681_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2683_ = v___x_2678_;
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2678_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2686_; 
if (v_isShared_2684_ == 0)
{
v___x_2686_ = v___x_2683_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_a_2681_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
}
}
}
else
{
lean_object* v___x_2690_; 
lean_dec(v___x_2635_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec_ref(v___f_2627_);
lean_dec_ref(v___x_2626_);
if (v_isShared_2665_ == 0)
{
lean_ctor_set_tag(v___x_2664_, 1);
lean_ctor_set(v___x_2664_, 0, v_a_2659_);
v___x_2690_ = v___x_2664_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2659_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
else
{
lean_object* v___x_2693_; 
lean_dec(v___x_2635_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec_ref(v___f_2627_);
lean_dec_ref(v___x_2626_);
if (v_isShared_2665_ == 0)
{
lean_ctor_set_tag(v___x_2664_, 1);
lean_ctor_set(v___x_2664_, 0, v_a_2659_);
v___x_2693_ = v___x_2664_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2659_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
else
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2704_; 
lean_dec(v_a_2659_);
lean_dec(v___x_2635_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec_ref(v___f_2627_);
lean_dec_ref(v___x_2626_);
v_a_2697_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2699_ = v___x_2662_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2662_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2702_; 
if (v_isShared_2700_ == 0)
{
v___x_2702_ = v___x_2699_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2697_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
else
{
lean_dec(v_a_2659_);
lean_dec(v_a_2656_);
lean_dec(v___x_2635_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec_ref(v___f_2627_);
lean_dec_ref(v___x_2626_);
return v___x_2657_;
}
}
}
}
else
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
lean_dec(v___x_2635_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec_ref(v___f_2627_);
lean_dec_ref(v___x_2626_);
lean_dec_ref(v___x_2625_);
v_a_2707_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___x_2655_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2655_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2707_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
v___jp_2636_:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2638_ = lean_st_ref_get(v___x_2635_);
lean_dec(v___x_2635_);
lean_dec(v___x_2638_);
v___x_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2639_, 0, v_a_2637_);
return v___x_2639_;
}
v___jp_2640_:
{
if (lean_obj_tag(v___y_2641_) == 0)
{
lean_object* v_a_2642_; lean_object* v_a_2643_; 
v_a_2642_ = lean_ctor_get(v___y_2641_, 0);
lean_inc(v_a_2642_);
lean_dec_ref_known(v___y_2641_, 1);
v_a_2643_ = lean_ctor_get(v_a_2642_, 0);
lean_inc(v_a_2643_);
lean_dec(v_a_2642_);
v_a_2637_ = v_a_2643_;
goto v___jp_2636_;
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec(v___x_2635_);
v_a_2644_ = lean_ctor_get(v___y_2641_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___y_2641_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___y_2641_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___y_2641_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
v___jp_2652_:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = lean_box(0);
lean_inc(v___x_2635_);
v___x_2654_ = lean_apply_10(v___f_2627_, v___x_2653_, v___x_2626_, v___x_2635_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, lean_box(0));
v___y_2641_ = v___x_2654_;
goto v___jp_2640_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed(lean_object* v___x_2715_, lean_object* v___x_2716_, lean_object* v___x_2717_, lean_object* v___f_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(v___x_2715_, v___x_2716_, v___x_2717_, v___f_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(lean_object* v___x_2727_, uint8_t v___x_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2727_, v___x_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed(lean_object* v___x_2737_, lean_object* v___x_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
uint8_t v___x_11302__boxed_2746_; lean_object* v_res_2747_; 
v___x_11302__boxed_2746_ = lean_unbox(v___x_2738_);
v_res_2747_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(v___x_2737_, v___x_11302__boxed_2746_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(lean_object* v_cls_2748_, lean_object* v_msg_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v_ref_2755_; lean_object* v___x_2756_; lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2801_; 
v_ref_2755_ = lean_ctor_get(v___y_2752_, 2);
v___x_2756_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2759_ = v___x_2756_;
v_isShared_2760_ = v_isSharedCheck_2801_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2756_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2801_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2761_; lean_object* v_traceState_2762_; lean_object* v_env_2763_; lean_object* v_nextMacroScope_2764_; lean_object* v_ngen_2765_; lean_object* v_auxDeclNGen_2766_; lean_object* v_cache_2767_; lean_object* v_messages_2768_; lean_object* v_infoState_2769_; lean_object* v_snapshotTasks_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2800_; 
v___x_2761_ = lean_st_ref_take(v___y_2753_);
v_traceState_2762_ = lean_ctor_get(v___x_2761_, 4);
v_env_2763_ = lean_ctor_get(v___x_2761_, 0);
v_nextMacroScope_2764_ = lean_ctor_get(v___x_2761_, 1);
v_ngen_2765_ = lean_ctor_get(v___x_2761_, 2);
v_auxDeclNGen_2766_ = lean_ctor_get(v___x_2761_, 3);
v_cache_2767_ = lean_ctor_get(v___x_2761_, 5);
v_messages_2768_ = lean_ctor_get(v___x_2761_, 6);
v_infoState_2769_ = lean_ctor_get(v___x_2761_, 7);
v_snapshotTasks_2770_ = lean_ctor_get(v___x_2761_, 8);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2772_ = v___x_2761_;
v_isShared_2773_ = v_isSharedCheck_2800_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_snapshotTasks_2770_);
lean_inc(v_infoState_2769_);
lean_inc(v_messages_2768_);
lean_inc(v_cache_2767_);
lean_inc(v_traceState_2762_);
lean_inc(v_auxDeclNGen_2766_);
lean_inc(v_ngen_2765_);
lean_inc(v_nextMacroScope_2764_);
lean_inc(v_env_2763_);
lean_dec(v___x_2761_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2800_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
uint64_t v_tid_2774_; lean_object* v_traces_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2799_; 
v_tid_2774_ = lean_ctor_get_uint64(v_traceState_2762_, sizeof(void*)*1);
v_traces_2775_ = lean_ctor_get(v_traceState_2762_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v_traceState_2762_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2777_ = v_traceState_2762_;
v_isShared_2778_ = v_isSharedCheck_2799_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_traces_2775_);
lean_dec(v_traceState_2762_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2799_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2779_; double v___x_2780_; uint8_t v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2789_; 
v___x_2779_ = lean_box(0);
v___x_2780_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0);
v___x_2781_ = 0;
v___x_2782_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2783_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2783_, 0, v_cls_2748_);
lean_ctor_set(v___x_2783_, 1, v___x_2779_);
lean_ctor_set(v___x_2783_, 2, v___x_2782_);
lean_ctor_set_float(v___x_2783_, sizeof(void*)*3, v___x_2780_);
lean_ctor_set_float(v___x_2783_, sizeof(void*)*3 + 8, v___x_2780_);
lean_ctor_set_uint8(v___x_2783_, sizeof(void*)*3 + 16, v___x_2781_);
v___x_2784_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__1));
v___x_2785_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2783_);
lean_ctor_set(v___x_2785_, 1, v_a_2757_);
lean_ctor_set(v___x_2785_, 2, v___x_2784_);
lean_inc(v_ref_2755_);
v___x_2786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2786_, 0, v_ref_2755_);
lean_ctor_set(v___x_2786_, 1, v___x_2785_);
v___x_2787_ = l_Lean_PersistentArray_push___redArg(v_traces_2775_, v___x_2786_);
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 0, v___x_2787_);
v___x_2789_ = v___x_2777_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2787_);
lean_ctor_set_uint64(v_reuseFailAlloc_2798_, sizeof(void*)*1, v_tid_2774_);
v___x_2789_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
lean_object* v___x_2791_; 
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 4, v___x_2789_);
v___x_2791_ = v___x_2772_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_env_2763_);
lean_ctor_set(v_reuseFailAlloc_2797_, 1, v_nextMacroScope_2764_);
lean_ctor_set(v_reuseFailAlloc_2797_, 2, v_ngen_2765_);
lean_ctor_set(v_reuseFailAlloc_2797_, 3, v_auxDeclNGen_2766_);
lean_ctor_set(v_reuseFailAlloc_2797_, 4, v___x_2789_);
lean_ctor_set(v_reuseFailAlloc_2797_, 5, v_cache_2767_);
lean_ctor_set(v_reuseFailAlloc_2797_, 6, v_messages_2768_);
lean_ctor_set(v_reuseFailAlloc_2797_, 7, v_infoState_2769_);
lean_ctor_set(v_reuseFailAlloc_2797_, 8, v_snapshotTasks_2770_);
v___x_2791_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2795_; 
v___x_2792_ = lean_st_ref_put(v___y_2753_, v___x_2791_);
v___x_2793_ = lean_box(0);
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 0, v___x_2793_);
v___x_2795_ = v___x_2759_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v___x_2793_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3___boxed(lean_object* v_cls_2802_, lean_object* v_msg_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v_cls_2802_, v_msg_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
return v_res_2809_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__0));
v___x_2812_ = l_Lean_stringToMessageData(v___x_2811_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(lean_object* v_term_2813_, lean_object* v___x_2814_, lean_object* v___x_2815_, lean_object* v___f_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v___y_2823_; lean_object* v___x_2841_; 
v___x_2841_ = l_Lean_Elab_Term_TermElabM_run___redArg(v_term_2813_, v___x_2814_, v___x_2815_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2850_; 
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec_ref(v___f_2816_);
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2844_ = v___x_2841_;
v_isShared_2845_ = v_isSharedCheck_2850_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2841_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2850_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v_fst_2846_; lean_object* v___x_2848_; 
v_fst_2846_ = lean_ctor_get(v_a_2842_, 0);
lean_inc(v_fst_2846_);
lean_dec(v_a_2842_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 0, v_fst_2846_);
v___x_2848_ = v___x_2844_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_fst_2846_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2894_; 
v_a_2851_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2853_ = v___x_2841_;
v_isShared_2854_ = v_isSharedCheck_2894_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2841_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2894_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
uint8_t v___y_2859_; uint8_t v___x_2892_; 
v___x_2892_ = l_Lean_Exception_isInterrupt(v_a_2851_);
if (v___x_2892_ == 0)
{
uint8_t v___x_2893_; 
lean_inc(v_a_2851_);
v___x_2893_ = l_Lean_Exception_isRuntime(v_a_2851_);
v___y_2859_ = v___x_2893_;
goto v___jp_2858_;
}
else
{
v___y_2859_ = v___x_2892_;
goto v___jp_2858_;
}
v___jp_2855_:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2856_ = lean_box(0);
v___x_2857_ = lean_apply_6(v___f_2816_, v___x_2856_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, lean_box(0));
v___y_2823_ = v___x_2857_;
goto v___jp_2822_;
}
v___jp_2858_:
{
if (v___y_2859_ == 0)
{
uint8_t v___x_2860_; 
v___x_2860_ = l_Lean_Exception_isInterrupt(v_a_2851_);
if (v___x_2860_ == 0)
{
uint8_t v___x_2861_; 
lean_inc(v_a_2851_);
v___x_2861_ = l_Lean_Exception_isMaxRecDepth(v_a_2851_);
if (v___x_2861_ == 0)
{
lean_object* v_toCold_2862_; lean_object* v_options_2863_; uint8_t v_hasTrace_2864_; 
lean_del_object(v___x_2853_);
v_toCold_2862_ = lean_ctor_get(v___y_2819_, 0);
v_options_2863_ = lean_ctor_get(v_toCold_2862_, 2);
v_hasTrace_2864_ = lean_ctor_get_uint8(v_options_2863_, sizeof(void*)*1);
if (v_hasTrace_2864_ == 0)
{
lean_dec(v_a_2851_);
goto v___jp_2855_;
}
else
{
lean_object* v_inheritedTraceOptions_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; uint8_t v___x_2868_; 
v_inheritedTraceOptions_2865_ = lean_ctor_get(v_toCold_2862_, 11);
v___x_2866_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2867_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_2868_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2865_, v_options_2863_, v___x_2867_);
if (v___x_2868_ == 0)
{
lean_dec(v_a_2851_);
goto v___jp_2855_;
}
else
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2869_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1);
v___x_2870_ = l_Lean_Exception_toMessageData(v_a_2851_);
v___x_2871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2869_);
lean_ctor_set(v___x_2871_, 1, v___x_2870_);
v___x_2872_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_2866_, v___x_2871_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_a_2873_; lean_object* v___x_2874_; 
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_a_2873_);
lean_dec_ref_known(v___x_2872_, 1);
v___x_2874_ = lean_apply_6(v___f_2816_, v_a_2873_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, lean_box(0));
v___y_2823_ = v___x_2874_;
goto v___jp_2822_;
}
else
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec_ref(v___f_2816_);
v_a_2875_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___x_2872_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2872_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
}
}
else
{
lean_object* v___x_2884_; 
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec_ref(v___f_2816_);
if (v_isShared_2854_ == 0)
{
v___x_2884_ = v___x_2853_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2851_);
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
lean_object* v___x_2887_; 
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec_ref(v___f_2816_);
if (v_isShared_2854_ == 0)
{
v___x_2887_ = v___x_2853_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2851_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
else
{
lean_object* v___x_2890_; 
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec_ref(v___f_2816_);
if (v_isShared_2854_ == 0)
{
v___x_2890_ = v___x_2853_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2851_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
}
}
v___jp_2822_:
{
if (lean_obj_tag(v___y_2823_) == 0)
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2832_; 
v_a_2824_ = lean_ctor_get(v___y_2823_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___y_2823_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2826_ = v___y_2823_;
v_isShared_2827_ = v_isSharedCheck_2832_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___y_2823_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2832_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v_a_2828_; lean_object* v___x_2830_; 
v_a_2828_ = lean_ctor_get(v_a_2824_, 0);
lean_inc(v_a_2828_);
lean_dec(v_a_2824_);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 0, v_a_2828_);
v___x_2830_ = v___x_2826_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2828_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
else
{
lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2840_; 
v_a_2833_ = lean_ctor_get(v___y_2823_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___y_2823_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2835_ = v___y_2823_;
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___y_2823_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2838_; 
if (v_isShared_2836_ == 0)
{
v___x_2838_ = v___x_2835_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2833_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___boxed(lean_object* v_term_2895_, lean_object* v___x_2896_, lean_object* v___x_2897_, lean_object* v___f_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(v_term_2895_, v___x_2896_, v___x_2897_, v___f_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_2905_, lean_object* v_vals_2906_, lean_object* v_i_2907_, lean_object* v_k_2908_){
_start:
{
lean_object* v___x_2909_; uint8_t v___x_2910_; 
v___x_2909_ = lean_array_get_size(v_keys_2905_);
v___x_2910_ = lean_nat_dec_lt(v_i_2907_, v___x_2909_);
if (v___x_2910_ == 0)
{
lean_object* v___x_2911_; 
lean_dec(v_i_2907_);
v___x_2911_ = lean_box(0);
return v___x_2911_;
}
else
{
lean_object* v_k_x27_2912_; uint8_t v___x_2913_; 
v_k_x27_2912_ = lean_array_fget_borrowed(v_keys_2905_, v_i_2907_);
v___x_2913_ = l_Lean_instBEqMVarId_beq(v_k_2908_, v_k_x27_2912_);
if (v___x_2913_ == 0)
{
lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2914_ = lean_unsigned_to_nat(1u);
v___x_2915_ = lean_nat_add(v_i_2907_, v___x_2914_);
lean_dec(v_i_2907_);
v_i_2907_ = v___x_2915_;
goto _start;
}
else
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2917_ = lean_array_fget_borrowed(v_vals_2906_, v_i_2907_);
lean_dec(v_i_2907_);
lean_inc(v___x_2917_);
v___x_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2917_);
return v___x_2918_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_2919_, lean_object* v_vals_2920_, lean_object* v_i_2921_, lean_object* v_k_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_keys_2919_, v_vals_2920_, v_i_2921_, v_k_2922_);
lean_dec(v_k_2922_);
lean_dec_ref(v_vals_2920_);
lean_dec_ref(v_keys_2919_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(lean_object* v_x_2924_, size_t v_x_2925_, lean_object* v_x_2926_){
_start:
{
if (lean_obj_tag(v_x_2924_) == 0)
{
lean_object* v_es_2927_; lean_object* v___x_2928_; size_t v___x_2929_; size_t v___x_2930_; lean_object* v_j_2931_; lean_object* v___x_2932_; 
v_es_2927_ = lean_ctor_get(v_x_2924_, 0);
v___x_2928_ = lean_box(2);
v___x_2929_ = ((size_t)31ULL);
v___x_2930_ = lean_usize_land(v_x_2925_, v___x_2929_);
v_j_2931_ = lean_usize_to_nat(v___x_2930_);
v___x_2932_ = lean_array_get_borrowed(v___x_2928_, v_es_2927_, v_j_2931_);
lean_dec(v_j_2931_);
switch(lean_obj_tag(v___x_2932_))
{
case 0:
{
lean_object* v_key_2933_; lean_object* v_val_2934_; uint8_t v___x_2935_; 
v_key_2933_ = lean_ctor_get(v___x_2932_, 0);
v_val_2934_ = lean_ctor_get(v___x_2932_, 1);
v___x_2935_ = l_Lean_instBEqMVarId_beq(v_x_2926_, v_key_2933_);
if (v___x_2935_ == 0)
{
lean_object* v___x_2936_; 
v___x_2936_ = lean_box(0);
return v___x_2936_;
}
else
{
lean_object* v___x_2937_; 
lean_inc(v_val_2934_);
v___x_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2937_, 0, v_val_2934_);
return v___x_2937_;
}
}
case 1:
{
lean_object* v_node_2938_; size_t v___x_2939_; size_t v___x_2940_; 
v_node_2938_ = lean_ctor_get(v___x_2932_, 0);
v___x_2939_ = ((size_t)5ULL);
v___x_2940_ = lean_usize_shift_right(v_x_2925_, v___x_2939_);
v_x_2924_ = v_node_2938_;
v_x_2925_ = v___x_2940_;
goto _start;
}
default: 
{
lean_object* v___x_2942_; 
v___x_2942_ = lean_box(0);
return v___x_2942_;
}
}
}
else
{
lean_object* v_ks_2943_; lean_object* v_vs_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v_ks_2943_ = lean_ctor_get(v_x_2924_, 0);
v_vs_2944_ = lean_ctor_get(v_x_2924_, 1);
v___x_2945_ = lean_unsigned_to_nat(0u);
v___x_2946_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_ks_2943_, v_vs_2944_, v___x_2945_, v_x_2926_);
return v___x_2946_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg___boxed(lean_object* v_x_2947_, lean_object* v_x_2948_, lean_object* v_x_2949_){
_start:
{
size_t v_x_11621__boxed_2950_; lean_object* v_res_2951_; 
v_x_11621__boxed_2950_ = lean_unbox_usize(v_x_2948_);
lean_dec(v_x_2948_);
v_res_2951_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_2947_, v_x_11621__boxed_2950_, v_x_2949_);
lean_dec(v_x_2949_);
lean_dec_ref(v_x_2947_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(lean_object* v_x_2952_, lean_object* v_x_2953_){
_start:
{
uint64_t v___x_2954_; size_t v___x_2955_; lean_object* v___x_2956_; 
v___x_2954_ = l_Lean_instHashableMVarId_hash(v_x_2953_);
v___x_2955_ = lean_uint64_to_usize(v___x_2954_);
v___x_2956_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_2952_, v___x_2955_, v_x_2953_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg___boxed(lean_object* v_x_2957_, lean_object* v_x_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_x_2957_, v_x_2958_);
lean_dec(v_x_2958_);
lean_dec_ref(v_x_2957_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(lean_object* v_c_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_){
_start:
{
lean_object* v_mctx_2989_; lean_object* v_env_2990_; lean_object* v_opts_2991_; lean_object* v_namingCtx_2992_; lean_object* v_goal_2993_; lean_object* v_decls_2994_; lean_object* v___x_2995_; 
v_mctx_2989_ = lean_ctor_get(v_c_2985_, 3);
lean_inc_ref(v_mctx_2989_);
v_env_2990_ = lean_ctor_get(v_c_2985_, 2);
lean_inc_ref(v_env_2990_);
v_opts_2991_ = lean_ctor_get(v_c_2985_, 4);
lean_inc_ref(v_opts_2991_);
v_namingCtx_2992_ = lean_ctor_get(v_c_2985_, 5);
lean_inc_ref(v_namingCtx_2992_);
v_goal_2993_ = lean_ctor_get(v_c_2985_, 6);
lean_inc(v_goal_2993_);
lean_dec_ref(v_c_2985_);
v_decls_2994_ = lean_ctor_get(v_mctx_2989_, 5);
v___x_2995_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_decls_2994_, v_goal_2993_);
if (lean_obj_tag(v___x_2995_) == 1)
{
lean_object* v_val_2996_; lean_object* v_lctx_2997_; lean_object* v___f_2998_; lean_object* v___f_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___f_3004_; lean_object* v___x_3005_; uint8_t v___x_3006_; lean_object* v___x_3007_; lean_object* v_term_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___f_3011_; lean_object* v___x_3012_; 
v_val_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_val_2996_);
lean_dec_ref_known(v___x_2995_, 1);
v_lctx_2997_ = lean_ctor_get(v_val_2996_, 1);
lean_inc_ref(v_lctx_2997_);
lean_dec(v_val_2996_);
v___f_2998_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__0));
v___f_2999_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__1));
v___x_3000_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__3));
v___x_3001_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__4));
v___x_3002_ = lean_box(0);
lean_inc(v_goal_2993_);
v___x_3003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3003_, 0, v_goal_2993_);
lean_ctor_set(v___x_3003_, 1, v___x_3002_);
v___f_3004_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed), 11, 4);
lean_closure_set(v___f_3004_, 0, v___x_3003_);
lean_closure_set(v___f_3004_, 1, v___x_3000_);
lean_closure_set(v___f_3004_, 2, v___x_3001_);
lean_closure_set(v___f_3004_, 3, v___f_2998_);
v___x_3005_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed), 10, 3);
lean_closure_set(v___x_3005_, 0, lean_box(0));
lean_closure_set(v___x_3005_, 1, v_goal_2993_);
lean_closure_set(v___x_3005_, 2, v___f_3004_);
v___x_3006_ = 1;
v___x_3007_ = lean_box(v___x_3006_);
v_term_3008_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed), 9, 2);
lean_closure_set(v_term_3008_, 0, v___x_3005_);
lean_closure_set(v_term_3008_, 1, v___x_3007_);
v___x_3009_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__6));
v___x_3010_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__7));
v___f_3011_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___boxed), 9, 4);
lean_closure_set(v___f_3011_, 0, v_term_3008_);
lean_closure_set(v___f_3011_, 1, v___x_3009_);
lean_closure_set(v___f_3011_, 2, v___x_3010_);
lean_closure_set(v___f_3011_, 3, v___f_2999_);
v___x_3012_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_2990_, v_mctx_2989_, v_lctx_2997_, v_opts_2991_, v_namingCtx_2992_, v___f_3011_, v_a_2986_, v_a_2987_);
lean_dec_ref(v_namingCtx_2992_);
return v___x_3012_;
}
else
{
lean_object* v___x_3013_; lean_object* v___x_3014_; 
lean_dec(v___x_2995_);
lean_dec(v_goal_2993_);
lean_dec_ref(v_namingCtx_2992_);
lean_dec_ref(v_opts_2991_);
lean_dec_ref(v_env_2990_);
lean_dec_ref(v_mctx_2989_);
v___x_3013_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__0));
v___x_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3013_);
return v___x_3014_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___boxed(lean_object* v_c_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(v_c_3015_, v_a_3016_, v_a_3017_);
lean_dec(v_a_3017_);
lean_dec_ref(v_a_3016_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0(lean_object* v_00_u03b2_3020_, lean_object* v_x_3021_, lean_object* v_x_3022_){
_start:
{
lean_object* v___x_3023_; 
v___x_3023_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_x_3021_, v_x_3022_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___boxed(lean_object* v_00_u03b2_3024_, lean_object* v_x_3025_, lean_object* v_x_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0(v_00_u03b2_3024_, v_x_3025_, v_x_3026_);
lean_dec(v_x_3026_);
lean_dec_ref(v_x_3025_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(lean_object* v_cls_3028_, lean_object* v_msg_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
lean_object* v___x_3039_; 
v___x_3039_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_3028_, v_msg_3029_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___boxed(lean_object* v_cls_3040_, lean_object* v_msg_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(v_cls_3040_, v_msg_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
return v_res_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(lean_object* v_00_u03b2_3052_, lean_object* v_x_3053_, size_t v_x_3054_, lean_object* v_x_3055_){
_start:
{
lean_object* v___x_3056_; 
v___x_3056_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_3053_, v_x_3054_, v_x_3055_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3057_, lean_object* v_x_3058_, lean_object* v_x_3059_, lean_object* v_x_3060_){
_start:
{
size_t v_x_11878__boxed_3061_; lean_object* v_res_3062_; 
v_x_11878__boxed_3061_ = lean_unbox_usize(v_x_3059_);
lean_dec(v_x_3059_);
v_res_3062_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(v_00_u03b2_3057_, v_x_3058_, v_x_11878__boxed_3061_, v_x_3060_);
lean_dec(v_x_3060_);
lean_dec_ref(v_x_3058_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3063_, lean_object* v_keys_3064_, lean_object* v_vals_3065_, lean_object* v_heq_3066_, lean_object* v_i_3067_, lean_object* v_k_3068_){
_start:
{
lean_object* v___x_3069_; 
v___x_3069_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_keys_3064_, v_vals_3065_, v_i_3067_, v_k_3068_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3070_, lean_object* v_keys_3071_, lean_object* v_vals_3072_, lean_object* v_heq_3073_, lean_object* v_i_3074_, lean_object* v_k_3075_){
_start:
{
lean_object* v_res_3076_; 
v_res_3076_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2(v_00_u03b2_3070_, v_keys_3071_, v_vals_3072_, v_heq_3073_, v_i_3074_, v_k_3075_);
lean_dec(v_k_3075_);
lean_dec_ref(v_vals_3072_);
lean_dec_ref(v_keys_3071_);
return v_res_3076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(uint8_t v___x_3079_, lean_object* v___x_3080_, lean_object* v_ref_3081_, lean_object* v_a_3082_, lean_object* v___x_3083_, lean_object* v___x_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
if (v___x_3079_ == 0)
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; uint8_t v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3080_);
v___x_3089_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__0));
v___x_3090_ = lean_box(0);
v___x_3091_ = 4;
v___x_3092_ = l_Lean_MessageData_nil;
v___x_3093_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_3081_, v_a_3082_, v___x_3088_, v___x_3089_, v___x_3090_, v___x_3091_, v___x_3092_, v___y_3085_, v___y_3086_);
return v___x_3093_;
}
else
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; uint8_t v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3094_ = lean_array_get(v___x_3083_, v_a_3082_, v___x_3084_);
lean_dec_ref(v_a_3082_);
v___x_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3080_);
v___x_3096_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__1));
v___x_3097_ = lean_box(0);
v___x_3098_ = 4;
v___x_3099_ = l_Lean_MessageData_nil;
v___x_3100_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_3081_, v___x_3094_, v___x_3095_, v___x_3096_, v___x_3097_, v___x_3098_, v___x_3099_, v___y_3085_, v___y_3086_);
return v___x_3100_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed(lean_object* v___x_3101_, lean_object* v___x_3102_, lean_object* v_ref_3103_, lean_object* v_a_3104_, lean_object* v___x_3105_, lean_object* v___x_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_){
_start:
{
uint8_t v___x_3485__boxed_3110_; lean_object* v_res_3111_; 
v___x_3485__boxed_3110_ = lean_unbox(v___x_3101_);
v_res_3111_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(v___x_3485__boxed_3110_, v___x_3102_, v_ref_3103_, v_a_3104_, v___x_3105_, v___x_3106_, v___y_3107_, v___y_3108_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___x_3106_);
lean_dec_ref(v___x_3105_);
return v_res_3111_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_3112_, uint8_t v___y_3113_, lean_object* v_x_3114_){
_start:
{
if (lean_obj_tag(v_x_3114_) == 1)
{
lean_object* v_pre_3115_; 
v_pre_3115_ = lean_ctor_get(v_x_3114_, 0);
if (lean_obj_tag(v_pre_3115_) == 0)
{
lean_object* v_str_3116_; lean_object* v___x_3117_; uint8_t v___x_3118_; 
v_str_3116_ = lean_ctor_get(v_x_3114_, 1);
v___x_3117_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__1));
v___x_3118_ = lean_string_dec_eq(v_str_3116_, v___x_3117_);
if (v___x_3118_ == 0)
{
return v___x_3118_;
}
else
{
return v_suppressElabErrors_3112_;
}
}
else
{
return v___y_3113_;
}
}
else
{
return v___y_3113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_3119_, lean_object* v___y_3120_, lean_object* v_x_3121_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3122_; uint8_t v___y_3538__boxed_3123_; uint8_t v_res_3124_; lean_object* v_r_3125_; 
v_suppressElabErrors_boxed_3122_ = lean_unbox(v_suppressElabErrors_3119_);
v___y_3538__boxed_3123_ = lean_unbox(v___y_3120_);
v_res_3124_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_3122_, v___y_3538__boxed_3123_, v_x_3121_);
lean_dec(v_x_3121_);
v_r_3125_ = lean_box(v_res_3124_);
return v_r_3125_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(lean_object* v_ref_3126_, lean_object* v_msgData_3127_, uint8_t v_severity_3128_, uint8_t v_isSilent_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
lean_object* v___y_3134_; uint8_t v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; uint8_t v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; uint8_t v___y_3199_; uint8_t v___y_3200_; lean_object* v___y_3201_; uint8_t v___y_3202_; lean_object* v___y_3203_; uint8_t v___y_3227_; uint8_t v___y_3228_; lean_object* v___y_3229_; uint8_t v___y_3230_; lean_object* v___y_3231_; uint8_t v___y_3235_; uint8_t v___y_3236_; uint8_t v___y_3237_; uint8_t v___x_3252_; uint8_t v___y_3254_; uint8_t v___y_3255_; uint8_t v___y_3256_; uint8_t v___y_3258_; uint8_t v___x_3270_; 
v___x_3252_ = 2;
v___x_3270_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3128_, v___x_3252_);
if (v___x_3270_ == 0)
{
v___y_3258_ = v___x_3270_;
goto v___jp_3257_;
}
else
{
uint8_t v___x_3271_; 
lean_inc_ref(v_msgData_3127_);
v___x_3271_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3127_);
v___y_3258_ = v___x_3271_;
goto v___jp_3257_;
}
v___jp_3133_:
{
lean_object* v___x_3142_; 
v___x_3142_ = l_Lean_Elab_Command_getScope___redArg(v___y_3141_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v_a_3143_; lean_object* v___x_3144_; 
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc(v_a_3143_);
lean_dec_ref_known(v___x_3142_, 1);
v___x_3144_ = l_Lean_Elab_Command_getScope___redArg(v___y_3141_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3181_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3147_ = v___x_3144_;
v_isShared_3148_ = v_isSharedCheck_3181_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3144_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3181_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3149_; lean_object* v_currNamespace_3150_; lean_object* v_openDecls_3151_; lean_object* v_env_3152_; lean_object* v_messages_3153_; lean_object* v_scopes_3154_; lean_object* v_usedQuotCtxts_3155_; lean_object* v_nextMacroScope_3156_; lean_object* v_maxRecDepth_3157_; lean_object* v_ngen_3158_; lean_object* v_auxDeclNGen_3159_; lean_object* v_infoState_3160_; lean_object* v_traceState_3161_; lean_object* v_snapshotTasks_3162_; lean_object* v_prevLinterStates_3163_; lean_object* v_codeQualityEntryTasks_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3180_; 
v___x_3149_ = lean_st_ref_take(v___y_3141_);
v_currNamespace_3150_ = lean_ctor_get(v_a_3143_, 2);
lean_inc(v_currNamespace_3150_);
lean_dec(v_a_3143_);
v_openDecls_3151_ = lean_ctor_get(v_a_3145_, 3);
lean_inc(v_openDecls_3151_);
lean_dec(v_a_3145_);
v_env_3152_ = lean_ctor_get(v___x_3149_, 0);
v_messages_3153_ = lean_ctor_get(v___x_3149_, 1);
v_scopes_3154_ = lean_ctor_get(v___x_3149_, 2);
v_usedQuotCtxts_3155_ = lean_ctor_get(v___x_3149_, 3);
v_nextMacroScope_3156_ = lean_ctor_get(v___x_3149_, 4);
v_maxRecDepth_3157_ = lean_ctor_get(v___x_3149_, 5);
v_ngen_3158_ = lean_ctor_get(v___x_3149_, 6);
v_auxDeclNGen_3159_ = lean_ctor_get(v___x_3149_, 7);
v_infoState_3160_ = lean_ctor_get(v___x_3149_, 8);
v_traceState_3161_ = lean_ctor_get(v___x_3149_, 9);
v_snapshotTasks_3162_ = lean_ctor_get(v___x_3149_, 10);
v_prevLinterStates_3163_ = lean_ctor_get(v___x_3149_, 11);
v_codeQualityEntryTasks_3164_ = lean_ctor_get(v___x_3149_, 12);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3166_ = v___x_3149_;
v_isShared_3167_ = v_isSharedCheck_3180_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3164_);
lean_inc(v_prevLinterStates_3163_);
lean_inc(v_snapshotTasks_3162_);
lean_inc(v_traceState_3161_);
lean_inc(v_infoState_3160_);
lean_inc(v_auxDeclNGen_3159_);
lean_inc(v_ngen_3158_);
lean_inc(v_maxRecDepth_3157_);
lean_inc(v_nextMacroScope_3156_);
lean_inc(v_usedQuotCtxts_3155_);
lean_inc(v_scopes_3154_);
lean_inc(v_messages_3153_);
lean_inc(v_env_3152_);
lean_dec(v___x_3149_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3180_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3173_; 
v___x_3168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3168_, 0, v_currNamespace_3150_);
lean_ctor_set(v___x_3168_, 1, v_openDecls_3151_);
v___x_3169_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3168_);
lean_ctor_set(v___x_3169_, 1, v___y_3140_);
lean_inc_ref(v___y_3137_);
lean_inc_ref(v___y_3136_);
v___x_3170_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3170_, 0, v___y_3136_);
lean_ctor_set(v___x_3170_, 1, v___y_3139_);
lean_ctor_set(v___x_3170_, 2, v___y_3134_);
lean_ctor_set(v___x_3170_, 3, v___y_3137_);
lean_ctor_set(v___x_3170_, 4, v___x_3169_);
lean_ctor_set_uint8(v___x_3170_, sizeof(void*)*5, v___y_3135_);
lean_ctor_set_uint8(v___x_3170_, sizeof(void*)*5 + 1, v___y_3138_);
lean_ctor_set_uint8(v___x_3170_, sizeof(void*)*5 + 2, v_isSilent_3129_);
v___x_3171_ = l_Lean_MessageLog_add(v___x_3170_, v_messages_3153_);
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 1, v___x_3171_);
v___x_3173_ = v___x_3166_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_env_3152_);
lean_ctor_set(v_reuseFailAlloc_3179_, 1, v___x_3171_);
lean_ctor_set(v_reuseFailAlloc_3179_, 2, v_scopes_3154_);
lean_ctor_set(v_reuseFailAlloc_3179_, 3, v_usedQuotCtxts_3155_);
lean_ctor_set(v_reuseFailAlloc_3179_, 4, v_nextMacroScope_3156_);
lean_ctor_set(v_reuseFailAlloc_3179_, 5, v_maxRecDepth_3157_);
lean_ctor_set(v_reuseFailAlloc_3179_, 6, v_ngen_3158_);
lean_ctor_set(v_reuseFailAlloc_3179_, 7, v_auxDeclNGen_3159_);
lean_ctor_set(v_reuseFailAlloc_3179_, 8, v_infoState_3160_);
lean_ctor_set(v_reuseFailAlloc_3179_, 9, v_traceState_3161_);
lean_ctor_set(v_reuseFailAlloc_3179_, 10, v_snapshotTasks_3162_);
lean_ctor_set(v_reuseFailAlloc_3179_, 11, v_prevLinterStates_3163_);
lean_ctor_set(v_reuseFailAlloc_3179_, 12, v_codeQualityEntryTasks_3164_);
v___x_3173_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3177_; 
v___x_3174_ = lean_st_ref_put(v___y_3141_, v___x_3173_);
v___x_3175_ = lean_box(0);
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 0, v___x_3175_);
v___x_3177_ = v___x_3147_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v___x_3175_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
}
}
else
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
lean_dec(v_a_3143_);
lean_dec_ref(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3134_);
v_a_3182_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3184_ = v___x_3144_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3144_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_dec_ref(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3134_);
v_a_3190_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_3142_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3142_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
v___jp_3198_:
{
lean_object* v_fileName_3204_; lean_object* v_fileMap_3205_; uint8_t v_suppressElabErrors_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3225_; 
v_fileName_3204_ = lean_ctor_get(v___y_3130_, 0);
v_fileMap_3205_ = lean_ctor_get(v___y_3130_, 1);
v_suppressElabErrors_3206_ = lean_ctor_get_uint8(v___y_3130_, sizeof(void*)*10);
v___x_3207_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3127_);
v___x_3208_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(v___x_3207_, v___y_3131_);
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3211_ = v___x_3208_;
v_isShared_3212_ = v_isSharedCheck_3225_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3208_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3225_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
lean_inc_ref_n(v_fileMap_3205_, 2);
v___x_3213_ = l_Lean_FileMap_toPosition(v_fileMap_3205_, v___y_3201_);
lean_dec(v___y_3201_);
v___x_3214_ = l_Lean_FileMap_toPosition(v_fileMap_3205_, v___y_3203_);
lean_dec(v___y_3203_);
v___x_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3214_);
v___x_3216_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
if (v_suppressElabErrors_3206_ == 0)
{
lean_del_object(v___x_3211_);
v___y_3134_ = v___x_3215_;
v___y_3135_ = v___y_3200_;
v___y_3136_ = v_fileName_3204_;
v___y_3137_ = v___x_3216_;
v___y_3138_ = v___y_3202_;
v___y_3139_ = v___x_3213_;
v___y_3140_ = v_a_3209_;
v___y_3141_ = v___y_3131_;
goto v___jp_3133_;
}
else
{
lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___f_3219_; uint8_t v___x_3220_; 
v___x_3217_ = lean_box(v_suppressElabErrors_3206_);
v___x_3218_ = lean_box(v___y_3199_);
v___f_3219_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3219_, 0, v___x_3217_);
lean_closure_set(v___f_3219_, 1, v___x_3218_);
lean_inc(v_a_3209_);
v___x_3220_ = l_Lean_MessageData_hasTag(v___f_3219_, v_a_3209_);
if (v___x_3220_ == 0)
{
lean_object* v___x_3221_; lean_object* v___x_3223_; 
lean_dec_ref_known(v___x_3215_, 1);
lean_dec_ref(v___x_3213_);
lean_dec(v_a_3209_);
v___x_3221_ = lean_box(0);
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 0, v___x_3221_);
v___x_3223_ = v___x_3211_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3221_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
else
{
lean_del_object(v___x_3211_);
v___y_3134_ = v___x_3215_;
v___y_3135_ = v___y_3200_;
v___y_3136_ = v_fileName_3204_;
v___y_3137_ = v___x_3216_;
v___y_3138_ = v___y_3202_;
v___y_3139_ = v___x_3213_;
v___y_3140_ = v_a_3209_;
v___y_3141_ = v___y_3131_;
goto v___jp_3133_;
}
}
}
}
v___jp_3226_:
{
lean_object* v___x_3232_; 
v___x_3232_ = l_Lean_Syntax_getTailPos_x3f(v___y_3229_, v___y_3228_);
lean_dec(v___y_3229_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_inc(v___y_3231_);
v___y_3199_ = v___y_3227_;
v___y_3200_ = v___y_3228_;
v___y_3201_ = v___y_3231_;
v___y_3202_ = v___y_3230_;
v___y_3203_ = v___y_3231_;
goto v___jp_3198_;
}
else
{
lean_object* v_val_3233_; 
v_val_3233_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_val_3233_);
lean_dec_ref_known(v___x_3232_, 1);
v___y_3199_ = v___y_3227_;
v___y_3200_ = v___y_3228_;
v___y_3201_ = v___y_3231_;
v___y_3202_ = v___y_3230_;
v___y_3203_ = v_val_3233_;
goto v___jp_3198_;
}
}
v___jp_3234_:
{
lean_object* v___x_3238_; 
v___x_3238_ = l_Lean_Elab_Command_getRef___redArg(v___y_3130_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v_a_3239_; lean_object* v_ref_3240_; lean_object* v___x_3241_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
lean_inc(v_a_3239_);
lean_dec_ref_known(v___x_3238_, 1);
v_ref_3240_ = l_Lean_replaceRef(v_ref_3126_, v_a_3239_);
lean_dec(v_a_3239_);
v___x_3241_ = l_Lean_Syntax_getPos_x3f(v_ref_3240_, v___y_3236_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v___x_3242_; 
v___x_3242_ = lean_unsigned_to_nat(0u);
v___y_3227_ = v___y_3235_;
v___y_3228_ = v___y_3236_;
v___y_3229_ = v_ref_3240_;
v___y_3230_ = v___y_3237_;
v___y_3231_ = v___x_3242_;
goto v___jp_3226_;
}
else
{
lean_object* v_val_3243_; 
v_val_3243_ = lean_ctor_get(v___x_3241_, 0);
lean_inc(v_val_3243_);
lean_dec_ref_known(v___x_3241_, 1);
v___y_3227_ = v___y_3235_;
v___y_3228_ = v___y_3236_;
v___y_3229_ = v_ref_3240_;
v___y_3230_ = v___y_3237_;
v___y_3231_ = v_val_3243_;
goto v___jp_3226_;
}
}
else
{
lean_object* v_a_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3251_; 
lean_dec_ref(v_msgData_3127_);
v_a_3244_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3246_ = v___x_3238_;
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_a_3244_);
lean_dec(v___x_3238_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3249_; 
if (v_isShared_3247_ == 0)
{
v___x_3249_ = v___x_3246_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_a_3244_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
}
}
v___jp_3253_:
{
if (v___y_3256_ == 0)
{
v___y_3235_ = v___y_3254_;
v___y_3236_ = v___y_3255_;
v___y_3237_ = v_severity_3128_;
goto v___jp_3234_;
}
else
{
v___y_3235_ = v___y_3254_;
v___y_3236_ = v___y_3255_;
v___y_3237_ = v___x_3252_;
goto v___jp_3234_;
}
}
v___jp_3257_:
{
if (v___y_3258_ == 0)
{
lean_object* v___x_3259_; lean_object* v_scopes_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v_opts_3263_; uint8_t v___x_3264_; uint8_t v___x_3265_; 
v___x_3259_ = lean_st_ref_get(v___y_3131_);
v_scopes_3260_ = lean_ctor_get(v___x_3259_, 2);
lean_inc(v_scopes_3260_);
lean_dec(v___x_3259_);
v___x_3261_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3262_ = l_List_head_x21___redArg(v___x_3261_, v_scopes_3260_);
lean_dec(v_scopes_3260_);
v_opts_3263_ = lean_ctor_get(v___x_3262_, 1);
lean_inc_ref(v_opts_3263_);
lean_dec(v___x_3262_);
v___x_3264_ = 1;
v___x_3265_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3128_, v___x_3264_);
if (v___x_3265_ == 0)
{
lean_dec_ref(v_opts_3263_);
v___y_3254_ = v___y_3258_;
v___y_3255_ = v___y_3258_;
v___y_3256_ = v___x_3265_;
goto v___jp_3253_;
}
else
{
lean_object* v___x_3266_; uint8_t v___x_3267_; 
v___x_3266_ = l_Lean_warningAsError;
v___x_3267_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_3263_, v___x_3266_);
lean_dec_ref(v_opts_3263_);
v___y_3254_ = v___y_3258_;
v___y_3255_ = v___y_3258_;
v___y_3256_ = v___x_3267_;
goto v___jp_3253_;
}
}
else
{
lean_object* v___x_3268_; lean_object* v___x_3269_; 
lean_dec_ref(v_msgData_3127_);
v___x_3268_ = lean_box(0);
v___x_3269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3268_);
return v___x_3269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___boxed(lean_object* v_ref_3272_, lean_object* v_msgData_3273_, lean_object* v_severity_3274_, lean_object* v_isSilent_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_){
_start:
{
uint8_t v_severity_boxed_3279_; uint8_t v_isSilent_boxed_3280_; lean_object* v_res_3281_; 
v_severity_boxed_3279_ = lean_unbox(v_severity_3274_);
v_isSilent_boxed_3280_ = lean_unbox(v_isSilent_3275_);
v_res_3281_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3272_, v_msgData_3273_, v_severity_boxed_3279_, v_isSilent_boxed_3280_, v___y_3276_, v___y_3277_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec(v_ref_3272_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(lean_object* v_ref_3282_, lean_object* v_msgData_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_){
_start:
{
uint8_t v___x_3287_; uint8_t v___x_3288_; lean_object* v___x_3289_; 
v___x_3287_ = 0;
v___x_3288_ = 0;
v___x_3289_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3282_, v_msgData_3283_, v___x_3287_, v___x_3288_, v___y_3284_, v___y_3285_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0___boxed(lean_object* v_ref_3290_, lean_object* v_msgData_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_){
_start:
{
lean_object* v_res_3295_; 
v_res_3295_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3290_, v_msgData_3291_, v___y_3292_, v___y_3293_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v_ref_3290_);
return v_res_3295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(lean_object* v___x_3297_, lean_object* v_x_3298_){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3299_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___closed__0));
v___x_3300_ = lean_string_append(v___x_3299_, v___x_3297_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed(lean_object* v___x_3301_, lean_object* v_x_3302_){
_start:
{
lean_object* v_res_3303_; 
v_res_3303_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(v___x_3301_, v_x_3302_);
lean_dec_ref(v_x_3302_);
lean_dec_ref(v___x_3301_);
return v_res_3303_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3305_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__0));
v___x_3306_ = l_Lean_stringToMessageData(v___x_3305_);
return v___x_3306_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3308_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__2));
v___x_3309_ = l_Lean_stringToMessageData(v___x_3308_);
return v___x_3309_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3311_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__4));
v___x_3312_ = l_Lean_stringToMessageData(v___x_3311_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(lean_object* v___x_3313_, uint8_t v___x_3314_, lean_object* v___x_3315_, lean_object* v_insertPos_3316_, lean_object* v_cmdLine_3317_, lean_object* v_ref_3318_, size_t v_sz_3319_, size_t v_i_3320_, lean_object* v_bs_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
uint8_t v___x_3325_; 
v___x_3325_ = lean_usize_dec_lt(v_i_3320_, v_sz_3319_);
if (v___x_3325_ == 0)
{
lean_object* v___x_3326_; 
lean_dec_ref(v___x_3315_);
lean_dec_ref(v___x_3313_);
v___x_3326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3326_, 0, v_bs_3321_);
return v___x_3326_;
}
else
{
lean_object* v_v_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v_v_3327_ = lean_array_uget(v_bs_3321_, v_i_3320_);
lean_inc(v_v_3327_);
v___x_3328_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppTactic___boxed), 4, 1);
lean_closure_set(v___x_3328_, 0, v_v_3327_);
v___x_3329_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_3328_, v___y_3322_, v___y_3323_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v_a_3330_; lean_object* v___x_3331_; lean_object* v_bs_x27_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___f_3335_; lean_object* v___x_3336_; 
v_a_3330_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_a_3330_);
lean_dec_ref_known(v___x_3329_, 1);
v___x_3331_ = lean_unsigned_to_nat(0u);
v_bs_x27_3332_ = lean_array_uset(v_bs_3321_, v_i_3320_, v___x_3331_);
v___x_3333_ = l_Std_Format_defWidth;
v___x_3334_ = l_Std_Format_pretty(v_a_3330_, v___x_3333_, v___x_3331_, v___x_3331_);
lean_inc_ref(v___x_3334_);
v___f_3335_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3335_, 0, v___x_3334_);
lean_inc_ref(v___x_3313_);
v___x_3336_ = lean_string_append(v___x_3313_, v___x_3334_);
lean_dec_ref(v___x_3334_);
if (v___x_3314_ == 0)
{
goto v___jp_3337_;
}
else
{
lean_object* v___x_3348_; lean_object* v_line_3349_; lean_object* v_column_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3385_; 
lean_inc_ref(v___x_3315_);
v___x_3348_ = l_Lean_FileMap_toPosition(v___x_3315_, v_insertPos_3316_);
v_line_3349_ = lean_ctor_get(v___x_3348_, 0);
v_column_3350_ = lean_ctor_get(v___x_3348_, 1);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3352_ = v___x_3348_;
v_isShared_3353_ = v_isSharedCheck_3385_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_column_3350_);
lean_inc(v_line_3349_);
lean_dec(v___x_3348_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3385_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3362_; 
v___x_3354_ = lean_nat_sub(v_line_3349_, v_cmdLine_3317_);
lean_dec(v_line_3349_);
v___x_3355_ = lean_unsigned_to_nat(1u);
v___x_3356_ = lean_nat_add(v___x_3354_, v___x_3355_);
lean_dec(v___x_3354_);
v___x_3357_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1);
lean_inc_ref(v___x_3336_);
v___x_3358_ = l_String_quote(v___x_3336_);
v___x_3359_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3358_);
v___x_3360_ = l_Lean_MessageData_ofFormat(v___x_3359_);
if (v_isShared_3353_ == 0)
{
lean_ctor_set_tag(v___x_3352_, 7);
lean_ctor_set(v___x_3352_, 1, v___x_3360_);
lean_ctor_set(v___x_3352_, 0, v___x_3357_);
v___x_3362_ = v___x_3352_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v___x_3357_);
lean_ctor_set(v_reuseFailAlloc_3384_, 1, v___x_3360_);
v___x_3362_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3363_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3);
v___x_3364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3362_);
lean_ctor_set(v___x_3364_, 1, v___x_3363_);
v___x_3365_ = l_Nat_reprFast(v___x_3356_);
v___x_3366_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
v___x_3367_ = l_Lean_MessageData_ofFormat(v___x_3366_);
v___x_3368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3364_);
lean_ctor_set(v___x_3368_, 1, v___x_3367_);
v___x_3369_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5);
v___x_3370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3368_);
lean_ctor_set(v___x_3370_, 1, v___x_3369_);
v___x_3371_ = l_Nat_reprFast(v_column_3350_);
v___x_3372_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3371_);
v___x_3373_ = l_Lean_MessageData_ofFormat(v___x_3372_);
v___x_3374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3370_);
lean_ctor_set(v___x_3374_, 1, v___x_3373_);
v___x_3375_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3318_, v___x_3374_, v___y_3322_, v___y_3323_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_dec_ref_known(v___x_3375_, 1);
goto v___jp_3337_;
}
else
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3383_; 
lean_dec_ref(v___x_3336_);
lean_dec_ref(v___f_3335_);
lean_dec_ref(v_bs_x27_3332_);
lean_dec(v_v_3327_);
lean_dec_ref(v___x_3315_);
lean_dec_ref(v___x_3313_);
v_a_3376_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3378_ = v___x_3375_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3375_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3381_; 
if (v_isShared_3379_ == 0)
{
v___x_3381_ = v___x_3378_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_a_3376_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
}
}
}
}
v___jp_3337_:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; size_t v___x_3344_; size_t v___x_3345_; lean_object* v___x_3346_; 
v___x_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3336_);
v___x_3339_ = lean_box(0);
v___x_3340_ = l_Lean_MessageData_ofSyntax(v_v_3327_);
v___x_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3340_);
v___x_3342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3342_, 0, v___f_3335_);
v___x_3343_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3338_);
lean_ctor_set(v___x_3343_, 1, v___x_3339_);
lean_ctor_set(v___x_3343_, 2, v___x_3339_);
lean_ctor_set(v___x_3343_, 3, v___x_3339_);
lean_ctor_set(v___x_3343_, 4, v___x_3341_);
lean_ctor_set(v___x_3343_, 5, v___x_3342_);
v___x_3344_ = ((size_t)1ULL);
v___x_3345_ = lean_usize_add(v_i_3320_, v___x_3344_);
v___x_3346_ = lean_array_uset(v_bs_x27_3332_, v_i_3320_, v___x_3343_);
v_i_3320_ = v___x_3345_;
v_bs_3321_ = v___x_3346_;
goto _start;
}
}
else
{
lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3393_; 
lean_dec(v_v_3327_);
lean_dec_ref(v_bs_3321_);
lean_dec_ref(v___x_3315_);
lean_dec_ref(v___x_3313_);
v_a_3386_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3388_ = v___x_3329_;
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v___x_3329_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3391_; 
if (v_isShared_3389_ == 0)
{
v___x_3391_ = v___x_3388_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_a_3386_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___boxed(lean_object* v___x_3394_, lean_object* v___x_3395_, lean_object* v___x_3396_, lean_object* v_insertPos_3397_, lean_object* v_cmdLine_3398_, lean_object* v_ref_3399_, lean_object* v_sz_3400_, lean_object* v_i_3401_, lean_object* v_bs_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_){
_start:
{
uint8_t v___x_3850__boxed_3406_; size_t v_sz_boxed_3407_; size_t v_i_boxed_3408_; lean_object* v_res_3409_; 
v___x_3850__boxed_3406_ = lean_unbox(v___x_3395_);
v_sz_boxed_3407_ = lean_unbox_usize(v_sz_3400_);
lean_dec(v_sz_3400_);
v_i_boxed_3408_ = lean_unbox_usize(v_i_3401_);
lean_dec(v_i_3401_);
v_res_3409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3394_, v___x_3850__boxed_3406_, v___x_3396_, v_insertPos_3397_, v_cmdLine_3398_, v_ref_3399_, v_sz_boxed_3407_, v_i_boxed_3408_, v_bs_3402_, v___y_3403_, v___y_3404_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v_ref_3399_);
lean_dec(v_cmdLine_3398_);
lean_dec(v_insertPos_3397_);
return v_res_3409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(lean_object* v_tacticSeq_3410_, lean_object* v_ref_3411_, lean_object* v_insertPos_3412_, lean_object* v_suggs_3413_, lean_object* v_cmdLine_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_){
_start:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; uint8_t v___x_3420_; 
v___x_3418_ = lean_array_get_size(v_suggs_3413_);
v___x_3419_ = lean_unsigned_to_nat(0u);
v___x_3420_ = lean_nat_dec_eq(v___x_3418_, v___x_3419_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; lean_object* v_fileMap_3422_; lean_object* v_scopes_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v_opts_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; uint8_t v___x_3429_; size_t v_sz_3430_; size_t v___x_3431_; lean_object* v___x_3432_; 
v___x_3421_ = lean_st_ref_get(v_a_3416_);
v_fileMap_3422_ = lean_ctor_get(v_a_3415_, 1);
v_scopes_3423_ = lean_ctor_get(v___x_3421_, 2);
lean_inc(v_scopes_3423_);
lean_dec(v___x_3421_);
v___x_3424_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3425_ = l_List_head_x21___redArg(v___x_3424_, v_scopes_3423_);
lean_dec(v_scopes_3423_);
v_opts_3426_ = lean_ctor_get(v___x_3425_, 1);
lean_inc_ref(v_opts_3426_);
lean_dec(v___x_3425_);
lean_inc_ref_n(v_fileMap_3422_, 2);
v___x_3427_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(v_tacticSeq_3410_, v_fileMap_3422_);
v___x_3428_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_debug_autoTry_showEdits;
v___x_3429_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_3426_, v___x_3428_);
lean_dec_ref(v_opts_3426_);
v_sz_3430_ = lean_array_size(v_suggs_3413_);
v___x_3431_ = ((size_t)0ULL);
v___x_3432_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3427_, v___x_3429_, v_fileMap_3422_, v_insertPos_3412_, v_cmdLine_3414_, v_ref_3411_, v_sz_3430_, v___x_3431_, v_suggs_3413_, v_a_3415_, v_a_3416_);
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_object* v_a_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; uint8_t v___x_3438_; lean_object* v___x_3439_; lean_object* v___y_3440_; lean_object* v___x_3441_; 
v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
lean_inc(v_a_3433_);
lean_dec_ref_known(v___x_3432_, 1);
v___x_3434_ = l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default;
v___x_3435_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx(v_insertPos_3412_);
v___x_3436_ = lean_array_get_size(v_a_3433_);
v___x_3437_ = lean_unsigned_to_nat(1u);
v___x_3438_ = lean_nat_dec_eq(v___x_3436_, v___x_3437_);
v___x_3439_ = lean_box(v___x_3438_);
v___y_3440_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed), 9, 6);
lean_closure_set(v___y_3440_, 0, v___x_3439_);
lean_closure_set(v___y_3440_, 1, v___x_3435_);
lean_closure_set(v___y_3440_, 2, v_ref_3411_);
lean_closure_set(v___y_3440_, 3, v_a_3433_);
lean_closure_set(v___y_3440_, 4, v___x_3434_);
lean_closure_set(v___y_3440_, 5, v___x_3419_);
v___x_3441_ = l_Lean_Elab_Command_liftCoreM___redArg(v___y_3440_, v_a_3415_, v_a_3416_);
return v___x_3441_;
}
else
{
lean_object* v_a_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3449_; 
lean_dec(v_insertPos_3412_);
lean_dec(v_ref_3411_);
v_a_3442_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3444_ = v___x_3432_;
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_a_3442_);
lean_dec(v___x_3432_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3447_; 
if (v_isShared_3445_ == 0)
{
v___x_3447_ = v___x_3444_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_a_3442_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
}
else
{
lean_object* v___x_3450_; lean_object* v___x_3451_; 
lean_dec_ref(v_suggs_3413_);
lean_dec(v_insertPos_3412_);
lean_dec(v_ref_3411_);
v___x_3450_ = lean_box(0);
v___x_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3450_);
return v___x_3451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___boxed(lean_object* v_tacticSeq_3452_, lean_object* v_ref_3453_, lean_object* v_insertPos_3454_, lean_object* v_suggs_3455_, lean_object* v_cmdLine_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(v_tacticSeq_3452_, v_ref_3453_, v_insertPos_3454_, v_suggs_3455_, v_cmdLine_3456_, v_a_3457_, v_a_3458_);
lean_dec(v_a_3458_);
lean_dec_ref(v_a_3457_);
lean_dec(v_cmdLine_3456_);
lean_dec(v_tacticSeq_3452_);
return v_res_3460_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(lean_object* v_x_3461_){
_start:
{
uint8_t v___x_3462_; 
v___x_3462_ = 0;
return v___x_3462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0___boxed(lean_object* v_x_3463_){
_start:
{
uint8_t v_res_3464_; lean_object* v_r_3465_; 
v_res_3464_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(v_x_3463_);
lean_dec(v_x_3463_);
v_r_3465_ = lean_box(v_res_3464_);
return v_r_3465_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7(void){
_start:
{
lean_object* v___x_3482_; 
v___x_3482_ = l_Array_mkArray0(lean_box(0));
return v___x_3482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(lean_object* v___f_3486_, lean_object* v_ref_3487_, lean_object* v_goal_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_){
_start:
{
lean_object* v_toCold_3494_; lean_object* v_currRecDepth_3495_; lean_object* v_ref_3496_; uint8_t v_diag_3497_; uint8_t v_suppressElabErrors_3498_; uint8_t v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; uint8_t v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v_ref_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; 
v_toCold_3494_ = lean_ctor_get(v___y_3491_, 0);
v_currRecDepth_3495_ = lean_ctor_get(v___y_3491_, 1);
v_ref_3496_ = lean_ctor_get(v___y_3491_, 2);
v_diag_3497_ = lean_ctor_get_uint8(v___y_3491_, sizeof(void*)*3);
v_suppressElabErrors_3498_ = lean_ctor_get_uint8(v___y_3491_, sizeof(void*)*3 + 1);
v___x_3499_ = 0;
v___x_3500_ = l_Lean_SourceInfo_fromRef(v_ref_3496_, v___x_3499_);
v___x_3501_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__1));
v___x_3502_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__2));
lean_inc_n(v___x_3500_, 3);
v___x_3503_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3500_);
lean_ctor_set(v___x_3503_, 1, v___x_3502_);
v___x_3504_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__4));
v___x_3505_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__6));
v___x_3506_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7);
v___x_3507_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3500_);
lean_ctor_set(v___x_3507_, 1, v___x_3505_);
lean_ctor_set(v___x_3507_, 2, v___x_3506_);
v___x_3508_ = l_Lean_Syntax_node1(v___x_3500_, v___x_3504_, v___x_3507_);
v___x_3509_ = l_Lean_Syntax_node2(v___x_3500_, v___x_3501_, v___x_3503_, v___x_3508_);
v___x_3510_ = lean_box(0);
v___x_3511_ = lean_box(0);
v___x_3512_ = 1;
v___x_3513_ = lean_box(1);
v___x_3514_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__5));
v___x_3515_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_3515_, 0, v___x_3510_);
lean_ctor_set(v___x_3515_, 1, v___x_3511_);
lean_ctor_set(v___x_3515_, 2, v___x_3510_);
lean_ctor_set(v___x_3515_, 3, v___f_3486_);
lean_ctor_set(v___x_3515_, 4, v___x_3513_);
lean_ctor_set(v___x_3515_, 5, v___x_3513_);
lean_ctor_set(v___x_3515_, 6, v___x_3510_);
lean_ctor_set(v___x_3515_, 7, v___x_3514_);
lean_ctor_set_uint8(v___x_3515_, sizeof(void*)*8, v___x_3512_);
lean_ctor_set_uint8(v___x_3515_, sizeof(void*)*8 + 1, v___x_3512_);
lean_ctor_set_uint8(v___x_3515_, sizeof(void*)*8 + 2, v___x_3512_);
lean_ctor_set_uint8(v___x_3515_, sizeof(void*)*8 + 3, v___x_3512_);
lean_ctor_set_uint8(v___x_3515_, sizeof(void*)*8 + 4, v___x_3499_);
lean_ctor_set_uint8(v___x_3515_, sizeof(void*)*8 + 5, v___x_3499_);
lean_ctor_set_uint8(v___x_3515_, sizeof(void*)*8 + 6, v___x_3499_);
lean_ctor_set_uint8(v___x_3515_, sizeof(void*)*8 + 7, v___x_3499_);
lean_ctor_set_uint8(v___x_3515_, sizeof(void*)*8 + 8, v___x_3512_);
lean_ctor_set_uint8(v___x_3515_, sizeof(void*)*8 + 9, v___x_3499_);
lean_ctor_set_uint8(v___x_3515_, sizeof(void*)*8 + 10, v___x_3512_);
v___x_3516_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__8));
v_ref_3517_ = l_Lean_replaceRef(v_ref_3487_, v_ref_3496_);
lean_inc(v_currRecDepth_3495_);
lean_inc_ref(v_toCold_3494_);
v___x_3518_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3518_, 0, v_toCold_3494_);
lean_ctor_set(v___x_3518_, 1, v_currRecDepth_3495_);
lean_ctor_set(v___x_3518_, 2, v_ref_3517_);
lean_ctor_set_uint8(v___x_3518_, sizeof(void*)*3, v_diag_3497_);
lean_ctor_set_uint8(v___x_3518_, sizeof(void*)*3 + 1, v_suppressElabErrors_3498_);
v___x_3519_ = l_Lean_Elab_runTactic(v_goal_3488_, v___x_3509_, v___x_3515_, v___x_3516_, v___y_3489_, v___y_3490_, v___x_3518_, v___y_3492_);
lean_dec_ref_known(v___x_3518_, 3);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3527_; 
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3527_ == 0)
{
lean_object* v_unused_3528_; 
v_unused_3528_ = lean_ctor_get(v___x_3519_, 0);
lean_dec(v_unused_3528_);
v___x_3521_ = v___x_3519_;
v_isShared_3522_ = v_isSharedCheck_3527_;
goto v_resetjp_3520_;
}
else
{
lean_dec(v___x_3519_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3527_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3523_; lean_object* v___x_3525_; 
v___x_3523_ = lean_box(0);
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 0, v___x_3523_);
v___x_3525_ = v___x_3521_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v___x_3523_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
else
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3557_; 
v_a_3529_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3531_ = v___x_3519_;
v_isShared_3532_ = v_isSharedCheck_3557_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3519_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3557_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3538_; uint8_t v___y_3540_; uint8_t v___y_3552_; uint8_t v___x_3555_; 
lean_inc(v_a_3529_);
v___x_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3538_, 0, v_a_3529_);
v___x_3555_ = l_Lean_Exception_isInterrupt(v_a_3529_);
if (v___x_3555_ == 0)
{
uint8_t v___x_3556_; 
lean_inc(v_a_3529_);
v___x_3556_ = l_Lean_Exception_isRuntime(v_a_3529_);
v___y_3552_ = v___x_3556_;
goto v___jp_3551_;
}
else
{
v___y_3552_ = v___x_3555_;
goto v___jp_3551_;
}
v___jp_3533_:
{
lean_object* v___x_3534_; lean_object* v___x_3536_; 
v___x_3534_ = lean_box(0);
if (v_isShared_3532_ == 0)
{
lean_ctor_set_tag(v___x_3531_, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3534_);
v___x_3536_ = v___x_3531_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3534_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
v___jp_3539_:
{
if (v___y_3540_ == 0)
{
lean_object* v_options_3541_; uint8_t v_hasTrace_3542_; 
lean_dec_ref_known(v___x_3538_, 1);
v_options_3541_ = lean_ctor_get(v_toCold_3494_, 2);
v_hasTrace_3542_ = lean_ctor_get_uint8(v_options_3541_, sizeof(void*)*1);
if (v_hasTrace_3542_ == 0)
{
lean_dec(v_a_3529_);
goto v___jp_3533_;
}
else
{
lean_object* v_inheritedTraceOptions_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; uint8_t v___x_3546_; 
v_inheritedTraceOptions_3543_ = lean_ctor_get(v_toCold_3494_, 11);
v___x_3544_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3545_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_3546_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3543_, v_options_3541_, v___x_3545_);
if (v___x_3546_ == 0)
{
lean_dec(v_a_3529_);
goto v___jp_3533_;
}
else
{
lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
lean_del_object(v___x_3531_);
v___x_3547_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_3548_ = l_Lean_Exception_toMessageData(v_a_3529_);
v___x_3549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3547_);
lean_ctor_set(v___x_3549_, 1, v___x_3548_);
v___x_3550_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_3544_, v___x_3549_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
return v___x_3550_;
}
}
}
else
{
lean_del_object(v___x_3531_);
lean_dec(v_a_3529_);
return v___x_3538_;
}
}
v___jp_3551_:
{
if (v___y_3552_ == 0)
{
uint8_t v___x_3553_; 
v___x_3553_ = l_Lean_Exception_isInterrupt(v_a_3529_);
if (v___x_3553_ == 0)
{
uint8_t v___x_3554_; 
lean_inc(v_a_3529_);
v___x_3554_ = l_Lean_Exception_isMaxRecDepth(v_a_3529_);
v___y_3540_ = v___x_3554_;
goto v___jp_3539_;
}
else
{
v___y_3540_ = v___x_3553_;
goto v___jp_3539_;
}
}
else
{
lean_del_object(v___x_3531_);
lean_dec(v_a_3529_);
return v___x_3538_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___boxed(lean_object* v___f_3558_, lean_object* v_ref_3559_, lean_object* v_goal_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_){
_start:
{
lean_object* v_res_3566_; 
v_res_3566_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(v___f_3558_, v_ref_3559_, v_goal_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
lean_dec(v___y_3564_);
lean_dec_ref(v___y_3563_);
lean_dec(v___y_3562_);
lean_dec_ref(v___y_3561_);
lean_dec(v_ref_3559_);
return v_res_3566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(lean_object* v_c_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_){
_start:
{
lean_object* v_mctx_3572_; lean_object* v_ref_3573_; lean_object* v_env_3574_; lean_object* v_opts_3575_; lean_object* v_namingCtx_3576_; lean_object* v_goal_3577_; lean_object* v_decls_3578_; lean_object* v___x_3579_; 
v_mctx_3572_ = lean_ctor_get(v_c_3568_, 3);
lean_inc_ref(v_mctx_3572_);
v_ref_3573_ = lean_ctor_get(v_c_3568_, 1);
lean_inc(v_ref_3573_);
v_env_3574_ = lean_ctor_get(v_c_3568_, 2);
lean_inc_ref(v_env_3574_);
v_opts_3575_ = lean_ctor_get(v_c_3568_, 4);
lean_inc_ref(v_opts_3575_);
v_namingCtx_3576_ = lean_ctor_get(v_c_3568_, 5);
lean_inc_ref(v_namingCtx_3576_);
v_goal_3577_ = lean_ctor_get(v_c_3568_, 6);
lean_inc(v_goal_3577_);
lean_dec_ref(v_c_3568_);
v_decls_3578_ = lean_ctor_get(v_mctx_3572_, 5);
v___x_3579_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_decls_3578_, v_goal_3577_);
if (lean_obj_tag(v___x_3579_) == 1)
{
lean_object* v_val_3580_; lean_object* v_lctx_3581_; lean_object* v___f_3582_; lean_object* v___f_3583_; lean_object* v___x_3584_; 
v_val_3580_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_val_3580_);
lean_dec_ref_known(v___x_3579_, 1);
v_lctx_3581_ = lean_ctor_get(v_val_3580_, 1);
lean_inc_ref(v_lctx_3581_);
lean_dec(v_val_3580_);
v___f_3582_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___closed__0));
v___f_3583_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___boxed), 8, 3);
lean_closure_set(v___f_3583_, 0, v___f_3582_);
lean_closure_set(v___f_3583_, 1, v_ref_3573_);
lean_closure_set(v___f_3583_, 2, v_goal_3577_);
v___x_3584_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_3574_, v_mctx_3572_, v_lctx_3581_, v_opts_3575_, v_namingCtx_3576_, v___f_3583_, v_a_3569_, v_a_3570_);
lean_dec_ref(v_namingCtx_3576_);
return v___x_3584_;
}
else
{
lean_object* v___x_3585_; lean_object* v___x_3586_; 
lean_dec(v___x_3579_);
lean_dec(v_goal_3577_);
lean_dec_ref(v_namingCtx_3576_);
lean_dec_ref(v_opts_3575_);
lean_dec_ref(v_env_3574_);
lean_dec(v_ref_3573_);
lean_dec_ref(v_mctx_3572_);
v___x_3585_ = lean_box(0);
v___x_3586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3585_);
return v___x_3586_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___boxed(lean_object* v_c_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_){
_start:
{
lean_object* v_res_3591_; 
v_res_3591_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(v_c_3587_, v_a_3588_, v_a_3589_);
lean_dec(v_a_3589_);
lean_dec_ref(v_a_3588_);
return v_res_3591_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(lean_object* v___x_3592_, lean_object* v_val_3593_, lean_object* v_as_3594_, size_t v_i_3595_, size_t v_stop_3596_){
_start:
{
uint8_t v___x_3601_; uint8_t v___x_3602_; 
v___x_3601_ = 0;
v___x_3602_ = lean_usize_dec_eq(v_i_3595_, v_stop_3596_);
if (v___x_3602_ == 0)
{
lean_object* v___x_3603_; lean_object* v_pos_3604_; uint8_t v_severity_3605_; lean_object* v_data_3606_; lean_object* v___f_3607_; uint8_t v___x_3608_; lean_object* v___x_3609_; uint8_t v___x_3610_; uint8_t v___y_3612_; 
v___x_3603_ = lean_array_uget_borrowed(v_as_3594_, v_i_3595_);
v_pos_3604_ = lean_ctor_get(v___x_3603_, 1);
v_severity_3605_ = lean_ctor_get_uint8(v___x_3603_, sizeof(void*)*5 + 1);
v_data_3606_ = lean_ctor_get(v___x_3603_, 4);
v___f_3607_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
v___x_3608_ = 1;
lean_inc_ref(v_pos_3604_);
v___x_3609_ = l_Lean_FileMap_ofPosition(v___x_3592_, v_pos_3604_);
v___x_3610_ = l_Lean_Syntax_Range_contains(v_val_3593_, v___x_3609_, v___x_3608_);
lean_dec(v___x_3609_);
if (v_severity_3605_ == 2)
{
v___y_3612_ = v___x_3608_;
goto v___jp_3611_;
}
else
{
v___y_3612_ = v___x_3601_;
goto v___jp_3611_;
}
v___jp_3611_:
{
if (v___x_3610_ == 0)
{
goto v___jp_3597_;
}
else
{
if (v___y_3612_ == 0)
{
goto v___jp_3597_;
}
else
{
uint8_t v___x_3613_; 
lean_inc(v_data_3606_);
v___x_3613_ = l_Lean_MessageData_hasTag(v___f_3607_, v_data_3606_);
if (v___x_3613_ == 0)
{
return v___x_3608_;
}
else
{
goto v___jp_3597_;
}
}
}
}
}
else
{
return v___x_3601_;
}
v___jp_3597_:
{
size_t v___x_3598_; size_t v___x_3599_; 
v___x_3598_ = ((size_t)1ULL);
v___x_3599_ = lean_usize_add(v_i_3595_, v___x_3598_);
v_i_3595_ = v___x_3599_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1___boxed(lean_object* v___x_3614_, lean_object* v_val_3615_, lean_object* v_as_3616_, lean_object* v_i_3617_, lean_object* v_stop_3618_){
_start:
{
size_t v_i_boxed_3619_; size_t v_stop_boxed_3620_; uint8_t v_res_3621_; lean_object* v_r_3622_; 
v_i_boxed_3619_ = lean_unbox_usize(v_i_3617_);
lean_dec(v_i_3617_);
v_stop_boxed_3620_ = lean_unbox_usize(v_stop_3618_);
lean_dec(v_stop_3618_);
v_res_3621_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3614_, v_val_3615_, v_as_3616_, v_i_boxed_3619_, v_stop_boxed_3620_);
lean_dec_ref(v_as_3616_);
lean_dec_ref(v_val_3615_);
lean_dec_ref(v___x_3614_);
v_r_3622_ = lean_box(v_res_3621_);
return v_r_3622_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(lean_object* v___x_3623_, lean_object* v_val_3624_, lean_object* v_x_3625_){
_start:
{
if (lean_obj_tag(v_x_3625_) == 0)
{
lean_object* v_cs_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; uint8_t v___x_3629_; 
v_cs_3626_ = lean_ctor_get(v_x_3625_, 0);
v___x_3627_ = lean_unsigned_to_nat(0u);
v___x_3628_ = lean_array_get_size(v_cs_3626_);
v___x_3629_ = lean_nat_dec_lt(v___x_3627_, v___x_3628_);
if (v___x_3629_ == 0)
{
return v___x_3629_;
}
else
{
if (v___x_3629_ == 0)
{
return v___x_3629_;
}
else
{
size_t v___x_3630_; size_t v___x_3631_; uint8_t v___x_3632_; 
v___x_3630_ = ((size_t)0ULL);
v___x_3631_ = lean_usize_of_nat(v___x_3628_);
v___x_3632_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3623_, v_val_3624_, v_cs_3626_, v___x_3630_, v___x_3631_);
return v___x_3632_;
}
}
}
else
{
lean_object* v_vs_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; uint8_t v___x_3636_; 
v_vs_3633_ = lean_ctor_get(v_x_3625_, 0);
v___x_3634_ = lean_unsigned_to_nat(0u);
v___x_3635_ = lean_array_get_size(v_vs_3633_);
v___x_3636_ = lean_nat_dec_lt(v___x_3634_, v___x_3635_);
if (v___x_3636_ == 0)
{
return v___x_3636_;
}
else
{
if (v___x_3636_ == 0)
{
return v___x_3636_;
}
else
{
size_t v___x_3637_; size_t v___x_3638_; uint8_t v___x_3639_; 
v___x_3637_ = ((size_t)0ULL);
v___x_3638_ = lean_usize_of_nat(v___x_3635_);
v___x_3639_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3623_, v_val_3624_, v_vs_3633_, v___x_3637_, v___x_3638_);
return v___x_3639_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(lean_object* v___x_3640_, lean_object* v_val_3641_, lean_object* v_as_3642_, size_t v_i_3643_, size_t v_stop_3644_){
_start:
{
uint8_t v___x_3645_; 
v___x_3645_ = lean_usize_dec_eq(v_i_3643_, v_stop_3644_);
if (v___x_3645_ == 0)
{
lean_object* v___x_3646_; uint8_t v___x_3647_; 
v___x_3646_ = lean_array_uget_borrowed(v_as_3642_, v_i_3643_);
v___x_3647_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3640_, v_val_3641_, v___x_3646_);
if (v___x_3647_ == 0)
{
size_t v___x_3648_; size_t v___x_3649_; 
v___x_3648_ = ((size_t)1ULL);
v___x_3649_ = lean_usize_add(v_i_3643_, v___x_3648_);
v_i_3643_ = v___x_3649_;
goto _start;
}
else
{
return v___x_3647_;
}
}
else
{
uint8_t v___x_3651_; 
v___x_3651_ = 0;
return v___x_3651_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3652_, lean_object* v_val_3653_, lean_object* v_as_3654_, lean_object* v_i_3655_, lean_object* v_stop_3656_){
_start:
{
size_t v_i_boxed_3657_; size_t v_stop_boxed_3658_; uint8_t v_res_3659_; lean_object* v_r_3660_; 
v_i_boxed_3657_ = lean_unbox_usize(v_i_3655_);
lean_dec(v_i_3655_);
v_stop_boxed_3658_ = lean_unbox_usize(v_stop_3656_);
lean_dec(v_stop_3656_);
v_res_3659_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3652_, v_val_3653_, v_as_3654_, v_i_boxed_3657_, v_stop_boxed_3658_);
lean_dec_ref(v_as_3654_);
lean_dec_ref(v_val_3653_);
lean_dec_ref(v___x_3652_);
v_r_3660_ = lean_box(v_res_3659_);
return v_r_3660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0___boxed(lean_object* v___x_3661_, lean_object* v_val_3662_, lean_object* v_x_3663_){
_start:
{
uint8_t v_res_3664_; lean_object* v_r_3665_; 
v_res_3664_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3661_, v_val_3662_, v_x_3663_);
lean_dec_ref(v_x_3663_);
lean_dec_ref(v_val_3662_);
lean_dec_ref(v___x_3661_);
v_r_3665_ = lean_box(v_res_3664_);
return v_r_3665_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(lean_object* v___x_3666_, lean_object* v_val_3667_, lean_object* v_t_3668_){
_start:
{
lean_object* v_root_3669_; lean_object* v_tail_3670_; uint8_t v___x_3671_; 
v_root_3669_ = lean_ctor_get(v_t_3668_, 0);
v_tail_3670_ = lean_ctor_get(v_t_3668_, 1);
v___x_3671_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3666_, v_val_3667_, v_root_3669_);
if (v___x_3671_ == 0)
{
lean_object* v___x_3672_; lean_object* v___x_3673_; uint8_t v___x_3674_; 
v___x_3672_ = lean_unsigned_to_nat(0u);
v___x_3673_ = lean_array_get_size(v_tail_3670_);
v___x_3674_ = lean_nat_dec_lt(v___x_3672_, v___x_3673_);
if (v___x_3674_ == 0)
{
return v___x_3674_;
}
else
{
if (v___x_3674_ == 0)
{
return v___x_3674_;
}
else
{
size_t v___x_3675_; size_t v___x_3676_; uint8_t v___x_3677_; 
v___x_3675_ = ((size_t)0ULL);
v___x_3676_ = lean_usize_of_nat(v___x_3673_);
v___x_3677_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3666_, v_val_3667_, v_tail_3670_, v___x_3675_, v___x_3676_);
return v___x_3677_;
}
}
}
else
{
return v___x_3671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0___boxed(lean_object* v___x_3678_, lean_object* v_val_3679_, lean_object* v_t_3680_){
_start:
{
uint8_t v_res_3681_; lean_object* v_r_3682_; 
v_res_3681_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v___x_3678_, v_val_3679_, v_t_3680_);
lean_dec_ref(v_t_3680_);
lean_dec_ref(v_val_3679_);
lean_dec_ref(v___x_3678_);
v_r_3682_ = lean_box(v_res_3681_);
return v_r_3682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(lean_object* v_stx_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_){
_start:
{
uint8_t v___x_3687_; lean_object* v___x_3688_; 
v___x_3687_ = 0;
v___x_3688_ = l_Lean_Syntax_getRange_x3f(v_stx_3683_, v___x_3687_);
if (lean_obj_tag(v___x_3688_) == 1)
{
lean_object* v_val_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3702_; 
v_val_3689_ = lean_ctor_get(v___x_3688_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3691_ = v___x_3688_;
v_isShared_3692_ = v_isSharedCheck_3702_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_val_3689_);
lean_dec(v___x_3688_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3702_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3693_; lean_object* v_fileMap_3694_; lean_object* v_messages_3695_; lean_object* v___x_3696_; uint8_t v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3700_; 
v___x_3693_ = lean_st_ref_get(v_a_3685_);
v_fileMap_3694_ = lean_ctor_get(v_a_3684_, 1);
v_messages_3695_ = lean_ctor_get(v___x_3693_, 1);
lean_inc_ref(v_messages_3695_);
lean_dec(v___x_3693_);
v___x_3696_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_3695_);
v___x_3697_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v_fileMap_3694_, v_val_3689_, v___x_3696_);
lean_dec_ref(v___x_3696_);
lean_dec(v_val_3689_);
v___x_3698_ = lean_box(v___x_3697_);
if (v_isShared_3692_ == 0)
{
lean_ctor_set_tag(v___x_3691_, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3698_);
v___x_3700_ = v___x_3691_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v___x_3698_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
else
{
lean_object* v___x_3703_; lean_object* v___x_3704_; 
lean_dec(v___x_3688_);
v___x_3703_ = lean_box(v___x_3687_);
v___x_3704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3703_);
return v___x_3704_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError___boxed(lean_object* v_stx_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_){
_start:
{
lean_object* v_res_3709_; 
v_res_3709_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(v_stx_3705_, v_a_3706_, v_a_3707_);
lean_dec(v_a_3707_);
lean_dec_ref(v_a_3706_);
lean_dec(v_stx_3705_);
return v_res_3709_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(lean_object* v_tree_3710_, lean_object* v_fileMap_3711_, lean_object* v_c_3712_){
_start:
{
lean_object* v___y_3714_; lean_object* v_kind_3718_; lean_object* v_ref_3719_; lean_object* v___y_3721_; 
v_kind_3718_ = lean_ctor_get(v_c_3712_, 0);
lean_inc(v_kind_3718_);
v_ref_3719_ = lean_ctor_get(v_c_3712_, 1);
lean_inc(v_ref_3719_);
lean_dec_ref(v_c_3712_);
if (lean_obj_tag(v_kind_3718_) == 0)
{
lean_object* v_insertPos_3737_; 
lean_dec(v_ref_3719_);
v_insertPos_3737_ = lean_ctor_get(v_kind_3718_, 1);
lean_inc(v_insertPos_3737_);
v___y_3721_ = v_insertPos_3737_;
goto v___jp_3720_;
}
else
{
uint8_t v___x_3738_; lean_object* v___x_3739_; 
v___x_3738_ = 0;
v___x_3739_ = l_Lean_Syntax_getPos_x3f(v_ref_3719_, v___x_3738_);
lean_dec(v_ref_3719_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v___x_3740_; 
v___x_3740_ = lean_unsigned_to_nat(0u);
v___y_3721_ = v___x_3740_;
goto v___jp_3720_;
}
else
{
lean_object* v_val_3741_; 
v_val_3741_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_val_3741_);
lean_dec_ref_known(v___x_3739_, 1);
v___y_3721_ = v_val_3741_;
goto v___jp_3720_;
}
}
v___jp_3713_:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; uint8_t v___x_3717_; 
v___x_3715_ = l_List_lengthTR___redArg(v___y_3714_);
lean_dec(v___y_3714_);
v___x_3716_ = lean_unsigned_to_nat(1u);
v___x_3717_ = lean_nat_dec_eq(v___x_3715_, v___x_3716_);
lean_dec(v___x_3715_);
return v___x_3717_;
}
v___jp_3720_:
{
lean_object* v___x_3722_; 
v___x_3722_ = l_Lean_Elab_InfoTree_goalsAt_x3f(v_fileMap_3711_, v_tree_3710_, v___y_3721_);
if (lean_obj_tag(v___x_3722_) == 1)
{
lean_object* v_tail_3723_; 
v_tail_3723_ = lean_ctor_get(v___x_3722_, 1);
lean_inc(v_tail_3723_);
if (lean_obj_tag(v_tail_3723_) == 0)
{
if (lean_obj_tag(v_kind_3718_) == 0)
{
lean_object* v_head_3724_; lean_object* v_tacticSeq_3725_; uint8_t v___x_3726_; lean_object* v___x_3727_; 
v_head_3724_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_head_3724_);
lean_dec_ref_known(v___x_3722_, 2);
v_tacticSeq_3725_ = lean_ctor_get(v_kind_3718_, 0);
lean_inc(v_tacticSeq_3725_);
lean_dec_ref_known(v_kind_3718_, 2);
v___x_3726_ = 0;
v___x_3727_ = l_Lean_Syntax_getPos_x3f(v_tacticSeq_3725_, v___x_3726_);
lean_dec(v_tacticSeq_3725_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_tacticInfo_3728_; lean_object* v_goalsBefore_3729_; 
v_tacticInfo_3728_ = lean_ctor_get(v_head_3724_, 1);
lean_inc_ref(v_tacticInfo_3728_);
lean_dec(v_head_3724_);
v_goalsBefore_3729_ = lean_ctor_get(v_tacticInfo_3728_, 2);
lean_inc(v_goalsBefore_3729_);
lean_dec_ref(v_tacticInfo_3728_);
v___y_3714_ = v_goalsBefore_3729_;
goto v___jp_3713_;
}
else
{
lean_object* v_tacticInfo_3730_; lean_object* v_goalsAfter_3731_; 
lean_dec_ref_known(v___x_3727_, 1);
v_tacticInfo_3730_ = lean_ctor_get(v_head_3724_, 1);
lean_inc_ref(v_tacticInfo_3730_);
lean_dec(v_head_3724_);
v_goalsAfter_3731_ = lean_ctor_get(v_tacticInfo_3730_, 4);
lean_inc(v_goalsAfter_3731_);
lean_dec_ref(v_tacticInfo_3730_);
v___y_3714_ = v_goalsAfter_3731_;
goto v___jp_3713_;
}
}
else
{
lean_object* v_head_3732_; lean_object* v_tacticInfo_3733_; lean_object* v_goalsBefore_3734_; 
v_head_3732_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_head_3732_);
lean_dec_ref_known(v___x_3722_, 2);
v_tacticInfo_3733_ = lean_ctor_get(v_head_3732_, 1);
lean_inc_ref(v_tacticInfo_3733_);
lean_dec(v_head_3732_);
v_goalsBefore_3734_ = lean_ctor_get(v_tacticInfo_3733_, 2);
lean_inc(v_goalsBefore_3734_);
lean_dec_ref(v_tacticInfo_3733_);
v___y_3714_ = v_goalsBefore_3734_;
goto v___jp_3713_;
}
}
else
{
uint8_t v___x_3735_; 
lean_dec(v_tail_3723_);
lean_dec_ref_known(v___x_3722_, 2);
lean_dec(v_kind_3718_);
v___x_3735_ = 0;
return v___x_3735_;
}
}
else
{
uint8_t v___x_3736_; 
lean_dec(v___x_3722_);
lean_dec(v_kind_3718_);
v___x_3736_ = 0;
return v___x_3736_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos___boxed(lean_object* v_tree_3742_, lean_object* v_fileMap_3743_, lean_object* v_c_3744_){
_start:
{
uint8_t v_res_3745_; lean_object* v_r_3746_; 
v_res_3745_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(v_tree_3742_, v_fileMap_3743_, v_c_3744_);
v_r_3746_ = lean_box(v_res_3745_);
return v_r_3746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(lean_object* v___y_3747_){
_start:
{
lean_object* v___x_3749_; lean_object* v_infoState_3750_; lean_object* v_trees_3751_; lean_object* v___x_3752_; 
v___x_3749_ = lean_st_ref_get(v___y_3747_);
v_infoState_3750_ = lean_ctor_get(v___x_3749_, 8);
lean_inc_ref(v_infoState_3750_);
lean_dec(v___x_3749_);
v_trees_3751_ = lean_ctor_get(v_infoState_3750_, 2);
lean_inc_ref(v_trees_3751_);
lean_dec_ref(v_infoState_3750_);
v___x_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3752_, 0, v_trees_3751_);
return v___x_3752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg___boxed(lean_object* v___y_3753_, lean_object* v___y_3754_){
_start:
{
lean_object* v_res_3755_; 
v_res_3755_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_3753_);
lean_dec(v___y_3753_);
return v_res_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
lean_object* v___x_3759_; 
v___x_3759_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_3757_);
return v___x_3759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___boxed(lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
lean_object* v_res_3763_; 
v_res_3763_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(v___y_3760_, v___y_3761_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
return v_res_3763_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3765_; lean_object* v___x_3766_; 
v___x_3765_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__0));
v___x_3766_ = l_Lean_stringToMessageData(v___x_3765_);
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(lean_object* v_tree_3767_, lean_object* v___x_3768_, lean_object* v___x_3769_, lean_object* v_as_3770_, size_t v_sz_3771_, size_t v_i_3772_, lean_object* v_b_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
lean_object* v_a_3778_; uint8_t v___x_3782_; 
v___x_3782_ = lean_usize_dec_lt(v_i_3772_, v_sz_3771_);
if (v___x_3782_ == 0)
{
lean_object* v___x_3783_; 
lean_dec_ref(v___x_3768_);
lean_dec_ref(v_tree_3767_);
v___x_3783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3783_, 0, v_b_3773_);
return v___x_3783_;
}
else
{
lean_object* v___x_3784_; lean_object* v_a_3785_; uint8_t v___x_3786_; 
v___x_3784_ = lean_box(0);
v_a_3785_ = lean_array_uget_borrowed(v_as_3770_, v_i_3772_);
lean_inc(v_a_3785_);
lean_inc_ref(v___x_3768_);
lean_inc_ref(v_tree_3767_);
v___x_3786_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(v_tree_3767_, v___x_3768_, v_a_3785_);
if (v___x_3786_ == 0)
{
lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v_scopes_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v_opts_3793_; uint8_t v_hasTrace_3794_; 
v___x_3787_ = l_Lean_inheritedTraceOptions;
v___x_3788_ = lean_st_ref_get(v___x_3787_);
v___x_3789_ = lean_st_ref_get(v___y_3775_);
v_scopes_3790_ = lean_ctor_get(v___x_3789_, 2);
lean_inc(v_scopes_3790_);
lean_dec(v___x_3789_);
v___x_3791_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3792_ = l_List_head_x21___redArg(v___x_3791_, v_scopes_3790_);
lean_dec(v_scopes_3790_);
v_opts_3793_ = lean_ctor_get(v___x_3792_, 1);
lean_inc_ref(v_opts_3793_);
lean_dec(v___x_3792_);
v_hasTrace_3794_ = lean_ctor_get_uint8(v_opts_3793_, sizeof(void*)*1);
if (v_hasTrace_3794_ == 0)
{
lean_dec_ref(v_opts_3793_);
lean_dec(v___x_3788_);
v_a_3778_ = v___x_3784_;
goto v___jp_3777_;
}
else
{
lean_object* v___x_3795_; lean_object* v___x_3796_; uint8_t v___x_3797_; 
v___x_3795_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3796_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_3797_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3788_, v_opts_3793_, v___x_3796_);
lean_dec_ref(v_opts_3793_);
lean_dec(v___x_3788_);
if (v___x_3797_ == 0)
{
v_a_3778_ = v___x_3784_;
goto v___jp_3777_;
}
else
{
lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3798_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1);
v___x_3799_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_3795_, v___x_3798_, v___y_3774_, v___y_3775_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_dec_ref_known(v___x_3799_, 1);
v_a_3778_ = v___x_3784_;
goto v___jp_3777_;
}
else
{
lean_dec_ref(v___x_3768_);
lean_dec_ref(v_tree_3767_);
return v___x_3799_;
}
}
}
}
else
{
lean_object* v_kind_3800_; 
v_kind_3800_ = lean_ctor_get(v_a_3785_, 0);
if (lean_obj_tag(v_kind_3800_) == 0)
{
lean_object* v_ref_3801_; lean_object* v_tacticSeq_3802_; lean_object* v_insertPos_3803_; lean_object* v___x_3804_; 
v_ref_3801_ = lean_ctor_get(v_a_3785_, 1);
v_tacticSeq_3802_ = lean_ctor_get(v_kind_3800_, 0);
v_insertPos_3803_ = lean_ctor_get(v_kind_3800_, 1);
lean_inc(v_a_3785_);
v___x_3804_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(v_a_3785_, v___y_3774_, v___y_3775_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v_a_3805_; lean_object* v___x_3806_; 
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
lean_inc(v_a_3805_);
lean_dec_ref_known(v___x_3804_, 1);
lean_inc(v_insertPos_3803_);
lean_inc(v_ref_3801_);
v___x_3806_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(v_tacticSeq_3802_, v_ref_3801_, v_insertPos_3803_, v_a_3805_, v___x_3769_, v___y_3774_, v___y_3775_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_dec_ref_known(v___x_3806_, 1);
v_a_3778_ = v___x_3784_;
goto v___jp_3777_;
}
else
{
lean_dec_ref(v___x_3768_);
lean_dec_ref(v_tree_3767_);
return v___x_3806_;
}
}
else
{
lean_object* v_a_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3814_; 
lean_dec_ref(v___x_3768_);
lean_dec_ref(v_tree_3767_);
v_a_3807_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3814_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3809_ = v___x_3804_;
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_a_3807_);
lean_dec(v___x_3804_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3812_; 
if (v_isShared_3810_ == 0)
{
v___x_3812_ = v___x_3809_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_a_3807_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
}
else
{
lean_object* v___x_3815_; 
lean_inc(v_a_3785_);
v___x_3815_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(v_a_3785_, v___y_3774_, v___y_3775_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_dec_ref_known(v___x_3815_, 1);
v_a_3778_ = v___x_3784_;
goto v___jp_3777_;
}
else
{
lean_dec_ref(v___x_3768_);
lean_dec_ref(v_tree_3767_);
return v___x_3815_;
}
}
}
}
v___jp_3777_:
{
size_t v___x_3779_; size_t v___x_3780_; 
v___x_3779_ = ((size_t)1ULL);
v___x_3780_ = lean_usize_add(v_i_3772_, v___x_3779_);
v_i_3772_ = v___x_3780_;
v_b_3773_ = v_a_3778_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___boxed(lean_object* v_tree_3816_, lean_object* v___x_3817_, lean_object* v___x_3818_, lean_object* v_as_3819_, lean_object* v_sz_3820_, lean_object* v_i_3821_, lean_object* v_b_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_){
_start:
{
size_t v_sz_boxed_3826_; size_t v_i_boxed_3827_; lean_object* v_res_3828_; 
v_sz_boxed_3826_ = lean_unbox_usize(v_sz_3820_);
lean_dec(v_sz_3820_);
v_i_boxed_3827_ = lean_unbox_usize(v_i_3821_);
lean_dec(v_i_3821_);
v_res_3828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_tree_3816_, v___x_3817_, v___x_3818_, v_as_3819_, v_sz_boxed_3826_, v_i_boxed_3827_, v_b_3822_, v___y_3823_, v___y_3824_);
lean_dec(v___y_3824_);
lean_dec_ref(v___y_3823_);
lean_dec_ref(v_as_3819_);
lean_dec(v___x_3818_);
return v_res_3828_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3833_; lean_object* v___x_3834_; 
v___x_3833_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__1));
v___x_3834_ = l_Lean_stringToMessageData(v___x_3833_);
return v___x_3834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(lean_object* v_stx_3835_, lean_object* v___x_3836_, lean_object* v___x_3837_, lean_object* v___x_3838_, lean_object* v___x_3839_, lean_object* v_as_3840_, size_t v_sz_3841_, size_t v_i_3842_, lean_object* v_b_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_){
_start:
{
uint8_t v___x_3847_; 
v___x_3847_ = lean_usize_dec_lt(v_i_3842_, v_sz_3841_);
if (v___x_3847_ == 0)
{
lean_object* v___x_3848_; 
lean_dec_ref(v___x_3838_);
lean_dec(v_stx_3835_);
v___x_3848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3848_, 0, v_b_3843_);
return v___x_3848_;
}
else
{
lean_object* v_a_3849_; lean_object* v___x_3850_; 
lean_dec_ref(v_b_3843_);
v_a_3849_ = lean_array_uget_borrowed(v_as_3840_, v_i_3842_);
lean_inc(v_a_3849_);
lean_inc(v_stx_3835_);
v___x_3850_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3835_, v___x_3836_, v_a_3849_, v___x_3837_, v___y_3844_, v___y_3845_);
if (lean_obj_tag(v___x_3850_) == 0)
{
lean_object* v_a_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v_scopes_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v_opts_3858_; uint8_t v_hasTrace_3859_; lean_object* v___x_3860_; lean_object* v___y_3862_; lean_object* v___y_3863_; 
v_a_3851_ = lean_ctor_get(v___x_3850_, 0);
lean_inc(v_a_3851_);
lean_dec_ref_known(v___x_3850_, 1);
v___x_3852_ = l_Lean_inheritedTraceOptions;
v___x_3853_ = lean_st_ref_get(v___x_3852_);
v___x_3854_ = lean_st_ref_get(v___y_3845_);
v_scopes_3855_ = lean_ctor_get(v___x_3854_, 2);
lean_inc(v_scopes_3855_);
lean_dec(v___x_3854_);
v___x_3856_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3857_ = l_List_head_x21___redArg(v___x_3856_, v_scopes_3855_);
lean_dec(v_scopes_3855_);
v_opts_3858_ = lean_ctor_get(v___x_3857_, 1);
lean_inc_ref(v_opts_3858_);
lean_dec(v___x_3857_);
v_hasTrace_3859_ = lean_ctor_get_uint8(v_opts_3858_, sizeof(void*)*1);
v___x_3860_ = lean_box(0);
if (v_hasTrace_3859_ == 0)
{
lean_dec_ref(v_opts_3858_);
lean_dec(v___x_3853_);
v___y_3862_ = v___y_3844_;
v___y_3863_ = v___y_3845_;
goto v___jp_3861_;
}
else
{
lean_object* v___x_3879_; lean_object* v___x_3880_; uint8_t v___x_3881_; 
v___x_3879_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3880_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_3881_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3853_, v_opts_3858_, v___x_3880_);
lean_dec_ref(v_opts_3858_);
lean_dec(v___x_3853_);
if (v___x_3881_ == 0)
{
v___y_3862_ = v___y_3844_;
v___y_3863_ = v___y_3845_;
goto v___jp_3861_;
}
else
{
lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3882_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_3883_ = lean_array_get_size(v_a_3851_);
v___x_3884_ = l_Nat_reprFast(v___x_3883_);
v___x_3885_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3885_, 0, v___x_3884_);
v___x_3886_ = l_Lean_MessageData_ofFormat(v___x_3885_);
v___x_3887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3882_);
lean_ctor_set(v___x_3887_, 1, v___x_3886_);
v___x_3888_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_3879_, v___x_3887_, v___y_3844_, v___y_3845_);
if (lean_obj_tag(v___x_3888_) == 0)
{
lean_dec_ref_known(v___x_3888_, 1);
v___y_3862_ = v___y_3844_;
v___y_3863_ = v___y_3845_;
goto v___jp_3861_;
}
else
{
lean_object* v_a_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3896_; 
lean_dec(v_a_3851_);
lean_dec_ref(v___x_3838_);
lean_dec(v_stx_3835_);
v_a_3889_ = lean_ctor_get(v___x_3888_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3888_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3891_ = v___x_3888_;
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_a_3889_);
lean_dec(v___x_3888_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3894_; 
if (v_isShared_3892_ == 0)
{
v___x_3894_ = v___x_3891_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_a_3889_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
}
}
v___jp_3861_:
{
size_t v_sz_3864_; size_t v___x_3865_; lean_object* v___x_3866_; 
v_sz_3864_ = lean_array_size(v_a_3851_);
v___x_3865_ = ((size_t)0ULL);
lean_inc_ref(v___x_3838_);
lean_inc(v_a_3849_);
v___x_3866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_3849_, v___x_3838_, v___x_3839_, v_a_3851_, v_sz_3864_, v___x_3865_, v___x_3860_, v___y_3862_, v___y_3863_);
lean_dec(v_a_3851_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_object* v___x_3867_; size_t v___x_3868_; size_t v___x_3869_; 
lean_dec_ref_known(v___x_3866_, 1);
v___x_3867_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_3868_ = ((size_t)1ULL);
v___x_3869_ = lean_usize_add(v_i_3842_, v___x_3868_);
v_i_3842_ = v___x_3869_;
v_b_3843_ = v___x_3867_;
goto _start;
}
else
{
lean_object* v_a_3871_; lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3878_; 
lean_dec_ref(v___x_3838_);
lean_dec(v_stx_3835_);
v_a_3871_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3878_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3873_ = v___x_3866_;
v_isShared_3874_ = v_isSharedCheck_3878_;
goto v_resetjp_3872_;
}
else
{
lean_inc(v_a_3871_);
lean_dec(v___x_3866_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3878_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
lean_object* v___x_3876_; 
if (v_isShared_3874_ == 0)
{
v___x_3876_ = v___x_3873_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v_a_3871_);
v___x_3876_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
return v___x_3876_;
}
}
}
}
}
else
{
lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3904_; 
lean_dec_ref(v___x_3838_);
lean_dec(v_stx_3835_);
v_a_3897_ = lean_ctor_get(v___x_3850_, 0);
v_isSharedCheck_3904_ = !lean_is_exclusive(v___x_3850_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3899_ = v___x_3850_;
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3850_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3902_; 
if (v_isShared_3900_ == 0)
{
v___x_3902_ = v___x_3899_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_a_3897_);
v___x_3902_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
return v___x_3902_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___boxed(lean_object* v_stx_3905_, lean_object* v___x_3906_, lean_object* v___x_3907_, lean_object* v___x_3908_, lean_object* v___x_3909_, lean_object* v_as_3910_, lean_object* v_sz_3911_, lean_object* v_i_3912_, lean_object* v_b_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_){
_start:
{
size_t v_sz_boxed_3917_; size_t v_i_boxed_3918_; lean_object* v_res_3919_; 
v_sz_boxed_3917_ = lean_unbox_usize(v_sz_3911_);
lean_dec(v_sz_3911_);
v_i_boxed_3918_ = lean_unbox_usize(v_i_3912_);
lean_dec(v_i_3912_);
v_res_3919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_3905_, v___x_3906_, v___x_3907_, v___x_3908_, v___x_3909_, v_as_3910_, v_sz_boxed_3917_, v_i_boxed_3918_, v_b_3913_, v___y_3914_, v___y_3915_);
lean_dec(v___y_3915_);
lean_dec_ref(v___y_3914_);
lean_dec_ref(v_as_3910_);
lean_dec(v___x_3909_);
lean_dec_ref(v___x_3907_);
lean_dec_ref(v___x_3906_);
return v_res_3919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(lean_object* v_stx_3920_, lean_object* v___x_3921_, lean_object* v___x_3922_, lean_object* v___x_3923_, lean_object* v___x_3924_, lean_object* v_as_3925_, size_t v_sz_3926_, size_t v_i_3927_, lean_object* v_b_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_){
_start:
{
uint8_t v___x_3932_; 
v___x_3932_ = lean_usize_dec_lt(v_i_3927_, v_sz_3926_);
if (v___x_3932_ == 0)
{
lean_object* v___x_3933_; 
lean_dec_ref(v___x_3923_);
lean_dec(v_stx_3920_);
v___x_3933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3933_, 0, v_b_3928_);
return v___x_3933_;
}
else
{
lean_object* v_a_3934_; lean_object* v___x_3935_; 
lean_dec_ref(v_b_3928_);
v_a_3934_ = lean_array_uget_borrowed(v_as_3925_, v_i_3927_);
lean_inc(v_a_3934_);
lean_inc(v_stx_3920_);
v___x_3935_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3920_, v___x_3921_, v_a_3934_, v___x_3922_, v___y_3929_, v___y_3930_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v_a_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v_scopes_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v_opts_3943_; uint8_t v_hasTrace_3944_; lean_object* v___x_3945_; lean_object* v___y_3947_; lean_object* v___y_3948_; 
v_a_3936_ = lean_ctor_get(v___x_3935_, 0);
lean_inc(v_a_3936_);
lean_dec_ref_known(v___x_3935_, 1);
v___x_3937_ = l_Lean_inheritedTraceOptions;
v___x_3938_ = lean_st_ref_get(v___x_3937_);
v___x_3939_ = lean_st_ref_get(v___y_3930_);
v_scopes_3940_ = lean_ctor_get(v___x_3939_, 2);
lean_inc(v_scopes_3940_);
lean_dec(v___x_3939_);
v___x_3941_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3942_ = l_List_head_x21___redArg(v___x_3941_, v_scopes_3940_);
lean_dec(v_scopes_3940_);
v_opts_3943_ = lean_ctor_get(v___x_3942_, 1);
lean_inc_ref(v_opts_3943_);
lean_dec(v___x_3942_);
v_hasTrace_3944_ = lean_ctor_get_uint8(v_opts_3943_, sizeof(void*)*1);
v___x_3945_ = lean_box(0);
if (v_hasTrace_3944_ == 0)
{
lean_dec_ref(v_opts_3943_);
lean_dec(v___x_3938_);
v___y_3947_ = v___y_3929_;
v___y_3948_ = v___y_3930_;
goto v___jp_3946_;
}
else
{
lean_object* v___x_3964_; lean_object* v___x_3965_; uint8_t v___x_3966_; 
v___x_3964_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3965_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_3966_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3938_, v_opts_3943_, v___x_3965_);
lean_dec_ref(v_opts_3943_);
lean_dec(v___x_3938_);
if (v___x_3966_ == 0)
{
v___y_3947_ = v___y_3929_;
v___y_3948_ = v___y_3930_;
goto v___jp_3946_;
}
else
{
lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3967_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_3968_ = lean_array_get_size(v_a_3936_);
v___x_3969_ = l_Nat_reprFast(v___x_3968_);
v___x_3970_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3969_);
v___x_3971_ = l_Lean_MessageData_ofFormat(v___x_3970_);
v___x_3972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3967_);
lean_ctor_set(v___x_3972_, 1, v___x_3971_);
v___x_3973_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_3964_, v___x_3972_, v___y_3929_, v___y_3930_);
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_dec_ref_known(v___x_3973_, 1);
v___y_3947_ = v___y_3929_;
v___y_3948_ = v___y_3930_;
goto v___jp_3946_;
}
else
{
lean_object* v_a_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3981_; 
lean_dec(v_a_3936_);
lean_dec_ref(v___x_3923_);
lean_dec(v_stx_3920_);
v_a_3974_ = lean_ctor_get(v___x_3973_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3976_ = v___x_3973_;
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_a_3974_);
lean_dec(v___x_3973_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v___x_3979_; 
if (v_isShared_3977_ == 0)
{
v___x_3979_ = v___x_3976_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v_a_3974_);
v___x_3979_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
return v___x_3979_;
}
}
}
}
}
v___jp_3946_:
{
size_t v_sz_3949_; size_t v___x_3950_; lean_object* v___x_3951_; 
v_sz_3949_ = lean_array_size(v_a_3936_);
v___x_3950_ = ((size_t)0ULL);
lean_inc_ref(v___x_3923_);
lean_inc(v_a_3934_);
v___x_3951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_3934_, v___x_3923_, v___x_3924_, v_a_3936_, v_sz_3949_, v___x_3950_, v___x_3945_, v___y_3947_, v___y_3948_);
lean_dec(v_a_3936_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_object* v___x_3952_; size_t v___x_3953_; size_t v___x_3954_; lean_object* v___x_3955_; 
lean_dec_ref_known(v___x_3951_, 1);
v___x_3952_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_3953_ = ((size_t)1ULL);
v___x_3954_ = lean_usize_add(v_i_3927_, v___x_3953_);
v___x_3955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_3920_, v___x_3921_, v___x_3922_, v___x_3923_, v___x_3924_, v_as_3925_, v_sz_3926_, v___x_3954_, v___x_3952_, v___y_3929_, v___y_3930_);
return v___x_3955_;
}
else
{
lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3963_; 
lean_dec_ref(v___x_3923_);
lean_dec(v_stx_3920_);
v_a_3956_ = lean_ctor_get(v___x_3951_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3951_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3958_ = v___x_3951_;
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___x_3951_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3961_; 
if (v_isShared_3959_ == 0)
{
v___x_3961_ = v___x_3958_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_a_3956_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
}
}
}
else
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3989_; 
lean_dec_ref(v___x_3923_);
lean_dec(v_stx_3920_);
v_a_3982_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3984_ = v___x_3935_;
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3935_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3987_; 
if (v_isShared_3985_ == 0)
{
v___x_3987_ = v___x_3984_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_a_3982_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3___boxed(lean_object* v_stx_3990_, lean_object* v___x_3991_, lean_object* v___x_3992_, lean_object* v___x_3993_, lean_object* v___x_3994_, lean_object* v_as_3995_, lean_object* v_sz_3996_, lean_object* v_i_3997_, lean_object* v_b_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_){
_start:
{
size_t v_sz_boxed_4002_; size_t v_i_boxed_4003_; lean_object* v_res_4004_; 
v_sz_boxed_4002_ = lean_unbox_usize(v_sz_3996_);
lean_dec(v_sz_3996_);
v_i_boxed_4003_ = lean_unbox_usize(v_i_3997_);
lean_dec(v_i_3997_);
v_res_4004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(v_stx_3990_, v___x_3991_, v___x_3992_, v___x_3993_, v___x_3994_, v_as_3995_, v_sz_boxed_4002_, v_i_boxed_4003_, v_b_3998_, v___y_3999_, v___y_4000_);
lean_dec(v___y_4000_);
lean_dec_ref(v___y_3999_);
lean_dec_ref(v_as_3995_);
lean_dec(v___x_3994_);
lean_dec_ref(v___x_3992_);
lean_dec_ref(v___x_3991_);
return v_res_4004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(lean_object* v_stx_4008_, lean_object* v___x_4009_, lean_object* v___x_4010_, lean_object* v___x_4011_, lean_object* v___x_4012_, lean_object* v_as_4013_, size_t v_sz_4014_, size_t v_i_4015_, lean_object* v_b_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_){
_start:
{
uint8_t v___x_4020_; 
v___x_4020_ = lean_usize_dec_lt(v_i_4015_, v_sz_4014_);
if (v___x_4020_ == 0)
{
lean_object* v___x_4021_; 
lean_dec_ref(v___x_4011_);
lean_dec(v_stx_4008_);
v___x_4021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4021_, 0, v_b_4016_);
return v___x_4021_;
}
else
{
lean_object* v_a_4022_; lean_object* v___x_4023_; 
lean_dec_ref(v_b_4016_);
v_a_4022_ = lean_array_uget_borrowed(v_as_4013_, v_i_4015_);
lean_inc(v_a_4022_);
lean_inc(v_stx_4008_);
v___x_4023_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_4008_, v___x_4009_, v_a_4022_, v___x_4010_, v___y_4017_, v___y_4018_);
if (lean_obj_tag(v___x_4023_) == 0)
{
lean_object* v_a_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v_scopes_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v_opts_4031_; uint8_t v_hasTrace_4032_; lean_object* v___x_4033_; lean_object* v___y_4035_; lean_object* v___y_4036_; 
v_a_4024_ = lean_ctor_get(v___x_4023_, 0);
lean_inc(v_a_4024_);
lean_dec_ref_known(v___x_4023_, 1);
v___x_4025_ = l_Lean_inheritedTraceOptions;
v___x_4026_ = lean_st_ref_get(v___x_4025_);
v___x_4027_ = lean_st_ref_get(v___y_4018_);
v_scopes_4028_ = lean_ctor_get(v___x_4027_, 2);
lean_inc(v_scopes_4028_);
lean_dec(v___x_4027_);
v___x_4029_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4030_ = l_List_head_x21___redArg(v___x_4029_, v_scopes_4028_);
lean_dec(v_scopes_4028_);
v_opts_4031_ = lean_ctor_get(v___x_4030_, 1);
lean_inc_ref(v_opts_4031_);
lean_dec(v___x_4030_);
v_hasTrace_4032_ = lean_ctor_get_uint8(v_opts_4031_, sizeof(void*)*1);
v___x_4033_ = lean_box(0);
if (v_hasTrace_4032_ == 0)
{
lean_dec_ref(v_opts_4031_);
lean_dec(v___x_4026_);
v___y_4035_ = v___y_4017_;
v___y_4036_ = v___y_4018_;
goto v___jp_4034_;
}
else
{
lean_object* v___x_4052_; lean_object* v___x_4053_; uint8_t v___x_4054_; 
v___x_4052_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4053_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_4054_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4026_, v_opts_4031_, v___x_4053_);
lean_dec_ref(v_opts_4031_);
lean_dec(v___x_4026_);
if (v___x_4054_ == 0)
{
v___y_4035_ = v___y_4017_;
v___y_4036_ = v___y_4018_;
goto v___jp_4034_;
}
else
{
lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4055_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_4056_ = lean_array_get_size(v_a_4024_);
v___x_4057_ = l_Nat_reprFast(v___x_4056_);
v___x_4058_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4058_, 0, v___x_4057_);
v___x_4059_ = l_Lean_MessageData_ofFormat(v___x_4058_);
v___x_4060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4060_, 0, v___x_4055_);
lean_ctor_set(v___x_4060_, 1, v___x_4059_);
v___x_4061_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_4052_, v___x_4060_, v___y_4017_, v___y_4018_);
if (lean_obj_tag(v___x_4061_) == 0)
{
lean_dec_ref_known(v___x_4061_, 1);
v___y_4035_ = v___y_4017_;
v___y_4036_ = v___y_4018_;
goto v___jp_4034_;
}
else
{
lean_object* v_a_4062_; lean_object* v___x_4064_; uint8_t v_isShared_4065_; uint8_t v_isSharedCheck_4069_; 
lean_dec(v_a_4024_);
lean_dec_ref(v___x_4011_);
lean_dec(v_stx_4008_);
v_a_4062_ = lean_ctor_get(v___x_4061_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_4061_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4064_ = v___x_4061_;
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
else
{
lean_inc(v_a_4062_);
lean_dec(v___x_4061_);
v___x_4064_ = lean_box(0);
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
v_resetjp_4063_:
{
lean_object* v___x_4067_; 
if (v_isShared_4065_ == 0)
{
v___x_4067_ = v___x_4064_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_a_4062_);
v___x_4067_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
return v___x_4067_;
}
}
}
}
}
v___jp_4034_:
{
size_t v_sz_4037_; size_t v___x_4038_; lean_object* v___x_4039_; 
v_sz_4037_ = lean_array_size(v_a_4024_);
v___x_4038_ = ((size_t)0ULL);
lean_inc_ref(v___x_4011_);
lean_inc(v_a_4022_);
v___x_4039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4022_, v___x_4011_, v___x_4012_, v_a_4024_, v_sz_4037_, v___x_4038_, v___x_4033_, v___y_4035_, v___y_4036_);
lean_dec(v_a_4024_);
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_object* v___x_4040_; size_t v___x_4041_; size_t v___x_4042_; 
lean_dec_ref_known(v___x_4039_, 1);
v___x_4040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_4041_ = ((size_t)1ULL);
v___x_4042_ = lean_usize_add(v_i_4015_, v___x_4041_);
v_i_4015_ = v___x_4042_;
v_b_4016_ = v___x_4040_;
goto _start;
}
else
{
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4051_; 
lean_dec_ref(v___x_4011_);
lean_dec(v_stx_4008_);
v_a_4044_ = lean_ctor_get(v___x_4039_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_4039_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4046_ = v___x_4039_;
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___x_4039_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4049_; 
if (v_isShared_4047_ == 0)
{
v___x_4049_ = v___x_4046_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4044_);
v___x_4049_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
return v___x_4049_;
}
}
}
}
}
else
{
lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4077_; 
lean_dec_ref(v___x_4011_);
lean_dec(v_stx_4008_);
v_a_4070_ = lean_ctor_get(v___x_4023_, 0);
v_isSharedCheck_4077_ = !lean_is_exclusive(v___x_4023_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_4072_ = v___x_4023_;
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v___x_4023_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4075_; 
if (v_isShared_4073_ == 0)
{
v___x_4075_ = v___x_4072_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_a_4070_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_stx_4078_, lean_object* v___x_4079_, lean_object* v___x_4080_, lean_object* v___x_4081_, lean_object* v___x_4082_, lean_object* v_as_4083_, lean_object* v_sz_4084_, lean_object* v_i_4085_, lean_object* v_b_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
size_t v_sz_boxed_4090_; size_t v_i_boxed_4091_; lean_object* v_res_4092_; 
v_sz_boxed_4090_ = lean_unbox_usize(v_sz_4084_);
lean_dec(v_sz_4084_);
v_i_boxed_4091_ = lean_unbox_usize(v_i_4085_);
lean_dec(v_i_4085_);
v_res_4092_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4078_, v___x_4079_, v___x_4080_, v___x_4081_, v___x_4082_, v_as_4083_, v_sz_boxed_4090_, v_i_boxed_4091_, v_b_4086_, v___y_4087_, v___y_4088_);
lean_dec(v___y_4088_);
lean_dec_ref(v___y_4087_);
lean_dec_ref(v_as_4083_);
lean_dec(v___x_4082_);
lean_dec_ref(v___x_4080_);
lean_dec_ref(v___x_4079_);
return v_res_4092_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(lean_object* v_stx_4093_, lean_object* v___x_4094_, lean_object* v___x_4095_, lean_object* v___x_4096_, lean_object* v___x_4097_, lean_object* v_as_4098_, size_t v_sz_4099_, size_t v_i_4100_, lean_object* v_b_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_){
_start:
{
uint8_t v___x_4105_; 
v___x_4105_ = lean_usize_dec_lt(v_i_4100_, v_sz_4099_);
if (v___x_4105_ == 0)
{
lean_object* v___x_4106_; 
lean_dec_ref(v___x_4096_);
lean_dec(v_stx_4093_);
v___x_4106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4106_, 0, v_b_4101_);
return v___x_4106_;
}
else
{
lean_object* v_a_4107_; lean_object* v___x_4108_; 
lean_dec_ref(v_b_4101_);
v_a_4107_ = lean_array_uget_borrowed(v_as_4098_, v_i_4100_);
lean_inc(v_a_4107_);
lean_inc(v_stx_4093_);
v___x_4108_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_4093_, v___x_4094_, v_a_4107_, v___x_4095_, v___y_4102_, v___y_4103_);
if (lean_obj_tag(v___x_4108_) == 0)
{
lean_object* v_a_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v_scopes_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v_opts_4116_; uint8_t v_hasTrace_4117_; lean_object* v___x_4118_; lean_object* v___y_4120_; lean_object* v___y_4121_; 
v_a_4109_ = lean_ctor_get(v___x_4108_, 0);
lean_inc(v_a_4109_);
lean_dec_ref_known(v___x_4108_, 1);
v___x_4110_ = l_Lean_inheritedTraceOptions;
v___x_4111_ = lean_st_ref_get(v___x_4110_);
v___x_4112_ = lean_st_ref_get(v___y_4103_);
v_scopes_4113_ = lean_ctor_get(v___x_4112_, 2);
lean_inc(v_scopes_4113_);
lean_dec(v___x_4112_);
v___x_4114_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4115_ = l_List_head_x21___redArg(v___x_4114_, v_scopes_4113_);
lean_dec(v_scopes_4113_);
v_opts_4116_ = lean_ctor_get(v___x_4115_, 1);
lean_inc_ref(v_opts_4116_);
lean_dec(v___x_4115_);
v_hasTrace_4117_ = lean_ctor_get_uint8(v_opts_4116_, sizeof(void*)*1);
v___x_4118_ = lean_box(0);
if (v_hasTrace_4117_ == 0)
{
lean_dec_ref(v_opts_4116_);
lean_dec(v___x_4111_);
v___y_4120_ = v___y_4102_;
v___y_4121_ = v___y_4103_;
goto v___jp_4119_;
}
else
{
lean_object* v___x_4137_; lean_object* v___x_4138_; uint8_t v___x_4139_; 
v___x_4137_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4138_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_4139_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4111_, v_opts_4116_, v___x_4138_);
lean_dec_ref(v_opts_4116_);
lean_dec(v___x_4111_);
if (v___x_4139_ == 0)
{
v___y_4120_ = v___y_4102_;
v___y_4121_ = v___y_4103_;
goto v___jp_4119_;
}
else
{
lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; 
v___x_4140_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_4141_ = lean_array_get_size(v_a_4109_);
v___x_4142_ = l_Nat_reprFast(v___x_4141_);
v___x_4143_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4142_);
v___x_4144_ = l_Lean_MessageData_ofFormat(v___x_4143_);
v___x_4145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4145_, 0, v___x_4140_);
lean_ctor_set(v___x_4145_, 1, v___x_4144_);
v___x_4146_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_4137_, v___x_4145_, v___y_4102_, v___y_4103_);
if (lean_obj_tag(v___x_4146_) == 0)
{
lean_dec_ref_known(v___x_4146_, 1);
v___y_4120_ = v___y_4102_;
v___y_4121_ = v___y_4103_;
goto v___jp_4119_;
}
else
{
lean_object* v_a_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4154_; 
lean_dec(v_a_4109_);
lean_dec_ref(v___x_4096_);
lean_dec(v_stx_4093_);
v_a_4147_ = lean_ctor_get(v___x_4146_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4146_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4149_ = v___x_4146_;
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_a_4147_);
lean_dec(v___x_4146_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___x_4152_; 
if (v_isShared_4150_ == 0)
{
v___x_4152_ = v___x_4149_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_a_4147_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
}
v___jp_4119_:
{
size_t v_sz_4122_; size_t v___x_4123_; lean_object* v___x_4124_; 
v_sz_4122_ = lean_array_size(v_a_4109_);
v___x_4123_ = ((size_t)0ULL);
lean_inc_ref(v___x_4096_);
lean_inc(v_a_4107_);
v___x_4124_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4107_, v___x_4096_, v___x_4097_, v_a_4109_, v_sz_4122_, v___x_4123_, v___x_4118_, v___y_4120_, v___y_4121_);
lean_dec(v_a_4109_);
if (lean_obj_tag(v___x_4124_) == 0)
{
lean_object* v___x_4125_; size_t v___x_4126_; size_t v___x_4127_; lean_object* v___x_4128_; 
lean_dec_ref_known(v___x_4124_, 1);
v___x_4125_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_4126_ = ((size_t)1ULL);
v___x_4127_ = lean_usize_add(v_i_4100_, v___x_4126_);
v___x_4128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4093_, v___x_4094_, v___x_4095_, v___x_4096_, v___x_4097_, v_as_4098_, v_sz_4099_, v___x_4127_, v___x_4125_, v___y_4102_, v___y_4103_);
return v___x_4128_;
}
else
{
lean_object* v_a_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4136_; 
lean_dec_ref(v___x_4096_);
lean_dec(v_stx_4093_);
v_a_4129_ = lean_ctor_get(v___x_4124_, 0);
v_isSharedCheck_4136_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4131_ = v___x_4124_;
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_a_4129_);
lean_dec(v___x_4124_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v___x_4134_; 
if (v_isShared_4132_ == 0)
{
v___x_4134_ = v___x_4131_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_a_4129_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
return v___x_4134_;
}
}
}
}
}
else
{
lean_object* v_a_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4162_; 
lean_dec_ref(v___x_4096_);
lean_dec(v_stx_4093_);
v_a_4155_ = lean_ctor_get(v___x_4108_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4157_ = v___x_4108_;
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_a_4155_);
lean_dec(v___x_4108_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4160_; 
if (v_isShared_4158_ == 0)
{
v___x_4160_ = v___x_4157_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_a_4155_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4___boxed(lean_object* v_stx_4163_, lean_object* v___x_4164_, lean_object* v___x_4165_, lean_object* v___x_4166_, lean_object* v___x_4167_, lean_object* v_as_4168_, lean_object* v_sz_4169_, lean_object* v_i_4170_, lean_object* v_b_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_){
_start:
{
size_t v_sz_boxed_4175_; size_t v_i_boxed_4176_; lean_object* v_res_4177_; 
v_sz_boxed_4175_ = lean_unbox_usize(v_sz_4169_);
lean_dec(v_sz_4169_);
v_i_boxed_4176_ = lean_unbox_usize(v_i_4170_);
lean_dec(v_i_4170_);
v_res_4177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(v_stx_4163_, v___x_4164_, v___x_4165_, v___x_4166_, v___x_4167_, v_as_4168_, v_sz_boxed_4175_, v_i_boxed_4176_, v_b_4171_, v___y_4172_, v___y_4173_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
lean_dec_ref(v_as_4168_);
lean_dec(v___x_4167_);
lean_dec_ref(v___x_4165_);
lean_dec_ref(v___x_4164_);
return v_res_4177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(lean_object* v_init_4178_, lean_object* v_stx_4179_, lean_object* v___x_4180_, lean_object* v___x_4181_, lean_object* v___x_4182_, lean_object* v___x_4183_, lean_object* v_n_4184_, lean_object* v_b_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_){
_start:
{
if (lean_obj_tag(v_n_4184_) == 0)
{
lean_object* v_cs_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; size_t v_sz_4192_; size_t v___x_4193_; lean_object* v___x_4194_; 
v_cs_4189_ = lean_ctor_get(v_n_4184_, 0);
v___x_4190_ = lean_box(0);
v___x_4191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4190_);
lean_ctor_set(v___x_4191_, 1, v_b_4185_);
v_sz_4192_ = lean_array_size(v_cs_4189_);
v___x_4193_ = ((size_t)0ULL);
v___x_4194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(v_init_4178_, v_stx_4179_, v___x_4180_, v___x_4181_, v___x_4182_, v___x_4183_, v_cs_4189_, v_sz_4192_, v___x_4193_, v___x_4191_, v___y_4186_, v___y_4187_);
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
else
{
lean_object* v_vs_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; size_t v_sz_4221_; size_t v___x_4222_; lean_object* v___x_4223_; 
v_vs_4218_ = lean_ctor_get(v_n_4184_, 0);
v___x_4219_ = lean_box(0);
v___x_4220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4220_, 0, v___x_4219_);
lean_ctor_set(v___x_4220_, 1, v_b_4185_);
v_sz_4221_ = lean_array_size(v_vs_4218_);
v___x_4222_ = ((size_t)0ULL);
v___x_4223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(v_stx_4179_, v___x_4180_, v___x_4181_, v___x_4182_, v___x_4183_, v_vs_4218_, v_sz_4221_, v___x_4222_, v___x_4220_, v___y_4186_, v___y_4187_);
if (lean_obj_tag(v___x_4223_) == 0)
{
lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4238_; 
v_a_4224_ = lean_ctor_get(v___x_4223_, 0);
v_isSharedCheck_4238_ = !lean_is_exclusive(v___x_4223_);
if (v_isSharedCheck_4238_ == 0)
{
v___x_4226_ = v___x_4223_;
v_isShared_4227_ = v_isSharedCheck_4238_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_dec(v___x_4223_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4238_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v_fst_4228_; 
v_fst_4228_ = lean_ctor_get(v_a_4224_, 0);
if (lean_obj_tag(v_fst_4228_) == 0)
{
lean_object* v_snd_4229_; lean_object* v___x_4230_; lean_object* v___x_4232_; 
v_snd_4229_ = lean_ctor_get(v_a_4224_, 1);
lean_inc(v_snd_4229_);
lean_dec(v_a_4224_);
v___x_4230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4230_, 0, v_snd_4229_);
if (v_isShared_4227_ == 0)
{
lean_ctor_set(v___x_4226_, 0, v___x_4230_);
v___x_4232_ = v___x_4226_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v___x_4230_);
v___x_4232_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
return v___x_4232_;
}
}
else
{
lean_object* v_val_4234_; lean_object* v___x_4236_; 
lean_inc_ref(v_fst_4228_);
lean_dec(v_a_4224_);
v_val_4234_ = lean_ctor_get(v_fst_4228_, 0);
lean_inc(v_val_4234_);
lean_dec_ref_known(v_fst_4228_, 1);
if (v_isShared_4227_ == 0)
{
lean_ctor_set(v___x_4226_, 0, v_val_4234_);
v___x_4236_ = v___x_4226_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_val_4234_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
}
}
else
{
lean_object* v_a_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4246_; 
v_a_4239_ = lean_ctor_get(v___x_4223_, 0);
v_isSharedCheck_4246_ = !lean_is_exclusive(v___x_4223_);
if (v_isSharedCheck_4246_ == 0)
{
v___x_4241_ = v___x_4223_;
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_a_4239_);
lean_dec(v___x_4223_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
lean_object* v___x_4244_; 
if (v_isShared_4242_ == 0)
{
v___x_4244_ = v___x_4241_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_a_4239_);
v___x_4244_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
return v___x_4244_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(lean_object* v_init_4247_, lean_object* v_stx_4248_, lean_object* v___x_4249_, lean_object* v___x_4250_, lean_object* v___x_4251_, lean_object* v___x_4252_, lean_object* v_as_4253_, size_t v_sz_4254_, size_t v_i_4255_, lean_object* v_b_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_){
_start:
{
uint8_t v___x_4260_; 
v___x_4260_ = lean_usize_dec_lt(v_i_4255_, v_sz_4254_);
if (v___x_4260_ == 0)
{
lean_object* v___x_4261_; 
lean_dec_ref(v___x_4251_);
lean_dec(v_stx_4248_);
v___x_4261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4261_, 0, v_b_4256_);
return v___x_4261_;
}
else
{
lean_object* v_snd_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4296_; 
v_snd_4262_ = lean_ctor_get(v_b_4256_, 1);
v_isSharedCheck_4296_ = !lean_is_exclusive(v_b_4256_);
if (v_isSharedCheck_4296_ == 0)
{
lean_object* v_unused_4297_; 
v_unused_4297_ = lean_ctor_get(v_b_4256_, 0);
lean_dec(v_unused_4297_);
v___x_4264_ = v_b_4256_;
v_isShared_4265_ = v_isSharedCheck_4296_;
goto v_resetjp_4263_;
}
else
{
lean_inc(v_snd_4262_);
lean_dec(v_b_4256_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4296_;
goto v_resetjp_4263_;
}
v_resetjp_4263_:
{
lean_object* v_a_4266_; lean_object* v___x_4267_; 
v_a_4266_ = lean_array_uget_borrowed(v_as_4253_, v_i_4255_);
lean_inc(v_snd_4262_);
lean_inc_ref(v___x_4251_);
lean_inc(v_stx_4248_);
v___x_4267_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4247_, v_stx_4248_, v___x_4249_, v___x_4250_, v___x_4251_, v___x_4252_, v_a_4266_, v_snd_4262_, v___y_4257_, v___y_4258_);
if (lean_obj_tag(v___x_4267_) == 0)
{
lean_object* v_a_4268_; lean_object* v___x_4270_; uint8_t v_isShared_4271_; uint8_t v_isSharedCheck_4287_; 
v_a_4268_ = lean_ctor_get(v___x_4267_, 0);
v_isSharedCheck_4287_ = !lean_is_exclusive(v___x_4267_);
if (v_isSharedCheck_4287_ == 0)
{
v___x_4270_ = v___x_4267_;
v_isShared_4271_ = v_isSharedCheck_4287_;
goto v_resetjp_4269_;
}
else
{
lean_inc(v_a_4268_);
lean_dec(v___x_4267_);
v___x_4270_ = lean_box(0);
v_isShared_4271_ = v_isSharedCheck_4287_;
goto v_resetjp_4269_;
}
v_resetjp_4269_:
{
if (lean_obj_tag(v_a_4268_) == 0)
{
lean_object* v___x_4272_; lean_object* v___x_4274_; 
lean_dec_ref(v___x_4251_);
lean_dec(v_stx_4248_);
v___x_4272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4272_, 0, v_a_4268_);
if (v_isShared_4265_ == 0)
{
lean_ctor_set(v___x_4264_, 0, v___x_4272_);
v___x_4274_ = v___x_4264_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v___x_4272_);
lean_ctor_set(v_reuseFailAlloc_4278_, 1, v_snd_4262_);
v___x_4274_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
lean_object* v___x_4276_; 
if (v_isShared_4271_ == 0)
{
lean_ctor_set(v___x_4270_, 0, v___x_4274_);
v___x_4276_ = v___x_4270_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v___x_4274_);
v___x_4276_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
return v___x_4276_;
}
}
}
else
{
lean_object* v_a_4279_; lean_object* v___x_4280_; lean_object* v___x_4282_; 
lean_del_object(v___x_4270_);
lean_dec(v_snd_4262_);
v_a_4279_ = lean_ctor_get(v_a_4268_, 0);
lean_inc(v_a_4279_);
lean_dec_ref_known(v_a_4268_, 1);
v___x_4280_ = lean_box(0);
if (v_isShared_4265_ == 0)
{
lean_ctor_set(v___x_4264_, 1, v_a_4279_);
lean_ctor_set(v___x_4264_, 0, v___x_4280_);
v___x_4282_ = v___x_4264_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4286_; 
v_reuseFailAlloc_4286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4286_, 0, v___x_4280_);
lean_ctor_set(v_reuseFailAlloc_4286_, 1, v_a_4279_);
v___x_4282_ = v_reuseFailAlloc_4286_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
size_t v___x_4283_; size_t v___x_4284_; 
v___x_4283_ = ((size_t)1ULL);
v___x_4284_ = lean_usize_add(v_i_4255_, v___x_4283_);
v_i_4255_ = v___x_4284_;
v_b_4256_ = v___x_4282_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4295_; 
lean_del_object(v___x_4264_);
lean_dec(v_snd_4262_);
lean_dec_ref(v___x_4251_);
lean_dec(v_stx_4248_);
v_a_4288_ = lean_ctor_get(v___x_4267_, 0);
v_isSharedCheck_4295_ = !lean_is_exclusive(v___x_4267_);
if (v_isSharedCheck_4295_ == 0)
{
v___x_4290_ = v___x_4267_;
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_a_4288_);
lean_dec(v___x_4267_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
lean_object* v___x_4293_; 
if (v_isShared_4291_ == 0)
{
v___x_4293_ = v___x_4290_;
goto v_reusejp_4292_;
}
else
{
lean_object* v_reuseFailAlloc_4294_; 
v_reuseFailAlloc_4294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4294_, 0, v_a_4288_);
v___x_4293_ = v_reuseFailAlloc_4294_;
goto v_reusejp_4292_;
}
v_reusejp_4292_:
{
return v___x_4293_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3___boxed(lean_object* v_init_4298_, lean_object* v_stx_4299_, lean_object* v___x_4300_, lean_object* v___x_4301_, lean_object* v___x_4302_, lean_object* v___x_4303_, lean_object* v_as_4304_, lean_object* v_sz_4305_, lean_object* v_i_4306_, lean_object* v_b_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_){
_start:
{
size_t v_sz_boxed_4311_; size_t v_i_boxed_4312_; lean_object* v_res_4313_; 
v_sz_boxed_4311_ = lean_unbox_usize(v_sz_4305_);
lean_dec(v_sz_4305_);
v_i_boxed_4312_ = lean_unbox_usize(v_i_4306_);
lean_dec(v_i_4306_);
v_res_4313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(v_init_4298_, v_stx_4299_, v___x_4300_, v___x_4301_, v___x_4302_, v___x_4303_, v_as_4304_, v_sz_boxed_4311_, v_i_boxed_4312_, v_b_4307_, v___y_4308_, v___y_4309_);
lean_dec(v___y_4309_);
lean_dec_ref(v___y_4308_);
lean_dec_ref(v_as_4304_);
lean_dec(v___x_4303_);
lean_dec_ref(v___x_4301_);
lean_dec_ref(v___x_4300_);
return v_res_4313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2___boxed(lean_object* v_init_4314_, lean_object* v_stx_4315_, lean_object* v___x_4316_, lean_object* v___x_4317_, lean_object* v___x_4318_, lean_object* v___x_4319_, lean_object* v_n_4320_, lean_object* v_b_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_){
_start:
{
lean_object* v_res_4325_; 
v_res_4325_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4314_, v_stx_4315_, v___x_4316_, v___x_4317_, v___x_4318_, v___x_4319_, v_n_4320_, v_b_4321_, v___y_4322_, v___y_4323_);
lean_dec(v___y_4323_);
lean_dec_ref(v___y_4322_);
lean_dec_ref(v_n_4320_);
lean_dec(v___x_4319_);
lean_dec_ref(v___x_4317_);
lean_dec_ref(v___x_4316_);
return v_res_4325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(lean_object* v___x_4326_, lean_object* v___x_4327_, lean_object* v_stx_4328_, lean_object* v___x_4329_, lean_object* v___x_4330_, lean_object* v_t_4331_, lean_object* v_init_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_){
_start:
{
lean_object* v_root_4336_; lean_object* v_tail_4337_; lean_object* v___x_4338_; 
v_root_4336_ = lean_ctor_get(v_t_4331_, 0);
v_tail_4337_ = lean_ctor_get(v_t_4331_, 1);
lean_inc_ref(v___x_4326_);
lean_inc(v_stx_4328_);
v___x_4338_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4332_, v_stx_4328_, v___x_4329_, v___x_4330_, v___x_4326_, v___x_4327_, v_root_4336_, v_init_4332_, v___y_4333_, v___y_4334_);
if (lean_obj_tag(v___x_4338_) == 0)
{
lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4375_; 
v_a_4339_ = lean_ctor_get(v___x_4338_, 0);
v_isSharedCheck_4375_ = !lean_is_exclusive(v___x_4338_);
if (v_isSharedCheck_4375_ == 0)
{
v___x_4341_ = v___x_4338_;
v_isShared_4342_ = v_isSharedCheck_4375_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v___x_4338_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4375_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
if (lean_obj_tag(v_a_4339_) == 0)
{
lean_object* v_a_4343_; lean_object* v___x_4345_; 
lean_dec(v_stx_4328_);
lean_dec_ref(v___x_4326_);
v_a_4343_ = lean_ctor_get(v_a_4339_, 0);
lean_inc(v_a_4343_);
lean_dec_ref_known(v_a_4339_, 1);
if (v_isShared_4342_ == 0)
{
lean_ctor_set(v___x_4341_, 0, v_a_4343_);
v___x_4345_ = v___x_4341_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_a_4343_);
v___x_4345_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
return v___x_4345_;
}
}
else
{
lean_object* v_a_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; size_t v_sz_4350_; size_t v___x_4351_; lean_object* v___x_4352_; 
lean_del_object(v___x_4341_);
v_a_4347_ = lean_ctor_get(v_a_4339_, 0);
lean_inc(v_a_4347_);
lean_dec_ref_known(v_a_4339_, 1);
v___x_4348_ = lean_box(0);
v___x_4349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4349_, 0, v___x_4348_);
lean_ctor_set(v___x_4349_, 1, v_a_4347_);
v_sz_4350_ = lean_array_size(v_tail_4337_);
v___x_4351_ = ((size_t)0ULL);
v___x_4352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(v_stx_4328_, v___x_4329_, v___x_4330_, v___x_4326_, v___x_4327_, v_tail_4337_, v_sz_4350_, v___x_4351_, v___x_4349_, v___y_4333_, v___y_4334_);
if (lean_obj_tag(v___x_4352_) == 0)
{
lean_object* v_a_4353_; lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4366_; 
v_a_4353_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4366_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4366_ == 0)
{
v___x_4355_ = v___x_4352_;
v_isShared_4356_ = v_isSharedCheck_4366_;
goto v_resetjp_4354_;
}
else
{
lean_inc(v_a_4353_);
lean_dec(v___x_4352_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4366_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v_fst_4357_; 
v_fst_4357_ = lean_ctor_get(v_a_4353_, 0);
if (lean_obj_tag(v_fst_4357_) == 0)
{
lean_object* v_snd_4358_; lean_object* v___x_4360_; 
v_snd_4358_ = lean_ctor_get(v_a_4353_, 1);
lean_inc(v_snd_4358_);
lean_dec(v_a_4353_);
if (v_isShared_4356_ == 0)
{
lean_ctor_set(v___x_4355_, 0, v_snd_4358_);
v___x_4360_ = v___x_4355_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_snd_4358_);
v___x_4360_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
return v___x_4360_;
}
}
else
{
lean_object* v_val_4362_; lean_object* v___x_4364_; 
lean_inc_ref(v_fst_4357_);
lean_dec(v_a_4353_);
v_val_4362_ = lean_ctor_get(v_fst_4357_, 0);
lean_inc(v_val_4362_);
lean_dec_ref_known(v_fst_4357_, 1);
if (v_isShared_4356_ == 0)
{
lean_ctor_set(v___x_4355_, 0, v_val_4362_);
v___x_4364_ = v___x_4355_;
goto v_reusejp_4363_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_val_4362_);
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
else
{
lean_object* v_a_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4374_; 
v_a_4367_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4374_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4374_ == 0)
{
v___x_4369_ = v___x_4352_;
v_isShared_4370_ = v_isSharedCheck_4374_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_a_4367_);
lean_dec(v___x_4352_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4374_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v___x_4372_; 
if (v_isShared_4370_ == 0)
{
v___x_4372_ = v___x_4369_;
goto v_reusejp_4371_;
}
else
{
lean_object* v_reuseFailAlloc_4373_; 
v_reuseFailAlloc_4373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4373_, 0, v_a_4367_);
v___x_4372_ = v_reuseFailAlloc_4373_;
goto v_reusejp_4371_;
}
v_reusejp_4371_:
{
return v___x_4372_;
}
}
}
}
}
}
else
{
lean_object* v_a_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4383_; 
lean_dec(v_stx_4328_);
lean_dec_ref(v___x_4326_);
v_a_4376_ = lean_ctor_get(v___x_4338_, 0);
v_isSharedCheck_4383_ = !lean_is_exclusive(v___x_4338_);
if (v_isSharedCheck_4383_ == 0)
{
v___x_4378_ = v___x_4338_;
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_a_4376_);
lean_dec(v___x_4338_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4381_; 
if (v_isShared_4379_ == 0)
{
v___x_4381_ = v___x_4378_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_a_4376_);
v___x_4381_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
return v___x_4381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2___boxed(lean_object* v___x_4384_, lean_object* v___x_4385_, lean_object* v_stx_4386_, lean_object* v___x_4387_, lean_object* v___x_4388_, lean_object* v_t_4389_, lean_object* v_init_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_){
_start:
{
lean_object* v_res_4394_; 
v_res_4394_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___x_4384_, v___x_4385_, v_stx_4386_, v___x_4387_, v___x_4388_, v_t_4389_, v_init_4390_, v___y_4391_, v___y_4392_);
lean_dec(v___y_4392_);
lean_dec_ref(v___y_4391_);
lean_dec_ref(v_t_4389_);
lean_dec_ref(v___x_4388_);
lean_dec_ref(v___x_4387_);
lean_dec(v___x_4385_);
return v_res_4394_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; 
v___x_4396_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__0));
v___x_4397_ = l_Lean_stringToMessageData(v___x_4396_);
return v___x_4397_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4401_; lean_object* v___x_4402_; 
v___x_4401_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__4));
v___x_4402_ = l_Lean_stringToMessageData(v___x_4401_);
return v___x_4402_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; 
v___x_4404_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__6));
v___x_4405_ = l_Lean_stringToMessageData(v___x_4404_);
return v___x_4405_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9(void){
_start:
{
lean_object* v___x_4407_; lean_object* v___x_4408_; 
v___x_4407_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__8));
v___x_4408_ = l_Lean_stringToMessageData(v___x_4407_);
return v___x_4408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(lean_object* v_stx_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_){
_start:
{
lean_object* v___x_4416_; lean_object* v_scopes_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v_opts_4420_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___y_4425_; uint8_t v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4446_; lean_object* v___y_4452_; uint8_t v___y_4453_; lean_object* v___y_4454_; lean_object* v___y_4455_; lean_object* v___y_4461_; lean_object* v___y_4462_; uint8_t v___y_4463_; uint8_t v___y_4464_; lean_object* v___y_4465_; uint8_t v___y_4474_; lean_object* v___y_4475_; uint8_t v___y_4476_; uint8_t v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; uint8_t v___y_4488_; uint8_t v___y_4489_; uint8_t v___y_4490_; uint8_t v___y_4524_; lean_object* v___x_4531_; uint8_t v___x_4532_; 
v___x_4416_ = lean_st_ref_get(v___y_4411_);
v_scopes_4417_ = lean_ctor_get(v___x_4416_, 2);
lean_inc(v_scopes_4417_);
lean_dec(v___x_4416_);
v___x_4418_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4419_ = l_List_head_x21___redArg(v___x_4418_, v_scopes_4417_);
lean_dec(v_scopes_4417_);
v_opts_4420_ = lean_ctor_get(v___x_4419_, 1);
lean_inc_ref(v_opts_4420_);
lean_dec(v___x_4419_);
v___x_4531_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_4532_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4420_, v___x_4531_);
if (v___x_4532_ == 0)
{
lean_object* v___x_4533_; uint8_t v___x_4534_; 
v___x_4533_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_4534_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4420_, v___x_4533_);
v___y_4524_ = v___x_4534_;
goto v___jp_4523_;
}
else
{
v___y_4524_ = v___x_4532_;
goto v___jp_4523_;
}
v___jp_4413_:
{
lean_object* v___x_4414_; lean_object* v___x_4415_; 
v___x_4414_ = lean_box(0);
v___x_4415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4415_, 0, v___x_4414_);
return v___x_4415_;
}
v___jp_4421_:
{
lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v_a_4428_; lean_object* v___x_4429_; lean_object* v_line_4430_; lean_object* v_messages_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; 
v___x_4426_ = lean_st_ref_get(v___y_4422_);
v___x_4427_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_4422_);
v_a_4428_ = lean_ctor_get(v___x_4427_, 0);
lean_inc(v_a_4428_);
lean_dec_ref(v___x_4427_);
lean_inc_ref_n(v___y_4423_, 2);
v___x_4429_ = l_Lean_FileMap_toPosition(v___y_4423_, v___y_4425_);
lean_dec(v___y_4425_);
v_line_4430_ = lean_ctor_get(v___x_4429_, 0);
lean_inc(v_line_4430_);
lean_dec_ref(v___x_4429_);
v_messages_4431_ = lean_ctor_get(v___x_4426_, 1);
lean_inc_ref(v_messages_4431_);
lean_dec(v___x_4426_);
v___x_4432_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_4431_);
v___x_4433_ = lean_box(0);
v___x_4434_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___y_4423_, v_line_4430_, v_stx_4409_, v_opts_4420_, v___x_4432_, v_a_4428_, v___x_4433_, v___y_4424_, v___y_4422_);
lean_dec(v_a_4428_);
lean_dec_ref(v___x_4432_);
lean_dec_ref(v_opts_4420_);
lean_dec(v_line_4430_);
if (lean_obj_tag(v___x_4434_) == 0)
{
lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4441_; 
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_4434_);
if (v_isSharedCheck_4441_ == 0)
{
lean_object* v_unused_4442_; 
v_unused_4442_ = lean_ctor_get(v___x_4434_, 0);
lean_dec(v_unused_4442_);
v___x_4436_ = v___x_4434_;
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
else
{
lean_dec(v___x_4434_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v___x_4439_; 
if (v_isShared_4437_ == 0)
{
lean_ctor_set(v___x_4436_, 0, v___x_4433_);
v___x_4439_ = v___x_4436_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v___x_4433_);
v___x_4439_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
return v___x_4439_;
}
}
}
else
{
return v___x_4434_;
}
}
v___jp_4443_:
{
lean_object* v_fileMap_4447_; lean_object* v___x_4448_; 
v_fileMap_4447_ = lean_ctor_get(v___y_4445_, 1);
v___x_4448_ = l_Lean_Syntax_getPos_x3f(v_stx_4409_, v___y_4444_);
if (lean_obj_tag(v___x_4448_) == 0)
{
lean_object* v___x_4449_; 
v___x_4449_ = lean_unsigned_to_nat(0u);
v___y_4422_ = v___y_4446_;
v___y_4423_ = v_fileMap_4447_;
v___y_4424_ = v___y_4445_;
v___y_4425_ = v___x_4449_;
goto v___jp_4421_;
}
else
{
lean_object* v_val_4450_; 
v_val_4450_ = lean_ctor_get(v___x_4448_, 0);
lean_inc(v_val_4450_);
lean_dec_ref_known(v___x_4448_, 1);
v___y_4422_ = v___y_4446_;
v___y_4423_ = v_fileMap_4447_;
v___y_4424_ = v___y_4445_;
v___y_4425_ = v_val_4450_;
goto v___jp_4421_;
}
}
v___jp_4451_:
{
lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; 
lean_inc_ref(v___y_4455_);
v___x_4456_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4456_, 0, v___y_4455_);
v___x_4457_ = l_Lean_MessageData_ofFormat(v___x_4456_);
v___x_4458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4458_, 0, v___y_4454_);
lean_ctor_set(v___x_4458_, 1, v___x_4457_);
lean_inc(v___y_4452_);
v___x_4459_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___y_4452_, v___x_4458_, v___y_4410_, v___y_4411_);
if (lean_obj_tag(v___x_4459_) == 0)
{
lean_dec_ref_known(v___x_4459_, 1);
v___y_4444_ = v___y_4453_;
v___y_4445_ = v___y_4410_;
v___y_4446_ = v___y_4411_;
goto v___jp_4443_;
}
else
{
lean_dec_ref(v_opts_4420_);
lean_dec(v_stx_4409_);
return v___x_4459_;
}
}
v___jp_4460_:
{
lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; 
lean_inc_ref(v___y_4465_);
v___x_4466_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4466_, 0, v___y_4465_);
v___x_4467_ = l_Lean_MessageData_ofFormat(v___x_4466_);
v___x_4468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4468_, 0, v___y_4461_);
lean_ctor_set(v___x_4468_, 1, v___x_4467_);
v___x_4469_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1);
v___x_4470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4470_, 0, v___x_4468_);
lean_ctor_set(v___x_4470_, 1, v___x_4469_);
if (v___y_4464_ == 0)
{
lean_object* v___x_4471_; 
v___x_4471_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4452_ = v___y_4462_;
v___y_4453_ = v___y_4463_;
v___y_4454_ = v___x_4470_;
v___y_4455_ = v___x_4471_;
goto v___jp_4451_;
}
else
{
lean_object* v___x_4472_; 
v___x_4472_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4452_ = v___y_4462_;
v___y_4453_ = v___y_4463_;
v___y_4454_ = v___x_4470_;
v___y_4455_ = v___x_4472_;
goto v___jp_4451_;
}
}
v___jp_4473_:
{
lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; 
lean_inc_ref(v___y_4479_);
v___x_4480_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4480_, 0, v___y_4479_);
v___x_4481_ = l_Lean_MessageData_ofFormat(v___x_4480_);
lean_inc_ref(v___y_4478_);
v___x_4482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4482_, 0, v___y_4478_);
lean_ctor_set(v___x_4482_, 1, v___x_4481_);
v___x_4483_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5);
v___x_4484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4484_, 0, v___x_4482_);
lean_ctor_set(v___x_4484_, 1, v___x_4483_);
if (v___y_4474_ == 0)
{
lean_object* v___x_4485_; 
v___x_4485_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4461_ = v___x_4484_;
v___y_4462_ = v___y_4475_;
v___y_4463_ = v___y_4476_;
v___y_4464_ = v___y_4477_;
v___y_4465_ = v___x_4485_;
goto v___jp_4460_;
}
else
{
lean_object* v___x_4486_; 
v___x_4486_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4461_ = v___x_4484_;
v___y_4462_ = v___y_4475_;
v___y_4463_ = v___y_4476_;
v___y_4464_ = v___y_4477_;
v___y_4465_ = v___x_4486_;
goto v___jp_4460_;
}
}
v___jp_4487_:
{
lean_object* v___x_4491_; lean_object* v_a_4492_; uint8_t v___x_4493_; 
v___x_4491_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(v_stx_4409_, v___y_4410_, v___y_4411_);
v_a_4492_ = lean_ctor_get(v___x_4491_, 0);
lean_inc(v_a_4492_);
lean_dec_ref(v___x_4491_);
v___x_4493_ = lean_unbox(v_a_4492_);
if (v___x_4493_ == 0)
{
lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v_scopes_4497_; lean_object* v___x_4498_; lean_object* v_opts_4499_; uint8_t v_hasTrace_4500_; 
v___x_4494_ = l_Lean_inheritedTraceOptions;
v___x_4495_ = lean_st_ref_get(v___x_4494_);
v___x_4496_ = lean_st_ref_get(v___y_4411_);
v_scopes_4497_ = lean_ctor_get(v___x_4496_, 2);
lean_inc(v_scopes_4497_);
lean_dec(v___x_4496_);
v___x_4498_ = l_List_head_x21___redArg(v___x_4418_, v_scopes_4497_);
lean_dec(v_scopes_4497_);
v_opts_4499_ = lean_ctor_get(v___x_4498_, 1);
lean_inc_ref(v_opts_4499_);
lean_dec(v___x_4498_);
v_hasTrace_4500_ = lean_ctor_get_uint8(v_opts_4499_, sizeof(void*)*1);
if (v_hasTrace_4500_ == 0)
{
uint8_t v___x_4501_; 
lean_dec_ref(v_opts_4499_);
lean_dec(v___x_4495_);
v___x_4501_ = lean_unbox(v_a_4492_);
lean_dec(v_a_4492_);
v___y_4444_ = v___x_4501_;
v___y_4445_ = v___y_4410_;
v___y_4446_ = v___y_4411_;
goto v___jp_4443_;
}
else
{
lean_object* v___x_4502_; lean_object* v___x_4503_; uint8_t v___x_4504_; 
v___x_4502_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4503_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_4504_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4495_, v_opts_4499_, v___x_4503_);
lean_dec_ref(v_opts_4499_);
lean_dec(v___x_4495_);
if (v___x_4504_ == 0)
{
uint8_t v___x_4505_; 
v___x_4505_ = lean_unbox(v_a_4492_);
lean_dec(v_a_4492_);
v___y_4444_ = v___x_4505_;
v___y_4445_ = v___y_4410_;
v___y_4446_ = v___y_4411_;
goto v___jp_4443_;
}
else
{
lean_object* v___x_4506_; 
v___x_4506_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7);
if (v___y_4489_ == 0)
{
lean_object* v___x_4507_; uint8_t v___x_4508_; 
v___x_4507_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___x_4508_ = lean_unbox(v_a_4492_);
lean_dec(v_a_4492_);
v___y_4474_ = v___y_4488_;
v___y_4475_ = v___x_4502_;
v___y_4476_ = v___x_4508_;
v___y_4477_ = v___y_4490_;
v___y_4478_ = v___x_4506_;
v___y_4479_ = v___x_4507_;
goto v___jp_4473_;
}
else
{
lean_object* v___x_4509_; uint8_t v___x_4510_; 
v___x_4509_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___x_4510_ = lean_unbox(v_a_4492_);
lean_dec(v_a_4492_);
v___y_4474_ = v___y_4488_;
v___y_4475_ = v___x_4502_;
v___y_4476_ = v___x_4510_;
v___y_4477_ = v___y_4490_;
v___y_4478_ = v___x_4506_;
v___y_4479_ = v___x_4509_;
goto v___jp_4473_;
}
}
}
}
else
{
lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v_scopes_4514_; lean_object* v___x_4515_; lean_object* v_opts_4516_; uint8_t v_hasTrace_4517_; 
lean_dec(v_a_4492_);
lean_dec_ref(v_opts_4420_);
lean_dec(v_stx_4409_);
v___x_4511_ = l_Lean_inheritedTraceOptions;
v___x_4512_ = lean_st_ref_get(v___x_4511_);
v___x_4513_ = lean_st_ref_get(v___y_4411_);
v_scopes_4514_ = lean_ctor_get(v___x_4513_, 2);
lean_inc(v_scopes_4514_);
lean_dec(v___x_4513_);
v___x_4515_ = l_List_head_x21___redArg(v___x_4418_, v_scopes_4514_);
lean_dec(v_scopes_4514_);
v_opts_4516_ = lean_ctor_get(v___x_4515_, 1);
lean_inc_ref(v_opts_4516_);
lean_dec(v___x_4515_);
v_hasTrace_4517_ = lean_ctor_get_uint8(v_opts_4516_, sizeof(void*)*1);
if (v_hasTrace_4517_ == 0)
{
lean_dec_ref(v_opts_4516_);
lean_dec(v___x_4512_);
goto v___jp_4413_;
}
else
{
lean_object* v___x_4518_; lean_object* v___x_4519_; uint8_t v___x_4520_; 
v___x_4518_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4519_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_4520_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4512_, v_opts_4516_, v___x_4519_);
lean_dec_ref(v_opts_4516_);
lean_dec(v___x_4512_);
if (v___x_4520_ == 0)
{
goto v___jp_4413_;
}
else
{
lean_object* v___x_4521_; lean_object* v___x_4522_; 
v___x_4521_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9);
v___x_4522_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_4518_, v___x_4521_, v___y_4410_, v___y_4411_);
if (lean_obj_tag(v___x_4522_) == 0)
{
lean_dec_ref_known(v___x_4522_, 1);
goto v___jp_4413_;
}
else
{
return v___x_4522_;
}
}
}
}
}
v___jp_4523_:
{
lean_object* v___x_4525_; uint8_t v___x_4526_; lean_object* v___x_4527_; uint8_t v___x_4528_; 
v___x_4525_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
v___x_4526_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4420_, v___x_4525_);
v___x_4527_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v___x_4528_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4420_, v___x_4527_);
if (v___y_4524_ == 0)
{
if (v___x_4526_ == 0)
{
if (v___x_4528_ == 0)
{
lean_object* v___x_4529_; lean_object* v___x_4530_; 
lean_dec_ref(v_opts_4420_);
lean_dec(v_stx_4409_);
v___x_4529_ = lean_box(0);
v___x_4530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4530_, 0, v___x_4529_);
return v___x_4530_;
}
else
{
v___y_4488_ = v___x_4526_;
v___y_4489_ = v___y_4524_;
v___y_4490_ = v___x_4528_;
goto v___jp_4487_;
}
}
else
{
v___y_4488_ = v___x_4526_;
v___y_4489_ = v___y_4524_;
v___y_4490_ = v___x_4528_;
goto v___jp_4487_;
}
}
else
{
v___y_4488_ = v___x_4526_;
v___y_4489_ = v___y_4524_;
v___y_4490_ = v___x_4528_;
goto v___jp_4487_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___boxed(lean_object* v_stx_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
lean_object* v_res_4539_; 
v_res_4539_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(v_stx_4535_, v___y_4536_, v___y_4537_);
lean_dec(v___y_4537_);
lean_dec_ref(v___y_4536_);
return v_res_4539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4552_; lean_object* v___x_4553_; 
v___x_4552_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook));
v___x_4553_ = l_Lean_Elab_Command_addLinter(v___x_4552_);
return v___x_4553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2____boxed(lean_object* v_a_4554_){
_start:
{
lean_object* v_res_4555_; 
v_res_4555_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_();
return v_res_4555_;
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
