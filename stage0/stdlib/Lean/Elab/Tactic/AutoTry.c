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
lean_object* v___x_337_; uint8_t v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v_fileName_364_; lean_object* v_fileMap_365_; lean_object* v_ref_366_; lean_object* v_cancelTk_x3f_367_; lean_object* v_a_369_; lean_object* v_a_376_; lean_object* v_currNamespace_378_; lean_object* v_openDecls_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v_env_385_; lean_object* v___x_386_; uint8_t v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; uint8_t v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; uint8_t v___y_484_; lean_object* v___x_504_; uint8_t v___x_505_; lean_object* v___y_507_; lean_object* v___y_508_; uint8_t v___y_538_; uint8_t v___x_558_; 
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
v___x_504_ = l_Lean_diagnostics;
v___x_505_ = lean_uint8_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23);
v___x_558_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_385_);
lean_dec_ref(v_env_385_);
if (v___x_505_ == 0)
{
if (v___x_558_ == 0)
{
lean_inc(v___x_360_);
v___y_507_ = v___x_384_;
v___y_508_ = v___x_360_;
goto v___jp_506_;
}
else
{
v___y_538_ = v___x_505_;
goto v___jp_537_;
}
}
else
{
v___y_538_ = v___x_558_;
goto v___jp_537_;
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
lean_object* v___x_392_; lean_object* v_fileName_393_; lean_object* v_fileMap_394_; lean_object* v_currRecDepth_395_; lean_object* v_ref_396_; lean_object* v_currNamespace_397_; lean_object* v_openDecls_398_; lean_object* v_initHeartbeats_399_; lean_object* v_maxHeartbeats_400_; lean_object* v_quotContext_401_; lean_object* v_currMacroScope_402_; lean_object* v_cancelTk_x3f_403_; uint8_t v_suppressElabErrors_404_; lean_object* v_inheritedTraceOptions_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_476_; 
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
v_isSharedCheck_476_ = !lean_is_exclusive(v___y_390_);
if (v_isSharedCheck_476_ == 0)
{
lean_object* v_unused_477_; lean_object* v_unused_478_; 
v_unused_477_ = lean_ctor_get(v___y_390_, 4);
lean_dec(v_unused_477_);
v_unused_478_ = lean_ctor_get(v___y_390_, 2);
lean_dec(v_unused_478_);
v___x_407_ = v___y_390_;
v_isShared_408_ = v_isSharedCheck_476_;
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
v_isShared_408_ = v_isSharedCheck_476_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v___x_411_; 
v___x_409_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__1(v_opts_331_, v___y_389_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 4, v___x_409_);
lean_ctor_set(v___x_407_, 2, v_opts_331_);
v___x_411_ = v___x_407_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_fileName_393_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_fileMap_394_);
lean_ctor_set(v_reuseFailAlloc_475_, 2, v_opts_331_);
lean_ctor_set(v_reuseFailAlloc_475_, 3, v_currRecDepth_395_);
lean_ctor_set(v_reuseFailAlloc_475_, 4, v___x_409_);
lean_ctor_set(v_reuseFailAlloc_475_, 5, v_ref_396_);
lean_ctor_set(v_reuseFailAlloc_475_, 6, v_currNamespace_397_);
lean_ctor_set(v_reuseFailAlloc_475_, 7, v_openDecls_398_);
lean_ctor_set(v_reuseFailAlloc_475_, 8, v_initHeartbeats_399_);
lean_ctor_set(v_reuseFailAlloc_475_, 9, v_maxHeartbeats_400_);
lean_ctor_set(v_reuseFailAlloc_475_, 10, v_quotContext_401_);
lean_ctor_set(v_reuseFailAlloc_475_, 11, v_currMacroScope_402_);
lean_ctor_set(v_reuseFailAlloc_475_, 12, v_cancelTk_x3f_403_);
lean_ctor_set(v_reuseFailAlloc_475_, 13, v_inheritedTraceOptions_405_);
lean_ctor_set_uint8(v_reuseFailAlloc_475_, sizeof(void*)*14 + 1, v_suppressElabErrors_404_);
v___x_411_ = v_reuseFailAlloc_475_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
lean_object* v___x_412_; 
lean_ctor_set_uint8(v___x_411_, sizeof(void*)*14, v___y_388_);
lean_inc(v___x_392_);
v___x_412_ = lean_apply_5(v_x_333_, v___x_345_, v___x_392_, v___x_411_, v___y_391_, lean_box(0));
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_459_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_459_ == 0)
{
v___x_415_ = v___x_412_;
v_isShared_416_ = v_isSharedCheck_459_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_412_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_459_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v_traceState_420_; lean_object* v_traceState_421_; lean_object* v_env_422_; lean_object* v_messages_423_; lean_object* v_scopes_424_; lean_object* v_usedQuotCtxts_425_; lean_object* v_nextMacroScope_426_; lean_object* v_maxRecDepth_427_; lean_object* v_ngen_428_; lean_object* v_auxDeclNGen_429_; lean_object* v_infoState_430_; lean_object* v_snapshotTasks_431_; lean_object* v_prevLinterStates_432_; lean_object* v_codeQualityEntryTasks_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_457_; 
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
v_codeQualityEntryTasks_433_ = lean_ctor_get(v___x_419_, 12);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_457_ == 0)
{
lean_object* v_unused_458_; 
v_unused_458_ = lean_ctor_get(v___x_419_, 9);
lean_dec(v_unused_458_);
v___x_435_ = v___x_419_;
v_isShared_436_ = v_isSharedCheck_457_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_codeQualityEntryTasks_433_);
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
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_457_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v_messages_437_; uint64_t v_tid_438_; lean_object* v_traces_439_; lean_object* v_traces_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_456_; 
v_messages_437_ = lean_ctor_get(v___x_418_, 6);
lean_inc_ref(v_messages_437_);
lean_dec(v___x_418_);
v_tid_438_ = lean_ctor_get_uint64(v_traceState_420_, sizeof(void*)*1);
v_traces_439_ = lean_ctor_get(v_traceState_420_, 0);
lean_inc_ref(v_traces_439_);
lean_dec_ref(v_traceState_420_);
v_traces_440_ = lean_ctor_get(v_traceState_421_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v_traceState_421_);
if (v_isSharedCheck_456_ == 0)
{
v___x_442_ = v_traceState_421_;
v_isShared_443_ = v_isSharedCheck_456_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_traces_440_);
lean_dec(v_traceState_421_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_456_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_444_ = l_Lean_MessageLog_append(v_messages_423_, v_messages_437_);
v___x_445_ = l_Lean_PersistentArray_append___redArg(v_traces_439_, v_traces_440_);
lean_dec_ref(v_traces_440_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v___x_445_);
v___x_447_ = v___x_442_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_445_);
v___x_447_ = v_reuseFailAlloc_455_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_449_; 
lean_ctor_set_uint64(v___x_447_, sizeof(void*)*1, v_tid_438_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 9, v___x_447_);
lean_ctor_set(v___x_435_, 1, v___x_444_);
v___x_449_ = v___x_435_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_env_422_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v_scopes_424_);
lean_ctor_set(v_reuseFailAlloc_454_, 3, v_usedQuotCtxts_425_);
lean_ctor_set(v_reuseFailAlloc_454_, 4, v_nextMacroScope_426_);
lean_ctor_set(v_reuseFailAlloc_454_, 5, v_maxRecDepth_427_);
lean_ctor_set(v_reuseFailAlloc_454_, 6, v_ngen_428_);
lean_ctor_set(v_reuseFailAlloc_454_, 7, v_auxDeclNGen_429_);
lean_ctor_set(v_reuseFailAlloc_454_, 8, v_infoState_430_);
lean_ctor_set(v_reuseFailAlloc_454_, 9, v___x_447_);
lean_ctor_set(v_reuseFailAlloc_454_, 10, v_snapshotTasks_431_);
lean_ctor_set(v_reuseFailAlloc_454_, 11, v_prevLinterStates_432_);
lean_ctor_set(v_reuseFailAlloc_454_, 12, v_codeQualityEntryTasks_433_);
v___x_449_ = v_reuseFailAlloc_454_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_450_ = lean_st_ref_put(v_a_335_, v___x_449_);
if (v_isShared_416_ == 0)
{
v___x_452_ = v___x_415_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_413_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_460_; 
lean_dec(v___x_392_);
lean_dec(v___x_360_);
v_a_460_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_460_);
lean_dec_ref_known(v___x_412_, 1);
if (lean_obj_tag(v_a_460_) == 0)
{
lean_object* v_msg_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v_msg_461_ = lean_ctor_get(v_a_460_, 1);
lean_inc_ref(v_msg_461_);
lean_dec_ref_known(v_a_460_, 2);
v___x_462_ = l_Lean_MessageData_toString(v_msg_461_);
v___x_463_ = lean_mk_io_user_error(v___x_462_);
v_a_369_ = v___x_463_;
goto v___jp_368_;
}
else
{
lean_object* v_id_464_; lean_object* v___x_465_; 
v_id_464_ = lean_ctor_get(v_a_460_, 0);
lean_inc(v_id_464_);
lean_dec_ref_known(v_a_460_, 2);
v___x_465_ = l_Lean_InternalExceptionId_getName(v_id_464_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec(v_id_464_);
v_a_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_a_466_);
lean_dec_ref_known(v___x_465_, 1);
v___x_467_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20));
v___x_468_ = l_Lean_Name_toString(v_a_466_, v___x_340_);
v___x_469_ = lean_string_append(v___x_467_, v___x_468_);
lean_dec_ref(v___x_468_);
v_a_376_ = v___x_469_;
goto v___jp_375_;
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
lean_dec_ref_known(v___x_465_, 1);
v___x_470_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21));
v___x_471_ = l_Nat_reprFast(v_id_464_);
v___x_472_ = lean_string_append(v___x_470_, v___x_471_);
lean_dec_ref(v___x_471_);
v___x_473_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__22));
v___x_474_ = lean_string_append(v___x_472_, v___x_473_);
v_a_376_ = v___x_474_;
goto v___jp_375_;
}
}
}
}
}
}
v___jp_479_:
{
if (v___y_484_ == 0)
{
lean_object* v___x_485_; lean_object* v_env_486_; lean_object* v_nextMacroScope_487_; lean_object* v_ngen_488_; lean_object* v_auxDeclNGen_489_; lean_object* v_traceState_490_; lean_object* v_messages_491_; lean_object* v_infoState_492_; lean_object* v_snapshotTasks_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_502_; 
v___x_485_ = lean_st_ref_take(v___y_482_);
v_env_486_ = lean_ctor_get(v___x_485_, 0);
v_nextMacroScope_487_ = lean_ctor_get(v___x_485_, 1);
v_ngen_488_ = lean_ctor_get(v___x_485_, 2);
v_auxDeclNGen_489_ = lean_ctor_get(v___x_485_, 3);
v_traceState_490_ = lean_ctor_get(v___x_485_, 4);
v_messages_491_ = lean_ctor_get(v___x_485_, 6);
v_infoState_492_ = lean_ctor_get(v___x_485_, 7);
v_snapshotTasks_493_ = lean_ctor_get(v___x_485_, 8);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_502_ == 0)
{
lean_object* v_unused_503_; 
v_unused_503_ = lean_ctor_get(v___x_485_, 5);
lean_dec(v_unused_503_);
v___x_495_ = v___x_485_;
v_isShared_496_ = v_isSharedCheck_502_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_snapshotTasks_493_);
lean_inc(v_infoState_492_);
lean_inc(v_messages_491_);
lean_inc(v_traceState_490_);
lean_inc(v_auxDeclNGen_489_);
lean_inc(v_ngen_488_);
lean_inc(v_nextMacroScope_487_);
lean_inc(v_env_486_);
lean_dec(v___x_485_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_502_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_497_ = l_Lean_Kernel_enableDiag(v_env_486_, v___y_480_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 5, v___x_349_);
lean_ctor_set(v___x_495_, 0, v___x_497_);
v___x_499_ = v___x_495_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_nextMacroScope_487_);
lean_ctor_set(v_reuseFailAlloc_501_, 2, v_ngen_488_);
lean_ctor_set(v_reuseFailAlloc_501_, 3, v_auxDeclNGen_489_);
lean_ctor_set(v_reuseFailAlloc_501_, 4, v_traceState_490_);
lean_ctor_set(v_reuseFailAlloc_501_, 5, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_501_, 6, v_messages_491_);
lean_ctor_set(v_reuseFailAlloc_501_, 7, v_infoState_492_);
lean_ctor_set(v_reuseFailAlloc_501_, 8, v_snapshotTasks_493_);
v___x_499_ = v_reuseFailAlloc_501_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_500_; 
v___x_500_ = lean_st_ref_put(v___y_482_, v___x_499_);
v___y_388_ = v___y_480_;
v___y_389_ = v___y_483_;
v___y_390_ = v___y_481_;
v___y_391_ = v___y_482_;
goto v___jp_387_;
}
}
}
else
{
v___y_388_ = v___y_480_;
v___y_389_ = v___y_483_;
v___y_390_ = v___y_481_;
v___y_391_ = v___y_482_;
goto v___jp_387_;
}
}
v___jp_506_:
{
lean_object* v___x_509_; lean_object* v_fileName_510_; lean_object* v_fileMap_511_; lean_object* v_currRecDepth_512_; lean_object* v_ref_513_; lean_object* v_currNamespace_514_; lean_object* v_openDecls_515_; lean_object* v_initHeartbeats_516_; lean_object* v_maxHeartbeats_517_; lean_object* v_quotContext_518_; lean_object* v_currMacroScope_519_; lean_object* v_cancelTk_x3f_520_; uint8_t v_suppressElabErrors_521_; lean_object* v_inheritedTraceOptions_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_534_; 
v___x_509_ = lean_st_ref_get(v___y_508_);
v_fileName_510_ = lean_ctor_get(v___y_507_, 0);
v_fileMap_511_ = lean_ctor_get(v___y_507_, 1);
v_currRecDepth_512_ = lean_ctor_get(v___y_507_, 3);
v_ref_513_ = lean_ctor_get(v___y_507_, 5);
v_currNamespace_514_ = lean_ctor_get(v___y_507_, 6);
v_openDecls_515_ = lean_ctor_get(v___y_507_, 7);
v_initHeartbeats_516_ = lean_ctor_get(v___y_507_, 8);
v_maxHeartbeats_517_ = lean_ctor_get(v___y_507_, 9);
v_quotContext_518_ = lean_ctor_get(v___y_507_, 10);
v_currMacroScope_519_ = lean_ctor_get(v___y_507_, 11);
v_cancelTk_x3f_520_ = lean_ctor_get(v___y_507_, 12);
v_suppressElabErrors_521_ = lean_ctor_get_uint8(v___y_507_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_522_ = lean_ctor_get(v___y_507_, 13);
v_isSharedCheck_534_ = !lean_is_exclusive(v___y_507_);
if (v_isSharedCheck_534_ == 0)
{
lean_object* v_unused_535_; lean_object* v_unused_536_; 
v_unused_535_ = lean_ctor_get(v___y_507_, 4);
lean_dec(v_unused_535_);
v_unused_536_ = lean_ctor_get(v___y_507_, 2);
lean_dec(v_unused_536_);
v___x_524_ = v___y_507_;
v_isShared_525_ = v_isSharedCheck_534_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_inheritedTraceOptions_522_);
lean_inc(v_cancelTk_x3f_520_);
lean_inc(v_currMacroScope_519_);
lean_inc(v_quotContext_518_);
lean_inc(v_maxHeartbeats_517_);
lean_inc(v_initHeartbeats_516_);
lean_inc(v_openDecls_515_);
lean_inc(v_currNamespace_514_);
lean_inc(v_ref_513_);
lean_inc(v_currRecDepth_512_);
lean_inc(v_fileMap_511_);
lean_inc(v_fileName_510_);
lean_dec(v___y_507_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_534_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v_env_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
v_env_526_ = lean_ctor_get(v___x_509_, 0);
lean_inc_ref(v_env_526_);
lean_dec(v___x_509_);
v___x_527_ = l_Lean_maxRecDepth;
v___x_528_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 4, v___x_528_);
lean_ctor_set(v___x_524_, 2, v___x_380_);
v___x_530_ = v___x_524_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_fileName_510_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_fileMap_511_);
lean_ctor_set(v_reuseFailAlloc_533_, 2, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_533_, 3, v_currRecDepth_512_);
lean_ctor_set(v_reuseFailAlloc_533_, 4, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_533_, 5, v_ref_513_);
lean_ctor_set(v_reuseFailAlloc_533_, 6, v_currNamespace_514_);
lean_ctor_set(v_reuseFailAlloc_533_, 7, v_openDecls_515_);
lean_ctor_set(v_reuseFailAlloc_533_, 8, v_initHeartbeats_516_);
lean_ctor_set(v_reuseFailAlloc_533_, 9, v_maxHeartbeats_517_);
lean_ctor_set(v_reuseFailAlloc_533_, 10, v_quotContext_518_);
lean_ctor_set(v_reuseFailAlloc_533_, 11, v_currMacroScope_519_);
lean_ctor_set(v_reuseFailAlloc_533_, 12, v_cancelTk_x3f_520_);
lean_ctor_set(v_reuseFailAlloc_533_, 13, v_inheritedTraceOptions_522_);
lean_ctor_set_uint8(v_reuseFailAlloc_533_, sizeof(void*)*14 + 1, v_suppressElabErrors_521_);
v___x_530_ = v_reuseFailAlloc_533_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
uint8_t v___x_531_; uint8_t v___x_532_; 
lean_ctor_set_uint8(v___x_530_, sizeof(void*)*14, v___x_505_);
v___x_531_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_331_, v___x_504_);
v___x_532_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_526_);
lean_dec_ref(v_env_526_);
if (v___x_531_ == 0)
{
if (v___x_532_ == 0)
{
v___y_388_ = v___x_531_;
v___y_389_ = v___x_527_;
v___y_390_ = v___x_530_;
v___y_391_ = v___y_508_;
goto v___jp_387_;
}
else
{
v___y_480_ = v___x_531_;
v___y_481_ = v___x_530_;
v___y_482_ = v___y_508_;
v___y_483_ = v___x_527_;
v___y_484_ = v___x_531_;
goto v___jp_479_;
}
}
else
{
v___y_480_ = v___x_531_;
v___y_481_ = v___x_530_;
v___y_482_ = v___y_508_;
v___y_483_ = v___x_527_;
v___y_484_ = v___x_532_;
goto v___jp_479_;
}
}
}
}
v___jp_537_:
{
if (v___y_538_ == 0)
{
lean_object* v___x_539_; lean_object* v_env_540_; lean_object* v_nextMacroScope_541_; lean_object* v_ngen_542_; lean_object* v_auxDeclNGen_543_; lean_object* v_traceState_544_; lean_object* v_messages_545_; lean_object* v_infoState_546_; lean_object* v_snapshotTasks_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_556_; 
v___x_539_ = lean_st_ref_take(v___x_360_);
v_env_540_ = lean_ctor_get(v___x_539_, 0);
v_nextMacroScope_541_ = lean_ctor_get(v___x_539_, 1);
v_ngen_542_ = lean_ctor_get(v___x_539_, 2);
v_auxDeclNGen_543_ = lean_ctor_get(v___x_539_, 3);
v_traceState_544_ = lean_ctor_get(v___x_539_, 4);
v_messages_545_ = lean_ctor_get(v___x_539_, 6);
v_infoState_546_ = lean_ctor_get(v___x_539_, 7);
v_snapshotTasks_547_ = lean_ctor_get(v___x_539_, 8);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_556_ == 0)
{
lean_object* v_unused_557_; 
v_unused_557_ = lean_ctor_get(v___x_539_, 5);
lean_dec(v_unused_557_);
v___x_549_ = v___x_539_;
v_isShared_550_ = v_isSharedCheck_556_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_snapshotTasks_547_);
lean_inc(v_infoState_546_);
lean_inc(v_messages_545_);
lean_inc(v_traceState_544_);
lean_inc(v_auxDeclNGen_543_);
lean_inc(v_ngen_542_);
lean_inc(v_nextMacroScope_541_);
lean_inc(v_env_540_);
lean_dec(v___x_539_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_556_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = l_Lean_Kernel_enableDiag(v_env_540_, v___x_505_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 5, v___x_349_);
lean_ctor_set(v___x_549_, 0, v___x_551_);
v___x_553_ = v___x_549_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_nextMacroScope_541_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v_ngen_542_);
lean_ctor_set(v_reuseFailAlloc_555_, 3, v_auxDeclNGen_543_);
lean_ctor_set(v_reuseFailAlloc_555_, 4, v_traceState_544_);
lean_ctor_set(v_reuseFailAlloc_555_, 5, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_555_, 6, v_messages_545_);
lean_ctor_set(v_reuseFailAlloc_555_, 7, v_infoState_546_);
lean_ctor_set(v_reuseFailAlloc_555_, 8, v_snapshotTasks_547_);
v___x_553_ = v_reuseFailAlloc_555_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_554_; 
v___x_554_ = lean_st_ref_put(v___x_360_, v___x_553_);
lean_inc(v___x_360_);
v___y_507_ = v___x_384_;
v___y_508_ = v___x_360_;
goto v___jp_506_;
}
}
}
else
{
lean_inc(v___x_360_);
v___y_507_ = v___x_384_;
v___y_508_ = v___x_360_;
goto v___jp_506_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___boxed(lean_object* v_env_559_, lean_object* v_mctx_560_, lean_object* v_lctx_561_, lean_object* v_opts_562_, lean_object* v_namingCtx_563_, lean_object* v_x_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_559_, v_mctx_560_, v_lctx_561_, v_opts_562_, v_namingCtx_563_, v_x_564_, v_a_565_, v_a_566_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
lean_dec_ref(v_namingCtx_563_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope(lean_object* v_00_u03b1_569_, lean_object* v_env_570_, lean_object* v_mctx_571_, lean_object* v_lctx_572_, lean_object* v_opts_573_, lean_object* v_namingCtx_574_, lean_object* v_x_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_570_, v_mctx_571_, v_lctx_572_, v_opts_573_, v_namingCtx_574_, v_x_575_, v_a_576_, v_a_577_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___boxed(lean_object* v_00_u03b1_580_, lean_object* v_env_581_, lean_object* v_mctx_582_, lean_object* v_lctx_583_, lean_object* v_opts_584_, lean_object* v_namingCtx_585_, lean_object* v_x_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope(v_00_u03b1_580_, v_env_581_, v_mctx_582_, v_lctx_583_, v_opts_584_, v_namingCtx_585_, v_x_586_, v_a_587_, v_a_588_);
lean_dec(v_a_588_);
lean_dec_ref(v_a_587_);
lean_dec_ref(v_namingCtx_585_);
return v_res_590_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(lean_object* v_stx_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_Syntax_getKind(v_stx_594_);
if (lean_obj_tag(v___x_595_) == 1)
{
lean_object* v_pre_596_; 
v_pre_596_ = lean_ctor_get(v___x_595_, 0);
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
lean_inc(v_pre_598_);
if (lean_obj_tag(v_pre_598_) == 1)
{
lean_object* v_pre_599_; 
v_pre_599_ = lean_ctor_get(v_pre_598_, 0);
if (lean_obj_tag(v_pre_599_) == 0)
{
lean_object* v_str_600_; lean_object* v_str_601_; lean_object* v_str_602_; lean_object* v_str_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v_str_600_ = lean_ctor_get(v___x_595_, 1);
lean_inc_ref(v_str_600_);
lean_dec_ref_known(v___x_595_, 2);
v_str_601_ = lean_ctor_get(v_pre_596_, 1);
lean_inc_ref(v_str_601_);
lean_dec_ref_known(v_pre_596_, 2);
v_str_602_ = lean_ctor_get(v_pre_597_, 1);
lean_inc_ref(v_str_602_);
lean_dec_ref_known(v_pre_597_, 2);
v_str_603_ = lean_ctor_get(v_pre_598_, 1);
lean_inc_ref(v_str_603_);
lean_dec_ref_known(v_pre_598_, 2);
v___x_604_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_605_ = lean_string_dec_eq(v_str_603_, v___x_604_);
lean_dec_ref(v_str_603_);
if (v___x_605_ == 0)
{
lean_dec_ref(v_str_602_);
lean_dec_ref(v_str_601_);
lean_dec_ref(v_str_600_);
return v___x_605_;
}
else
{
lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_606_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0));
v___x_607_ = lean_string_dec_eq(v_str_602_, v___x_606_);
lean_dec_ref(v_str_602_);
if (v___x_607_ == 0)
{
lean_dec_ref(v_str_601_);
lean_dec_ref(v_str_600_);
return v___x_607_;
}
else
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_609_ = lean_string_dec_eq(v_str_601_, v___x_608_);
lean_dec_ref(v_str_601_);
if (v___x_609_ == 0)
{
lean_dec_ref(v_str_600_);
return v___x_609_;
}
else
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__1));
v___x_611_ = lean_string_dec_eq(v_str_600_, v___x_610_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__2));
v___x_613_ = lean_string_dec_eq(v_str_600_, v___x_612_);
lean_dec_ref(v_str_600_);
return v___x_613_;
}
else
{
lean_dec_ref(v_str_600_);
return v___x_611_;
}
}
}
}
}
else
{
uint8_t v___x_614_; 
lean_dec_ref_known(v_pre_598_, 2);
lean_dec_ref_known(v_pre_597_, 2);
lean_dec_ref_known(v_pre_596_, 2);
lean_dec_ref_known(v___x_595_, 2);
v___x_614_ = 0;
return v___x_614_;
}
}
else
{
uint8_t v___x_615_; 
lean_dec_ref_known(v_pre_597_, 2);
lean_dec(v_pre_598_);
lean_dec_ref_known(v_pre_596_, 2);
lean_dec_ref_known(v___x_595_, 2);
v___x_615_ = 0;
return v___x_615_;
}
}
else
{
uint8_t v___x_616_; 
lean_dec(v_pre_597_);
lean_dec_ref_known(v_pre_596_, 2);
lean_dec_ref_known(v___x_595_, 2);
v___x_616_ = 0;
return v___x_616_;
}
}
else
{
uint8_t v___x_617_; 
lean_dec(v_pre_596_);
lean_dec_ref_known(v___x_595_, 2);
v___x_617_ = 0;
return v___x_617_;
}
}
else
{
uint8_t v___x_618_; 
lean_dec(v___x_595_);
v___x_618_ = 0;
return v___x_618_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___boxed(lean_object* v_stx_619_){
_start:
{
uint8_t v_res_620_; lean_object* v_r_621_; 
v_res_620_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(v_stx_619_);
v_r_621_ = lean_box(v_res_620_);
return v_r_621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx(lean_object* v_x_622_){
_start:
{
if (lean_obj_tag(v_x_622_) == 0)
{
lean_object* v___x_623_; 
v___x_623_ = lean_unsigned_to_nat(0u);
return v___x_623_;
}
else
{
lean_object* v___x_624_; 
v___x_624_ = lean_unsigned_to_nat(1u);
return v___x_624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx___boxed(lean_object* v_x_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx(v_x_625_);
lean_dec(v_x_625_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(lean_object* v_t_627_, lean_object* v_k_628_){
_start:
{
if (lean_obj_tag(v_t_627_) == 0)
{
lean_object* v_tacticSeq_629_; lean_object* v_insertPos_630_; lean_object* v___x_631_; 
v_tacticSeq_629_ = lean_ctor_get(v_t_627_, 0);
lean_inc(v_tacticSeq_629_);
v_insertPos_630_ = lean_ctor_get(v_t_627_, 1);
lean_inc(v_insertPos_630_);
lean_dec_ref_known(v_t_627_, 2);
v___x_631_ = lean_apply_2(v_k_628_, v_tacticSeq_629_, v_insertPos_630_);
return v___x_631_;
}
else
{
return v_k_628_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim(lean_object* v_motive_632_, lean_object* v_ctorIdx_633_, lean_object* v_t_634_, lean_object* v_h_635_, lean_object* v_k_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_634_, v_k_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___boxed(lean_object* v_motive_638_, lean_object* v_ctorIdx_639_, lean_object* v_t_640_, lean_object* v_h_641_, lean_object* v_k_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim(v_motive_638_, v_ctorIdx_639_, v_t_640_, v_h_641_, v_k_642_);
lean_dec(v_ctorIdx_639_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_unsolvedGoal_elim___redArg(lean_object* v_t_644_, lean_object* v_unsolvedGoal_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_644_, v_unsolvedGoal_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_unsolvedGoal_elim(lean_object* v_motive_647_, lean_object* v_t_648_, lean_object* v_h_649_, lean_object* v_unsolvedGoal_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_648_, v_unsolvedGoal_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_sorryTactic_elim___redArg(lean_object* v_t_652_, lean_object* v_sorryTactic_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_652_, v_sorryTactic_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_sorryTactic_elim(lean_object* v_motive_655_, lean_object* v_t_656_, lean_object* v_h_657_, lean_object* v_sorryTactic_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_656_, v_sorryTactic_658_);
return v___x_659_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed__const__1(void){
_start:
{
uint32_t v___x_663_; lean_object* v___x_664_; 
v___x_663_ = 32;
v___x_664_ = lean_box_uint32(v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(lean_object* v_tacticSeq_665_, lean_object* v_fileMap_666_){
_start:
{
uint8_t v___x_667_; lean_object* v___x_668_; 
v___x_667_ = 0;
v___x_668_ = l_Lean_Syntax_getPos_x3f(v_tacticSeq_665_, v___x_667_);
if (lean_obj_tag(v___x_668_) == 1)
{
lean_object* v_val_669_; lean_object* v___x_670_; 
v_val_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_val_669_);
lean_dec_ref_known(v___x_668_, 1);
v___x_670_ = l_Lean_Syntax_getTailPos_x3f(v_tacticSeq_665_, v___x_667_);
if (lean_obj_tag(v___x_670_) == 1)
{
lean_object* v_val_671_; lean_object* v_startPos_672_; lean_object* v_line_673_; lean_object* v_column_674_; lean_object* v_endPos_675_; lean_object* v_line_676_; uint8_t v___x_677_; 
v_val_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_val_671_);
lean_dec_ref_known(v___x_670_, 1);
lean_inc_ref(v_fileMap_666_);
v_startPos_672_ = l_Lean_FileMap_toPosition(v_fileMap_666_, v_val_669_);
lean_dec(v_val_669_);
v_line_673_ = lean_ctor_get(v_startPos_672_, 0);
lean_inc(v_line_673_);
v_column_674_ = lean_ctor_get(v_startPos_672_, 1);
lean_inc(v_column_674_);
lean_dec_ref(v_startPos_672_);
v_endPos_675_ = l_Lean_FileMap_toPosition(v_fileMap_666_, v_val_671_);
lean_dec(v_val_671_);
v_line_676_ = lean_ctor_get(v_endPos_675_, 0);
lean_inc(v_line_676_);
lean_dec_ref(v_endPos_675_);
v___x_677_ = lean_nat_dec_eq(v_line_673_, v_line_676_);
lean_dec(v_line_676_);
lean_dec(v_line_673_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_678_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__0));
v___x_679_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed__const__1;
v___x_680_ = l_List_replicateTR___redArg(v_column_674_, v___x_679_);
v___x_681_ = lean_string_mk(v___x_680_);
v___x_682_ = lean_string_append(v___x_678_, v___x_681_);
lean_dec_ref(v___x_681_);
return v___x_682_;
}
else
{
lean_object* v___x_683_; 
lean_dec(v_column_674_);
v___x_683_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__1));
return v___x_683_;
}
}
else
{
lean_object* v___x_684_; 
lean_dec(v___x_670_);
lean_dec(v_val_669_);
lean_dec_ref(v_fileMap_666_);
v___x_684_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__2));
return v___x_684_;
}
}
else
{
lean_object* v___x_685_; 
lean_dec(v___x_668_);
lean_dec_ref(v_fileMap_666_);
v___x_685_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__2));
return v___x_685_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed(lean_object* v_tacticSeq_686_, lean_object* v_fileMap_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(v_tacticSeq_686_, v_fileMap_687_);
lean_dec(v_tacticSeq_686_);
return v_res_688_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_691_ = lean_string_utf8_byte_size(v___x_690_);
return v___x_691_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_692_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1);
v___x_693_ = lean_unsigned_to_nat(0u);
v___x_694_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_695_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v___x_693_);
lean_ctor_set(v___x_695_, 2, v___x_692_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx(lean_object* v_p_696_){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_697_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_698_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2);
lean_inc(v_p_696_);
v___x_699_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
lean_ctor_set(v___x_699_, 1, v_p_696_);
lean_ctor_set(v___x_699_, 2, v___x_698_);
lean_ctor_set(v___x_699_, 3, v_p_696_);
v___x_700_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v___x_697_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(lean_object* v_range_701_){
_start:
{
lean_object* v_start_702_; lean_object* v_stop_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_713_; 
v_start_702_ = lean_ctor_get(v_range_701_, 0);
v_stop_703_ = lean_ctor_get(v_range_701_, 1);
v_isSharedCheck_713_ = !lean_is_exclusive(v_range_701_);
if (v_isSharedCheck_713_ == 0)
{
v___x_705_ = v_range_701_;
v_isShared_706_ = v_isSharedCheck_713_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_stop_703_);
lean_inc(v_start_702_);
lean_dec(v_range_701_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_713_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_707_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_708_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2);
v___x_709_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v_start_702_);
lean_ctor_set(v___x_709_, 2, v___x_708_);
lean_ctor_set(v___x_709_, 3, v_stop_703_);
if (v_isShared_706_ == 0)
{
lean_ctor_set_tag(v___x_705_, 2);
lean_ctor_set(v___x_705_, 1, v___x_707_);
lean_ctor_set(v___x_705_, 0, v___x_709_);
v___x_711_ = v___x_705_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v___x_707_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(lean_object* v_mc_x3f_714_, lean_object* v_nc_x3f_715_, lean_object* v_msg_716_, lean_object* v_acc_717_){
_start:
{
switch(lean_obj_tag(v_msg_716_))
{
case 3:
{
lean_object* v_a_718_; lean_object* v_a_719_; lean_object* v___x_720_; 
lean_dec(v_mc_x3f_714_);
v_a_718_ = lean_ctor_get(v_msg_716_, 0);
v_a_719_ = lean_ctor_get(v_msg_716_, 1);
lean_inc_ref(v_a_718_);
v___x_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_720_, 0, v_a_718_);
v_mc_x3f_714_ = v___x_720_;
v_msg_716_ = v_a_719_;
goto _start;
}
case 4:
{
lean_object* v_a_722_; lean_object* v_a_723_; lean_object* v___x_724_; 
lean_dec(v_nc_x3f_715_);
v_a_722_ = lean_ctor_get(v_msg_716_, 0);
v_a_723_ = lean_ctor_get(v_msg_716_, 1);
lean_inc_ref(v_a_722_);
v___x_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_724_, 0, v_a_722_);
v_nc_x3f_715_ = v___x_724_;
v_msg_716_ = v_a_723_;
goto _start;
}
case 5:
{
lean_object* v_a_726_; 
v_a_726_ = lean_ctor_get(v_msg_716_, 1);
v_msg_716_ = v_a_726_;
goto _start;
}
case 6:
{
lean_object* v_a_728_; 
v_a_728_ = lean_ctor_get(v_msg_716_, 0);
v_msg_716_ = v_a_728_;
goto _start;
}
case 8:
{
lean_object* v_a_730_; 
v_a_730_ = lean_ctor_get(v_msg_716_, 1);
v_msg_716_ = v_a_730_;
goto _start;
}
case 7:
{
lean_object* v_a_732_; lean_object* v_a_733_; lean_object* v___x_734_; 
v_a_732_ = lean_ctor_get(v_msg_716_, 0);
v_a_733_ = lean_ctor_get(v_msg_716_, 1);
lean_inc(v_nc_x3f_715_);
lean_inc(v_mc_x3f_714_);
v___x_734_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_714_, v_nc_x3f_715_, v_a_732_, v_acc_717_);
v_msg_716_ = v_a_733_;
v_acc_717_ = v___x_734_;
goto _start;
}
case 2:
{
lean_object* v_a_736_; 
v_a_736_ = lean_ctor_get(v_msg_716_, 1);
v_msg_716_ = v_a_736_;
goto _start;
}
case 9:
{
lean_object* v_msg_738_; lean_object* v_children_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___x_743_; 
v_msg_738_ = lean_ctor_get(v_msg_716_, 1);
v_children_739_ = lean_ctor_get(v_msg_716_, 2);
lean_inc(v_nc_x3f_715_);
lean_inc(v_mc_x3f_714_);
v___x_740_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_714_, v_nc_x3f_715_, v_msg_738_, v_acc_717_);
v___x_741_ = lean_unsigned_to_nat(0u);
v___x_742_ = lean_array_get_size(v_children_739_);
v___x_743_ = lean_nat_dec_lt(v___x_741_, v___x_742_);
if (v___x_743_ == 0)
{
lean_dec(v_nc_x3f_715_);
lean_dec(v_mc_x3f_714_);
return v___x_740_;
}
else
{
uint8_t v___x_744_; 
v___x_744_ = lean_nat_dec_le(v___x_742_, v___x_742_);
if (v___x_744_ == 0)
{
if (v___x_743_ == 0)
{
lean_dec(v_nc_x3f_715_);
lean_dec(v_mc_x3f_714_);
return v___x_740_;
}
else
{
size_t v___x_745_; size_t v___x_746_; lean_object* v___x_747_; 
v___x_745_ = ((size_t)0ULL);
v___x_746_ = lean_usize_of_nat(v___x_742_);
v___x_747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_714_, v_nc_x3f_715_, v_children_739_, v___x_745_, v___x_746_, v___x_740_);
return v___x_747_;
}
}
else
{
size_t v___x_748_; size_t v___x_749_; lean_object* v___x_750_; 
v___x_748_ = ((size_t)0ULL);
v___x_749_ = lean_usize_of_nat(v___x_742_);
v___x_750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_714_, v_nc_x3f_715_, v_children_739_, v___x_748_, v___x_749_, v___x_740_);
return v___x_750_;
}
}
}
case 1:
{
if (lean_obj_tag(v_mc_x3f_714_) == 1)
{
if (lean_obj_tag(v_nc_x3f_715_) == 1)
{
lean_object* v_a_751_; lean_object* v_val_752_; lean_object* v_val_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v_a_751_ = lean_ctor_get(v_msg_716_, 0);
v_val_752_ = lean_ctor_get(v_mc_x3f_714_, 0);
lean_inc(v_val_752_);
lean_dec_ref_known(v_mc_x3f_714_, 1);
v_val_753_ = lean_ctor_get(v_nc_x3f_715_, 0);
lean_inc(v_val_753_);
lean_dec_ref_known(v_nc_x3f_715_, 1);
lean_inc(v_a_751_);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v_val_753_);
lean_ctor_set(v___x_754_, 1, v_a_751_);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v_val_752_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v___x_756_ = lean_array_push(v_acc_717_, v___x_755_);
return v___x_756_;
}
else
{
lean_dec_ref_known(v_mc_x3f_714_, 1);
lean_dec(v_nc_x3f_715_);
return v_acc_717_;
}
}
else
{
lean_dec(v_nc_x3f_715_);
lean_dec(v_mc_x3f_714_);
return v_acc_717_;
}
}
default: 
{
lean_dec(v_nc_x3f_715_);
lean_dec(v_mc_x3f_714_);
return v_acc_717_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(lean_object* v_mc_x3f_757_, lean_object* v_nc_x3f_758_, lean_object* v_as_759_, size_t v_i_760_, size_t v_stop_761_, lean_object* v_b_762_){
_start:
{
uint8_t v___x_763_; 
v___x_763_ = lean_usize_dec_eq(v_i_760_, v_stop_761_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; lean_object* v___x_765_; size_t v___x_766_; size_t v___x_767_; 
v___x_764_ = lean_array_uget_borrowed(v_as_759_, v_i_760_);
lean_inc(v_nc_x3f_758_);
lean_inc(v_mc_x3f_757_);
v___x_765_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_757_, v_nc_x3f_758_, v___x_764_, v_b_762_);
v___x_766_ = ((size_t)1ULL);
v___x_767_ = lean_usize_add(v_i_760_, v___x_766_);
v_i_760_ = v___x_767_;
v_b_762_ = v___x_765_;
goto _start;
}
else
{
lean_dec(v_nc_x3f_758_);
lean_dec(v_mc_x3f_757_);
return v_b_762_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0___boxed(lean_object* v_mc_x3f_769_, lean_object* v_nc_x3f_770_, lean_object* v_as_771_, lean_object* v_i_772_, lean_object* v_stop_773_, lean_object* v_b_774_){
_start:
{
size_t v_i_boxed_775_; size_t v_stop_boxed_776_; lean_object* v_res_777_; 
v_i_boxed_775_ = lean_unbox_usize(v_i_772_);
lean_dec(v_i_772_);
v_stop_boxed_776_ = lean_unbox_usize(v_stop_773_);
lean_dec(v_stop_773_);
v_res_777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_769_, v_nc_x3f_770_, v_as_771_, v_i_boxed_775_, v_stop_boxed_776_, v_b_774_);
lean_dec_ref(v_as_771_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go___boxed(lean_object* v_mc_x3f_778_, lean_object* v_nc_x3f_779_, lean_object* v_msg_780_, lean_object* v_acc_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_778_, v_nc_x3f_779_, v_msg_780_, v_acc_781_);
lean_dec_ref(v_msg_780_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(lean_object* v_msg_785_){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_786_ = lean_box(0);
v___x_787_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___closed__0));
v___x_788_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v___x_786_, v___x_786_, v_msg_785_, v___x_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___boxed(lean_object* v_msg_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_msg_789_);
lean_dec_ref(v_msg_789_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f(lean_object* v_range_793_, lean_object* v_stx_794_){
_start:
{
lean_object* v___x_795_; 
lean_inc(v_stx_794_);
v___x_795_ = l_Lean_Syntax_getKind(v_stx_794_);
if (lean_obj_tag(v___x_795_) == 1)
{
lean_object* v_pre_796_; 
v_pre_796_ = lean_ctor_get(v___x_795_, 0);
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
lean_inc(v_pre_798_);
if (lean_obj_tag(v_pre_798_) == 1)
{
lean_object* v_pre_799_; 
v_pre_799_ = lean_ctor_get(v_pre_798_, 0);
if (lean_obj_tag(v_pre_799_) == 0)
{
lean_object* v_str_800_; lean_object* v_str_801_; lean_object* v_str_802_; lean_object* v_str_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v_str_800_ = lean_ctor_get(v___x_795_, 1);
lean_inc_ref(v_str_800_);
lean_dec_ref_known(v___x_795_, 2);
v_str_801_ = lean_ctor_get(v_pre_796_, 1);
lean_inc_ref(v_str_801_);
lean_dec_ref_known(v_pre_796_, 2);
v_str_802_ = lean_ctor_get(v_pre_797_, 1);
lean_inc_ref(v_str_802_);
lean_dec_ref_known(v_pre_797_, 2);
v_str_803_ = lean_ctor_get(v_pre_798_, 1);
lean_inc_ref(v_str_803_);
lean_dec_ref_known(v_pre_798_, 2);
v___x_804_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_805_ = lean_string_dec_eq(v_str_803_, v___x_804_);
lean_dec_ref(v_str_803_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; 
lean_dec_ref(v_str_802_);
lean_dec_ref(v_str_801_);
lean_dec_ref(v_str_800_);
lean_dec(v_stx_794_);
lean_dec_ref(v_range_793_);
v___x_806_ = lean_box(0);
return v___x_806_;
}
else
{
lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_807_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0));
v___x_808_ = lean_string_dec_eq(v_str_802_, v___x_807_);
lean_dec_ref(v_str_802_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; 
lean_dec_ref(v_str_801_);
lean_dec_ref(v_str_800_);
lean_dec(v_stx_794_);
lean_dec_ref(v_range_793_);
v___x_809_ = lean_box(0);
return v___x_809_;
}
else
{
lean_object* v___x_810_; uint8_t v___x_811_; 
v___x_810_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_811_ = lean_string_dec_eq(v_str_801_, v___x_810_);
lean_dec_ref(v_str_801_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; 
lean_dec_ref(v_str_800_);
lean_dec(v_stx_794_);
lean_dec_ref(v_range_793_);
v___x_812_ = lean_box(0);
return v___x_812_;
}
else
{
lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_813_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__0));
v___x_814_ = lean_string_dec_eq(v_str_800_, v___x_813_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; uint8_t v___x_816_; 
v___x_815_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__1));
v___x_816_ = lean_string_dec_eq(v_str_800_, v___x_815_);
lean_dec_ref(v_str_800_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; 
lean_dec(v_stx_794_);
lean_dec_ref(v_range_793_);
v___x_817_ = lean_box(0);
return v___x_817_;
}
else
{
lean_object* v___x_818_; lean_object* v_body_819_; lean_object* v___y_821_; lean_object* v___x_824_; 
v___x_818_ = lean_unsigned_to_nat(1u);
v_body_819_ = l_Lean_Syntax_getArg(v_stx_794_, v___x_818_);
v___x_824_ = l_Lean_Syntax_getTailPos_x3f(v_body_819_, v___x_814_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_825_ = lean_unsigned_to_nat(2u);
v___x_826_ = l_Lean_Syntax_getArg(v_stx_794_, v___x_825_);
lean_dec(v_stx_794_);
v___x_827_ = l_Lean_Syntax_getPos_x3f(v___x_826_, v___x_814_);
lean_dec(v___x_826_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_stop_828_; 
v_stop_828_ = lean_ctor_get(v_range_793_, 1);
lean_inc(v_stop_828_);
lean_dec_ref(v_range_793_);
v___y_821_ = v_stop_828_;
goto v___jp_820_;
}
else
{
lean_object* v_val_829_; 
lean_dec_ref(v_range_793_);
v_val_829_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_val_829_);
lean_dec_ref_known(v___x_827_, 1);
v___y_821_ = v_val_829_;
goto v___jp_820_;
}
}
else
{
lean_object* v_val_830_; 
lean_dec(v_stx_794_);
lean_dec_ref(v_range_793_);
v_val_830_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_val_830_);
lean_dec_ref_known(v___x_824_, 1);
v___y_821_ = v_val_830_;
goto v___jp_820_;
}
v___jp_820_:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_822_, 0, v_body_819_);
lean_ctor_set(v___x_822_, 1, v___y_821_);
v___x_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
return v___x_823_;
}
}
}
else
{
lean_object* v___x_831_; lean_object* v_body_832_; lean_object* v___y_834_; uint8_t v___x_837_; lean_object* v___x_838_; 
lean_dec_ref(v_str_800_);
v___x_831_ = lean_unsigned_to_nat(0u);
v_body_832_ = l_Lean_Syntax_getArg(v_stx_794_, v___x_831_);
lean_dec(v_stx_794_);
v___x_837_ = 0;
v___x_838_ = l_Lean_Syntax_getTailPos_x3f(v_body_832_, v___x_837_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_stop_839_; 
v_stop_839_ = lean_ctor_get(v_range_793_, 1);
lean_inc(v_stop_839_);
lean_dec_ref(v_range_793_);
v___y_834_ = v_stop_839_;
goto v___jp_833_;
}
else
{
lean_object* v_val_840_; 
lean_dec_ref(v_range_793_);
v_val_840_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_val_840_);
lean_dec_ref_known(v___x_838_, 1);
v___y_834_ = v_val_840_;
goto v___jp_833_;
}
v___jp_833_:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v_body_832_);
lean_ctor_set(v___x_835_, 1, v___y_834_);
v___x_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
return v___x_836_;
}
}
}
}
}
}
else
{
lean_object* v___x_841_; 
lean_dec_ref_known(v_pre_798_, 2);
lean_dec_ref_known(v_pre_797_, 2);
lean_dec_ref_known(v_pre_796_, 2);
lean_dec_ref_known(v___x_795_, 2);
lean_dec(v_stx_794_);
lean_dec_ref(v_range_793_);
v___x_841_ = lean_box(0);
return v___x_841_;
}
}
else
{
lean_object* v___x_842_; 
lean_dec(v_pre_798_);
lean_dec_ref_known(v_pre_797_, 2);
lean_dec_ref_known(v_pre_796_, 2);
lean_dec_ref_known(v___x_795_, 2);
lean_dec(v_stx_794_);
lean_dec_ref(v_range_793_);
v___x_842_ = lean_box(0);
return v___x_842_;
}
}
else
{
lean_object* v___x_843_; 
lean_dec(v_pre_797_);
lean_dec_ref_known(v_pre_796_, 2);
lean_dec_ref_known(v___x_795_, 2);
lean_dec(v_stx_794_);
lean_dec_ref(v_range_793_);
v___x_843_ = lean_box(0);
return v___x_843_;
}
}
else
{
lean_object* v___x_844_; 
lean_dec(v_pre_796_);
lean_dec_ref_known(v___x_795_, 2);
lean_dec(v_stx_794_);
lean_dec_ref(v_range_793_);
v___x_844_ = lean_box(0);
return v___x_844_;
}
}
else
{
lean_object* v___x_845_; 
lean_dec(v___x_795_);
lean_dec(v_stx_794_);
lean_dec_ref(v_range_793_);
v___x_845_ = lean_box(0);
return v___x_845_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(lean_object* v_range_849_, lean_object* v_stx_850_){
_start:
{
lean_object* v___x_851_; 
lean_inc(v_stx_850_);
lean_inc_ref(v_range_849_);
v___x_851_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f(v_range_849_, v_stx_850_);
if (lean_obj_tag(v___x_851_) == 1)
{
lean_dec(v_stx_850_);
lean_dec_ref(v_range_849_);
return v___x_851_;
}
else
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; size_t v_sz_855_; size_t v___x_856_; lean_object* v___x_857_; lean_object* v_fst_858_; 
lean_dec(v___x_851_);
v___x_852_ = l_Lean_Syntax_getArgs(v_stx_850_);
lean_dec(v_stx_850_);
v___x_853_ = lean_box(0);
v___x_854_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v_sz_855_ = lean_array_size(v___x_852_);
v___x_856_ = ((size_t)0ULL);
v___x_857_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(v_range_849_, v___x_852_, v_sz_855_, v___x_856_, v___x_854_);
lean_dec_ref(v___x_852_);
v_fst_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_fst_858_);
lean_dec_ref(v___x_857_);
if (lean_obj_tag(v_fst_858_) == 0)
{
return v___x_853_;
}
else
{
lean_object* v_val_859_; 
v_val_859_ = lean_ctor_get(v_fst_858_, 0);
lean_inc(v_val_859_);
lean_dec_ref_known(v_fst_858_, 1);
return v_val_859_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(lean_object* v_range_860_, lean_object* v_as_861_, size_t v_sz_862_, size_t v_i_863_, lean_object* v_b_864_){
_start:
{
uint8_t v___x_865_; 
v___x_865_ = lean_usize_dec_lt(v_i_863_, v_sz_862_);
if (v___x_865_ == 0)
{
lean_dec_ref(v_range_860_);
lean_inc_ref(v_b_864_);
return v_b_864_;
}
else
{
lean_object* v___x_866_; lean_object* v_a_867_; lean_object* v___x_868_; 
v___x_866_ = lean_box(0);
v_a_867_ = lean_array_uget_borrowed(v_as_861_, v_i_863_);
lean_inc(v_a_867_);
lean_inc_ref(v_range_860_);
v___x_868_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(v_range_860_, v_a_867_);
if (lean_obj_tag(v___x_868_) == 1)
{
lean_object* v___x_869_; lean_object* v___x_870_; 
lean_dec_ref(v_range_860_);
v___x_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
v___x_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
lean_ctor_set(v___x_870_, 1, v___x_866_);
return v___x_870_;
}
else
{
lean_object* v___x_871_; size_t v___x_872_; size_t v___x_873_; 
lean_dec(v___x_868_);
v___x_871_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v___x_872_ = ((size_t)1ULL);
v___x_873_ = lean_usize_add(v_i_863_, v___x_872_);
v_i_863_ = v___x_873_;
v_b_864_ = v___x_871_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___boxed(lean_object* v_range_875_, lean_object* v_as_876_, lean_object* v_sz_877_, lean_object* v_i_878_, lean_object* v_b_879_){
_start:
{
size_t v_sz_boxed_880_; size_t v_i_boxed_881_; lean_object* v_res_882_; 
v_sz_boxed_880_ = lean_unbox_usize(v_sz_877_);
lean_dec(v_sz_877_);
v_i_boxed_881_ = lean_unbox_usize(v_i_878_);
lean_dec(v_i_878_);
v_res_882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(v_range_875_, v_as_876_, v_sz_boxed_880_, v_i_boxed_881_, v_b_879_);
lean_dec_ref(v_b_879_);
lean_dec_ref(v_as_876_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(lean_object* v_range_883_, lean_object* v_stx_884_){
_start:
{
uint8_t v___x_885_; lean_object* v___x_886_; 
v___x_885_ = 0;
v___x_886_ = l_Lean_Syntax_getRange_x3f(v_stx_884_, v___x_885_);
if (lean_obj_tag(v___x_886_) == 1)
{
lean_object* v_val_887_; uint8_t v___x_888_; 
v_val_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_val_887_);
lean_dec_ref_known(v___x_886_, 1);
v___x_888_ = l_Lean_Syntax_Range_includes(v_val_887_, v_range_883_, v___x_885_, v___x_885_);
lean_dec(v_val_887_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; 
lean_dec(v_stx_884_);
lean_dec_ref(v_range_883_);
v___x_889_ = lean_box(0);
return v___x_889_;
}
else
{
lean_object* v___x_890_; lean_object* v___x_891_; size_t v_sz_892_; size_t v___x_893_; lean_object* v___x_894_; lean_object* v_fst_895_; 
v___x_890_ = l_Lean_Syntax_getArgs(v_stx_884_);
v___x_891_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v_sz_892_ = lean_array_size(v___x_890_);
v___x_893_ = ((size_t)0ULL);
lean_inc_ref(v_range_883_);
v___x_894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(v_range_883_, v___x_890_, v_sz_892_, v___x_893_, v___x_891_);
lean_dec_ref(v___x_890_);
v_fst_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_fst_895_);
lean_dec_ref(v___x_894_);
if (lean_obj_tag(v_fst_895_) == 0)
{
lean_object* v___x_896_; 
v___x_896_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(v_range_883_, v_stx_884_);
return v___x_896_;
}
else
{
lean_object* v_val_897_; 
lean_dec(v_stx_884_);
lean_dec_ref(v_range_883_);
v_val_897_ = lean_ctor_get(v_fst_895_, 0);
lean_inc(v_val_897_);
lean_dec_ref_known(v_fst_895_, 1);
return v_val_897_;
}
}
}
else
{
lean_object* v___x_898_; 
lean_dec(v___x_886_);
lean_dec(v_stx_884_);
lean_dec_ref(v_range_883_);
v___x_898_ = lean_box(0);
return v___x_898_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(lean_object* v_range_899_, lean_object* v_as_900_, size_t v_sz_901_, size_t v_i_902_, lean_object* v_b_903_){
_start:
{
uint8_t v___x_904_; 
v___x_904_ = lean_usize_dec_lt(v_i_902_, v_sz_901_);
if (v___x_904_ == 0)
{
lean_dec_ref(v_range_899_);
lean_inc_ref(v_b_903_);
return v_b_903_;
}
else
{
lean_object* v___x_905_; lean_object* v_a_906_; lean_object* v___x_907_; 
v___x_905_ = lean_box(0);
v_a_906_ = lean_array_uget_borrowed(v_as_900_, v_i_902_);
lean_inc(v_a_906_);
lean_inc_ref(v_range_899_);
v___x_907_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v_range_899_, v_a_906_);
if (lean_obj_tag(v___x_907_) == 1)
{
lean_object* v___x_908_; lean_object* v___x_909_; 
lean_dec_ref(v_range_899_);
v___x_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
v___x_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
lean_ctor_set(v___x_909_, 1, v___x_905_);
return v___x_909_;
}
else
{
lean_object* v___x_910_; size_t v___x_911_; size_t v___x_912_; 
lean_dec(v___x_907_);
v___x_910_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v___x_911_ = ((size_t)1ULL);
v___x_912_ = lean_usize_add(v_i_902_, v___x_911_);
v_i_902_ = v___x_912_;
v_b_903_ = v___x_910_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0___boxed(lean_object* v_range_914_, lean_object* v_as_915_, lean_object* v_sz_916_, lean_object* v_i_917_, lean_object* v_b_918_){
_start:
{
size_t v_sz_boxed_919_; size_t v_i_boxed_920_; lean_object* v_res_921_; 
v_sz_boxed_919_ = lean_unbox_usize(v_sz_916_);
lean_dec(v_sz_916_);
v_i_boxed_920_ = lean_unbox_usize(v_i_917_);
lean_dec(v_i_917_);
v_res_921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(v_range_914_, v_as_915_, v_sz_boxed_919_, v_i_boxed_920_, v_b_918_);
lean_dec_ref(v_b_918_);
lean_dec_ref(v_as_915_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody(lean_object* v_cmd_922_, lean_object* v_range_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v_range_923_, v_cmd_922_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0(lean_object* v_ctx_925_, lean_object* v_info_926_, lean_object* v_acc_927_){
_start:
{
if (lean_obj_tag(v_info_926_) == 0)
{
lean_object* v_i_928_; lean_object* v_toElabInfo_929_; lean_object* v_mctxBefore_930_; lean_object* v_goalsBefore_931_; lean_object* v_stx_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_950_; 
v_i_928_ = lean_ctor_get(v_info_926_, 0);
lean_inc_ref(v_i_928_);
lean_dec_ref_known(v_info_926_, 1);
v_toElabInfo_929_ = lean_ctor_get(v_i_928_, 0);
lean_inc_ref(v_toElabInfo_929_);
v_mctxBefore_930_ = lean_ctor_get(v_i_928_, 1);
lean_inc_ref(v_mctxBefore_930_);
v_goalsBefore_931_ = lean_ctor_get(v_i_928_, 2);
lean_inc(v_goalsBefore_931_);
lean_dec_ref(v_i_928_);
v_stx_932_ = lean_ctor_get(v_toElabInfo_929_, 1);
v_isSharedCheck_950_ = !lean_is_exclusive(v_toElabInfo_929_);
if (v_isSharedCheck_950_ == 0)
{
lean_object* v_unused_951_; 
v_unused_951_ = lean_ctor_get(v_toElabInfo_929_, 0);
lean_dec(v_unused_951_);
v___x_934_ = v_toElabInfo_929_;
v_isShared_935_ = v_isSharedCheck_950_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_stx_932_);
lean_dec(v_toElabInfo_929_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_950_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
uint8_t v___x_936_; 
lean_inc(v_stx_932_);
v___x_936_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(v_stx_932_);
if (v___x_936_ == 0)
{
lean_del_object(v___x_934_);
lean_dec(v_stx_932_);
lean_dec(v_goalsBefore_931_);
lean_dec_ref(v_mctxBefore_930_);
return v_acc_927_;
}
else
{
lean_object* v___x_937_; 
v___x_937_ = l_List_head_x3f___redArg(v_goalsBefore_931_);
lean_dec(v_goalsBefore_931_);
if (lean_obj_tag(v___x_937_) == 1)
{
lean_object* v_toCommandContextInfo_938_; lean_object* v_val_939_; lean_object* v_env_940_; lean_object* v_options_941_; lean_object* v_currNamespace_942_; lean_object* v_openDecls_943_; lean_object* v_namingCtx_945_; 
v_toCommandContextInfo_938_ = lean_ctor_get(v_ctx_925_, 0);
v_val_939_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_val_939_);
lean_dec_ref_known(v___x_937_, 1);
v_env_940_ = lean_ctor_get(v_toCommandContextInfo_938_, 0);
v_options_941_ = lean_ctor_get(v_toCommandContextInfo_938_, 4);
v_currNamespace_942_ = lean_ctor_get(v_toCommandContextInfo_938_, 5);
v_openDecls_943_ = lean_ctor_get(v_toCommandContextInfo_938_, 6);
lean_inc(v_openDecls_943_);
lean_inc(v_currNamespace_942_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 1, v_openDecls_943_);
lean_ctor_set(v___x_934_, 0, v_currNamespace_942_);
v_namingCtx_945_ = v___x_934_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_currNamespace_942_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_openDecls_943_);
v_namingCtx_945_ = v_reuseFailAlloc_949_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_946_ = lean_box(1);
lean_inc_ref(v_options_941_);
lean_inc_ref(v_env_940_);
v___x_947_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v_stx_932_);
lean_ctor_set(v___x_947_, 2, v_env_940_);
lean_ctor_set(v___x_947_, 3, v_mctxBefore_930_);
lean_ctor_set(v___x_947_, 4, v_options_941_);
lean_ctor_set(v___x_947_, 5, v_namingCtx_945_);
lean_ctor_set(v___x_947_, 6, v_val_939_);
v___x_948_ = lean_array_push(v_acc_927_, v___x_947_);
return v___x_948_;
}
}
else
{
lean_dec(v___x_937_);
lean_del_object(v___x_934_);
lean_dec(v_stx_932_);
lean_dec_ref(v_mctxBefore_930_);
return v_acc_927_;
}
}
}
}
else
{
lean_dec_ref(v_info_926_);
return v_acc_927_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0___boxed(lean_object* v_ctx_952_, lean_object* v_info_953_, lean_object* v_acc_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0(v_ctx_952_, v_info_953_, v_acc_954_);
lean_dec_ref(v_ctx_952_);
return v_res_955_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_956_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__0);
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
return v___x_958_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_959_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1);
v___x_960_ = lean_unsigned_to_nat(0u);
v___x_961_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
lean_ctor_set(v___x_961_, 2, v___x_960_);
lean_ctor_set(v___x_961_, 3, v___x_960_);
lean_ctor_set(v___x_961_, 4, v___x_959_);
lean_ctor_set(v___x_961_, 5, v___x_959_);
lean_ctor_set(v___x_961_, 6, v___x_959_);
lean_ctor_set(v___x_961_, 7, v___x_959_);
lean_ctor_set(v___x_961_, 8, v___x_959_);
lean_ctor_set(v___x_961_, 9, v___x_959_);
lean_ctor_set(v___x_961_, 10, v___x_959_);
return v___x_961_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_962_ = lean_unsigned_to_nat(32u);
v___x_963_ = lean_mk_empty_array_with_capacity(v___x_962_);
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_965_ = ((size_t)5ULL);
v___x_966_ = lean_unsigned_to_nat(0u);
v___x_967_ = lean_unsigned_to_nat(32u);
v___x_968_ = lean_mk_empty_array_with_capacity(v___x_967_);
v___x_969_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__3);
v___x_970_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_970_, 0, v___x_969_);
lean_ctor_set(v___x_970_, 1, v___x_968_);
lean_ctor_set(v___x_970_, 2, v___x_966_);
lean_ctor_set(v___x_970_, 3, v___x_966_);
lean_ctor_set_usize(v___x_970_, 4, v___x_965_);
return v___x_970_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_971_ = lean_box(1);
v___x_972_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__4);
v___x_973_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__1);
v___x_974_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
lean_ctor_set(v___x_974_, 1, v___x_972_);
lean_ctor_set(v___x_974_, 2, v___x_971_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(lean_object* v_msgData_975_, lean_object* v___y_976_){
_start:
{
lean_object* v___x_978_; lean_object* v_env_979_; lean_object* v___x_980_; lean_object* v_scopes_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v_opts_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_978_ = lean_st_ref_get(v___y_976_);
v_env_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc_ref(v_env_979_);
lean_dec(v___x_978_);
v___x_980_ = lean_st_ref_get(v___y_976_);
v_scopes_981_ = lean_ctor_get(v___x_980_, 2);
lean_inc(v_scopes_981_);
lean_dec(v___x_980_);
v___x_982_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_983_ = l_List_head_x21___redArg(v___x_982_, v_scopes_981_);
lean_dec(v_scopes_981_);
v_opts_984_ = lean_ctor_get(v___x_983_, 1);
lean_inc_ref(v_opts_984_);
lean_dec(v___x_983_);
v___x_985_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__2);
v___x_986_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___closed__5);
v___x_987_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_987_, 0, v_env_979_);
lean_ctor_set(v___x_987_, 1, v___x_985_);
lean_ctor_set(v___x_987_, 2, v___x_986_);
lean_ctor_set(v___x_987_, 3, v_opts_984_);
v___x_988_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
lean_ctor_set(v___x_988_, 1, v_msgData_975_);
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg___boxed(lean_object* v_msgData_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(v_msgData_990_, v___y_991_);
lean_dec(v___y_991_);
return v_res_993_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0(void){
_start:
{
lean_object* v___x_994_; double v___x_995_; 
v___x_994_ = lean_unsigned_to_nat(0u);
v___x_995_ = lean_float_of_nat(v___x_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(lean_object* v_cls_998_, lean_object* v_msg_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Lean_Elab_Command_getRef___redArg(v___y_1000_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1054_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(v_msg_999_, v___y_1001_);
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1054_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1054_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; lean_object* v_traceState_1011_; lean_object* v_env_1012_; lean_object* v_messages_1013_; lean_object* v_scopes_1014_; lean_object* v_usedQuotCtxts_1015_; lean_object* v_nextMacroScope_1016_; lean_object* v_maxRecDepth_1017_; lean_object* v_ngen_1018_; lean_object* v_auxDeclNGen_1019_; lean_object* v_infoState_1020_; lean_object* v_snapshotTasks_1021_; lean_object* v_prevLinterStates_1022_; lean_object* v_codeQualityEntryTasks_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1053_; 
v___x_1010_ = lean_st_ref_take(v___y_1001_);
v_traceState_1011_ = lean_ctor_get(v___x_1010_, 9);
v_env_1012_ = lean_ctor_get(v___x_1010_, 0);
v_messages_1013_ = lean_ctor_get(v___x_1010_, 1);
v_scopes_1014_ = lean_ctor_get(v___x_1010_, 2);
v_usedQuotCtxts_1015_ = lean_ctor_get(v___x_1010_, 3);
v_nextMacroScope_1016_ = lean_ctor_get(v___x_1010_, 4);
v_maxRecDepth_1017_ = lean_ctor_get(v___x_1010_, 5);
v_ngen_1018_ = lean_ctor_get(v___x_1010_, 6);
v_auxDeclNGen_1019_ = lean_ctor_get(v___x_1010_, 7);
v_infoState_1020_ = lean_ctor_get(v___x_1010_, 8);
v_snapshotTasks_1021_ = lean_ctor_get(v___x_1010_, 10);
v_prevLinterStates_1022_ = lean_ctor_get(v___x_1010_, 11);
v_codeQualityEntryTasks_1023_ = lean_ctor_get(v___x_1010_, 12);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1025_ = v___x_1010_;
v_isShared_1026_ = v_isSharedCheck_1053_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1023_);
lean_inc(v_prevLinterStates_1022_);
lean_inc(v_snapshotTasks_1021_);
lean_inc(v_traceState_1011_);
lean_inc(v_infoState_1020_);
lean_inc(v_auxDeclNGen_1019_);
lean_inc(v_ngen_1018_);
lean_inc(v_maxRecDepth_1017_);
lean_inc(v_nextMacroScope_1016_);
lean_inc(v_usedQuotCtxts_1015_);
lean_inc(v_scopes_1014_);
lean_inc(v_messages_1013_);
lean_inc(v_env_1012_);
lean_dec(v___x_1010_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1053_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
uint64_t v_tid_1027_; lean_object* v_traces_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1052_; 
v_tid_1027_ = lean_ctor_get_uint64(v_traceState_1011_, sizeof(void*)*1);
v_traces_1028_ = lean_ctor_get(v_traceState_1011_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_traceState_1011_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1030_ = v_traceState_1011_;
v_isShared_1031_ = v_isSharedCheck_1052_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_traces_1028_);
lean_dec(v_traceState_1011_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1052_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1032_; double v___x_1033_; uint8_t v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1042_; 
v___x_1032_ = lean_box(0);
v___x_1033_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0);
v___x_1034_ = 0;
v___x_1035_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_1036_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1036_, 0, v_cls_998_);
lean_ctor_set(v___x_1036_, 1, v___x_1032_);
lean_ctor_set(v___x_1036_, 2, v___x_1035_);
lean_ctor_set_float(v___x_1036_, sizeof(void*)*3, v___x_1033_);
lean_ctor_set_float(v___x_1036_, sizeof(void*)*3 + 8, v___x_1033_);
lean_ctor_set_uint8(v___x_1036_, sizeof(void*)*3 + 16, v___x_1034_);
v___x_1037_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__1));
v___x_1038_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set(v___x_1038_, 1, v_a_1006_);
lean_ctor_set(v___x_1038_, 2, v___x_1037_);
v___x_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1039_, 0, v_a_1004_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = l_Lean_PersistentArray_push___redArg(v_traces_1028_, v___x_1039_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___x_1040_);
v___x_1042_ = v___x_1030_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1040_);
lean_ctor_set_uint64(v_reuseFailAlloc_1051_, sizeof(void*)*1, v_tid_1027_);
v___x_1042_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1044_; 
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 9, v___x_1042_);
v___x_1044_ = v___x_1025_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_env_1012_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_messages_1013_);
lean_ctor_set(v_reuseFailAlloc_1050_, 2, v_scopes_1014_);
lean_ctor_set(v_reuseFailAlloc_1050_, 3, v_usedQuotCtxts_1015_);
lean_ctor_set(v_reuseFailAlloc_1050_, 4, v_nextMacroScope_1016_);
lean_ctor_set(v_reuseFailAlloc_1050_, 5, v_maxRecDepth_1017_);
lean_ctor_set(v_reuseFailAlloc_1050_, 6, v_ngen_1018_);
lean_ctor_set(v_reuseFailAlloc_1050_, 7, v_auxDeclNGen_1019_);
lean_ctor_set(v_reuseFailAlloc_1050_, 8, v_infoState_1020_);
lean_ctor_set(v_reuseFailAlloc_1050_, 9, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1050_, 10, v_snapshotTasks_1021_);
lean_ctor_set(v_reuseFailAlloc_1050_, 11, v_prevLinterStates_1022_);
lean_ctor_set(v_reuseFailAlloc_1050_, 12, v_codeQualityEntryTasks_1023_);
v___x_1044_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1045_ = lean_st_ref_put(v___y_1001_, v___x_1044_);
v___x_1046_ = lean_box(0);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1046_);
v___x_1048_ = v___x_1008_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec_ref(v_msg_999_);
lean_dec(v_cls_998_);
v_a_1055_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1003_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1003_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___boxed(lean_object* v_cls_1063_, lean_object* v_msg_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v_cls_1063_, v_msg_1064_, v___y_1065_, v___y_1066_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
return v_res_1068_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0(lean_object* v_x_1073_){
_start:
{
lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1074_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0___closed__1));
v___x_1075_ = lean_name_eq(v_x_1073_, v___x_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0___boxed(lean_object* v_x_1076_){
_start:
{
uint8_t v_res_1077_; lean_object* v_r_1078_; 
v_res_1077_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___lam__0(v_x_1076_);
lean_dec(v_x_1076_);
v_r_1078_ = lean_box(v_res_1077_);
return v_r_1078_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(lean_object* v_a_1079_, lean_object* v_x_1080_){
_start:
{
if (lean_obj_tag(v_x_1080_) == 0)
{
uint8_t v___x_1081_; 
v___x_1081_ = 0;
return v___x_1081_;
}
else
{
lean_object* v_key_1082_; lean_object* v_tail_1083_; uint8_t v___y_1085_; lean_object* v_fst_1087_; lean_object* v_snd_1088_; lean_object* v_fst_1089_; lean_object* v_snd_1090_; uint8_t v___x_1091_; 
v_key_1082_ = lean_ctor_get(v_x_1080_, 0);
v_tail_1083_ = lean_ctor_get(v_x_1080_, 2);
v_fst_1087_ = lean_ctor_get(v_key_1082_, 0);
v_snd_1088_ = lean_ctor_get(v_key_1082_, 1);
v_fst_1089_ = lean_ctor_get(v_a_1079_, 0);
v_snd_1090_ = lean_ctor_get(v_a_1079_, 1);
v___x_1091_ = l_Lean_Syntax_instBEqRange_beq(v_fst_1087_, v_fst_1089_);
if (v___x_1091_ == 0)
{
v___y_1085_ = v___x_1091_;
goto v___jp_1084_;
}
else
{
uint8_t v___x_1092_; 
v___x_1092_ = l_Lean_instBEqMVarId_beq(v_snd_1088_, v_snd_1090_);
v___y_1085_ = v___x_1092_;
goto v___jp_1084_;
}
v___jp_1084_:
{
if (v___y_1085_ == 0)
{
v_x_1080_ = v_tail_1083_;
goto _start;
}
else
{
return v___y_1085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg___boxed(lean_object* v_a_1093_, lean_object* v_x_1094_){
_start:
{
uint8_t v_res_1095_; lean_object* v_r_1096_; 
v_res_1095_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(v_a_1093_, v_x_1094_);
lean_dec(v_x_1094_);
lean_dec_ref(v_a_1093_);
v_r_1096_ = lean_box(v_res_1095_);
return v_r_1096_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(lean_object* v_m_1097_, lean_object* v_a_1098_){
_start:
{
lean_object* v_buckets_1099_; lean_object* v_fst_1100_; lean_object* v_snd_1101_; lean_object* v___x_1102_; uint64_t v___x_1103_; uint64_t v___x_1104_; uint64_t v___x_1105_; uint64_t v___x_1106_; uint64_t v___x_1107_; uint64_t v_fold_1108_; uint64_t v___x_1109_; uint64_t v___x_1110_; uint64_t v___x_1111_; size_t v___x_1112_; size_t v___x_1113_; size_t v___x_1114_; size_t v___x_1115_; size_t v___x_1116_; lean_object* v___x_1117_; uint8_t v___x_1118_; 
v_buckets_1099_ = lean_ctor_get(v_m_1097_, 1);
v_fst_1100_ = lean_ctor_get(v_a_1098_, 0);
v_snd_1101_ = lean_ctor_get(v_a_1098_, 1);
v___x_1102_ = lean_array_get_size(v_buckets_1099_);
v___x_1103_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1100_);
v___x_1104_ = l_Lean_instHashableMVarId_hash(v_snd_1101_);
v___x_1105_ = lean_uint64_mix_hash(v___x_1103_, v___x_1104_);
v___x_1106_ = 32ULL;
v___x_1107_ = lean_uint64_shift_right(v___x_1105_, v___x_1106_);
v_fold_1108_ = lean_uint64_xor(v___x_1105_, v___x_1107_);
v___x_1109_ = 16ULL;
v___x_1110_ = lean_uint64_shift_right(v_fold_1108_, v___x_1109_);
v___x_1111_ = lean_uint64_xor(v_fold_1108_, v___x_1110_);
v___x_1112_ = lean_uint64_to_usize(v___x_1111_);
v___x_1113_ = lean_usize_of_nat(v___x_1102_);
v___x_1114_ = ((size_t)1ULL);
v___x_1115_ = lean_usize_sub(v___x_1113_, v___x_1114_);
v___x_1116_ = lean_usize_land(v___x_1112_, v___x_1115_);
v___x_1117_ = lean_array_uget_borrowed(v_buckets_1099_, v___x_1116_);
v___x_1118_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(v_a_1098_, v___x_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg___boxed(lean_object* v_m_1119_, lean_object* v_a_1120_){
_start:
{
uint8_t v_res_1121_; lean_object* v_r_1122_; 
v_res_1121_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(v_m_1119_, v_a_1120_);
lean_dec_ref(v_a_1120_);
lean_dec_ref(v_m_1119_);
v_r_1122_ = lean_box(v_res_1121_);
return v_r_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3_spec__8___redArg(lean_object* v_x_1123_, lean_object* v_x_1124_){
_start:
{
if (lean_obj_tag(v_x_1124_) == 0)
{
return v_x_1123_;
}
else
{
lean_object* v_key_1125_; lean_object* v_value_1126_; lean_object* v_tail_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1154_; 
v_key_1125_ = lean_ctor_get(v_x_1124_, 0);
v_value_1126_ = lean_ctor_get(v_x_1124_, 1);
v_tail_1127_ = lean_ctor_get(v_x_1124_, 2);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_x_1124_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1129_ = v_x_1124_;
v_isShared_1130_ = v_isSharedCheck_1154_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_tail_1127_);
lean_inc(v_value_1126_);
lean_inc(v_key_1125_);
lean_dec(v_x_1124_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1154_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v_fst_1131_; lean_object* v_snd_1132_; lean_object* v___x_1133_; uint64_t v___x_1134_; uint64_t v___x_1135_; uint64_t v___x_1136_; uint64_t v___x_1137_; uint64_t v___x_1138_; uint64_t v_fold_1139_; uint64_t v___x_1140_; uint64_t v___x_1141_; uint64_t v___x_1142_; size_t v___x_1143_; size_t v___x_1144_; size_t v___x_1145_; size_t v___x_1146_; size_t v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1150_; 
v_fst_1131_ = lean_ctor_get(v_key_1125_, 0);
v_snd_1132_ = lean_ctor_get(v_key_1125_, 1);
v___x_1133_ = lean_array_get_size(v_x_1123_);
v___x_1134_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1131_);
v___x_1135_ = l_Lean_instHashableMVarId_hash(v_snd_1132_);
v___x_1136_ = lean_uint64_mix_hash(v___x_1134_, v___x_1135_);
v___x_1137_ = 32ULL;
v___x_1138_ = lean_uint64_shift_right(v___x_1136_, v___x_1137_);
v_fold_1139_ = lean_uint64_xor(v___x_1136_, v___x_1138_);
v___x_1140_ = 16ULL;
v___x_1141_ = lean_uint64_shift_right(v_fold_1139_, v___x_1140_);
v___x_1142_ = lean_uint64_xor(v_fold_1139_, v___x_1141_);
v___x_1143_ = lean_uint64_to_usize(v___x_1142_);
v___x_1144_ = lean_usize_of_nat(v___x_1133_);
v___x_1145_ = ((size_t)1ULL);
v___x_1146_ = lean_usize_sub(v___x_1144_, v___x_1145_);
v___x_1147_ = lean_usize_land(v___x_1143_, v___x_1146_);
v___x_1148_ = lean_array_uget_borrowed(v_x_1123_, v___x_1147_);
lean_inc(v___x_1148_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 2, v___x_1148_);
v___x_1150_ = v___x_1129_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_key_1125_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_value_1126_);
lean_ctor_set(v_reuseFailAlloc_1153_, 2, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_array_uset(v_x_1123_, v___x_1147_, v___x_1150_);
v_x_1123_ = v___x_1151_;
v_x_1124_ = v_tail_1127_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3___redArg(lean_object* v_i_1155_, lean_object* v_source_1156_, lean_object* v_target_1157_){
_start:
{
lean_object* v___x_1158_; uint8_t v___x_1159_; 
v___x_1158_ = lean_array_get_size(v_source_1156_);
v___x_1159_ = lean_nat_dec_lt(v_i_1155_, v___x_1158_);
if (v___x_1159_ == 0)
{
lean_dec_ref(v_source_1156_);
lean_dec(v_i_1155_);
return v_target_1157_;
}
else
{
lean_object* v_es_1160_; lean_object* v___x_1161_; lean_object* v_source_1162_; lean_object* v_target_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v_es_1160_ = lean_array_fget(v_source_1156_, v_i_1155_);
v___x_1161_ = lean_box(0);
v_source_1162_ = lean_array_fset(v_source_1156_, v_i_1155_, v___x_1161_);
v_target_1163_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3_spec__8___redArg(v_target_1157_, v_es_1160_);
v___x_1164_ = lean_unsigned_to_nat(1u);
v___x_1165_ = lean_nat_add(v_i_1155_, v___x_1164_);
lean_dec(v_i_1155_);
v_i_1155_ = v___x_1165_;
v_source_1156_ = v_source_1162_;
v_target_1157_ = v_target_1163_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2___redArg(lean_object* v_data_1167_){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v_nbuckets_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1168_ = lean_array_get_size(v_data_1167_);
v___x_1169_ = lean_unsigned_to_nat(2u);
v_nbuckets_1170_ = lean_nat_mul(v___x_1168_, v___x_1169_);
v___x_1171_ = lean_unsigned_to_nat(0u);
v___x_1172_ = lean_box(0);
v___x_1173_ = lean_mk_array(v_nbuckets_1170_, v___x_1172_);
v___x_1174_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3___redArg(v___x_1171_, v_data_1167_, v___x_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(lean_object* v_m_1175_, lean_object* v_a_1176_, lean_object* v_b_1177_){
_start:
{
lean_object* v_size_1178_; lean_object* v_buckets_1179_; lean_object* v_fst_1180_; lean_object* v_snd_1181_; lean_object* v___x_1182_; uint64_t v___x_1183_; uint64_t v___x_1184_; uint64_t v___x_1185_; uint64_t v___x_1186_; uint64_t v___x_1187_; uint64_t v_fold_1188_; uint64_t v___x_1189_; uint64_t v___x_1190_; uint64_t v___x_1191_; size_t v___x_1192_; size_t v___x_1193_; size_t v___x_1194_; size_t v___x_1195_; size_t v___x_1196_; lean_object* v_bkt_1197_; uint8_t v___x_1198_; 
v_size_1178_ = lean_ctor_get(v_m_1175_, 0);
v_buckets_1179_ = lean_ctor_get(v_m_1175_, 1);
v_fst_1180_ = lean_ctor_get(v_a_1176_, 0);
v_snd_1181_ = lean_ctor_get(v_a_1176_, 1);
v___x_1182_ = lean_array_get_size(v_buckets_1179_);
v___x_1183_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1180_);
v___x_1184_ = l_Lean_instHashableMVarId_hash(v_snd_1181_);
v___x_1185_ = lean_uint64_mix_hash(v___x_1183_, v___x_1184_);
v___x_1186_ = 32ULL;
v___x_1187_ = lean_uint64_shift_right(v___x_1185_, v___x_1186_);
v_fold_1188_ = lean_uint64_xor(v___x_1185_, v___x_1187_);
v___x_1189_ = 16ULL;
v___x_1190_ = lean_uint64_shift_right(v_fold_1188_, v___x_1189_);
v___x_1191_ = lean_uint64_xor(v_fold_1188_, v___x_1190_);
v___x_1192_ = lean_uint64_to_usize(v___x_1191_);
v___x_1193_ = lean_usize_of_nat(v___x_1182_);
v___x_1194_ = ((size_t)1ULL);
v___x_1195_ = lean_usize_sub(v___x_1193_, v___x_1194_);
v___x_1196_ = lean_usize_land(v___x_1192_, v___x_1195_);
v_bkt_1197_ = lean_array_uget_borrowed(v_buckets_1179_, v___x_1196_);
v___x_1198_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(v_a_1176_, v_bkt_1197_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1219_; 
lean_inc_ref(v_buckets_1179_);
lean_inc(v_size_1178_);
v_isSharedCheck_1219_ = !lean_is_exclusive(v_m_1175_);
if (v_isSharedCheck_1219_ == 0)
{
lean_object* v_unused_1220_; lean_object* v_unused_1221_; 
v_unused_1220_ = lean_ctor_get(v_m_1175_, 1);
lean_dec(v_unused_1220_);
v_unused_1221_ = lean_ctor_get(v_m_1175_, 0);
lean_dec(v_unused_1221_);
v___x_1200_ = v_m_1175_;
v_isShared_1201_ = v_isSharedCheck_1219_;
goto v_resetjp_1199_;
}
else
{
lean_dec(v_m_1175_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1219_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1202_; lean_object* v_size_x27_1203_; lean_object* v___x_1204_; lean_object* v_buckets_x27_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; 
v___x_1202_ = lean_unsigned_to_nat(1u);
v_size_x27_1203_ = lean_nat_add(v_size_1178_, v___x_1202_);
lean_dec(v_size_1178_);
lean_inc(v_bkt_1197_);
v___x_1204_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1204_, 0, v_a_1176_);
lean_ctor_set(v___x_1204_, 1, v_b_1177_);
lean_ctor_set(v___x_1204_, 2, v_bkt_1197_);
v_buckets_x27_1205_ = lean_array_uset(v_buckets_1179_, v___x_1196_, v___x_1204_);
v___x_1206_ = lean_unsigned_to_nat(4u);
v___x_1207_ = lean_nat_mul(v_size_x27_1203_, v___x_1206_);
v___x_1208_ = lean_unsigned_to_nat(3u);
v___x_1209_ = lean_nat_div(v___x_1207_, v___x_1208_);
lean_dec(v___x_1207_);
v___x_1210_ = lean_array_get_size(v_buckets_x27_1205_);
v___x_1211_ = lean_nat_dec_le(v___x_1209_, v___x_1210_);
lean_dec(v___x_1209_);
if (v___x_1211_ == 0)
{
lean_object* v_val_1212_; lean_object* v___x_1214_; 
v_val_1212_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2___redArg(v_buckets_x27_1205_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 1, v_val_1212_);
lean_ctor_set(v___x_1200_, 0, v_size_x27_1203_);
v___x_1214_ = v___x_1200_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_size_x27_1203_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v_val_1212_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
else
{
lean_object* v___x_1217_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 1, v_buckets_x27_1205_);
lean_ctor_set(v___x_1200_, 0, v_size_x27_1203_);
v___x_1217_ = v___x_1200_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_size_x27_1203_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v_buckets_x27_1205_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
else
{
lean_dec(v_b_1177_);
lean_dec_ref(v_a_1176_);
return v_m_1175_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(lean_object* v___x_1222_, lean_object* v_fst_1223_, lean_object* v_snd_1224_, lean_object* v___x_1225_, lean_object* v_as_1226_, size_t v_sz_1227_, size_t v_i_1228_, lean_object* v_b_1229_){
_start:
{
lean_object* v_a_1232_; uint8_t v___x_1236_; 
v___x_1236_ = lean_usize_dec_lt(v_i_1228_, v_sz_1227_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; 
lean_dec(v___x_1225_);
lean_dec(v_snd_1224_);
lean_dec(v_fst_1223_);
lean_dec_ref(v___x_1222_);
v___x_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1237_, 0, v_b_1229_);
return v___x_1237_;
}
else
{
lean_object* v_a_1238_; lean_object* v_snd_1239_; lean_object* v_fst_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1276_; 
v_a_1238_ = lean_array_uget(v_as_1226_, v_i_1228_);
v_snd_1239_ = lean_ctor_get(v_a_1238_, 1);
v_fst_1240_ = lean_ctor_get(v_a_1238_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v_a_1238_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1242_ = v_a_1238_;
v_isShared_1243_ = v_isSharedCheck_1276_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_snd_1239_);
lean_inc(v_fst_1240_);
lean_dec(v_a_1238_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1276_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v_fst_1244_; lean_object* v_snd_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1275_; 
v_fst_1244_ = lean_ctor_get(v_snd_1239_, 0);
v_snd_1245_ = lean_ctor_get(v_snd_1239_, 1);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_snd_1239_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1247_ = v_snd_1239_;
v_isShared_1248_ = v_isSharedCheck_1275_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_snd_1245_);
lean_inc(v_fst_1244_);
lean_dec(v_snd_1239_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1275_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v_fst_1249_; lean_object* v_snd_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1274_; 
v_fst_1249_ = lean_ctor_get(v_b_1229_, 0);
v_snd_1250_ = lean_ctor_get(v_b_1229_, 1);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_b_1229_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1252_ = v_b_1229_;
v_isShared_1253_ = v_isSharedCheck_1274_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_snd_1250_);
lean_inc(v_fst_1249_);
lean_dec(v_b_1229_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1274_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
lean_inc(v_snd_1245_);
lean_inc_ref(v___x_1222_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 1, v_snd_1245_);
lean_ctor_set(v___x_1252_, 0, v___x_1222_);
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1222_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_snd_1245_);
v___x_1255_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
uint8_t v___x_1256_; 
v___x_1256_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(v_snd_1250_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_object* v_env_1257_; lean_object* v_mctx_1258_; lean_object* v_opts_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1263_; 
v_env_1257_ = lean_ctor_get(v_fst_1240_, 0);
lean_inc_ref(v_env_1257_);
v_mctx_1258_ = lean_ctor_get(v_fst_1240_, 1);
lean_inc_ref(v_mctx_1258_);
v_opts_1259_ = lean_ctor_get(v_fst_1240_, 3);
lean_inc_ref(v_opts_1259_);
lean_dec(v_fst_1240_);
v___x_1260_ = lean_box(0);
v___x_1261_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_snd_1250_, v___x_1255_, v___x_1260_);
lean_inc(v_snd_1224_);
lean_inc(v_fst_1223_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 1, v_snd_1224_);
lean_ctor_set(v___x_1242_, 0, v_fst_1223_);
v___x_1263_ = v___x_1242_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_fst_1223_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v_snd_1224_);
v___x_1263_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1267_; 
lean_inc(v___x_1225_);
v___x_1264_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
lean_ctor_set(v___x_1264_, 1, v___x_1225_);
lean_ctor_set(v___x_1264_, 2, v_env_1257_);
lean_ctor_set(v___x_1264_, 3, v_mctx_1258_);
lean_ctor_set(v___x_1264_, 4, v_opts_1259_);
lean_ctor_set(v___x_1264_, 5, v_fst_1244_);
lean_ctor_set(v___x_1264_, 6, v_snd_1245_);
v___x_1265_ = lean_array_push(v_fst_1249_, v___x_1264_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 1, v___x_1261_);
lean_ctor_set(v___x_1247_, 0, v___x_1265_);
v___x_1267_ = v___x_1247_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1265_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v___x_1261_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
v_a_1232_ = v___x_1267_;
goto v___jp_1231_;
}
}
}
else
{
lean_object* v___x_1271_; 
lean_dec_ref(v___x_1255_);
lean_dec(v_snd_1245_);
lean_dec(v_fst_1244_);
lean_del_object(v___x_1242_);
lean_dec(v_fst_1240_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 1, v_snd_1250_);
lean_ctor_set(v___x_1247_, 0, v_fst_1249_);
v___x_1271_ = v___x_1247_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_fst_1249_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_snd_1250_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
v_a_1232_ = v___x_1271_;
goto v___jp_1231_;
}
}
}
}
}
}
}
v___jp_1231_:
{
size_t v___x_1233_; size_t v___x_1234_; 
v___x_1233_ = ((size_t)1ULL);
v___x_1234_ = lean_usize_add(v_i_1228_, v___x_1233_);
v_i_1228_ = v___x_1234_;
v_b_1229_ = v_a_1232_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg___boxed(lean_object* v___x_1277_, lean_object* v_fst_1278_, lean_object* v_snd_1279_, lean_object* v___x_1280_, lean_object* v_as_1281_, lean_object* v_sz_1282_, lean_object* v_i_1283_, lean_object* v_b_1284_, lean_object* v___y_1285_){
_start:
{
size_t v_sz_boxed_1286_; size_t v_i_boxed_1287_; lean_object* v_res_1288_; 
v_sz_boxed_1286_ = lean_unbox_usize(v_sz_1282_);
lean_dec(v_sz_1282_);
v_i_boxed_1287_ = lean_unbox_usize(v_i_1283_);
lean_dec(v_i_1283_);
v_res_1288_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1277_, v_fst_1278_, v_snd_1279_, v___x_1280_, v_as_1281_, v_sz_boxed_1286_, v_i_boxed_1287_, v_b_1284_);
lean_dec_ref(v_as_1281_);
return v_res_1288_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1293_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__2));
v___x_1295_ = l_Lean_Name_append(v___x_1294_, v___x_1293_);
return v___x_1295_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__4));
v___x_1298_ = l_Lean_stringToMessageData(v___x_1297_);
return v___x_1298_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7(void){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__6));
v___x_1301_ = l_Lean_stringToMessageData(v___x_1300_);
return v___x_1301_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__8));
v___x_1304_ = l_Lean_stringToMessageData(v___x_1303_);
return v___x_1304_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__10));
v___x_1307_ = l_Lean_stringToMessageData(v___x_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12(lean_object* v___x_1308_, lean_object* v_val_1309_, lean_object* v_cmd_1310_, uint8_t v_onUnsolved_1311_, uint8_t v___y_1312_, lean_object* v_as_1313_, size_t v_sz_1314_, size_t v_i_1315_, lean_object* v_b_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
uint8_t v___x_1320_; 
v___x_1320_ = lean_usize_dec_lt(v_i_1315_, v_sz_1314_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; 
lean_dec(v_cmd_1310_);
v___x_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1321_, 0, v_b_1316_);
return v___x_1321_;
}
else
{
lean_object* v_snd_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1470_; 
v_snd_1322_ = lean_ctor_get(v_b_1316_, 1);
v_isSharedCheck_1470_ = !lean_is_exclusive(v_b_1316_);
if (v_isSharedCheck_1470_ == 0)
{
lean_object* v_unused_1471_; 
v_unused_1471_ = lean_ctor_get(v_b_1316_, 0);
lean_dec(v_unused_1471_);
v___x_1324_ = v_b_1316_;
v_isShared_1325_ = v_isSharedCheck_1470_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_snd_1322_);
lean_dec(v_b_1316_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1470_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v_fst_1326_; lean_object* v_snd_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1469_; 
v_fst_1326_ = lean_ctor_get(v_snd_1322_, 0);
v_snd_1327_ = lean_ctor_get(v_snd_1322_, 1);
v_isSharedCheck_1469_ = !lean_is_exclusive(v_snd_1322_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1329_ = v_snd_1322_;
v_isShared_1330_ = v_isSharedCheck_1469_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_snd_1327_);
lean_inc(v_fst_1326_);
lean_dec(v_snd_1322_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1469_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v_a_1331_; lean_object* v_pos_1332_; lean_object* v_endPos_1333_; uint8_t v_severity_1334_; lean_object* v_data_1335_; lean_object* v___x_1336_; lean_object* v_a_1338_; 
v_a_1331_ = lean_array_uget_borrowed(v_as_1313_, v_i_1315_);
v_pos_1332_ = lean_ctor_get(v_a_1331_, 1);
v_endPos_1333_ = lean_ctor_get(v_a_1331_, 2);
lean_inc(v_endPos_1333_);
v_severity_1334_ = lean_ctor_get_uint8(v_a_1331_, sizeof(void*)*5 + 1);
v_data_1335_ = lean_ctor_get(v_a_1331_, 4);
v___x_1336_ = lean_box(0);
if (v_severity_1334_ == 2)
{
lean_object* v___f_1351_; uint8_t v___x_1352_; 
v___f_1351_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
lean_inc(v_data_1335_);
v___x_1352_ = l_Lean_MessageData_hasTag(v___f_1351_, v_data_1335_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1353_; 
lean_dec(v_endPos_1333_);
lean_del_object(v___x_1324_);
v___x_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1353_, 0, v_fst_1326_);
lean_ctor_set(v___x_1353_, 1, v_snd_1327_);
v_a_1338_ = v___x_1353_;
goto v___jp_1337_;
}
else
{
if (lean_obj_tag(v_endPos_1333_) == 1)
{
lean_object* v_val_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1466_; 
v_val_1354_ = lean_ctor_get(v_endPos_1333_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_endPos_1333_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1356_ = v_endPos_1333_;
v_isShared_1357_ = v_isSharedCheck_1466_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_val_1354_);
lean_dec(v_endPos_1333_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1466_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; uint8_t v___x_1362_; 
lean_inc_ref(v_pos_1332_);
v___x_1358_ = l_Lean_FileMap_ofPosition(v___x_1308_, v_pos_1332_);
v___x_1359_ = l_Lean_FileMap_ofPosition(v___x_1308_, v_val_1354_);
lean_inc(v___x_1359_);
lean_inc(v___x_1358_);
v___x_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1358_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
v___x_1361_ = 0;
v___x_1362_ = l_Lean_Syntax_Range_includes(v_val_1309_, v___x_1360_, v___x_1361_, v___x_1361_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; 
lean_dec_ref_known(v___x_1360_, 2);
lean_dec(v___x_1359_);
lean_dec(v___x_1358_);
lean_del_object(v___x_1356_);
lean_del_object(v___x_1324_);
v___x_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1363_, 0, v_fst_1326_);
lean_ctor_set(v___x_1363_, 1, v_snd_1327_);
v_a_1338_ = v___x_1363_;
goto v___jp_1337_;
}
else
{
lean_object* v___x_1364_; 
lean_inc(v_cmd_1310_);
lean_inc_ref(v___x_1360_);
v___x_1364_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1360_, v_cmd_1310_);
if (lean_obj_tag(v___x_1364_) == 1)
{
lean_object* v_val_1365_; lean_object* v_fst_1366_; lean_object* v_snd_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1430_; 
lean_dec(v___x_1359_);
lean_dec(v___x_1358_);
lean_del_object(v___x_1356_);
v_val_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_val_1365_);
lean_dec_ref_known(v___x_1364_, 1);
v_fst_1366_ = lean_ctor_get(v_val_1365_, 0);
v_snd_1367_ = lean_ctor_get(v_val_1365_, 1);
v_isSharedCheck_1430_ = !lean_is_exclusive(v_val_1365_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1369_ = v_val_1365_;
v_isShared_1370_ = v_isSharedCheck_1430_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_snd_1367_);
lean_inc(v_fst_1366_);
lean_dec(v_val_1365_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1430_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; uint8_t v___y_1428_; lean_object* v___x_1429_; 
v___x_1429_ = l_Lean_Syntax_getPos_x3f(v_fst_1366_, v___x_1361_);
if (lean_obj_tag(v___x_1429_) == 0)
{
v___y_1428_ = v___x_1362_;
goto v___jp_1427_;
}
else
{
lean_dec_ref_known(v___x_1429_, 1);
v___y_1428_ = v___x_1361_;
goto v___jp_1427_;
}
v___jp_1371_:
{
lean_object* v___x_1377_; 
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 1, v_snd_1327_);
lean_ctor_set(v___x_1369_, 0, v_fst_1326_);
v___x_1377_ = v___x_1369_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_fst_1326_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_snd_1327_);
v___x_1377_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
size_t v_sz_1378_; size_t v___x_1379_; lean_object* v___x_1380_; 
v_sz_1378_ = lean_array_size(v___y_1372_);
v___x_1379_ = ((size_t)0ULL);
v___x_1380_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1360_, v_fst_1366_, v_snd_1367_, v___y_1373_, v___y_1372_, v_sz_1378_, v___x_1379_, v___x_1377_);
lean_dec_ref(v___y_1372_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v_fst_1382_; lean_object* v_snd_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_a_1381_);
lean_dec_ref_known(v___x_1380_, 1);
v_fst_1382_ = lean_ctor_get(v_a_1381_, 0);
v_snd_1383_ = lean_ctor_get(v_a_1381_, 1);
v_isSharedCheck_1390_ = !lean_is_exclusive(v_a_1381_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v_a_1381_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_snd_1383_);
lean_inc(v_fst_1382_);
lean_dec(v_a_1381_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_fst_1382_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_snd_1383_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
v_a_1338_ = v___x_1388_;
goto v___jp_1337_;
}
}
}
else
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
lean_del_object(v___x_1329_);
lean_dec(v_cmd_1310_);
v_a_1391_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1380_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1380_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
}
v___jp_1400_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
lean_inc_ref(v___x_1360_);
v___x_1401_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1360_);
v___x_1402_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1335_);
v___x_1403_ = lean_array_get_size(v___x_1402_);
v___x_1404_ = lean_unsigned_to_nat(0u);
v___x_1405_ = lean_nat_dec_eq(v___x_1403_, v___x_1404_);
if (v___x_1405_ == 0)
{
v___y_1372_ = v___x_1402_;
v___y_1373_ = v___x_1401_;
v___y_1374_ = v___y_1317_;
v___y_1375_ = v___y_1318_;
goto v___jp_1371_;
}
else
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v_scopes_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v_opts_1412_; uint8_t v_hasTrace_1413_; 
v___x_1406_ = l_Lean_inheritedTraceOptions;
v___x_1407_ = lean_st_ref_get(v___x_1406_);
v___x_1408_ = lean_st_ref_get(v___y_1318_);
v_scopes_1409_ = lean_ctor_get(v___x_1408_, 2);
lean_inc(v_scopes_1409_);
lean_dec(v___x_1408_);
v___x_1410_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1411_ = l_List_head_x21___redArg(v___x_1410_, v_scopes_1409_);
lean_dec(v_scopes_1409_);
v_opts_1412_ = lean_ctor_get(v___x_1411_, 1);
lean_inc_ref(v_opts_1412_);
lean_dec(v___x_1411_);
v_hasTrace_1413_ = lean_ctor_get_uint8(v_opts_1412_, sizeof(void*)*1);
if (v_hasTrace_1413_ == 0)
{
lean_dec_ref(v_opts_1412_);
lean_dec(v___x_1407_);
v___y_1372_ = v___x_1402_;
v___y_1373_ = v___x_1401_;
v___y_1374_ = v___y_1317_;
v___y_1375_ = v___y_1318_;
goto v___jp_1371_;
}
else
{
lean_object* v___x_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; 
v___x_1414_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1415_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1416_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1407_, v_opts_1412_, v___x_1415_);
lean_dec_ref(v_opts_1412_);
lean_dec(v___x_1407_);
if (v___x_1416_ == 0)
{
v___y_1372_ = v___x_1402_;
v___y_1373_ = v___x_1401_;
v___y_1374_ = v___y_1317_;
v___y_1375_ = v___y_1318_;
goto v___jp_1371_;
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5);
v___x_1418_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1414_, v___x_1417_, v___y_1317_, v___y_1318_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_dec_ref_known(v___x_1418_, 1);
v___y_1372_ = v___x_1402_;
v___y_1373_ = v___x_1401_;
v___y_1374_ = v___y_1317_;
v___y_1375_ = v___y_1318_;
goto v___jp_1371_;
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_dec_ref(v___x_1402_);
lean_dec(v___x_1401_);
lean_del_object(v___x_1369_);
lean_dec(v_snd_1367_);
lean_dec(v_fst_1366_);
lean_dec_ref_known(v___x_1360_, 2);
lean_del_object(v___x_1329_);
lean_dec(v_snd_1327_);
lean_dec(v_fst_1326_);
lean_dec(v_cmd_1310_);
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1418_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1418_);
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
}
}
v___jp_1427_:
{
if (v_onUnsolved_1311_ == 0)
{
if (v___y_1312_ == 0)
{
lean_del_object(v___x_1369_);
lean_dec(v_snd_1367_);
lean_dec(v_fst_1366_);
lean_dec_ref_known(v___x_1360_, 2);
goto v___jp_1345_;
}
else
{
if (v___y_1428_ == 0)
{
lean_del_object(v___x_1369_);
lean_dec(v_snd_1367_);
lean_dec(v_fst_1366_);
lean_dec_ref_known(v___x_1360_, 2);
goto v___jp_1345_;
}
else
{
lean_del_object(v___x_1324_);
goto v___jp_1400_;
}
}
}
else
{
lean_del_object(v___x_1324_);
goto v___jp_1400_;
}
}
}
}
else
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v_scopes_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v_opts_1437_; uint8_t v_hasTrace_1438_; 
lean_dec(v___x_1364_);
lean_dec_ref_known(v___x_1360_, 2);
lean_del_object(v___x_1324_);
v___x_1431_ = l_Lean_inheritedTraceOptions;
v___x_1432_ = lean_st_ref_get(v___x_1431_);
v___x_1433_ = lean_st_ref_get(v___y_1318_);
v_scopes_1434_ = lean_ctor_get(v___x_1433_, 2);
lean_inc(v_scopes_1434_);
lean_dec(v___x_1433_);
v___x_1435_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1436_ = l_List_head_x21___redArg(v___x_1435_, v_scopes_1434_);
lean_dec(v_scopes_1434_);
v_opts_1437_ = lean_ctor_get(v___x_1436_, 1);
lean_inc_ref(v_opts_1437_);
lean_dec(v___x_1436_);
v_hasTrace_1438_ = lean_ctor_get_uint8(v_opts_1437_, sizeof(void*)*1);
if (v_hasTrace_1438_ == 0)
{
lean_dec_ref(v_opts_1437_);
lean_dec(v___x_1432_);
lean_dec(v___x_1359_);
lean_dec(v___x_1358_);
lean_del_object(v___x_1356_);
goto v___jp_1349_;
}
else
{
lean_object* v___x_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; 
v___x_1439_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1440_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1441_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1432_, v_opts_1437_, v___x_1440_);
lean_dec_ref(v_opts_1437_);
lean_dec(v___x_1432_);
if (v___x_1441_ == 0)
{
lean_dec(v___x_1359_);
lean_dec(v___x_1358_);
lean_del_object(v___x_1356_);
goto v___jp_1349_;
}
else
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1445_; 
v___x_1442_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7);
v___x_1443_ = l_Nat_reprFast(v___x_1358_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set_tag(v___x_1356_, 3);
lean_ctor_set(v___x_1356_, 0, v___x_1443_);
v___x_1445_ = v___x_1356_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1443_);
v___x_1445_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1446_ = l_Lean_MessageData_ofFormat(v___x_1445_);
v___x_1447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1442_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
v___x_1448_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9);
v___x_1449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1447_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = l_Nat_reprFast(v___x_1359_);
v___x_1451_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
v___x_1452_ = l_Lean_MessageData_ofFormat(v___x_1451_);
v___x_1453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1449_);
lean_ctor_set(v___x_1453_, 1, v___x_1452_);
v___x_1454_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11);
v___x_1455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1453_);
lean_ctor_set(v___x_1455_, 1, v___x_1454_);
v___x_1456_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1439_, v___x_1455_, v___y_1317_, v___y_1318_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_dec_ref_known(v___x_1456_, 1);
goto v___jp_1349_;
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_del_object(v___x_1329_);
lean_dec(v_snd_1327_);
lean_dec(v_fst_1326_);
lean_dec(v_cmd_1310_);
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1456_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1456_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
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
lean_object* v___x_1467_; 
lean_dec(v_endPos_1333_);
lean_del_object(v___x_1324_);
v___x_1467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1467_, 0, v_fst_1326_);
lean_ctor_set(v___x_1467_, 1, v_snd_1327_);
v_a_1338_ = v___x_1467_;
goto v___jp_1337_;
}
}
}
else
{
lean_object* v___x_1468_; 
lean_dec(v_endPos_1333_);
lean_del_object(v___x_1324_);
v___x_1468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1468_, 0, v_fst_1326_);
lean_ctor_set(v___x_1468_, 1, v_snd_1327_);
v_a_1338_ = v___x_1468_;
goto v___jp_1337_;
}
v___jp_1337_:
{
lean_object* v___x_1340_; 
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 1, v_a_1338_);
lean_ctor_set(v___x_1329_, 0, v___x_1336_);
v___x_1340_ = v___x_1329_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1336_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v_a_1338_);
v___x_1340_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
size_t v___x_1341_; size_t v___x_1342_; 
v___x_1341_ = ((size_t)1ULL);
v___x_1342_ = lean_usize_add(v_i_1315_, v___x_1341_);
v_i_1315_ = v___x_1342_;
v_b_1316_ = v___x_1340_;
goto _start;
}
}
v___jp_1345_:
{
lean_object* v___x_1347_; 
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 1, v_snd_1327_);
lean_ctor_set(v___x_1324_, 0, v_fst_1326_);
v___x_1347_ = v___x_1324_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_fst_1326_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v_snd_1327_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
v_a_1338_ = v___x_1347_;
goto v___jp_1337_;
}
}
v___jp_1349_:
{
lean_object* v___x_1350_; 
v___x_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1350_, 0, v_fst_1326_);
lean_ctor_set(v___x_1350_, 1, v_snd_1327_);
v_a_1338_ = v___x_1350_;
goto v___jp_1337_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___boxed(lean_object* v___x_1472_, lean_object* v_val_1473_, lean_object* v_cmd_1474_, lean_object* v_onUnsolved_1475_, lean_object* v___y_1476_, lean_object* v_as_1477_, lean_object* v_sz_1478_, lean_object* v_i_1479_, lean_object* v_b_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
uint8_t v_onUnsolved_boxed_1484_; uint8_t v___y_11924__boxed_1485_; size_t v_sz_boxed_1486_; size_t v_i_boxed_1487_; lean_object* v_res_1488_; 
v_onUnsolved_boxed_1484_ = lean_unbox(v_onUnsolved_1475_);
v___y_11924__boxed_1485_ = lean_unbox(v___y_1476_);
v_sz_boxed_1486_ = lean_unbox_usize(v_sz_1478_);
lean_dec(v_sz_1478_);
v_i_boxed_1487_ = lean_unbox_usize(v_i_1479_);
lean_dec(v_i_1479_);
v_res_1488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12(v___x_1472_, v_val_1473_, v_cmd_1474_, v_onUnsolved_boxed_1484_, v___y_11924__boxed_1485_, v_as_1477_, v_sz_boxed_1486_, v_i_boxed_1487_, v_b_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec_ref(v_as_1477_);
lean_dec_ref(v_val_1473_);
lean_dec_ref(v___x_1472_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8(lean_object* v___x_1489_, lean_object* v_val_1490_, lean_object* v_cmd_1491_, uint8_t v_onUnsolved_1492_, uint8_t v___y_1493_, lean_object* v_as_1494_, size_t v_sz_1495_, size_t v_i_1496_, lean_object* v_b_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
uint8_t v___x_1501_; 
v___x_1501_ = lean_usize_dec_lt(v_i_1496_, v_sz_1495_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; 
lean_dec(v_cmd_1491_);
v___x_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1502_, 0, v_b_1497_);
return v___x_1502_;
}
else
{
lean_object* v_snd_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1651_; 
v_snd_1503_ = lean_ctor_get(v_b_1497_, 1);
v_isSharedCheck_1651_ = !lean_is_exclusive(v_b_1497_);
if (v_isSharedCheck_1651_ == 0)
{
lean_object* v_unused_1652_; 
v_unused_1652_ = lean_ctor_get(v_b_1497_, 0);
lean_dec(v_unused_1652_);
v___x_1505_ = v_b_1497_;
v_isShared_1506_ = v_isSharedCheck_1651_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_snd_1503_);
lean_dec(v_b_1497_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1651_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v_fst_1507_; lean_object* v_snd_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1650_; 
v_fst_1507_ = lean_ctor_get(v_snd_1503_, 0);
v_snd_1508_ = lean_ctor_get(v_snd_1503_, 1);
v_isSharedCheck_1650_ = !lean_is_exclusive(v_snd_1503_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1510_ = v_snd_1503_;
v_isShared_1511_ = v_isSharedCheck_1650_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_snd_1508_);
lean_inc(v_fst_1507_);
lean_dec(v_snd_1503_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1650_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v_a_1512_; lean_object* v_pos_1513_; lean_object* v_endPos_1514_; uint8_t v_severity_1515_; lean_object* v_data_1516_; lean_object* v___x_1517_; lean_object* v_a_1519_; 
v_a_1512_ = lean_array_uget_borrowed(v_as_1494_, v_i_1496_);
v_pos_1513_ = lean_ctor_get(v_a_1512_, 1);
v_endPos_1514_ = lean_ctor_get(v_a_1512_, 2);
lean_inc(v_endPos_1514_);
v_severity_1515_ = lean_ctor_get_uint8(v_a_1512_, sizeof(void*)*5 + 1);
v_data_1516_ = lean_ctor_get(v_a_1512_, 4);
v___x_1517_ = lean_box(0);
if (v_severity_1515_ == 2)
{
lean_object* v___f_1532_; uint8_t v___x_1533_; 
v___f_1532_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
lean_inc(v_data_1516_);
v___x_1533_ = l_Lean_MessageData_hasTag(v___f_1532_, v_data_1516_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1534_; 
lean_dec(v_endPos_1514_);
lean_del_object(v___x_1505_);
v___x_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1534_, 0, v_fst_1507_);
lean_ctor_set(v___x_1534_, 1, v_snd_1508_);
v_a_1519_ = v___x_1534_;
goto v___jp_1518_;
}
else
{
if (lean_obj_tag(v_endPos_1514_) == 1)
{
lean_object* v_val_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1647_; 
v_val_1535_ = lean_ctor_get(v_endPos_1514_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_endPos_1514_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1537_ = v_endPos_1514_;
v_isShared_1538_ = v_isSharedCheck_1647_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_val_1535_);
lean_dec(v_endPos_1514_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1647_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; uint8_t v___x_1542_; uint8_t v___x_1543_; 
lean_inc_ref(v_pos_1513_);
v___x_1539_ = l_Lean_FileMap_ofPosition(v___x_1489_, v_pos_1513_);
v___x_1540_ = l_Lean_FileMap_ofPosition(v___x_1489_, v_val_1535_);
lean_inc(v___x_1540_);
lean_inc(v___x_1539_);
v___x_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1539_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = 0;
v___x_1543_ = l_Lean_Syntax_Range_includes(v_val_1490_, v___x_1541_, v___x_1542_, v___x_1542_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; 
lean_dec_ref_known(v___x_1541_, 2);
lean_dec(v___x_1540_);
lean_dec(v___x_1539_);
lean_del_object(v___x_1537_);
lean_del_object(v___x_1505_);
v___x_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1544_, 0, v_fst_1507_);
lean_ctor_set(v___x_1544_, 1, v_snd_1508_);
v_a_1519_ = v___x_1544_;
goto v___jp_1518_;
}
else
{
lean_object* v___x_1545_; 
lean_inc(v_cmd_1491_);
lean_inc_ref(v___x_1541_);
v___x_1545_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1541_, v_cmd_1491_);
if (lean_obj_tag(v___x_1545_) == 1)
{
lean_object* v_val_1546_; lean_object* v_fst_1547_; lean_object* v_snd_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1611_; 
lean_dec(v___x_1540_);
lean_dec(v___x_1539_);
lean_del_object(v___x_1537_);
v_val_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_val_1546_);
lean_dec_ref_known(v___x_1545_, 1);
v_fst_1547_ = lean_ctor_get(v_val_1546_, 0);
v_snd_1548_ = lean_ctor_get(v_val_1546_, 1);
v_isSharedCheck_1611_ = !lean_is_exclusive(v_val_1546_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1550_ = v_val_1546_;
v_isShared_1551_ = v_isSharedCheck_1611_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_snd_1548_);
lean_inc(v_fst_1547_);
lean_dec(v_val_1546_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1611_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; uint8_t v___y_1609_; lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_Syntax_getPos_x3f(v_fst_1547_, v___x_1542_);
if (lean_obj_tag(v___x_1610_) == 0)
{
v___y_1609_ = v___x_1543_;
goto v___jp_1608_;
}
else
{
lean_dec_ref_known(v___x_1610_, 1);
v___y_1609_ = v___x_1542_;
goto v___jp_1608_;
}
v___jp_1552_:
{
lean_object* v___x_1558_; 
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 1, v_snd_1508_);
lean_ctor_set(v___x_1550_, 0, v_fst_1507_);
v___x_1558_ = v___x_1550_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_fst_1507_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_snd_1508_);
v___x_1558_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
size_t v_sz_1559_; size_t v___x_1560_; lean_object* v___x_1561_; 
v_sz_1559_ = lean_array_size(v___y_1554_);
v___x_1560_ = ((size_t)0ULL);
v___x_1561_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1541_, v_fst_1547_, v_snd_1548_, v___y_1553_, v___y_1554_, v_sz_1559_, v___x_1560_, v___x_1558_);
lean_dec_ref(v___y_1554_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v_fst_1563_; lean_object* v_snd_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref_known(v___x_1561_, 1);
v_fst_1563_ = lean_ctor_get(v_a_1562_, 0);
v_snd_1564_ = lean_ctor_get(v_a_1562_, 1);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_a_1562_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v_a_1562_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_snd_1564_);
lean_inc(v_fst_1563_);
lean_dec(v_a_1562_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_fst_1563_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_snd_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
v_a_1519_ = v___x_1569_;
goto v___jp_1518_;
}
}
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_del_object(v___x_1510_);
lean_dec(v_cmd_1491_);
v_a_1572_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1561_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1561_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
v___jp_1581_:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; uint8_t v___x_1586_; 
lean_inc_ref(v___x_1541_);
v___x_1582_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1541_);
v___x_1583_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1516_);
v___x_1584_ = lean_array_get_size(v___x_1583_);
v___x_1585_ = lean_unsigned_to_nat(0u);
v___x_1586_ = lean_nat_dec_eq(v___x_1584_, v___x_1585_);
if (v___x_1586_ == 0)
{
v___y_1553_ = v___x_1582_;
v___y_1554_ = v___x_1583_;
v___y_1555_ = v___y_1498_;
v___y_1556_ = v___y_1499_;
goto v___jp_1552_;
}
else
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v_scopes_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v_opts_1593_; uint8_t v_hasTrace_1594_; 
v___x_1587_ = l_Lean_inheritedTraceOptions;
v___x_1588_ = lean_st_ref_get(v___x_1587_);
v___x_1589_ = lean_st_ref_get(v___y_1499_);
v_scopes_1590_ = lean_ctor_get(v___x_1589_, 2);
lean_inc(v_scopes_1590_);
lean_dec(v___x_1589_);
v___x_1591_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1592_ = l_List_head_x21___redArg(v___x_1591_, v_scopes_1590_);
lean_dec(v_scopes_1590_);
v_opts_1593_ = lean_ctor_get(v___x_1592_, 1);
lean_inc_ref(v_opts_1593_);
lean_dec(v___x_1592_);
v_hasTrace_1594_ = lean_ctor_get_uint8(v_opts_1593_, sizeof(void*)*1);
if (v_hasTrace_1594_ == 0)
{
lean_dec_ref(v_opts_1593_);
lean_dec(v___x_1588_);
v___y_1553_ = v___x_1582_;
v___y_1554_ = v___x_1583_;
v___y_1555_ = v___y_1498_;
v___y_1556_ = v___y_1499_;
goto v___jp_1552_;
}
else
{
lean_object* v___x_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1595_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1596_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1597_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1588_, v_opts_1593_, v___x_1596_);
lean_dec_ref(v_opts_1593_);
lean_dec(v___x_1588_);
if (v___x_1597_ == 0)
{
v___y_1553_ = v___x_1582_;
v___y_1554_ = v___x_1583_;
v___y_1555_ = v___y_1498_;
v___y_1556_ = v___y_1499_;
goto v___jp_1552_;
}
else
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5);
v___x_1599_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1595_, v___x_1598_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_dec_ref_known(v___x_1599_, 1);
v___y_1553_ = v___x_1582_;
v___y_1554_ = v___x_1583_;
v___y_1555_ = v___y_1498_;
v___y_1556_ = v___y_1499_;
goto v___jp_1552_;
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec_ref(v___x_1583_);
lean_dec(v___x_1582_);
lean_del_object(v___x_1550_);
lean_dec(v_snd_1548_);
lean_dec(v_fst_1547_);
lean_dec_ref_known(v___x_1541_, 2);
lean_del_object(v___x_1510_);
lean_dec(v_snd_1508_);
lean_dec(v_fst_1507_);
lean_dec(v_cmd_1491_);
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1599_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1599_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
}
}
v___jp_1608_:
{
if (v_onUnsolved_1492_ == 0)
{
if (v___y_1493_ == 0)
{
lean_del_object(v___x_1550_);
lean_dec(v_snd_1548_);
lean_dec(v_fst_1547_);
lean_dec_ref_known(v___x_1541_, 2);
goto v___jp_1526_;
}
else
{
if (v___y_1609_ == 0)
{
lean_del_object(v___x_1550_);
lean_dec(v_snd_1548_);
lean_dec(v_fst_1547_);
lean_dec_ref_known(v___x_1541_, 2);
goto v___jp_1526_;
}
else
{
lean_del_object(v___x_1505_);
goto v___jp_1581_;
}
}
}
else
{
lean_del_object(v___x_1505_);
goto v___jp_1581_;
}
}
}
}
else
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v_scopes_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v_opts_1618_; uint8_t v_hasTrace_1619_; 
lean_dec(v___x_1545_);
lean_dec_ref_known(v___x_1541_, 2);
lean_del_object(v___x_1505_);
v___x_1612_ = l_Lean_inheritedTraceOptions;
v___x_1613_ = lean_st_ref_get(v___x_1612_);
v___x_1614_ = lean_st_ref_get(v___y_1499_);
v_scopes_1615_ = lean_ctor_get(v___x_1614_, 2);
lean_inc(v_scopes_1615_);
lean_dec(v___x_1614_);
v___x_1616_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1617_ = l_List_head_x21___redArg(v___x_1616_, v_scopes_1615_);
lean_dec(v_scopes_1615_);
v_opts_1618_ = lean_ctor_get(v___x_1617_, 1);
lean_inc_ref(v_opts_1618_);
lean_dec(v___x_1617_);
v_hasTrace_1619_ = lean_ctor_get_uint8(v_opts_1618_, sizeof(void*)*1);
if (v_hasTrace_1619_ == 0)
{
lean_dec_ref(v_opts_1618_);
lean_dec(v___x_1613_);
lean_dec(v___x_1540_);
lean_dec(v___x_1539_);
lean_del_object(v___x_1537_);
goto v___jp_1530_;
}
else
{
lean_object* v___x_1620_; lean_object* v___x_1621_; uint8_t v___x_1622_; 
v___x_1620_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1621_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1622_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1613_, v_opts_1618_, v___x_1621_);
lean_dec_ref(v_opts_1618_);
lean_dec(v___x_1613_);
if (v___x_1622_ == 0)
{
lean_dec(v___x_1540_);
lean_dec(v___x_1539_);
lean_del_object(v___x_1537_);
goto v___jp_1530_;
}
else
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1626_; 
v___x_1623_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7);
v___x_1624_ = l_Nat_reprFast(v___x_1539_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set_tag(v___x_1537_, 3);
lean_ctor_set(v___x_1537_, 0, v___x_1624_);
v___x_1626_ = v___x_1537_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1624_);
v___x_1626_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1627_ = l_Lean_MessageData_ofFormat(v___x_1626_);
v___x_1628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1623_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
v___x_1629_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9);
v___x_1630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1628_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
v___x_1631_ = l_Nat_reprFast(v___x_1540_);
v___x_1632_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
v___x_1633_ = l_Lean_MessageData_ofFormat(v___x_1632_);
v___x_1634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1630_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11);
v___x_1636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1634_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1620_, v___x_1636_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_dec_ref_known(v___x_1637_, 1);
goto v___jp_1530_;
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
lean_del_object(v___x_1510_);
lean_dec(v_snd_1508_);
lean_dec(v_fst_1507_);
lean_dec(v_cmd_1491_);
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1637_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1637_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
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
lean_object* v___x_1648_; 
lean_dec(v_endPos_1514_);
lean_del_object(v___x_1505_);
v___x_1648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1648_, 0, v_fst_1507_);
lean_ctor_set(v___x_1648_, 1, v_snd_1508_);
v_a_1519_ = v___x_1648_;
goto v___jp_1518_;
}
}
}
else
{
lean_object* v___x_1649_; 
lean_dec(v_endPos_1514_);
lean_del_object(v___x_1505_);
v___x_1649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1649_, 0, v_fst_1507_);
lean_ctor_set(v___x_1649_, 1, v_snd_1508_);
v_a_1519_ = v___x_1649_;
goto v___jp_1518_;
}
v___jp_1518_:
{
lean_object* v___x_1521_; 
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 1, v_a_1519_);
lean_ctor_set(v___x_1510_, 0, v___x_1517_);
v___x_1521_ = v___x_1510_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_a_1519_);
v___x_1521_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
size_t v___x_1522_; size_t v___x_1523_; lean_object* v___x_1524_; 
v___x_1522_ = ((size_t)1ULL);
v___x_1523_ = lean_usize_add(v_i_1496_, v___x_1522_);
v___x_1524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12(v___x_1489_, v_val_1490_, v_cmd_1491_, v_onUnsolved_1492_, v___y_1493_, v_as_1494_, v_sz_1495_, v___x_1523_, v___x_1521_, v___y_1498_, v___y_1499_);
return v___x_1524_;
}
}
v___jp_1526_:
{
lean_object* v___x_1528_; 
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 1, v_snd_1508_);
lean_ctor_set(v___x_1505_, 0, v_fst_1507_);
v___x_1528_ = v___x_1505_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_fst_1507_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_snd_1508_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
v_a_1519_ = v___x_1528_;
goto v___jp_1518_;
}
}
v___jp_1530_:
{
lean_object* v___x_1531_; 
v___x_1531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1531_, 0, v_fst_1507_);
lean_ctor_set(v___x_1531_, 1, v_snd_1508_);
v_a_1519_ = v___x_1531_;
goto v___jp_1518_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8___boxed(lean_object* v___x_1653_, lean_object* v_val_1654_, lean_object* v_cmd_1655_, lean_object* v_onUnsolved_1656_, lean_object* v___y_1657_, lean_object* v_as_1658_, lean_object* v_sz_1659_, lean_object* v_i_1660_, lean_object* v_b_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
uint8_t v_onUnsolved_boxed_1665_; uint8_t v___y_12265__boxed_1666_; size_t v_sz_boxed_1667_; size_t v_i_boxed_1668_; lean_object* v_res_1669_; 
v_onUnsolved_boxed_1665_ = lean_unbox(v_onUnsolved_1656_);
v___y_12265__boxed_1666_ = lean_unbox(v___y_1657_);
v_sz_boxed_1667_ = lean_unbox_usize(v_sz_1659_);
lean_dec(v_sz_1659_);
v_i_boxed_1668_ = lean_unbox_usize(v_i_1660_);
lean_dec(v_i_1660_);
v_res_1669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8(v___x_1653_, v_val_1654_, v_cmd_1655_, v_onUnsolved_boxed_1665_, v___y_12265__boxed_1666_, v_as_1658_, v_sz_boxed_1667_, v_i_boxed_1668_, v_b_1661_, v___y_1662_, v___y_1663_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec_ref(v_as_1658_);
lean_dec_ref(v_val_1654_);
lean_dec_ref(v___x_1653_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10_spec__12(lean_object* v___x_1670_, lean_object* v_val_1671_, lean_object* v_cmd_1672_, uint8_t v_onUnsolved_1673_, uint8_t v___y_1674_, lean_object* v_as_1675_, size_t v_sz_1676_, size_t v_i_1677_, lean_object* v_b_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
uint8_t v___x_1682_; 
v___x_1682_ = lean_usize_dec_lt(v_i_1677_, v_sz_1676_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; 
lean_dec(v_cmd_1672_);
v___x_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1683_, 0, v_b_1678_);
return v___x_1683_;
}
else
{
lean_object* v_snd_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1832_; 
v_snd_1684_ = lean_ctor_get(v_b_1678_, 1);
v_isSharedCheck_1832_ = !lean_is_exclusive(v_b_1678_);
if (v_isSharedCheck_1832_ == 0)
{
lean_object* v_unused_1833_; 
v_unused_1833_ = lean_ctor_get(v_b_1678_, 0);
lean_dec(v_unused_1833_);
v___x_1686_ = v_b_1678_;
v_isShared_1687_ = v_isSharedCheck_1832_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_snd_1684_);
lean_dec(v_b_1678_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1832_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v_fst_1688_; lean_object* v_snd_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1831_; 
v_fst_1688_ = lean_ctor_get(v_snd_1684_, 0);
v_snd_1689_ = lean_ctor_get(v_snd_1684_, 1);
v_isSharedCheck_1831_ = !lean_is_exclusive(v_snd_1684_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1691_ = v_snd_1684_;
v_isShared_1692_ = v_isSharedCheck_1831_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_snd_1689_);
lean_inc(v_fst_1688_);
lean_dec(v_snd_1684_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1831_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v_a_1693_; lean_object* v_pos_1694_; lean_object* v_endPos_1695_; uint8_t v_severity_1696_; lean_object* v_data_1697_; lean_object* v___x_1698_; lean_object* v_a_1700_; 
v_a_1693_ = lean_array_uget_borrowed(v_as_1675_, v_i_1677_);
v_pos_1694_ = lean_ctor_get(v_a_1693_, 1);
v_endPos_1695_ = lean_ctor_get(v_a_1693_, 2);
lean_inc(v_endPos_1695_);
v_severity_1696_ = lean_ctor_get_uint8(v_a_1693_, sizeof(void*)*5 + 1);
v_data_1697_ = lean_ctor_get(v_a_1693_, 4);
v___x_1698_ = lean_box(0);
if (v_severity_1696_ == 2)
{
lean_object* v___f_1713_; uint8_t v___x_1714_; 
v___f_1713_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
lean_inc(v_data_1697_);
v___x_1714_ = l_Lean_MessageData_hasTag(v___f_1713_, v_data_1697_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; 
lean_dec(v_endPos_1695_);
lean_del_object(v___x_1686_);
v___x_1715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1715_, 0, v_fst_1688_);
lean_ctor_set(v___x_1715_, 1, v_snd_1689_);
v_a_1700_ = v___x_1715_;
goto v___jp_1699_;
}
else
{
if (lean_obj_tag(v_endPos_1695_) == 1)
{
lean_object* v_val_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1828_; 
v_val_1716_ = lean_ctor_get(v_endPos_1695_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v_endPos_1695_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1718_ = v_endPos_1695_;
v_isShared_1719_ = v_isSharedCheck_1828_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_val_1716_);
lean_dec(v_endPos_1695_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1828_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; uint8_t v___x_1723_; uint8_t v___x_1724_; 
lean_inc_ref(v_pos_1694_);
v___x_1720_ = l_Lean_FileMap_ofPosition(v___x_1670_, v_pos_1694_);
v___x_1721_ = l_Lean_FileMap_ofPosition(v___x_1670_, v_val_1716_);
lean_inc(v___x_1721_);
lean_inc(v___x_1720_);
v___x_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1720_);
lean_ctor_set(v___x_1722_, 1, v___x_1721_);
v___x_1723_ = 0;
v___x_1724_ = l_Lean_Syntax_Range_includes(v_val_1671_, v___x_1722_, v___x_1723_, v___x_1723_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1725_; 
lean_dec_ref_known(v___x_1722_, 2);
lean_dec(v___x_1721_);
lean_dec(v___x_1720_);
lean_del_object(v___x_1718_);
lean_del_object(v___x_1686_);
v___x_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1725_, 0, v_fst_1688_);
lean_ctor_set(v___x_1725_, 1, v_snd_1689_);
v_a_1700_ = v___x_1725_;
goto v___jp_1699_;
}
else
{
lean_object* v___x_1726_; 
lean_inc(v_cmd_1672_);
lean_inc_ref(v___x_1722_);
v___x_1726_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1722_, v_cmd_1672_);
if (lean_obj_tag(v___x_1726_) == 1)
{
lean_object* v_val_1727_; lean_object* v_fst_1728_; lean_object* v_snd_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1792_; 
lean_dec(v___x_1721_);
lean_dec(v___x_1720_);
lean_del_object(v___x_1718_);
v_val_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_val_1727_);
lean_dec_ref_known(v___x_1726_, 1);
v_fst_1728_ = lean_ctor_get(v_val_1727_, 0);
v_snd_1729_ = lean_ctor_get(v_val_1727_, 1);
v_isSharedCheck_1792_ = !lean_is_exclusive(v_val_1727_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1731_ = v_val_1727_;
v_isShared_1732_ = v_isSharedCheck_1792_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_snd_1729_);
lean_inc(v_fst_1728_);
lean_dec(v_val_1727_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1792_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; uint8_t v___y_1790_; lean_object* v___x_1791_; 
v___x_1791_ = l_Lean_Syntax_getPos_x3f(v_fst_1728_, v___x_1723_);
if (lean_obj_tag(v___x_1791_) == 0)
{
v___y_1790_ = v___x_1724_;
goto v___jp_1789_;
}
else
{
lean_dec_ref_known(v___x_1791_, 1);
v___y_1790_ = v___x_1723_;
goto v___jp_1789_;
}
v___jp_1733_:
{
lean_object* v___x_1739_; 
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 1, v_snd_1689_);
lean_ctor_set(v___x_1731_, 0, v_fst_1688_);
v___x_1739_ = v___x_1731_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_fst_1688_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_snd_1689_);
v___x_1739_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
size_t v_sz_1740_; size_t v___x_1741_; lean_object* v___x_1742_; 
v_sz_1740_ = lean_array_size(v___y_1735_);
v___x_1741_ = ((size_t)0ULL);
v___x_1742_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1722_, v_fst_1728_, v_snd_1729_, v___y_1734_, v___y_1735_, v_sz_1740_, v___x_1741_, v___x_1739_);
lean_dec_ref(v___y_1735_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v_fst_1744_; lean_object* v_snd_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_a_1743_);
lean_dec_ref_known(v___x_1742_, 1);
v_fst_1744_ = lean_ctor_get(v_a_1743_, 0);
v_snd_1745_ = lean_ctor_get(v_a_1743_, 1);
v_isSharedCheck_1752_ = !lean_is_exclusive(v_a_1743_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v_a_1743_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_snd_1745_);
lean_inc(v_fst_1744_);
lean_dec(v_a_1743_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_fst_1744_);
lean_ctor_set(v_reuseFailAlloc_1751_, 1, v_snd_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
v_a_1700_ = v___x_1750_;
goto v___jp_1699_;
}
}
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_del_object(v___x_1691_);
lean_dec(v_cmd_1672_);
v_a_1753_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1742_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1742_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
}
v___jp_1762_:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; uint8_t v___x_1767_; 
lean_inc_ref(v___x_1722_);
v___x_1763_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1722_);
v___x_1764_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1697_);
v___x_1765_ = lean_array_get_size(v___x_1764_);
v___x_1766_ = lean_unsigned_to_nat(0u);
v___x_1767_ = lean_nat_dec_eq(v___x_1765_, v___x_1766_);
if (v___x_1767_ == 0)
{
v___y_1734_ = v___x_1763_;
v___y_1735_ = v___x_1764_;
v___y_1736_ = v___y_1679_;
v___y_1737_ = v___y_1680_;
goto v___jp_1733_;
}
else
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v_scopes_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v_opts_1774_; uint8_t v_hasTrace_1775_; 
v___x_1768_ = l_Lean_inheritedTraceOptions;
v___x_1769_ = lean_st_ref_get(v___x_1768_);
v___x_1770_ = lean_st_ref_get(v___y_1680_);
v_scopes_1771_ = lean_ctor_get(v___x_1770_, 2);
lean_inc(v_scopes_1771_);
lean_dec(v___x_1770_);
v___x_1772_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1773_ = l_List_head_x21___redArg(v___x_1772_, v_scopes_1771_);
lean_dec(v_scopes_1771_);
v_opts_1774_ = lean_ctor_get(v___x_1773_, 1);
lean_inc_ref(v_opts_1774_);
lean_dec(v___x_1773_);
v_hasTrace_1775_ = lean_ctor_get_uint8(v_opts_1774_, sizeof(void*)*1);
if (v_hasTrace_1775_ == 0)
{
lean_dec_ref(v_opts_1774_);
lean_dec(v___x_1769_);
v___y_1734_ = v___x_1763_;
v___y_1735_ = v___x_1764_;
v___y_1736_ = v___y_1679_;
v___y_1737_ = v___y_1680_;
goto v___jp_1733_;
}
else
{
lean_object* v___x_1776_; lean_object* v___x_1777_; uint8_t v___x_1778_; 
v___x_1776_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1777_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1778_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1769_, v_opts_1774_, v___x_1777_);
lean_dec_ref(v_opts_1774_);
lean_dec(v___x_1769_);
if (v___x_1778_ == 0)
{
v___y_1734_ = v___x_1763_;
v___y_1735_ = v___x_1764_;
v___y_1736_ = v___y_1679_;
v___y_1737_ = v___y_1680_;
goto v___jp_1733_;
}
else
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1779_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5);
v___x_1780_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1776_, v___x_1779_, v___y_1679_, v___y_1680_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_dec_ref_known(v___x_1780_, 1);
v___y_1734_ = v___x_1763_;
v___y_1735_ = v___x_1764_;
v___y_1736_ = v___y_1679_;
v___y_1737_ = v___y_1680_;
goto v___jp_1733_;
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec_ref(v___x_1764_);
lean_dec(v___x_1763_);
lean_del_object(v___x_1731_);
lean_dec(v_snd_1729_);
lean_dec(v_fst_1728_);
lean_dec_ref_known(v___x_1722_, 2);
lean_del_object(v___x_1691_);
lean_dec(v_snd_1689_);
lean_dec(v_fst_1688_);
lean_dec(v_cmd_1672_);
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1780_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1780_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
}
}
}
v___jp_1789_:
{
if (v_onUnsolved_1673_ == 0)
{
if (v___y_1674_ == 0)
{
lean_del_object(v___x_1731_);
lean_dec(v_snd_1729_);
lean_dec(v_fst_1728_);
lean_dec_ref_known(v___x_1722_, 2);
goto v___jp_1707_;
}
else
{
if (v___y_1790_ == 0)
{
lean_del_object(v___x_1731_);
lean_dec(v_snd_1729_);
lean_dec(v_fst_1728_);
lean_dec_ref_known(v___x_1722_, 2);
goto v___jp_1707_;
}
else
{
lean_del_object(v___x_1686_);
goto v___jp_1762_;
}
}
}
else
{
lean_del_object(v___x_1686_);
goto v___jp_1762_;
}
}
}
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v_scopes_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v_opts_1799_; uint8_t v_hasTrace_1800_; 
lean_dec(v___x_1726_);
lean_dec_ref_known(v___x_1722_, 2);
lean_del_object(v___x_1686_);
v___x_1793_ = l_Lean_inheritedTraceOptions;
v___x_1794_ = lean_st_ref_get(v___x_1793_);
v___x_1795_ = lean_st_ref_get(v___y_1680_);
v_scopes_1796_ = lean_ctor_get(v___x_1795_, 2);
lean_inc(v_scopes_1796_);
lean_dec(v___x_1795_);
v___x_1797_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1798_ = l_List_head_x21___redArg(v___x_1797_, v_scopes_1796_);
lean_dec(v_scopes_1796_);
v_opts_1799_ = lean_ctor_get(v___x_1798_, 1);
lean_inc_ref(v_opts_1799_);
lean_dec(v___x_1798_);
v_hasTrace_1800_ = lean_ctor_get_uint8(v_opts_1799_, sizeof(void*)*1);
if (v_hasTrace_1800_ == 0)
{
lean_dec_ref(v_opts_1799_);
lean_dec(v___x_1794_);
lean_dec(v___x_1721_);
lean_dec(v___x_1720_);
lean_del_object(v___x_1718_);
goto v___jp_1711_;
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1801_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1802_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1803_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1794_, v_opts_1799_, v___x_1802_);
lean_dec_ref(v_opts_1799_);
lean_dec(v___x_1794_);
if (v___x_1803_ == 0)
{
lean_dec(v___x_1721_);
lean_dec(v___x_1720_);
lean_del_object(v___x_1718_);
goto v___jp_1711_;
}
else
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1807_; 
v___x_1804_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7);
v___x_1805_ = l_Nat_reprFast(v___x_1720_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set_tag(v___x_1718_, 3);
lean_ctor_set(v___x_1718_, 0, v___x_1805_);
v___x_1807_ = v___x_1718_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1805_);
v___x_1807_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1808_ = l_Lean_MessageData_ofFormat(v___x_1807_);
v___x_1809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1804_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
v___x_1810_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9);
v___x_1811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1809_);
lean_ctor_set(v___x_1811_, 1, v___x_1810_);
v___x_1812_ = l_Nat_reprFast(v___x_1721_);
v___x_1813_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
v___x_1814_ = l_Lean_MessageData_ofFormat(v___x_1813_);
v___x_1815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1811_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
v___x_1816_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11);
v___x_1817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1815_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
v___x_1818_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1801_, v___x_1817_, v___y_1679_, v___y_1680_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_dec_ref_known(v___x_1818_, 1);
goto v___jp_1711_;
}
else
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
lean_del_object(v___x_1691_);
lean_dec(v_snd_1689_);
lean_dec(v_fst_1688_);
lean_dec(v_cmd_1672_);
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1818_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1818_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
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
lean_object* v___x_1829_; 
lean_dec(v_endPos_1695_);
lean_del_object(v___x_1686_);
v___x_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1829_, 0, v_fst_1688_);
lean_ctor_set(v___x_1829_, 1, v_snd_1689_);
v_a_1700_ = v___x_1829_;
goto v___jp_1699_;
}
}
}
else
{
lean_object* v___x_1830_; 
lean_dec(v_endPos_1695_);
lean_del_object(v___x_1686_);
v___x_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1830_, 0, v_fst_1688_);
lean_ctor_set(v___x_1830_, 1, v_snd_1689_);
v_a_1700_ = v___x_1830_;
goto v___jp_1699_;
}
v___jp_1699_:
{
lean_object* v___x_1702_; 
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 1, v_a_1700_);
lean_ctor_set(v___x_1691_, 0, v___x_1698_);
v___x_1702_ = v___x_1691_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1698_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_a_1700_);
v___x_1702_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
size_t v___x_1703_; size_t v___x_1704_; 
v___x_1703_ = ((size_t)1ULL);
v___x_1704_ = lean_usize_add(v_i_1677_, v___x_1703_);
v_i_1677_ = v___x_1704_;
v_b_1678_ = v___x_1702_;
goto _start;
}
}
v___jp_1707_:
{
lean_object* v___x_1709_; 
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 1, v_snd_1689_);
lean_ctor_set(v___x_1686_, 0, v_fst_1688_);
v___x_1709_ = v___x_1686_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_fst_1688_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v_snd_1689_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
v_a_1700_ = v___x_1709_;
goto v___jp_1699_;
}
}
v___jp_1711_:
{
lean_object* v___x_1712_; 
v___x_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1712_, 0, v_fst_1688_);
lean_ctor_set(v___x_1712_, 1, v_snd_1689_);
v_a_1700_ = v___x_1712_;
goto v___jp_1699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10_spec__12___boxed(lean_object* v___x_1834_, lean_object* v_val_1835_, lean_object* v_cmd_1836_, lean_object* v_onUnsolved_1837_, lean_object* v___y_1838_, lean_object* v_as_1839_, lean_object* v_sz_1840_, lean_object* v_i_1841_, lean_object* v_b_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
uint8_t v_onUnsolved_boxed_1846_; uint8_t v___y_12597__boxed_1847_; size_t v_sz_boxed_1848_; size_t v_i_boxed_1849_; lean_object* v_res_1850_; 
v_onUnsolved_boxed_1846_ = lean_unbox(v_onUnsolved_1837_);
v___y_12597__boxed_1847_ = lean_unbox(v___y_1838_);
v_sz_boxed_1848_ = lean_unbox_usize(v_sz_1840_);
lean_dec(v_sz_1840_);
v_i_boxed_1849_ = lean_unbox_usize(v_i_1841_);
lean_dec(v_i_1841_);
v_res_1850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10_spec__12(v___x_1834_, v_val_1835_, v_cmd_1836_, v_onUnsolved_boxed_1846_, v___y_12597__boxed_1847_, v_as_1839_, v_sz_boxed_1848_, v_i_boxed_1849_, v_b_1842_, v___y_1843_, v___y_1844_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec_ref(v_as_1839_);
lean_dec_ref(v_val_1835_);
lean_dec_ref(v___x_1834_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10(lean_object* v___x_1851_, lean_object* v_val_1852_, lean_object* v_cmd_1853_, uint8_t v_onUnsolved_1854_, uint8_t v___y_1855_, lean_object* v_as_1856_, size_t v_sz_1857_, size_t v_i_1858_, lean_object* v_b_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
uint8_t v___x_1863_; 
v___x_1863_ = lean_usize_dec_lt(v_i_1858_, v_sz_1857_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; 
lean_dec(v_cmd_1853_);
v___x_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1864_, 0, v_b_1859_);
return v___x_1864_;
}
else
{
lean_object* v_snd_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_2013_; 
v_snd_1865_ = lean_ctor_get(v_b_1859_, 1);
v_isSharedCheck_2013_ = !lean_is_exclusive(v_b_1859_);
if (v_isSharedCheck_2013_ == 0)
{
lean_object* v_unused_2014_; 
v_unused_2014_ = lean_ctor_get(v_b_1859_, 0);
lean_dec(v_unused_2014_);
v___x_1867_ = v_b_1859_;
v_isShared_1868_ = v_isSharedCheck_2013_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_snd_1865_);
lean_dec(v_b_1859_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_2013_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v_fst_1869_; lean_object* v_snd_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_2012_; 
v_fst_1869_ = lean_ctor_get(v_snd_1865_, 0);
v_snd_1870_ = lean_ctor_get(v_snd_1865_, 1);
v_isSharedCheck_2012_ = !lean_is_exclusive(v_snd_1865_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_1872_ = v_snd_1865_;
v_isShared_1873_ = v_isSharedCheck_2012_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_snd_1870_);
lean_inc(v_fst_1869_);
lean_dec(v_snd_1865_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_2012_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v_a_1874_; lean_object* v_pos_1875_; lean_object* v_endPos_1876_; uint8_t v_severity_1877_; lean_object* v_data_1878_; lean_object* v___x_1879_; lean_object* v_a_1881_; 
v_a_1874_ = lean_array_uget_borrowed(v_as_1856_, v_i_1858_);
v_pos_1875_ = lean_ctor_get(v_a_1874_, 1);
v_endPos_1876_ = lean_ctor_get(v_a_1874_, 2);
lean_inc(v_endPos_1876_);
v_severity_1877_ = lean_ctor_get_uint8(v_a_1874_, sizeof(void*)*5 + 1);
v_data_1878_ = lean_ctor_get(v_a_1874_, 4);
v___x_1879_ = lean_box(0);
if (v_severity_1877_ == 2)
{
lean_object* v___f_1894_; uint8_t v___x_1895_; 
v___f_1894_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
lean_inc(v_data_1878_);
v___x_1895_ = l_Lean_MessageData_hasTag(v___f_1894_, v_data_1878_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; 
lean_dec(v_endPos_1876_);
lean_del_object(v___x_1867_);
v___x_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1896_, 0, v_fst_1869_);
lean_ctor_set(v___x_1896_, 1, v_snd_1870_);
v_a_1881_ = v___x_1896_;
goto v___jp_1880_;
}
else
{
if (lean_obj_tag(v_endPos_1876_) == 1)
{
lean_object* v_val_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_2009_; 
v_val_1897_ = lean_ctor_get(v_endPos_1876_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_endPos_1876_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_1899_ = v_endPos_1876_;
v_isShared_1900_ = v_isSharedCheck_2009_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_val_1897_);
lean_dec(v_endPos_1876_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_2009_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; uint8_t v___x_1904_; uint8_t v___x_1905_; 
lean_inc_ref(v_pos_1875_);
v___x_1901_ = l_Lean_FileMap_ofPosition(v___x_1851_, v_pos_1875_);
v___x_1902_ = l_Lean_FileMap_ofPosition(v___x_1851_, v_val_1897_);
lean_inc(v___x_1902_);
lean_inc(v___x_1901_);
v___x_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1901_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = 0;
v___x_1905_ = l_Lean_Syntax_Range_includes(v_val_1852_, v___x_1903_, v___x_1904_, v___x_1904_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; 
lean_dec_ref_known(v___x_1903_, 2);
lean_dec(v___x_1902_);
lean_dec(v___x_1901_);
lean_del_object(v___x_1899_);
lean_del_object(v___x_1867_);
v___x_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1906_, 0, v_fst_1869_);
lean_ctor_set(v___x_1906_, 1, v_snd_1870_);
v_a_1881_ = v___x_1906_;
goto v___jp_1880_;
}
else
{
lean_object* v___x_1907_; 
lean_inc(v_cmd_1853_);
lean_inc_ref(v___x_1903_);
v___x_1907_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1903_, v_cmd_1853_);
if (lean_obj_tag(v___x_1907_) == 1)
{
lean_object* v_val_1908_; lean_object* v_fst_1909_; lean_object* v_snd_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1973_; 
lean_dec(v___x_1902_);
lean_dec(v___x_1901_);
lean_del_object(v___x_1899_);
v_val_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_val_1908_);
lean_dec_ref_known(v___x_1907_, 1);
v_fst_1909_ = lean_ctor_get(v_val_1908_, 0);
v_snd_1910_ = lean_ctor_get(v_val_1908_, 1);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_val_1908_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1912_ = v_val_1908_;
v_isShared_1913_ = v_isSharedCheck_1973_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_snd_1910_);
lean_inc(v_fst_1909_);
lean_dec(v_val_1908_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1973_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; uint8_t v___y_1971_; lean_object* v___x_1972_; 
v___x_1972_ = l_Lean_Syntax_getPos_x3f(v_fst_1909_, v___x_1904_);
if (lean_obj_tag(v___x_1972_) == 0)
{
v___y_1971_ = v___x_1905_;
goto v___jp_1970_;
}
else
{
lean_dec_ref_known(v___x_1972_, 1);
v___y_1971_ = v___x_1904_;
goto v___jp_1970_;
}
v___jp_1914_:
{
lean_object* v___x_1920_; 
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 1, v_snd_1870_);
lean_ctor_set(v___x_1912_, 0, v_fst_1869_);
v___x_1920_ = v___x_1912_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_fst_1869_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v_snd_1870_);
v___x_1920_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
size_t v_sz_1921_; size_t v___x_1922_; lean_object* v___x_1923_; 
v_sz_1921_ = lean_array_size(v___y_1915_);
v___x_1922_ = ((size_t)0ULL);
v___x_1923_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_1903_, v_fst_1909_, v_snd_1910_, v___y_1916_, v___y_1915_, v_sz_1921_, v___x_1922_, v___x_1920_);
lean_dec_ref(v___y_1915_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v_fst_1925_; lean_object* v_snd_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1923_, 1);
v_fst_1925_ = lean_ctor_get(v_a_1924_, 0);
v_snd_1926_ = lean_ctor_get(v_a_1924_, 1);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_a_1924_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v_a_1924_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_snd_1926_);
lean_inc(v_fst_1925_);
lean_dec(v_a_1924_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_fst_1925_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_snd_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
v_a_1881_ = v___x_1931_;
goto v___jp_1880_;
}
}
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
lean_del_object(v___x_1872_);
lean_dec(v_cmd_1853_);
v_a_1934_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1923_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1923_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
}
v___jp_1943_:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; uint8_t v___x_1948_; 
lean_inc_ref(v___x_1903_);
v___x_1944_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1903_);
v___x_1945_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1878_);
v___x_1946_ = lean_array_get_size(v___x_1945_);
v___x_1947_ = lean_unsigned_to_nat(0u);
v___x_1948_ = lean_nat_dec_eq(v___x_1946_, v___x_1947_);
if (v___x_1948_ == 0)
{
v___y_1915_ = v___x_1945_;
v___y_1916_ = v___x_1944_;
v___y_1917_ = v___y_1860_;
v___y_1918_ = v___y_1861_;
goto v___jp_1914_;
}
else
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v_scopes_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v_opts_1955_; uint8_t v_hasTrace_1956_; 
v___x_1949_ = l_Lean_inheritedTraceOptions;
v___x_1950_ = lean_st_ref_get(v___x_1949_);
v___x_1951_ = lean_st_ref_get(v___y_1861_);
v_scopes_1952_ = lean_ctor_get(v___x_1951_, 2);
lean_inc(v_scopes_1952_);
lean_dec(v___x_1951_);
v___x_1953_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1954_ = l_List_head_x21___redArg(v___x_1953_, v_scopes_1952_);
lean_dec(v_scopes_1952_);
v_opts_1955_ = lean_ctor_get(v___x_1954_, 1);
lean_inc_ref(v_opts_1955_);
lean_dec(v___x_1954_);
v_hasTrace_1956_ = lean_ctor_get_uint8(v_opts_1955_, sizeof(void*)*1);
if (v_hasTrace_1956_ == 0)
{
lean_dec_ref(v_opts_1955_);
lean_dec(v___x_1950_);
v___y_1915_ = v___x_1945_;
v___y_1916_ = v___x_1944_;
v___y_1917_ = v___y_1860_;
v___y_1918_ = v___y_1861_;
goto v___jp_1914_;
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; 
v___x_1957_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1958_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1959_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1950_, v_opts_1955_, v___x_1958_);
lean_dec_ref(v_opts_1955_);
lean_dec(v___x_1950_);
if (v___x_1959_ == 0)
{
v___y_1915_ = v___x_1945_;
v___y_1916_ = v___x_1944_;
v___y_1917_ = v___y_1860_;
v___y_1918_ = v___y_1861_;
goto v___jp_1914_;
}
else
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__5);
v___x_1961_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1957_, v___x_1960_, v___y_1860_, v___y_1861_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_dec_ref_known(v___x_1961_, 1);
v___y_1915_ = v___x_1945_;
v___y_1916_ = v___x_1944_;
v___y_1917_ = v___y_1860_;
v___y_1918_ = v___y_1861_;
goto v___jp_1914_;
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec_ref(v___x_1945_);
lean_dec(v___x_1944_);
lean_del_object(v___x_1912_);
lean_dec(v_snd_1910_);
lean_dec(v_fst_1909_);
lean_dec_ref_known(v___x_1903_, 2);
lean_del_object(v___x_1872_);
lean_dec(v_snd_1870_);
lean_dec(v_fst_1869_);
lean_dec(v_cmd_1853_);
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1961_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1961_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
}
}
}
v___jp_1970_:
{
if (v_onUnsolved_1854_ == 0)
{
if (v___y_1855_ == 0)
{
lean_del_object(v___x_1912_);
lean_dec(v_snd_1910_);
lean_dec(v_fst_1909_);
lean_dec_ref_known(v___x_1903_, 2);
goto v___jp_1888_;
}
else
{
if (v___y_1971_ == 0)
{
lean_del_object(v___x_1912_);
lean_dec(v_snd_1910_);
lean_dec(v_fst_1909_);
lean_dec_ref_known(v___x_1903_, 2);
goto v___jp_1888_;
}
else
{
lean_del_object(v___x_1867_);
goto v___jp_1943_;
}
}
}
else
{
lean_del_object(v___x_1867_);
goto v___jp_1943_;
}
}
}
}
else
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v_scopes_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v_opts_1980_; uint8_t v_hasTrace_1981_; 
lean_dec(v___x_1907_);
lean_dec_ref_known(v___x_1903_, 2);
lean_del_object(v___x_1867_);
v___x_1974_ = l_Lean_inheritedTraceOptions;
v___x_1975_ = lean_st_ref_get(v___x_1974_);
v___x_1976_ = lean_st_ref_get(v___y_1861_);
v_scopes_1977_ = lean_ctor_get(v___x_1976_, 2);
lean_inc(v_scopes_1977_);
lean_dec(v___x_1976_);
v___x_1978_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1979_ = l_List_head_x21___redArg(v___x_1978_, v_scopes_1977_);
lean_dec(v_scopes_1977_);
v_opts_1980_ = lean_ctor_get(v___x_1979_, 1);
lean_inc_ref(v_opts_1980_);
lean_dec(v___x_1979_);
v_hasTrace_1981_ = lean_ctor_get_uint8(v_opts_1980_, sizeof(void*)*1);
if (v_hasTrace_1981_ == 0)
{
lean_dec_ref(v_opts_1980_);
lean_dec(v___x_1975_);
lean_dec(v___x_1902_);
lean_dec(v___x_1901_);
lean_del_object(v___x_1899_);
goto v___jp_1892_;
}
else
{
lean_object* v___x_1982_; lean_object* v___x_1983_; uint8_t v___x_1984_; 
v___x_1982_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1983_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_1984_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1975_, v_opts_1980_, v___x_1983_);
lean_dec_ref(v_opts_1980_);
lean_dec(v___x_1975_);
if (v___x_1984_ == 0)
{
lean_dec(v___x_1902_);
lean_dec(v___x_1901_);
lean_del_object(v___x_1899_);
goto v___jp_1892_;
}
else
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1988_; 
v___x_1985_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__7);
v___x_1986_ = l_Nat_reprFast(v___x_1901_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set_tag(v___x_1899_, 3);
lean_ctor_set(v___x_1899_, 0, v___x_1986_);
v___x_1988_ = v___x_1899_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_1986_);
v___x_1988_ = v_reuseFailAlloc_2008_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1989_ = l_Lean_MessageData_ofFormat(v___x_1988_);
v___x_1990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1985_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
v___x_1991_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__9);
v___x_1992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1990_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
v___x_1993_ = l_Nat_reprFast(v___x_1902_);
v___x_1994_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1993_);
v___x_1995_ = l_Lean_MessageData_ofFormat(v___x_1994_);
v___x_1996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1992_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
v___x_1997_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__11);
v___x_1998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1996_);
lean_ctor_set(v___x_1998_, 1, v___x_1997_);
v___x_1999_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_1982_, v___x_1998_, v___y_1860_, v___y_1861_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_dec_ref_known(v___x_1999_, 1);
goto v___jp_1892_;
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_del_object(v___x_1872_);
lean_dec(v_snd_1870_);
lean_dec(v_fst_1869_);
lean_dec(v_cmd_1853_);
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1999_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1999_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
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
lean_object* v___x_2010_; 
lean_dec(v_endPos_1876_);
lean_del_object(v___x_1867_);
v___x_2010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2010_, 0, v_fst_1869_);
lean_ctor_set(v___x_2010_, 1, v_snd_1870_);
v_a_1881_ = v___x_2010_;
goto v___jp_1880_;
}
}
}
else
{
lean_object* v___x_2011_; 
lean_dec(v_endPos_1876_);
lean_del_object(v___x_1867_);
v___x_2011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2011_, 0, v_fst_1869_);
lean_ctor_set(v___x_2011_, 1, v_snd_1870_);
v_a_1881_ = v___x_2011_;
goto v___jp_1880_;
}
v___jp_1880_:
{
lean_object* v___x_1883_; 
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 1, v_a_1881_);
lean_ctor_set(v___x_1872_, 0, v___x_1879_);
v___x_1883_ = v___x_1872_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1879_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v_a_1881_);
v___x_1883_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
size_t v___x_1884_; size_t v___x_1885_; lean_object* v___x_1886_; 
v___x_1884_ = ((size_t)1ULL);
v___x_1885_ = lean_usize_add(v_i_1858_, v___x_1884_);
v___x_1886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10_spec__12(v___x_1851_, v_val_1852_, v_cmd_1853_, v_onUnsolved_1854_, v___y_1855_, v_as_1856_, v_sz_1857_, v___x_1885_, v___x_1883_, v___y_1860_, v___y_1861_);
return v___x_1886_;
}
}
v___jp_1888_:
{
lean_object* v___x_1890_; 
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 1, v_snd_1870_);
lean_ctor_set(v___x_1867_, 0, v_fst_1869_);
v___x_1890_ = v___x_1867_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_fst_1869_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_snd_1870_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
v_a_1881_ = v___x_1890_;
goto v___jp_1880_;
}
}
v___jp_1892_:
{
lean_object* v___x_1893_; 
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v_fst_1869_);
lean_ctor_set(v___x_1893_, 1, v_snd_1870_);
v_a_1881_ = v___x_1893_;
goto v___jp_1880_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10___boxed(lean_object* v___x_2015_, lean_object* v_val_2016_, lean_object* v_cmd_2017_, lean_object* v_onUnsolved_2018_, lean_object* v___y_2019_, lean_object* v_as_2020_, lean_object* v_sz_2021_, lean_object* v_i_2022_, lean_object* v_b_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
uint8_t v_onUnsolved_boxed_2027_; uint8_t v___y_12929__boxed_2028_; size_t v_sz_boxed_2029_; size_t v_i_boxed_2030_; lean_object* v_res_2031_; 
v_onUnsolved_boxed_2027_ = lean_unbox(v_onUnsolved_2018_);
v___y_12929__boxed_2028_ = lean_unbox(v___y_2019_);
v_sz_boxed_2029_ = lean_unbox_usize(v_sz_2021_);
lean_dec(v_sz_2021_);
v_i_boxed_2030_ = lean_unbox_usize(v_i_2022_);
lean_dec(v_i_2022_);
v_res_2031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10(v___x_2015_, v_val_2016_, v_cmd_2017_, v_onUnsolved_boxed_2027_, v___y_12929__boxed_2028_, v_as_2020_, v_sz_boxed_2029_, v_i_boxed_2030_, v_b_2023_, v___y_2024_, v___y_2025_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec_ref(v_as_2020_);
lean_dec_ref(v_val_2016_);
lean_dec_ref(v___x_2015_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(lean_object* v_init_2032_, lean_object* v___x_2033_, lean_object* v_val_2034_, lean_object* v_cmd_2035_, uint8_t v_onUnsolved_2036_, uint8_t v___y_2037_, lean_object* v_n_2038_, lean_object* v_b_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
if (lean_obj_tag(v_n_2038_) == 0)
{
lean_object* v_cs_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; size_t v_sz_2046_; size_t v___x_2047_; lean_object* v___x_2048_; 
v_cs_2043_ = lean_ctor_get(v_n_2038_, 0);
v___x_2044_ = lean_box(0);
v___x_2045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2044_);
lean_ctor_set(v___x_2045_, 1, v_b_2039_);
v_sz_2046_ = lean_array_size(v_cs_2043_);
v___x_2047_ = ((size_t)0ULL);
v___x_2048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__9(v_init_2032_, v___x_2033_, v_val_2034_, v_cmd_2035_, v_onUnsolved_2036_, v___y_2037_, v_cs_2043_, v_sz_2046_, v___x_2047_, v___x_2045_, v___y_2040_, v___y_2041_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2063_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2051_ = v___x_2048_;
v_isShared_2052_ = v_isSharedCheck_2063_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2048_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2063_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v_fst_2053_; 
v_fst_2053_ = lean_ctor_get(v_a_2049_, 0);
if (lean_obj_tag(v_fst_2053_) == 0)
{
lean_object* v_snd_2054_; lean_object* v___x_2055_; lean_object* v___x_2057_; 
v_snd_2054_ = lean_ctor_get(v_a_2049_, 1);
lean_inc(v_snd_2054_);
lean_dec(v_a_2049_);
v___x_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2055_, 0, v_snd_2054_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 0, v___x_2055_);
v___x_2057_ = v___x_2051_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v___x_2055_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
else
{
lean_object* v_val_2059_; lean_object* v___x_2061_; 
lean_inc_ref(v_fst_2053_);
lean_dec(v_a_2049_);
v_val_2059_ = lean_ctor_get(v_fst_2053_, 0);
lean_inc(v_val_2059_);
lean_dec_ref_known(v_fst_2053_, 1);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 0, v_val_2059_);
v___x_2061_ = v___x_2051_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_val_2059_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
v_a_2064_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2048_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2048_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
else
{
lean_object* v_vs_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; size_t v_sz_2075_; size_t v___x_2076_; lean_object* v___x_2077_; 
v_vs_2072_ = lean_ctor_get(v_n_2038_, 0);
v___x_2073_ = lean_box(0);
v___x_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2073_);
lean_ctor_set(v___x_2074_, 1, v_b_2039_);
v_sz_2075_ = lean_array_size(v_vs_2072_);
v___x_2076_ = ((size_t)0ULL);
v___x_2077_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__10(v___x_2033_, v_val_2034_, v_cmd_2035_, v_onUnsolved_2036_, v___y_2037_, v_vs_2072_, v_sz_2075_, v___x_2076_, v___x_2074_, v___y_2040_, v___y_2041_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2092_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2080_ = v___x_2077_;
v_isShared_2081_ = v_isSharedCheck_2092_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2077_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2092_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v_fst_2082_; 
v_fst_2082_ = lean_ctor_get(v_a_2078_, 0);
if (lean_obj_tag(v_fst_2082_) == 0)
{
lean_object* v_snd_2083_; lean_object* v___x_2084_; lean_object* v___x_2086_; 
v_snd_2083_ = lean_ctor_get(v_a_2078_, 1);
lean_inc(v_snd_2083_);
lean_dec(v_a_2078_);
v___x_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2084_, 0, v_snd_2083_);
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 0, v___x_2084_);
v___x_2086_ = v___x_2080_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
else
{
lean_object* v_val_2088_; lean_object* v___x_2090_; 
lean_inc_ref(v_fst_2082_);
lean_dec(v_a_2078_);
v_val_2088_ = lean_ctor_get(v_fst_2082_, 0);
lean_inc(v_val_2088_);
lean_dec_ref_known(v_fst_2082_, 1);
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 0, v_val_2088_);
v___x_2090_ = v___x_2080_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_val_2088_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
else
{
lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2100_; 
v_a_2093_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2095_ = v___x_2077_;
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_2077_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_a_2093_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__9(lean_object* v_init_2101_, lean_object* v___x_2102_, lean_object* v_val_2103_, lean_object* v_cmd_2104_, uint8_t v_onUnsolved_2105_, uint8_t v___y_2106_, lean_object* v_as_2107_, size_t v_sz_2108_, size_t v_i_2109_, lean_object* v_b_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
uint8_t v___x_2114_; 
v___x_2114_ = lean_usize_dec_lt(v_i_2109_, v_sz_2108_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2115_; 
lean_dec(v_cmd_2104_);
v___x_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2115_, 0, v_b_2110_);
return v___x_2115_;
}
else
{
lean_object* v_snd_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2150_; 
v_snd_2116_ = lean_ctor_get(v_b_2110_, 1);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_b_2110_);
if (v_isSharedCheck_2150_ == 0)
{
lean_object* v_unused_2151_; 
v_unused_2151_ = lean_ctor_get(v_b_2110_, 0);
lean_dec(v_unused_2151_);
v___x_2118_ = v_b_2110_;
v_isShared_2119_ = v_isSharedCheck_2150_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_snd_2116_);
lean_dec(v_b_2110_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2150_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v_a_2120_; lean_object* v___x_2121_; 
v_a_2120_ = lean_array_uget_borrowed(v_as_2107_, v_i_2109_);
lean_inc(v_snd_2116_);
lean_inc(v_cmd_2104_);
v___x_2121_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(v_init_2101_, v___x_2102_, v_val_2103_, v_cmd_2104_, v_onUnsolved_2105_, v___y_2106_, v_a_2120_, v_snd_2116_, v___y_2111_, v___y_2112_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2141_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2124_ = v___x_2121_;
v_isShared_2125_ = v_isSharedCheck_2141_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2121_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2141_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
if (lean_obj_tag(v_a_2122_) == 0)
{
lean_object* v___x_2126_; lean_object* v___x_2128_; 
lean_dec(v_cmd_2104_);
v___x_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2126_, 0, v_a_2122_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2126_);
v___x_2128_ = v___x_2118_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2126_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v_snd_2116_);
v___x_2128_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v___x_2130_; 
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2128_);
v___x_2130_ = v___x_2124_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2128_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2134_; lean_object* v___x_2136_; 
lean_del_object(v___x_2124_);
lean_dec(v_snd_2116_);
v_a_2133_ = lean_ctor_get(v_a_2122_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v_a_2122_, 1);
v___x_2134_ = lean_box(0);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 1, v_a_2133_);
lean_ctor_set(v___x_2118_, 0, v___x_2134_);
v___x_2136_ = v___x_2118_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2134_);
lean_ctor_set(v_reuseFailAlloc_2140_, 1, v_a_2133_);
v___x_2136_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
size_t v___x_2137_; size_t v___x_2138_; 
v___x_2137_ = ((size_t)1ULL);
v___x_2138_ = lean_usize_add(v_i_2109_, v___x_2137_);
v_i_2109_ = v___x_2138_;
v_b_2110_ = v___x_2136_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_del_object(v___x_2118_);
lean_dec(v_snd_2116_);
lean_dec(v_cmd_2104_);
v_a_2142_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2121_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2121_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__9___boxed(lean_object* v_init_2152_, lean_object* v___x_2153_, lean_object* v_val_2154_, lean_object* v_cmd_2155_, lean_object* v_onUnsolved_2156_, lean_object* v___y_2157_, lean_object* v_as_2158_, lean_object* v_sz_2159_, lean_object* v_i_2160_, lean_object* v_b_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
uint8_t v_onUnsolved_boxed_2165_; uint8_t v___y_13230__boxed_2166_; size_t v_sz_boxed_2167_; size_t v_i_boxed_2168_; lean_object* v_res_2169_; 
v_onUnsolved_boxed_2165_ = lean_unbox(v_onUnsolved_2156_);
v___y_13230__boxed_2166_ = lean_unbox(v___y_2157_);
v_sz_boxed_2167_ = lean_unbox_usize(v_sz_2159_);
lean_dec(v_sz_2159_);
v_i_boxed_2168_ = lean_unbox_usize(v_i_2160_);
lean_dec(v_i_2160_);
v_res_2169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7_spec__9(v_init_2152_, v___x_2153_, v_val_2154_, v_cmd_2155_, v_onUnsolved_boxed_2165_, v___y_13230__boxed_2166_, v_as_2158_, v_sz_boxed_2167_, v_i_boxed_2168_, v_b_2161_, v___y_2162_, v___y_2163_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec_ref(v_as_2158_);
lean_dec_ref(v_val_2154_);
lean_dec_ref(v___x_2153_);
lean_dec_ref(v_init_2152_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7___boxed(lean_object* v_init_2170_, lean_object* v___x_2171_, lean_object* v_val_2172_, lean_object* v_cmd_2173_, lean_object* v_onUnsolved_2174_, lean_object* v___y_2175_, lean_object* v_n_2176_, lean_object* v_b_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
uint8_t v_onUnsolved_boxed_2181_; uint8_t v___y_13252__boxed_2182_; lean_object* v_res_2183_; 
v_onUnsolved_boxed_2181_ = lean_unbox(v_onUnsolved_2174_);
v___y_13252__boxed_2182_ = lean_unbox(v___y_2175_);
v_res_2183_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(v_init_2170_, v___x_2171_, v_val_2172_, v_cmd_2173_, v_onUnsolved_boxed_2181_, v___y_13252__boxed_2182_, v_n_2176_, v_b_2177_, v___y_2178_, v___y_2179_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec_ref(v_n_2176_);
lean_dec_ref(v_val_2172_);
lean_dec_ref(v___x_2171_);
lean_dec_ref(v_init_2170_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(lean_object* v___x_2184_, lean_object* v_val_2185_, lean_object* v_cmd_2186_, uint8_t v_onUnsolved_2187_, uint8_t v___y_2188_, lean_object* v_t_2189_, lean_object* v_init_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v_root_2194_; lean_object* v_tail_2195_; lean_object* v___x_2196_; 
v_root_2194_ = lean_ctor_get(v_t_2189_, 0);
v_tail_2195_ = lean_ctor_get(v_t_2189_, 1);
lean_inc(v_cmd_2186_);
lean_inc_ref(v_init_2190_);
v___x_2196_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__7(v_init_2190_, v___x_2184_, v_val_2185_, v_cmd_2186_, v_onUnsolved_2187_, v___y_2188_, v_root_2194_, v_init_2190_, v___y_2191_, v___y_2192_);
lean_dec_ref(v_init_2190_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2233_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2199_ = v___x_2196_;
v_isShared_2200_ = v_isSharedCheck_2233_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2196_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2233_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
if (lean_obj_tag(v_a_2197_) == 0)
{
lean_object* v_a_2201_; lean_object* v___x_2203_; 
lean_dec(v_cmd_2186_);
v_a_2201_ = lean_ctor_get(v_a_2197_, 0);
lean_inc(v_a_2201_);
lean_dec_ref_known(v_a_2197_, 1);
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 0, v_a_2201_);
v___x_2203_ = v___x_2199_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2201_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; size_t v_sz_2208_; size_t v___x_2209_; lean_object* v___x_2210_; 
lean_del_object(v___x_2199_);
v_a_2205_ = lean_ctor_get(v_a_2197_, 0);
lean_inc(v_a_2205_);
lean_dec_ref_known(v_a_2197_, 1);
v___x_2206_ = lean_box(0);
v___x_2207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
lean_ctor_set(v___x_2207_, 1, v_a_2205_);
v_sz_2208_ = lean_array_size(v_tail_2195_);
v___x_2209_ = ((size_t)0ULL);
v___x_2210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8(v___x_2184_, v_val_2185_, v_cmd_2186_, v_onUnsolved_2187_, v___y_2188_, v_tail_2195_, v_sz_2208_, v___x_2209_, v___x_2207_, v___y_2191_, v___y_2192_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2224_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2213_ = v___x_2210_;
v_isShared_2214_ = v_isSharedCheck_2224_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2210_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2224_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v_fst_2215_; 
v_fst_2215_ = lean_ctor_get(v_a_2211_, 0);
if (lean_obj_tag(v_fst_2215_) == 0)
{
lean_object* v_snd_2216_; lean_object* v___x_2218_; 
v_snd_2216_ = lean_ctor_get(v_a_2211_, 1);
lean_inc(v_snd_2216_);
lean_dec(v_a_2211_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 0, v_snd_2216_);
v___x_2218_ = v___x_2213_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_snd_2216_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
else
{
lean_object* v_val_2220_; lean_object* v___x_2222_; 
lean_inc_ref(v_fst_2215_);
lean_dec(v_a_2211_);
v_val_2220_ = lean_ctor_get(v_fst_2215_, 0);
lean_inc(v_val_2220_);
lean_dec_ref_known(v_fst_2215_, 1);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 0, v_val_2220_);
v___x_2222_ = v___x_2213_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_val_2220_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
v_a_2225_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2210_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2210_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
}
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
lean_dec(v_cmd_2186_);
v_a_2234_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2196_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2196_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___boxed(lean_object* v___x_2242_, lean_object* v_val_2243_, lean_object* v_cmd_2244_, lean_object* v_onUnsolved_2245_, lean_object* v___y_2246_, lean_object* v_t_2247_, lean_object* v_init_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
uint8_t v_onUnsolved_boxed_2252_; uint8_t v___y_13443__boxed_2253_; lean_object* v_res_2254_; 
v_onUnsolved_boxed_2252_ = lean_unbox(v_onUnsolved_2245_);
v___y_13443__boxed_2253_ = lean_unbox(v___y_2246_);
v_res_2254_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_2242_, v_val_2243_, v_cmd_2244_, v_onUnsolved_boxed_2252_, v___y_13443__boxed_2253_, v_t_2247_, v_init_2248_, v___y_2249_, v___y_2250_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec_ref(v_t_2247_);
lean_dec_ref(v_val_2243_);
lean_dec_ref(v___x_2242_);
return v_res_2254_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0(void){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2255_ = lean_box(0);
v___x_2256_ = lean_unsigned_to_nat(16u);
v___x_2257_ = lean_mk_array(v___x_2256_, v___x_2255_);
return v___x_2257_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1(void){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2258_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0);
v___x_2259_ = lean_unsigned_to_nat(0u);
v___x_2260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
lean_ctor_set(v___x_2260_, 1, v___x_2258_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(lean_object* v_cmd_2264_, lean_object* v_opts_2265_, lean_object* v_tree_2266_, lean_object* v_msgs_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
uint8_t v___y_2272_; lean_object* v___y_2273_; uint8_t v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; uint8_t v___y_2277_; uint8_t v___y_2303_; uint8_t v___y_2304_; lean_object* v_acc_2305_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v___f_2309_; uint8_t v___y_2311_; lean_object* v___x_2318_; uint8_t v___x_2319_; 
v___f_2309_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__2));
v___x_2318_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_2319_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2265_, v___x_2318_);
if (v___x_2319_ == 0)
{
lean_object* v___x_2320_; uint8_t v___x_2321_; 
v___x_2320_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_2321_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2265_, v___x_2320_);
v___y_2311_ = v___x_2321_;
goto v___jp_2310_;
}
else
{
v___y_2311_ = v___x_2319_;
goto v___jp_2310_;
}
v___jp_2271_:
{
lean_object* v___x_2278_; 
v___x_2278_ = l_Lean_Syntax_getRange_x3f(v_cmd_2264_, v___y_2277_);
if (lean_obj_tag(v___x_2278_) == 1)
{
lean_object* v_val_2279_; lean_object* v_fileMap_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v_val_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_val_2279_);
lean_dec_ref_known(v___x_2278_, 1);
v_fileMap_2280_ = lean_ctor_get(v___y_2276_, 1);
v___x_2281_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1);
v___x_2282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___y_2273_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
v___x_2283_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v_fileMap_2280_, v_val_2279_, v_cmd_2264_, v___y_2274_, v___y_2272_, v_msgs_2267_, v___x_2282_, v___y_2276_, v___y_2275_);
lean_dec(v_val_2279_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2292_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2286_ = v___x_2283_;
v_isShared_2287_ = v_isSharedCheck_2292_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2283_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2292_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v_fst_2288_; lean_object* v___x_2290_; 
v_fst_2288_ = lean_ctor_get(v_a_2284_, 0);
lean_inc(v_fst_2288_);
lean_dec(v_a_2284_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v_fst_2288_);
v___x_2290_ = v___x_2286_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_fst_2288_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
v_a_2293_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2283_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2283_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
else
{
lean_object* v___x_2301_; 
lean_dec(v___x_2278_);
lean_dec(v_cmd_2264_);
v___x_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2301_, 0, v___y_2273_);
return v___x_2301_;
}
}
v___jp_2302_:
{
if (v___y_2304_ == 0)
{
if (v___y_2303_ == 0)
{
lean_object* v___x_2308_; 
lean_dec(v_cmd_2264_);
v___x_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2308_, 0, v_acc_2305_);
return v___x_2308_;
}
else
{
v___y_2272_ = v___y_2303_;
v___y_2273_ = v_acc_2305_;
v___y_2274_ = v___y_2304_;
v___y_2275_ = v___y_2307_;
v___y_2276_ = v___y_2306_;
v___y_2277_ = v___y_2303_;
goto v___jp_2271_;
}
}
else
{
v___y_2272_ = v___y_2303_;
v___y_2273_ = v_acc_2305_;
v___y_2274_ = v___y_2304_;
v___y_2275_ = v___y_2307_;
v___y_2276_ = v___y_2306_;
v___y_2277_ = v___y_2304_;
goto v___jp_2271_;
}
}
v___jp_2310_:
{
lean_object* v___x_2312_; uint8_t v_onUnsolved_2313_; lean_object* v___x_2314_; uint8_t v_onSorry_2315_; lean_object* v_acc_2316_; 
v___x_2312_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
v_onUnsolved_2313_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2265_, v___x_2312_);
v___x_2314_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v_onSorry_2315_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_2265_, v___x_2314_);
v_acc_2316_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__3));
if (v_onSorry_2315_ == 0)
{
lean_dec_ref(v_tree_2266_);
v___y_2303_ = v___y_2311_;
v___y_2304_ = v_onUnsolved_2313_;
v_acc_2305_ = v_acc_2316_;
v___y_2306_ = v_a_2268_;
v___y_2307_ = v_a_2269_;
goto v___jp_2302_;
}
else
{
lean_object* v_acc_2317_; 
v_acc_2317_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_2309_, v_acc_2316_, v_tree_2266_);
v___y_2303_ = v___y_2311_;
v___y_2304_ = v_onUnsolved_2313_;
v_acc_2305_ = v_acc_2317_;
v___y_2306_ = v_a_2268_;
v___y_2307_ = v_a_2269_;
goto v___jp_2302_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___boxed(lean_object* v_cmd_2322_, lean_object* v_opts_2323_, lean_object* v_tree_2324_, lean_object* v_msgs_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_cmd_2322_, v_opts_2323_, v_tree_2324_, v_msgs_2325_, v_a_2326_, v_a_2327_);
lean_dec(v_a_2327_);
lean_dec_ref(v_a_2326_);
lean_dec_ref(v_msgs_2325_);
lean_dec_ref(v_opts_2323_);
return v_res_2329_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(lean_object* v_00_u03b2_2330_, lean_object* v_m_2331_, lean_object* v_a_2332_){
_start:
{
uint8_t v___x_2333_; 
v___x_2333_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___redArg(v_m_2331_, v_a_2332_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___boxed(lean_object* v_00_u03b2_2334_, lean_object* v_m_2335_, lean_object* v_a_2336_){
_start:
{
uint8_t v_res_2337_; lean_object* v_r_2338_; 
v_res_2337_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_00_u03b2_2334_, v_m_2335_, v_a_2336_);
lean_dec_ref(v_a_2336_);
lean_dec_ref(v_m_2335_);
v_r_2338_ = lean_box(v_res_2337_);
return v_r_2338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1(lean_object* v_00_u03b2_2339_, lean_object* v_m_2340_, lean_object* v_a_2341_, lean_object* v_b_2342_){
_start:
{
lean_object* v___x_2343_; 
v___x_2343_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_m_2340_, v_a_2341_, v_b_2342_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2(lean_object* v___x_2344_, lean_object* v_fst_2345_, lean_object* v_snd_2346_, lean_object* v___x_2347_, lean_object* v_as_2348_, size_t v_sz_2349_, size_t v_i_2350_, lean_object* v_b_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v___x_2355_; 
v___x_2355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v___x_2344_, v_fst_2345_, v_snd_2346_, v___x_2347_, v_as_2348_, v_sz_2349_, v_i_2350_, v_b_2351_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___boxed(lean_object* v___x_2356_, lean_object* v_fst_2357_, lean_object* v_snd_2358_, lean_object* v___x_2359_, lean_object* v_as_2360_, lean_object* v_sz_2361_, lean_object* v_i_2362_, lean_object* v_b_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
size_t v_sz_boxed_2367_; size_t v_i_boxed_2368_; lean_object* v_res_2369_; 
v_sz_boxed_2367_ = lean_unbox_usize(v_sz_2361_);
lean_dec(v_sz_2361_);
v_i_boxed_2368_ = lean_unbox_usize(v_i_2362_);
lean_dec(v_i_2362_);
v_res_2369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2(v___x_2356_, v_fst_2357_, v_snd_2358_, v___x_2359_, v_as_2360_, v_sz_boxed_2367_, v_i_boxed_2368_, v_b_2363_, v___y_2364_, v___y_2365_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec_ref(v_as_2360_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5(lean_object* v_msgData_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(v_msgData_2370_, v___y_2372_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___boxed(lean_object* v_msgData_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5(v_msgData_2375_, v___y_2376_, v___y_2377_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
return v_res_2379_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0(lean_object* v_00_u03b2_2380_, lean_object* v_a_2381_, lean_object* v_x_2382_){
_start:
{
uint8_t v___x_2383_; 
v___x_2383_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___redArg(v_a_2381_, v_x_2382_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2384_, lean_object* v_a_2385_, lean_object* v_x_2386_){
_start:
{
uint8_t v_res_2387_; lean_object* v_r_2388_; 
v_res_2387_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_spec__0(v_00_u03b2_2384_, v_a_2385_, v_x_2386_);
lean_dec(v_x_2386_);
lean_dec_ref(v_a_2385_);
v_r_2388_ = lean_box(v_res_2387_);
return v_r_2388_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2(lean_object* v_00_u03b2_2389_, lean_object* v_data_2390_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2___redArg(v_data_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2392_, lean_object* v_i_2393_, lean_object* v_source_2394_, lean_object* v_target_2395_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3___redArg(v_i_2393_, v_source_2394_, v_target_2395_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3_spec__8(lean_object* v_00_u03b2_2397_, lean_object* v_x_2398_, lean_object* v_x_2399_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__2_spec__3_spec__8___redArg(v_x_2398_, v_x_2399_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(lean_object* v_x_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v___x_2409_; 
lean_inc(v___y_2403_);
lean_inc_ref(v___y_2402_);
v___x_2409_ = lean_apply_7(v_x_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, lean_box(0));
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed(lean_object* v_x_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(v_x_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(lean_object* v_mvarId_2419_, lean_object* v_x_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v___f_2428_; lean_object* v___x_2429_; 
lean_inc(v___y_2422_);
lean_inc_ref(v___y_2421_);
v___f_2428_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2428_, 0, v_x_2420_);
lean_closure_set(v___f_2428_, 1, v___y_2421_);
lean_closure_set(v___f_2428_, 2, v___y_2422_);
v___x_2429_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2419_, v___f_2428_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
if (lean_obj_tag(v___x_2429_) == 0)
{
return v___x_2429_;
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2429_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2429_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___boxed(lean_object* v_mvarId_2438_, lean_object* v_x_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2438_, v_x_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(lean_object* v_00_u03b1_2448_, lean_object* v_mvarId_2449_, lean_object* v_x_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2449_, v_x_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed(lean_object* v_00_u03b1_2459_, lean_object* v_mvarId_2460_, lean_object* v_x_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(v_00_u03b1_2459_, v_mvarId_2460_, v_x_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(lean_object* v_____r_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2484_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2484_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___boxed(lean_object* v_____r_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(v_____r_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(lean_object* v_____r_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2503_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1___boxed(lean_object* v_____r_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(v_____r_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
return v_res_2511_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(uint8_t v___x_2512_, lean_object* v_x_2513_){
_start:
{
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2___boxed(lean_object* v___x_2514_, lean_object* v_x_2515_){
_start:
{
uint8_t v___x_10922__boxed_2516_; uint8_t v_res_2517_; lean_object* v_r_2518_; 
v___x_10922__boxed_2516_ = lean_unbox(v___x_2514_);
v_res_2517_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(v___x_10922__boxed_2516_, v_x_2515_);
lean_dec(v_x_2515_);
v_r_2518_ = lean_box(v_res_2517_);
return v_r_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(lean_object* v_msgData_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v___x_2525_; lean_object* v_env_2526_; lean_object* v___x_2527_; lean_object* v_mctx_2528_; lean_object* v_lctx_2529_; lean_object* v_options_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2525_ = lean_st_ref_get(v___y_2523_);
v_env_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc_ref(v_env_2526_);
lean_dec(v___x_2525_);
v___x_2527_ = lean_st_ref_get(v___y_2521_);
v_mctx_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc_ref(v_mctx_2528_);
lean_dec(v___x_2527_);
v_lctx_2529_ = lean_ctor_get(v___y_2520_, 2);
v_options_2530_ = lean_ctor_get(v___y_2522_, 2);
lean_inc_ref(v_options_2530_);
lean_inc_ref(v_lctx_2529_);
v___x_2531_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2531_, 0, v_env_2526_);
lean_ctor_set(v___x_2531_, 1, v_mctx_2528_);
lean_ctor_set(v___x_2531_, 2, v_lctx_2529_);
lean_ctor_set(v___x_2531_, 3, v_options_2530_);
v___x_2532_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2531_);
lean_ctor_set(v___x_2532_, 1, v_msgData_2519_);
v___x_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2532_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2___boxed(lean_object* v_msgData_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msgData_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(lean_object* v_cls_2541_, lean_object* v_msg_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_){
_start:
{
lean_object* v_ref_2548_; lean_object* v___x_2549_; lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2594_; 
v_ref_2548_ = lean_ctor_get(v___y_2545_, 5);
v___x_2549_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2552_ = v___x_2549_;
v_isShared_2553_ = v_isSharedCheck_2594_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2549_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2594_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2554_; lean_object* v_traceState_2555_; lean_object* v_env_2556_; lean_object* v_nextMacroScope_2557_; lean_object* v_ngen_2558_; lean_object* v_auxDeclNGen_2559_; lean_object* v_cache_2560_; lean_object* v_messages_2561_; lean_object* v_infoState_2562_; lean_object* v_snapshotTasks_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2593_; 
v___x_2554_ = lean_st_ref_take(v___y_2546_);
v_traceState_2555_ = lean_ctor_get(v___x_2554_, 4);
v_env_2556_ = lean_ctor_get(v___x_2554_, 0);
v_nextMacroScope_2557_ = lean_ctor_get(v___x_2554_, 1);
v_ngen_2558_ = lean_ctor_get(v___x_2554_, 2);
v_auxDeclNGen_2559_ = lean_ctor_get(v___x_2554_, 3);
v_cache_2560_ = lean_ctor_get(v___x_2554_, 5);
v_messages_2561_ = lean_ctor_get(v___x_2554_, 6);
v_infoState_2562_ = lean_ctor_get(v___x_2554_, 7);
v_snapshotTasks_2563_ = lean_ctor_get(v___x_2554_, 8);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2565_ = v___x_2554_;
v_isShared_2566_ = v_isSharedCheck_2593_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_snapshotTasks_2563_);
lean_inc(v_infoState_2562_);
lean_inc(v_messages_2561_);
lean_inc(v_cache_2560_);
lean_inc(v_traceState_2555_);
lean_inc(v_auxDeclNGen_2559_);
lean_inc(v_ngen_2558_);
lean_inc(v_nextMacroScope_2557_);
lean_inc(v_env_2556_);
lean_dec(v___x_2554_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2593_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
uint64_t v_tid_2567_; lean_object* v_traces_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2592_; 
v_tid_2567_ = lean_ctor_get_uint64(v_traceState_2555_, sizeof(void*)*1);
v_traces_2568_ = lean_ctor_get(v_traceState_2555_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v_traceState_2555_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2570_ = v_traceState_2555_;
v_isShared_2571_ = v_isSharedCheck_2592_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_traces_2568_);
lean_dec(v_traceState_2555_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2592_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; double v___x_2573_; uint8_t v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2582_; 
v___x_2572_ = lean_box(0);
v___x_2573_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0);
v___x_2574_ = 0;
v___x_2575_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2576_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2576_, 0, v_cls_2541_);
lean_ctor_set(v___x_2576_, 1, v___x_2572_);
lean_ctor_set(v___x_2576_, 2, v___x_2575_);
lean_ctor_set_float(v___x_2576_, sizeof(void*)*3, v___x_2573_);
lean_ctor_set_float(v___x_2576_, sizeof(void*)*3 + 8, v___x_2573_);
lean_ctor_set_uint8(v___x_2576_, sizeof(void*)*3 + 16, v___x_2574_);
v___x_2577_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__1));
v___x_2578_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2576_);
lean_ctor_set(v___x_2578_, 1, v_a_2550_);
lean_ctor_set(v___x_2578_, 2, v___x_2577_);
lean_inc(v_ref_2548_);
v___x_2579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2579_, 0, v_ref_2548_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
v___x_2580_ = l_Lean_PersistentArray_push___redArg(v_traces_2568_, v___x_2579_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 0, v___x_2580_);
v___x_2582_ = v___x_2570_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v___x_2580_);
lean_ctor_set_uint64(v_reuseFailAlloc_2591_, sizeof(void*)*1, v_tid_2567_);
v___x_2582_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
lean_object* v___x_2584_; 
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 4, v___x_2582_);
v___x_2584_ = v___x_2565_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_env_2556_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v_nextMacroScope_2557_);
lean_ctor_set(v_reuseFailAlloc_2590_, 2, v_ngen_2558_);
lean_ctor_set(v_reuseFailAlloc_2590_, 3, v_auxDeclNGen_2559_);
lean_ctor_set(v_reuseFailAlloc_2590_, 4, v___x_2582_);
lean_ctor_set(v_reuseFailAlloc_2590_, 5, v_cache_2560_);
lean_ctor_set(v_reuseFailAlloc_2590_, 6, v_messages_2561_);
lean_ctor_set(v_reuseFailAlloc_2590_, 7, v_infoState_2562_);
lean_ctor_set(v_reuseFailAlloc_2590_, 8, v_snapshotTasks_2563_);
v___x_2584_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2588_; 
v___x_2585_ = lean_st_ref_put(v___y_2546_, v___x_2584_);
v___x_2586_ = lean_box(0);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 0, v___x_2586_);
v___x_2588_ = v___x_2552_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2586_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg___boxed(lean_object* v_cls_2595_, lean_object* v_msg_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_2595_, v_msg_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
return v_res_2602_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__0));
v___x_2605_ = l_Lean_stringToMessageData(v___x_2604_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(lean_object* v___x_2606_, lean_object* v___x_2607_, lean_object* v___x_2608_, lean_object* v___f_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v___x_2617_; lean_object* v_a_2619_; lean_object* v___y_2623_; lean_object* v___x_2637_; 
v___x_2617_ = lean_st_mk_ref(v___x_2606_);
v___x_2637_ = l_Lean_Elab_Tactic_saveState___redArg(v___x_2617_, v___y_2611_, v___y_2613_, v___y_2615_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_a_2638_; lean_object* v___x_2639_; 
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_a_2638_);
lean_dec_ref_known(v___x_2637_, 1);
v___x_2639_ = l_Lean_Elab_Tactic_Try_collectTryCoreSuggestions(v___x_2607_, v___x_2608_, v___x_2617_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; 
lean_dec(v_a_2638_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec_ref(v___f_2609_);
lean_dec_ref(v___x_2608_);
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
lean_inc(v_a_2640_);
lean_dec_ref_known(v___x_2639_, 1);
v_a_2619_ = v_a_2640_;
goto v___jp_2618_;
}
else
{
lean_object* v_a_2641_; uint8_t v___y_2643_; uint8_t v___x_2686_; 
v_a_2641_ = lean_ctor_get(v___x_2639_, 0);
lean_inc(v_a_2641_);
v___x_2686_ = l_Lean_Exception_isInterrupt(v_a_2641_);
if (v___x_2686_ == 0)
{
uint8_t v___x_2687_; 
lean_inc(v_a_2641_);
v___x_2687_ = l_Lean_Exception_isRuntime(v_a_2641_);
v___y_2643_ = v___x_2687_;
goto v___jp_2642_;
}
else
{
v___y_2643_ = v___x_2686_;
goto v___jp_2642_;
}
v___jp_2642_:
{
if (v___y_2643_ == 0)
{
lean_object* v___x_2644_; 
lean_dec_ref_known(v___x_2639_, 1);
v___x_2644_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2638_, v___y_2643_, v___x_2617_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2676_; 
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2676_ == 0)
{
lean_object* v_unused_2677_; 
v_unused_2677_ = lean_ctor_get(v___x_2644_, 0);
lean_dec(v_unused_2677_);
v___x_2646_ = v___x_2644_;
v_isShared_2647_ = v_isSharedCheck_2676_;
goto v_resetjp_2645_;
}
else
{
lean_dec(v___x_2644_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2676_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
uint8_t v___x_2648_; 
v___x_2648_ = l_Lean_Exception_isInterrupt(v_a_2641_);
if (v___x_2648_ == 0)
{
uint8_t v___x_2649_; 
lean_inc(v_a_2641_);
v___x_2649_ = l_Lean_Exception_isMaxRecDepth(v_a_2641_);
if (v___x_2649_ == 0)
{
lean_object* v_options_2650_; uint8_t v_hasTrace_2651_; 
lean_del_object(v___x_2646_);
v_options_2650_ = lean_ctor_get(v___y_2614_, 2);
v_hasTrace_2651_ = lean_ctor_get_uint8(v_options_2650_, sizeof(void*)*1);
if (v_hasTrace_2651_ == 0)
{
lean_dec(v_a_2641_);
goto v___jp_2634_;
}
else
{
lean_object* v_inheritedTraceOptions_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; uint8_t v___x_2655_; 
v_inheritedTraceOptions_2652_ = lean_ctor_get(v___y_2614_, 13);
v___x_2653_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2654_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_2655_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2652_, v_options_2650_, v___x_2654_);
if (v___x_2655_ == 0)
{
lean_dec(v_a_2641_);
goto v___jp_2634_;
}
else
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2656_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_2657_ = l_Lean_Exception_toMessageData(v_a_2641_);
v___x_2658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2656_);
lean_ctor_set(v___x_2658_, 1, v___x_2657_);
v___x_2659_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v___x_2653_, v___x_2658_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___x_2661_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref_known(v___x_2659_, 1);
lean_inc(v___x_2617_);
v___x_2661_ = lean_apply_10(v___f_2609_, v_a_2660_, v___x_2608_, v___x_2617_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, lean_box(0));
v___y_2623_ = v___x_2661_;
goto v___jp_2622_;
}
else
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2669_; 
lean_dec(v___x_2617_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec_ref(v___f_2609_);
lean_dec_ref(v___x_2608_);
v_a_2662_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2664_ = v___x_2659_;
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2659_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2667_; 
if (v_isShared_2665_ == 0)
{
v___x_2667_ = v___x_2664_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2662_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
}
}
else
{
lean_object* v___x_2671_; 
lean_dec(v___x_2617_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec_ref(v___f_2609_);
lean_dec_ref(v___x_2608_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set_tag(v___x_2646_, 1);
lean_ctor_set(v___x_2646_, 0, v_a_2641_);
v___x_2671_ = v___x_2646_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_a_2641_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
else
{
lean_object* v___x_2674_; 
lean_dec(v___x_2617_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec_ref(v___f_2609_);
lean_dec_ref(v___x_2608_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set_tag(v___x_2646_, 1);
lean_ctor_set(v___x_2646_, 0, v_a_2641_);
v___x_2674_ = v___x_2646_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2641_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
lean_dec(v_a_2641_);
lean_dec(v___x_2617_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec_ref(v___f_2609_);
lean_dec_ref(v___x_2608_);
v_a_2678_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v___x_2644_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2644_);
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
}
else
{
lean_dec(v_a_2641_);
lean_dec(v_a_2638_);
lean_dec(v___x_2617_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec_ref(v___f_2609_);
lean_dec_ref(v___x_2608_);
return v___x_2639_;
}
}
}
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
lean_dec(v___x_2617_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec_ref(v___f_2609_);
lean_dec_ref(v___x_2608_);
lean_dec_ref(v___x_2607_);
v_a_2688_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2637_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2637_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
v___jp_2618_:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2620_ = lean_st_ref_get(v___x_2617_);
lean_dec(v___x_2617_);
lean_dec(v___x_2620_);
v___x_2621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2621_, 0, v_a_2619_);
return v___x_2621_;
}
v___jp_2622_:
{
if (lean_obj_tag(v___y_2623_) == 0)
{
lean_object* v_a_2624_; lean_object* v_a_2625_; 
v_a_2624_ = lean_ctor_get(v___y_2623_, 0);
lean_inc(v_a_2624_);
lean_dec_ref_known(v___y_2623_, 1);
v_a_2625_ = lean_ctor_get(v_a_2624_, 0);
lean_inc(v_a_2625_);
lean_dec(v_a_2624_);
v_a_2619_ = v_a_2625_;
goto v___jp_2618_;
}
else
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2633_; 
lean_dec(v___x_2617_);
v_a_2626_ = lean_ctor_get(v___y_2623_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___y_2623_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2628_ = v___y_2623_;
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___y_2623_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
if (v_isShared_2629_ == 0)
{
v___x_2631_ = v___x_2628_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
v___jp_2634_:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2635_ = lean_box(0);
lean_inc(v___x_2617_);
v___x_2636_ = lean_apply_10(v___f_2609_, v___x_2635_, v___x_2608_, v___x_2617_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, lean_box(0));
v___y_2623_ = v___x_2636_;
goto v___jp_2622_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed(lean_object* v___x_2696_, lean_object* v___x_2697_, lean_object* v___x_2698_, lean_object* v___f_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(v___x_2696_, v___x_2697_, v___x_2698_, v___f_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(lean_object* v___x_2708_, uint8_t v___x_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v___x_2717_; 
v___x_2717_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2708_, v___x_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed(lean_object* v___x_2718_, lean_object* v___x_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
uint8_t v___x_11251__boxed_2727_; lean_object* v_res_2728_; 
v___x_11251__boxed_2727_ = lean_unbox(v___x_2719_);
v_res_2728_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(v___x_2718_, v___x_11251__boxed_2727_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(lean_object* v_cls_2729_, lean_object* v_msg_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
lean_object* v_ref_2736_; lean_object* v___x_2737_; lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2782_; 
v_ref_2736_ = lean_ctor_get(v___y_2733_, 5);
v___x_2737_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2740_ = v___x_2737_;
v_isShared_2741_ = v_isSharedCheck_2782_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2737_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2782_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2742_; lean_object* v_traceState_2743_; lean_object* v_env_2744_; lean_object* v_nextMacroScope_2745_; lean_object* v_ngen_2746_; lean_object* v_auxDeclNGen_2747_; lean_object* v_cache_2748_; lean_object* v_messages_2749_; lean_object* v_infoState_2750_; lean_object* v_snapshotTasks_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2781_; 
v___x_2742_ = lean_st_ref_take(v___y_2734_);
v_traceState_2743_ = lean_ctor_get(v___x_2742_, 4);
v_env_2744_ = lean_ctor_get(v___x_2742_, 0);
v_nextMacroScope_2745_ = lean_ctor_get(v___x_2742_, 1);
v_ngen_2746_ = lean_ctor_get(v___x_2742_, 2);
v_auxDeclNGen_2747_ = lean_ctor_get(v___x_2742_, 3);
v_cache_2748_ = lean_ctor_get(v___x_2742_, 5);
v_messages_2749_ = lean_ctor_get(v___x_2742_, 6);
v_infoState_2750_ = lean_ctor_get(v___x_2742_, 7);
v_snapshotTasks_2751_ = lean_ctor_get(v___x_2742_, 8);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2753_ = v___x_2742_;
v_isShared_2754_ = v_isSharedCheck_2781_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_snapshotTasks_2751_);
lean_inc(v_infoState_2750_);
lean_inc(v_messages_2749_);
lean_inc(v_cache_2748_);
lean_inc(v_traceState_2743_);
lean_inc(v_auxDeclNGen_2747_);
lean_inc(v_ngen_2746_);
lean_inc(v_nextMacroScope_2745_);
lean_inc(v_env_2744_);
lean_dec(v___x_2742_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2781_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
uint64_t v_tid_2755_; lean_object* v_traces_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2780_; 
v_tid_2755_ = lean_ctor_get_uint64(v_traceState_2743_, sizeof(void*)*1);
v_traces_2756_ = lean_ctor_get(v_traceState_2743_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v_traceState_2743_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2758_ = v_traceState_2743_;
v_isShared_2759_ = v_isSharedCheck_2780_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_traces_2756_);
lean_dec(v_traceState_2743_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2780_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2760_; double v___x_2761_; uint8_t v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2770_; 
v___x_2760_ = lean_box(0);
v___x_2761_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__0);
v___x_2762_ = 0;
v___x_2763_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2764_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2764_, 0, v_cls_2729_);
lean_ctor_set(v___x_2764_, 1, v___x_2760_);
lean_ctor_set(v___x_2764_, 2, v___x_2763_);
lean_ctor_set_float(v___x_2764_, sizeof(void*)*3, v___x_2761_);
lean_ctor_set_float(v___x_2764_, sizeof(void*)*3 + 8, v___x_2761_);
lean_ctor_set_uint8(v___x_2764_, sizeof(void*)*3 + 16, v___x_2762_);
v___x_2765_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___closed__1));
v___x_2766_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2764_);
lean_ctor_set(v___x_2766_, 1, v_a_2738_);
lean_ctor_set(v___x_2766_, 2, v___x_2765_);
lean_inc(v_ref_2736_);
v___x_2767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2767_, 0, v_ref_2736_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
v___x_2768_ = l_Lean_PersistentArray_push___redArg(v_traces_2756_, v___x_2767_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v___x_2768_);
v___x_2770_ = v___x_2758_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2768_);
lean_ctor_set_uint64(v_reuseFailAlloc_2779_, sizeof(void*)*1, v_tid_2755_);
v___x_2770_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
lean_object* v___x_2772_; 
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 4, v___x_2770_);
v___x_2772_ = v___x_2753_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_env_2744_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v_nextMacroScope_2745_);
lean_ctor_set(v_reuseFailAlloc_2778_, 2, v_ngen_2746_);
lean_ctor_set(v_reuseFailAlloc_2778_, 3, v_auxDeclNGen_2747_);
lean_ctor_set(v_reuseFailAlloc_2778_, 4, v___x_2770_);
lean_ctor_set(v_reuseFailAlloc_2778_, 5, v_cache_2748_);
lean_ctor_set(v_reuseFailAlloc_2778_, 6, v_messages_2749_);
lean_ctor_set(v_reuseFailAlloc_2778_, 7, v_infoState_2750_);
lean_ctor_set(v_reuseFailAlloc_2778_, 8, v_snapshotTasks_2751_);
v___x_2772_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2776_; 
v___x_2773_ = lean_st_ref_put(v___y_2734_, v___x_2772_);
v___x_2774_ = lean_box(0);
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 0, v___x_2774_);
v___x_2776_ = v___x_2740_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___x_2774_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3___boxed(lean_object* v_cls_2783_, lean_object* v_msg_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v_cls_2783_, v_msg_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
return v_res_2790_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2792_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__0));
v___x_2793_ = l_Lean_stringToMessageData(v___x_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(lean_object* v_term_2794_, lean_object* v___x_2795_, lean_object* v___x_2796_, lean_object* v___f_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v___y_2804_; lean_object* v___x_2822_; 
v___x_2822_ = l_Lean_Elab_Term_TermElabM_run___redArg(v_term_2794_, v___x_2795_, v___x_2796_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2831_; 
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec_ref(v___f_2797_);
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2825_ = v___x_2822_;
v_isShared_2826_ = v_isSharedCheck_2831_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2822_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2831_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v_fst_2827_; lean_object* v___x_2829_; 
v_fst_2827_ = lean_ctor_get(v_a_2823_, 0);
lean_inc(v_fst_2827_);
lean_dec(v_a_2823_);
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 0, v_fst_2827_);
v___x_2829_ = v___x_2825_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_fst_2827_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2874_; 
v_a_2832_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2834_ = v___x_2822_;
v_isShared_2835_ = v_isSharedCheck_2874_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2822_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2874_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
uint8_t v___y_2840_; uint8_t v___x_2872_; 
v___x_2872_ = l_Lean_Exception_isInterrupt(v_a_2832_);
if (v___x_2872_ == 0)
{
uint8_t v___x_2873_; 
lean_inc(v_a_2832_);
v___x_2873_ = l_Lean_Exception_isRuntime(v_a_2832_);
v___y_2840_ = v___x_2873_;
goto v___jp_2839_;
}
else
{
v___y_2840_ = v___x_2872_;
goto v___jp_2839_;
}
v___jp_2836_:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2837_ = lean_box(0);
v___x_2838_ = lean_apply_6(v___f_2797_, v___x_2837_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, lean_box(0));
v___y_2804_ = v___x_2838_;
goto v___jp_2803_;
}
v___jp_2839_:
{
if (v___y_2840_ == 0)
{
uint8_t v___x_2841_; 
v___x_2841_ = l_Lean_Exception_isInterrupt(v_a_2832_);
if (v___x_2841_ == 0)
{
uint8_t v___x_2842_; 
lean_inc(v_a_2832_);
v___x_2842_ = l_Lean_Exception_isMaxRecDepth(v_a_2832_);
if (v___x_2842_ == 0)
{
lean_object* v_options_2843_; uint8_t v_hasTrace_2844_; 
lean_del_object(v___x_2834_);
v_options_2843_ = lean_ctor_get(v___y_2800_, 2);
v_hasTrace_2844_ = lean_ctor_get_uint8(v_options_2843_, sizeof(void*)*1);
if (v_hasTrace_2844_ == 0)
{
lean_dec(v_a_2832_);
goto v___jp_2836_;
}
else
{
lean_object* v_inheritedTraceOptions_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; uint8_t v___x_2848_; 
v_inheritedTraceOptions_2845_ = lean_ctor_get(v___y_2800_, 13);
v___x_2846_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2847_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_2848_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2845_, v_options_2843_, v___x_2847_);
if (v___x_2848_ == 0)
{
lean_dec(v_a_2832_);
goto v___jp_2836_;
}
else
{
lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2849_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1);
v___x_2850_ = l_Lean_Exception_toMessageData(v_a_2832_);
v___x_2851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2849_);
lean_ctor_set(v___x_2851_, 1, v___x_2850_);
v___x_2852_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_2846_, v___x_2851_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2854_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2853_);
lean_dec_ref_known(v___x_2852_, 1);
v___x_2854_ = lean_apply_6(v___f_2797_, v_a_2853_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, lean_box(0));
v___y_2804_ = v___x_2854_;
goto v___jp_2803_;
}
else
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec_ref(v___f_2797_);
v_a_2855_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___x_2852_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2852_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2855_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
}
}
else
{
lean_object* v___x_2864_; 
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec_ref(v___f_2797_);
if (v_isShared_2835_ == 0)
{
v___x_2864_ = v___x_2834_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_a_2832_);
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
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec_ref(v___f_2797_);
if (v_isShared_2835_ == 0)
{
v___x_2867_ = v___x_2834_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2832_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
else
{
lean_object* v___x_2870_; 
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec_ref(v___f_2797_);
if (v_isShared_2835_ == 0)
{
v___x_2870_ = v___x_2834_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2832_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
}
v___jp_2803_:
{
if (lean_obj_tag(v___y_2804_) == 0)
{
lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2813_; 
v_a_2805_ = lean_ctor_get(v___y_2804_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___y_2804_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2807_ = v___y_2804_;
v_isShared_2808_ = v_isSharedCheck_2813_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_dec(v___y_2804_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2813_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v_a_2809_; lean_object* v___x_2811_; 
v_a_2809_ = lean_ctor_get(v_a_2805_, 0);
lean_inc(v_a_2809_);
lean_dec(v_a_2805_);
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 0, v_a_2809_);
v___x_2811_ = v___x_2807_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_a_2809_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
else
{
lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2821_; 
v_a_2814_ = lean_ctor_get(v___y_2804_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___y_2804_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2816_ = v___y_2804_;
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_dec(v___y_2804_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2819_; 
if (v_isShared_2817_ == 0)
{
v___x_2819_ = v___x_2816_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_a_2814_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___boxed(lean_object* v_term_2875_, lean_object* v___x_2876_, lean_object* v___x_2877_, lean_object* v___f_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(v_term_2875_, v___x_2876_, v___x_2877_, v___f_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_2885_, lean_object* v_vals_2886_, lean_object* v_i_2887_, lean_object* v_k_2888_){
_start:
{
lean_object* v___x_2889_; uint8_t v___x_2890_; 
v___x_2889_ = lean_array_get_size(v_keys_2885_);
v___x_2890_ = lean_nat_dec_lt(v_i_2887_, v___x_2889_);
if (v___x_2890_ == 0)
{
lean_object* v___x_2891_; 
lean_dec(v_i_2887_);
v___x_2891_ = lean_box(0);
return v___x_2891_;
}
else
{
lean_object* v_k_x27_2892_; uint8_t v___x_2893_; 
v_k_x27_2892_ = lean_array_fget_borrowed(v_keys_2885_, v_i_2887_);
v___x_2893_ = l_Lean_instBEqMVarId_beq(v_k_2888_, v_k_x27_2892_);
if (v___x_2893_ == 0)
{
lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2894_ = lean_unsigned_to_nat(1u);
v___x_2895_ = lean_nat_add(v_i_2887_, v___x_2894_);
lean_dec(v_i_2887_);
v_i_2887_ = v___x_2895_;
goto _start;
}
else
{
lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2897_ = lean_array_fget_borrowed(v_vals_2886_, v_i_2887_);
lean_dec(v_i_2887_);
lean_inc(v___x_2897_);
v___x_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2897_);
return v___x_2898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_2899_, lean_object* v_vals_2900_, lean_object* v_i_2901_, lean_object* v_k_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_keys_2899_, v_vals_2900_, v_i_2901_, v_k_2902_);
lean_dec(v_k_2902_);
lean_dec_ref(v_vals_2900_);
lean_dec_ref(v_keys_2899_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(lean_object* v_x_2904_, size_t v_x_2905_, lean_object* v_x_2906_){
_start:
{
if (lean_obj_tag(v_x_2904_) == 0)
{
lean_object* v_es_2907_; lean_object* v___x_2908_; size_t v___x_2909_; size_t v___x_2910_; lean_object* v_j_2911_; lean_object* v___x_2912_; 
v_es_2907_ = lean_ctor_get(v_x_2904_, 0);
v___x_2908_ = lean_box(2);
v___x_2909_ = ((size_t)31ULL);
v___x_2910_ = lean_usize_land(v_x_2905_, v___x_2909_);
v_j_2911_ = lean_usize_to_nat(v___x_2910_);
v___x_2912_ = lean_array_get_borrowed(v___x_2908_, v_es_2907_, v_j_2911_);
lean_dec(v_j_2911_);
switch(lean_obj_tag(v___x_2912_))
{
case 0:
{
lean_object* v_key_2913_; lean_object* v_val_2914_; uint8_t v___x_2915_; 
v_key_2913_ = lean_ctor_get(v___x_2912_, 0);
v_val_2914_ = lean_ctor_get(v___x_2912_, 1);
v___x_2915_ = l_Lean_instBEqMVarId_beq(v_x_2906_, v_key_2913_);
if (v___x_2915_ == 0)
{
lean_object* v___x_2916_; 
v___x_2916_ = lean_box(0);
return v___x_2916_;
}
else
{
lean_object* v___x_2917_; 
lean_inc(v_val_2914_);
v___x_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2917_, 0, v_val_2914_);
return v___x_2917_;
}
}
case 1:
{
lean_object* v_node_2918_; size_t v___x_2919_; size_t v___x_2920_; 
v_node_2918_ = lean_ctor_get(v___x_2912_, 0);
v___x_2919_ = ((size_t)5ULL);
v___x_2920_ = lean_usize_shift_right(v_x_2905_, v___x_2919_);
v_x_2904_ = v_node_2918_;
v_x_2905_ = v___x_2920_;
goto _start;
}
default: 
{
lean_object* v___x_2922_; 
v___x_2922_ = lean_box(0);
return v___x_2922_;
}
}
}
else
{
lean_object* v_ks_2923_; lean_object* v_vs_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v_ks_2923_ = lean_ctor_get(v_x_2904_, 0);
v_vs_2924_ = lean_ctor_get(v_x_2904_, 1);
v___x_2925_ = lean_unsigned_to_nat(0u);
v___x_2926_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_ks_2923_, v_vs_2924_, v___x_2925_, v_x_2906_);
return v___x_2926_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg___boxed(lean_object* v_x_2927_, lean_object* v_x_2928_, lean_object* v_x_2929_){
_start:
{
size_t v_x_11570__boxed_2930_; lean_object* v_res_2931_; 
v_x_11570__boxed_2930_ = lean_unbox_usize(v_x_2928_);
lean_dec(v_x_2928_);
v_res_2931_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_2927_, v_x_11570__boxed_2930_, v_x_2929_);
lean_dec(v_x_2929_);
lean_dec_ref(v_x_2927_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(lean_object* v_x_2932_, lean_object* v_x_2933_){
_start:
{
uint64_t v___x_2934_; size_t v___x_2935_; lean_object* v___x_2936_; 
v___x_2934_ = l_Lean_instHashableMVarId_hash(v_x_2933_);
v___x_2935_ = lean_uint64_to_usize(v___x_2934_);
v___x_2936_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_2932_, v___x_2935_, v_x_2933_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg___boxed(lean_object* v_x_2937_, lean_object* v_x_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_x_2937_, v_x_2938_);
lean_dec(v_x_2938_);
lean_dec_ref(v_x_2937_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(lean_object* v_c_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_){
_start:
{
lean_object* v_mctx_2969_; lean_object* v_env_2970_; lean_object* v_opts_2971_; lean_object* v_namingCtx_2972_; lean_object* v_goal_2973_; lean_object* v_decls_2974_; lean_object* v___x_2975_; 
v_mctx_2969_ = lean_ctor_get(v_c_2965_, 3);
lean_inc_ref(v_mctx_2969_);
v_env_2970_ = lean_ctor_get(v_c_2965_, 2);
lean_inc_ref(v_env_2970_);
v_opts_2971_ = lean_ctor_get(v_c_2965_, 4);
lean_inc_ref(v_opts_2971_);
v_namingCtx_2972_ = lean_ctor_get(v_c_2965_, 5);
lean_inc_ref(v_namingCtx_2972_);
v_goal_2973_ = lean_ctor_get(v_c_2965_, 6);
lean_inc(v_goal_2973_);
lean_dec_ref(v_c_2965_);
v_decls_2974_ = lean_ctor_get(v_mctx_2969_, 5);
v___x_2975_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_decls_2974_, v_goal_2973_);
if (lean_obj_tag(v___x_2975_) == 1)
{
lean_object* v_val_2976_; lean_object* v_lctx_2977_; lean_object* v___f_2978_; lean_object* v___f_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___f_2984_; lean_object* v___x_2985_; uint8_t v___x_2986_; lean_object* v___x_2987_; lean_object* v_term_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___f_2991_; lean_object* v___x_2992_; 
v_val_2976_ = lean_ctor_get(v___x_2975_, 0);
lean_inc(v_val_2976_);
lean_dec_ref_known(v___x_2975_, 1);
v_lctx_2977_ = lean_ctor_get(v_val_2976_, 1);
lean_inc_ref(v_lctx_2977_);
lean_dec(v_val_2976_);
v___f_2978_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__0));
v___f_2979_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__1));
v___x_2980_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__3));
v___x_2981_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__4));
v___x_2982_ = lean_box(0);
lean_inc(v_goal_2973_);
v___x_2983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2983_, 0, v_goal_2973_);
lean_ctor_set(v___x_2983_, 1, v___x_2982_);
v___f_2984_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed), 11, 4);
lean_closure_set(v___f_2984_, 0, v___x_2983_);
lean_closure_set(v___f_2984_, 1, v___x_2980_);
lean_closure_set(v___f_2984_, 2, v___x_2981_);
lean_closure_set(v___f_2984_, 3, v___f_2978_);
v___x_2985_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed), 10, 3);
lean_closure_set(v___x_2985_, 0, lean_box(0));
lean_closure_set(v___x_2985_, 1, v_goal_2973_);
lean_closure_set(v___x_2985_, 2, v___f_2984_);
v___x_2986_ = 1;
v___x_2987_ = lean_box(v___x_2986_);
v_term_2988_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed), 9, 2);
lean_closure_set(v_term_2988_, 0, v___x_2985_);
lean_closure_set(v_term_2988_, 1, v___x_2987_);
v___x_2989_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__6));
v___x_2990_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__7));
v___f_2991_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___boxed), 9, 4);
lean_closure_set(v___f_2991_, 0, v_term_2988_);
lean_closure_set(v___f_2991_, 1, v___x_2989_);
lean_closure_set(v___f_2991_, 2, v___x_2990_);
lean_closure_set(v___f_2991_, 3, v___f_2979_);
v___x_2992_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_2970_, v_mctx_2969_, v_lctx_2977_, v_opts_2971_, v_namingCtx_2972_, v___f_2991_, v_a_2966_, v_a_2967_);
lean_dec_ref(v_namingCtx_2972_);
return v___x_2992_;
}
else
{
lean_object* v___x_2993_; lean_object* v___x_2994_; 
lean_dec(v___x_2975_);
lean_dec(v_goal_2973_);
lean_dec_ref(v_namingCtx_2972_);
lean_dec_ref(v_opts_2971_);
lean_dec_ref(v_env_2970_);
lean_dec_ref(v_mctx_2969_);
v___x_2993_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__0));
v___x_2994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2993_);
return v___x_2994_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___boxed(lean_object* v_c_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_){
_start:
{
lean_object* v_res_2999_; 
v_res_2999_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(v_c_2995_, v_a_2996_, v_a_2997_);
lean_dec(v_a_2997_);
lean_dec_ref(v_a_2996_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0(lean_object* v_00_u03b2_3000_, lean_object* v_x_3001_, lean_object* v_x_3002_){
_start:
{
lean_object* v___x_3003_; 
v___x_3003_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_x_3001_, v_x_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___boxed(lean_object* v_00_u03b2_3004_, lean_object* v_x_3005_, lean_object* v_x_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0(v_00_u03b2_3004_, v_x_3005_, v_x_3006_);
lean_dec(v_x_3006_);
lean_dec_ref(v_x_3005_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(lean_object* v_cls_3008_, lean_object* v_msg_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_){
_start:
{
lean_object* v___x_3019_; 
v___x_3019_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_3008_, v_msg_3009_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___boxed(lean_object* v_cls_3020_, lean_object* v_msg_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(v_cls_3020_, v_msg_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(lean_object* v_00_u03b2_3032_, lean_object* v_x_3033_, size_t v_x_3034_, lean_object* v_x_3035_){
_start:
{
lean_object* v___x_3036_; 
v___x_3036_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_3033_, v_x_3034_, v_x_3035_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3037_, lean_object* v_x_3038_, lean_object* v_x_3039_, lean_object* v_x_3040_){
_start:
{
size_t v_x_11827__boxed_3041_; lean_object* v_res_3042_; 
v_x_11827__boxed_3041_ = lean_unbox_usize(v_x_3039_);
lean_dec(v_x_3039_);
v_res_3042_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(v_00_u03b2_3037_, v_x_3038_, v_x_11827__boxed_3041_, v_x_3040_);
lean_dec(v_x_3040_);
lean_dec_ref(v_x_3038_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3043_, lean_object* v_keys_3044_, lean_object* v_vals_3045_, lean_object* v_heq_3046_, lean_object* v_i_3047_, lean_object* v_k_3048_){
_start:
{
lean_object* v___x_3049_; 
v___x_3049_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_keys_3044_, v_vals_3045_, v_i_3047_, v_k_3048_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3050_, lean_object* v_keys_3051_, lean_object* v_vals_3052_, lean_object* v_heq_3053_, lean_object* v_i_3054_, lean_object* v_k_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2(v_00_u03b2_3050_, v_keys_3051_, v_vals_3052_, v_heq_3053_, v_i_3054_, v_k_3055_);
lean_dec(v_k_3055_);
lean_dec_ref(v_vals_3052_);
lean_dec_ref(v_keys_3051_);
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(uint8_t v___x_3059_, lean_object* v___x_3060_, lean_object* v_ref_3061_, lean_object* v_a_3062_, lean_object* v___x_3063_, lean_object* v___x_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
if (v___x_3059_ == 0)
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; uint8_t v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3060_);
v___x_3069_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__0));
v___x_3070_ = lean_box(0);
v___x_3071_ = 4;
v___x_3072_ = l_Lean_MessageData_nil;
v___x_3073_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_3061_, v_a_3062_, v___x_3068_, v___x_3069_, v___x_3070_, v___x_3071_, v___x_3072_, v___y_3065_, v___y_3066_);
return v___x_3073_;
}
else
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; uint8_t v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3074_ = lean_array_get(v___x_3063_, v_a_3062_, v___x_3064_);
lean_dec_ref(v_a_3062_);
v___x_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3060_);
v___x_3076_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__1));
v___x_3077_ = lean_box(0);
v___x_3078_ = 4;
v___x_3079_ = l_Lean_MessageData_nil;
v___x_3080_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_3061_, v___x_3074_, v___x_3075_, v___x_3076_, v___x_3077_, v___x_3078_, v___x_3079_, v___y_3065_, v___y_3066_);
return v___x_3080_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed(lean_object* v___x_3081_, lean_object* v___x_3082_, lean_object* v_ref_3083_, lean_object* v_a_3084_, lean_object* v___x_3085_, lean_object* v___x_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_){
_start:
{
uint8_t v___x_3485__boxed_3090_; lean_object* v_res_3091_; 
v___x_3485__boxed_3090_ = lean_unbox(v___x_3081_);
v_res_3091_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(v___x_3485__boxed_3090_, v___x_3082_, v_ref_3083_, v_a_3084_, v___x_3085_, v___x_3086_, v___y_3087_, v___y_3088_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
lean_dec(v___x_3086_);
lean_dec_ref(v___x_3085_);
return v_res_3091_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_3092_, uint8_t v___y_3093_, lean_object* v_x_3094_){
_start:
{
if (lean_obj_tag(v_x_3094_) == 1)
{
lean_object* v_pre_3095_; 
v_pre_3095_ = lean_ctor_get(v_x_3094_, 0);
if (lean_obj_tag(v_pre_3095_) == 0)
{
lean_object* v_str_3096_; lean_object* v___x_3097_; uint8_t v___x_3098_; 
v_str_3096_ = lean_ctor_get(v_x_3094_, 1);
v___x_3097_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__1));
v___x_3098_ = lean_string_dec_eq(v_str_3096_, v___x_3097_);
if (v___x_3098_ == 0)
{
return v___x_3098_;
}
else
{
return v_suppressElabErrors_3092_;
}
}
else
{
return v___y_3093_;
}
}
else
{
return v___y_3093_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_3099_, lean_object* v___y_3100_, lean_object* v_x_3101_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3102_; uint8_t v___y_3538__boxed_3103_; uint8_t v_res_3104_; lean_object* v_r_3105_; 
v_suppressElabErrors_boxed_3102_ = lean_unbox(v_suppressElabErrors_3099_);
v___y_3538__boxed_3103_ = lean_unbox(v___y_3100_);
v_res_3104_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_3102_, v___y_3538__boxed_3103_, v_x_3101_);
lean_dec(v_x_3101_);
v_r_3105_ = lean_box(v_res_3104_);
return v_r_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(lean_object* v_ref_3106_, lean_object* v_msgData_3107_, uint8_t v_severity_3108_, uint8_t v_isSilent_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_){
_start:
{
lean_object* v___y_3114_; uint8_t v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; uint8_t v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; uint8_t v___y_3179_; uint8_t v___y_3180_; lean_object* v___y_3181_; uint8_t v___y_3182_; lean_object* v___y_3183_; uint8_t v___y_3207_; uint8_t v___y_3208_; lean_object* v___y_3209_; uint8_t v___y_3210_; lean_object* v___y_3211_; uint8_t v___y_3215_; uint8_t v___y_3216_; uint8_t v___y_3217_; uint8_t v___x_3232_; uint8_t v___y_3234_; uint8_t v___y_3235_; uint8_t v___y_3236_; uint8_t v___y_3238_; uint8_t v___x_3250_; 
v___x_3232_ = 2;
v___x_3250_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3108_, v___x_3232_);
if (v___x_3250_ == 0)
{
v___y_3238_ = v___x_3250_;
goto v___jp_3237_;
}
else
{
uint8_t v___x_3251_; 
lean_inc_ref(v_msgData_3107_);
v___x_3251_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3107_);
v___y_3238_ = v___x_3251_;
goto v___jp_3237_;
}
v___jp_3113_:
{
lean_object* v___x_3122_; 
v___x_3122_ = l_Lean_Elab_Command_getScope___redArg(v___y_3121_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_a_3123_; lean_object* v___x_3124_; 
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc(v_a_3123_);
lean_dec_ref_known(v___x_3122_, 1);
v___x_3124_ = l_Lean_Elab_Command_getScope___redArg(v___y_3121_);
if (lean_obj_tag(v___x_3124_) == 0)
{
lean_object* v_a_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3161_; 
v_a_3125_ = lean_ctor_get(v___x_3124_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3127_ = v___x_3124_;
v_isShared_3128_ = v_isSharedCheck_3161_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_a_3125_);
lean_dec(v___x_3124_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3161_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3129_; lean_object* v_currNamespace_3130_; lean_object* v_openDecls_3131_; lean_object* v_env_3132_; lean_object* v_messages_3133_; lean_object* v_scopes_3134_; lean_object* v_usedQuotCtxts_3135_; lean_object* v_nextMacroScope_3136_; lean_object* v_maxRecDepth_3137_; lean_object* v_ngen_3138_; lean_object* v_auxDeclNGen_3139_; lean_object* v_infoState_3140_; lean_object* v_traceState_3141_; lean_object* v_snapshotTasks_3142_; lean_object* v_prevLinterStates_3143_; lean_object* v_codeQualityEntryTasks_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3160_; 
v___x_3129_ = lean_st_ref_take(v___y_3121_);
v_currNamespace_3130_ = lean_ctor_get(v_a_3123_, 2);
lean_inc(v_currNamespace_3130_);
lean_dec(v_a_3123_);
v_openDecls_3131_ = lean_ctor_get(v_a_3125_, 3);
lean_inc(v_openDecls_3131_);
lean_dec(v_a_3125_);
v_env_3132_ = lean_ctor_get(v___x_3129_, 0);
v_messages_3133_ = lean_ctor_get(v___x_3129_, 1);
v_scopes_3134_ = lean_ctor_get(v___x_3129_, 2);
v_usedQuotCtxts_3135_ = lean_ctor_get(v___x_3129_, 3);
v_nextMacroScope_3136_ = lean_ctor_get(v___x_3129_, 4);
v_maxRecDepth_3137_ = lean_ctor_get(v___x_3129_, 5);
v_ngen_3138_ = lean_ctor_get(v___x_3129_, 6);
v_auxDeclNGen_3139_ = lean_ctor_get(v___x_3129_, 7);
v_infoState_3140_ = lean_ctor_get(v___x_3129_, 8);
v_traceState_3141_ = lean_ctor_get(v___x_3129_, 9);
v_snapshotTasks_3142_ = lean_ctor_get(v___x_3129_, 10);
v_prevLinterStates_3143_ = lean_ctor_get(v___x_3129_, 11);
v_codeQualityEntryTasks_3144_ = lean_ctor_get(v___x_3129_, 12);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3146_ = v___x_3129_;
v_isShared_3147_ = v_isSharedCheck_3160_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3144_);
lean_inc(v_prevLinterStates_3143_);
lean_inc(v_snapshotTasks_3142_);
lean_inc(v_traceState_3141_);
lean_inc(v_infoState_3140_);
lean_inc(v_auxDeclNGen_3139_);
lean_inc(v_ngen_3138_);
lean_inc(v_maxRecDepth_3137_);
lean_inc(v_nextMacroScope_3136_);
lean_inc(v_usedQuotCtxts_3135_);
lean_inc(v_scopes_3134_);
lean_inc(v_messages_3133_);
lean_inc(v_env_3132_);
lean_dec(v___x_3129_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3160_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3153_; 
v___x_3148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3148_, 0, v_currNamespace_3130_);
lean_ctor_set(v___x_3148_, 1, v_openDecls_3131_);
v___x_3149_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3148_);
lean_ctor_set(v___x_3149_, 1, v___y_3120_);
lean_inc_ref(v___y_3117_);
lean_inc_ref(v___y_3116_);
v___x_3150_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3150_, 0, v___y_3116_);
lean_ctor_set(v___x_3150_, 1, v___y_3119_);
lean_ctor_set(v___x_3150_, 2, v___y_3114_);
lean_ctor_set(v___x_3150_, 3, v___y_3117_);
lean_ctor_set(v___x_3150_, 4, v___x_3149_);
lean_ctor_set_uint8(v___x_3150_, sizeof(void*)*5, v___y_3115_);
lean_ctor_set_uint8(v___x_3150_, sizeof(void*)*5 + 1, v___y_3118_);
lean_ctor_set_uint8(v___x_3150_, sizeof(void*)*5 + 2, v_isSilent_3109_);
v___x_3151_ = l_Lean_MessageLog_add(v___x_3150_, v_messages_3133_);
if (v_isShared_3147_ == 0)
{
lean_ctor_set(v___x_3146_, 1, v___x_3151_);
v___x_3153_ = v___x_3146_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_env_3132_);
lean_ctor_set(v_reuseFailAlloc_3159_, 1, v___x_3151_);
lean_ctor_set(v_reuseFailAlloc_3159_, 2, v_scopes_3134_);
lean_ctor_set(v_reuseFailAlloc_3159_, 3, v_usedQuotCtxts_3135_);
lean_ctor_set(v_reuseFailAlloc_3159_, 4, v_nextMacroScope_3136_);
lean_ctor_set(v_reuseFailAlloc_3159_, 5, v_maxRecDepth_3137_);
lean_ctor_set(v_reuseFailAlloc_3159_, 6, v_ngen_3138_);
lean_ctor_set(v_reuseFailAlloc_3159_, 7, v_auxDeclNGen_3139_);
lean_ctor_set(v_reuseFailAlloc_3159_, 8, v_infoState_3140_);
lean_ctor_set(v_reuseFailAlloc_3159_, 9, v_traceState_3141_);
lean_ctor_set(v_reuseFailAlloc_3159_, 10, v_snapshotTasks_3142_);
lean_ctor_set(v_reuseFailAlloc_3159_, 11, v_prevLinterStates_3143_);
lean_ctor_set(v_reuseFailAlloc_3159_, 12, v_codeQualityEntryTasks_3144_);
v___x_3153_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3157_; 
v___x_3154_ = lean_st_ref_put(v___y_3121_, v___x_3153_);
v___x_3155_ = lean_box(0);
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 0, v___x_3155_);
v___x_3157_ = v___x_3127_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v___x_3155_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
lean_dec(v_a_3123_);
lean_dec_ref(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3114_);
v_a_3162_ = lean_ctor_get(v___x_3124_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3124_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3124_);
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
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
lean_dec_ref(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3114_);
v_a_3170_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3122_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3122_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
}
v___jp_3178_:
{
lean_object* v_fileName_3184_; lean_object* v_fileMap_3185_; uint8_t v_suppressElabErrors_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3205_; 
v_fileName_3184_ = lean_ctor_get(v___y_3110_, 0);
v_fileMap_3185_ = lean_ctor_get(v___y_3110_, 1);
v_suppressElabErrors_3186_ = lean_ctor_get_uint8(v___y_3110_, sizeof(void*)*10);
v___x_3187_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3107_);
v___x_3188_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_spec__5___redArg(v___x_3187_, v___y_3111_);
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3191_ = v___x_3188_;
v_isShared_3192_ = v_isSharedCheck_3205_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3188_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3205_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
lean_inc_ref_n(v_fileMap_3185_, 2);
v___x_3193_ = l_Lean_FileMap_toPosition(v_fileMap_3185_, v___y_3181_);
lean_dec(v___y_3181_);
v___x_3194_ = l_Lean_FileMap_toPosition(v_fileMap_3185_, v___y_3183_);
lean_dec(v___y_3183_);
v___x_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3194_);
v___x_3196_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
if (v_suppressElabErrors_3186_ == 0)
{
lean_del_object(v___x_3191_);
v___y_3114_ = v___x_3195_;
v___y_3115_ = v___y_3180_;
v___y_3116_ = v_fileName_3184_;
v___y_3117_ = v___x_3196_;
v___y_3118_ = v___y_3182_;
v___y_3119_ = v___x_3193_;
v___y_3120_ = v_a_3189_;
v___y_3121_ = v___y_3111_;
goto v___jp_3113_;
}
else
{
lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___f_3199_; uint8_t v___x_3200_; 
v___x_3197_ = lean_box(v_suppressElabErrors_3186_);
v___x_3198_ = lean_box(v___y_3179_);
v___f_3199_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3199_, 0, v___x_3197_);
lean_closure_set(v___f_3199_, 1, v___x_3198_);
lean_inc(v_a_3189_);
v___x_3200_ = l_Lean_MessageData_hasTag(v___f_3199_, v_a_3189_);
if (v___x_3200_ == 0)
{
lean_object* v___x_3201_; lean_object* v___x_3203_; 
lean_dec_ref_known(v___x_3195_, 1);
lean_dec_ref(v___x_3193_);
lean_dec(v_a_3189_);
v___x_3201_ = lean_box(0);
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 0, v___x_3201_);
v___x_3203_ = v___x_3191_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v___x_3201_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
else
{
lean_del_object(v___x_3191_);
v___y_3114_ = v___x_3195_;
v___y_3115_ = v___y_3180_;
v___y_3116_ = v_fileName_3184_;
v___y_3117_ = v___x_3196_;
v___y_3118_ = v___y_3182_;
v___y_3119_ = v___x_3193_;
v___y_3120_ = v_a_3189_;
v___y_3121_ = v___y_3111_;
goto v___jp_3113_;
}
}
}
}
v___jp_3206_:
{
lean_object* v___x_3212_; 
v___x_3212_ = l_Lean_Syntax_getTailPos_x3f(v___y_3209_, v___y_3208_);
lean_dec(v___y_3209_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_inc(v___y_3211_);
v___y_3179_ = v___y_3207_;
v___y_3180_ = v___y_3208_;
v___y_3181_ = v___y_3211_;
v___y_3182_ = v___y_3210_;
v___y_3183_ = v___y_3211_;
goto v___jp_3178_;
}
else
{
lean_object* v_val_3213_; 
v_val_3213_ = lean_ctor_get(v___x_3212_, 0);
lean_inc(v_val_3213_);
lean_dec_ref_known(v___x_3212_, 1);
v___y_3179_ = v___y_3207_;
v___y_3180_ = v___y_3208_;
v___y_3181_ = v___y_3211_;
v___y_3182_ = v___y_3210_;
v___y_3183_ = v_val_3213_;
goto v___jp_3178_;
}
}
v___jp_3214_:
{
lean_object* v___x_3218_; 
v___x_3218_ = l_Lean_Elab_Command_getRef___redArg(v___y_3110_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v_a_3219_; lean_object* v_ref_3220_; lean_object* v___x_3221_; 
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_a_3219_);
lean_dec_ref_known(v___x_3218_, 1);
v_ref_3220_ = l_Lean_replaceRef(v_ref_3106_, v_a_3219_);
lean_dec(v_a_3219_);
v___x_3221_ = l_Lean_Syntax_getPos_x3f(v_ref_3220_, v___y_3216_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v___x_3222_; 
v___x_3222_ = lean_unsigned_to_nat(0u);
v___y_3207_ = v___y_3215_;
v___y_3208_ = v___y_3216_;
v___y_3209_ = v_ref_3220_;
v___y_3210_ = v___y_3217_;
v___y_3211_ = v___x_3222_;
goto v___jp_3206_;
}
else
{
lean_object* v_val_3223_; 
v_val_3223_ = lean_ctor_get(v___x_3221_, 0);
lean_inc(v_val_3223_);
lean_dec_ref_known(v___x_3221_, 1);
v___y_3207_ = v___y_3215_;
v___y_3208_ = v___y_3216_;
v___y_3209_ = v_ref_3220_;
v___y_3210_ = v___y_3217_;
v___y_3211_ = v_val_3223_;
goto v___jp_3206_;
}
}
else
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3231_; 
lean_dec_ref(v_msgData_3107_);
v_a_3224_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3226_ = v___x_3218_;
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3218_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
if (v_isShared_3227_ == 0)
{
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3224_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
}
v___jp_3233_:
{
if (v___y_3236_ == 0)
{
v___y_3215_ = v___y_3234_;
v___y_3216_ = v___y_3235_;
v___y_3217_ = v_severity_3108_;
goto v___jp_3214_;
}
else
{
v___y_3215_ = v___y_3234_;
v___y_3216_ = v___y_3235_;
v___y_3217_ = v___x_3232_;
goto v___jp_3214_;
}
}
v___jp_3237_:
{
if (v___y_3238_ == 0)
{
lean_object* v___x_3239_; lean_object* v_scopes_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v_opts_3243_; uint8_t v___x_3244_; uint8_t v___x_3245_; 
v___x_3239_ = lean_st_ref_get(v___y_3111_);
v_scopes_3240_ = lean_ctor_get(v___x_3239_, 2);
lean_inc(v_scopes_3240_);
lean_dec(v___x_3239_);
v___x_3241_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3242_ = l_List_head_x21___redArg(v___x_3241_, v_scopes_3240_);
lean_dec(v_scopes_3240_);
v_opts_3243_ = lean_ctor_get(v___x_3242_, 1);
lean_inc_ref(v_opts_3243_);
lean_dec(v___x_3242_);
v___x_3244_ = 1;
v___x_3245_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3108_, v___x_3244_);
if (v___x_3245_ == 0)
{
lean_dec_ref(v_opts_3243_);
v___y_3234_ = v___y_3238_;
v___y_3235_ = v___y_3238_;
v___y_3236_ = v___x_3245_;
goto v___jp_3233_;
}
else
{
lean_object* v___x_3246_; uint8_t v___x_3247_; 
v___x_3246_ = l_Lean_warningAsError;
v___x_3247_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_3243_, v___x_3246_);
lean_dec_ref(v_opts_3243_);
v___y_3234_ = v___y_3238_;
v___y_3235_ = v___y_3238_;
v___y_3236_ = v___x_3247_;
goto v___jp_3233_;
}
}
else
{
lean_object* v___x_3248_; lean_object* v___x_3249_; 
lean_dec_ref(v_msgData_3107_);
v___x_3248_ = lean_box(0);
v___x_3249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3248_);
return v___x_3249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___boxed(lean_object* v_ref_3252_, lean_object* v_msgData_3253_, lean_object* v_severity_3254_, lean_object* v_isSilent_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
uint8_t v_severity_boxed_3259_; uint8_t v_isSilent_boxed_3260_; lean_object* v_res_3261_; 
v_severity_boxed_3259_ = lean_unbox(v_severity_3254_);
v_isSilent_boxed_3260_ = lean_unbox(v_isSilent_3255_);
v_res_3261_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3252_, v_msgData_3253_, v_severity_boxed_3259_, v_isSilent_boxed_3260_, v___y_3256_, v___y_3257_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec(v_ref_3252_);
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(lean_object* v_ref_3262_, lean_object* v_msgData_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_){
_start:
{
uint8_t v___x_3267_; uint8_t v___x_3268_; lean_object* v___x_3269_; 
v___x_3267_ = 0;
v___x_3268_ = 0;
v___x_3269_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3262_, v_msgData_3263_, v___x_3267_, v___x_3268_, v___y_3264_, v___y_3265_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0___boxed(lean_object* v_ref_3270_, lean_object* v_msgData_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
lean_object* v_res_3275_; 
v_res_3275_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3270_, v_msgData_3271_, v___y_3272_, v___y_3273_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v_ref_3270_);
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(lean_object* v___x_3277_, lean_object* v_x_3278_){
_start:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3279_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___closed__0));
v___x_3280_ = lean_string_append(v___x_3279_, v___x_3277_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed(lean_object* v___x_3281_, lean_object* v_x_3282_){
_start:
{
lean_object* v_res_3283_; 
v_res_3283_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(v___x_3281_, v_x_3282_);
lean_dec_ref(v_x_3282_);
lean_dec_ref(v___x_3281_);
return v_res_3283_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__0));
v___x_3286_ = l_Lean_stringToMessageData(v___x_3285_);
return v___x_3286_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3288_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__2));
v___x_3289_ = l_Lean_stringToMessageData(v___x_3288_);
return v___x_3289_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3291_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__4));
v___x_3292_ = l_Lean_stringToMessageData(v___x_3291_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(lean_object* v___x_3293_, uint8_t v___x_3294_, lean_object* v___x_3295_, lean_object* v_insertPos_3296_, lean_object* v_cmdLine_3297_, lean_object* v_ref_3298_, size_t v_sz_3299_, size_t v_i_3300_, lean_object* v_bs_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
uint8_t v___x_3305_; 
v___x_3305_ = lean_usize_dec_lt(v_i_3300_, v_sz_3299_);
if (v___x_3305_ == 0)
{
lean_object* v___x_3306_; 
lean_dec_ref(v___x_3295_);
lean_dec_ref(v___x_3293_);
v___x_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3306_, 0, v_bs_3301_);
return v___x_3306_;
}
else
{
lean_object* v_v_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v_v_3307_ = lean_array_uget(v_bs_3301_, v_i_3300_);
lean_inc(v_v_3307_);
v___x_3308_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppTactic___boxed), 4, 1);
lean_closure_set(v___x_3308_, 0, v_v_3307_);
v___x_3309_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_3308_, v___y_3302_, v___y_3303_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_object* v_a_3310_; lean_object* v___x_3311_; lean_object* v_bs_x27_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___f_3315_; lean_object* v___x_3316_; 
v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
lean_inc(v_a_3310_);
lean_dec_ref_known(v___x_3309_, 1);
v___x_3311_ = lean_unsigned_to_nat(0u);
v_bs_x27_3312_ = lean_array_uset(v_bs_3301_, v_i_3300_, v___x_3311_);
v___x_3313_ = l_Std_Format_defWidth;
v___x_3314_ = l_Std_Format_pretty(v_a_3310_, v___x_3313_, v___x_3311_, v___x_3311_);
lean_inc_ref(v___x_3314_);
v___f_3315_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3315_, 0, v___x_3314_);
lean_inc_ref(v___x_3293_);
v___x_3316_ = lean_string_append(v___x_3293_, v___x_3314_);
lean_dec_ref(v___x_3314_);
if (v___x_3294_ == 0)
{
goto v___jp_3317_;
}
else
{
lean_object* v___x_3328_; lean_object* v_line_3329_; lean_object* v_column_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3365_; 
lean_inc_ref(v___x_3295_);
v___x_3328_ = l_Lean_FileMap_toPosition(v___x_3295_, v_insertPos_3296_);
v_line_3329_ = lean_ctor_get(v___x_3328_, 0);
v_column_3330_ = lean_ctor_get(v___x_3328_, 1);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3332_ = v___x_3328_;
v_isShared_3333_ = v_isSharedCheck_3365_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_column_3330_);
lean_inc(v_line_3329_);
lean_dec(v___x_3328_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3365_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3342_; 
v___x_3334_ = lean_nat_sub(v_line_3329_, v_cmdLine_3297_);
lean_dec(v_line_3329_);
v___x_3335_ = lean_unsigned_to_nat(1u);
v___x_3336_ = lean_nat_add(v___x_3334_, v___x_3335_);
lean_dec(v___x_3334_);
v___x_3337_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1);
lean_inc_ref(v___x_3316_);
v___x_3338_ = l_String_quote(v___x_3316_);
v___x_3339_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3338_);
v___x_3340_ = l_Lean_MessageData_ofFormat(v___x_3339_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set_tag(v___x_3332_, 7);
lean_ctor_set(v___x_3332_, 1, v___x_3340_);
lean_ctor_set(v___x_3332_, 0, v___x_3337_);
v___x_3342_ = v___x_3332_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v___x_3337_);
lean_ctor_set(v_reuseFailAlloc_3364_, 1, v___x_3340_);
v___x_3342_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3343_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3);
v___x_3344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3342_);
lean_ctor_set(v___x_3344_, 1, v___x_3343_);
v___x_3345_ = l_Nat_reprFast(v___x_3336_);
v___x_3346_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3345_);
v___x_3347_ = l_Lean_MessageData_ofFormat(v___x_3346_);
v___x_3348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3344_);
lean_ctor_set(v___x_3348_, 1, v___x_3347_);
v___x_3349_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5);
v___x_3350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3348_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
v___x_3351_ = l_Nat_reprFast(v_column_3330_);
v___x_3352_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3351_);
v___x_3353_ = l_Lean_MessageData_ofFormat(v___x_3352_);
v___x_3354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3350_);
lean_ctor_set(v___x_3354_, 1, v___x_3353_);
v___x_3355_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3298_, v___x_3354_, v___y_3302_, v___y_3303_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_dec_ref_known(v___x_3355_, 1);
goto v___jp_3317_;
}
else
{
lean_object* v_a_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3363_; 
lean_dec_ref(v___x_3316_);
lean_dec_ref(v___f_3315_);
lean_dec_ref(v_bs_x27_3312_);
lean_dec(v_v_3307_);
lean_dec_ref(v___x_3295_);
lean_dec_ref(v___x_3293_);
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3358_ = v___x_3355_;
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_a_3356_);
lean_dec(v___x_3355_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3361_; 
if (v_isShared_3359_ == 0)
{
v___x_3361_ = v___x_3358_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_a_3356_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
}
}
}
}
v___jp_3317_:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; size_t v___x_3324_; size_t v___x_3325_; lean_object* v___x_3326_; 
v___x_3318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3316_);
v___x_3319_ = lean_box(0);
v___x_3320_ = l_Lean_MessageData_ofSyntax(v_v_3307_);
v___x_3321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3320_);
v___x_3322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3322_, 0, v___f_3315_);
v___x_3323_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3318_);
lean_ctor_set(v___x_3323_, 1, v___x_3319_);
lean_ctor_set(v___x_3323_, 2, v___x_3319_);
lean_ctor_set(v___x_3323_, 3, v___x_3319_);
lean_ctor_set(v___x_3323_, 4, v___x_3321_);
lean_ctor_set(v___x_3323_, 5, v___x_3322_);
v___x_3324_ = ((size_t)1ULL);
v___x_3325_ = lean_usize_add(v_i_3300_, v___x_3324_);
v___x_3326_ = lean_array_uset(v_bs_x27_3312_, v_i_3300_, v___x_3323_);
v_i_3300_ = v___x_3325_;
v_bs_3301_ = v___x_3326_;
goto _start;
}
}
else
{
lean_object* v_a_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3373_; 
lean_dec(v_v_3307_);
lean_dec_ref(v_bs_3301_);
lean_dec_ref(v___x_3295_);
lean_dec_ref(v___x_3293_);
v_a_3366_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3368_ = v___x_3309_;
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_a_3366_);
lean_dec(v___x_3309_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3371_; 
if (v_isShared_3369_ == 0)
{
v___x_3371_ = v___x_3368_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_a_3366_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___boxed(lean_object* v___x_3374_, lean_object* v___x_3375_, lean_object* v___x_3376_, lean_object* v_insertPos_3377_, lean_object* v_cmdLine_3378_, lean_object* v_ref_3379_, lean_object* v_sz_3380_, lean_object* v_i_3381_, lean_object* v_bs_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
uint8_t v___x_3850__boxed_3386_; size_t v_sz_boxed_3387_; size_t v_i_boxed_3388_; lean_object* v_res_3389_; 
v___x_3850__boxed_3386_ = lean_unbox(v___x_3375_);
v_sz_boxed_3387_ = lean_unbox_usize(v_sz_3380_);
lean_dec(v_sz_3380_);
v_i_boxed_3388_ = lean_unbox_usize(v_i_3381_);
lean_dec(v_i_3381_);
v_res_3389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3374_, v___x_3850__boxed_3386_, v___x_3376_, v_insertPos_3377_, v_cmdLine_3378_, v_ref_3379_, v_sz_boxed_3387_, v_i_boxed_3388_, v_bs_3382_, v___y_3383_, v___y_3384_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
lean_dec(v_ref_3379_);
lean_dec(v_cmdLine_3378_);
lean_dec(v_insertPos_3377_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(lean_object* v_tacticSeq_3390_, lean_object* v_ref_3391_, lean_object* v_insertPos_3392_, lean_object* v_suggs_3393_, lean_object* v_cmdLine_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_){
_start:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; uint8_t v___x_3400_; 
v___x_3398_ = lean_array_get_size(v_suggs_3393_);
v___x_3399_ = lean_unsigned_to_nat(0u);
v___x_3400_ = lean_nat_dec_eq(v___x_3398_, v___x_3399_);
if (v___x_3400_ == 0)
{
lean_object* v___x_3401_; lean_object* v_fileMap_3402_; lean_object* v_scopes_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v_opts_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; uint8_t v___x_3409_; size_t v_sz_3410_; size_t v___x_3411_; lean_object* v___x_3412_; 
v___x_3401_ = lean_st_ref_get(v_a_3396_);
v_fileMap_3402_ = lean_ctor_get(v_a_3395_, 1);
v_scopes_3403_ = lean_ctor_get(v___x_3401_, 2);
lean_inc(v_scopes_3403_);
lean_dec(v___x_3401_);
v___x_3404_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3405_ = l_List_head_x21___redArg(v___x_3404_, v_scopes_3403_);
lean_dec(v_scopes_3403_);
v_opts_3406_ = lean_ctor_get(v___x_3405_, 1);
lean_inc_ref(v_opts_3406_);
lean_dec(v___x_3405_);
lean_inc_ref_n(v_fileMap_3402_, 2);
v___x_3407_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(v_tacticSeq_3390_, v_fileMap_3402_);
v___x_3408_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_debug_autoTry_showEdits;
v___x_3409_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_3406_, v___x_3408_);
lean_dec_ref(v_opts_3406_);
v_sz_3410_ = lean_array_size(v_suggs_3393_);
v___x_3411_ = ((size_t)0ULL);
v___x_3412_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3407_, v___x_3409_, v_fileMap_3402_, v_insertPos_3392_, v_cmdLine_3394_, v_ref_3391_, v_sz_3410_, v___x_3411_, v_suggs_3393_, v_a_3395_, v_a_3396_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_object* v_a_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; uint8_t v___x_3418_; lean_object* v___x_3419_; lean_object* v___y_3420_; lean_object* v___x_3421_; 
v_a_3413_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_a_3413_);
lean_dec_ref_known(v___x_3412_, 1);
v___x_3414_ = l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default;
v___x_3415_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx(v_insertPos_3392_);
v___x_3416_ = lean_array_get_size(v_a_3413_);
v___x_3417_ = lean_unsigned_to_nat(1u);
v___x_3418_ = lean_nat_dec_eq(v___x_3416_, v___x_3417_);
v___x_3419_ = lean_box(v___x_3418_);
v___y_3420_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed), 9, 6);
lean_closure_set(v___y_3420_, 0, v___x_3419_);
lean_closure_set(v___y_3420_, 1, v___x_3415_);
lean_closure_set(v___y_3420_, 2, v_ref_3391_);
lean_closure_set(v___y_3420_, 3, v_a_3413_);
lean_closure_set(v___y_3420_, 4, v___x_3414_);
lean_closure_set(v___y_3420_, 5, v___x_3399_);
v___x_3421_ = l_Lean_Elab_Command_liftCoreM___redArg(v___y_3420_, v_a_3395_, v_a_3396_);
return v___x_3421_;
}
else
{
lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3429_; 
lean_dec(v_insertPos_3392_);
lean_dec(v_ref_3391_);
v_a_3422_ = lean_ctor_get(v___x_3412_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3424_ = v___x_3412_;
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___x_3412_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3427_; 
if (v_isShared_3425_ == 0)
{
v___x_3427_ = v___x_3424_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_a_3422_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
}
else
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
lean_dec_ref(v_suggs_3393_);
lean_dec(v_insertPos_3392_);
lean_dec(v_ref_3391_);
v___x_3430_ = lean_box(0);
v___x_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3430_);
return v___x_3431_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___boxed(lean_object* v_tacticSeq_3432_, lean_object* v_ref_3433_, lean_object* v_insertPos_3434_, lean_object* v_suggs_3435_, lean_object* v_cmdLine_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_){
_start:
{
lean_object* v_res_3440_; 
v_res_3440_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(v_tacticSeq_3432_, v_ref_3433_, v_insertPos_3434_, v_suggs_3435_, v_cmdLine_3436_, v_a_3437_, v_a_3438_);
lean_dec(v_a_3438_);
lean_dec_ref(v_a_3437_);
lean_dec(v_cmdLine_3436_);
lean_dec(v_tacticSeq_3432_);
return v_res_3440_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(lean_object* v_x_3441_){
_start:
{
uint8_t v___x_3442_; 
v___x_3442_ = 0;
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0___boxed(lean_object* v_x_3443_){
_start:
{
uint8_t v_res_3444_; lean_object* v_r_3445_; 
v_res_3444_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(v_x_3443_);
lean_dec(v_x_3443_);
v_r_3445_ = lean_box(v_res_3444_);
return v_r_3445_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7(void){
_start:
{
lean_object* v___x_3462_; 
v___x_3462_ = l_Array_mkArray0(lean_box(0));
return v___x_3462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(lean_object* v___f_3466_, lean_object* v_ref_3467_, lean_object* v_goal_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_){
_start:
{
lean_object* v_fileName_3474_; lean_object* v_fileMap_3475_; lean_object* v_options_3476_; lean_object* v_currRecDepth_3477_; lean_object* v_maxRecDepth_3478_; lean_object* v_ref_3479_; lean_object* v_currNamespace_3480_; lean_object* v_openDecls_3481_; lean_object* v_initHeartbeats_3482_; lean_object* v_maxHeartbeats_3483_; lean_object* v_quotContext_3484_; lean_object* v_currMacroScope_3485_; uint8_t v_diag_3486_; lean_object* v_cancelTk_x3f_3487_; uint8_t v_suppressElabErrors_3488_; lean_object* v_inheritedTraceOptions_3489_; uint8_t v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; uint8_t v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v_ref_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
v_fileName_3474_ = lean_ctor_get(v___y_3471_, 0);
v_fileMap_3475_ = lean_ctor_get(v___y_3471_, 1);
v_options_3476_ = lean_ctor_get(v___y_3471_, 2);
v_currRecDepth_3477_ = lean_ctor_get(v___y_3471_, 3);
v_maxRecDepth_3478_ = lean_ctor_get(v___y_3471_, 4);
v_ref_3479_ = lean_ctor_get(v___y_3471_, 5);
v_currNamespace_3480_ = lean_ctor_get(v___y_3471_, 6);
v_openDecls_3481_ = lean_ctor_get(v___y_3471_, 7);
v_initHeartbeats_3482_ = lean_ctor_get(v___y_3471_, 8);
v_maxHeartbeats_3483_ = lean_ctor_get(v___y_3471_, 9);
v_quotContext_3484_ = lean_ctor_get(v___y_3471_, 10);
v_currMacroScope_3485_ = lean_ctor_get(v___y_3471_, 11);
v_diag_3486_ = lean_ctor_get_uint8(v___y_3471_, sizeof(void*)*14);
v_cancelTk_x3f_3487_ = lean_ctor_get(v___y_3471_, 12);
v_suppressElabErrors_3488_ = lean_ctor_get_uint8(v___y_3471_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3489_ = lean_ctor_get(v___y_3471_, 13);
v___x_3490_ = 0;
v___x_3491_ = l_Lean_SourceInfo_fromRef(v_ref_3479_, v___x_3490_);
v___x_3492_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__1));
v___x_3493_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__2));
lean_inc_n(v___x_3491_, 3);
v___x_3494_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3491_);
lean_ctor_set(v___x_3494_, 1, v___x_3493_);
v___x_3495_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__4));
v___x_3496_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__6));
v___x_3497_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7);
v___x_3498_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3498_, 0, v___x_3491_);
lean_ctor_set(v___x_3498_, 1, v___x_3496_);
lean_ctor_set(v___x_3498_, 2, v___x_3497_);
v___x_3499_ = l_Lean_Syntax_node1(v___x_3491_, v___x_3495_, v___x_3498_);
v___x_3500_ = l_Lean_Syntax_node2(v___x_3491_, v___x_3492_, v___x_3494_, v___x_3499_);
v___x_3501_ = lean_box(0);
v___x_3502_ = lean_box(0);
v___x_3503_ = 1;
v___x_3504_ = lean_box(1);
v___x_3505_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__5));
v___x_3506_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_3506_, 0, v___x_3501_);
lean_ctor_set(v___x_3506_, 1, v___x_3502_);
lean_ctor_set(v___x_3506_, 2, v___x_3501_);
lean_ctor_set(v___x_3506_, 3, v___f_3466_);
lean_ctor_set(v___x_3506_, 4, v___x_3504_);
lean_ctor_set(v___x_3506_, 5, v___x_3504_);
lean_ctor_set(v___x_3506_, 6, v___x_3501_);
lean_ctor_set(v___x_3506_, 7, v___x_3505_);
lean_ctor_set_uint8(v___x_3506_, sizeof(void*)*8, v___x_3503_);
lean_ctor_set_uint8(v___x_3506_, sizeof(void*)*8 + 1, v___x_3503_);
lean_ctor_set_uint8(v___x_3506_, sizeof(void*)*8 + 2, v___x_3503_);
lean_ctor_set_uint8(v___x_3506_, sizeof(void*)*8 + 3, v___x_3503_);
lean_ctor_set_uint8(v___x_3506_, sizeof(void*)*8 + 4, v___x_3490_);
lean_ctor_set_uint8(v___x_3506_, sizeof(void*)*8 + 5, v___x_3490_);
lean_ctor_set_uint8(v___x_3506_, sizeof(void*)*8 + 6, v___x_3490_);
lean_ctor_set_uint8(v___x_3506_, sizeof(void*)*8 + 7, v___x_3490_);
lean_ctor_set_uint8(v___x_3506_, sizeof(void*)*8 + 8, v___x_3503_);
lean_ctor_set_uint8(v___x_3506_, sizeof(void*)*8 + 9, v___x_3490_);
lean_ctor_set_uint8(v___x_3506_, sizeof(void*)*8 + 10, v___x_3503_);
v___x_3507_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__8));
v_ref_3508_ = l_Lean_replaceRef(v_ref_3467_, v_ref_3479_);
lean_inc_ref(v_inheritedTraceOptions_3489_);
lean_inc(v_cancelTk_x3f_3487_);
lean_inc(v_currMacroScope_3485_);
lean_inc(v_quotContext_3484_);
lean_inc(v_maxHeartbeats_3483_);
lean_inc(v_initHeartbeats_3482_);
lean_inc(v_openDecls_3481_);
lean_inc(v_currNamespace_3480_);
lean_inc(v_maxRecDepth_3478_);
lean_inc(v_currRecDepth_3477_);
lean_inc_ref(v_options_3476_);
lean_inc_ref(v_fileMap_3475_);
lean_inc_ref(v_fileName_3474_);
v___x_3509_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3509_, 0, v_fileName_3474_);
lean_ctor_set(v___x_3509_, 1, v_fileMap_3475_);
lean_ctor_set(v___x_3509_, 2, v_options_3476_);
lean_ctor_set(v___x_3509_, 3, v_currRecDepth_3477_);
lean_ctor_set(v___x_3509_, 4, v_maxRecDepth_3478_);
lean_ctor_set(v___x_3509_, 5, v_ref_3508_);
lean_ctor_set(v___x_3509_, 6, v_currNamespace_3480_);
lean_ctor_set(v___x_3509_, 7, v_openDecls_3481_);
lean_ctor_set(v___x_3509_, 8, v_initHeartbeats_3482_);
lean_ctor_set(v___x_3509_, 9, v_maxHeartbeats_3483_);
lean_ctor_set(v___x_3509_, 10, v_quotContext_3484_);
lean_ctor_set(v___x_3509_, 11, v_currMacroScope_3485_);
lean_ctor_set(v___x_3509_, 12, v_cancelTk_x3f_3487_);
lean_ctor_set(v___x_3509_, 13, v_inheritedTraceOptions_3489_);
lean_ctor_set_uint8(v___x_3509_, sizeof(void*)*14, v_diag_3486_);
lean_ctor_set_uint8(v___x_3509_, sizeof(void*)*14 + 1, v_suppressElabErrors_3488_);
v___x_3510_ = l_Lean_Elab_runTactic(v_goal_3468_, v___x_3500_, v___x_3506_, v___x_3507_, v___y_3469_, v___y_3470_, v___x_3509_, v___y_3472_);
lean_dec_ref_known(v___x_3509_, 14);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3518_; 
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3518_ == 0)
{
lean_object* v_unused_3519_; 
v_unused_3519_ = lean_ctor_get(v___x_3510_, 0);
lean_dec(v_unused_3519_);
v___x_3512_ = v___x_3510_;
v_isShared_3513_ = v_isSharedCheck_3518_;
goto v_resetjp_3511_;
}
else
{
lean_dec(v___x_3510_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3518_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3514_; lean_object* v___x_3516_; 
v___x_3514_ = lean_box(0);
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 0, v___x_3514_);
v___x_3516_ = v___x_3512_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3514_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3546_; 
v_a_3520_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3522_ = v___x_3510_;
v_isShared_3523_ = v_isSharedCheck_3546_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3510_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3546_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3529_; uint8_t v___y_3531_; uint8_t v___y_3541_; uint8_t v___x_3544_; 
lean_inc(v_a_3520_);
v___x_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3529_, 0, v_a_3520_);
v___x_3544_ = l_Lean_Exception_isInterrupt(v_a_3520_);
if (v___x_3544_ == 0)
{
uint8_t v___x_3545_; 
lean_inc(v_a_3520_);
v___x_3545_ = l_Lean_Exception_isRuntime(v_a_3520_);
v___y_3541_ = v___x_3545_;
goto v___jp_3540_;
}
else
{
v___y_3541_ = v___x_3544_;
goto v___jp_3540_;
}
v___jp_3524_:
{
lean_object* v___x_3525_; lean_object* v___x_3527_; 
v___x_3525_ = lean_box(0);
if (v_isShared_3523_ == 0)
{
lean_ctor_set_tag(v___x_3522_, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3525_);
v___x_3527_ = v___x_3522_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3525_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
v___jp_3530_:
{
if (v___y_3531_ == 0)
{
uint8_t v_hasTrace_3532_; 
lean_dec_ref_known(v___x_3529_, 1);
v_hasTrace_3532_ = lean_ctor_get_uint8(v_options_3476_, sizeof(void*)*1);
if (v_hasTrace_3532_ == 0)
{
lean_dec(v_a_3520_);
goto v___jp_3524_;
}
else
{
lean_object* v___x_3533_; lean_object* v___x_3534_; uint8_t v___x_3535_; 
v___x_3533_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3534_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_3535_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3489_, v_options_3476_, v___x_3534_);
if (v___x_3535_ == 0)
{
lean_dec(v_a_3520_);
goto v___jp_3524_;
}
else
{
lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; 
lean_del_object(v___x_3522_);
v___x_3536_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_3537_ = l_Lean_Exception_toMessageData(v_a_3520_);
v___x_3538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3536_);
lean_ctor_set(v___x_3538_, 1, v___x_3537_);
v___x_3539_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_3533_, v___x_3538_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
return v___x_3539_;
}
}
}
else
{
lean_del_object(v___x_3522_);
lean_dec(v_a_3520_);
return v___x_3529_;
}
}
v___jp_3540_:
{
if (v___y_3541_ == 0)
{
uint8_t v___x_3542_; 
v___x_3542_ = l_Lean_Exception_isInterrupt(v_a_3520_);
if (v___x_3542_ == 0)
{
uint8_t v___x_3543_; 
lean_inc(v_a_3520_);
v___x_3543_ = l_Lean_Exception_isMaxRecDepth(v_a_3520_);
v___y_3531_ = v___x_3543_;
goto v___jp_3530_;
}
else
{
v___y_3531_ = v___x_3542_;
goto v___jp_3530_;
}
}
else
{
lean_del_object(v___x_3522_);
lean_dec(v_a_3520_);
return v___x_3529_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___boxed(lean_object* v___f_3547_, lean_object* v_ref_3548_, lean_object* v_goal_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
lean_object* v_res_3555_; 
v_res_3555_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(v___f_3547_, v_ref_3548_, v_goal_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec(v_ref_3548_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(lean_object* v_c_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_){
_start:
{
lean_object* v_mctx_3561_; lean_object* v_ref_3562_; lean_object* v_env_3563_; lean_object* v_opts_3564_; lean_object* v_namingCtx_3565_; lean_object* v_goal_3566_; lean_object* v_decls_3567_; lean_object* v___x_3568_; 
v_mctx_3561_ = lean_ctor_get(v_c_3557_, 3);
lean_inc_ref(v_mctx_3561_);
v_ref_3562_ = lean_ctor_get(v_c_3557_, 1);
lean_inc(v_ref_3562_);
v_env_3563_ = lean_ctor_get(v_c_3557_, 2);
lean_inc_ref(v_env_3563_);
v_opts_3564_ = lean_ctor_get(v_c_3557_, 4);
lean_inc_ref(v_opts_3564_);
v_namingCtx_3565_ = lean_ctor_get(v_c_3557_, 5);
lean_inc_ref(v_namingCtx_3565_);
v_goal_3566_ = lean_ctor_get(v_c_3557_, 6);
lean_inc(v_goal_3566_);
lean_dec_ref(v_c_3557_);
v_decls_3567_ = lean_ctor_get(v_mctx_3561_, 5);
v___x_3568_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_decls_3567_, v_goal_3566_);
if (lean_obj_tag(v___x_3568_) == 1)
{
lean_object* v_val_3569_; lean_object* v_lctx_3570_; lean_object* v___f_3571_; lean_object* v___f_3572_; lean_object* v___x_3573_; 
v_val_3569_ = lean_ctor_get(v___x_3568_, 0);
lean_inc(v_val_3569_);
lean_dec_ref_known(v___x_3568_, 1);
v_lctx_3570_ = lean_ctor_get(v_val_3569_, 1);
lean_inc_ref(v_lctx_3570_);
lean_dec(v_val_3569_);
v___f_3571_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___closed__0));
v___f_3572_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___boxed), 8, 3);
lean_closure_set(v___f_3572_, 0, v___f_3571_);
lean_closure_set(v___f_3572_, 1, v_ref_3562_);
lean_closure_set(v___f_3572_, 2, v_goal_3566_);
v___x_3573_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_3563_, v_mctx_3561_, v_lctx_3570_, v_opts_3564_, v_namingCtx_3565_, v___f_3572_, v_a_3558_, v_a_3559_);
lean_dec_ref(v_namingCtx_3565_);
return v___x_3573_;
}
else
{
lean_object* v___x_3574_; lean_object* v___x_3575_; 
lean_dec(v___x_3568_);
lean_dec(v_goal_3566_);
lean_dec_ref(v_namingCtx_3565_);
lean_dec_ref(v_opts_3564_);
lean_dec_ref(v_env_3563_);
lean_dec(v_ref_3562_);
lean_dec_ref(v_mctx_3561_);
v___x_3574_ = lean_box(0);
v___x_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3574_);
return v___x_3575_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___boxed(lean_object* v_c_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_){
_start:
{
lean_object* v_res_3580_; 
v_res_3580_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(v_c_3576_, v_a_3577_, v_a_3578_);
lean_dec(v_a_3578_);
lean_dec_ref(v_a_3577_);
return v_res_3580_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(lean_object* v___x_3581_, lean_object* v_val_3582_, lean_object* v_as_3583_, size_t v_i_3584_, size_t v_stop_3585_){
_start:
{
uint8_t v___x_3590_; uint8_t v___x_3591_; 
v___x_3590_ = 0;
v___x_3591_ = lean_usize_dec_eq(v_i_3584_, v_stop_3585_);
if (v___x_3591_ == 0)
{
lean_object* v___x_3592_; lean_object* v_pos_3593_; uint8_t v_severity_3594_; lean_object* v_data_3595_; lean_object* v___f_3596_; uint8_t v___x_3597_; lean_object* v___x_3598_; uint8_t v___x_3599_; uint8_t v___y_3601_; 
v___x_3592_ = lean_array_uget_borrowed(v_as_3583_, v_i_3584_);
v_pos_3593_ = lean_ctor_get(v___x_3592_, 1);
v_severity_3594_ = lean_ctor_get_uint8(v___x_3592_, sizeof(void*)*5 + 1);
v_data_3595_ = lean_ctor_get(v___x_3592_, 4);
v___f_3596_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__0));
v___x_3597_ = 1;
lean_inc_ref(v_pos_3593_);
v___x_3598_ = l_Lean_FileMap_ofPosition(v___x_3581_, v_pos_3593_);
v___x_3599_ = l_Lean_Syntax_Range_contains(v_val_3582_, v___x_3598_, v___x_3597_);
lean_dec(v___x_3598_);
if (v_severity_3594_ == 2)
{
v___y_3601_ = v___x_3597_;
goto v___jp_3600_;
}
else
{
v___y_3601_ = v___x_3590_;
goto v___jp_3600_;
}
v___jp_3600_:
{
if (v___x_3599_ == 0)
{
goto v___jp_3586_;
}
else
{
if (v___y_3601_ == 0)
{
goto v___jp_3586_;
}
else
{
uint8_t v___x_3602_; 
lean_inc(v_data_3595_);
v___x_3602_ = l_Lean_MessageData_hasTag(v___f_3596_, v_data_3595_);
if (v___x_3602_ == 0)
{
return v___x_3597_;
}
else
{
goto v___jp_3586_;
}
}
}
}
}
else
{
return v___x_3590_;
}
v___jp_3586_:
{
size_t v___x_3587_; size_t v___x_3588_; 
v___x_3587_ = ((size_t)1ULL);
v___x_3588_ = lean_usize_add(v_i_3584_, v___x_3587_);
v_i_3584_ = v___x_3588_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1___boxed(lean_object* v___x_3603_, lean_object* v_val_3604_, lean_object* v_as_3605_, lean_object* v_i_3606_, lean_object* v_stop_3607_){
_start:
{
size_t v_i_boxed_3608_; size_t v_stop_boxed_3609_; uint8_t v_res_3610_; lean_object* v_r_3611_; 
v_i_boxed_3608_ = lean_unbox_usize(v_i_3606_);
lean_dec(v_i_3606_);
v_stop_boxed_3609_ = lean_unbox_usize(v_stop_3607_);
lean_dec(v_stop_3607_);
v_res_3610_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3603_, v_val_3604_, v_as_3605_, v_i_boxed_3608_, v_stop_boxed_3609_);
lean_dec_ref(v_as_3605_);
lean_dec_ref(v_val_3604_);
lean_dec_ref(v___x_3603_);
v_r_3611_ = lean_box(v_res_3610_);
return v_r_3611_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(lean_object* v___x_3612_, lean_object* v_val_3613_, lean_object* v_x_3614_){
_start:
{
if (lean_obj_tag(v_x_3614_) == 0)
{
lean_object* v_cs_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; uint8_t v___x_3618_; 
v_cs_3615_ = lean_ctor_get(v_x_3614_, 0);
v___x_3616_ = lean_unsigned_to_nat(0u);
v___x_3617_ = lean_array_get_size(v_cs_3615_);
v___x_3618_ = lean_nat_dec_lt(v___x_3616_, v___x_3617_);
if (v___x_3618_ == 0)
{
return v___x_3618_;
}
else
{
if (v___x_3618_ == 0)
{
return v___x_3618_;
}
else
{
size_t v___x_3619_; size_t v___x_3620_; uint8_t v___x_3621_; 
v___x_3619_ = ((size_t)0ULL);
v___x_3620_ = lean_usize_of_nat(v___x_3617_);
v___x_3621_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3612_, v_val_3613_, v_cs_3615_, v___x_3619_, v___x_3620_);
return v___x_3621_;
}
}
}
else
{
lean_object* v_vs_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; uint8_t v___x_3625_; 
v_vs_3622_ = lean_ctor_get(v_x_3614_, 0);
v___x_3623_ = lean_unsigned_to_nat(0u);
v___x_3624_ = lean_array_get_size(v_vs_3622_);
v___x_3625_ = lean_nat_dec_lt(v___x_3623_, v___x_3624_);
if (v___x_3625_ == 0)
{
return v___x_3625_;
}
else
{
if (v___x_3625_ == 0)
{
return v___x_3625_;
}
else
{
size_t v___x_3626_; size_t v___x_3627_; uint8_t v___x_3628_; 
v___x_3626_ = ((size_t)0ULL);
v___x_3627_ = lean_usize_of_nat(v___x_3624_);
v___x_3628_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3612_, v_val_3613_, v_vs_3622_, v___x_3626_, v___x_3627_);
return v___x_3628_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(lean_object* v___x_3629_, lean_object* v_val_3630_, lean_object* v_as_3631_, size_t v_i_3632_, size_t v_stop_3633_){
_start:
{
uint8_t v___x_3634_; 
v___x_3634_ = lean_usize_dec_eq(v_i_3632_, v_stop_3633_);
if (v___x_3634_ == 0)
{
lean_object* v___x_3635_; uint8_t v___x_3636_; 
v___x_3635_ = lean_array_uget_borrowed(v_as_3631_, v_i_3632_);
v___x_3636_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3629_, v_val_3630_, v___x_3635_);
if (v___x_3636_ == 0)
{
size_t v___x_3637_; size_t v___x_3638_; 
v___x_3637_ = ((size_t)1ULL);
v___x_3638_ = lean_usize_add(v_i_3632_, v___x_3637_);
v_i_3632_ = v___x_3638_;
goto _start;
}
else
{
return v___x_3636_;
}
}
else
{
uint8_t v___x_3640_; 
v___x_3640_ = 0;
return v___x_3640_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3641_, lean_object* v_val_3642_, lean_object* v_as_3643_, lean_object* v_i_3644_, lean_object* v_stop_3645_){
_start:
{
size_t v_i_boxed_3646_; size_t v_stop_boxed_3647_; uint8_t v_res_3648_; lean_object* v_r_3649_; 
v_i_boxed_3646_ = lean_unbox_usize(v_i_3644_);
lean_dec(v_i_3644_);
v_stop_boxed_3647_ = lean_unbox_usize(v_stop_3645_);
lean_dec(v_stop_3645_);
v_res_3648_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3641_, v_val_3642_, v_as_3643_, v_i_boxed_3646_, v_stop_boxed_3647_);
lean_dec_ref(v_as_3643_);
lean_dec_ref(v_val_3642_);
lean_dec_ref(v___x_3641_);
v_r_3649_ = lean_box(v_res_3648_);
return v_r_3649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0___boxed(lean_object* v___x_3650_, lean_object* v_val_3651_, lean_object* v_x_3652_){
_start:
{
uint8_t v_res_3653_; lean_object* v_r_3654_; 
v_res_3653_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3650_, v_val_3651_, v_x_3652_);
lean_dec_ref(v_x_3652_);
lean_dec_ref(v_val_3651_);
lean_dec_ref(v___x_3650_);
v_r_3654_ = lean_box(v_res_3653_);
return v_r_3654_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(lean_object* v___x_3655_, lean_object* v_val_3656_, lean_object* v_t_3657_){
_start:
{
lean_object* v_root_3658_; lean_object* v_tail_3659_; uint8_t v___x_3660_; 
v_root_3658_ = lean_ctor_get(v_t_3657_, 0);
v_tail_3659_ = lean_ctor_get(v_t_3657_, 1);
v___x_3660_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3655_, v_val_3656_, v_root_3658_);
if (v___x_3660_ == 0)
{
lean_object* v___x_3661_; lean_object* v___x_3662_; uint8_t v___x_3663_; 
v___x_3661_ = lean_unsigned_to_nat(0u);
v___x_3662_ = lean_array_get_size(v_tail_3659_);
v___x_3663_ = lean_nat_dec_lt(v___x_3661_, v___x_3662_);
if (v___x_3663_ == 0)
{
return v___x_3663_;
}
else
{
if (v___x_3663_ == 0)
{
return v___x_3663_;
}
else
{
size_t v___x_3664_; size_t v___x_3665_; uint8_t v___x_3666_; 
v___x_3664_ = ((size_t)0ULL);
v___x_3665_ = lean_usize_of_nat(v___x_3662_);
v___x_3666_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3655_, v_val_3656_, v_tail_3659_, v___x_3664_, v___x_3665_);
return v___x_3666_;
}
}
}
else
{
return v___x_3660_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0___boxed(lean_object* v___x_3667_, lean_object* v_val_3668_, lean_object* v_t_3669_){
_start:
{
uint8_t v_res_3670_; lean_object* v_r_3671_; 
v_res_3670_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v___x_3667_, v_val_3668_, v_t_3669_);
lean_dec_ref(v_t_3669_);
lean_dec_ref(v_val_3668_);
lean_dec_ref(v___x_3667_);
v_r_3671_ = lean_box(v_res_3670_);
return v_r_3671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(lean_object* v_stx_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_){
_start:
{
uint8_t v___x_3676_; lean_object* v___x_3677_; 
v___x_3676_ = 0;
v___x_3677_ = l_Lean_Syntax_getRange_x3f(v_stx_3672_, v___x_3676_);
if (lean_obj_tag(v___x_3677_) == 1)
{
lean_object* v_val_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3691_; 
v_val_3678_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3680_ = v___x_3677_;
v_isShared_3681_ = v_isSharedCheck_3691_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_val_3678_);
lean_dec(v___x_3677_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3691_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3682_; lean_object* v_fileMap_3683_; lean_object* v_messages_3684_; lean_object* v___x_3685_; uint8_t v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3689_; 
v___x_3682_ = lean_st_ref_get(v_a_3674_);
v_fileMap_3683_ = lean_ctor_get(v_a_3673_, 1);
v_messages_3684_ = lean_ctor_get(v___x_3682_, 1);
lean_inc_ref(v_messages_3684_);
lean_dec(v___x_3682_);
v___x_3685_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_3684_);
v___x_3686_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v_fileMap_3683_, v_val_3678_, v___x_3685_);
lean_dec_ref(v___x_3685_);
lean_dec(v_val_3678_);
v___x_3687_ = lean_box(v___x_3686_);
if (v_isShared_3681_ == 0)
{
lean_ctor_set_tag(v___x_3680_, 0);
lean_ctor_set(v___x_3680_, 0, v___x_3687_);
v___x_3689_ = v___x_3680_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v___x_3687_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
}
else
{
lean_object* v___x_3692_; lean_object* v___x_3693_; 
lean_dec(v___x_3677_);
v___x_3692_ = lean_box(v___x_3676_);
v___x_3693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3692_);
return v___x_3693_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError___boxed(lean_object* v_stx_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_){
_start:
{
lean_object* v_res_3698_; 
v_res_3698_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(v_stx_3694_, v_a_3695_, v_a_3696_);
lean_dec(v_a_3696_);
lean_dec_ref(v_a_3695_);
lean_dec(v_stx_3694_);
return v_res_3698_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(lean_object* v_tree_3699_, lean_object* v_fileMap_3700_, lean_object* v_c_3701_){
_start:
{
lean_object* v___y_3703_; lean_object* v_kind_3707_; lean_object* v_ref_3708_; lean_object* v___y_3710_; 
v_kind_3707_ = lean_ctor_get(v_c_3701_, 0);
lean_inc(v_kind_3707_);
v_ref_3708_ = lean_ctor_get(v_c_3701_, 1);
lean_inc(v_ref_3708_);
lean_dec_ref(v_c_3701_);
if (lean_obj_tag(v_kind_3707_) == 0)
{
lean_object* v_insertPos_3726_; 
lean_dec(v_ref_3708_);
v_insertPos_3726_ = lean_ctor_get(v_kind_3707_, 1);
lean_inc(v_insertPos_3726_);
v___y_3710_ = v_insertPos_3726_;
goto v___jp_3709_;
}
else
{
uint8_t v___x_3727_; lean_object* v___x_3728_; 
v___x_3727_ = 0;
v___x_3728_ = l_Lean_Syntax_getPos_x3f(v_ref_3708_, v___x_3727_);
lean_dec(v_ref_3708_);
if (lean_obj_tag(v___x_3728_) == 0)
{
lean_object* v___x_3729_; 
v___x_3729_ = lean_unsigned_to_nat(0u);
v___y_3710_ = v___x_3729_;
goto v___jp_3709_;
}
else
{
lean_object* v_val_3730_; 
v_val_3730_ = lean_ctor_get(v___x_3728_, 0);
lean_inc(v_val_3730_);
lean_dec_ref_known(v___x_3728_, 1);
v___y_3710_ = v_val_3730_;
goto v___jp_3709_;
}
}
v___jp_3702_:
{
lean_object* v___x_3704_; lean_object* v___x_3705_; uint8_t v___x_3706_; 
v___x_3704_ = l_List_lengthTR___redArg(v___y_3703_);
lean_dec(v___y_3703_);
v___x_3705_ = lean_unsigned_to_nat(1u);
v___x_3706_ = lean_nat_dec_eq(v___x_3704_, v___x_3705_);
lean_dec(v___x_3704_);
return v___x_3706_;
}
v___jp_3709_:
{
lean_object* v___x_3711_; 
v___x_3711_ = l_Lean_Elab_InfoTree_goalsAt_x3f(v_fileMap_3700_, v_tree_3699_, v___y_3710_);
if (lean_obj_tag(v___x_3711_) == 1)
{
lean_object* v_tail_3712_; 
v_tail_3712_ = lean_ctor_get(v___x_3711_, 1);
lean_inc(v_tail_3712_);
if (lean_obj_tag(v_tail_3712_) == 0)
{
if (lean_obj_tag(v_kind_3707_) == 0)
{
lean_object* v_head_3713_; lean_object* v_tacticSeq_3714_; uint8_t v___x_3715_; lean_object* v___x_3716_; 
v_head_3713_ = lean_ctor_get(v___x_3711_, 0);
lean_inc(v_head_3713_);
lean_dec_ref_known(v___x_3711_, 2);
v_tacticSeq_3714_ = lean_ctor_get(v_kind_3707_, 0);
lean_inc(v_tacticSeq_3714_);
lean_dec_ref_known(v_kind_3707_, 2);
v___x_3715_ = 0;
v___x_3716_ = l_Lean_Syntax_getPos_x3f(v_tacticSeq_3714_, v___x_3715_);
lean_dec(v_tacticSeq_3714_);
if (lean_obj_tag(v___x_3716_) == 0)
{
lean_object* v_tacticInfo_3717_; lean_object* v_goalsBefore_3718_; 
v_tacticInfo_3717_ = lean_ctor_get(v_head_3713_, 1);
lean_inc_ref(v_tacticInfo_3717_);
lean_dec(v_head_3713_);
v_goalsBefore_3718_ = lean_ctor_get(v_tacticInfo_3717_, 2);
lean_inc(v_goalsBefore_3718_);
lean_dec_ref(v_tacticInfo_3717_);
v___y_3703_ = v_goalsBefore_3718_;
goto v___jp_3702_;
}
else
{
lean_object* v_tacticInfo_3719_; lean_object* v_goalsAfter_3720_; 
lean_dec_ref_known(v___x_3716_, 1);
v_tacticInfo_3719_ = lean_ctor_get(v_head_3713_, 1);
lean_inc_ref(v_tacticInfo_3719_);
lean_dec(v_head_3713_);
v_goalsAfter_3720_ = lean_ctor_get(v_tacticInfo_3719_, 4);
lean_inc(v_goalsAfter_3720_);
lean_dec_ref(v_tacticInfo_3719_);
v___y_3703_ = v_goalsAfter_3720_;
goto v___jp_3702_;
}
}
else
{
lean_object* v_head_3721_; lean_object* v_tacticInfo_3722_; lean_object* v_goalsBefore_3723_; 
v_head_3721_ = lean_ctor_get(v___x_3711_, 0);
lean_inc(v_head_3721_);
lean_dec_ref_known(v___x_3711_, 2);
v_tacticInfo_3722_ = lean_ctor_get(v_head_3721_, 1);
lean_inc_ref(v_tacticInfo_3722_);
lean_dec(v_head_3721_);
v_goalsBefore_3723_ = lean_ctor_get(v_tacticInfo_3722_, 2);
lean_inc(v_goalsBefore_3723_);
lean_dec_ref(v_tacticInfo_3722_);
v___y_3703_ = v_goalsBefore_3723_;
goto v___jp_3702_;
}
}
else
{
uint8_t v___x_3724_; 
lean_dec(v_tail_3712_);
lean_dec_ref_known(v___x_3711_, 2);
lean_dec(v_kind_3707_);
v___x_3724_ = 0;
return v___x_3724_;
}
}
else
{
uint8_t v___x_3725_; 
lean_dec(v___x_3711_);
lean_dec(v_kind_3707_);
v___x_3725_ = 0;
return v___x_3725_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos___boxed(lean_object* v_tree_3731_, lean_object* v_fileMap_3732_, lean_object* v_c_3733_){
_start:
{
uint8_t v_res_3734_; lean_object* v_r_3735_; 
v_res_3734_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(v_tree_3731_, v_fileMap_3732_, v_c_3733_);
v_r_3735_ = lean_box(v_res_3734_);
return v_r_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(lean_object* v___y_3736_){
_start:
{
lean_object* v___x_3738_; lean_object* v_infoState_3739_; lean_object* v_trees_3740_; lean_object* v___x_3741_; 
v___x_3738_ = lean_st_ref_get(v___y_3736_);
v_infoState_3739_ = lean_ctor_get(v___x_3738_, 8);
lean_inc_ref(v_infoState_3739_);
lean_dec(v___x_3738_);
v_trees_3740_ = lean_ctor_get(v_infoState_3739_, 2);
lean_inc_ref(v_trees_3740_);
lean_dec_ref(v_infoState_3739_);
v___x_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3741_, 0, v_trees_3740_);
return v___x_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg___boxed(lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
lean_object* v_res_3744_; 
v_res_3744_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_3742_);
lean_dec(v___y_3742_);
return v_res_3744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
lean_object* v___x_3748_; 
v___x_3748_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_3746_);
return v___x_3748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___boxed(lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_){
_start:
{
lean_object* v_res_3752_; 
v_res_3752_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(v___y_3749_, v___y_3750_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
return v_res_3752_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3754_; lean_object* v___x_3755_; 
v___x_3754_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__0));
v___x_3755_ = l_Lean_stringToMessageData(v___x_3754_);
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(lean_object* v_tree_3756_, lean_object* v___x_3757_, lean_object* v___x_3758_, lean_object* v_as_3759_, size_t v_sz_3760_, size_t v_i_3761_, lean_object* v_b_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
lean_object* v_a_3767_; uint8_t v___x_3771_; 
v___x_3771_ = lean_usize_dec_lt(v_i_3761_, v_sz_3760_);
if (v___x_3771_ == 0)
{
lean_object* v___x_3772_; 
lean_dec_ref(v___x_3757_);
lean_dec_ref(v_tree_3756_);
v___x_3772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3772_, 0, v_b_3762_);
return v___x_3772_;
}
else
{
lean_object* v___x_3773_; lean_object* v_a_3774_; uint8_t v___x_3775_; 
v___x_3773_ = lean_box(0);
v_a_3774_ = lean_array_uget_borrowed(v_as_3759_, v_i_3761_);
lean_inc(v_a_3774_);
lean_inc_ref(v___x_3757_);
lean_inc_ref(v_tree_3756_);
v___x_3775_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(v_tree_3756_, v___x_3757_, v_a_3774_);
if (v___x_3775_ == 0)
{
lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v_scopes_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v_opts_3782_; uint8_t v_hasTrace_3783_; 
v___x_3776_ = l_Lean_inheritedTraceOptions;
v___x_3777_ = lean_st_ref_get(v___x_3776_);
v___x_3778_ = lean_st_ref_get(v___y_3764_);
v_scopes_3779_ = lean_ctor_get(v___x_3778_, 2);
lean_inc(v_scopes_3779_);
lean_dec(v___x_3778_);
v___x_3780_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3781_ = l_List_head_x21___redArg(v___x_3780_, v_scopes_3779_);
lean_dec(v_scopes_3779_);
v_opts_3782_ = lean_ctor_get(v___x_3781_, 1);
lean_inc_ref(v_opts_3782_);
lean_dec(v___x_3781_);
v_hasTrace_3783_ = lean_ctor_get_uint8(v_opts_3782_, sizeof(void*)*1);
if (v_hasTrace_3783_ == 0)
{
lean_dec_ref(v_opts_3782_);
lean_dec(v___x_3777_);
v_a_3767_ = v___x_3773_;
goto v___jp_3766_;
}
else
{
lean_object* v___x_3784_; lean_object* v___x_3785_; uint8_t v___x_3786_; 
v___x_3784_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3785_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_3786_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3777_, v_opts_3782_, v___x_3785_);
lean_dec_ref(v_opts_3782_);
lean_dec(v___x_3777_);
if (v___x_3786_ == 0)
{
v_a_3767_ = v___x_3773_;
goto v___jp_3766_;
}
else
{
lean_object* v___x_3787_; lean_object* v___x_3788_; 
v___x_3787_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1);
v___x_3788_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_3784_, v___x_3787_, v___y_3763_, v___y_3764_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_dec_ref_known(v___x_3788_, 1);
v_a_3767_ = v___x_3773_;
goto v___jp_3766_;
}
else
{
lean_dec_ref(v___x_3757_);
lean_dec_ref(v_tree_3756_);
return v___x_3788_;
}
}
}
}
else
{
lean_object* v_kind_3789_; 
v_kind_3789_ = lean_ctor_get(v_a_3774_, 0);
if (lean_obj_tag(v_kind_3789_) == 0)
{
lean_object* v_ref_3790_; lean_object* v_tacticSeq_3791_; lean_object* v_insertPos_3792_; lean_object* v___x_3793_; 
v_ref_3790_ = lean_ctor_get(v_a_3774_, 1);
v_tacticSeq_3791_ = lean_ctor_get(v_kind_3789_, 0);
v_insertPos_3792_ = lean_ctor_get(v_kind_3789_, 1);
lean_inc(v_a_3774_);
v___x_3793_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(v_a_3774_, v___y_3763_, v___y_3764_);
if (lean_obj_tag(v___x_3793_) == 0)
{
lean_object* v_a_3794_; lean_object* v___x_3795_; 
v_a_3794_ = lean_ctor_get(v___x_3793_, 0);
lean_inc(v_a_3794_);
lean_dec_ref_known(v___x_3793_, 1);
lean_inc(v_insertPos_3792_);
lean_inc(v_ref_3790_);
v___x_3795_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(v_tacticSeq_3791_, v_ref_3790_, v_insertPos_3792_, v_a_3794_, v___x_3758_, v___y_3763_, v___y_3764_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_dec_ref_known(v___x_3795_, 1);
v_a_3767_ = v___x_3773_;
goto v___jp_3766_;
}
else
{
lean_dec_ref(v___x_3757_);
lean_dec_ref(v_tree_3756_);
return v___x_3795_;
}
}
else
{
lean_object* v_a_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3803_; 
lean_dec_ref(v___x_3757_);
lean_dec_ref(v_tree_3756_);
v_a_3796_ = lean_ctor_get(v___x_3793_, 0);
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3798_ = v___x_3793_;
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_a_3796_);
lean_dec(v___x_3793_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v___x_3801_; 
if (v_isShared_3799_ == 0)
{
v___x_3801_ = v___x_3798_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_a_3796_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
}
}
else
{
lean_object* v___x_3804_; 
lean_inc(v_a_3774_);
v___x_3804_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(v_a_3774_, v___y_3763_, v___y_3764_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_dec_ref_known(v___x_3804_, 1);
v_a_3767_ = v___x_3773_;
goto v___jp_3766_;
}
else
{
lean_dec_ref(v___x_3757_);
lean_dec_ref(v_tree_3756_);
return v___x_3804_;
}
}
}
}
v___jp_3766_:
{
size_t v___x_3768_; size_t v___x_3769_; 
v___x_3768_ = ((size_t)1ULL);
v___x_3769_ = lean_usize_add(v_i_3761_, v___x_3768_);
v_i_3761_ = v___x_3769_;
v_b_3762_ = v_a_3767_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___boxed(lean_object* v_tree_3805_, lean_object* v___x_3806_, lean_object* v___x_3807_, lean_object* v_as_3808_, lean_object* v_sz_3809_, lean_object* v_i_3810_, lean_object* v_b_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_){
_start:
{
size_t v_sz_boxed_3815_; size_t v_i_boxed_3816_; lean_object* v_res_3817_; 
v_sz_boxed_3815_ = lean_unbox_usize(v_sz_3809_);
lean_dec(v_sz_3809_);
v_i_boxed_3816_ = lean_unbox_usize(v_i_3810_);
lean_dec(v_i_3810_);
v_res_3817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_tree_3805_, v___x_3806_, v___x_3807_, v_as_3808_, v_sz_boxed_3815_, v_i_boxed_3816_, v_b_3811_, v___y_3812_, v___y_3813_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
lean_dec_ref(v_as_3808_);
lean_dec(v___x_3807_);
return v_res_3817_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3822_; lean_object* v___x_3823_; 
v___x_3822_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__1));
v___x_3823_ = l_Lean_stringToMessageData(v___x_3822_);
return v___x_3823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(lean_object* v_stx_3824_, lean_object* v___x_3825_, lean_object* v___x_3826_, lean_object* v___x_3827_, lean_object* v___x_3828_, lean_object* v_as_3829_, size_t v_sz_3830_, size_t v_i_3831_, lean_object* v_b_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_){
_start:
{
uint8_t v___x_3836_; 
v___x_3836_ = lean_usize_dec_lt(v_i_3831_, v_sz_3830_);
if (v___x_3836_ == 0)
{
lean_object* v___x_3837_; 
lean_dec_ref(v___x_3827_);
lean_dec(v_stx_3824_);
v___x_3837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3837_, 0, v_b_3832_);
return v___x_3837_;
}
else
{
lean_object* v_a_3838_; lean_object* v___x_3839_; 
lean_dec_ref(v_b_3832_);
v_a_3838_ = lean_array_uget_borrowed(v_as_3829_, v_i_3831_);
lean_inc(v_a_3838_);
lean_inc(v_stx_3824_);
v___x_3839_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3824_, v___x_3825_, v_a_3838_, v___x_3826_, v___y_3833_, v___y_3834_);
if (lean_obj_tag(v___x_3839_) == 0)
{
lean_object* v_a_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v_scopes_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v_opts_3847_; uint8_t v_hasTrace_3848_; lean_object* v___x_3849_; lean_object* v___y_3851_; lean_object* v___y_3852_; 
v_a_3840_ = lean_ctor_get(v___x_3839_, 0);
lean_inc(v_a_3840_);
lean_dec_ref_known(v___x_3839_, 1);
v___x_3841_ = l_Lean_inheritedTraceOptions;
v___x_3842_ = lean_st_ref_get(v___x_3841_);
v___x_3843_ = lean_st_ref_get(v___y_3834_);
v_scopes_3844_ = lean_ctor_get(v___x_3843_, 2);
lean_inc(v_scopes_3844_);
lean_dec(v___x_3843_);
v___x_3845_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3846_ = l_List_head_x21___redArg(v___x_3845_, v_scopes_3844_);
lean_dec(v_scopes_3844_);
v_opts_3847_ = lean_ctor_get(v___x_3846_, 1);
lean_inc_ref(v_opts_3847_);
lean_dec(v___x_3846_);
v_hasTrace_3848_ = lean_ctor_get_uint8(v_opts_3847_, sizeof(void*)*1);
v___x_3849_ = lean_box(0);
if (v_hasTrace_3848_ == 0)
{
lean_dec_ref(v_opts_3847_);
lean_dec(v___x_3842_);
v___y_3851_ = v___y_3833_;
v___y_3852_ = v___y_3834_;
goto v___jp_3850_;
}
else
{
lean_object* v___x_3868_; lean_object* v___x_3869_; uint8_t v___x_3870_; 
v___x_3868_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3869_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_3870_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3842_, v_opts_3847_, v___x_3869_);
lean_dec_ref(v_opts_3847_);
lean_dec(v___x_3842_);
if (v___x_3870_ == 0)
{
v___y_3851_ = v___y_3833_;
v___y_3852_ = v___y_3834_;
goto v___jp_3850_;
}
else
{
lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___x_3871_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_3872_ = lean_array_get_size(v_a_3840_);
v___x_3873_ = l_Nat_reprFast(v___x_3872_);
v___x_3874_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3873_);
v___x_3875_ = l_Lean_MessageData_ofFormat(v___x_3874_);
v___x_3876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3876_, 0, v___x_3871_);
lean_ctor_set(v___x_3876_, 1, v___x_3875_);
v___x_3877_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_3868_, v___x_3876_, v___y_3833_, v___y_3834_);
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_dec_ref_known(v___x_3877_, 1);
v___y_3851_ = v___y_3833_;
v___y_3852_ = v___y_3834_;
goto v___jp_3850_;
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
lean_dec(v_a_3840_);
lean_dec_ref(v___x_3827_);
lean_dec(v_stx_3824_);
v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3877_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3877_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
}
}
v___jp_3850_:
{
size_t v_sz_3853_; size_t v___x_3854_; lean_object* v___x_3855_; 
v_sz_3853_ = lean_array_size(v_a_3840_);
v___x_3854_ = ((size_t)0ULL);
lean_inc_ref(v___x_3827_);
lean_inc(v_a_3838_);
v___x_3855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_3838_, v___x_3827_, v___x_3828_, v_a_3840_, v_sz_3853_, v___x_3854_, v___x_3849_, v___y_3851_, v___y_3852_);
lean_dec(v_a_3840_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v___x_3856_; size_t v___x_3857_; size_t v___x_3858_; 
lean_dec_ref_known(v___x_3855_, 1);
v___x_3856_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_3857_ = ((size_t)1ULL);
v___x_3858_ = lean_usize_add(v_i_3831_, v___x_3857_);
v_i_3831_ = v___x_3858_;
v_b_3832_ = v___x_3856_;
goto _start;
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec_ref(v___x_3827_);
lean_dec(v_stx_3824_);
v_a_3860_ = lean_ctor_get(v___x_3855_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3855_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3855_);
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
else
{
lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3893_; 
lean_dec_ref(v___x_3827_);
lean_dec(v_stx_3824_);
v_a_3886_ = lean_ctor_get(v___x_3839_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3888_ = v___x_3839_;
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v___x_3839_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3891_; 
if (v_isShared_3889_ == 0)
{
v___x_3891_ = v___x_3888_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v_a_3886_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
return v___x_3891_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___boxed(lean_object* v_stx_3894_, lean_object* v___x_3895_, lean_object* v___x_3896_, lean_object* v___x_3897_, lean_object* v___x_3898_, lean_object* v_as_3899_, lean_object* v_sz_3900_, lean_object* v_i_3901_, lean_object* v_b_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_){
_start:
{
size_t v_sz_boxed_3906_; size_t v_i_boxed_3907_; lean_object* v_res_3908_; 
v_sz_boxed_3906_ = lean_unbox_usize(v_sz_3900_);
lean_dec(v_sz_3900_);
v_i_boxed_3907_ = lean_unbox_usize(v_i_3901_);
lean_dec(v_i_3901_);
v_res_3908_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_3894_, v___x_3895_, v___x_3896_, v___x_3897_, v___x_3898_, v_as_3899_, v_sz_boxed_3906_, v_i_boxed_3907_, v_b_3902_, v___y_3903_, v___y_3904_);
lean_dec(v___y_3904_);
lean_dec_ref(v___y_3903_);
lean_dec_ref(v_as_3899_);
lean_dec(v___x_3898_);
lean_dec_ref(v___x_3896_);
lean_dec_ref(v___x_3895_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(lean_object* v_stx_3909_, lean_object* v___x_3910_, lean_object* v___x_3911_, lean_object* v___x_3912_, lean_object* v___x_3913_, lean_object* v_as_3914_, size_t v_sz_3915_, size_t v_i_3916_, lean_object* v_b_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_){
_start:
{
uint8_t v___x_3921_; 
v___x_3921_ = lean_usize_dec_lt(v_i_3916_, v_sz_3915_);
if (v___x_3921_ == 0)
{
lean_object* v___x_3922_; 
lean_dec_ref(v___x_3912_);
lean_dec(v_stx_3909_);
v___x_3922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3922_, 0, v_b_3917_);
return v___x_3922_;
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3924_; 
lean_dec_ref(v_b_3917_);
v_a_3923_ = lean_array_uget_borrowed(v_as_3914_, v_i_3916_);
lean_inc(v_a_3923_);
lean_inc(v_stx_3909_);
v___x_3924_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3909_, v___x_3910_, v_a_3923_, v___x_3911_, v___y_3918_, v___y_3919_);
if (lean_obj_tag(v___x_3924_) == 0)
{
lean_object* v_a_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v_scopes_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v_opts_3932_; uint8_t v_hasTrace_3933_; lean_object* v___x_3934_; lean_object* v___y_3936_; lean_object* v___y_3937_; 
v_a_3925_ = lean_ctor_get(v___x_3924_, 0);
lean_inc(v_a_3925_);
lean_dec_ref_known(v___x_3924_, 1);
v___x_3926_ = l_Lean_inheritedTraceOptions;
v___x_3927_ = lean_st_ref_get(v___x_3926_);
v___x_3928_ = lean_st_ref_get(v___y_3919_);
v_scopes_3929_ = lean_ctor_get(v___x_3928_, 2);
lean_inc(v_scopes_3929_);
lean_dec(v___x_3928_);
v___x_3930_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3931_ = l_List_head_x21___redArg(v___x_3930_, v_scopes_3929_);
lean_dec(v_scopes_3929_);
v_opts_3932_ = lean_ctor_get(v___x_3931_, 1);
lean_inc_ref(v_opts_3932_);
lean_dec(v___x_3931_);
v_hasTrace_3933_ = lean_ctor_get_uint8(v_opts_3932_, sizeof(void*)*1);
v___x_3934_ = lean_box(0);
if (v_hasTrace_3933_ == 0)
{
lean_dec_ref(v_opts_3932_);
lean_dec(v___x_3927_);
v___y_3936_ = v___y_3918_;
v___y_3937_ = v___y_3919_;
goto v___jp_3935_;
}
else
{
lean_object* v___x_3953_; lean_object* v___x_3954_; uint8_t v___x_3955_; 
v___x_3953_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3954_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_3955_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3927_, v_opts_3932_, v___x_3954_);
lean_dec_ref(v_opts_3932_);
lean_dec(v___x_3927_);
if (v___x_3955_ == 0)
{
v___y_3936_ = v___y_3918_;
v___y_3937_ = v___y_3919_;
goto v___jp_3935_;
}
else
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3956_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_3957_ = lean_array_get_size(v_a_3925_);
v___x_3958_ = l_Nat_reprFast(v___x_3957_);
v___x_3959_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3958_);
v___x_3960_ = l_Lean_MessageData_ofFormat(v___x_3959_);
v___x_3961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3956_);
lean_ctor_set(v___x_3961_, 1, v___x_3960_);
v___x_3962_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_3953_, v___x_3961_, v___y_3918_, v___y_3919_);
if (lean_obj_tag(v___x_3962_) == 0)
{
lean_dec_ref_known(v___x_3962_, 1);
v___y_3936_ = v___y_3918_;
v___y_3937_ = v___y_3919_;
goto v___jp_3935_;
}
else
{
lean_object* v_a_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3970_; 
lean_dec(v_a_3925_);
lean_dec_ref(v___x_3912_);
lean_dec(v_stx_3909_);
v_a_3963_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3965_ = v___x_3962_;
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_a_3963_);
lean_dec(v___x_3962_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3968_; 
if (v_isShared_3966_ == 0)
{
v___x_3968_ = v___x_3965_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_a_3963_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
}
}
}
v___jp_3935_:
{
size_t v_sz_3938_; size_t v___x_3939_; lean_object* v___x_3940_; 
v_sz_3938_ = lean_array_size(v_a_3925_);
v___x_3939_ = ((size_t)0ULL);
lean_inc_ref(v___x_3912_);
lean_inc(v_a_3923_);
v___x_3940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_3923_, v___x_3912_, v___x_3913_, v_a_3925_, v_sz_3938_, v___x_3939_, v___x_3934_, v___y_3936_, v___y_3937_);
lean_dec(v_a_3925_);
if (lean_obj_tag(v___x_3940_) == 0)
{
lean_object* v___x_3941_; size_t v___x_3942_; size_t v___x_3943_; lean_object* v___x_3944_; 
lean_dec_ref_known(v___x_3940_, 1);
v___x_3941_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_3942_ = ((size_t)1ULL);
v___x_3943_ = lean_usize_add(v_i_3916_, v___x_3942_);
v___x_3944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_3909_, v___x_3910_, v___x_3911_, v___x_3912_, v___x_3913_, v_as_3914_, v_sz_3915_, v___x_3943_, v___x_3941_, v___y_3918_, v___y_3919_);
return v___x_3944_;
}
else
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3952_; 
lean_dec_ref(v___x_3912_);
lean_dec(v_stx_3909_);
v_a_3945_ = lean_ctor_get(v___x_3940_, 0);
v_isSharedCheck_3952_ = !lean_is_exclusive(v___x_3940_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3947_ = v___x_3940_;
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v___x_3940_);
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
else
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3978_; 
lean_dec_ref(v___x_3912_);
lean_dec(v_stx_3909_);
v_a_3971_ = lean_ctor_get(v___x_3924_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3924_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3973_ = v___x_3924_;
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3924_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3976_; 
if (v_isShared_3974_ == 0)
{
v___x_3976_ = v___x_3973_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3___boxed(lean_object* v_stx_3979_, lean_object* v___x_3980_, lean_object* v___x_3981_, lean_object* v___x_3982_, lean_object* v___x_3983_, lean_object* v_as_3984_, lean_object* v_sz_3985_, lean_object* v_i_3986_, lean_object* v_b_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_){
_start:
{
size_t v_sz_boxed_3991_; size_t v_i_boxed_3992_; lean_object* v_res_3993_; 
v_sz_boxed_3991_ = lean_unbox_usize(v_sz_3985_);
lean_dec(v_sz_3985_);
v_i_boxed_3992_ = lean_unbox_usize(v_i_3986_);
lean_dec(v_i_3986_);
v_res_3993_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(v_stx_3979_, v___x_3980_, v___x_3981_, v___x_3982_, v___x_3983_, v_as_3984_, v_sz_boxed_3991_, v_i_boxed_3992_, v_b_3987_, v___y_3988_, v___y_3989_);
lean_dec(v___y_3989_);
lean_dec_ref(v___y_3988_);
lean_dec_ref(v_as_3984_);
lean_dec(v___x_3983_);
lean_dec_ref(v___x_3981_);
lean_dec_ref(v___x_3980_);
return v_res_3993_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(lean_object* v_stx_3997_, lean_object* v___x_3998_, lean_object* v___x_3999_, lean_object* v___x_4000_, lean_object* v___x_4001_, lean_object* v_as_4002_, size_t v_sz_4003_, size_t v_i_4004_, lean_object* v_b_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_){
_start:
{
uint8_t v___x_4009_; 
v___x_4009_ = lean_usize_dec_lt(v_i_4004_, v_sz_4003_);
if (v___x_4009_ == 0)
{
lean_object* v___x_4010_; 
lean_dec_ref(v___x_4000_);
lean_dec(v_stx_3997_);
v___x_4010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4010_, 0, v_b_4005_);
return v___x_4010_;
}
else
{
lean_object* v_a_4011_; lean_object* v___x_4012_; 
lean_dec_ref(v_b_4005_);
v_a_4011_ = lean_array_uget_borrowed(v_as_4002_, v_i_4004_);
lean_inc(v_a_4011_);
lean_inc(v_stx_3997_);
v___x_4012_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3997_, v___x_3998_, v_a_4011_, v___x_3999_, v___y_4006_, v___y_4007_);
if (lean_obj_tag(v___x_4012_) == 0)
{
lean_object* v_a_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v_scopes_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v_opts_4020_; uint8_t v_hasTrace_4021_; lean_object* v___x_4022_; lean_object* v___y_4024_; lean_object* v___y_4025_; 
v_a_4013_ = lean_ctor_get(v___x_4012_, 0);
lean_inc(v_a_4013_);
lean_dec_ref_known(v___x_4012_, 1);
v___x_4014_ = l_Lean_inheritedTraceOptions;
v___x_4015_ = lean_st_ref_get(v___x_4014_);
v___x_4016_ = lean_st_ref_get(v___y_4007_);
v_scopes_4017_ = lean_ctor_get(v___x_4016_, 2);
lean_inc(v_scopes_4017_);
lean_dec(v___x_4016_);
v___x_4018_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4019_ = l_List_head_x21___redArg(v___x_4018_, v_scopes_4017_);
lean_dec(v_scopes_4017_);
v_opts_4020_ = lean_ctor_get(v___x_4019_, 1);
lean_inc_ref(v_opts_4020_);
lean_dec(v___x_4019_);
v_hasTrace_4021_ = lean_ctor_get_uint8(v_opts_4020_, sizeof(void*)*1);
v___x_4022_ = lean_box(0);
if (v_hasTrace_4021_ == 0)
{
lean_dec_ref(v_opts_4020_);
lean_dec(v___x_4015_);
v___y_4024_ = v___y_4006_;
v___y_4025_ = v___y_4007_;
goto v___jp_4023_;
}
else
{
lean_object* v___x_4041_; lean_object* v___x_4042_; uint8_t v___x_4043_; 
v___x_4041_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4042_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_4043_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4015_, v_opts_4020_, v___x_4042_);
lean_dec_ref(v_opts_4020_);
lean_dec(v___x_4015_);
if (v___x_4043_ == 0)
{
v___y_4024_ = v___y_4006_;
v___y_4025_ = v___y_4007_;
goto v___jp_4023_;
}
else
{
lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___x_4044_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_4045_ = lean_array_get_size(v_a_4013_);
v___x_4046_ = l_Nat_reprFast(v___x_4045_);
v___x_4047_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4046_);
v___x_4048_ = l_Lean_MessageData_ofFormat(v___x_4047_);
v___x_4049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4049_, 0, v___x_4044_);
lean_ctor_set(v___x_4049_, 1, v___x_4048_);
v___x_4050_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_4041_, v___x_4049_, v___y_4006_, v___y_4007_);
if (lean_obj_tag(v___x_4050_) == 0)
{
lean_dec_ref_known(v___x_4050_, 1);
v___y_4024_ = v___y_4006_;
v___y_4025_ = v___y_4007_;
goto v___jp_4023_;
}
else
{
lean_object* v_a_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4058_; 
lean_dec(v_a_4013_);
lean_dec_ref(v___x_4000_);
lean_dec(v_stx_3997_);
v_a_4051_ = lean_ctor_get(v___x_4050_, 0);
v_isSharedCheck_4058_ = !lean_is_exclusive(v___x_4050_);
if (v_isSharedCheck_4058_ == 0)
{
v___x_4053_ = v___x_4050_;
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_a_4051_);
lean_dec(v___x_4050_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4056_; 
if (v_isShared_4054_ == 0)
{
v___x_4056_ = v___x_4053_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_a_4051_);
v___x_4056_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
return v___x_4056_;
}
}
}
}
}
v___jp_4023_:
{
size_t v_sz_4026_; size_t v___x_4027_; lean_object* v___x_4028_; 
v_sz_4026_ = lean_array_size(v_a_4013_);
v___x_4027_ = ((size_t)0ULL);
lean_inc_ref(v___x_4000_);
lean_inc(v_a_4011_);
v___x_4028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4011_, v___x_4000_, v___x_4001_, v_a_4013_, v_sz_4026_, v___x_4027_, v___x_4022_, v___y_4024_, v___y_4025_);
lean_dec(v_a_4013_);
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_object* v___x_4029_; size_t v___x_4030_; size_t v___x_4031_; 
lean_dec_ref_known(v___x_4028_, 1);
v___x_4029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_4030_ = ((size_t)1ULL);
v___x_4031_ = lean_usize_add(v_i_4004_, v___x_4030_);
v_i_4004_ = v___x_4031_;
v_b_4005_ = v___x_4029_;
goto _start;
}
else
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4040_; 
lean_dec_ref(v___x_4000_);
lean_dec(v_stx_3997_);
v_a_4033_ = lean_ctor_get(v___x_4028_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4035_ = v___x_4028_;
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_4028_);
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
else
{
lean_object* v_a_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4066_; 
lean_dec_ref(v___x_4000_);
lean_dec(v_stx_3997_);
v_a_4059_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4061_ = v___x_4012_;
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_a_4059_);
lean_dec(v___x_4012_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v___x_4064_; 
if (v_isShared_4062_ == 0)
{
v___x_4064_ = v___x_4061_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_a_4059_);
v___x_4064_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
return v___x_4064_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_stx_4067_, lean_object* v___x_4068_, lean_object* v___x_4069_, lean_object* v___x_4070_, lean_object* v___x_4071_, lean_object* v_as_4072_, lean_object* v_sz_4073_, lean_object* v_i_4074_, lean_object* v_b_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_){
_start:
{
size_t v_sz_boxed_4079_; size_t v_i_boxed_4080_; lean_object* v_res_4081_; 
v_sz_boxed_4079_ = lean_unbox_usize(v_sz_4073_);
lean_dec(v_sz_4073_);
v_i_boxed_4080_ = lean_unbox_usize(v_i_4074_);
lean_dec(v_i_4074_);
v_res_4081_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4067_, v___x_4068_, v___x_4069_, v___x_4070_, v___x_4071_, v_as_4072_, v_sz_boxed_4079_, v_i_boxed_4080_, v_b_4075_, v___y_4076_, v___y_4077_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
lean_dec_ref(v_as_4072_);
lean_dec(v___x_4071_);
lean_dec_ref(v___x_4069_);
lean_dec_ref(v___x_4068_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(lean_object* v_stx_4082_, lean_object* v___x_4083_, lean_object* v___x_4084_, lean_object* v___x_4085_, lean_object* v___x_4086_, lean_object* v_as_4087_, size_t v_sz_4088_, size_t v_i_4089_, lean_object* v_b_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_){
_start:
{
uint8_t v___x_4094_; 
v___x_4094_ = lean_usize_dec_lt(v_i_4089_, v_sz_4088_);
if (v___x_4094_ == 0)
{
lean_object* v___x_4095_; 
lean_dec_ref(v___x_4085_);
lean_dec(v_stx_4082_);
v___x_4095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4095_, 0, v_b_4090_);
return v___x_4095_;
}
else
{
lean_object* v_a_4096_; lean_object* v___x_4097_; 
lean_dec_ref(v_b_4090_);
v_a_4096_ = lean_array_uget_borrowed(v_as_4087_, v_i_4089_);
lean_inc(v_a_4096_);
lean_inc(v_stx_4082_);
v___x_4097_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_4082_, v___x_4083_, v_a_4096_, v___x_4084_, v___y_4091_, v___y_4092_);
if (lean_obj_tag(v___x_4097_) == 0)
{
lean_object* v_a_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v_scopes_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v_opts_4105_; uint8_t v_hasTrace_4106_; lean_object* v___x_4107_; lean_object* v___y_4109_; lean_object* v___y_4110_; 
v_a_4098_ = lean_ctor_get(v___x_4097_, 0);
lean_inc(v_a_4098_);
lean_dec_ref_known(v___x_4097_, 1);
v___x_4099_ = l_Lean_inheritedTraceOptions;
v___x_4100_ = lean_st_ref_get(v___x_4099_);
v___x_4101_ = lean_st_ref_get(v___y_4092_);
v_scopes_4102_ = lean_ctor_get(v___x_4101_, 2);
lean_inc(v_scopes_4102_);
lean_dec(v___x_4101_);
v___x_4103_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4104_ = l_List_head_x21___redArg(v___x_4103_, v_scopes_4102_);
lean_dec(v_scopes_4102_);
v_opts_4105_ = lean_ctor_get(v___x_4104_, 1);
lean_inc_ref(v_opts_4105_);
lean_dec(v___x_4104_);
v_hasTrace_4106_ = lean_ctor_get_uint8(v_opts_4105_, sizeof(void*)*1);
v___x_4107_ = lean_box(0);
if (v_hasTrace_4106_ == 0)
{
lean_dec_ref(v_opts_4105_);
lean_dec(v___x_4100_);
v___y_4109_ = v___y_4091_;
v___y_4110_ = v___y_4092_;
goto v___jp_4108_;
}
else
{
lean_object* v___x_4126_; lean_object* v___x_4127_; uint8_t v___x_4128_; 
v___x_4126_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4127_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_4128_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4100_, v_opts_4105_, v___x_4127_);
lean_dec_ref(v_opts_4105_);
lean_dec(v___x_4100_);
if (v___x_4128_ == 0)
{
v___y_4109_ = v___y_4091_;
v___y_4110_ = v___y_4092_;
goto v___jp_4108_;
}
else
{
lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
v___x_4129_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_4130_ = lean_array_get_size(v_a_4098_);
v___x_4131_ = l_Nat_reprFast(v___x_4130_);
v___x_4132_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4131_);
v___x_4133_ = l_Lean_MessageData_ofFormat(v___x_4132_);
v___x_4134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4134_, 0, v___x_4129_);
lean_ctor_set(v___x_4134_, 1, v___x_4133_);
v___x_4135_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_4126_, v___x_4134_, v___y_4091_, v___y_4092_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_dec_ref_known(v___x_4135_, 1);
v___y_4109_ = v___y_4091_;
v___y_4110_ = v___y_4092_;
goto v___jp_4108_;
}
else
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4143_; 
lean_dec(v_a_4098_);
lean_dec_ref(v___x_4085_);
lean_dec(v_stx_4082_);
v_a_4136_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4138_ = v___x_4135_;
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4135_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4141_; 
if (v_isShared_4139_ == 0)
{
v___x_4141_ = v___x_4138_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4136_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
}
v___jp_4108_:
{
size_t v_sz_4111_; size_t v___x_4112_; lean_object* v___x_4113_; 
v_sz_4111_ = lean_array_size(v_a_4098_);
v___x_4112_ = ((size_t)0ULL);
lean_inc_ref(v___x_4085_);
lean_inc(v_a_4096_);
v___x_4113_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4096_, v___x_4085_, v___x_4086_, v_a_4098_, v_sz_4111_, v___x_4112_, v___x_4107_, v___y_4109_, v___y_4110_);
lean_dec(v_a_4098_);
if (lean_obj_tag(v___x_4113_) == 0)
{
lean_object* v___x_4114_; size_t v___x_4115_; size_t v___x_4116_; lean_object* v___x_4117_; 
lean_dec_ref_known(v___x_4113_, 1);
v___x_4114_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_4115_ = ((size_t)1ULL);
v___x_4116_ = lean_usize_add(v_i_4089_, v___x_4115_);
v___x_4117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4082_, v___x_4083_, v___x_4084_, v___x_4085_, v___x_4086_, v_as_4087_, v_sz_4088_, v___x_4116_, v___x_4114_, v___y_4091_, v___y_4092_);
return v___x_4117_;
}
else
{
lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4125_; 
lean_dec_ref(v___x_4085_);
lean_dec(v_stx_4082_);
v_a_4118_ = lean_ctor_get(v___x_4113_, 0);
v_isSharedCheck_4125_ = !lean_is_exclusive(v___x_4113_);
if (v_isSharedCheck_4125_ == 0)
{
v___x_4120_ = v___x_4113_;
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_a_4118_);
lean_dec(v___x_4113_);
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
else
{
lean_object* v_a_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4151_; 
lean_dec_ref(v___x_4085_);
lean_dec(v_stx_4082_);
v_a_4144_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4151_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4151_ == 0)
{
v___x_4146_ = v___x_4097_;
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_a_4144_);
lean_dec(v___x_4097_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4149_; 
if (v_isShared_4147_ == 0)
{
v___x_4149_ = v___x_4146_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v_a_4144_);
v___x_4149_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
return v___x_4149_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4___boxed(lean_object* v_stx_4152_, lean_object* v___x_4153_, lean_object* v___x_4154_, lean_object* v___x_4155_, lean_object* v___x_4156_, lean_object* v_as_4157_, lean_object* v_sz_4158_, lean_object* v_i_4159_, lean_object* v_b_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_){
_start:
{
size_t v_sz_boxed_4164_; size_t v_i_boxed_4165_; lean_object* v_res_4166_; 
v_sz_boxed_4164_ = lean_unbox_usize(v_sz_4158_);
lean_dec(v_sz_4158_);
v_i_boxed_4165_ = lean_unbox_usize(v_i_4159_);
lean_dec(v_i_4159_);
v_res_4166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(v_stx_4152_, v___x_4153_, v___x_4154_, v___x_4155_, v___x_4156_, v_as_4157_, v_sz_boxed_4164_, v_i_boxed_4165_, v_b_4160_, v___y_4161_, v___y_4162_);
lean_dec(v___y_4162_);
lean_dec_ref(v___y_4161_);
lean_dec_ref(v_as_4157_);
lean_dec(v___x_4156_);
lean_dec_ref(v___x_4154_);
lean_dec_ref(v___x_4153_);
return v_res_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(lean_object* v_init_4167_, lean_object* v_stx_4168_, lean_object* v___x_4169_, lean_object* v___x_4170_, lean_object* v___x_4171_, lean_object* v___x_4172_, lean_object* v_n_4173_, lean_object* v_b_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_){
_start:
{
if (lean_obj_tag(v_n_4173_) == 0)
{
lean_object* v_cs_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; size_t v_sz_4181_; size_t v___x_4182_; lean_object* v___x_4183_; 
v_cs_4178_ = lean_ctor_get(v_n_4173_, 0);
v___x_4179_ = lean_box(0);
v___x_4180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4179_);
lean_ctor_set(v___x_4180_, 1, v_b_4174_);
v_sz_4181_ = lean_array_size(v_cs_4178_);
v___x_4182_ = ((size_t)0ULL);
v___x_4183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(v_init_4167_, v_stx_4168_, v___x_4169_, v___x_4170_, v___x_4171_, v___x_4172_, v_cs_4178_, v_sz_4181_, v___x_4182_, v___x_4180_, v___y_4175_, v___y_4176_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_object* v_a_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4198_; 
v_a_4184_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4198_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4198_ == 0)
{
v___x_4186_ = v___x_4183_;
v_isShared_4187_ = v_isSharedCheck_4198_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_a_4184_);
lean_dec(v___x_4183_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4198_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v_fst_4188_; 
v_fst_4188_ = lean_ctor_get(v_a_4184_, 0);
if (lean_obj_tag(v_fst_4188_) == 0)
{
lean_object* v_snd_4189_; lean_object* v___x_4190_; lean_object* v___x_4192_; 
v_snd_4189_ = lean_ctor_get(v_a_4184_, 1);
lean_inc(v_snd_4189_);
lean_dec(v_a_4184_);
v___x_4190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4190_, 0, v_snd_4189_);
if (v_isShared_4187_ == 0)
{
lean_ctor_set(v___x_4186_, 0, v___x_4190_);
v___x_4192_ = v___x_4186_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v___x_4190_);
v___x_4192_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
return v___x_4192_;
}
}
else
{
lean_object* v_val_4194_; lean_object* v___x_4196_; 
lean_inc_ref(v_fst_4188_);
lean_dec(v_a_4184_);
v_val_4194_ = lean_ctor_get(v_fst_4188_, 0);
lean_inc(v_val_4194_);
lean_dec_ref_known(v_fst_4188_, 1);
if (v_isShared_4187_ == 0)
{
lean_ctor_set(v___x_4186_, 0, v_val_4194_);
v___x_4196_ = v___x_4186_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v_val_4194_);
v___x_4196_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
return v___x_4196_;
}
}
}
}
else
{
lean_object* v_a_4199_; lean_object* v___x_4201_; uint8_t v_isShared_4202_; uint8_t v_isSharedCheck_4206_; 
v_a_4199_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4206_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4206_ == 0)
{
v___x_4201_ = v___x_4183_;
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
else
{
lean_inc(v_a_4199_);
lean_dec(v___x_4183_);
v___x_4201_ = lean_box(0);
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
v_resetjp_4200_:
{
lean_object* v___x_4204_; 
if (v_isShared_4202_ == 0)
{
v___x_4204_ = v___x_4201_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v_a_4199_);
v___x_4204_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
return v___x_4204_;
}
}
}
}
else
{
lean_object* v_vs_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; size_t v_sz_4210_; size_t v___x_4211_; lean_object* v___x_4212_; 
v_vs_4207_ = lean_ctor_get(v_n_4173_, 0);
v___x_4208_ = lean_box(0);
v___x_4209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4208_);
lean_ctor_set(v___x_4209_, 1, v_b_4174_);
v_sz_4210_ = lean_array_size(v_vs_4207_);
v___x_4211_ = ((size_t)0ULL);
v___x_4212_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(v_stx_4168_, v___x_4169_, v___x_4170_, v___x_4171_, v___x_4172_, v_vs_4207_, v_sz_4210_, v___x_4211_, v___x_4209_, v___y_4175_, v___y_4176_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4227_; 
v_a_4213_ = lean_ctor_get(v___x_4212_, 0);
v_isSharedCheck_4227_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4227_ == 0)
{
v___x_4215_ = v___x_4212_;
v_isShared_4216_ = v_isSharedCheck_4227_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4212_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4227_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v_fst_4217_; 
v_fst_4217_ = lean_ctor_get(v_a_4213_, 0);
if (lean_obj_tag(v_fst_4217_) == 0)
{
lean_object* v_snd_4218_; lean_object* v___x_4219_; lean_object* v___x_4221_; 
v_snd_4218_ = lean_ctor_get(v_a_4213_, 1);
lean_inc(v_snd_4218_);
lean_dec(v_a_4213_);
v___x_4219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4219_, 0, v_snd_4218_);
if (v_isShared_4216_ == 0)
{
lean_ctor_set(v___x_4215_, 0, v___x_4219_);
v___x_4221_ = v___x_4215_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v___x_4219_);
v___x_4221_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
return v___x_4221_;
}
}
else
{
lean_object* v_val_4223_; lean_object* v___x_4225_; 
lean_inc_ref(v_fst_4217_);
lean_dec(v_a_4213_);
v_val_4223_ = lean_ctor_get(v_fst_4217_, 0);
lean_inc(v_val_4223_);
lean_dec_ref_known(v_fst_4217_, 1);
if (v_isShared_4216_ == 0)
{
lean_ctor_set(v___x_4215_, 0, v_val_4223_);
v___x_4225_ = v___x_4215_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_val_4223_);
v___x_4225_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
return v___x_4225_;
}
}
}
}
else
{
lean_object* v_a_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4235_; 
v_a_4228_ = lean_ctor_get(v___x_4212_, 0);
v_isSharedCheck_4235_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4230_ = v___x_4212_;
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_a_4228_);
lean_dec(v___x_4212_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___x_4233_; 
if (v_isShared_4231_ == 0)
{
v___x_4233_ = v___x_4230_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_a_4228_);
v___x_4233_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
return v___x_4233_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(lean_object* v_init_4236_, lean_object* v_stx_4237_, lean_object* v___x_4238_, lean_object* v___x_4239_, lean_object* v___x_4240_, lean_object* v___x_4241_, lean_object* v_as_4242_, size_t v_sz_4243_, size_t v_i_4244_, lean_object* v_b_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_){
_start:
{
uint8_t v___x_4249_; 
v___x_4249_ = lean_usize_dec_lt(v_i_4244_, v_sz_4243_);
if (v___x_4249_ == 0)
{
lean_object* v___x_4250_; 
lean_dec_ref(v___x_4240_);
lean_dec(v_stx_4237_);
v___x_4250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4250_, 0, v_b_4245_);
return v___x_4250_;
}
else
{
lean_object* v_snd_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4285_; 
v_snd_4251_ = lean_ctor_get(v_b_4245_, 1);
v_isSharedCheck_4285_ = !lean_is_exclusive(v_b_4245_);
if (v_isSharedCheck_4285_ == 0)
{
lean_object* v_unused_4286_; 
v_unused_4286_ = lean_ctor_get(v_b_4245_, 0);
lean_dec(v_unused_4286_);
v___x_4253_ = v_b_4245_;
v_isShared_4254_ = v_isSharedCheck_4285_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_snd_4251_);
lean_dec(v_b_4245_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4285_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v_a_4255_; lean_object* v___x_4256_; 
v_a_4255_ = lean_array_uget_borrowed(v_as_4242_, v_i_4244_);
lean_inc(v_snd_4251_);
lean_inc_ref(v___x_4240_);
lean_inc(v_stx_4237_);
v___x_4256_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4236_, v_stx_4237_, v___x_4238_, v___x_4239_, v___x_4240_, v___x_4241_, v_a_4255_, v_snd_4251_, v___y_4246_, v___y_4247_);
if (lean_obj_tag(v___x_4256_) == 0)
{
lean_object* v_a_4257_; lean_object* v___x_4259_; uint8_t v_isShared_4260_; uint8_t v_isSharedCheck_4276_; 
v_a_4257_ = lean_ctor_get(v___x_4256_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4256_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4259_ = v___x_4256_;
v_isShared_4260_ = v_isSharedCheck_4276_;
goto v_resetjp_4258_;
}
else
{
lean_inc(v_a_4257_);
lean_dec(v___x_4256_);
v___x_4259_ = lean_box(0);
v_isShared_4260_ = v_isSharedCheck_4276_;
goto v_resetjp_4258_;
}
v_resetjp_4258_:
{
if (lean_obj_tag(v_a_4257_) == 0)
{
lean_object* v___x_4261_; lean_object* v___x_4263_; 
lean_dec_ref(v___x_4240_);
lean_dec(v_stx_4237_);
v___x_4261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4261_, 0, v_a_4257_);
if (v_isShared_4254_ == 0)
{
lean_ctor_set(v___x_4253_, 0, v___x_4261_);
v___x_4263_ = v___x_4253_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v___x_4261_);
lean_ctor_set(v_reuseFailAlloc_4267_, 1, v_snd_4251_);
v___x_4263_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
lean_object* v___x_4265_; 
if (v_isShared_4260_ == 0)
{
lean_ctor_set(v___x_4259_, 0, v___x_4263_);
v___x_4265_ = v___x_4259_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v___x_4263_);
v___x_4265_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
return v___x_4265_;
}
}
}
else
{
lean_object* v_a_4268_; lean_object* v___x_4269_; lean_object* v___x_4271_; 
lean_del_object(v___x_4259_);
lean_dec(v_snd_4251_);
v_a_4268_ = lean_ctor_get(v_a_4257_, 0);
lean_inc(v_a_4268_);
lean_dec_ref_known(v_a_4257_, 1);
v___x_4269_ = lean_box(0);
if (v_isShared_4254_ == 0)
{
lean_ctor_set(v___x_4253_, 1, v_a_4268_);
lean_ctor_set(v___x_4253_, 0, v___x_4269_);
v___x_4271_ = v___x_4253_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v___x_4269_);
lean_ctor_set(v_reuseFailAlloc_4275_, 1, v_a_4268_);
v___x_4271_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
size_t v___x_4272_; size_t v___x_4273_; 
v___x_4272_ = ((size_t)1ULL);
v___x_4273_ = lean_usize_add(v_i_4244_, v___x_4272_);
v_i_4244_ = v___x_4273_;
v_b_4245_ = v___x_4271_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4284_; 
lean_del_object(v___x_4253_);
lean_dec(v_snd_4251_);
lean_dec_ref(v___x_4240_);
lean_dec(v_stx_4237_);
v_a_4277_ = lean_ctor_get(v___x_4256_, 0);
v_isSharedCheck_4284_ = !lean_is_exclusive(v___x_4256_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4279_ = v___x_4256_;
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_a_4277_);
lean_dec(v___x_4256_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v___x_4282_; 
if (v_isShared_4280_ == 0)
{
v___x_4282_ = v___x_4279_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v_a_4277_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
return v___x_4282_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3___boxed(lean_object* v_init_4287_, lean_object* v_stx_4288_, lean_object* v___x_4289_, lean_object* v___x_4290_, lean_object* v___x_4291_, lean_object* v___x_4292_, lean_object* v_as_4293_, lean_object* v_sz_4294_, lean_object* v_i_4295_, lean_object* v_b_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_){
_start:
{
size_t v_sz_boxed_4300_; size_t v_i_boxed_4301_; lean_object* v_res_4302_; 
v_sz_boxed_4300_ = lean_unbox_usize(v_sz_4294_);
lean_dec(v_sz_4294_);
v_i_boxed_4301_ = lean_unbox_usize(v_i_4295_);
lean_dec(v_i_4295_);
v_res_4302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(v_init_4287_, v_stx_4288_, v___x_4289_, v___x_4290_, v___x_4291_, v___x_4292_, v_as_4293_, v_sz_boxed_4300_, v_i_boxed_4301_, v_b_4296_, v___y_4297_, v___y_4298_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
lean_dec_ref(v_as_4293_);
lean_dec(v___x_4292_);
lean_dec_ref(v___x_4290_);
lean_dec_ref(v___x_4289_);
return v_res_4302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2___boxed(lean_object* v_init_4303_, lean_object* v_stx_4304_, lean_object* v___x_4305_, lean_object* v___x_4306_, lean_object* v___x_4307_, lean_object* v___x_4308_, lean_object* v_n_4309_, lean_object* v_b_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_){
_start:
{
lean_object* v_res_4314_; 
v_res_4314_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4303_, v_stx_4304_, v___x_4305_, v___x_4306_, v___x_4307_, v___x_4308_, v_n_4309_, v_b_4310_, v___y_4311_, v___y_4312_);
lean_dec(v___y_4312_);
lean_dec_ref(v___y_4311_);
lean_dec_ref(v_n_4309_);
lean_dec(v___x_4308_);
lean_dec_ref(v___x_4306_);
lean_dec_ref(v___x_4305_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(lean_object* v___x_4315_, lean_object* v___x_4316_, lean_object* v_stx_4317_, lean_object* v___x_4318_, lean_object* v___x_4319_, lean_object* v_t_4320_, lean_object* v_init_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_){
_start:
{
lean_object* v_root_4325_; lean_object* v_tail_4326_; lean_object* v___x_4327_; 
v_root_4325_ = lean_ctor_get(v_t_4320_, 0);
v_tail_4326_ = lean_ctor_get(v_t_4320_, 1);
lean_inc_ref(v___x_4315_);
lean_inc(v_stx_4317_);
v___x_4327_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4321_, v_stx_4317_, v___x_4318_, v___x_4319_, v___x_4315_, v___x_4316_, v_root_4325_, v_init_4321_, v___y_4322_, v___y_4323_);
if (lean_obj_tag(v___x_4327_) == 0)
{
lean_object* v_a_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4364_; 
v_a_4328_ = lean_ctor_get(v___x_4327_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4327_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4330_ = v___x_4327_;
v_isShared_4331_ = v_isSharedCheck_4364_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_a_4328_);
lean_dec(v___x_4327_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4364_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
if (lean_obj_tag(v_a_4328_) == 0)
{
lean_object* v_a_4332_; lean_object* v___x_4334_; 
lean_dec(v_stx_4317_);
lean_dec_ref(v___x_4315_);
v_a_4332_ = lean_ctor_get(v_a_4328_, 0);
lean_inc(v_a_4332_);
lean_dec_ref_known(v_a_4328_, 1);
if (v_isShared_4331_ == 0)
{
lean_ctor_set(v___x_4330_, 0, v_a_4332_);
v___x_4334_ = v___x_4330_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_a_4332_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
return v___x_4334_;
}
}
else
{
lean_object* v_a_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; size_t v_sz_4339_; size_t v___x_4340_; lean_object* v___x_4341_; 
lean_del_object(v___x_4330_);
v_a_4336_ = lean_ctor_get(v_a_4328_, 0);
lean_inc(v_a_4336_);
lean_dec_ref_known(v_a_4328_, 1);
v___x_4337_ = lean_box(0);
v___x_4338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4338_, 0, v___x_4337_);
lean_ctor_set(v___x_4338_, 1, v_a_4336_);
v_sz_4339_ = lean_array_size(v_tail_4326_);
v___x_4340_ = ((size_t)0ULL);
v___x_4341_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(v_stx_4317_, v___x_4318_, v___x_4319_, v___x_4315_, v___x_4316_, v_tail_4326_, v_sz_4339_, v___x_4340_, v___x_4338_, v___y_4322_, v___y_4323_);
if (lean_obj_tag(v___x_4341_) == 0)
{
lean_object* v_a_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4355_; 
v_a_4342_ = lean_ctor_get(v___x_4341_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4341_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4344_ = v___x_4341_;
v_isShared_4345_ = v_isSharedCheck_4355_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_a_4342_);
lean_dec(v___x_4341_);
v___x_4344_ = lean_box(0);
v_isShared_4345_ = v_isSharedCheck_4355_;
goto v_resetjp_4343_;
}
v_resetjp_4343_:
{
lean_object* v_fst_4346_; 
v_fst_4346_ = lean_ctor_get(v_a_4342_, 0);
if (lean_obj_tag(v_fst_4346_) == 0)
{
lean_object* v_snd_4347_; lean_object* v___x_4349_; 
v_snd_4347_ = lean_ctor_get(v_a_4342_, 1);
lean_inc(v_snd_4347_);
lean_dec(v_a_4342_);
if (v_isShared_4345_ == 0)
{
lean_ctor_set(v___x_4344_, 0, v_snd_4347_);
v___x_4349_ = v___x_4344_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_snd_4347_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
else
{
lean_object* v_val_4351_; lean_object* v___x_4353_; 
lean_inc_ref(v_fst_4346_);
lean_dec(v_a_4342_);
v_val_4351_ = lean_ctor_get(v_fst_4346_, 0);
lean_inc(v_val_4351_);
lean_dec_ref_known(v_fst_4346_, 1);
if (v_isShared_4345_ == 0)
{
lean_ctor_set(v___x_4344_, 0, v_val_4351_);
v___x_4353_ = v___x_4344_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_val_4351_);
v___x_4353_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
return v___x_4353_;
}
}
}
}
else
{
lean_object* v_a_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4363_; 
v_a_4356_ = lean_ctor_get(v___x_4341_, 0);
v_isSharedCheck_4363_ = !lean_is_exclusive(v___x_4341_);
if (v_isSharedCheck_4363_ == 0)
{
v___x_4358_ = v___x_4341_;
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_a_4356_);
lean_dec(v___x_4341_);
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
}
else
{
lean_object* v_a_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4372_; 
lean_dec(v_stx_4317_);
lean_dec_ref(v___x_4315_);
v_a_4365_ = lean_ctor_get(v___x_4327_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4327_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4367_ = v___x_4327_;
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_a_4365_);
lean_dec(v___x_4327_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v___x_4370_; 
if (v_isShared_4368_ == 0)
{
v___x_4370_ = v___x_4367_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v_a_4365_);
v___x_4370_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
return v___x_4370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2___boxed(lean_object* v___x_4373_, lean_object* v___x_4374_, lean_object* v_stx_4375_, lean_object* v___x_4376_, lean_object* v___x_4377_, lean_object* v_t_4378_, lean_object* v_init_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_){
_start:
{
lean_object* v_res_4383_; 
v_res_4383_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___x_4373_, v___x_4374_, v_stx_4375_, v___x_4376_, v___x_4377_, v_t_4378_, v_init_4379_, v___y_4380_, v___y_4381_);
lean_dec(v___y_4381_);
lean_dec_ref(v___y_4380_);
lean_dec_ref(v_t_4378_);
lean_dec_ref(v___x_4377_);
lean_dec_ref(v___x_4376_);
lean_dec(v___x_4374_);
return v_res_4383_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4385_; lean_object* v___x_4386_; 
v___x_4385_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__0));
v___x_4386_ = l_Lean_stringToMessageData(v___x_4385_);
return v___x_4386_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; 
v___x_4390_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__4));
v___x_4391_ = l_Lean_stringToMessageData(v___x_4390_);
return v___x_4391_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4393_; lean_object* v___x_4394_; 
v___x_4393_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__6));
v___x_4394_ = l_Lean_stringToMessageData(v___x_4393_);
return v___x_4394_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9(void){
_start:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; 
v___x_4396_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__8));
v___x_4397_ = l_Lean_stringToMessageData(v___x_4396_);
return v___x_4397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(lean_object* v_stx_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_){
_start:
{
lean_object* v___x_4405_; lean_object* v_scopes_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v_opts_4409_; lean_object* v___y_4411_; lean_object* v___y_4412_; lean_object* v___y_4413_; lean_object* v___y_4414_; uint8_t v___y_4433_; lean_object* v___y_4434_; lean_object* v___y_4435_; lean_object* v___y_4441_; uint8_t v___y_4442_; lean_object* v___y_4443_; lean_object* v___y_4444_; lean_object* v___y_4450_; lean_object* v___y_4451_; uint8_t v___y_4452_; uint8_t v___y_4453_; lean_object* v___y_4454_; uint8_t v___y_4463_; lean_object* v___y_4464_; uint8_t v___y_4465_; uint8_t v___y_4466_; lean_object* v___y_4467_; lean_object* v___y_4468_; uint8_t v___y_4477_; uint8_t v___y_4478_; uint8_t v___y_4479_; uint8_t v___y_4513_; lean_object* v___x_4520_; uint8_t v___x_4521_; 
v___x_4405_ = lean_st_ref_get(v___y_4400_);
v_scopes_4406_ = lean_ctor_get(v___x_4405_, 2);
lean_inc(v_scopes_4406_);
lean_dec(v___x_4405_);
v___x_4407_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4408_ = l_List_head_x21___redArg(v___x_4407_, v_scopes_4406_);
lean_dec(v_scopes_4406_);
v_opts_4409_ = lean_ctor_get(v___x_4408_, 1);
lean_inc_ref(v_opts_4409_);
lean_dec(v___x_4408_);
v___x_4520_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_4521_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4409_, v___x_4520_);
if (v___x_4521_ == 0)
{
lean_object* v___x_4522_; uint8_t v___x_4523_; 
v___x_4522_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_4523_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4409_, v___x_4522_);
v___y_4513_ = v___x_4523_;
goto v___jp_4512_;
}
else
{
v___y_4513_ = v___x_4521_;
goto v___jp_4512_;
}
v___jp_4402_:
{
lean_object* v___x_4403_; lean_object* v___x_4404_; 
v___x_4403_ = lean_box(0);
v___x_4404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4403_);
return v___x_4404_;
}
v___jp_4410_:
{
lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v_a_4417_; lean_object* v___x_4418_; lean_object* v_line_4419_; lean_object* v_messages_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; 
v___x_4415_ = lean_st_ref_get(v___y_4411_);
v___x_4416_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_4411_);
v_a_4417_ = lean_ctor_get(v___x_4416_, 0);
lean_inc(v_a_4417_);
lean_dec_ref(v___x_4416_);
lean_inc_ref_n(v___y_4412_, 2);
v___x_4418_ = l_Lean_FileMap_toPosition(v___y_4412_, v___y_4414_);
lean_dec(v___y_4414_);
v_line_4419_ = lean_ctor_get(v___x_4418_, 0);
lean_inc(v_line_4419_);
lean_dec_ref(v___x_4418_);
v_messages_4420_ = lean_ctor_get(v___x_4415_, 1);
lean_inc_ref(v_messages_4420_);
lean_dec(v___x_4415_);
v___x_4421_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_4420_);
v___x_4422_ = lean_box(0);
v___x_4423_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___y_4412_, v_line_4419_, v_stx_4398_, v_opts_4409_, v___x_4421_, v_a_4417_, v___x_4422_, v___y_4413_, v___y_4411_);
lean_dec(v_a_4417_);
lean_dec_ref(v___x_4421_);
lean_dec_ref(v_opts_4409_);
lean_dec(v_line_4419_);
if (lean_obj_tag(v___x_4423_) == 0)
{
lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4430_; 
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4423_);
if (v_isSharedCheck_4430_ == 0)
{
lean_object* v_unused_4431_; 
v_unused_4431_ = lean_ctor_get(v___x_4423_, 0);
lean_dec(v_unused_4431_);
v___x_4425_ = v___x_4423_;
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
else
{
lean_dec(v___x_4423_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v___x_4428_; 
if (v_isShared_4426_ == 0)
{
lean_ctor_set(v___x_4425_, 0, v___x_4422_);
v___x_4428_ = v___x_4425_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v___x_4422_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
return v___x_4428_;
}
}
}
else
{
return v___x_4423_;
}
}
v___jp_4432_:
{
lean_object* v_fileMap_4436_; lean_object* v___x_4437_; 
v_fileMap_4436_ = lean_ctor_get(v___y_4434_, 1);
v___x_4437_ = l_Lean_Syntax_getPos_x3f(v_stx_4398_, v___y_4433_);
if (lean_obj_tag(v___x_4437_) == 0)
{
lean_object* v___x_4438_; 
v___x_4438_ = lean_unsigned_to_nat(0u);
v___y_4411_ = v___y_4435_;
v___y_4412_ = v_fileMap_4436_;
v___y_4413_ = v___y_4434_;
v___y_4414_ = v___x_4438_;
goto v___jp_4410_;
}
else
{
lean_object* v_val_4439_; 
v_val_4439_ = lean_ctor_get(v___x_4437_, 0);
lean_inc(v_val_4439_);
lean_dec_ref_known(v___x_4437_, 1);
v___y_4411_ = v___y_4435_;
v___y_4412_ = v_fileMap_4436_;
v___y_4413_ = v___y_4434_;
v___y_4414_ = v_val_4439_;
goto v___jp_4410_;
}
}
v___jp_4440_:
{
lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; 
lean_inc_ref(v___y_4444_);
v___x_4445_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4445_, 0, v___y_4444_);
v___x_4446_ = l_Lean_MessageData_ofFormat(v___x_4445_);
v___x_4447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4447_, 0, v___y_4443_);
lean_ctor_set(v___x_4447_, 1, v___x_4446_);
lean_inc(v___y_4441_);
v___x_4448_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___y_4441_, v___x_4447_, v___y_4399_, v___y_4400_);
if (lean_obj_tag(v___x_4448_) == 0)
{
lean_dec_ref_known(v___x_4448_, 1);
v___y_4433_ = v___y_4442_;
v___y_4434_ = v___y_4399_;
v___y_4435_ = v___y_4400_;
goto v___jp_4432_;
}
else
{
lean_dec_ref(v_opts_4409_);
lean_dec(v_stx_4398_);
return v___x_4448_;
}
}
v___jp_4449_:
{
lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; 
lean_inc_ref(v___y_4454_);
v___x_4455_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4455_, 0, v___y_4454_);
v___x_4456_ = l_Lean_MessageData_ofFormat(v___x_4455_);
v___x_4457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4457_, 0, v___y_4450_);
lean_ctor_set(v___x_4457_, 1, v___x_4456_);
v___x_4458_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1);
v___x_4459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4459_, 0, v___x_4457_);
lean_ctor_set(v___x_4459_, 1, v___x_4458_);
if (v___y_4453_ == 0)
{
lean_object* v___x_4460_; 
v___x_4460_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4441_ = v___y_4451_;
v___y_4442_ = v___y_4452_;
v___y_4443_ = v___x_4459_;
v___y_4444_ = v___x_4460_;
goto v___jp_4440_;
}
else
{
lean_object* v___x_4461_; 
v___x_4461_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4441_ = v___y_4451_;
v___y_4442_ = v___y_4452_;
v___y_4443_ = v___x_4459_;
v___y_4444_ = v___x_4461_;
goto v___jp_4440_;
}
}
v___jp_4462_:
{
lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; 
lean_inc_ref(v___y_4468_);
v___x_4469_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4469_, 0, v___y_4468_);
v___x_4470_ = l_Lean_MessageData_ofFormat(v___x_4469_);
lean_inc_ref(v___y_4467_);
v___x_4471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4471_, 0, v___y_4467_);
lean_ctor_set(v___x_4471_, 1, v___x_4470_);
v___x_4472_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5);
v___x_4473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4473_, 0, v___x_4471_);
lean_ctor_set(v___x_4473_, 1, v___x_4472_);
if (v___y_4463_ == 0)
{
lean_object* v___x_4474_; 
v___x_4474_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4450_ = v___x_4473_;
v___y_4451_ = v___y_4464_;
v___y_4452_ = v___y_4465_;
v___y_4453_ = v___y_4466_;
v___y_4454_ = v___x_4474_;
goto v___jp_4449_;
}
else
{
lean_object* v___x_4475_; 
v___x_4475_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4450_ = v___x_4473_;
v___y_4451_ = v___y_4464_;
v___y_4452_ = v___y_4465_;
v___y_4453_ = v___y_4466_;
v___y_4454_ = v___x_4475_;
goto v___jp_4449_;
}
}
v___jp_4476_:
{
lean_object* v___x_4480_; lean_object* v_a_4481_; uint8_t v___x_4482_; 
v___x_4480_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(v_stx_4398_, v___y_4399_, v___y_4400_);
v_a_4481_ = lean_ctor_get(v___x_4480_, 0);
lean_inc(v_a_4481_);
lean_dec_ref(v___x_4480_);
v___x_4482_ = lean_unbox(v_a_4481_);
if (v___x_4482_ == 0)
{
lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v_scopes_4486_; lean_object* v___x_4487_; lean_object* v_opts_4488_; uint8_t v_hasTrace_4489_; 
v___x_4483_ = l_Lean_inheritedTraceOptions;
v___x_4484_ = lean_st_ref_get(v___x_4483_);
v___x_4485_ = lean_st_ref_get(v___y_4400_);
v_scopes_4486_ = lean_ctor_get(v___x_4485_, 2);
lean_inc(v_scopes_4486_);
lean_dec(v___x_4485_);
v___x_4487_ = l_List_head_x21___redArg(v___x_4407_, v_scopes_4486_);
lean_dec(v_scopes_4486_);
v_opts_4488_ = lean_ctor_get(v___x_4487_, 1);
lean_inc_ref(v_opts_4488_);
lean_dec(v___x_4487_);
v_hasTrace_4489_ = lean_ctor_get_uint8(v_opts_4488_, sizeof(void*)*1);
if (v_hasTrace_4489_ == 0)
{
uint8_t v___x_4490_; 
lean_dec_ref(v_opts_4488_);
lean_dec(v___x_4484_);
v___x_4490_ = lean_unbox(v_a_4481_);
lean_dec(v_a_4481_);
v___y_4433_ = v___x_4490_;
v___y_4434_ = v___y_4399_;
v___y_4435_ = v___y_4400_;
goto v___jp_4432_;
}
else
{
lean_object* v___x_4491_; lean_object* v___x_4492_; uint8_t v___x_4493_; 
v___x_4491_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4492_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_4493_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4484_, v_opts_4488_, v___x_4492_);
lean_dec_ref(v_opts_4488_);
lean_dec(v___x_4484_);
if (v___x_4493_ == 0)
{
uint8_t v___x_4494_; 
v___x_4494_ = lean_unbox(v_a_4481_);
lean_dec(v_a_4481_);
v___y_4433_ = v___x_4494_;
v___y_4434_ = v___y_4399_;
v___y_4435_ = v___y_4400_;
goto v___jp_4432_;
}
else
{
lean_object* v___x_4495_; 
v___x_4495_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7);
if (v___y_4478_ == 0)
{
lean_object* v___x_4496_; uint8_t v___x_4497_; 
v___x_4496_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___x_4497_ = lean_unbox(v_a_4481_);
lean_dec(v_a_4481_);
v___y_4463_ = v___y_4477_;
v___y_4464_ = v___x_4491_;
v___y_4465_ = v___x_4497_;
v___y_4466_ = v___y_4479_;
v___y_4467_ = v___x_4495_;
v___y_4468_ = v___x_4496_;
goto v___jp_4462_;
}
else
{
lean_object* v___x_4498_; uint8_t v___x_4499_; 
v___x_4498_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___x_4499_ = lean_unbox(v_a_4481_);
lean_dec(v_a_4481_);
v___y_4463_ = v___y_4477_;
v___y_4464_ = v___x_4491_;
v___y_4465_ = v___x_4499_;
v___y_4466_ = v___y_4479_;
v___y_4467_ = v___x_4495_;
v___y_4468_ = v___x_4498_;
goto v___jp_4462_;
}
}
}
}
else
{
lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v_scopes_4503_; lean_object* v___x_4504_; lean_object* v_opts_4505_; uint8_t v_hasTrace_4506_; 
lean_dec(v_a_4481_);
lean_dec_ref(v_opts_4409_);
lean_dec(v_stx_4398_);
v___x_4500_ = l_Lean_inheritedTraceOptions;
v___x_4501_ = lean_st_ref_get(v___x_4500_);
v___x_4502_ = lean_st_ref_get(v___y_4400_);
v_scopes_4503_ = lean_ctor_get(v___x_4502_, 2);
lean_inc(v_scopes_4503_);
lean_dec(v___x_4502_);
v___x_4504_ = l_List_head_x21___redArg(v___x_4407_, v_scopes_4503_);
lean_dec(v_scopes_4503_);
v_opts_4505_ = lean_ctor_get(v___x_4504_, 1);
lean_inc_ref(v_opts_4505_);
lean_dec(v___x_4504_);
v_hasTrace_4506_ = lean_ctor_get_uint8(v_opts_4505_, sizeof(void*)*1);
if (v_hasTrace_4506_ == 0)
{
lean_dec_ref(v_opts_4505_);
lean_dec(v___x_4501_);
goto v___jp_4402_;
}
else
{
lean_object* v___x_4507_; lean_object* v___x_4508_; uint8_t v___x_4509_; 
v___x_4507_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4508_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__8_spec__12___closed__3);
v___x_4509_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4501_, v_opts_4505_, v___x_4508_);
lean_dec_ref(v_opts_4505_);
lean_dec(v___x_4501_);
if (v___x_4509_ == 0)
{
goto v___jp_4402_;
}
else
{
lean_object* v___x_4510_; lean_object* v___x_4511_; 
v___x_4510_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9);
v___x_4511_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_4507_, v___x_4510_, v___y_4399_, v___y_4400_);
if (lean_obj_tag(v___x_4511_) == 0)
{
lean_dec_ref_known(v___x_4511_, 1);
goto v___jp_4402_;
}
else
{
return v___x_4511_;
}
}
}
}
}
v___jp_4512_:
{
lean_object* v___x_4514_; uint8_t v___x_4515_; lean_object* v___x_4516_; uint8_t v___x_4517_; 
v___x_4514_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
v___x_4515_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4409_, v___x_4514_);
v___x_4516_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v___x_4517_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_4409_, v___x_4516_);
if (v___y_4513_ == 0)
{
if (v___x_4515_ == 0)
{
if (v___x_4517_ == 0)
{
lean_object* v___x_4518_; lean_object* v___x_4519_; 
lean_dec_ref(v_opts_4409_);
lean_dec(v_stx_4398_);
v___x_4518_ = lean_box(0);
v___x_4519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4519_, 0, v___x_4518_);
return v___x_4519_;
}
else
{
v___y_4477_ = v___x_4515_;
v___y_4478_ = v___y_4513_;
v___y_4479_ = v___x_4517_;
goto v___jp_4476_;
}
}
else
{
v___y_4477_ = v___x_4515_;
v___y_4478_ = v___y_4513_;
v___y_4479_ = v___x_4517_;
goto v___jp_4476_;
}
}
else
{
v___y_4477_ = v___x_4515_;
v___y_4478_ = v___y_4513_;
v___y_4479_ = v___x_4517_;
goto v___jp_4476_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___boxed(lean_object* v_stx_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_){
_start:
{
lean_object* v_res_4528_; 
v_res_4528_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(v_stx_4524_, v___y_4525_, v___y_4526_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
return v_res_4528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4541_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook));
v___x_4542_ = l_Lean_Elab_Command_addLinter(v___x_4541_);
return v___x_4542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2____boxed(lean_object* v_a_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_();
return v_res_4544_;
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
